From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list numbers.
From lrust.typing Require Import lft_contexts product programs.
From lrust.typing Require Export type.
From lrust.lang Require Import notation.
From iris.prelude Require Import options.

(* see product.v, the proof should pretty much the same *)
Section record.
  Context `{!typeGS Σ}.
  Lemma split_prod_mt tid ty1 ty2 q l :
    (l ↦∗{q}: λ vl,
       ∃ vl1 vl2, ⌜vl = vl1 ++ vl2⌝ ∗ ty1.(ty_own) tid vl1 ∗ ty2.(ty_own) tid vl2)%I
       ⊣⊢ l ↦∗{q}: ty1.(ty_own) tid ∗ (l +ₗ ty1.(ty_size)) ↦∗{q}: ty2.(ty_own) tid.
  Proof.
    iSplit; iIntros "H".
    - iDestruct "H" as (vl) "[H↦ H]". iDestruct "H" as (vl1 vl2) "(% & H1 & H2)".
      subst. rewrite heap_mapsto_vec_app. iDestruct "H↦" as "[H↦1 H↦2]".
      iDestruct (ty_size_eq with "H1") as %->.
      iSplitL "H1 H↦1"; iExists _; iFrame.
    - iDestruct "H" as "[H1 H2]". iDestruct "H1" as (vl1) "[H↦1 H1]".
      iDestruct "H2" as (vl2) "[H↦2 H2]". iExists (vl1 ++ vl2).
      rewrite heap_mapsto_vec_app. iDestruct (ty_size_eq with "H1") as %->.
      iFrame. iExists _, _. by iFrame.
  Qed.
  (* FIXME: the RustBelt paper says
  types in Rust do not just cover a single VALUE:
  In general, data is laid out in memory
  and spans multiple locations.
  However, we have to impose some restrictions
  on the lists of values accepted by a type:
  we require that every type has a fixed size [τ].size.
  This size is used to compute
  the layout of compound data structures,
  e.g., for product types.
  We require that a type only accepts lists whose length matches the size
  是说，rustbelt的value大小都是1，该怎么办呢！！！
  不然我会被迫要证明
    [(l r: v1 :r: v2)%V] = [v1] ++ [v2]
  而且我们丢失了label的信息
  *)
  Program Definition rcons (p : (string * type)) (ty2 : type) : type :=
    let (l, ty1) := p in
    {| ty_size := ty1.(ty_size) + ty2.(ty_size);
       ty_own tid vl := (∃ vl1 vl2,
         ⌜vl = vl1 ++ vl2⌝ ∗ ty1.(ty_own) tid vl1 ∗ ty2.(ty_own) tid vl2)%I;
       ty_shr κ tid l :=
         (ty1.(ty_shr) κ tid l ∗
          ty2.(ty_shr) κ tid (l +ₗ ty1.(ty_size)))%I
    |}.
  Next Obligation.
    iIntros (_ ty2 l ty1 ??) "H".
    iDestruct "H" as (v1 v2 ->) "[H1 H2]".
    rewrite app_length. (* without this rewrite, we can't destruct the next equations with -> *)
    iDestruct (ty_size_eq with "H1") as %->.
    iDestruct (ty_size_eq with "H2") as %->.
    done.
  Qed.
  Next Obligation.
    iIntros (_ ty2 _ ty1 E κ l tid q H) "#Hctx H /= Htok".
    rewrite split_prod_mt.
    (* from full borrow we can create a shared reference *)
    (* but first we need to split the full borrow *)
    iMod (bor_sep with "Hctx H") as "(H1 & H2)"; first done.
    (* now we get the sharing predicate from H1 and H2, using ty-share *)
    iMod (ty1.(ty_share) with "Hctx H1 Htok") as "[H1 Htok]"; first apply H.
    iMod (ty2.(ty_share) with "Hctx H2 Htok") as "[H2 Htok]"; first apply H.
    iModIntro. iFrame.
  Qed.
  Next Obligation.
    iIntros (_ ty2 _ ty1 ?? ??) "#H⊑ [H1 H2]".
    (* need to shorten lifetime, respectively *)
    iSplit.
    - by iApply (ty1.(ty_shr_mono) with "H⊑").
    - by iApply (ty2.(ty_shr_mono) with "H⊑").
  Qed.
  (* oh hello, can we hide rcons here it's not really a record *)
  Definition record := foldr rcons unit0.
  Global Instance rcons_proper n l:
  Proper (type_dist2 n ==> type_dist2 n ==> type_dist2 n) (λ t1 t2, rcons (l, t1) t2).
  Proof. solve_type_proper. Qed.
  Global Instance record_proper n ls : Proper (Forall2 (type_dist2 n) ==> type_dist2 n) 
    (λ ts, record (zip ls ts)).
  Proof.
    (*
    If induction_arg is a natural, 
    then `destruct natural` behaves like 
    intros until natural 
    followed by destruct applied to 
    the last introduced hypothesis.
    *)
    intros ???.
    (* KEY! *)
    generalize dependent ls.
    induction H; first reflexivity. (* induction on H, not the other list types *)
    destruct ls; first f_equal.
    assert (∀ A B (x : A) (y : B) xs ys, zip (x :: xs) (y :: ys) = (x,y) :: zip xs ys); first done. 
    do 2 rewrite H1.
    apply rcons_proper; first apply H. apply IHForall2.
  Qed.
End record.

Section typing.
Context `{!typeGS Σ}.

  Lemma type_rcons E L l p1 p2 t1 t2: 
    ⊢ typed_instruction_ty E L [p1 ◁ t1 ; p2 ◁ t2] (l r: p1 :r: p2) (rcons (l, t1) t2).
  Proof.
    iIntros (tid ?) "_ _ $ $ (Hp1 & Hp2 & _)".
    wp_apply (wp_hasty with "Hp1").
    iIntros (v1) "_ H1".
    wp_apply (wp_hasty with "Hp2").
    iIntros (v2) "_ H2".
    iApply wp_value.
    rewrite tctx_interp_singleton tctx_hasty_val.
    simpl. iExists [v1], [v2]. iFrame. admit.
  Admitted.
End typing.
