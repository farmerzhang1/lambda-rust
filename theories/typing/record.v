From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list numbers.
From lrust.typing Require Import lft_contexts product programs.
From lrust.typing Require Export type.
From lrust.lang Require Import notation.
From iris.prelude Require Import options.

(* see product.v, the proof should pretty much the same *)
Section record.
  Context `{!typeGS Σ}.
  Lemma split_prod_mt tid ty1 ty2 q l f :
    (l ↦∗{q}: λ vl,
       ∃ v1 v2, ⌜vl = [(f r: v1 :r: v2)%V]⌝ ∗ ty1.(ty_own) tid [v1] ∗ ty2.(ty_own) tid [v2])%I
       ⊣⊢ (∃ v1, l ↦∗{q} [v1] ∗ ty1.(ty_own) tid [v1]) ∗ (∃ v2, (l +ₗ ty1.(ty_size)) ↦∗{q} [v2] ∗ ty2.(ty_own) tid [v2]).
  Proof.
    iSplit; iIntros "H".
    - iDestruct "H" as (vl) "[H↦ H]". iDestruct "H" as (v1 v2) "(% & H1 & H2)".
      subst. rewrite heap_mapsto_vec_idemp /= app_nil_r heap_mapsto_vec_app.
      iDestruct "H↦" as "[H↦1 H↦2]".
      iDestruct (ty_size_eq with "H1") as %<-.
      rewrite flattenv_simpl lty_size_singleton -!heap_mapsto_val_idemp.
      iSplitL "H↦1 H1"; iExists _; iFrame.
    - iDestruct "H" as "[H1 H2]".
      iDestruct "H1" as (v1) "[Hvl1 Hown1]".
      iDestruct "H2" as (v2) "[Hvl2 Hown2]".
      iExists [(f r: v1 :r: v2)%V].
      (* so ugly!! *)
      assert (l ↦∗{q} [(f r: v1 :r: v2)%V] ⊣⊢ l ↦∗{q} ([v1] ++ [v2])).
      { rewrite heap_mapsto_vec_idemp /= app_nil_r.
        assert (l ↦∗{q} [v1; v2] ⊣⊢ l ↦∗{q} (flattenv v1 ++ flattenv v2)); first by rewrite heap_mapsto_vec_idemp /= app_nil_r.
        by rewrite H.
      }
      rewrite H heap_mapsto_vec_app. iDestruct (ty_size_eq with "Hown1") as %<-.
      iFrame. iExists _, _. by iFrame.
  Qed.
  (* is this even provable? I'm so very not sure *)
  Lemma val_singleton_vec_exists l q ty tid κ : &{κ}(∃ v, l ↦∗{q} [v] ∗ ty_own ty tid [v]) -∗ &{κ}(l ↦∗{q}: ty_own ty tid).
  Proof.
  Admitted.

  Program Definition rcons (p : (string * type)) (ty2 : type) : type :=
    let (l, ty1) := p in
    {| ty_size := ty1.(ty_size) + ty2.(ty_size);
       ty_own tid vl := (∃ v1 v2, ⌜vl = [(l r: v1 :r: v2)%V]⌝ ∗ ty1.(ty_own) tid [v1] ∗ ty2.(ty_own) tid [v2])%I;
       ty_shr κ tid l :=
         (ty1.(ty_shr) κ tid l ∗
          ty2.(ty_shr) κ tid (l +ₗ ty1.(ty_size)))%I
    |}.
  Next Obligation.
    iIntros (_ ty2 f ty1 ??) "H".
    iDestruct "H" as (v1 v2 ->) "[H1 H2]".
    rewrite /list_ty_size /= Nat.add_0_r.
    iDestruct (ty_size_eq with "H1") as %<-.
    iDestruct (ty_size_eq with "H2") as %<-.
    by rewrite !lty_size_singleton.
  Qed.
  Next Obligation.
    iIntros (_ ty2 f ty1 E κ l tid q H) "#Hctx H /= Htok".
    rewrite split_prod_mt.
    (* from full borrow we can create a shared reference *)
    (* but first we need to split the full borrow *)
    iMod (bor_sep with "Hctx H") as "(H1 & H2)"; first done.
    iDestruct (val_singleton_vec_exists with "H1") as "H1".
    iDestruct (val_singleton_vec_exists with "H2") as "H2".
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
  Program Definition rnil' : type :=
  {| ty_size := 1;
     ty_own tid vl := ⌜vl = [rnil%V]⌝%I;
     ty_shr κ tid l :=
      emp%I
  |}.
  Next Obligation.
    iIntros (??) "%H". subst vl. iPureIntro. done.
  Qed.
  Next Obligation.
    iIntros (??????) "_ _ Htok". iModIntro. iFrame.
  Qed.
  Next Obligation.
    iIntros (????) "_ //".
  Qed.

  (* FIXME: because we didn't make val_size rnil to be zero, we can't use unit in foldr (it has size 0), but use our custom 1size rnil type *)
  Definition record := foldr rcons rnil'.
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
  Global Instance record_wf fl tyl `{!ListTyWf tyl} : TyWf (record (zip fl tyl)) :=
    { ty_lfts := tyl_lfts tyl; ty_wf_E := tyl_wf_E tyl }.

End record.

Section typing.
Context `{!typeGS Σ}.
  Lemma tctx_incl_rnil_singleton E L T : tctx_incl E L T [rnil%V ◁ rnil'].
  Proof.
    iIntros (???) "_ _ $ _ !>".
    rewrite tctx_interp_singleton /tctx_elt_interp.
    iExists rnil%V; iSplit; done.
  Qed.

  Lemma tctx_extract_ctx_rnil E L T1 T2 T3 :
    tctx_extract_ctx E L T1 T2 T3 → tctx_extract_ctx E L ((rnil%V ◁ rnil') :: T1) T2 T3.
  Proof.
    rewrite /tctx_extract_hasty.
    apply tctx_extract_ctx_hasty,
      (tctx_incl_frame_r T2 [] [rnil%V ◁ rnil']),
      tctx_incl_rnil_singleton.
  Qed.

  Lemma tctx_incl_rnil E L T1 T2 :
    tctx_incl E L T1 T2 → tctx_incl E L T1 ((rnil%V ◁ rnil') :: T2).
  Proof.
    iIntros (Hincl ???) "Hlft HEl q T".
    iMod (Hincl with "Hlft HEl q T") as "[q HT]".
    rewrite tctx_interp_cons tctx_hasty_val.
    iModIntro. iFrame. done.
  Qed.

  Fixpoint tlookup {A : Type} (f : string) l : option A := match l with
    | [] => None
    | (f', ty)::l' => if bool_decide (f = f') then Some ty else tlookup f l'
  end.

  Lemma type_rcons_instr E L l p1 p2 t1 t2: 
    ⊢ typed_instruction_ty E L [p1 ◁ t1 ; p2 ◁ t2] (l r: p1 :r: p2) (rcons (l, t1) t2).
  Proof.
    iIntros (tid ?) "_ _ $ $ (Hp1 & Hp2 & _)".
    wp_apply (wp_hasty with "Hp1").
    iIntros (v1) "_ H1".
    wp_apply (wp_hasty with "Hp2").
    iIntros (v2) "_ H2".
    iApply wp_value.
    rewrite tctx_interp_singleton tctx_hasty_val.
    simpl. eauto with iFrame.
  Qed.

  Fixpoint flatten v := match v with
    | (f r: v1 :r: v2)%V => (f, v1) :: flatten v2
    | _ => []
  end.
  Inductive record_val : val → Prop :=
    | RVNil : record_val rnil%V
    | RVCons f v' v1 : record_val v1 → record_val (f r: v' :r: v1).
  Lemma flatten_eq v f : lang.tlookup v f = tlookup f (flatten v).
  Proof.
    induction v; try done.
    simpl.
    case_bool_decide; done.
  Qed.

  Lemma ty_own_lookup_val fs v f tid ty :
    tlookup f fs = Some ty →
    ty_own (record fs) tid [v] -∗
    ∃v', ⌜lang.tlookup v f = Some v'⌝.
  Proof.
    iIntros (?) "Hown".
    rewrite flatten_eq.
    destruct fs as [| (?, ?) ?]; try done.
    replace (record ((s, t) :: fs)) with (rcons (s, t) (record fs)) by done.
    rewrite /rcons /=; iDestruct "Hown" as (??) "[% _]".
    iPureIntro. simpl.
    (* destruct v; try done. *)
    revert v1 v2  H0.
    induction v as [ | | | ]; try done.
    simpl.
    intros. simpl in H0.
    assert (l = s) by admit.
    assert (v0 = v1) by admit.
    assert (v2 = v3) by admit.
    subst.
    case_bool_decide.
    - by exists v1.
    - admit.
    (* FIXME: I belive the proof method is wrong, 
    I might need to generalize something somewhere, also, I think I'll need to associate the return value and the type *)
  Admitted.

  Lemma type_proj_instr E L f p fs ty :
    tlookup f fs = Some ty →
    ⊢ typed_instruction_ty E L [p ◁ record fs] (p ↓ f) ty.
  Proof.
    iIntros (Hlookup tid ?) "_ _ $ $ Hp".
    rewrite tctx_interp_singleton.
    wp_apply (wp_hasty with "Hp").
    iIntros (v) "_ Hown".
    iDestruct (ty_own_lookup_val with "Hown") as "%H"; first apply Hlookup.
    destruct H.
    iApply wp_proj; first apply H. (* I need to get the value from record *)
    admit.
  Admitted.

  Lemma type_rcons' E L C T T' p ty x e f:
    Closed (x :b: []) e →
    tctx_extract_ctx E L [p ◁ ty] T T' →
    (∀ (v : val), typed_body E L C ((v ◁ rcons (f, ty) rnil') :: T') (subst' x v e)) -∗
    typed_body E L C T (let: x := (f r: p :r: rnil) in e).
  Proof. iIntros. iApply type_let; [iApply type_rcons_instr| |done]. 
    admit.
  Admitted.

  Lemma type_rcons E L C T T' p1 p2 ty1 ty2 x e f:
    Closed (x :b: []) e →
    tctx_extract_ctx E L [p1 ◁ ty1; p2 ◁ ty2] T T' →
    (∀ (v : val), typed_body E L C ((v ◁ rcons (f, ty1) ty2) :: T') (subst' x v e)) -∗
    typed_body E L C T (let: x := (f r: p1 :r: p2) in e).
  Proof. iIntros. iApply type_let; [iApply type_rcons_instr|solve_typing|done]. Qed.

  Lemma type_proj E L C T T' p ty x e f fs:
    Closed (x :b: []) e →
    tlookup f fs = Some ty →
    tctx_extract_ctx E L [p ◁ record fs] T T' →
    (∀ (v : val), typed_body E L C ((v ◁ ty) :: T') (subst' x v e)) -∗
    typed_body E L C T (let: x := p ↓ f in e).
  Proof. iIntros. iApply type_let; [by iApply type_proj_instr|solve_typing|done]. Qed.

End typing.
Global Arguments record : simpl never.
Global Arguments rcons : simpl never.
