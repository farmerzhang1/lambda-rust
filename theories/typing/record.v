From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list numbers.
From lrust.typing Require Import lft_contexts product.
From lrust.typing Require Export type.

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
  Program Definition record2 (p : (string * type)) (ty1 : type) : type :=
    let (_, ty2) := p in
    {| ty_size := ty1.(ty_size) + ty2.(ty_size);
       ty_own tid vl := (∃ vl1 vl2,
         ⌜vl = vl1 ++ vl2⌝ ∗ ty1.(ty_own) tid vl1 ∗ ty2.(ty_own) tid vl2)%I;
       ty_shr κ tid l :=
         (ty1.(ty_shr) κ tid l ∗
          ty2.(ty_shr) κ tid (l +ₗ ty1.(ty_size)))%I
    |}.
  Next Obligation.
    iIntros (_ ty1 _ ty2 ??) "H".
    iDestruct "H" as (vl1 vl2 ->) "[H1 H2]".
    rewrite app_length. (* without this rewrite, we can't destruct the next equations with -> *)
    iDestruct (ty_size_eq with "H1") as %->.
    iDestruct (ty_size_eq with "H2") as %->.
    done.
  Qed.
  Next Obligation.
    iIntros (_ ty1 _ ty2 E κ l tid q H) "#Hctx H /= Htok".
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
    iIntros (_ ty1 _ ty2 ?? ??) "#H⊑ [H1 H2]".
    (* need to shorten lifetime, respectively *)
    iSplit.
    - by iApply (ty1.(ty_shr_mono) with "H⊑").
    - by iApply (ty2.(ty_shr_mono) with "H⊑").
  Qed.
  (* oh hello, can we hide record2 here it's not really a record *)
  Definition record := foldr record2 unit0.
  (* we need to proof that the field names are distinct? *)
  Definition record_example := record [("x", unit0) ; ("y", unit0); ("z", unit0)].
End record.
