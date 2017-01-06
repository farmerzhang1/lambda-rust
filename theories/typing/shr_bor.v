From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics.
From lrust.lifetime Require Import frac_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import lft_contexts type_context programs.
Set Default Proof Using "Type".

Section shr_bor.
  Context `{typeG Σ}.

  Program Definition shr_bor (κ : lft) (ty : type) : type :=
    {| st_own tid vl := (∃ (l:loc), ⌜vl = [ #l ]⌝ ∗ ty.(ty_shr) κ tid l)%I |}.
  Next Obligation.
    iIntros (κ ty tid vl) "H". iDestruct "H" as (l) "[% _]". by subst.
  Qed.

  Global Instance shr_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> subtype E L ==> subtype E L) shr_bor.
  Proof.
    intros κ1 κ2 Hκ ty1 ty2 Hty. apply subtype_simple_type.
    iIntros (??) "#LFT #HE #HL H". iDestruct (Hκ with "HE HL") as "#Hκ".
    iDestruct "H" as (l) "(% & H)". subst. iExists _. iSplit. done.
    iApply (ty2.(ty_shr_mono) with "LFT Hκ").
    iDestruct (Hty with "* [] [] []") as "(_ & _ & #Hs1)"; [done..|clear Hty].
    by iApply "Hs1".
  Qed.
  Global Instance shr_mono_flip E L :
    Proper (lctx_lft_incl E L ==> flip (subtype E L) ==> flip (subtype E L)) shr_bor.
  Proof. intros ??????. by apply shr_mono. Qed.
  Global Instance shr_proper E L :
    Proper (lctx_lft_eq E L ==> eqtype E L ==> eqtype E L) shr_bor.
  Proof. intros ??[] ??[]. by split; apply shr_mono. Qed.

  Global Instance shr_contractive κ : Contractive (shr_bor κ).
  Proof.
    intros n ?? EQ. unfold shr_bor. f_equiv. rewrite st_dist_unfold.
    f_contractive=> /= tid vl. repeat f_equiv. apply EQ.
  Qed.
  Global Instance shr_ne κ n : Proper (dist n ==> dist n) (shr_bor κ).
  Proof. apply contractive_ne, _. Qed.

  Global Instance shr_send κ ty :
    Sync ty → Send (shr_bor κ ty).
  Proof.
    iIntros (Hsync tid1 tid2 vl) "H". iDestruct "H" as (l) "[% Hshr]".
    iExists _. iSplit; first done. by iApply Hsync.
  Qed.
End shr_bor.

Notation "&shr{ κ } ty" := (shr_bor κ ty)
  (format "&shr{ κ } ty", at level 20, right associativity) : lrust_type_scope.

Section typing.
  Context `{typeG Σ}.

  Lemma shr_mono' E L κ1 κ2 ty1 ty2 :
    lctx_lft_incl E L κ2 κ1 → subtype E L ty1 ty2 →
    subtype E L (&shr{κ1} ty1) (&shr{κ2} ty2).
  Proof. by intros; apply shr_mono. Qed.
  Lemma shr_proper' E L κ ty1 ty2 :
    eqtype E L ty1 ty2 → eqtype E L (&shr{κ} ty1) (&shr{κ} ty2).
  Proof. by intros; apply shr_proper. Qed.

  Lemma tctx_reborrow_shr E L p ty κ κ' :
    lctx_lft_incl E L κ' κ →
    tctx_incl E L [p ◁ &shr{κ}ty] [p ◁ &shr{κ'}ty; p ◁{κ} &shr{κ}ty].
  Proof.
    iIntros (Hκκ' tid ??) "#LFT HE HL H".
    iDestruct (elctx_interp_persist with "HE") as "#HE'".
    iDestruct (llctx_interp_persist with "HL") as "#HL'". iFrame "HE HL".
    iDestruct (Hκκ' with "HE' HL'") as "Hκκ'".
    rewrite /tctx_interp big_sepL_singleton big_sepL_cons big_sepL_singleton.
    iDestruct "H" as (v) "[% #H]". iDestruct "H" as (l) "[EQ Hshr]".
    iDestruct "EQ" as %[=->]. simpl. iModIntro. iSplit.
    - iExists _. iSplit. done. iExists _. iSplit. done.
      by iApply (ty_shr_mono with "LFT Hκκ' Hshr").
    - iExists _. iSplit. done. iIntros "_". iIntros "!>".
      iExists _. auto.
  Qed.

  Lemma read_shr E L κ ty :
    Copy ty → lctx_lft_alive E L κ → typed_read E L (&shr{κ}ty) ty (&shr{κ}ty).
  Proof.
    iIntros (Hcopy Halive) "!#". iIntros (v tid F qE qL ?) "#LFT Htl HE HL Hown".
    iMod (Halive with "HE HL") as (q) "[Hκ Hclose]"; first set_solver.
    iDestruct "Hown" as (l) "[EQ #Hshr]". iDestruct "EQ" as %[=->].
     assert (↑shrN ⊆ (↑lrustN : coPset)) by solve_ndisj. (* set_solver needs some help. *)
    iMod (copy_shr_acc with "LFT Hshr Htl Hκ") as (q') "(Htl & H↦ & Hcl)".
    { set_solver. } { rewrite ->shr_locsE_shrN. set_solver. }
    iDestruct "H↦" as (vl) "[>Hmt #Hown]". iModIntro. iExists _, _, _.
    iSplit; first done. iFrame "∗#". iIntros "Hmt".
    iMod ("Hcl" with "Htl [Hmt]") as "[$ Hκ]".
    { iExists _. iFrame "∗#". }
    iMod ("Hclose" with "Hκ") as "[$ $]". iExists _. auto.
  Qed.
End typing.

Hint Resolve shr_mono' shr_proper' : lrust_typing.
