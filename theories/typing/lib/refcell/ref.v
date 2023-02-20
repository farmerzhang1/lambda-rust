From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth csum frac agree.
From iris.bi Require Import fractional.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing.
From lrust.typing.lib.refcell Require Import refcell.
From iris.prelude Require Import options.

Definition refcell_refN := refcellN .@ "ref".

Section ref.
  Context `{!typeGS Σ, !refcellG Σ}.

  (* The Rust type looks as follows (after some unfolding):

     pub struct Ref<'b, T: ?Sized + 'b> {
       value: &'b T,
       borrow: &'b Cell<BorrowFlag>,
     }
  *)

  Program Definition ref (α : lft) (ty : type) :=
    tc_opaque
    {| ty_size := 2;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc lv);  #(LitLoc lrc) ] =>
           ∃ ν q γ β ty', ty.(ty_shr) (α ⊓ ν) tid lv ∗
             α ⊑ β ∗ &na{β, tid, refcell_invN}(refcell_inv tid lrc γ β ty') ∗
             q.[ν] ∗ own γ (◯ reading_stR q ν)
         | _ => False
         end;
       ty_shr κ tid l :=
          ∃ ν q γ β ty' (lv lrc : loc),
             κ ⊑ ν ∗ &frac{κ} (λ q, l↦∗{q} [ #lv; #lrc]) ∗
             ▷ ty.(ty_shr) (α ⊓ ν) tid lv ∗
             ▷ (α ⊑ β) ∗ ▷ &na{β, tid, refcell_invN}(refcell_inv tid lrc γ β ty') ∗
             &na{κ, tid, refcell_refN}(own γ (◯ reading_stR q ν)) |}%I.
  Next Obligation. iIntros (???[|[[]| | |][|[[]| | |][]]]) "?"; auto. Qed.
  Next Obligation.
    iIntros (α ty E κ l tid q ?) "#LFT Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]"; first done.
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦"; first done.
    destruct vl as [|[[|lv|]| | |][|[[|lrc|]| | |][]]];
      try by iMod (bor_persistent with "LFT Hb Htok") as "[>[] _]".
    iMod (bor_exists with "LFT Hb") as (ν) "Hb"; first done.
    iMod (bor_exists with "LFT Hb") as (q') "Hb"; first done.
    iMod (bor_exists with "LFT Hb") as (γ) "Hb"; first done.
    iMod (bor_exists with "LFT Hb") as (β) "Hb"; first done.
    iMod (bor_exists with "LFT Hb") as (ty') "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[Hshr Hb]"; first done.
    iMod (bor_persistent with "LFT Hshr Htok") as "[#Hshr Htok]"; first done.
    iMod (bor_sep with "LFT Hb") as "[Hαβ Hb]"; first done.
    iMod (bor_persistent with "LFT Hαβ Htok") as "[#Hαβ Htok]"; first done.
    iMod (bor_sep with "LFT Hb") as "[Hinv Hb]"; first done.
    iMod (bor_persistent with "LFT Hinv Htok") as "[#Hinv $]"; first done.
    iMod (bor_sep with "LFT Hb") as "[Hκν Hb]"; first done.
    iDestruct (frac_bor_lft_incl with "LFT [> Hκν]") as "#Hκν".
    { iApply bor_fracture; try done. by rewrite Qp.mul_1_r. }
    iMod (bor_na with "Hb") as "#Hb"; first done. eauto 20.
  Qed.
  Next Obligation.
    iIntros (??????) "#? H". iDestruct "H" as (ν q γ β ty' lv lrc) "H".
    iExists _, _, _, _, _, _, _. iDestruct "H" as "#(? & ? & $ & $ & $ & ?)".
    iSplit; last iSplit.
    - by iApply lft_incl_trans.
    - by iApply frac_bor_shorten.
    - by iApply na_bor_shorten.
  Qed.

  Global Instance ref_wf α ty `{!TyWf ty} : TyWf (ref α ty) :=
    { ty_lfts := [α]; ty_wf_E := ty_wf_E ty ++ ty_outlives_E ty α }.

  Global Instance ref_type_contractive α : TypeContractive (ref α).
  Proof. solve_type_proper. Qed.
  Global Instance ref_ne α : NonExpansive (ref α).
  Proof. apply type_contractive_ne, _. Qed.

  Global Instance ref_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> subtype E L ==> subtype E L) ref.
  Proof.
    iIntros (α1 α2 Hα ty1 ty2 Hty qmax qL) "HL".
    iDestruct (Hty with "HL") as "#Hty". iDestruct (Hα with "HL") as "#Hα".
    iIntros "!> #HE". iDestruct ("Hα" with "HE") as %Hα1α2.
    iDestruct ("Hty" with "HE") as "(%&#Ho&#Hs)". iSplit; [|iSplit; iModIntro].
    - done.
    - iIntros (tid [|[[]| | |][|[[]| | |][]]]) "H"=>//=.
      iDestruct "H" as (ν q' γ β ty') "(#Hshr & #H⊑ & #Hinv & Htok & Hown)".
      iExists ν, q', γ, β, ty'. iFrame "∗#". iSplit.
      + iApply ty_shr_mono; last by iApply "Hs".
        iApply lft_intersect_mono; first by iApply lft_incl_syn_sem. iApply lft_incl_refl.
      + iApply lft_incl_trans; first by iApply lft_incl_syn_sem. done.
    - iIntros (κ tid l) "H /=". iDestruct "H" as (ν q' γ β ty' lv lrc) "H".
      iExists ν, q', γ, β, ty', lv, lrc. iDestruct "H" as "#($&$&?&?&$&$)". iSplit.
      + iApply ty_shr_mono; last by iApply "Hs".
        iApply lft_intersect_mono; first by iApply lft_incl_syn_sem. iApply lft_incl_refl.
      + iApply lft_incl_trans; first by iApply lft_incl_syn_sem. done.
  Qed.
  Global Instance ref_mono_flip E L :
    Proper (lctx_lft_incl E L ==> flip (subtype E L) ==> flip (subtype E L)) ref.
  Proof. intros ??????. by apply ref_mono. Qed.
  Lemma ref_mono' E L α1 α2 ty1 ty2 :
    lctx_lft_incl E L α2 α1 → subtype E L ty1 ty2 →
    subtype E L (ref α1 ty1) (ref α2 ty2).
  Proof. intros. by eapply ref_mono. Qed.
  Global Instance ref_proper E L :
    Proper (lctx_lft_eq E L ==> eqtype E L ==> eqtype E L) ref.
  Proof. intros ??[]?? EQ. split; apply ref_mono'; try done; apply EQ. Qed.
  Lemma ref_proper' E L α1 α2 ty1 ty2 :
    lctx_lft_eq E L α1 α2 → eqtype E L ty1 ty2 →
    eqtype E L (ref α1 ty1) (ref α2 ty2).
  Proof. intros. by eapply ref_proper. Qed.
End ref.

Global Hint Resolve refcell_mono' refcell_proper' : lrust_typing.
