From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth csum frac agree.
From iris.bi Require Import fractional.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Import typing.
From lrust.typing.lib.rwlock Require Import rwlock.
From iris.prelude Require Import options.

Section rwlockreadguard.
  Context `{!typeGS Σ, !rwlockG Σ}.

  (* Original Rust type:
    pub struct RwLockReadGuard<'a, T: ?Sized + 'a> {
        __lock: &'a RwLock<T>,
    }
  *)

  Program Definition rwlockreadguard (α : lft) (ty : type) :=
    {| ty_size := 1;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] =>
           ∃ ν q γ β tid_own, ty.(ty_shr) (α ⊓ ν) tid (l +ₗ 1) ∗
             α ⊑ β ∗ &at{β,rwlockN}(rwlock_inv tid_own tid l γ β ty) ∗
             q.[ν] ∗ own γ (◯ reading_st q ν) ∗
             (1.[ν] ={↑lftN ∪ lft_userE}[lft_userE]▷=∗ [†ν])
         | _ => False
         end;
       ty_shr κ tid l :=
         ∃ (l' : loc),
           &frac{κ} (λ q, l↦∗{q} [ #l']) ∗
           ▷ ty.(ty_shr) (α ⊓ κ) tid (l' +ₗ 1) |}%I.
  Next Obligation. intros α ty tid [|[[]| | |] []]; auto. Qed.
  Next Obligation.
    iIntros (α ty E κ l tid q ?) "#LFT Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]"; first done.
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦"; first done.
    destruct vl as [|[[|l'|]| | |][]];
      try by iMod (bor_persistent with "LFT Hb Htok") as "[>[] _]".
    iMod (bor_exists with "LFT Hb") as (ν) "Hb"; first done.
    iMod (bor_exists with "LFT Hb") as (q') "Hb"; first done.
    iMod (bor_exists with "LFT Hb") as (γ) "Hb"; first done.
    iMod (bor_exists with "LFT Hb") as (β) "Hb"; first done.
    iMod (bor_exists with "LFT Hb") as (tid_own) "Hb"; first done.
    iMod (bor_sep with "LFT Hb") as "[Hshr Hb]"; first done.
    iMod (bor_persistent with "LFT Hshr Htok") as "[#Hshr Htok]"; first done.
    iMod (bor_sep with "LFT Hb") as "[Hαβ Hb]"; first done.
    iMod (bor_persistent with "LFT Hαβ Htok") as "[#Hαβ Htok]"; first done.
    iMod (bor_sep with "LFT Hb") as "[Hinv Hb]"; first done.
    iMod (bor_persistent with "LFT Hinv Htok") as "[#Hinv $]"; first done.
    iMod (bor_sep with "LFT Hb") as "[Hκν _]"; first done.
    iDestruct (frac_bor_lft_incl with "LFT [> Hκν]") as "#Hκν".
    { iApply bor_fracture; try done. by rewrite Qp.mul_1_r. }
    iExists _. iFrame "#". iApply ty_shr_mono; last done.
    iApply lft_intersect_mono; last done. iApply lft_incl_refl.
  Qed.
  Next Obligation.
    iIntros (α ty κ κ' tid l) "#Hκ'κ H". iDestruct "H" as (l') "[#Hf #Hshr]".
    iExists l'. iSplit; first by iApply frac_bor_shorten.
    iApply ty_shr_mono; last done. iApply lft_intersect_mono; last done.
    iApply lft_incl_refl.
  Qed.

  Global Instance rwlockreadguard_wf α ty `{!TyWf ty} : TyWf (rwlockreadguard α ty) :=
    { ty_lfts := [α]; ty_wf_E := ty_wf_E ty ++ ty_outlives_E ty α }.

  Global Instance rwlockreadguard_type_contractive α : TypeContractive (rwlockreadguard α).
  Proof.
    constructor;
      solve_proper_core ltac:(fun _ => exact: type_dist2_S || (eapply rwlock_inv_type_ne; try reflexivity) ||
                                              f_type_equiv || f_contractive || f_equiv).
  Qed.
  Global Instance rwlockreadguard_ne α : NonExpansive (rwlockreadguard α).
  Proof. apply type_contractive_ne, _. Qed.

  (* The rust type is not covariant, although it probably could (cf. refcell).
     This would require changing the definition of the type, though. *)
  Global Instance rwlockreadguard_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> eqtype E L ==> subtype E L) rwlockreadguard.
  Proof.
    iIntros (α1 α2 Hα ty1 ty2 Hty qmax qL) "HL".
    iDestruct (proj1 Hty with "HL") as "#Hty". iDestruct (Hα with "HL") as "#Hα".
    iDestruct (rwlock_inv_proper with "HL") as "#Hty1ty2"; first done.
    iDestruct (rwlock_inv_proper with "HL") as "#Hty2ty1"; first by symmetry.
    iIntros "!> #HE". iDestruct ("Hα" with "HE") as %Hα1α2.
    iDestruct ("Hty" with "HE") as "(%&#Ho&#Hs)". iSplit; [|iSplit; iModIntro].
    - done.
    - iIntros (tid [|[[]| | |][]]) "H"; try done.
      iDestruct "H" as (ν q' γ β tid_own) "(#Hshr & #H⊑ & #Hinv & Htok & Hown)".
      iExists ν, q', γ, β, tid_own. iFrame "∗#". iSplit; last iSplit.
      + iApply ty_shr_mono; last by iApply "Hs".
        iApply lft_intersect_mono; first by iApply lft_incl_syn_sem. iApply lft_incl_refl.
      + iApply lft_incl_trans; first by iApply lft_incl_syn_sem. done.
      + iApply (at_bor_iff with "[] Hinv").
        iIntros "!> !>"; iSplit; iIntros "H". 
        * by iApply "Hty1ty2".
        * by iApply "Hty2ty1".
    - iIntros (κ tid l) "H". iDestruct "H" as (l') "[Hf Hshr]". iExists l'.
      iFrame. iApply ty_shr_mono; last by iApply "Hs".
      iApply lft_intersect_mono; first by iApply lft_incl_syn_sem. iApply lft_incl_refl.
  Qed.
  Global Instance rwlockreadguard_mono_flip E L :
    Proper (lctx_lft_incl E L ==> eqtype E L ==> flip (subtype E L))
           rwlockreadguard.
  Proof. intros ??????. by apply rwlockreadguard_mono. Qed.
  Lemma rwlockreadguard_mono' E L α1 α2 ty1 ty2 :
    lctx_lft_incl E L α2 α1 → eqtype E L ty1 ty2 →
    subtype E L (rwlockreadguard α1 ty1) (rwlockreadguard α2 ty2).
  Proof. intros. by eapply rwlockreadguard_mono. Qed.
  Global Instance rwlockreadguard_proper E L :
    Proper (lctx_lft_eq E L ==> eqtype E L ==> eqtype E L) rwlockreadguard.
  Proof. intros ??[]?? EQ. split; apply rwlockreadguard_mono'; try done; apply EQ. Qed.
  Lemma rwlockreadguard_proper' E L α1 α2 ty1 ty2 :
    lctx_lft_eq E L α1 α2 → eqtype E L ty1 ty2 →
    eqtype E L (rwlockreadguard α1 ty1) (rwlockreadguard α2 ty2).
  Proof. intros. by eapply rwlockreadguard_proper. Qed.

  (* Rust requires the type to also be Send.  Not sure why. *)
  Global Instance rwlockreadguard_sync α ty :
    Sync ty → Sync (rwlockreadguard α ty).
  Proof.
    move=>?????/=. apply bi.exist_mono=>?. by rewrite sync_change_tid.
  Qed.

  (* POSIX requires the unlock to occur from the thread that acquired
     the lock, so Rust does not implement Send for RwLockWriteGuard. We can
     prove this for our spinlock implementation, however. *)
  Global Instance rwlockreadguard_send α ty :
    Sync ty → Send (rwlockreadguard α ty).
  Proof.
    iIntros (??? [|[[]| | |][]]) "H"; try done. simpl. iRevert "H".
    iApply bi.exist_mono. iIntros (κ); simpl. apply bi.equiv_entails.
    repeat lazymatch goal with
           | |- (ty_shr _ _ _ _) ≡ (ty_shr _ _ _ _) => by apply sync_change_tid'
           | |- (rwlock_inv _ _ _ _ _ _) ≡ _ => by apply rwlock_inv_change_tid_shr
           | |- _ => f_equiv
           end.
  Qed.
End rwlockreadguard.

Global Hint Resolve rwlockreadguard_mono' rwlockreadguard_proper' : lrust_typing.
