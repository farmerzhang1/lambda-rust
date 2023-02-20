From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth csum frac agree excl numbers.
From iris.bi Require Import fractional.
From lrust.lifetime Require Import at_borrow.
From lrust.typing Require Import typing.
From iris.prelude Require Import options.

Definition rwlock_stR :=
  optionUR (csumR (exclR unitO) (prodR (prodR (agreeR lftO) fracR) positiveR)).
Class rwlockG Σ :=
  RwLockG :> inG Σ (authR rwlock_stR).
Definition rwlockΣ : gFunctors := #[GFunctor (authR rwlock_stR)].
Global Instance subG_rwlockΣ {Σ} : subG rwlockΣ Σ → rwlockG Σ.
Proof. solve_inG. Qed.

Definition Z_of_rwlock_st (st : rwlock_stR) : Z :=
  match st with
  | None => 0
  | Some (Cinr (_, _, n)) => Zpos n
  | Some _ => -1
  end.

Definition reading_st (q : frac) (ν : lft) : rwlock_stR :=
  Some (Cinr (to_agree ν, q, xH)).
Definition writing_st : rwlock_stR :=
  Some (Cinl (Excl ())).

Definition rwlockN := lrustN .@ "rwlock".

Section rwlock_inv.
  Context `{!typeGS Σ, !rwlockG Σ}.

  Definition rwlock_inv tid_own tid_shr (l : loc) (γ : gname) (α : lft) ty
    : iProp Σ :=
    (∃ st, l ↦ #(Z_of_rwlock_st st) ∗ own γ (● st) ∗
      match st return _ with
      | None =>
        (* Not locked. *)
        &{α}((l +ₗ 1) ↦∗: ty.(ty_own) tid_own)
      | Some (Cinr (agν, q, n)) =>
        (* Locked for read. *)
        ∃ (ν : lft) q', agν ≡ to_agree ν ∗
                □ (1.[ν] ={↑lftN ∪ lft_userE}[lft_userE]▷=∗ [†ν]) ∗
                ([†ν] ={↑lftN}=∗ &{α}((l +ₗ 1) ↦∗: ty.(ty_own) tid_own)) ∗
                ty.(ty_shr) (α ⊓ ν) tid_shr (l +ₗ 1) ∗
                ⌜(q + q')%Qp = 1%Qp⌝ ∗ q'.[ν]
      | _ => (* Locked for write. *) True
      end)%I.

  Global Instance rwlock_inv_type_ne n tid_own tid_shr l γ α :
    Proper (type_dist2 n ==> dist n) (rwlock_inv tid_own tid_shr l γ α).
  Proof.
    solve_proper_core
      ltac:(fun _ => exact: type_dist2_S || f_type_equiv || f_contractive || f_equiv).
  Qed.

  Global Instance rwlock_inv_ne tid_own tid_shr l γ α :
    NonExpansive (rwlock_inv tid_own tid_shr l γ α).
  Proof.
    intros n ???. eapply rwlock_inv_type_ne, type_dist_dist2. done.
  Qed.

  Lemma rwlock_inv_proper E L ty1 ty2 qmax qL :
    eqtype E L ty1 ty2 →
    llctx_interp_noend qmax L qL -∗ ∀ tid_own tid_shr l γ α, □ (elctx_interp E -∗
    rwlock_inv tid_own tid_shr l γ α ty1 -∗
    rwlock_inv tid_own tid_shr l γ α ty2).
  Proof.
    (* TODO : this proof is essentially [solve_proper], but within the logic.
              It would easily gain from some automation. *)
    rewrite eqtype_unfold. iIntros (Hty) "HL".
    iDestruct (Hty with "HL") as "#Hty". iIntros "%tid_own %tid_shr %l %γ %α !> #HE H".
    iDestruct ("Hty" with "HE") as "(% & #Hown & #Hshr)".
    iAssert (□ (&{α}((l +ₗ 1) ↦∗: ty_own ty1 tid_own) -∗
                &{α}((l +ₗ 1) ↦∗: ty_own ty2 tid_own)))%I as "#Hb".
    { iIntros "!> H". iApply bor_iff; last done.
      iNext; iModIntro; iSplit; iIntros "H"; iDestruct "H" as (vl) "[Hf H]"; iExists vl;
      iFrame; by iApply "Hown". }
    iDestruct "H" as (st) "H"; iExists st;
      iDestruct "H" as "($&$&H)"; destruct st as [[|[[agν ?]?]|]|]; try done;
      last by iApply "Hb".
    iDestruct "H" as (ν q') "(Hag & #Hend & Hh & ? & ? & ?)". iExists ν, q'.
    iFrame. iSplitR; first done. iSplitL "Hh"; last by iApply "Hshr".
    iIntros "Hν". iApply "Hb". iApply ("Hh" with "Hν").
  Qed.

  Lemma rwlock_inv_change_tid_own tid_own1 tid_own2 tid_shr l γ α ty :
    Send ty →
    rwlock_inv tid_own1 tid_shr l γ α ty ≡ rwlock_inv tid_own2 tid_shr l γ α ty.
  Proof.
    intros ?. apply bi.exist_proper=>?; do 7 f_equiv; first do 7 f_equiv.
    - do 5 f_equiv. iApply send_change_tid'.
    - iApply send_change_tid'.
  Qed.

  Lemma rwlock_inv_change_tid_shr tid_own tid_shr1 tid_shr2 l γ α ty :
    Sync ty →
    rwlock_inv tid_own tid_shr1 l γ α ty ≡ rwlock_inv tid_own tid_shr2 l γ α ty.
  Proof.
    intros ?. apply bi.exist_proper=>?; do 7 f_equiv; first do 7 f_equiv.
    iApply sync_change_tid'.
  Qed.
End rwlock_inv.

Section rwlock.
  Context `{!typeGS Σ, !rwlockG Σ}.

  (* Original Rust type (we ignore poisoning):
     pub struct RwLock<T: ?Sized> {
         inner: Box<sys::RWLock>,
         poison: poison::Flag,
         data: UnsafeCell<T>,
     }
  *)

  Program Definition rwlock (ty : type) :=
    {| ty_size := S ty.(ty_size);
       ty_own tid vl :=
         match vl return _ with
         | #(LitInt z) :: vl' => ⌜-1 ≤ z⌝ ∗ ty.(ty_own) tid vl'
         | _ => False
         end%I;
       ty_shr κ tid l :=
         (∃ α γ, κ ⊑ α ∗ &at{α,rwlockN}(rwlock_inv tid tid l γ α ty))%I |}.
  Next Obligation.
    iIntros (??[|[[]| | |]]); try iIntros "[]". rewrite ty_size_eq.
    iIntros "[_ %] !% /=". congruence.
  Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT Hb Htok".
    iMod (bor_acc_cons with "LFT Hb Htok") as "[H Hclose]"; first done.
    iDestruct "H" as ([|[[| |n]| | |]vl]) "[H↦ H]"; try iDestruct "H" as ">[]".
    iDestruct "H" as "[>% Hown]".
    iMod ("Hclose" $! ((∃ n:Z, l ↦ #n ∗ ⌜-1 ≤ n⌝) ∗
            (l +ₗ 1) ↦∗: ty.(ty_own) tid) with "[] [-]")%I as "[H [Htok Htok']]".
    { iIntros "!> [Hn Hvl] !>". iDestruct "Hn" as (n') "[Hn >%]".
      iDestruct "Hvl" as (vl') "[H↦ Hvl]".
      iExists (#n'::vl'). rewrite heap_mapsto_vec_cons. iFrame "∗%". }
    { iNext. rewrite heap_mapsto_vec_cons. iDestruct "H↦" as "[Hn Hvl]".
      iSplitL "Hn"; [eauto|iExists _; iFrame]. }
    iMod (bor_sep with "LFT H") as "[Hn Hvl]"; first done.
    iMod (bor_acc_cons with "LFT Hn Htok") as "[H Hclose]"; first done.
    iAssert ((q / 2).[κ] ∗ ▷ ∃ γ, rwlock_inv tid tid l γ κ ty)%I with "[> -Hclose]"
      as "[$ HQ]"; last first.
    { iMod ("Hclose" with "[] HQ") as "[Hb $]".
      - iIntros "!> H !>". iNext. iDestruct "H" as (γ st) "(H & _ & _)".
        iExists _. iIntros "{$H}!%". destruct st as [[|[[]?]|]|]; simpl; lia.
      - iMod (bor_exists with "LFT Hb") as (γ) "Hb"; first done.
        iExists κ, γ. iSplitR; first by iApply lft_incl_refl. iApply bor_share; try done.
        solve_ndisj. }
    clear dependent n. iDestruct "H" as ([|n|[]]) "[Hn >%]"; try lia.
    - iFrame. iMod (own_alloc (● None)) as (γ) "Hst"; first by apply auth_auth_valid.
      iExists γ, None. by iFrame.
    - iMod (lft_create with "LFT") as (ν) "[[Htok1 Htok2] #Hhν]"; first done.
      iMod (own_alloc (● Some (Cinr (to_agree ν, (1/2)%Qp, n)))) as (γ) "Hst".
      { by apply auth_auth_valid. }
      iMod (rebor _ _ (κ ⊓ ν) with "LFT [] Hvl") as "[Hvl Hh]"; first done.
      { iApply lft_intersect_incl_l. }
      iDestruct (lft_intersect_acc with "Htok' Htok1") as (q') "[Htok Hclose]".
      iMod (ty_share with "LFT Hvl Htok") as "[Hshr Htok]"; first done.
      iDestruct ("Hclose" with "Htok") as "[$ Htok]".
      iExists γ, _. iFrame "Hst Hn". iExists _, _. iIntros "{$Hshr}".
      iSplitR; first by auto. iFrame "Htok2". iSplitR; first done.
      rewrite Qp.div_2.  iSplitL; last by auto.
      iIntros "!> !> Hν". iDestruct (lft_tok_dead with "Htok Hν") as "[]".
    - iMod (own_alloc (● writing_st)) as (γ) "Hst". { by apply auth_auth_valid. }
      iFrame. iExists _, _. eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (?????) "#Hκ H". iDestruct "H" as (α γ) "[#??]".
    iExists _, _. iFrame. iApply lft_incl_trans; auto.
  Qed.

  Global Instance rwlock_wf ty `{!TyWf ty} : TyWf (rwlock ty) :=
    { ty_lfts := ty_lfts ty; ty_wf_E := ty_wf_E ty }.

  Global Instance rwlock_type_ne : TypeNonExpansive rwlock.
  Proof.
    constructor;
      solve_proper_core ltac:(fun _ => exact: type_dist2_S || (eapply rwlock_inv_type_ne; try reflexivity) ||
                                              f_type_equiv || f_contractive || f_equiv).
  Qed.

  Global Instance rwlock_ne : NonExpansive rwlock.
  Proof.
    constructor; solve_proper_core ltac:(fun _ => (eapply ty_size_ne; try reflexivity) || f_equiv).
  Qed.

  Global Instance rwlock_mono E L : Proper (eqtype E L ==> subtype E L) rwlock.
  Proof.
    (* TODO : this proof is essentially [solve_proper], but within the logic.
              It would easily gain from some automation. *)
    iIntros (ty1 ty2 EQ qmax qL) "HL". generalize EQ. rewrite eqtype_unfold=>EQ'.
    iDestruct (EQ' with "HL") as "#EQ'".
    iDestruct (rwlock_inv_proper with "HL") as "#Hty1ty2"; first done.
    iDestruct (rwlock_inv_proper with "HL") as "#Hty2ty1"; first by symmetry.
    iIntros "!> #HE". iDestruct ("EQ'" with "HE") as "(% & #Hown & #Hshr)".
    iSplit; [|iSplit].
    - iPureIntro. simpl. congruence.
    - iIntros "!> %tid %vl H". destruct vl as [|[[]| | |]]; try done.
      iDestruct "H" as "[$ H]". by iApply "Hown".
    - iIntros "!> %α %tid %l H". simpl.
      iDestruct "H" as (a γ) "[Ha H]". iExists a, γ. iFrame.
      iApply at_bor_iff; last done. iNext; iModIntro; iSplit; iIntros "H".
      + by iApply "Hty1ty2".
      + by iApply "Hty2ty1".
  Qed.
  Lemma rwlock_mono' E L ty1 ty2 :
    eqtype E L ty1 ty2 → subtype E L (rwlock ty1) (rwlock ty2).
  Proof. eapply rwlock_mono. Qed.
  Global Instance rwlock_proper E L : Proper (eqtype E L ==> eqtype E L) rwlock.
  Proof. by split; apply rwlock_mono. Qed.
  Lemma rwlock_proper' E L ty1 ty2 :
    eqtype E L ty1 ty2 → eqtype E L (rwlock ty1) (rwlock ty2).
  Proof. eapply rwlock_proper. Qed.

  (* Apparently, we don't need to require ty to be sync,
     contrarily to Rust's implementation. *)
  Global Instance rwlock_send ty :
    Send ty → Send (rwlock ty).
  Proof. move=>???[|[[]| | |]]//=??. iIntros "[$?]". by iApply send_change_tid. Qed.

  Global Instance rwlock_sync ty :
    Send ty → Sync ty → Sync (rwlock ty).
  Proof.
    move=>??????/=. do 2 apply bi.exist_mono=>?. apply bi.sep_mono_r.
    apply bi.equiv_entails. f_equiv.
    by rewrite rwlock_inv_change_tid_own rwlock_inv_change_tid_shr.
  Qed.
End rwlock.

Global Hint Resolve rwlock_mono' rwlock_proper' : lrust_typing.
