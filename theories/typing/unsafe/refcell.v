From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth csum frac agree.
From iris.base_logic Require Import big_op fractional.
From lrust.lang Require Import memcpy.
From lrust.lifetime Require Import na_borrow.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
Set Default Proof Using "Type".

Definition refcell_stR :=
  optionUR (csumR (exclR unitC) (prodR (prodR (agreeR (leibnizC lft)) fracR) posR)).
Class refcellG Σ :=
  RefCellG :> inG Σ (authR refcell_stR).

Definition Z_of_refcell_st (st : refcell_stR) : Z :=
  match st with
  | None => 0
  | Some (Cinr (_, _, n)) => Zpos n
  | Some _ => -1
  end.

Definition reading_st (q : frac) (κ : lft) : refcell_stR :=
  Some (Cinr (to_agree (κ : leibnizC lft), q, xH)).
Definition writing_st : refcell_stR := Some (Cinl (Excl ())).

Definition refcellN := nroot .@ "refcell".
Definition refcell_invN := refcellN .@ "inv".

Section refcell_inv.
  Context `{typeG Σ, refcellG Σ}.

  Definition refcell_inv tid (l : loc) (γ : gname) (α : lft) ty : iProp Σ :=
    (∃ st, l ↦ #(Z_of_refcell_st st) ∗ own γ (● st) ∗
      match st return _ with
      | None => &{α}(shift_loc l 1 ↦∗: ty.(ty_own) tid)
      | Some (Cinr ({|agree_car := ν|}, q, n)) =>
        ∃ q', ⌜(q + q')%Qp = 1%Qp⌝ ∗ q'.[ν] ∗
              ty.(ty_shr) (α ∪ ν) tid (shift_loc l 1) ∗
              ([†ν] ={lftE}=∗ &{α}(shift_loc l 1 ↦∗: ty.(ty_own) tid))
      | Some _ => True
      end)%I.

  Global Instance refcell_inv_ne n tid l γ α :
    Proper (dist n ==> dist n) (refcell_inv tid l γ α).
  Proof.
    intros ty1 ty2 Hty. unfold refcell_inv.
    repeat (f_contractive || f_equiv || apply Hty).
  Qed.

  Lemma refcell_inv_proper E L tid l γ α1 α2 ty1 ty2 :
    lctx_lft_incl E L α2 α1 → eqtype E L ty1 ty2 →
    lft_ctx -∗ elctx_interp_0 E -∗ ⌜llctx_interp_0 L⌝ -∗
    refcell_inv tid l γ α1 ty1 -∗ refcell_inv tid l γ α2 ty2.
  Proof.
    (* TODO : this proof is essentially [solve_proper], but within the logic.
              It would easily gain from some automation. *)
    iIntros (Hα Hty%eqtype_unfold) "#LFT #HE #HL H". unfold refcell_inv.
    iDestruct (Hty with "LFT HE HL") as "(% & Hown & Hshr)".
    iAssert (□ (&{α1} shift_loc l 1 ↦∗: ty_own ty1 tid -∗
                &{α2} shift_loc l 1 ↦∗: ty_own ty2 tid))%I with "[]" as "#Hb".
    { iIntros "!# H". iApply (bor_shorten with "[]"). by iApply Hα.
      iApply bor_iff_proper; last done.
      iSplit; iIntros "!>!#H"; iDestruct "H" as (vl) "[Hf H]"; iExists vl;
      iFrame; by iApply "Hown". }
    iDestruct "H" as (st) "H"; iExists st;
      iDestruct "H" as "($&$&H)"; destruct st as [[|[[[]]]|]|]; try done;
      last by iApply "Hb".
    iDestruct "H" as (q') "(Heq & Htok & Hs & H†)". iExists q'. iFrame. iSplitL "Hs".
    - iApply (ty_shr_mono); first done; last by iApply "Hshr".
      by iApply lft_glb_mono; [iApply Hα|iApply lft_incl_refl].
    - iIntros "?". iApply ("Hb" with ">"). by iApply "H†".
  Qed.
End refcell_inv.

Section refcell.
  Context `{typeG Σ, refcellG Σ}.

  Program Definition refcell (ty : type) :=
    {| ty_size := S ty.(ty_size);
       ty_own tid vl :=
         match vl return _ with
         | #(LitInt z) :: vl' => ⌜-1 ≤ z⌝ ∗ ty.(ty_own) tid vl'
         | _ => False
         end%I;
       ty_shr κ tid l :=
         (∃ α γ, κ ⊑ α ∗ &na{α, tid, refcell_invN}(refcell_inv tid l γ α ty))%I |}.
  Next Obligation.
    iIntros (??[|[[]|]]); try iIntros "[]". rewrite ty_size_eq.
    iIntros "[_ %]!%/=". congruence.
  Qed.
  Next Obligation.
    iIntros (ty E κ l tid q ?) "#LFT Hb Htok".
    iMod (bor_acc_cons with "LFT Hb Htok") as "[H Hclose]". done.
    iDestruct "H" as ([|[[| |n]|]vl]) "[H↦ H]"; try iDestruct "H" as ">[]".
    iDestruct "H" as "[>% Hown]".
    iMod ("Hclose" $! ((∃ n:Z, l ↦ #n ∗ ⌜-1 ≤ n⌝) ∗
            shift_loc l 1 ↦∗: ty.(ty_own) tid) with "[-] []")%I as "[H [Htok Htok']]".
    { iNext. rewrite heap_mapsto_vec_cons. iDestruct "H↦" as "[Hn Hvl]".
      iSplitL "Hn"; [eauto|iExists _; iFrame]. }
    { iIntros "!> [Hn Hvl] !>". iDestruct "Hn" as (n') "[Hn >%]".
      iDestruct "Hvl" as (vl') "[H↦ Hvl]".
      iExists (#n'::vl'). rewrite heap_mapsto_vec_cons. iFrame "∗%". }
    iMod (bor_sep with "LFT H") as "[Hn Hvl]". done.
    iMod (bor_acc_cons with "LFT Hn Htok") as "[H Hclose]". done.
    iAssert ((q / 2).[κ] ∗ ▷ ∃ γ, refcell_inv tid l γ κ ty)%I with ">[-Hclose]"
      as "[$ HQ]"; last first.
    { iMod ("Hclose" with "* HQ []") as "[Hb $]".
      - iIntros "!> H !>". iNext. iDestruct "H" as (γ st) "(? & _ & _)".
        iExists _. iIntros "{$H}!%". destruct st as [[|[[]?]|]|]; simpl; lia.
      - iMod (bor_exists with "LFT Hb") as (γ) "Hb". done.
        iExists κ, γ. iSplitR. by iApply lft_incl_refl. by iApply bor_na. }
    clear dependent n. iDestruct "H" as ([|n|[]]) "[Hn >%]"; try lia.
    - iFrame. iMod (own_alloc (● None)) as (γ) "Hst". done. iExists γ, None. by iFrame.
    - iMod (lft_create with "LFT") as (ν) "[[Htok1 Htok2] _]". done.
      iMod (own_alloc
         (● Some (Cinr (to_agree (ν : leibnizC _), (1/2)%Qp, n)))) as (γ) "Hst".
      { by apply auth_auth_valid. }
      destruct (Qp_lower_bound (1/2) (q/2)) as (q' & q1 & q2 & H12 & ->). rewrite H12.
      iDestruct "Htok'" as "[Htok' $]". iDestruct "Htok1" as "[Htok1 Htok1']".
      iApply (fupd_mask_mono lftE). done.
      iMod (rebor _ _ (κ ∪ ν) with "LFT [] Hvl") as "[Hvl Hh]". done.
      { iApply lft_le_incl. apply gmultiset_union_subseteq_l. }
      iMod (ty_share _ _ (κ ∪ ν) _ _ q' with "LFT Hvl [Htok' Htok1]")
        as "[Hshr Htok]". done.
      { rewrite -lft_tok_sep. iFrame. }
      rewrite -lft_tok_sep. iDestruct "Htok" as "[$ Htok]".
      iExists γ, _. iFrame "Hst Hn". iExists _. iIntros "{$Htok2 $Hshr}!>!>".
      rewrite -H12 Qp_div_2. iSplit; first done. iIntros "H†". iApply "Hh".
      rewrite -lft_dead_or. auto.
    - iMod (own_alloc (● Some (Cinl (Excl ())))) as (γ) "Hst".
      { by apply auth_auth_valid. }
      iFrame. iExists _, _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (?????) "LFT #Hκ H". iDestruct "H" as (α γ) "[#??]".
    iExists _, _. iFrame. iApply lft_incl_trans; auto.
  Qed.

  Global Instance refcell_ne n : Proper (dist n ==> dist n) refcell.
  Proof.
    move=>ty1 ty2 Hty. split; [split|]; simpl.
    - f_equiv. apply Hty.
    - f_contractive=>tid vl. repeat f_equiv. apply Hty.
    - intros κ tid l. by repeat f_equiv.
  Qed.

  Global Instance refcell_mono E L : Proper (eqtype E L ==> subtype E L) refcell.
  Proof.
    (* TODO : this proof is essentially [solve_proper], but within the logic.
              It would easily gain from some automation. *)
    iIntros (ty1 ty2 EQ) "#LFT #HE #HL". pose proof EQ as EQ'%eqtype_unfold.
    iDestruct (EQ' with "LFT HE HL") as "(% & #Hown & #Hshr)".
    iSplit; [|iSplit; iIntros "!# * H"].
    - iPureIntro. simpl. congruence.
    - destruct vl as [|[[]|]]; try done. iDestruct "H" as "[$ H]". by iApply "Hown".
    - iDestruct "H" as (a γ) "[Ha H]". iExists a, γ. iFrame.
      iApply na_bor_iff_proper; last done.
      iSplit; iIntros "!>!# H"; by iApply refcell_inv_proper.
  Qed.
  Lemma refcell_mono' E L ty1 ty2 :
    eqtype E L ty1 ty2 → subtype E L (refcell ty1) (refcell ty2).
  Proof. eapply refcell_mono. Qed.
  Global Instance refcell_proper E L : Proper (eqtype E L ==> eqtype E L) refcell.
  Proof. by split; apply refcell_mono. Qed.
  Lemma refcell_proper' E L ty1 ty2 :
    eqtype E L ty1 ty2 → eqtype E L (refcell ty1) (refcell ty2).
  Proof. eapply refcell_proper. Qed.

  Global Instance refcell_send :
    Send ty → Send (refcell ty).
  Proof. move=>????[|[[]|]]//=??. iIntros "[$?]". by iApply send_change_tid. Qed.
End refcell.

Definition refcell_refN := refcellN .@ "ref".

Section ref.
  Context `{typeG Σ, refcellG Σ}.

  Program Definition ref (α : lft) (ty : type) :=
    {| ty_size := 2;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc lv);  #(LitLoc lrc) ] =>
           ∃ ν q γ β ty', ty.(ty_shr) (α ∪ ν) tid lv ∗
             α ⊑ β ∗ &na{β, tid, refcell_invN}(refcell_inv tid lrc γ β ty') ∗
             q.[ν] ∗ own γ (◯ reading_st q ν)
         | _ => False
         end;
       ty_shr κ tid l :=
          ∃ ν q γ β ty' (lv lrc : loc),
             κ ⊑ ν ∗ &frac{κ} (λ q, l↦∗{q} [ #lv; #lrc]) ∗
             ▷ ty.(ty_shr) (α ∪ ν) tid lv ∗
             ▷ (α ⊑ β) ∗ ▷ &na{β, tid, refcell_invN}(refcell_inv tid lrc γ β ty') ∗
             &na{κ, tid, refcell_refN}(own γ (◯ reading_st q ν)) |}%I.
  Next Obligation.
    iIntros (???[|[[]|][|[[]|][]]]); try iIntros "[]". by iIntros "_".
  Qed.
  Next Obligation.
    iIntros (α ty E κ l tid q ?) "#LFT Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb". done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]". done.
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦". done.
    destruct vl as [|[[|lv|]|][|[[|lrc|]|][]]];
      try by iMod (bor_persistent_tok with "LFT Hb Htok") as "[>[] _]".
    iMod (bor_exists with "LFT Hb") as (ν) "Hb". done.
    iMod (bor_exists with "LFT Hb") as (q') "Hb". done.
    iMod (bor_exists with "LFT Hb") as (γ) "Hb". done.
    iMod (bor_exists with "LFT Hb") as (β) "Hb". done.
    iMod (bor_exists with "LFT Hb") as (ty') "Hb". done.
    iMod (bor_sep with "LFT Hb") as "[Hshr Hb]". done.
    iMod (bor_persistent_tok with "LFT Hshr Htok") as "[#Hshr Htok]". done.
    iMod (bor_sep with "LFT Hb") as "[Hαβ Hb]". done.
    iMod (bor_persistent_tok with "LFT Hαβ Htok") as "[#Hαβ Htok]". done.
    iMod (bor_sep with "LFT Hb") as "[Hinv Hb]". done.
    iMod (bor_persistent_tok with "LFT Hinv Htok") as "[#Hinv $]". done.
    iMod (bor_sep with "LFT Hb") as "[Hκν Hb]". done.
    (* FIXME : I cannot write #Hκν directly. *)
    iDestruct (frac_bor_lft_incl with "LFT >[Hκν]") as "Hκν";
      last iDestruct "Hκν" as "#Hκν".
    { iApply bor_fracture; try done. by rewrite Qp_mult_1_r. }
    iMod (bor_na with "Hb") as "#Hb". done. eauto 20.
  Qed.
  Next Obligation.
    iIntros (??????) "#? #? H". iDestruct "H" as (ν q γ β ty' lv lrc) "H".
    iExists _, _, _, _, _, _, _. iDestruct "H" as "#(? & ? & $ & $ & $ & ?)".
    iSplit; last iSplit.
    - by iApply lft_incl_trans.
    - by iApply frac_bor_shorten.
    - by iApply na_bor_shorten.
  Qed.

  Global Instance ref_contractive α : Contractive (ref α).
  Proof.
    intros n ?? EQ. unfold ref. split; [split|]=>//=.
    - f_contractive=>tid vl. repeat (f_contractive || f_equiv). apply EQ.
    - intros κ tid l. repeat (f_contractive || f_equiv). apply EQ.
  Qed.
  Global Instance ref_ne n α : Proper (dist n ==> dist n) (ref α).
  Proof. apply contractive_ne, _. Qed.

  Global Instance ref_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> subtype E L ==> subtype E L) ref.
  Proof.
    iIntros (α1 α2 Hα ty1 ty2 Hty) "#LFT #HE #HL".
    iDestruct (Hty with "LFT HE HL") as "(%&#Ho&#Hs)".
    iDestruct (Hα with "HE HL") as "Hα1α2".
    iSplit; [|iSplit; iAlways].
    - done.
    - iIntros (tid [|[[]|][|[[]|][]]]); try iIntros "[]". iIntros "H".
      iDestruct "H" as (ν q γ β ty') "(#Hshr & #H⊑ & #Hinv & Htok & Hown)".
      iExists ν, q, γ, β, ty'. iFrame "∗#". iSplit.
      + iApply ty_shr_mono; last by iApply "Hs". done.
        iApply lft_glb_mono. done. iApply lft_incl_refl.
      + by iApply lft_incl_trans.
    - iIntros (κ tid l) "H". iDestruct "H" as (ν q γ β ty' lv lrc) "H".
      iExists ν, q, γ, β, ty', lv, lrc. iDestruct "H" as "#($&$&?&?&$&$)". iSplit.
      + iApply ty_shr_mono; last by iApply "Hs". done.
        iApply lft_glb_mono. done. iApply lft_incl_refl.
      + by iApply lft_incl_trans.
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

Definition refcell_refmutN := refcellN .@ "refmut".

Section refmut.
  Context `{typeG Σ, refcellG Σ}.
  Local Hint Extern 1000 (_ ⊆ _) => set_solver : ndisj.

  Program Definition refmut (α : lft) (ty : type) :=
    {| ty_size := 2;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc lv);  #(LitLoc lrc) ] =>
           ∃ γ β ty', &{β}(lv ↦∗: ty.(ty_own) tid) ∗
             α ⊑ β ∗ &na{β, tid, refcell_invN}(refcell_inv tid lrc γ β ty') ∗
             own γ (◯ writing_st)
         | _ => False
         end;
       ty_shr κ tid l :=
         ∃ (lv lrc : loc),
           &frac{κ} (λ q, l↦∗{q} [ #lv; #lrc]) ∗
           □ ∀ F q, ⌜↑shrN ∪ lftE ⊆ F⌝ -∗ q.[α ∪ κ]
             ={F, F∖↑shrN∖↑lftN}▷=∗ ty.(ty_shr) (α ∪ κ) tid lv ∗ q.[α ∪ κ] |}%I.
  Next Obligation.
    iIntros (???[|[[]|][|[[]|][]]]); try iIntros "[]". by iIntros "_".
  Qed.
  Next Obligation.
    iIntros (α ty E κ l tid q HE) "#LFT Hb Htok".
    iMod (bor_exists with "LFT Hb") as (vl) "Hb". done.
    iMod (bor_sep with "LFT Hb") as "[H↦ Hb]". done.
    iMod (bor_fracture (λ q, l ↦∗{q} vl)%I with "LFT H↦") as "#H↦". done.
    destruct vl as [|[[|lv|]|][|[[|lrc|]|][]]];
      try by iMod (bor_persistent_tok with "LFT Hb Htok") as "[>[] _]".
    iMod (bor_exists with "LFT Hb") as (γ) "Hb". done.
    iMod (bor_exists with "LFT Hb") as (β) "Hb". done.
    iMod (bor_exists with "LFT Hb") as (ty') "Hb". done.
    rewrite (assoc _ _ (α ⊑ β)%I). iMod (bor_sep with "LFT Hb") as "[Hb _]". done.
    iMod (bor_sep with "LFT Hb") as "[Hb Hαβ]". done.
    iMod (bor_persistent_tok with "LFT Hαβ Htok") as "[#Hαβ $]". done.
    iExists _, _. iFrame "H↦". rewrite {1}bor_unfold_idx.
    iDestruct "Hb" as (i) "[#Hpb Hpbown]".
    iMod (inv_alloc shrN _ (idx_bor_own 1 i ∨ ty_shr ty (α ∪ κ) tid lv)%I
          with "[Hpbown]") as "#Hinv"; first by eauto.
    iIntros "!> !# * % Htok". clear HE.
    iMod (inv_open with "Hinv") as "[INV Hclose]". set_solver.
    iDestruct "INV" as "[>Hbtok|#Hshr]".
    - iMod (bor_unnest with "LFT [Hbtok]") as "Hb". solve_ndisj.
      { iApply bor_unfold_idx. eauto. }
      iModIntro. iNext. iMod "Hb".
      iMod (ty.(ty_share) with "LFT [Hb] Htok") as "[#Hshr $]". solve_ndisj.
      { iApply bor_shorten; last done. iApply lft_glb_mono. done. iApply lft_incl_refl. }
      iMod ("Hclose" with "[]") as "_"; auto.
    - iMod ("Hclose" with "[]") as "_". by eauto.
      iApply step_fupd_intro. set_solver. auto.
  Qed.
  Next Obligation.
    iIntros (??????) "#? #? H". iDestruct "H" as (lv lrc) "[#Hf #H]".
    iExists _, _. iSplit.
    - by iApply frac_bor_shorten.
    - iIntros "!# * % Htok".
      iMod (lft_incl_acc with "[] Htok") as (q') "[Htok Hclose]". set_solver.
      { iApply lft_glb_mono. iApply lft_incl_refl. done. }
      iMod ("H" with "* [] Htok") as "Hshr". done. iModIntro. iNext.
      iMod "Hshr" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
      iApply ty_shr_mono; try done. iApply lft_glb_mono. iApply lft_incl_refl. done.
  Qed.

  Global Instance refmut_contractive α : Contractive (refmut α).
  Proof.
    intros n ?? EQ. unfold refmut. split; [split|]=>//=.
    - f_contractive=>tid vl. repeat (f_contractive || f_equiv). apply EQ.
    - intros κ tid l. repeat (f_contractive || f_equiv). apply EQ.
  Qed.
  Global Instance refmut_ne n α : Proper (dist n ==> dist n) (refmut α).
  Proof. apply contractive_ne, _. Qed.

  Global Instance refmut_mono E L :
    Proper (flip (lctx_lft_incl E L) ==> eqtype E L ==> subtype E L) refmut.
  Proof.
    iIntros (α1 α2 Hα ty1 ty2 Hty) "#LFT #HE #HL".
    pose proof Hty as Hty'%eqtype_unfold.
    iDestruct (Hty' with "LFT HE HL") as "(%&#Ho&#Hs)".
    iDestruct (Hα with "HE HL") as "Hα1α2".
    iSplit; [|iSplit; iAlways].
    - done.
    - iIntros (tid [|[[]|][|[[]|][]]]); try iIntros "[]". iIntros "H".
      iDestruct "H" as (γ β ty') "(Hb & #H⊑ & #Hinv & Hown)".
      iExists γ, β, ty'. iFrame "∗#". iSplit.
      + iApply bor_iff_proper; last done.
        iSplit; iIntros "!>!# H"; iDestruct "H" as (vl) "[??]";
          iExists vl; iFrame; by iApply "Ho".
      + by iApply lft_incl_trans.
    - iIntros (κ tid l) "H". iDestruct "H" as (lv lrc) "H". iExists lv, lrc.
      iDestruct "H" as "[$ #H]". iIntros "!# * % Htok".
      iMod (lft_incl_acc with "[] Htok") as (q') "[Htok Hclose]". set_solver.
      { iApply lft_glb_mono. done. iApply lft_incl_refl. }
      iMod ("H" with "* [] Htok") as "Hshr". done. iModIntro. iNext.
      iMod "Hshr" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
      iApply ty_shr_mono; try done. iApply lft_glb_mono. done. iApply lft_incl_refl.
      by iApply "Hs".
  Qed.
  Global Instance refmut_mono_flip E L :
    Proper (lctx_lft_incl E L ==> eqtype E L ==> flip (subtype E L)) refmut.
  Proof. intros ??????. by apply refmut_mono. Qed.
  Lemma refmut_mono' E L α1 α2 ty1 ty2 :
    lctx_lft_incl E L α2 α1 → eqtype E L ty1 ty2 →
    subtype E L (refmut α1 ty1) (refmut α2 ty2) .
  Proof. intros. by eapply refmut_mono. Qed.
  Global Instance refmut_proper E L :
    Proper (lctx_lft_eq E L ==> eqtype E L ==> eqtype E  L) refmut.
  Proof. intros ??[]???. split; by apply refmut_mono'. Qed.
  Lemma refmut_proper' E L α1 α2 ty1 ty2 :
    lctx_lft_eq E L α1 α2 → eqtype E L ty1 ty2 →
    eqtype E L (ref α1 ty1) (ref α2 ty2).
  Proof. intros. by eapply ref_proper. Qed.
End refmut.

Hint Resolve refcell_mono' refcell_proper' ref_mono' ref_proper'
             refmut_mono' refmut_proper' : lrust_typing.

(* Section refcell_functions. *)
(*   Context `{typeG Σ, refcellG Σ}. *)

(*   (* Constructing a cell. *) *)
(*   Definition refcell_new ty : val := *)
(*     funrec: <> ["x"] := *)
(*       let: "r" := new [ #(S ty.(ty_size))] in *)
(*       "r" +ₗ #0 <- #0;; *)
(*       "r" +ₗ #1 <-{ty.(ty_size)} !"x";; *)
(*       "k" ["r"] *)
(*       cont: "k" ["r"] := *)
(*         delete [ #ty.(ty_size) ; "x"];; "return" ["r"]. *)

(*   Lemma refcell_new_type ty : *)
(*     typed_instruction_ty [] [] [] (refcell_new ty) *)
(*         (fn (λ _, [])%EL (λ _, [# ty]) (λ _:(), refcell ty)). *)
(*   Proof. *)
(*     apply type_fn; [apply _..|]. move=>/= _ ret arg. inv_vec arg=>x. simpl_subst. *)
(*     eapply (type_cont [_] [] *)
(*          (λ r, [x ◁ box (uninit ty.(ty_size)); r!!!0 ◁ box (refcell ty)])%TC); *)
(*       [solve_typing..| |]; last first. *)
(*     - simpl. intros k arg. inv_vec arg=>r. simpl_subst. *)
(*       eapply type_delete; [solve_typing..|]. *)
(*       eapply (type_jump [_]); solve_typing. *)
(*     - intros k. simpl_subst. eapply type_new; [solve_typing..|]. *)
(*       iIntros (r) "!# * #HEAP #LFT Hna HE _ Hk HT". simpl_subst. *)
(*       rewrite (Nat2Z.id (S ty.(ty_size))) tctx_interp_cons *)
(*               tctx_interp_singleton !tctx_hasty_val. *)
(*       iDestruct "HT" as "[Hr Hx]". *)
(*       destruct x as [[]|]; try iDestruct "Hx" as "[]". iDestruct "Hx" as "[Hx Hx†]". *)
(*       destruct r as [[]|]; try iDestruct "Hr" as "[]". iDestruct "Hr" as "[Hr Hr†]". *)
(*       iDestruct "Hr" as (vl) "Hr". rewrite uninit_own. iDestruct "Hr" as "[Hr↦ >%]". *)
(*       destruct vl as [|]; try done. rewrite heap_mapsto_vec_cons. *)
(*       iDestruct "Hr↦" as "[Hr↦0 Hr↦1]". wp_op. rewrite shift_loc_0. wp_write. *)

(* etrans. admit. apply wp_lam. wp_done. apply _. wp_done. *)
(* wp_seq. *)

(*  simpl *)

(*  simpl. *)
(* simpl. *)
(*       simpl_subst. *)

(*     eapply type_new; [solve_typing..|]=>r. simpl_subst. *)

(*     eapply (type_jump [_]); first solve_typing. *)
(*     iIntros (???) "#LFT $ $ Hty". rewrite !tctx_interp_singleton /=. done. *)
(*   Qed. *)