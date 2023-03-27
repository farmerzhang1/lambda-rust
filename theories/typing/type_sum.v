From iris.proofmode Require Import proofmode.
From lrust.lang Require Import memcpy.
From lrust.typing Require Import uninit uniq_bor shr_bor own sum.
From lrust.typing Require Import lft_contexts type_context programs product.
From iris.prelude Require Import options.

Section case.
  Context `{!typeGS Σ}.

  (* FIXME : have an Iris version of Forall2. *)
  Lemma type_case_own' E L C T p n tyl el :
    Forall2 (λ ty e,
      (⊢ typed_body E L C ((p +ₗ #0 ◁ own_ptr n (uninit 1)) :: (p +ₗ #1 ◁ own_ptr n ty) ::
         (p +ₗ #(S (ty.(ty_size))) ◁
            own_ptr n (uninit (max_list_with ty_size tyl - ty_size ty))) :: T) e) ∨
      (⊢ typed_body E L C ((p ◁ own_ptr n (sum tyl)) :: T) e))
      tyl el →
    ⊢ typed_body E L C ((p ◁ own_ptr n (sum tyl)) :: T) (case: !p of el).
  Proof.
    iIntros (Hel tid qmax) "#LFT #HE Hna HL HC HT". wp_bind p.
    rewrite tctx_interp_cons. iDestruct "HT" as "[Hp HT]".
    iApply (wp_hasty with "Hp"). iIntros ([[]| | |] Hv) "Hp"; try done.
    iDestruct "Hp" as "[H↦ Hf]". iDestruct "H↦" as (vl) "[H↦ Hown]".
    iDestruct "Hown" as (i vl' vl'') "(>% & >EQlen & Hown)". subst.
    simpl ty_size. iDestruct "EQlen" as %EQlen. rewrite -EQlen. simpl length.
    rewrite lty_cons list_ty_dist -!freeable_sz_split /=
            heap_mapsto_vec_cons heap_mapsto_vec_app.
    iDestruct "H↦" as "(H↦i & H↦vl' & H↦vl'')".
    iDestruct "Hf" as "(Hfi & Hfvl' & Hfvl'')".
    rewrite nth_lookup.
    destruct (tyl !! i) as [ty|] eqn:EQty; last iDestruct "Hown" as ">[]".
    edestruct @Forall2_lookup_l as (e & He & Hety); eauto.
    wp_read. wp_case; first (split; [lia|by rewrite Nat2Z.id]).
    destruct Hety as [Hety|Hety]; iApply (Hety with "LFT HE Hna HL HC");
      rewrite !tctx_interp_cons !tctx_hasty_val' /= ?Hv //=; iFrame "HT".
    - rewrite /own_ptr /=. iDestruct (ty.(ty_size_eq) with "Hown") as %<-.
      rewrite lty_cons /= in EQlen. apply eq_add_S in EQlen.
      iSplitL "H↦i Hfi"; last iSplitR "H↦vl'' Hfvl''".
      + rewrite shift_loc_0. iFrame. iExists [ #i]. rewrite heap_mapsto_vec_singleton.
        iFrame. auto.
      + eauto with iFrame.
      + rewrite -EQlen list_ty_dist Nat.add_comm Nat.add_sub shift_loc_assoc_nat.
        iFrame. iExists _. iFrame. auto.
    - rewrite /= -EQlen lty_cons list_ty_dist /= -(Nat.add_1_l (_+_)) -!freeable_sz_split. iFrame.
      iExists (#i :: vl' ++ vl''). iNext. rewrite heap_mapsto_vec_cons heap_mapsto_vec_app.
      iFrame. iExists i, vl', vl''. rewrite lty_cons list_ty_dist nth_lookup EQty /=. auto.
  Qed.

  Lemma type_case_own E L C T T' p n tyl el :
    tctx_extract_hasty E L p (own_ptr n (sum tyl)) T T' →
    Forall2 (λ ty e,
      (⊢ typed_body E L C ((p +ₗ #0 ◁ own_ptr n (uninit 1)) :: (p +ₗ #1 ◁ own_ptr n ty) ::
         (p +ₗ #(S (ty.(ty_size))) ◁
            own_ptr n (uninit (max_list_with ty_size tyl - ty_size ty))) :: T') e) ∨
      (⊢ typed_body E L C ((p ◁ own_ptr n (sum tyl)) :: T') e))
      tyl el →
    ⊢ typed_body E L C T (case: !p of el).
  Proof. unfold tctx_extract_hasty=>->. apply type_case_own'. Qed.

  Lemma type_case_uniq' E L C T p κ tyl el :
    lctx_lft_alive E L κ →
    Forall2 (λ ty e,
      (⊢ typed_body E L C ((p +ₗ #1 ◁ &uniq{κ}ty) :: T) e) ∨
      (⊢ typed_body E L C ((p ◁ &uniq{κ}(sum tyl)) :: T) e)) tyl el →
    ⊢ typed_body E L C ((p ◁ &uniq{κ}(sum tyl)) :: T) (case: !p of el).
  Proof.
    iIntros (Halive Hel tid qmax) "#LFT #HE Hna HL HC HT". wp_bind p.
    rewrite tctx_interp_cons. iDestruct "HT" as "[Hp HT]".
    iApply (wp_hasty with "Hp"). iIntros ([[|l|] | | |] Hv) "Hp"; try iDestruct "Hp" as "[]".
    iDestruct (llctx_interp_acc_noend with "HL") as "[HL HLclose]".
    iMod (Halive with "HE HL") as (q) "[Htok Hclose]"; first done.
    iMod (bor_acc_cons with "LFT Hp Htok") as "[H↦ Hclose']"; first done.
    iDestruct "H↦" as (vl) "[H↦ Hown]".
    iDestruct "Hown" as (i vl' vl'') "(>% & >EQlen & Hown)". subst.
    iDestruct "EQlen" as %EQlen.
    rewrite heap_mapsto_vec_cons heap_mapsto_vec_app nth_lookup.
    iDestruct "H↦" as "(H↦i & H↦vl' & H↦vl'')".
    destruct (tyl !! i) as [ty|] eqn:EQty; last iDestruct "Hown" as ">[]".
    edestruct @Forall2_lookup_l as (e & He & Hety); eauto.
    wp_read. wp_case; first (split; [lia|by rewrite Nat2Z.id]).
    iDestruct (ty.(ty_size_eq) with "Hown") as %EQlenvl'.
    destruct Hety as [Hety|Hety].
    - iMod ("Hclose'" $! ((l +ₗ 1) ↦∗: ty.(ty_own) tid)%I
            with "[H↦i H↦vl''] [H↦vl' Hown]") as "[Hb Htok]".
      { iIntros "!>Hown". iDestruct "Hown" as (vl'2) "[H↦ Hown]".
        iExists (#i::vl'2++vl''). iIntros "!>". iNext.
        iDestruct (ty.(ty_size_eq) with "Hown") as %EQlenvl'2.
        rewrite heap_mapsto_vec_cons heap_mapsto_vec_app EQlenvl' EQlenvl'2.
        iFrame. iExists _, _, _. iSplit; first by auto.
        rewrite -EQlen !lty_cons !list_ty_dist /= EQlenvl' EQlenvl'2 nth_lookup EQty /=. auto. }
      { iExists vl'. iFrame. }
      iMod ("Hclose" with "Htok") as "HL".
      iDestruct ("HLclose" with "HL") as "HL".
      iApply (Hety with "LFT HE Hna HL HC").
      rewrite !tctx_interp_cons !tctx_hasty_val' /= ?Hv //. iFrame.
    - iMod ("Hclose'" with "[] [H↦i H↦vl' H↦vl'' Hown]") as "[Hb Htok]";
        [by iIntros "!>$"| |].
      { iExists (#i::vl'++vl'').
        rewrite heap_mapsto_vec_cons heap_mapsto_vec_app /= -EQlen. iFrame. iNext.
        iExists i, vl', vl''. rewrite nth_lookup EQty. auto. }
      iMod ("Hclose" with "Htok") as "HL".
      iDestruct ("HLclose" with "HL") as "HL".
      iApply (Hety with "LFT HE Hna HL HC").
      rewrite !tctx_interp_cons !tctx_hasty_val' /= ?Hv //. iFrame.
  Qed.

  Lemma type_case_uniq E L C T T' p κ tyl el :
    tctx_extract_hasty E L p (&uniq{κ}(sum tyl)) T T' →
    lctx_lft_alive E L κ →
    Forall2 (λ ty e,
      (⊢ typed_body E L C ((p +ₗ #1 ◁ &uniq{κ}ty) :: T') e) ∨
      (⊢ typed_body E L C ((p ◁ &uniq{κ}(sum tyl)) :: T') e)) tyl el →
    ⊢ typed_body E L C T (case: !p of el).
  Proof. unfold tctx_extract_hasty=>->. apply type_case_uniq'. Qed.

  Lemma type_case_shr' E L C T p κ tyl el:
    lctx_lft_alive E L κ →
    Forall2 (λ ty e,
      (⊢ typed_body E L C ((p +ₗ #1 ◁ &shr{κ}ty) :: T) e) ∨
      (⊢ typed_body E L C ((p ◁ &shr{κ}(sum tyl)) :: T) e)) tyl el →
    ⊢ typed_body E L C ((p ◁ &shr{κ}(sum tyl)) :: T) (case: !p of el).
  Proof.
    iIntros (Halive Hel tid qmax) "#LFT #HE Hna HL HC HT". wp_bind p.
    rewrite tctx_interp_cons. iDestruct "HT" as "[Hp HT]".
    iApply (wp_hasty with "Hp"). iIntros ([[]| | |] Hv) "Hp"; try done.
    iDestruct "Hp" as (i) "[#Hb Hshr]".
    iDestruct (llctx_interp_acc_noend with "HL") as "[HL HLclose]".
    iMod (Halive with "HE HL") as (q) "[Htok Hclose]"; first done.
    iMod (frac_bor_acc with "LFT Hb Htok") as (q') "[[H↦i H↦vl''] Hclose']"; first done.
    rewrite nth_lookup.
    destruct (tyl !! i) as [ty|] eqn:EQty; last done.
    edestruct @Forall2_lookup_l as (e & He & Hety); eauto.
    wp_read. wp_case; first (split; [lia|by rewrite Nat2Z.id]).
    iMod ("Hclose'" with "[$H↦i $H↦vl'']") as "Htok".
    iMod ("Hclose" with "Htok") as "HL".
    iDestruct ("HLclose" with "HL") as "HL".
    destruct Hety as [Hety|Hety]; iApply (Hety with "LFT HE Hna HL HC");
      rewrite !tctx_interp_cons !tctx_hasty_val' /= ?Hv //; iFrame.
    iExists _. rewrite ->nth_lookup, EQty. auto.
  Qed.

  Lemma type_case_shr E L C T p κ tyl el :
    p ◁ &shr{κ}(sum tyl) ∈ T →
    lctx_lft_alive E L κ →
    Forall2 (λ ty e, ⊢ typed_body E L C ((p +ₗ #1 ◁ &shr{κ}ty) :: T) e) tyl el →
    ⊢ typed_body E L C T (case: !p of el).
  Proof.
    intros. rewrite ->copy_elem_of_tctx_incl; last done; last apply _.
    apply type_case_shr'; first done. eapply Forall2_impl; first done. auto.
  Qed.

  Lemma type_sum_assign_instr {E L} (i : nat) ty1 tyl ty ty2 p1 p2 :
    tyl !! i = Some ty →
    (⊢ typed_write E L ty1 (sum tyl) ty2) →
    ⊢ typed_instruction E L [p1 ◁ ty1; p2 ◁ ty] (p1 <-{Σ i} p2) (λ _, [p1 ◁ ty2]).
  Proof.
    iIntros (Hty Hw tid qmax) "#LFT #HE $ HL Hp".
    rewrite tctx_interp_cons tctx_interp_singleton.
    iDestruct "Hp" as "[Hp1 Hp2]". iDestruct (closed_hasty with "Hp1") as "%".
    iDestruct (closed_hasty with "Hp2") as "%". wp_bind p1.
    iApply (wp_hasty with "Hp1"). iIntros (v1 Hv1) "Hty1".
    rewrite typed_write_eq in Hw.
    iDestruct (llctx_interp_acc_noend with "HL") as "[HL HLclose]".
    iMod (Hw with "[] LFT HE HL Hty1") as (l vl) "(H & H↦ & Hw)"=>//=.
    destruct vl as [|? vl]; iDestruct "H" as %[[= Hlen] ->].
    rewrite heap_mapsto_vec_cons. iDestruct "H↦" as "[H↦0 H↦vl]".
    assert (val_size v = 1%nat) by admit.
    wp_write. wp_bind p1. iApply (wp_wand with "[]"); first by iApply (wp_eval_path).
    iIntros (? ->). wp_op. wp_bind p2. iApply (wp_hasty with "Hp2").
    iIntros (v2 Hv2) "Hty2". iDestruct (ty_size_eq with "Hty2") as %Hlenty.
    rewrite lty_cons in Hlen.
    rewrite H1 in Hlen.
    destruct vl as [|? vl].
    { exfalso. revert i Hty. clear - Hlen Hlenty.
      induction tyl as [|ty' tyl IH]=>//= -[|i] /=.
      - intros [= ->]. simpl in *.
        rewrite lty_size_singleton in Hlenty. apply eq_add_S in Hlen. 
        rewrite lty_size_emp in Hlen. rewrite -Hlenty in Hlen.
        assert (val_size v2 >= 1%nat) by apply val_gt1.
        lia.
      - apply IH. rewrite lty_size_emp in Hlen, IH. simpl in *. admit. }
    rewrite heap_mapsto_vec_cons -wp_fupd. iDestruct "H↦vl" as "[H↦ H↦vl]". rewrite H1. wp_write.
    rewrite tctx_interp_singleton tctx_hasty_val' //.
    iMod ("Hw" with "[-HLclose]") as "[HL $]"; last first.
    { iApply "HLclose". done. }
    iNext.
    iExists (_::_::_). rewrite !heap_mapsto_vec_cons.
    assert (val_size v0 = val_size v2) by admit.
    iFrame "H↦0 H↦". rewrite H2. simpl. iFrame.
    iExists i, [_], _. rewrite -Hlen nth_lookup Hty !lty_cons /= H2. auto.
  Admitted.

  Lemma type_sum_assign {E L} sty tyl i ty1 ty ty1' C T T' p1 p2 e:
    Closed [] e →
    0 ≤ i →
    sty = sum tyl →
    tctx_extract_ctx E L [p1 ◁ ty1; p2 ◁ ty] T T' →
    tyl !! (Z.to_nat i) = Some ty →
    (⊢ typed_write E L ty1 sty ty1') →
    typed_body E L C ((p1 ◁ ty1') :: T') e -∗
    typed_body E L C T (p1 <-{Σ i} p2 ;; e).
  Proof.
    iIntros (??->) "* **". rewrite -(Z2Nat.id i) //.
    iApply type_seq; [by eapply type_sum_assign_instr|done|done].
  Qed.

  Lemma type_sum_unit_instr {E L} (i : nat) tyl ty1 ty2 p :
    tyl !! i = Some unit →
    (⊢ typed_write E L ty1 (sum tyl) ty2) →
    ⊢ typed_instruction E L [p ◁ ty1] (p <-{Σ i} ()) (λ _, [p ◁ ty2]).
  Proof.
    iIntros (Hty Hw tid qmax) "#LFT #HE $ HL Hp". rewrite tctx_interp_singleton.
    wp_bind p. iApply (wp_hasty with "Hp"). iIntros (v Hv) "Hty".
    rewrite typed_write_eq in Hw.
    iDestruct (llctx_interp_acc_noend with "HL") as "[HL HLclose]".
    iMod (Hw with "[] LFT HE HL Hty") as (l vl) "(H & H↦ & Hw)"; first done.
    simpl. destruct vl as [|? vl]; iDestruct "H" as %[[= Hlen] ->].
    rewrite heap_mapsto_vec_cons -wp_fupd. iDestruct "H↦" as "[H↦0 H↦vl]".
    wp_write. rewrite tctx_interp_singleton tctx_hasty_val' //.
    iMod ("Hw" with "[-HLclose]") as "[HL $]"; last first.
    { iApply "HLclose". done. }
    iModIntro. iExists (_::_). rewrite heap_mapsto_vec_cons.
    assert (val_size v0 = 1%nat) by admit.
    iFrame "H↦0". rewrite H /=. iFrame.
    iExists i, [], _. rewrite -Hlen nth_lookup Hty !lty_cons H /=. auto.
  Admitted.

  Lemma type_sum_unit {E L} sty tyl i ty1 ty1' C T T' p e:
    Closed [] e →
    0 ≤ i →
    sty = sum tyl →
    tctx_extract_hasty E L p ty1 T T' →
    tyl !! (Z.to_nat i) = Some unit →
    (⊢ typed_write E L ty1 sty ty1') →
    typed_body E L C ((p ◁ ty1') :: T') e -∗
    typed_body E L C T (p <-{Σ i} () ;; e).
  Proof.
    iIntros (??->) "* **". rewrite -(Z2Nat.id i) //.
    iApply type_seq; [by eapply type_sum_unit_instr|solve_typing|done].
  Qed.

  Lemma type_sum_memcpy_instr {E L} (i : nat) tyl ty1 ty1' ty2 ty2' ty p1 p2 :
    tyl !! i = Some ty →
    (⊢ typed_write E L ty1 (sum tyl) ty1') →
    (⊢ typed_read E L ty2 ty ty2') →
    ⊢ typed_instruction E L [p1 ◁ ty1; p2 ◁ ty2]
               (p1 <-{ty.(ty_size),Σ i} !p2) (λ _, [p1 ◁ ty1'; p2 ◁ ty2']).
  Proof.
    iIntros (Hty Hw Hr tid qmax) "#LFT #HE Htl HL Hp".
    iDestruct (llctx_interp_acc_noend with "HL") as "[[HL1 HL2] HLclose]".
    rewrite tctx_interp_cons tctx_interp_singleton.
    iDestruct "Hp" as "[Hp1 Hp2]". iDestruct (closed_hasty with "Hp1") as "%".
    iDestruct (closed_hasty with "Hp2") as "%". wp_bind p1.
    iApply (wp_hasty with "Hp1"). iIntros (v1 Hv1) "Hty1".
    rewrite typed_write_eq in Hw.
    iMod (Hw with "[] LFT HE HL1 Hty1") as (l1 vl1) "(H & H↦ & Hw)"=>//=.
    clear Hw. destruct vl1 as [|? vl1]; iDestruct "H" as %[[= Hlen] ->].
    rewrite heap_mapsto_vec_cons -wp_fupd. assert (val_size v = 1%nat) by admit.
    iDestruct "H↦" as "[H↦0 H↦vl1]". wp_write.
    wp_bind p1. iApply (wp_wand with "[]"); first by iApply (wp_eval_path). iIntros (? ->).
    wp_op. wp_bind p2. iApply (wp_hasty with "Hp2"). iIntros (v2 Hv2) "Hty2".
    rewrite typed_read_eq in Hr.
    iMod (Hr with "[] LFT HE Htl HL2 Hty2") as (l2 vl2 q) "(% & H↦2 & Hty & Hr)"=>//=.
    clear Hr. subst. assert (ty.(ty_size) ≤ list_ty_size vl1).
    { revert i Hty. rewrite lty_cons H1 /= in Hlen. apply eq_add_S in Hlen. rewrite Hlen. clear.
      induction tyl as [|ty' tyl IH]=>//= -[|i] /=.
      - intros [= ->]. lia.
      - specialize (IH i). intuition lia. }
    rewrite heap_mapsto_vec_idemp -(take_drop (ty.(ty_size)) (flatten vl1)) heap_mapsto_vec_app.
    iDestruct "H↦vl1" as "[H↦vl1 H↦pad]".
    iDestruct (ty_size_eq with "Hty") as "#>%".
    rewrite !H1.
    iApply (wp_memcpy with "[$H↦vl1 $H↦2]"); [|lia|].
    { rewrite -flatten_size. admit.
      (* assert (∀ (n : nat) vl, n >= length (flatten vl) → flatten (take n (flatten vl)) = flatten vl).
      {
        clear. intros. induction vl; first rewrite /= take_nil //.
        simpl.
        rewrite firstn_app.
        rewrite /= app_length in H.
        rewrite !take_ge; try lia. rewrite flatten_dist flatten_idemp flattenv_idemp //.
      } *)
    }
    iNext; iIntros "[H↦vl1 H↦2]".
    rewrite tctx_interp_cons tctx_interp_singleton !tctx_hasty_val' //.
    iMod ("Hr" with "H↦2") as "($ & HL1 & $)".
    iMod ("Hw" with "[-HLclose HL1]") as "[HL $]"; last first.
    { iApply "HLclose". by iFrame. }
    iNext.
    rewrite split_sum_mt /is_pad. iExists i. rewrite nth_lookup Hty. iFrame.
    iSplitL "H↦pad".
    - admit.
      (* rewrite (shift_loc_assoc_nat _ 1) take_length Nat.min_l; last lia.
      iExists _. iFrame. rewrite /= drop_length. iPureIntro. lia. *)
    - iExists _. iFrame.
  Admitted.

  Lemma type_sum_memcpy {E L} sty tyl i ty1 ty2 ty n ty1' ty2' C T T' p1 p2 e:
    Closed [] e →
    0 ≤ i →
    sty = sum tyl →
    tctx_extract_ctx E L [p1 ◁ ty1; p2 ◁ ty2] T T' →
    tyl !! (Z.to_nat i) = Some ty →
    (⊢ typed_write E L ty1 sty ty1') →
    (⊢ typed_read E L ty2 ty ty2') →
    Z.of_nat (ty.(ty_size)) = n →
    typed_body E L C ((p1 ◁ ty1') :: (p2 ◁ ty2') :: T') e -∗
    typed_body E L C T (p1 <-{n,Σ i} !p2 ;; e).
  Proof.
    iIntros (?? -> ??? Hr ?) "?". subst. rewrite -(Z2Nat.id i) //.
    by iApply type_seq; [eapply type_sum_memcpy_instr, Hr|done|done].
  Qed.

  Lemma ty_outlives_E_elctx_sat_sum E L tyl {Wf : ListTyWf tyl} α:
    elctx_sat E L (tyl_outlives_E tyl α) →
    elctx_sat E L (ty_outlives_E (sum tyl) α).
  Proof.
    intro Hsat. eapply eq_ind; first done. clear Hsat. rewrite /ty_outlives_E /=.
    induction Wf as [|ty [] ?? IH]=>//=. rewrite IH fmap_app //.
  Qed.
End case.

Global Hint Resolve ty_outlives_E_elctx_sat_sum : lrust_typing.
