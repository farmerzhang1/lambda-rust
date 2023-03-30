From iris.proofmode Require Import proofmode.
From lrust.lang.lib Require Import memcpy.
From lrust.typing Require Export type.
From lrust.typing Require Import util uninit type_context programs.
From iris.prelude Require Import options.

Section own.
  Context `{!typeGS Σ}.

  Definition freeable_sz (n : nat) (sz : nat) (l : loc) : iProp Σ :=
    match sz, n return _ with
    | 0%nat, _ => True
    | _, 0%nat => False
    | sz, n => †{pos_to_Qp (Pos.of_nat sz) / pos_to_Qp (Pos.of_nat n)}l…sz
    end%I.
  Global Arguments freeable_sz : simpl never.

  Global Instance freeable_sz_timeless n sz l : Timeless (freeable_sz n sz l).
  Proof. destruct sz, n; apply _. Qed.

  Lemma freeable_sz_full n l : freeable_sz n n l ⊣⊢ †{1}l…n ∨ ⌜Z.of_nat n = 0⌝.
  Proof.
    destruct n as [|n].
    - iSplit; iIntros "H /="; auto.
    - assert (Z.of_nat (S n) = 0 ↔ False) as -> by done. rewrite right_id.
      by rewrite /freeable_sz Qp.div_diag.
  Qed.

  Lemma freeable_sz_full_S n l : freeable_sz (S n) (S n) l ⊣⊢ †{1}l…(S n).
  Proof. rewrite freeable_sz_full. iSplit; auto. iIntros "[$|%]"; done. Qed.

  Lemma freeable_sz_split n sz1 sz2 l :
    freeable_sz n sz1 l ∗ freeable_sz n sz2 (l +ₗ sz1) ⊣⊢
                freeable_sz n (sz1 + sz2) l.
  Proof.
    destruct sz1; [|destruct sz2;[|rewrite /freeable_sz plus_Sn_m; destruct n]].
    - by rewrite left_id shift_loc_0.
    - by rewrite right_id Nat.add_0_r.
    - iSplit.
      + by iIntros "[[]?]".
      + by iIntros "[]".
    - rewrite heap_freeable_op_eq. f_equiv; [|done..].
      by rewrite -Qp.div_add_distr pos_to_Qp_add -Nat2Pos.inj_add.
  Qed.

  (* Make sure 'simpl' doesn't unfold. *)
  Global Opaque freeable_sz.

  Program Definition own_ptr (n : nat) (ty : type) :=
    {| ty_size := 1;
       ty_own tid vl :=
         match vl return _ with
         | [ #(LitLoc l) ] =>
         (* We put a later in front of the †{q}, because we cannot use
            [ty_size_eq] on [ty] at step index 0, which would in turn
            prevent us to prove [subtype_own].

            Since this assertion is timeless, this should not cause
            problems. *)
          (* 
            ↦∗: 这个神奇的notation，估计是说存在某一个 heap value 被 own ，然后还满足冒号后面的predicate
            没猜错，see theories/lang/heap.v
          *)
           ▷ (l ↦∗: ty.(ty_own) tid ∗ freeable_sz n ty.(ty_size) l)
         | _ => False
         end%I;
       ty_shr κ tid l :=
         (∃ l':loc, &frac{κ}(λ q', l ↦{q'} #l') ∗
            □ (∀ F q, ⌜↑shrN ∪ ↑lftN ⊆ F⌝ -∗ q.[κ] ={F}[F∖↑shrN]▷=∗
                            ty.(ty_shr) κ tid l' ∗ q.[κ]))%I |}.
  Next Obligation. by iIntros (q ty tid [|[[]| | |][]]) "H". Qed.
  Next Obligation.
    move=>n ty N κ l tid ?? /=. iIntros "#LFT Hshr Htok".
    iMod (bor_exists with "LFT Hshr") as (vl) "Hb"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "[Hb1 Hb2]"; first solve_ndisj.
    destruct vl as [|[[|l'|]| | |][]];
      try (iMod (bor_persistent with "LFT Hb2 Htok") as "[>[]_]"; solve_ndisj).
    iFrame. iExists l'. rewrite heap_mapsto_vec_singleton.
    rewrite bi.later_sep.
    iMod (bor_sep with "LFT Hb2") as "[Hb2 _]"; first solve_ndisj.
    iMod (bor_fracture (λ q, l ↦{q} #l')%I with "LFT Hb1") as "$"; first solve_ndisj.
    iApply delay_sharing_later; done.
  Qed.
  Next Obligation.
    intros _ ty κ κ' tid l. iIntros "#Hκ #H".
    iDestruct "H" as (l') "[Hfb #Hvs]".
    iExists l'. iSplit; first by iApply (frac_bor_shorten with "[]"). iIntros "!> %F %q % Htok".
    iApply (step_fupd_mask_mono F _ (F∖↑shrN)); [solve_ndisj..|].
    iMod (lft_incl_acc with "Hκ Htok") as (q') "[Htok Hclose]"; first solve_ndisj.
    iMod ("Hvs" with "[%] Htok") as "Hvs'"; first solve_ndisj. iModIntro. iNext.
    iMod "Hvs'" as "[Hshr Htok]". iMod ("Hclose" with "Htok") as "$".
    by iApply (ty.(ty_shr_mono) with "Hκ").
  Qed.

  Global Instance own_ptr_wf n ty `{!TyWf ty} : TyWf (own_ptr n ty) :=
    { ty_lfts := ty_lfts ty; ty_wf_E := ty_wf_E ty }.

  Lemma own_type_incl n m ty1 ty2 :
    ▷ ⌜n = m⌝ -∗ ▷ type_incl ty1 ty2 -∗ type_incl (own_ptr n ty1) (own_ptr m ty2).
  Proof.
    iIntros "#Heq (#Hsz & #Ho & #Hs)". iSplit; first done. iSplit; iModIntro.
    - iIntros (?[|[[| |]| | |][]]) "H"; try done. simpl.
      iDestruct "H" as "[Hmt H†]". iNext. iDestruct ("Hsz") as %<-.
      iDestruct "Heq" as %->. iFrame. iApply (heap_mapsto_pred_wand with "Hmt").
      iApply "Ho".
    - iIntros (???) "H". iDestruct "H" as (l') "[Hfb #Hvs]".
      iExists l'. iFrame. iIntros "!>". iIntros (F' q) "% Htok".
      iMod ("Hvs" with "[%] Htok") as "Hvs'"; first done. iModIntro. iNext.
      iMod "Hvs'" as "[Hshr $]". iApply ("Hs" with "Hshr").
  Qed.

  Global Instance own_mono E L n :
    Proper (subtype E L ==> subtype E L) (own_ptr n).
  Proof.
    intros ty1 ty2 Hincl. iIntros (qmax qL) "HL".
    iDestruct (Hincl with "HL") as "#Hincl".
    iClear "∗". iIntros "!> #HE".
    iApply own_type_incl; first by auto. iApply "Hincl"; auto.
  Qed.
  Lemma own_mono' E L n1 n2 ty1 ty2 :
    n1 = n2 → subtype E L ty1 ty2 → subtype E L (own_ptr n1 ty1) (own_ptr n2 ty2).
  Proof. intros -> *. by apply own_mono. Qed.
  Global Instance own_proper E L n :
    Proper (eqtype E L ==> eqtype E L) (own_ptr n).
  Proof. intros ??[]; split; by apply own_mono. Qed.
  Lemma own_proper' E L n1 n2 ty1 ty2 :
    n1 = n2 → eqtype E L ty1 ty2 → eqtype E L (own_ptr n1 ty1) (own_ptr n2 ty2).
  Proof. intros -> *. by apply own_proper. Qed.

  Global Instance own_type_contractive n : TypeContractive (own_ptr n).
  Proof. solve_type_proper. Qed.

  Global Instance own_ne n : NonExpansive (own_ptr n).
  Proof. apply type_contractive_ne, _. Qed.

  Global Instance own_send n ty :
    Send ty → Send (own_ptr n ty).
  Proof.
    iIntros (Hsend tid1 tid2 [|[[| |]| | |][]]) "H"; try done.
    iDestruct "H" as "[Hm $]". iNext. iApply (heap_mapsto_pred_wand with "Hm").
    iIntros (vl) "?". by iApply Hsend.
  Qed.

  Global Instance own_sync n ty :
    Sync ty → Sync (own_ptr n ty).
  Proof.
    iIntros (Hsync κ tid1 tid2 l) "H". iDestruct "H" as (l') "[Hm #Hshr]".
    iExists _. iFrame "Hm". iModIntro. iIntros (F q) "% Htok".
    iMod ("Hshr" with "[] Htok") as "Hfin"; first done. iModIntro. iNext.
    iMod "Hfin" as "{Hshr} [Hshr $]". by iApply Hsync.
  Qed.
End own.

Section box.
  Context `{!typeGS Σ}.

  Definition box ty := own_ptr ty.(ty_size) ty.

  Lemma box_type_incl ty1 ty2 :
    ▷ type_incl ty1 ty2 -∗ type_incl (box ty1) (box ty2).
  Proof.
    iIntros "#Hincl". iApply own_type_incl; last done.
    iDestruct "Hincl" as "(? & _ & _)". done.
  Qed.

  Global Instance box_mono E L :
    Proper (subtype E L ==> subtype E L) box.
  Proof.
    intros ty1 ty2 Hincl. iIntros (qmax qL) "HL".
    iDestruct (Hincl with "HL") as "#Hincl".
    iClear "∗". iIntros "!> #HE".
    iApply box_type_incl. iApply "Hincl"; auto.
  Qed.
  Lemma box_mono' E L ty1 ty2 :
    subtype E L ty1 ty2 → subtype E L (box ty1) (box ty2).
  Proof. intros. by apply box_mono. Qed.
  Global Instance box_proper E L :
    Proper (eqtype E L ==> eqtype E L) box.
  Proof. intros ??[]; split; by apply box_mono. Qed.
  Lemma box_proper' E L ty1 ty2 :
    eqtype E L ty1 ty2 → eqtype E L (box ty1) (box ty2).
  Proof. intros. by apply box_proper. Qed.

  Global Instance box_type_contractive : TypeContractive box.
  Proof. solve_type_proper. Qed.

  Global Instance box_ne : NonExpansive box.
  Proof. apply type_contractive_ne, _. Qed.
End box.

Section util.
  Context `{!typeGS Σ}.

  Lemma ownptr_own n ty tid v :
    (own_ptr n ty).(ty_own) tid [v] ⊣⊢
       ∃ (l : loc) (vl : vec val ty.(ty_size)) (vl' : list val),
         ⌜v = #l⌝ ∗ ▷ ⌜vec_to_list vl = flatten vl'⌝ ∗ ▷ l ↦∗ vl' ∗ ▷ ty.(ty_own) tid vl' ∗ ▷ freeable_sz n ty.(ty_size) l.
  Proof.
    iSplit.
    - iIntros "Hown". destruct v as [[|l|]| | |]; try done.
      iExists l. iDestruct "Hown" as "[Hown $]". rewrite heap_mapsto_ty_own.
      iDestruct "Hown" as (vl vl') "(? & ? & ?)". eauto with iFrame.
    - iIntros "Hown". iDestruct "Hown" as (l vl vl') "(% & ? & ? & ? & ?)". subst v.
      iFrame. iExists _. iFrame.
  Qed.

  Lemma ownptr_uninit_own n m tid v :
    (own_ptr n (uninit m)).(ty_own) tid [v] ⊣⊢
         ∃ (l : loc) (vl' : list val), ⌜v = #l⌝ ∗ ▷ ⌜list_ty_size vl' = m⌝ ∗ ▷ l ↦∗ vl' ∗ ▷ freeable_sz n m l.
  Proof.
    rewrite ownptr_own. apply bi.exist_proper=>l. iSplit.
    (* FIXME: The goals here look rather confusing:  One cannot tell that we are looking at
       a statement in Iris; the top-level → could just as well be a Coq implication. *)
    - iIntros "H". iDestruct "H" as (vl vl') "(% & Hvl & Hl & Hown & $)". subst v.
      rewrite uninit_own.
      iExists (vl'). iSplit; try done. rewrite -bi.later_sep. iNext. 
      iFrame.
    - iIntros "H". iDestruct "H" as (vl) "(% & Hvl & Hl & $)". subst v.
      rewrite -flatten_size /uninit /=.
      setoid_rewrite <-bi.sep_exist_l.
      setoid_rewrite <-bi.sep_exist_l.
      iSplit; auto.
      setoid_rewrite <-bi.later_sep.
      setoid_rewrite <-bi.later_sep.
      setoid_rewrite <-bi.later_exist.
      setoid_rewrite <-bi.later_exist.
      iNext.
      iDestruct "Hvl" as %<-.
      iExists (list_to_vec (flatten vl)), vl.
      iFrame. iPureIntro; split; last by rewrite flatten_size.
      induction (flatten vl); auto. simpl. by rewrite IHl0.
  Qed.
End util.

Section typing.
  Context `{!typeGS Σ}.

  (** Typing *)
  Lemma write_own {E L} ty ty' n :
    ty.(ty_size) = ty'.(ty_size) → ⊢ typed_write E L (own_ptr n ty') ty (own_ptr n ty).
  Proof.
    rewrite typed_write_eq. iIntros (Hsz) "!>".
    iIntros ([[]| | |] tid F qmax qL ?) "_ _ $ Hown"; try done.
    rewrite /= Hsz. iDestruct "Hown" as "[H↦ $]". iDestruct "H↦" as (vl) "[>H↦ Hown]".
    iDestruct (ty_size_eq with "Hown") as "#>%". iExists _, _. iFrame "H↦". auto.
  Qed.

  Lemma read_own_copy E L ty n :
    Copy ty → ⊢ typed_read true E L (own_ptr n ty) ty (own_ptr n ty).
  Proof.
    rewrite typed_read_eq. iIntros (Hsz) "!>".
    iIntros ([[|l|]| | |] tid F qmax qL ?) "_ _ $ $ Hown"; try done.
    iDestruct "Hown" as "[H↦ H†]". iDestruct "H↦" as (vl) "[>H↦ #Hown]".
    iExists l, _, _. iFrame "∗#". iSplitR; first done. iIntros "!> Hl !>".
    iExists _. auto.
  Qed.

  Lemma read_own_move E L ty n s:
    ⊢ typed_read s E L (own_ptr n ty) ty (own_ptr n $ uninit ty.(ty_size)).
  Proof.
    rewrite typed_read_eq. iModIntro.
    iIntros ([[|l|]| | |] tid F qmax qL ?) "_ _ $ $ Hown"; try done.
    iDestruct "Hown" as "[H↦ H†]". iDestruct "H↦" as (vl) "[>H↦ Hown]".
    iDestruct (ty_size_eq with "Hown") as "#>%".
    iExists l, vl, _. iFrame "∗#". iSplitR; first done.
    destruct s; last admit. rewrite bi.True_sep. iIntros "!> Hl !> !>".
    iExists _. iFrame. simpl. done.
  Admitted.

  Lemma type_new_instr {E L} (n : Z) :
    0 ≤ n →
    ⊢ let n' := Z.to_nat n in
      typed_instruction_ty E L [] (new [ #n ]%E) (own_ptr n' (uninit n')).
  Proof.
    iIntros (? tid qmax) "#LFT #HE $ $ _".
    iApply wp_new; try done. iModIntro.
    iIntros (l) "(H† & Hlft)". rewrite tctx_interp_singleton tctx_hasty_val.
    iNext. rewrite freeable_sz_full Z2Nat.id //. iFrame.
    iExists (repeat #☠ (Z.to_nat n)). iFrame. by rewrite /= st_repeat_size.
  Qed.

  Lemma type_new {E L C T} (n' : nat) x (n : Z) e :
    Closed (x :b: []) e →
    0 ≤ n →
    n' = Z.to_nat n →
    (∀ (v : val),
        typed_body E L C ((v ◁ own_ptr n' (uninit n')) :: T) (subst' x v e)) -∗
    typed_body E L C T (let: x := new [ #n ] in e).
  Proof. iIntros. subst. iApply type_let; [by apply type_new_instr|solve_typing..]. Qed.

  Lemma type_new_subtype ty E L C T x (n : Z) e :
    Closed (x :b: []) e →
    0 ≤ n →
    let n' := Z.to_nat n in
    subtype E L (uninit n') ty →
    (∀ (v : val), typed_body E L C ((v ◁ own_ptr n' ty) :: T) (subst' x v e)) -∗
    typed_body E L C T (let: x := new [ #n ] in e).
  Proof.
    iIntros (????) "Htyp". iApply type_let; [by apply type_new_instr|solve_typing|].
    iIntros (v). iApply typed_body_mono; last iApply "Htyp"; try done.
    by apply (tctx_incl_frame_r _ [_] [_]), subtype_tctx_incl, own_mono.
  Qed.

  Lemma type_delete_instr {E L} ty (n : Z) p :
    Z.of_nat (ty.(ty_size)) = n →
    ⊢ typed_instruction E L [p ◁ own_ptr ty.(ty_size) ty] (delete [ #n; p])%E (λ _, []).
  Proof.
    iIntros (<- tid qmax) "#LFT #HE $ $ Hp". rewrite tctx_interp_singleton.
    wp_bind p. iApply (wp_hasty with "Hp"). iIntros ([[]| | |]) "_ Hown"; try done.
    iDestruct "Hown" as "[H↦: >H†]". iDestruct "H↦:" as (vl) "[>H↦ Hown]".
    iDestruct (ty_size_eq with "Hown") as "#>EQ".
    iDestruct "EQ" as %<-. iApply (wp_delete with "[-]"); auto.
    - iFrame "H↦". by iApply freeable_sz_full.
    - rewrite /tctx_interp /=; auto.
  Qed.

  Lemma type_delete {E L} ty C T T' (n' : nat) (n : Z)  p e :
    Closed [] e →
    tctx_extract_hasty E L p (own_ptr n' ty) T T' →
    n = n' → Z.of_nat (ty.(ty_size)) = n →
    typed_body E L C T' e -∗
    typed_body E L C T (delete [ #n; p ] ;; e).
  Proof.
    iIntros (?? -> Hlen) "?". iApply type_seq; [by apply type_delete_instr| |done].
    by rewrite (inj _ _ _ Hlen).
  Qed.

  Lemma type_letalloc_1 {E L} ty C T T' (x : string) p e :
    Closed [] p → Closed (x :b: []) e →
    tctx_extract_hasty E L p ty T T' →
    ty.(ty_size) = 1%nat →
    (∀ (v : val), typed_body E L C ((v ◁ own_ptr 1 ty)::T') (subst x v e)) -∗
    typed_body E L C T (letalloc: x <- p in e).
  Proof.
    iIntros (??? Hsz) "**". iApply type_new.
    - rewrite /Closed /=. rewrite !andb_True.
      eauto 10 using is_closed_weaken with set_solver.
    - done.
    - solve_typing.
    - iIntros (xv) "/=". rewrite -Hsz.
      assert (subst x xv (x <- p ;; e)%E = (xv <- p ;; subst x xv e)%E) as ->.
      { (* TODO : simpl_subst should be able to do this. *)
        unfold subst=>/=. repeat f_equal.
        - by rewrite bool_decide_true.
        - eapply is_closed_subst; first done. set_solver. }
      iApply type_assign; [|solve_typing|by eapply write_own|solve_typing].
      apply subst_is_closed; last done. apply is_closed_of_val.
  Qed.

  Lemma type_letalloc_n {E L} ty ty1 ty2 C T T' (x : string) p e :
    Closed [] p → Closed (x :b: []) e →
    tctx_extract_hasty E L p ty1 T T' →
    (⊢ typed_read true E L ty1 ty ty2) →
    (∀ (v : val),
        typed_body E L C ((v ◁ own_ptr (ty.(ty_size)) ty)::(p ◁ ty2)::T') (subst x v e)) -∗
    typed_body E L C T (letalloc: x <-{ty.(ty_size)} !p in e).
  Proof.
    iIntros. iApply type_new.
    - rewrite /Closed /=. rewrite !andb_True.
      eauto 10 using is_closed_of_val, is_closed_weaken with set_solver.
    - lia.
    - done.
    - iIntros (xv) "/=".
      assert (subst x xv (x <-{ty.(ty_size)} !p ;; e)%E =
              (xv <-{ty.(ty_size)} !p ;; subst x xv e)%E) as ->.
      { (* TODO : simpl_subst should be able to do this. *)
        unfold subst=>/=. repeat f_equal.
        - eapply (is_closed_subst []); last set_solver. apply is_closed_of_val.
        - by rewrite bool_decide_true.
        - eapply is_closed_subst; first done. set_solver. }
      rewrite Nat2Z.id. iApply type_memcpy.
      + apply subst_is_closed; last done. apply is_closed_of_val.
      + solve_typing.
      + (* TODO: Doing "eassumption" here shows that unification takes *forever* to fail.
           I guess that's caused by it trying to unify typed_read and typed_write,
           but considering that the Iris connectives are all sealed, why does
           that take so long? *)
        by eapply (write_own ty (uninit _)).
      + solve_typing.
      + done.
      + done.
  Qed.
End typing.

Global Hint Resolve own_mono' own_proper' box_mono' box_proper'
             write_own read_own_copy : lrust_typing.
(* By setting the priority high, we make sure copying is tried before
   moving. *)
Global Hint Resolve read_own_move | 100 : lrust_typing.
