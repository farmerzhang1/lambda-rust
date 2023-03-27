From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type.
From lrust.typing Require Import product.
From iris.prelude Require Import options.

Section uninit.
  Context `{!typeGS Σ}.

  Program Definition uninit_1 : type :=
    {| st_own tid vl := ⌜list_ty_size vl = 1%nat⌝%I |}.
  Next Obligation. done. Qed.

  Global Instance uninit_1_send : Send uninit_1.
  Proof. iIntros (tid1 tid2 vl) "H". done. Qed.

  Definition uninit0 (n : nat) : type :=
    Π (replicate n uninit_1).

  Lemma uninit0_sz n : ty_size (uninit0 n) = n.
  Proof. induction n=>//=. by f_equal. Qed.
  Lemma test_ty_own v tid : ⊢ ty_own (uninit0 (val_size v)) tid [v].
  Proof.
    iIntros "".
    iInduction v as [ | | | ] "IH"; simpl.
    - by iExists [(#l)%V], [].
    - by iExists [(RecV _ _ _)%V], [].
    - by iExists [rnil%V], [].
    - rewrite /uninit0 replicate_add. simpl.
      (* notice that product accepts a list of values
      and split the non-flattened list to two parts*)
      Abort.
  (*
    owning an (uninit0 n) already impose restrictions on the elements of vl:
    each val in vl must be a simple type, that's why the above lemma fails
  *)
  Lemma uninit0_own n tid vl :
    ty_own (uninit0 n) tid vl ⊣⊢ ⌜length vl = n ∧ list_ty_size vl = n⌝.
  Proof.
    iSplit.
    - iIntros "Hvl".
      iInduction n as [|n] "IH" forall (vl); simpl.
      + iDestruct "Hvl" as "%". subst vl. done.
      + iDestruct "Hvl" as (vl1 vl2) "(% & % & Hprod)".
        assert (length vl1 = 1%nat); first by apply (length1_size1 vl1).
        destruct vl1 as [|v [|]]; try done. subst vl. simpl.
        iDestruct ("IH" with "Hprod") as "[% %]". iPureIntro. 
        split; [f_equal; apply H | ].
        by rewrite lty_cons H2 -lty_size_singleton H0.
    - iIntros "[% %]". subst n. iInduction vl as [|v vl] "IH"; first done.
      simpl.
      iExists [v], vl; iSplit; first done. rename H0 into H.
      destruct v; try (iSplit; first done; iApply "IH";
        rewrite lty_cons in H; simpl in H;
        apply eq_add_S in H; iPureIntro; apply H).
      exfalso. revert H.
      simpl. rewrite lty_cons. intro H.
      simpl in H.
      assert (val_size v1 >= 1%nat) by apply val_gt1.
      assert (val_size v2 >= 1%nat) by apply val_gt1.
      assert (list_ty_size vl >= length vl) by apply lty_ge_len.
      lia.
  Qed.

  (* We redefine uninit as an alias of uninit0, so that ty_size and ty_own
     compute directly.  We re-use the sharing from the product as that saves a whole
     lot of work. *)
  Program Definition uninit (n : nat) : type :=
    {| ty_size := n; ty_own tid vl := ⌜list_ty_size vl = n⌝%I;
       ty_shr := (uninit0 n).(ty_shr) |}.
  Next Obligation. iIntros (???) "%". done. Qed.
  Next Obligation.
    iIntros (n ??????) "LFT Hvl". iApply (ty_share (uninit0 n) with "LFT"); first done.
    iApply (bor_iff with "[] Hvl"). iIntros "!> !>". setoid_rewrite uninit0_own.
    iSplit; iIntros "H".
    - iDestruct "H" as (vl) "[? %]". iExists (flatten vl).
      rewrite heap_mapsto_vec_idemp flatten_size -!flatten_size flatten_idemp !flatten_size.
      iFrame. done.
    - iDestruct "H" as (vl) "(Hvl & _ & Hlty)". iExists vl. iFrame.
  Qed.
  Next Obligation. intros. by apply ty_shr_mono. Qed.

  Global Instance uninit_wf n : TyWf (uninit n) :=
    { ty_lfts := []; ty_wf_E := [] }.

  Global Instance uninit_copy n : Copy (uninit n).
  Proof.
    assert (Copy (uninit0 n)) as [A B].
    { apply product_copy. by apply Forall_replicate, _. }
    split; first by apply _.
    rewrite uninit0_sz in B. setoid_rewrite uninit0_own in B.
    (* let's do some gymnastics! but not now *)
    admit.
  Admitted.

  Global Instance uninit_send n : Send (uninit n).
  Proof. iIntros (???) "?". done. Qed.

  Global Instance uninit_sync n : Sync (uninit n).
  Proof. apply product_sync, Forall_replicate, _. Qed.

  (* Unfolding lemma, kep only for backwards compatibility. *)
  Lemma uninit_own n tid vl :
    (uninit n).(ty_own) tid vl ⊣⊢ ⌜list_ty_size vl = n⌝.
  Proof. done. Qed.

  (* this should be subtype, since uninit n is now stronger than uninit 0 *)
  Lemma uninit_uninit0_subtype E L n :
    subtype E L (uninit0 n) (uninit n).
  Proof.
    apply type_incl_subtype. iIntros "". rewrite /type_incl.
    iSplit; last iSplit.
    - by rewrite uninit0_sz /uninit /=.
    - iIntros "!>" (??) "Hown". rewrite uninit0_own /uninit /=. by iDestruct "Hown" as "[_ ?]".
    - iIntros "!>" (???) "Hshr". done.
  Qed.

  Lemma uninit_product_subtype_cons_r {E L} (n : nat) ty tyl :
    ty.(ty_size) ≤ n →
    subtype E L (uninit ty.(ty_size)) ty →
    subtype E L (uninit (n-ty.(ty_size))) (Π tyl) →
    subtype E L (uninit n) (Π(ty :: tyl)).
  Proof.
    intros ?%Nat2Z.inj_le.
    intros.
    admit.
  Admitted.

  Lemma uninit_product_subtype_cons_l {E L} (n : nat) ty tyl :
    ty.(ty_size) ≤ n →
    subtype E L ty (uninit ty.(ty_size)) →
    subtype E L (Π tyl) (uninit (n-ty.(ty_size))) →
    subtype E L (Π(ty :: tyl)) (uninit n).
  Proof.
    intros ?%Nat2Z.inj_le.
    admit.
  Admitted.

  Lemma uninit_product_eqtype_cons_r {E L} (n : nat) ty tyl :
    ty.(ty_size) ≤ n →
    eqtype E L (uninit ty.(ty_size)) ty →
    eqtype E L (uninit (n-ty.(ty_size))) (Π tyl) →
    eqtype E L (uninit n) (Π(ty :: tyl)).
  Proof.
    intros ? [] []. split.
    - by apply uninit_product_subtype_cons_r.
    - by apply uninit_product_subtype_cons_l.
  Qed.
  Lemma uninit_product_eqtype_cons_l {E L} (n : nat) ty tyl :
    ty.(ty_size) ≤ n →
    eqtype E L ty (uninit ty.(ty_size)) →
    eqtype E L (Π tyl) (uninit (n-ty.(ty_size))) →
    eqtype E L (Π(ty :: tyl)) (uninit n).
  Proof. symmetry. by apply uninit_product_eqtype_cons_r. Qed.

  Lemma uninit_unit_eqtype E L n :
    n = 0%nat →
    eqtype E L (uninit n) unit.
  Proof. intros. apply eqtype_unfold. 
    iIntros (??) "HL !>HE".
    rewrite /type_equal.
    iSplit; first done. subst n. rewrite /uninit /unit /=.
    iSplit; last done.
    iIntros "!>" (??).
    iSplit; iIntros "%H"; iPureIntro; last rewrite H lty_size_emp //.
    destruct vl; try done. exfalso. revert H. rewrite lty_cons.
    assert (val_size v >= 1%nat) by apply val_gt1. lia.
  Qed.
  Lemma uninit_unit_eqtype' E L n :
    n = 0%nat →
    eqtype E L unit (uninit n).
  Proof. intros. symmetry. rewrite uninit_unit_eqtype; done. Qed.
  Lemma uninit_unit_subtype E L n :
    n = 0%nat →
    subtype E L (uninit n) unit.
  Proof. intros. 
    assert (eqtype E L (uninit n) unit) by rewrite uninit_unit_eqtype //.
    destruct H0 as [? ?]. apply H0.
  Qed.
  Lemma uninit_unit_subtype' E L n :
    n = 0%nat →
    subtype E L unit (uninit n).
  Proof.
    intros. 
    assert (eqtype E L unit (uninit n)) by rewrite uninit_unit_eqtype' //.
    destruct H0 as [? ?]. apply H0.
  Qed.
End uninit.

Global Hint Resolve uninit_product_eqtype_cons_l uninit_product_eqtype_cons_r
             uninit_product_subtype_cons_l uninit_product_subtype_cons_r
             uninit_unit_eqtype uninit_unit_eqtype'
             uninit_unit_subtype uninit_unit_subtype' : lrust_typing.
