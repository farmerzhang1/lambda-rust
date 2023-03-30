From iris.program_logic Require Export adequacy weakestpre.
From iris.algebra Require Import auth.
From lrust.lang Require Export heap.
From lrust.lang Require Import proofmode notation.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
From iris.prelude Require Import options.

Section record.
Context `{!typeGS Σ}.
Notation iProp := (iProp Σ).

Definition re1 := rnil%E.
Definition re2 := ("i1" r: #1 + #2 :r: "i2" r: #2 :r: rnil)%E.
Definition re3 := ("i1" r: #12 :r: "i2" r: #2 :r: rnil)%V.

Definition record_type := record [("i1", int); ("i2", int)].

Example re1_spec: ⊢ WP re1 {{ v, ⌜ v = RecordVNil ⌝ } }.
Proof.
rewrite /re1.
by iApply wp_value.
Qed.

Example re2_spec: ⊢ WP re2 {{ v,  ⌜ v = ("i1" r: #3 :r: "i2" r: #2 :r: rnil)%V ⌝ }}.
Proof.
rewrite /re2.
by wp_op.
Qed.
End record.

Section typing.
Context `{!typeGS Σ}.
Lemma re2_typed :  typed_val re3 record_type.
Proof.
  intros E L. iIntros (??) "lft #E Hna L T". rewrite /re3. iApply wp_value. iFrame.
  rewrite tctx_hasty_val. rewrite /record_type. iExists #12, ("i2" r: #2 :r: rnil)%V.
  iSplit; first done. iSplit; first done.
  iExists #2, rnil%V.
  iSplit; first done. iSplit; first done. rewrite /rnil' //.
Qed.

(* `{!TyWf t} *)
Definition fn_ty t := fn (λ _: (), FP (λ ϝ, ∅ ϝ) Vector.nil t).
Definition obj_pre t : type := record [("x", int); ("y", int); ("area", fn_ty t)].
Definition obj_pre1 t := record [("x", int); ("y", int); ("area", box t)].

Local Instance obj_contractive : TypeContractive obj_pre.
Proof.
  intros n o1 o2 Ho.
  rewrite /obj_pre.
  replace ([("x", int); ("y", int); ("area", fn_ty o1)]) with (zip ["x"; "y"; "area"] [int; int; fn_ty o1]); last done.
  replace ([("x", int); ("y", int); ("area", fn_ty o2)]) with (zip ["x"; "y"; "area"] [int; int; fn_ty o2]); last done.
  apply record_proper. (* well I guess f_equiv can't detect this directly*)
  rewrite /fn_ty. repeat f_equiv; simpl; [done | apply Ho].
Qed.

Local Instance obj_contractive1 : TypeContractive obj_pre1.
Proof.
  intros n o1 o2 Ho.
  rewrite /obj_pre1.
  replace ([("x", int); ("y", int); ("area", box o1)]) with (zip ["x"; "y"; "area"] [int; int; box o1]); last done.
  replace ([("x", int); ("y", int); ("area", box o2)]) with (zip ["x"; "y"; "area"] [int; int; box o2]); last done.
  apply record_proper. (* well I guess f_equiv can't detect this directly*)
  repeat f_equiv.
  apply Ho.
Qed.

Definition obj := type_fixpoint obj_pre.
Definition obj1 := type_fixpoint obj_pre1.

Definition obj_sub E L : subtype E L obj obj1.
Proof.
  apply fixpoint_mono. intros. unfold obj_pre, obj_pre1.
  admit.
Admitted.

Definition set_fn t := fn (λ _: (), FP (λ ϝ, ∅ ϝ) (Vector.cons int Vector.nil) t).
Definition counter_pre t : type := record [("get", int); ("set",  set_fn t); ("bump", box t)].

Local Instance counter_contractive : TypeContractive counter_pre.
Proof.
  intros n t1 t2 Ht.
  rewrite /counter_pre.
  replace ([("get", int); ("set", set_fn t1); ("bump", box t1)])
    with (zip ["get"; "set"; "bump"] [int; set_fn t1; box t1]); last done.
  replace ([("get", int); ("set", set_fn t2); ("bump", box t2)])
    with (zip ["get"; "set"; "bump"] [int; set_fn t2; box t2]); last done.
  apply record_proper. rewrite /set_fn.
  repeat f_equiv; simpl; first f_equiv; apply Ht.
Qed.

Definition mkobj_fn : val := fnrec: "mkobj" ["repr'"] :=
  let: "repr" := !"repr'" in
  let: "proj" := "repr" ↓ "x" in
  let: "set_fn" := (fn: ["n"] :=
    let: "n'" := !"n" in
    let: "rec" := "x" r: "n'" :r: rnil in
    let: "pp" := new [(#2)%V] in
    "pp" <- "rec";;         (* don't know why it has to add a % *)
    letcall: "obj" := "mkobj" ["pp"]%E in
    "return" ["obj"]) in
  let: "proj1" := "proj" + "proj" in
  let: "rec" := "x" r: "proj1" :r: rnil in
  let: "pp" := new [(#2)%V] in
  "pp" <- "rec";;
  letcall: "bumped" := "mkobj" ["pp"]%E in
  let: "last" := "bump" r: "bumped" :r: rnil in
  let: "middle" := "set" r: "set_fn" :r: "last" in
  let: "r" := "get" r: "proj" :r: "middle" in
  let: "rp" := new [(#4)%V] in
  "rp" <- "r";;
  "return" ["rp"].

Definition repr_ty := record [("x", int)].
Definition counter_ty := type_fixpoint counter_pre.

Local Lemma counter_unfold :
  counter_ty ≡ counter_pre counter_ty.
Proof. apply type_fixpoint_unfold. Qed.

Lemma counter_size : counter_ty.(ty_size) = 4%nat.
Proof. rewrite counter_unfold //. Qed.

Lemma counter_typed `{!TyWf repr_ty} `{!TyWf counter_ty} : typed_val mkobj_fn (fn(∅; repr_ty) → counter_ty).
Proof.
  intros E L. rewrite /mkobj_fn /repr_ty.
  iApply type_rec; [done |].
  iIntros "/= !>".
  iIntros (?????).
  inv_vec args=>?. simpl_subst.
  iApply type_deref'; [solve_typing..| ].
  iIntros (r). simpl_subst.
  iApply (type_proj _ _ _ _ _ _ int _ _ _ [("x", int)]); [done | solve_typing.. |].
  iIntros (v). simpl_subst.
  (*               E L T T' T1 *)
  iApply (type_let _ _ _ _ [f ◁ (fn(∅; repr_ty) → counter_ty)]); [ | solve_typing |].
  {
    iApply (type_fn _ _ _ _ _ 1%nat
    (* the setter type *)
    (λ _: (), FP (λ ϝ, ∅ ϝ) (Vector.cons int Vector.nil) counter_ty)); 
      [solve_typing..|].
  iIntros "!>" (????).
  inv_vec args=>?. simpl_subst.
  iApply type_deref; [solve_typing..|].
  iIntros (?). simpl_subst.
  (* tctx_extract_ctx T1 T2 T3: means we can
    split T2 into T1 and T3 (and the rest),
    it's not the other direction... *)
  iApply type_rcons'; [solve_typing|].
  iIntros (?). simpl_subst.
  iApply type_new; [solve_typing..|].
  iIntros (p); simpl_subst.
  iApply type_assign; [solve_typing..|].
    (*                   x E L C T T'*)
    iApply (type_letcall _ _ _ _ _ _).
    - rewrite Forall_singleton. solve_closed.
    - solve_typing.
    - solve_typing.
    - intros. simpl. admit.
    - simpl. solve_typing.
    - iIntros (?). simpl_subst. iApply type_jump; solve_typing.
  }
  iIntros (setter). simpl_subst.
  iApply type_plus; [solve_typing|].
  iIntros (?); simpl_subst.
  iApply type_rcons'; [solve_typing|].
  iIntros (?); simpl_subst.
  iApply type_new; [solve_typing..|].
  iIntros (p); simpl_subst.
  iApply type_assign; [solve_typing..|].
  iApply type_letcall; [solve_typing..|].
  iIntros (?); simpl_subst.
  iApply type_rcons'; [solve_typing..|].
  iIntros (?); simpl_subst.
  iApply type_rcons; [solve_typing|].
  iIntros (?); simpl_subst.
  iApply type_rcons; [solve_typing|].
  iIntros (?); simpl_subst.
  iApply type_new; [solve_typing..|].
  iIntros (?); simpl_subst.
  replace (fn (λ _ : (),
    {|
      fp_E := λ ϝ0 : lft, ∅ ϝ0;
      fp_tys := [#int];
      fp_ty := counter_ty
    |})) with (set_fn counter_ty); last done.
  iApply (type_assign _ _ (box counter_ty)); [solve_typing | | ].
  - replace (rcons ("get", int)
      (rcons ("set", set_fn counter_ty)
      (rcons ("bump", box counter_ty) rnil'))) 
      with (counter_pre counter_ty); last done.
    replace (counter_pre counter_ty) with counter_ty.
    + rewrite /box counter_size. iApply write_own. rewrite counter_size //.
    + clear. admit. (* rewrite counter_unfold. apply leibniz_equiv. *)
  - iApply type_jump; [solve_typing.. ].
  Admitted.

End typing.
