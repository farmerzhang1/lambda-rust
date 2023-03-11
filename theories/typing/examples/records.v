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
Definition record_type := record [("x", int); ("y", int); ("z", bool)].

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

Definition prod_pre t : type := Π [int; int; box t].
Local Instance prod_cont : TypeContractive prod_pre.
Proof.
  intros n p1 p2 Hp.
  rewrite /prod_pre. f_equiv.
  f_equiv.
  repeat f_equiv. apply Hp.
Qed.

Definition prod_pre1 t : type := Π [int; int; box t].
Local Instance prod_cont1 : TypeContractive prod_pre1.
Proof.
  intros n p1 p2 Hp.
  rewrite /prod_pre1. f_equiv.
  repeat f_equiv. apply Hp.
Qed.

Definition obj_sub E L : subtype E L (type_fixpoint prod_pre) (type_fixpoint prod_pre1).
Proof.
  apply fixpoint_mono. intros.
  apply product_mono. repeat f_equiv. apply H.
Qed.

Definition obj_pre t := record [("x", int); ("y", int); ("area", box t)].
Definition obj_pre1 t := record [("x", int); ("y", int); ("area", box t)].

Local Instance obj_contractive : TypeContractive obj_pre.
Proof.
  intros n o1 o2 Ho.
  rewrite /obj_pre.
  replace ([("x", int); ("y", int); ("area", box o1)]) with (zip ["x"; "y"; "area"] [int; int; box o1]); last done.
  replace ([("x", int); ("y", int); ("area", box o2)]) with (zip ["x"; "y"; "area"] [int; int; box o2]); last done.
  apply record_proper. (* well I guess f_equiv can't detect this directly*)
  repeat f_equiv.
  apply Ho.
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
(* TODO *)
End typing.
