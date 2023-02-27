From iris.program_logic Require Export adequacy weakestpre.
From iris.algebra Require Import auth.
From lrust.lang Require Export heap.
From lrust.lang Require Import proofmode notation.
From lrust.typing Require Export type.
From lrust.typing Require Import record int bool.
From iris.prelude Require Import options.

Section record.
Context `{!typeGS Σ}.
Notation iProp := (iProp Σ).

Definition re1 := rnil%E.
Definition re2 := ("i1" /: #1 + #2 :+: "i2" /: #2 :+: rnil)%E.
Definition record_type := record [("x", int); ("y", int); ("z", bool)].

Example re1_spec: ⊢ WP re1 {{ v, ⌜ v = RecordVNil ⌝ } }.
Proof.
rewrite /re1.
by iApply wp_value.
Qed.

Example re2_spec: ⊢ WP re2 {{ v,  ⌜ v = ("i1" /: #3 :+: "i2" /: #2 :+: rnil)%V ⌝ }}.
Proof.
rewrite /re2.
by wp_op.
Qed.
End record.
