From iris.proofmode Require Import proofmode.
From lrust.typing Require Import typing record.
From iris.prelude Require Import options.

Section record.
Context `{!typeGS Σ}.

Definition recordv_example := RecordNil.
Definition record_type := record [("x", int); ("y", int); ("z", bool)].


End record.
