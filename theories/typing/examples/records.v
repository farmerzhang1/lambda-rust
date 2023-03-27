From iris.program_logic Require Export adequacy weakestpre.
From iris.algebra Require Import auth.
From lrust.lang Require Export heap.
From lrust.lang Require Import proofmode notation.
From lrust.typing Require Export type.
From lrust.typing Require Import typing.
From iris.prelude Require Import options.

Check (Closed [] (rec: "mkobj" ["repr"] :=
  "repr" ↓ "x")%V).
Compute (Closed [] (rec: "mkobj" ["repr"] :=
  "repr" ↓ "x")%V).

Check (Closed ("mkobj" :b: ["repr"]%binder +b+ []) ("repr" ↓ "x")%E).
Compute (Closed ("mkobj" :b: ["repr"]%binder +b+ []) ("repr" ↓ "x")%E).

Definition obj_test : val :=
  rec: "mkobj" ["repr"] :=
    "repr" ↓ "x".

    (* "get" r: "repr" ↓ "x" :r: 
    "set" r: (λ: ["n"], ("mkobj" ["x" r: "n" :r: rnil])) :r:
    "bump" r: ("mkobj" [ ("x" r: (("repr" ↓ "x") + #1) :r: rnil)%E ]) :r: rnil%E. *)

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

Definition try_obj : val := rec: "mkobj" ["repr"] :=
  "get" r: "repr" ↓ "x" :r: 
  "set" r: (λ "n", "mkobj" ["x" r: "n" :r: rnil]) :r:
  "bump" : "mkobj" ["x" : "repr" ↓ "x" + #1] :r: rnil

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
  admit.
Admitted.
(* TODO *)
End typing.
