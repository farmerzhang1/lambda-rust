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
Definition prod_cont : TypeContractive prod_pre.
Proof.
    intros n p1 p2 Hp.
    rewrite /prod_pre. f_equiv.
    f_equiv.
    repeat f_equiv. apply Hp.
Qed.

Definition record_proper n ls : Proper (Forall2 (type_dist2 n) ==> type_dist2 n) 
  (λ ts, record (zip ls ts)).
Proof.
  (*
  If induction_arg is a natural, 
  then destruct natural behaves like 
  intros until natural 
  followed by destruct applied to 
  the last introduced hypothesis.
  *)
  intros ???.
  (* KEY! *)
  generalize dependent ls.
  induction H. (* induction on H, not the other list types *)
  - reflexivity.
  - destruct ls.
    + f_equal.
    + assert (∀ A B (x : A) (y : B) xs ys, zip (x :: xs) (y :: ys) = (x,y) :: zip xs ys); first done. 
      do 2 rewrite H1.
      apply rcons_proper; first apply H. apply IHForall2.
Qed.

Definition obj_pre t : type := record [("x", int); ("y", int); ("area", box t)].
Local Instance  obj_contractive : TypeContractive obj_pre.
Proof.
    intros n o1 o2 Ho.
    rewrite /obj_pre.
    replace ([("x", int); ("y", int); ("area", box o1)]) with (zip ["x"; "y"; "area"] [int; int; box o1]); last done.
    replace ([("x", int); ("y", int); ("area", box o2)]) with (zip ["x"; "y"; "area"] [int; int; box o2]); last done.
    apply record_proper.
    repeat f_equiv.
    apply Ho.
Qed.

Definition obj := type_fixpoint obj_pre.
(* TODO *)
End typing.
