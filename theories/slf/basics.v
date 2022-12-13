From iris.proofmode Require Import proofmode.
From lrust.typing Require Import typing.
From iris.prelude Require Import options.

Context `{!typeGS Σ}.
(*
  let incr =
    fun p →
      let n = !p in
      let m = n + 1 in
      p := m
*)
Definition incr : val :=
    fn: ["p"] := (* box *)
        let: "p'" := !"p" in (* we need to dereference p, to get the mutable reference *)
        let: "n" := !"p'" in (* and the value that the mutable reference is holding*)
        let: "m" := "n" + "n" in (* TODO: I changed "n" + #1 to "n" + "n", now `solve_typing` works *)
        "p'" <- "m";; 
        let: "r" := new [ #0] in return: ["r"]. (* returning unit needs to allocate an empty pointer *)

Lemma incr_type :
    typed_val incr (fn(∀ α, ∅; &uniq{α}(int)) → unit).
Proof.
  (* the first two line are mostly boilerplates *)
  intros E L. iApply type_fn; [solve_typing..|]. iIntros "/= !>". iIntros (α ϝ ret p).
  inv_vec p=>p. simpl_subst.
  iApply type_deref; [solve_typing..|]. iIntros (p'); simpl_subst.
  iApply type_deref; [solve_typing..|]. iIntros (n); simpl_subst.
  iApply type_let. { apply type_plus_instr. } { solve_typing. }
  iIntros (m); simpl_subst.
  iApply type_assign. { solve_typing. } { apply write_uniq; solve_typing. }
  iApply type_new; [solve_typing..|]. iIntros (r); simpl_subst.
  iApply type_jump. { solve_typing. } { solve_typing. }
  solve_typing.
Qed.
