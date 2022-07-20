From iris.proofmode Require Import proofmode.
From lrust.typing Require Import typing.
From iris.prelude Require Import options.

Section fixpoint.
  Context `{!typeGS Σ}.

  Local Definition my_list_pre l : type := sum [ unit; box l].

  Local Instance my_list_contractive : TypeContractive my_list_pre.
  Proof.
    (* FIXME: solve_type_proper should handle this. *)
    intros n l1 l2 Hl. rewrite /my_list_pre.
    f_equiv. constructor; last constructor; last by constructor.
    - done.
    - f_equiv. done.
  Qed.

  Definition my_list := type_fixpoint my_list_pre.

  Local Lemma my_list_unfold :
    my_list ≡ my_list_pre my_list.
  Proof. apply type_fixpoint_unfold. Qed.

  Lemma my_list_size : my_list.(ty_size) = 2%nat.
  Proof. rewrite my_list_unfold. done. Qed.
End fixpoint.
