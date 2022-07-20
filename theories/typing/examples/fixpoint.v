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
End fixpoint.
