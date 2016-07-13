From iris.proofmode Require Import coq_tactics.
From iris.proofmode Require Export weakestpre.
From lrust Require Export wp_tactics heap.
Import uPred.

Ltac wp_strip_later ::= iNext.

Section heap.
Context {Σ : gFunctors} `{heapG Σ}.
Implicit Types N : namespace.
Implicit Types P Q : iPropG lrust_lang Σ.
Implicit Types Φ : val → iPropG lrust_lang Σ.
Implicit Types Δ : envs (iResUR lrust_lang (globalF Σ)).

Global Instance into_sep_mapsto l q v :
  IntoSep false (l ↦{q} v) (l ↦{q/2} v) (l ↦{q/2} v).
Proof. by rewrite /IntoSep heap_mapsto_op_split. Qed.

Global Instance into_sep_mapsto_vec l q vl :
  IntoSep false (l ↦★{q} vl) (l ↦★{q/2} vl) (l ↦★{q/2} vl).
Proof. by rewrite /IntoSep heap_mapsto_vec_op_split. Qed.

Lemma tac_wp_alloc Δ Δ' N E j1 j2 n Φ :
  (Δ ⊢ heap_ctx N) → nclose N ⊆ E → 0 < n →
  IntoLaterEnvs Δ Δ' →
  (∀ l vl, n = length vl → ∃ Δ'',
    envs_app false (Esnoc (Esnoc Enil j1 (l ↦★ vl)) j2 (†l…(Z.to_nat n))) Δ'
      = Some Δ'' ∧
    (Δ'' ⊢ |={E}=> Φ (LitV $ LitLoc l))) →
  Δ ⊢ WP Alloc (Lit $ LitInt n) @ E {{ Φ }}.
Proof.
  intros ???? HΔ. rewrite -wp_alloc // -always_and_sep_l.
  apply and_intro; first done.
  rewrite into_later_env_sound; apply later_mono, forall_intro=> l;
  apply forall_intro=> vl. apply wand_intro_l. rewrite -assoc.
  apply pure_elim_sep_l=> Hn. apply wand_elim_r'.
  destruct (HΔ l vl) as (Δ''&?&HΔ'). done.
  rewrite envs_app_sound //; simpl. by rewrite right_id HΔ'.
Qed.

Lemma tac_wp_read Δ Δ' N E i l q v o Φ :
  (Δ ⊢ heap_ctx N) → nclose N ⊆ E → o = Na1Ord ∨ o = ScOrd →
  IntoLaterEnvs Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v)%I →
  (Δ' ⊢ |={E}=> Φ v) →
  Δ ⊢ WP Read o (Lit $ LitLoc l) @ E {{ Φ }}.
Proof.
  intros ??[->| ->]???.
  - rewrite -wp_read_na // -always_and_sep_l. apply and_intro; first done.
    rewrite into_later_env_sound -later_sep envs_lookup_split //; simpl.
      by apply later_mono, sep_mono_r, wand_mono.
  - rewrite -wp_read_sc // -always_and_sep_l. apply and_intro; first done.
    rewrite into_later_env_sound -later_sep envs_lookup_split //; simpl.
      by apply later_mono, sep_mono_r, wand_mono.
Qed.

Lemma tac_wp_write Δ Δ' Δ'' N E i l v e v' o Φ :
  to_val e = Some v' →
  (Δ ⊢ heap_ctx N) → nclose N ⊆ E → o = Na1Ord ∨ o = ScOrd →
  IntoLaterEnvs Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v')) Δ' = Some Δ'' →
  (Δ'' ⊢ |={E}=> Φ (LitV LitUnit)) →
  Δ ⊢ WP Write o (Lit $ LitLoc l) e @ E {{ Φ }}.
Proof.
  intros ???[->| ->]????.
  - rewrite -wp_write_na // -always_and_sep_l. apply and_intro; first done.
    rewrite into_later_env_sound -later_sep envs_simple_replace_sound //; simpl.
    rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
  - rewrite -wp_write_sc // -always_and_sep_l. apply and_intro; first done.
    rewrite into_later_env_sound -later_sep envs_simple_replace_sound //; simpl.
    rewrite right_id. by apply later_mono, sep_mono_r, wand_mono.
Qed.

End heap.

Tactic Notation "wp_apply" open_constr(lem) :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q => reshape_expr e ltac:(fun K e' =>
    wp_bind K; iApply lem; try iNext)
  | _ => fail "wp_apply: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) ident(vl) "as" constr(H) constr(Hf) :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         match eval hnf in e' with Alloc _ => wp_bind K end)
      |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
    eapply tac_wp_alloc with _ _ H Hf;
      [iAssumption || fail "wp_alloc: cannot find heap_ctx"
      |solve_ndisj
      |try fast_done
      |apply _
      |first [intros l vl ? | fail 1 "wp_alloc:" l "or" vl "not fresh"];
        eexists; split;
          [env_cbv; reflexivity || fail "wp_alloc:" H "or" Hf "not fresh"
          |wp_finish]]
  | _ => fail "wp_alloc: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) ident(vl) :=
  let H := iFresh in let Hf := iFresh in wp_alloc l vl as H Hf.

Tactic Notation "wp_read" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         match eval hnf in e' with Read _ _ => wp_bind K end)
      |fail 1 "wp_read: cannot find 'Read' in" e];
    eapply tac_wp_read;
      [iAssumption || fail "wp_read: cannot find heap_ctx"
      |solve_ndisj
      |(right; fast_done) || (left; fast_done) ||
       fail "wp_read: order is neither Na2Ord nor ScOrd"
      |apply _
      |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
       iAssumptionCore || fail "wp_read: cannot find" l "↦ ?"
      |wp_finish]
  | _ => fail "wp_read: not a 'wp'"
  end.

Tactic Notation "wp_write" :=
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         match eval hnf in e' with Write _ _ _ => wp_bind K end)
      |fail 1 "wp_write: cannot find 'Write' in" e];
    eapply tac_wp_write;
      [let e' := match goal with |- to_val ?e' = _ => e' end in
       wp_done || fail "wp_write:" e' "not a value"
      |iAssumption || fail "wp_write: cannot find heap_ctx"
      |solve_ndisj
      |(right; fast_done) || (left; fast_done) ||
       fail "wp_write: order is neither Na2Ord nor ScOrd"
      |apply _
      |let l := match goal with |- _ = Some (_, (?l ↦{_} _)%I) => l end in
       iAssumptionCore || fail "wp_write: cannot find" l "↦ ?"
      |env_cbv; reflexivity
      |wp_finish]
  | _ => fail "wp_write: not a 'wp'"
  end.
