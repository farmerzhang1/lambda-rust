From lrust.lang Require Import proofmode memcpy.
From lrust.typing Require Export type lft_contexts type_context cont_context.
From iris.prelude Require Import options.

Section typing.
  Context `{!typeGS Σ}.

  (** Function Body *)
  (* This is an iProp because it is also used by the function type. *)
  Definition typed_body (E : elctx) (L : llctx) (C : cctx) (T : tctx)
                        (e : expr) : iProp Σ :=
    (∀ tid (qmax : Qp), lft_ctx -∗ elctx_interp E -∗ na_own tid ⊤ -∗ llctx_interp qmax L -∗
               cctx_interp tid qmax C -∗ tctx_interp tid T -∗
               WP e {{ _, cont_postcondition }})%I.
  Global Arguments typed_body _ _ _ _ _%E.

  Global Instance typed_body_llctx_permut E :
    Proper ((≡ₚ) ==> eq ==> eq ==> eq ==> (⊢)) (typed_body E).
  Proof.
    intros L1 L2 HL C ? <- T ? <- e ? <-. rewrite /typed_body.
    by setoid_rewrite HL.
  Qed.

  Global Instance typed_body_elctx_permut :
    Proper ((≡ₚ) ==> eq ==> eq ==> eq ==> eq ==> (⊢)) typed_body.
  Proof.
    intros E1 E2 HE L ? <- C ? <- T ? <- e ? <-. rewrite /typed_body.
    by setoid_rewrite HE.
  Qed.

  Global Instance typed_body_mono E L:
    Proper (flip (cctx_incl E) ==> flip (tctx_incl E L) ==> eq ==> (⊢))
           (typed_body E L).
  Proof.
    intros C1 C2 HC T1 T2 HT e ? <-. iIntros "H".
    iIntros (tid qmax) "#LFT #HE Htl HL HC HT".
    iDestruct (llctx_interp_acc_noend with "HL") as "[HL HLclose]".
    iMod (HT with "LFT HE HL HT") as "(HL & HT)".
    iDestruct ("HLclose" with "HL") as "HL".
    iApply ("H" with "LFT HE Htl HL [HC] HT").
    by iApply (HC with "LFT HE HC").
  Qed.

  Lemma typed_body_tctx_incl E L T2 T1 C e :
    tctx_incl E L T1 T2 →
    (⊢ typed_body E L C T2 e) →
    ⊢ typed_body E L C T1 e.
  Proof.
    intros Hincl He2. iApply typed_body_mono; last done; done.
  Qed.

  Global Instance typed_body_mono_flip E L:
    Proper (cctx_incl E ==> tctx_incl E L ==> eq ==> flip (⊢))
           (typed_body E L).
  Proof. intros ?????????. by eapply typed_body_mono. Qed.

  (** Instruction *)
  Definition typed_instruction (E : elctx) (L : llctx)
             (T1 : tctx) (e : expr) (T2 : val → tctx) : iProp Σ :=
    (∀ tid qmax, lft_ctx -∗ elctx_interp E -∗ na_own tid ⊤ -∗
              llctx_interp qmax L -∗ tctx_interp tid T1 -∗
              WP e {{ v, na_own tid ⊤ ∗
                         llctx_interp qmax L ∗ tctx_interp tid (T2 v) }})%I.
  Global Arguments typed_instruction _ _ _ _%E _.

  (** Writing and Reading **)
  Definition typed_write_def (E : elctx) (L : llctx) (ty1 ty ty2 : type) : iProp Σ :=
    (□ ∀ v tid F qmax qL, ⌜↑lftN ∪ (↑lrustN) ⊆ F⌝ →
      lft_ctx -∗ elctx_interp E -∗ llctx_interp_noend qmax L qL -∗ ty1.(ty_own) tid [v] ={F}=∗
        ∃ (l : loc) vl, ⌜length vl = ty.(ty_size) ∧ v = #l⌝ ∗ l ↦∗ vl ∗
          (▷ l ↦∗: ty.(ty_own) tid ={F}=∗
            llctx_interp_noend qmax L qL ∗ ty2.(ty_own) tid [v]))%I.
  Definition typed_write_aux : seal (@typed_write_def). Proof. by eexists. Qed.
  Definition typed_write := typed_write_aux.(unseal).
  Definition typed_write_eq : @typed_write = @typed_write_def := typed_write_aux.(seal_eq).
  Global Arguments typed_write _ _ _%T _%T _%T.

  Global Instance typed_write_persistent (E : elctx) (L : llctx) (ty1 ty ty2 : type) :
    Persistent (typed_write E L ty1 ty ty2).
  Proof. rewrite typed_write_eq. apply _. Qed.

  (* Technically speaking, we could remvoe the vl quantifiaction here and use
     mapsto_pred instead (i.e., l ↦∗: ty.(ty_own) tid). However, that would
     make work for some of the provers way harder, since they'd have to show
     that nobody could possibly have changed the vl (because only half the
     fraction was given). So we go with the definition that is easier to prove. *)
  Definition typed_read_def (E : elctx) (L : llctx) (ty1 ty ty2 : type) : iProp Σ :=
    (□ ∀ v tid F qmax qL, ⌜↑lftN ∪ ↑lrustN ⊆ F⌝ →
      lft_ctx -∗ elctx_interp E -∗ na_own tid F -∗
      llctx_interp_noend qmax L qL -∗ ty1.(ty_own) tid [v] ={F}=∗
        ∃ (l : loc) vl q, ⌜v = #l⌝ ∗ l ↦∗{q} vl ∗ ▷ ty.(ty_own) tid vl ∗
              (l ↦∗{q} vl ={F}=∗ na_own tid F ∗
                              llctx_interp_noend qmax L qL ∗ ty2.(ty_own) tid [v]))%I.
  Definition typed_read_aux : seal (@typed_read_def). Proof. by eexists. Qed.
  Definition typed_read := typed_read_aux.(unseal).
  Definition typed_read_eq : @typed_read = @typed_read_def := typed_read_aux.(seal_eq).
  Global Arguments typed_read _ _ _%T _%T _%T.

  Global Instance typed_read_persistent (E : elctx) (L : llctx) (ty1 ty ty2 : type) :
    Persistent (typed_read E L ty1 ty ty2).
  Proof. rewrite typed_read_eq. apply _. Qed.
End typing.

Definition typed_instruction_ty `{!typeGS Σ} (E : elctx) (L : llctx) (T : tctx)
    (e : expr) (ty : type) : iProp Σ :=
  typed_instruction E L T e (λ v, [v ◁ ty]).
Global Arguments typed_instruction_ty {_ _} _ _ _ _%E _%T.

Definition typed_val `{!typeGS Σ} (v : val) (ty : type) : Prop :=
  ∀ E L, ⊢ typed_instruction_ty E L [] (of_val v) ty.
Global Arguments typed_val _ _ _%V _%T.

Section typing_rules.
  Context `{!typeGS Σ}.

  (* This lemma is helpful when switching from proving unsafe code in Iris
     back to proving it in the type system. *)
  Lemma type_type E L C T e :
    typed_body E L C T e -∗ typed_body E L C T e.
  Proof. done. Qed.

  (** This lemma can replace [κ1] by [κ2] and vice versa in positions that
  respect "semantic lifetime equivalence"; in particular, lifetimes of
  references can be adjusted this way.  However, it cannot replace lifetimes in
  other type constructors, as those might only respect *syntactic* lifetime
  equivalence. This lemma is *weaker* than what was in the original paper where
  lifetimes could be replaced everywhere; it had to be adjusted for GhostCell.
  See [typing.lib.diverging_static] for an example of how
  [type_equivalize_lft_static] without this restriction ciuld be used to subvert
  branding.

  This is technically not a proper typing rule since the type system has no way
  to express "subtyping wrt semantic lifetime inclusion".  However, there is no
  fundamental reason that we could not also reflect all these semantic facts on
  the syntactic side, it would just be very clunky (and note that in Coq we do
  not reflect this syntactic side anway). *)
  Lemma type_equivalize_lft E L C T1 T2 κ1 κ2 e :
    (∀ tid, lft_ctx -∗ κ1 ⊑ κ2 -∗ κ2 ⊑ κ1 -∗ tctx_interp tid T1 -∗ tctx_interp tid T2) →
    (⊢ typed_body E L C T2 e) →
    ⊢ typed_body E ((κ1 ⊑ₗ [κ2]) :: L) C T1 e.
  Proof.
    iIntros (Hswitch He tid qmax) "#LFT #HE Htl [Hκ HL] HC HT".
    iMod (lctx_equalize_lft_sem with "LFT Hκ") as "[Hκ1 Hκ2]".
    iApply (He with "LFT HE Htl HL HC [-]").
    iApply (Hswitch with "LFT Hκ1 Hκ2"). done.
  Qed.
  Lemma type_equivalize_lft_static E L C T1 T2 κ e :
    (∀ tid, lft_ctx -∗ static ⊑ κ -∗ tctx_interp tid T1 -∗ tctx_interp tid T2) →
    (⊢ typed_body E L C T2 e) →
    ⊢ typed_body E ((κ ⊑ₗ []) :: L) C T1 e.
  Proof.
    iIntros (Hswitch He tid qmax) "#LFT #HE Htl [Hκ HL] HC HT".
    iMod (lctx_equalize_lft_sem_static with "LFT Hκ") as "Hκ".
    iApply (He with "LFT HE Htl HL HC [-]").
    iApply (Hswitch with "LFT Hκ"). done.
  Qed.

  Lemma type_let' E L T1 T2 (T : tctx) C xb e e' :
    Closed (xb :b: []) e' →
    typed_instruction E L T1 e T2 -∗
    (∀ v : val, typed_body E L C (T2 v ++ T) (subst' xb v e')) -∗
    typed_body E L C (T1 ++ T) (let: xb := e in e').
  Proof.
    iIntros (Hc) "He He'". iIntros (tid qmax) "#LFT #HE Htl HL HC HT". rewrite tctx_interp_app.
    iDestruct "HT" as "[HT1 HT]". wp_bind e. iApply (wp_wand with "[He HL HT1 Htl]").
    { iApply ("He" with "LFT HE Htl HL HT1"). }
    iIntros (v) "/= (Htl & HL & HT2)". wp_let.
    iApply ("He'" with "LFT HE Htl HL HC [HT2 HT]").
    rewrite tctx_interp_app. by iFrame.
  Qed.

  (* We do not make the [typed_instruction] hypothesis part of the
     Iris hypotheses, because we want to preserve the order of the
     hypotheses. The is important, since proving [typed_instruction]
     will instantiate [T1] and [T2], and hence we know what to search
     for the following hypothesis. *)
  Lemma type_let E L T T' T1 T2 C xb e e' :
    Closed (xb :b: []) e' →
    (⊢ typed_instruction E L T1 e T2) →
    tctx_extract_ctx E L T1 T T' →
    (∀ v : val, typed_body E L C (T2 v ++ T') (subst' xb v e')) -∗
    typed_body E L C T (let: xb := e in e').
  Proof.
    unfold tctx_extract_ctx. iIntros (? He ->) "?". iApply type_let'; last done.
    iApply He.
  Qed.

  Lemma type_seq E L T T' T1 T2 C e e' :
    Closed [] e' →
    (⊢ typed_instruction E L T1 e (λ _, T2)) →
    tctx_extract_ctx E L T1 T T' →
    typed_body E L C (T2 ++ T') e' -∗
    typed_body E L C T (e ;; e').
  Proof. iIntros. iApply (type_let E L T T' T1 (λ _, T2)); auto. Qed.

  Lemma type_newlft {E L C T} κs e :
    Closed [] e →
    (∀ κ, typed_body E ((κ ⊑ₗ κs) :: L) C T e) -∗
    typed_body E L C T (Newlft ;; e).
  Proof.
    iIntros (Hc) "He". iIntros (tid qmax) "#LFT #HE Htl HL HC HT".
    iMod (lft_create with "LFT") as (Λ) "[Htk #Hinh]"; first done.
    set (κ' := lft_intersect_list κs). wp_seq.
    iApply ("He" $! (κ' ⊓ Λ) with "LFT HE Htl [HL Htk] HC HT").
    rewrite /llctx_interp /=. iFrame "HL".
    iExists Λ. iSplit; first done.
    destruct (decide (1 ≤ qmax)%Qp) as [_|Hlt%Qp.lt_nge].
    - by iFrame "#∗".
    - apply Qp.lt_sum in Hlt as [q' ->]. iDestruct "Htk" as "[$ Htk]".
      iIntros "Htk'". iApply "Hinh". iFrame.
  Qed.

  (* TODO: It should be possible to show this while taking only one step.
     Right now, we could take two. *)
  Lemma type_endlft E L C T1 T2 κ κs e :
    Closed [] e → UnblockTctx κ T1 T2 →
    typed_body E L C T2 e -∗ typed_body E ((κ ⊑ₗ κs) :: L) C T1 (Endlft ;; e).
  Proof.
    iIntros (Hc Hub) "He". iIntros (tid qmax) "#LFT #HE Htl [Hκ HL] HC HT".
    iDestruct "Hκ" as (Λ) "(% & Htok & Hend)".
    iSpecialize ("Hend" with "Htok"). wp_bind Endlft.
    iApply (wp_mask_mono _ (↑lftN ∪ lft_userE)); first done.
    iApply (wp_step_fupd with "Hend"); first set_solver+. wp_seq.
    iIntros "#Hdead !>". wp_seq. iApply ("He" with "LFT HE Htl HL HC [> -]").
    iApply (Hub with "[] HT"). simpl in *. subst κ. rewrite -lft_dead_or. auto.
  Qed.

  Lemma type_path_instr {E L} p ty :
    ⊢ typed_instruction_ty E L [p ◁ ty] p ty.
  Proof.
    iIntros (??) "_ _ $$ [? _]".
    iApply (wp_hasty with "[-]"); first done. iIntros (v) "_ Hv".
    rewrite tctx_interp_singleton. iExists v. iFrame. by rewrite eval_path_of_val.
  Qed.

  Lemma type_letpath {E L} ty C T T' x p e :
    Closed (x :b: []) e →
    tctx_extract_hasty E L p ty T T' →
    (∀ (v : val), typed_body E L C ((v ◁ ty) :: T') (subst' x v e)) -∗
    typed_body E L C T (let: x := p in e).
  Proof. iIntros. iApply type_let; [by apply type_path_instr|solve_typing|done]. Qed.

  Lemma type_assign_instr {E L} ty ty1 ty1' p1 p2 :
    (⊢ typed_write E L ty1 ty ty1') →
    (⊢ typed_instruction E L [p1 ◁ ty1; p2 ◁ ty] (p1 <- p2) (λ _, [p1 ◁ ty1'])).
  Proof.
    iIntros (Hwrt tid ?) "#LFT #HE $ HL".
    rewrite tctx_interp_cons tctx_interp_singleton. iIntros "[Hp1 Hp2]".
    wp_bind p1. iApply (wp_hasty with "Hp1"). iIntros (v1) "% Hown1".
    wp_bind p2. iApply (wp_hasty with "Hp2"). iIntros (v2) "_ Hown2".
    rewrite typed_write_eq in Hwrt.
    iDestruct (llctx_interp_acc_noend with "HL") as "[HL HLclose]".
    iMod (Hwrt with "[] LFT HE HL Hown1") as (l vl) "([% %] & Hl & Hclose)"; first done.
    subst v1. iDestruct (ty_size_eq with "Hown2") as "#Hsz". iDestruct "Hsz" as %Hsz.
    rewrite <-Hsz in *. destruct vl as [|v[|]]; try done.
    rewrite heap_mapsto_vec_singleton. iApply wp_fupd. wp_write.
    rewrite -heap_mapsto_vec_singleton.
    iMod ("Hclose" with "[Hl Hown2]") as "(HL & Hown)".
    { iExists _. iFrame. }
    iDestruct ("HLclose" with "HL") as "$".
    rewrite tctx_interp_singleton tctx_hasty_val' //.
  Qed.

  Lemma type_assign {E L} ty1 ty ty1' C T T' p1 p2 e:
    Closed [] e →
    tctx_extract_ctx E L [p1 ◁ ty1; p2 ◁ ty] T T' →
    (⊢ typed_write E L ty1 ty ty1') →
    typed_body E L C ((p1 ◁ ty1') :: T') e -∗
    typed_body E L C T (p1 <- p2 ;; e).
  Proof. iIntros. by iApply type_seq; first apply type_assign_instr. Qed.

  Lemma type_deref_instr {E L} ty ty1 ty1' p :
    ty.(ty_size) = 1%nat → (⊢ typed_read E L ty1 ty ty1') →
    (⊢ typed_instruction E L [p ◁ ty1] (!p) (λ v, [p ◁ ty1'; v ◁ ty])).
  Proof.
    iIntros (Hsz Hread tid qmax) "#LFT #HE Htl HL Hp".
    rewrite tctx_interp_singleton. wp_bind p. iApply (wp_hasty with "Hp").
    iIntros (v) "% Hown".
    rewrite typed_read_eq in Hread.
    iDestruct (llctx_interp_acc_noend with "HL") as "[HL HLclose]".
    iMod (Hread with "[] LFT HE Htl HL Hown") as
        (l vl q) "(% & Hl & Hown & Hclose)"; first done.
    subst v. iDestruct (ty_size_eq with "Hown") as "#>%". rewrite ->Hsz in *.
    destruct vl as [|v [|]]; try done.
    rewrite heap_mapsto_vec_singleton. iApply wp_fupd. wp_read.
    iMod ("Hclose" with "Hl") as "($ & HL & Hown2)".
    iDestruct ("HLclose" with "HL") as "$".
    rewrite tctx_interp_cons tctx_interp_singleton tctx_hasty_val tctx_hasty_val' //.
    by iFrame.
  Qed.

  Lemma type_deref {E L} ty1 C T T' ty ty1' x p e:
    Closed (x :b: []) e →
    tctx_extract_hasty E L p ty1 T T' →
    (⊢ typed_read E L ty1 ty ty1') →
    ty.(ty_size) = 1%nat →
    (∀ (v : val), typed_body E L C ((p ◁ ty1') :: (v ◁ ty) :: T') (subst' x v e)) -∗
    typed_body E L C T (let: x := !p in e).
  Proof. iIntros. by iApply type_let; [apply type_deref_instr|solve_typing|]. Qed.

  Lemma type_memcpy_iris E L qmax qL tid ty ty1 ty1' ty2 ty2' (n : Z) p1 p2 :
    Z.of_nat (ty.(ty_size)) = n →
    typed_write E L ty1 ty ty1' -∗ typed_read E L ty2 ty ty2' -∗
    {{{ lft_ctx ∗ elctx_interp E ∗ na_own tid ⊤ ∗ llctx_interp_noend qmax L qL ∗
        tctx_elt_interp tid (p1 ◁ ty1) ∗ tctx_elt_interp tid (p2 ◁ ty2) }}}
      (p1 <-{n} !p2)
    {{{ RET #☠; na_own tid ⊤ ∗ llctx_interp_noend qmax L qL ∗
                 tctx_elt_interp tid (p1 ◁ ty1') ∗ tctx_elt_interp tid (p2 ◁ ty2') }}}.
  Proof.
    iIntros (<-) "#Hwrt #Hread !>".
    iIntros (Φ) "(#LFT & #HE & Htl & [HL1 HL2] & [Hp1 Hp2]) HΦ".
    wp_bind p1. iApply (wp_hasty with "Hp1"). iIntros (v1) "% Hown1".
    wp_bind p2. iApply (wp_hasty with "Hp2"). iIntros (v2) "% Hown2".
    rewrite typed_write_eq typed_read_eq.
    iMod ("Hwrt" with "[] LFT HE HL1 Hown1")
      as (l1 vl1) "([% %] & Hl1 & Hcl1)"; first done.
    iMod ("Hread" with "[] LFT HE Htl HL2 Hown2")
      as (l2 vl2 q2) "(% & Hl2 & Hown2 & Hcl2)"; first done.
    iDestruct (ty_size_eq with "Hown2") as "#>%". subst v1 v2. iApply wp_fupd.
    iApply (wp_memcpy with "[$Hl1 $Hl2]"); try congruence; [].
    iNext. iIntros "[Hl1 Hl2]". iApply ("HΦ" with "[> -]"). rewrite !tctx_hasty_val' //.
    iMod ("Hcl1" with "[Hl1 Hown2]") as "($ & $)".
    { iExists _. iFrame. }
    iMod ("Hcl2" with "Hl2") as "($ & $ & $)". done.
  Qed.

  Lemma type_memcpy_instr {E L} ty ty1 ty1' ty2 ty2' (n : Z) p1 p2 :
    Z.of_nat (ty.(ty_size)) = n →
    (⊢ typed_write E L ty1 ty ty1') →
    (⊢ typed_read E L ty2 ty ty2') →
    ⊢ typed_instruction E L [p1 ◁ ty1; p2 ◁ ty2] (p1 <-{n} !p2)
                      (λ _, [p1 ◁ ty1'; p2 ◁ ty2']).
  Proof.
    iIntros (Hsz Hwrt Hread tid qmax) "#LFT #HE Htl HL HT".
    iDestruct (llctx_interp_acc_noend with "HL") as "[HL HLclose]".
    iApply (type_memcpy_iris with "[] [] [$LFT $Htl $HE $HL HT]"); try done.
    { by rewrite tctx_interp_cons tctx_interp_singleton. }
    rewrite tctx_interp_cons tctx_interp_singleton.
    iIntros "!> ($ & HL & $ & $)". by iApply "HLclose".
  Qed.

  Lemma type_memcpy {E L} ty ty1 ty2 (n : Z) C T T' ty1' ty2' p1 p2 e:
    Closed [] e →
    tctx_extract_ctx E L [p1 ◁ ty1; p2 ◁ ty2] T T' →
    (⊢ typed_write E L ty1 ty ty1') →
    (⊢ typed_read E L ty2 ty ty2') →
    Z.of_nat (ty.(ty_size)) = n →
    typed_body E L C ((p1 ◁ ty1') :: (p2 ◁ ty2') :: T') e -∗
    typed_body E L C T (p1 <-{n} !p2;; e).
  Proof. iIntros. by iApply type_seq; first eapply (type_memcpy_instr ty ty1 ty1'). Qed.
End typing_rules.
