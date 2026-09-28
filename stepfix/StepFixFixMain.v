(** * Main results: [step_fix_fix] is false, also at its use site in
    [asm_to_clight] / [backtranslation_proof].

    Imports security/BacktranslationProof2 (not in the Makefile; build.sh
    compiles it) only for the definitions [asm_program_is_wf],
    [wf_program_public], [asm_program_does_prefix] and for the admitted lemma
    [step_fix_fix] itself; these definitions and the statement of
    [step_fix_fix] are textually identical on ccs-backtranslation. *)

Require Import Coqlib Maps Integers Values Memory Globalenvs.
Require Import AST Smallstep Events Behaviors.
Require Import riscV.Asm.
Require Import BtBasics BtInfoAsm.
Require BacktranslationProof2.
Require Import StepFixFix.StepFixFixCommon.
Require StepFixFix.StepFixFixCheckpub StepFixFix.StepFixFixCallsig.
Require StepFixFix.StepFixFixBuiltinRes StepFixFix.StepFixFixEccMemcpy.

Module P1 := StepFixFix.StepFixFixCheckpub.
Module P2 := StepFixFix.StepFixFixCallsig.
Module P3 := StepFixFix.StepFixFixBuiltinRes.
Module P4 := StepFixFix.StepFixFixEccMemcpy.

(** ** Our restatement is (convertible to) the type of the admitted lemma. *)
Definition step_fix_fix_has_type_step_fix_fix_stmt : step_fix_fix_stmt :=
  BacktranslationProof2.step_fix_fix.

(** ** The admitted lemma is false (four independent counterexamples). *)
Theorem not_step_fix_fix : ~ step_fix_fix_stmt.
Proof. exact P1.not_step_fix_fix_checkpub. Qed.

(** Hence the development that contains the admitted lemma is inconsistent. *)
Theorem step_fix_fix_proves_False : False.
Proof. exact (not_step_fix_fix BacktranslationProof2.step_fix_fix). Qed.

(** ** The use site.

    [asm_to_clight] (BacktranslationProof2.v:1255 on ccs-backtranslation)
    has hypotheses [wf_program p], [wf_program_public p], [wf_main p],
    [wf_main_sig p], [exists s, Asm.initial_state p s], the trace bound and
    [asm_program_does_prefix p tr] (plus the section hypotheses EFO/IAO,
    which are about [external_functions_sem]/[inline_assembly_sem] only and
    do not mention the program).  It turns the latter into
    [star Asm.step s0 tr s'] for an initial state [s0] and some [s']
    ([semantics_has_initial_trace_prefix_implies_cut]) and applies
    [step_fix_fix] to it.  [backtranslation_proof] (line ~1473) has
    hypothesis [asm_program_is_wf p] and calls [asm_to_clight]. *)

Definition asm_to_clight_hyps (p: Asm.program) (tr: trace) : Prop :=
  wf_program p /\ BacktranslationProof2.wf_program_public p /\ wf_main p /\ wf_main_sig p /\
  (exists s, Asm.initial_state p s) /\
  Z.of_nat (length tr) < Int64.modulus /\
  BacktranslationProof2.asm_program_does_prefix p tr.

(** [step_fix_fix] restricted to the instances [asm_to_clight] needs. *)
Definition step_fix_fix_use_site_stmt : Prop :=
  forall (p: Asm.program) (tr: trace) (s s': Asm.state),
    asm_to_clight_hyps p tr ->
    Asm.initial_state p s ->
    star (Asm.step (comp_of_main p)) (Genv.globalenv p) s tr s' ->
    star (step_fix (comp_of_main p)) (Genv.globalenv p) s tr s'.

(** What each counterexample file establishes, packaged. *)
Definition bad_program (p: Asm.program) (tr: trace) : Prop :=
  (exists s, initial_state p s) /\
  (forall s, initial_state p s ->
     exists s', star (Asm.step (comp_of_main p)) (Genv.globalenv p) s tr s') /\
  (forall s s', initial_state p s ->
     ~ star (step_fix (comp_of_main p)) (Genv.globalenv p) s tr s').

Lemma length_one_bound: forall (e: event), Z.of_nat (length (e :: nil)) < Int64.modulus.
Proof. intros e. vm_compute. reflexivity. Qed.

Lemma bad_program_does_prefix:
  forall p tr, bad_program p tr -> BacktranslationProof2.asm_program_does_prefix p tr.
Proof.
  intros p tr ([s INIT] & RUN & _).
  destruct (RUN s INIT) as [s' STAR].
  destruct (state_behaves_exists (Asm.semantics p) s') as [beh SB].
  apply semantics_has_initial_trace_cut_implies_prefix.
  econstructor 1.
  - exact INIT.
  - exists s', beh. split; [exact STAR | exact SB].
Qed.

Lemma bad_program_is_wf:
  forall p tr, wf_program p -> BacktranslationProof2.wf_program_public p ->
    wf_main p -> wf_main_sig p -> bad_program p tr ->
    BacktranslationProof2.asm_program_is_wf p.
Proof.
  intros p tr WFP WFPP [b [FS [f FF]]] WFMS ([s INIT] & _ & _).
  split; [exact WFP | split; [exact WFPP | split]].
  - exists b. split; [exact FS |]. exists f. split; [exact FF |]. eapply WFMS; eauto.
  - inversion INIT; subst. eexists; eauto.
Qed.

Lemma bad_program_refutes_use_site:
  forall p e,
    wf_program p -> BacktranslationProof2.wf_program_public p -> wf_main p -> wf_main_sig p ->
    bad_program p (e :: nil) ->
    asm_to_clight_hyps p (e :: nil) /\
    BacktranslationProof2.asm_program_is_wf p /\
    ~ step_fix_fix_use_site_stmt.
Proof.
  intros p e WFP WFPP WFM WFMS BAD.
  assert (HYPS: asm_to_clight_hyps p (e :: nil)).
  { unfold asm_to_clight_hyps.
    split; [exact WFP |]. split; [exact WFPP |]. split; [exact WFM |].
    split; [exact WFMS |]. split; [apply BAD |].
    split; [apply length_one_bound | apply bad_program_does_prefix; exact BAD]. }
  split; [exact HYPS | split].
  - eapply bad_program_is_wf; eauto.
  - intros USE.
    destruct BAD as ([s INIT] & RUN & NORUN).
    destruct (RUN s INIT) as [s' STAR].
    apply (NORUN s s' INIT). eapply USE; eauto.
Qed.

(** ** Counterexample 1: CHECKPUB (public [int *px = &y;], cross-compartment call). *)

Lemma wf_prog1: wf_program P1.prog1.
Proof.
  unfold wf_program, prog_defs_names. simpl.
  repeat constructor; simpl; intuition discriminate.
Qed.

Lemma wf_public_prog1: BacktranslationProof2.wf_program_public P1.prog1.
Proof. intros id IN. exact IN. Qed.

Lemma wf_main_prog1: wf_main P1.prog1.
Proof.
  exists 3%positive. split; [reflexivity |]. eexists. reflexivity.
Qed.

Lemma wf_main_sig_prog1: wf_main_sig P1.prog1.
Proof.
  intros b f FS FF.
  change (Genv.find_symbol P1.ge1 P1.main_id = Some b) in FS.
  rewrite P1.ge1_symb_main in FS. inversion FS; subst.
  change (Genv.find_funct_ptr P1.ge1 3%positive = Some (Internal f)) in FF.
  rewrite P1.ge1_funct_main in FF. inversion FF; subst. reflexivity.
Qed.

Theorem checkpub_use_site:
  asm_to_clight_hyps P1.prog1 P1.tr1 /\
  BacktranslationProof2.asm_program_is_wf P1.prog1 /\
  bad_program P1.prog1 P1.tr1 /\
  ~ step_fix_fix_use_site_stmt.
Proof.
  destruct (bad_program_refutes_use_site P1.prog1 _ wf_prog1 wf_public_prog1
              wf_main_prog1 wf_main_sig_prog1 P1.checkpub_counterexample) as (H1 & H2 & H3).
  split; [exact H1 | split; [exact H2 | split; [exact P1.checkpub_counterexample | exact H3]]].
Qed.

(** ** Counterexample 2: CALLSIG (hand-written Asm call with a wrong signature). *)

Lemma wf_prog2: wf_program P2.prog2.
Proof.
  unfold wf_program, prog_defs_names. simpl.
  repeat constructor; simpl; intuition discriminate.
Qed.

Lemma wf_public_prog2: BacktranslationProof2.wf_program_public P2.prog2.
Proof. intros id IN. exact IN. Qed.

Lemma wf_main_prog2: wf_main P2.prog2.
Proof.
  exists 1%positive. split; [reflexivity |]. eexists. reflexivity.
Qed.

Lemma wf_main_sig_prog2: wf_main_sig P2.prog2.
Proof.
  intros b f FS FF.
  change (Genv.find_symbol P2.ge2 P2.main_id = Some b) in FS.
  rewrite P2.ge2_symb_main in FS. inversion FS; subst.
  change (Genv.find_funct_ptr P2.ge2 1%positive = Some (Internal f)) in FF.
  rewrite P2.ge2_funct_main in FF. inversion FF; subst. reflexivity.
Qed.

Theorem callsig_use_site:
  asm_to_clight_hyps P2.prog2 P2.tr2 /\
  BacktranslationProof2.asm_program_is_wf P2.prog2 /\
  bad_program P2.prog2 P2.tr2 /\
  ~ step_fix_fix_use_site_stmt.
Proof.
  destruct (bad_program_refutes_use_site P2.prog2 _ wf_prog2 wf_public_prog2
              wf_main_prog2 wf_main_sig_prog2 P2.callsig_counterexample) as (H1 & H2 & H3).
  split; [exact H1 | split; [exact H2 | split; [exact P2.callsig_counterexample | exact H3]]].
Qed.

(** ** Counterexample 3: builtin result register not from [mreg]. *)

Lemma wf_prog3: wf_program P3.prog3.
Proof.
  unfold wf_program, prog_defs_names. simpl.
  repeat constructor; simpl; intuition discriminate.
Qed.

Lemma wf_public_prog3: BacktranslationProof2.wf_program_public P3.prog3.
Proof. intros id IN. exact IN. Qed.

Lemma wf_main_prog3: wf_main P3.prog3.
Proof.
  exists 1%positive. split; [reflexivity |]. eexists. reflexivity.
Qed.

Lemma wf_main_sig_prog3: wf_main_sig P3.prog3.
Proof.
  intros b f FS FF.
  change (Genv.find_symbol P3.ge3 P3.main_id = Some b) in FS.
  rewrite P3.ge3_symb_main in FS. inversion FS; subst.
  change (Genv.find_funct_ptr P3.ge3 1%positive = Some (Internal f)) in FF.
  rewrite P3.ge3_funct_main in FF. inversion FF; subst. reflexivity.
Qed.

Theorem builtin_res_use_site:
  asm_to_clight_hyps P3.prog3 P3.tr3 /\
  BacktranslationProof2.asm_program_is_wf P3.prog3 /\
  bad_program P3.prog3 P3.tr3 /\
  ~ step_fix_fix_use_site_stmt.
Proof.
  destruct (bad_program_refutes_use_site P3.prog3 _ wf_prog3 wf_public_prog3
              wf_main_prog3 wf_main_sig_prog3 P3.builtin_res_counterexample) as (H1 & H2 & H3).
  split; [exact H1 | split; [exact H2 | split; [exact P3.builtin_res_counterexample | exact H3]]].
Qed.

(** ** Counterexample 4: ECC (memcpy, i.e. a struct assignment, into a public global). *)

Lemma wf_prog4: wf_program P4.prog4.
Proof.
  unfold wf_program, prog_defs_names. simpl.
  repeat constructor; simpl; intuition discriminate.
Qed.

Lemma wf_public_prog4: BacktranslationProof2.wf_program_public P4.prog4.
Proof. intros id IN. exact IN. Qed.

Lemma wf_main_prog4: wf_main P4.prog4.
Proof.
  exists 3%positive. split; [reflexivity |]. eexists. reflexivity.
Qed.

Lemma wf_main_sig_prog4: wf_main_sig P4.prog4.
Proof.
  intros b f FS FF.
  change (Genv.find_symbol P4.ge4 P4.main_id = Some b) in FS.
  rewrite P4.ge4_symb_main in FS. inversion FS; subst.
  change (Genv.find_funct_ptr P4.ge4 3%positive = Some (Internal f)) in FF.
  rewrite P4.ge4_funct_main in FF. inversion FF; subst. reflexivity.
Qed.

Theorem ecc_memcpy_use_site:
  asm_to_clight_hyps P4.prog4 P4.tr4 /\
  BacktranslationProof2.asm_program_is_wf P4.prog4 /\
  bad_program P4.prog4 P4.tr4 /\
  ~ step_fix_fix_use_site_stmt.
Proof.
  destruct (bad_program_refutes_use_site P4.prog4 _ wf_prog4 wf_public_prog4
              wf_main_prog4 wf_main_sig_prog4 P4.ecc_memcpy_counterexample) as (H1 & H2 & H3).
  split; [exact H1 | split; [exact H2 | split; [exact P4.ecc_memcpy_counterexample | exact H3]]].
Qed.

Theorem not_step_fix_fix_use_site : ~ step_fix_fix_use_site_stmt.
Proof. apply checkpub_use_site. Qed.

(** ** Which check fails where (the other premises hold). *)

Theorem checks_summary:
  (* prog1: CALLSIG holds at the call, CHECKPUB fails in the initial memory *)
  (exists fd, Genv.find_funct_ptr P1.ge1 4%positive = Some fd /\ signature_main = funsig fd) /\
  (forall m0, Genv.init_mem P1.prog1 = Some m0 -> ~ public_first_order P1.ge1 m0) /\
  (* prog2: CHECKPUB holds in the initial memory, CALLSIG fails at the call *)
  (forall m0, Genv.init_mem P2.prog2 = Some m0 -> public_first_order P2.ge2 m0) /\
  ~ (exists fd, Genv.find_funct_ptr P2.ge2 2%positive = Some fd /\ signature_main = funsig fd) /\
  (* prog3: the builtin result [BR (IR X31)] is not [map_builtin_res preg_of _];
     ECC is trivially true for EF_debug *)
  (forall res, BR (IR X31) <> map_builtin_res preg_of res) /\
  (forall m args, external_call_conds P3.ef_dbg P3.ge3 m args) /\
  (* prog4: [BR_none] is fine, ECC fails (memcpy destination is public) *)
  (BR_none : builtin_res preg) = map_builtin_res preg_of BR_none /\
  (forall m, ~ external_call_conds P4.ef_cpy P4.ge4 m
                 (Vptr 1%positive Ptrofs.zero :: Vptr 2%positive Ptrofs.zero :: nil)).
Proof.
  split; [exact P1.callsig_holds |].
  split; [exact P1.init_not_public_first_order |].
  split; [exact P2.init_public_first_order |].
  split; [exact P2.callsig_fails |].
  split; [exact P3.not_map_builtin_res |].
  split; [intros; exact I |].
  split; [exact P4.builtin_res_ok |].
  exact P4.ecc_fails.
Qed.

Check not_step_fix_fix.
Print Assumptions not_step_fix_fix.
Check step_fix_fix_proves_False.
Print Assumptions step_fix_fix_proves_False.
Check P1.not_step_fix_fix_checkpub.
Print Assumptions P1.not_step_fix_fix_checkpub.
Check P2.not_step_fix_fix_callsig.
Print Assumptions P2.not_step_fix_fix_callsig.
Check P3.not_step_fix_fix_builtin_res.
Print Assumptions P3.not_step_fix_fix_builtin_res.
Check P4.not_step_fix_fix_ecc_memcpy.
Print Assumptions P4.not_step_fix_fix_ecc_memcpy.
Check checkpub_use_site.
Print Assumptions checkpub_use_site.
Check callsig_use_site.
Print Assumptions callsig_use_site.
Check builtin_res_use_site.
Print Assumptions builtin_res_use_site.
Check ecc_memcpy_use_site.
Print Assumptions ecc_memcpy_use_site.
Check not_step_fix_fix_use_site.
Print Assumptions not_step_fix_fix_use_site.
Check checks_summary.
Print Assumptions checks_summary.
