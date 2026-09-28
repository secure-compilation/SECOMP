(* Checks on ccs-backtranslation (this branch is ccs-backtranslation with PR #19,
   whose riscV/Asm.v, security/BtInfoAsm.v and common/Events.v are unchanged).

   1. [step_fix_step]: step_fix is included in Asm.step.
   2. [step_fix_iff]: step_fix = Asm.step restricted by [fix_conds], where [fix_conds]
      states exactly the four fixes (CALLSIG, CHECKPUB on calls, CHECKPUB on returns,
      ECC on builtins and external functions, and the builtin result register being an
      mreg).  So step_fix_fix says: every step of every Asm.step run satisfies fix_conds.
   3. The statements of the top-level theorems and of all their hypotheses, and
      Print Assumptions. *)

From Coq Require Import List.
From compcert.lib Require Import Coqlib Maps Integers.
From compcert.common Require Import AST Values Memory Events Globalenvs Smallstep.
From compcert.riscV Require Import Machregs Asm.
From compcert.security Require Import BtInfoAsm BtInfoAsmBound BacktranslationProof BacktranslationProof2.

Section FIX.

Variable cpm: compartment.
Variable ge: genv.

Lemma step_fix_step s t s' :
  step_fix cpm ge s t s' -> step cpm ge s t s'.
Proof.
  intros H; destruct H.
  - eapply exec_step_internal; eauto.
  - eapply exec_step_internal_call; eauto.
  - eapply exec_step_internal_return; eauto.
  - eapply exec_step_return; eauto.
  - eapply exec_step_builtin; eauto.
  - eapply exec_step_external; eauto.
Qed.

(* The extra premises of step_fix, as a condition on an Asm.step. *)
Definition fix_conds (s: state) (t: trace) (s': state) : Prop :=
  match s, s' with
  | State st rs m, State st' rs' m' =>
      forall b ofs f i,
        rs PC = Vptr b ofs ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
        (* calls: CALLSIG and CHECKPUB *)
        (forall sig b' ofs',
            sig_call i = Some sig ->
            rs' PC = Vptr b' ofs' ->
            Genv.type_of_call ge (comp_of f) (Genv.find_comp_ignore_offset ge (Vptr b' ofs'))
              = Genv.CrossCompartmentCall ->
            (exists fd, Genv.find_funct_ptr ge b' = Some fd /\ sig = funsig fd)
            /\ public_first_order ge m)
        /\
        (* builtins: result register is an mreg, and ECC *)
        (forall ef args res,
            i = Pbuiltin ef args res ->
            (exists res', res = map_builtin_res preg_of res')
            /\ (forall vargs, eval_builtin_args ge rs (rs SP) m args vargs ->
                        external_call_conds ef ge m vargs))
  | State st rs m, ReturnState _ _ _ =>
      (* external functions: ECC *)
      forall b ef args,
        rs PC = Vptr b Ptrofs.zero ->
        Genv.find_funct_ptr ge b = Some (External ef) ->
        extcall_arguments rs m (ef_sig ef) args ->
        external_call_conds ef ge m args
  | ReturnState st rs m, State _ _ _ =>
      (* returns: CHECKPUB *)
      Genv.type_of_call ge (Genv.find_comp_ignore_offset ge (rs PC)) (callee_comp cpm st)
        = Genv.CrossCompartmentCall ->
      public_first_order ge m
  | _, _ => True
  end.

Lemma step_fix_iff s t s' :
  step_fix cpm ge s t s' <-> (step cpm ge s t s' /\ fix_conds s t s').
Proof.
  split.
  - intros H. split; [apply step_fix_step; exact H|].
    destruct H; simpl.
    + (* internal *)
      intros b0 ofs0 f0 i0 PC0 FF0 FI0.
      rewrite H in PC0; inversion PC0; subst b0 ofs0.
      rewrite H0 in FF0; inversion FF0; subst f0.
      rewrite H1 in FI0; inversion FI0; subst i0.
      split.
      * intros sig b'' ofs'' SC. congruence.
      * intros ef args res EQ. subst i. simpl in H2. discriminate.
    + (* internal call *)
      intros b0 ofs0 f0 i0 PC0 FF0 FI0.
      rewrite H in PC0; inversion PC0; subst b0 ofs0.
      rewrite H0 in FF0; inversion FF0; subst f0.
      rewrite H1 in FI0; inversion FI0; subst i0.
      split.
      * intros sig0 b'' ofs'' SC NPC TC.
        rewrite H3 in SC; inversion SC; subst sig0.
        rewrite NEXTPC in NPC; inversion NPC; subst b'' ofs''.
        split; auto.
      * intros ef args0 res EQ. subst i. simpl in H2. discriminate.
    + (* internal return: the PC is in an internal function, so the ECC case is vacuous *)
      intros b0 ef0 args0 PC0 FF0 _. rewrite H in PC0; inversion PC0; subst b0. congruence.
    + (* return *)
      intros TC. apply CHECKPUB. subst rec_cp cp'. exact TC.
    + (* builtin *)
      intros b0 ofs0 f0 i0 PC0 FF0 FI0.
      rewrite H in PC0; inversion PC0; subst b0 ofs0.
      rewrite H0 in FF0; inversion FF0; subst f0.
      rewrite H1 in FI0; inversion FI0; subst i0.
      split.
      * intros sig b'' ofs'' SC. discriminate.
      * intros ef0 args0 res0 EQ. inversion EQ; subst ef0 args0 res0.
        split; [eexists; reflexivity|].
        intros vargs0 EVA.
        assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto).
        subst vargs0; auto.
    + (* external *)
      intros b0 ef0 args0 PC0 FF0 EA0.
      rewrite H in PC0; inversion PC0; subst b0.
      rewrite H0 in FF0; inversion FF0; subst ef0.
      assert (args0 = args) by (eapply extcall_arguments_determ; eauto).
      subst args0; auto.
  - intros [H C]. revert C. destruct H; simpl; intros C.
    + eapply exec_step_fix_internal; eauto.
    + destruct (C _ _ _ _ H H0 H1) as [CALL _].
      eapply exec_step_fix_internal_call; eauto.
      * intros TC. exact (proj1 (CALL _ _ _ H3 NEXTPC TC)).
      * intros TC. exact (proj2 (CALL _ _ _ H3 NEXTPC TC)).
    + eapply exec_step_fix_internal_return; eauto.
    + eapply exec_step_fix_return; eauto.
      intros TC. apply C. subst rec_cp cp'. exact TC.
    + destruct (C _ _ _ _ H H0 H1) as [_ BI].
      destruct (BI _ _ _ eq_refl) as [[res' EQ] ECC]. subst res.
      eapply exec_step_fix_builtin; eauto.
    + eapply exec_step_fix_external; eauto.
Qed.

(* Hence step_fix_fix, instantiated at one step, is exactly "every Asm.step satisfies
   fix_conds" (for star, "every step of the run"). *)
Lemma step_fix_fix_one_step_iff :
  (forall s t s', step cpm ge s t s' -> step_fix cpm ge s t s')
  <-> (forall s t s', step cpm ge s t s' -> fix_conds s t s').
Proof.
  split.
  - intros H s t s' S. apply (proj1 (step_fix_iff s t s') (H _ _ _ S)).
  - intros H s t s' S. apply step_fix_iff. split; auto.
Qed.

End FIX.

(* --- Statements of the theorems and of their hypotheses. --- *)
About backtranslation_proof.
About asm_to_clight.
About step_fix_fix.
Print asm_program_is_wf.
Print wf_program.
Print wf_program_public.
Print wf_main.
Print wf_main_sig.
Print external_functions_observable.
Print inline_assembly_observable.
Print extcall_observable.
Print asm_program_does_prefix.
About asm_to_ir.
Print public_first_order.
Print loc_first_order.
Print external_call_conds.
Print visible_fo.
Print val_public.
Print block_public.

(* --- Assumptions. --- *)
Print Assumptions backtranslation_proof.
Print Assumptions asm_to_ir.
Print Assumptions step_fix_iff.
Print Assumptions step_fix_fix_one_step_iff.
