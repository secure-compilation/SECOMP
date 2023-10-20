(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Postorder renumbering of RTL control-flow graphs. *)

Require Import Coqlib Maps Postorder.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTL Renumber.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.

#[global]
Instance comp_transf_function: has_comp_transl transf_function.
Proof. now intros. Qed.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. eapply match_transform_program; eauto.
Qed.

Section PRESERVATION.

Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof. exact (Genv.find_funct_transf TRANSL). Qed.

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof. exact (Genv.find_funct_ptr_transf TRANSL). Qed.

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (Genv.find_symbol_transf TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf TRANSL).

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; reflexivity.
Qed.

Lemma find_function_ptr_translated:
  forall ros ls vf,
  find_function_ptr ge ros ls = Some vf ->
  find_function_ptr tge ros ls = Some vf.
Proof.
  unfold find_function_ptr; intros; destruct ros; simpl.
  eauto.
  rewrite symbols_preserved; eauto.
Qed.

Lemma find_function_translated:
  forall ros rs fd,
  find_function ge ros rs = Some fd ->
  find_function tge ros rs = Some (transf_fundef fd).
Proof.
  unfold find_function. intros.
  destruct (find_function_ptr ge ros rs) eqn:EQ; try discriminate.
  apply find_function_ptr_translated in EQ.
  rewrite EQ.
  eapply functions_translated; eauto.
Qed.

Lemma allowed_call_translated:
  forall cp vf,
    Genv.allowed_call ge cp vf ->
    Genv.allowed_call tge cp vf.
Proof.
  intros cp vf H.
  eapply (Genv.match_genvs_allowed_calls TRANSL). eauto.
Qed.

Lemma find_comp_translated:
  forall vf,
    Genv.find_comp ge vf = Genv.find_comp tge vf.
Proof.
  intros vf.
  eapply (Genv.match_genvs_find_comp TRANSL).
Qed.

Lemma type_of_call_translated:
  forall cp cp',
    Genv.type_of_call ge cp cp' = Genv.type_of_call tge cp cp'.
Proof.
  intros cp cp'.
  eapply Genv.match_genvs_type_of_call.
Qed.

Lemma call_trace_translated:
  forall cp cp' vf vargs tyargs t,
    call_trace ge cp cp' vf vargs tyargs t ->
    call_trace tge cp cp' vf vargs tyargs t.
Proof.
  intros cp cp' vf vargs tyargs t H.
  inv H. constructor; eauto.
  econstructor; eauto. apply Genv.find_invert_symbol.
  rewrite symbols_preserved.
  apply Genv.invert_find_symbol; eauto.
  eapply eventval_list_match_preserved; [| | eassumption].
  eapply senv_preserved.
  eapply senv_preserved.
Qed.

(** Effect of an injective renaming of nodes on a CFG. *)

Section RENUMBER.

Variable f: PTree.t positive.

Hypothesis f_inj: forall x1 x2 y, f!x1 = Some y -> f!x2 = Some y -> x1 = x2.

Lemma renum_cfg_nodes:
  forall c x y i,
  c!x = Some i -> f!x = Some y -> (renum_cfg f c)!y = Some(renum_instr f i).
Proof.
  set (P := fun (c c': code) =>
              forall x y i, c!x = Some i -> f!x = Some y -> c'!y = Some(renum_instr f i)).
  intros c0. change (P c0 (renum_cfg f c0)). unfold renum_cfg.
  apply PTree_Properties.fold_rec; unfold P; intros.
  (* extensionality *)
  eapply H0; eauto. rewrite H; auto.
  (* base *)
  rewrite PTree.gempty in H; congruence.
  (* induction *)
  rewrite PTree.gsspec in H2. unfold renum_node. destruct (peq x k).
  inv H2. rewrite H3. apply PTree.gss.
  destruct f!k as [y'|] eqn:?.
  rewrite PTree.gso. eauto. red; intros; subst y'. elim n. eapply f_inj; eauto.
  eauto.
Qed.

End RENUMBER.

Definition pnum (f: function) := postorder (successors_map f) f.(fn_entrypoint).

Definition reach (f: function) (pc: node) := reachable (successors_map f) f.(fn_entrypoint) pc.

Lemma transf_function_at:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  reach f pc ->
  (transf_function f).(fn_code)!(renum_pc (pnum f) pc) = Some(renum_instr (pnum f) i).
Proof.
  intros.
  destruct (postorder_correct (successors_map f) f.(fn_entrypoint)) as [A B].
  fold (pnum f) in *.
  unfold renum_pc. destruct (pnum f)! pc as [pc'|] eqn:?.
  simpl. eapply renum_cfg_nodes; eauto.
  elim (B pc); auto. unfold successors_map. rewrite PTree.gmap1. rewrite H. simpl. congruence.
Qed.

Ltac TR_AT :=
  match goal with
  | [ A: (fn_code _)!_ = Some _ , B: reach _ _ |- _ ] =>
        generalize (transf_function_at _ _ _ A B); simpl renum_instr; intros
  end.

Lemma reach_succ:
  forall f pc i s,
  f.(fn_code)!pc = Some i -> In s (successors_instr i) ->
  reach f pc -> reach f s.
Proof.
  unfold reach; intros. econstructor; eauto.
  unfold successors_map. rewrite PTree.gmap1. rewrite H. auto.
Qed.

Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_frames_intro: forall res ty cp f sp pc rs
        (REACH: reach f pc),
      match_frames (Stackframe res ty cp f sp pc rs)
                   (Stackframe res ty cp (transf_function f) sp (renum_pc (pnum f) pc) rs).

Lemma match_stacks_call_comp:
  forall stk1 stk2,
  list_forall2 match_frames stk1 stk2 ->
  call_comp stk1 = call_comp stk2.
Proof.
  intros stk1 stk2 H.
  destruct H; trivial.
  match goal with
  | H : match_frames _ _ |- _ =>
    destruct H; trivial
  end.
Qed.

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk'
        (STACKS: list_forall2 match_frames stk stk')
        (REACH: reach f pc),
      match_states (State stk f sp pc rs m)
                   (State stk' (transf_function f) sp (renum_pc (pnum f) pc) rs m)
  | match_callstates: forall stk f args m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (Callstate stk f args m)
                   (Callstate stk' (transf_fundef f) args m)
  | match_returnstates: forall stk v m stk'
        (STACKS: list_forall2 match_frames stk stk'),
      match_states (Returnstate stk v m)
                   (Returnstate stk' v m).

Lemma step_simulation:
  forall S1 t S2, RTL.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', RTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inv MS; try TR_AT.
(* nop *)
  econstructor; split. eapply exec_Inop; eauto.
  constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* op *)
  econstructor; split.
  eapply exec_Iop; eauto.
  instantiate (1 := v). rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
  constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* load *)
  econstructor; split.
  assert (eval_addressing tge sp addr rs ## args = Some a).
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  eapply exec_Iload; eauto.
  constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* store *)
  econstructor; split.
  assert (eval_addressing tge sp addr rs ## args = Some a).
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  eapply exec_Istore; eauto.
  constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* call *)
  econstructor; split.
  eapply exec_Icall with (fd := transf_fundef fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
    eapply find_function_ptr_translated; eauto.
    eapply allowed_call_translated; eauto.
    intros CROSS. eapply NO_CROSS_PTR.
    erewrite type_of_call_translated, find_comp_translated; eauto.
    rewrite <- find_comp_translated, comp_transf_function.
    eapply call_trace_translated; eauto.

  constructor. constructor; auto.
  rewrite <- find_comp_translated. constructor. eapply reach_succ; eauto. simpl; auto.
(* tailcall *)
  econstructor; split.
  eapply exec_Itailcall with (fd := transf_fundef fd); eauto.
    eapply find_function_translated; eauto.
    apply sig_preserved.
    rewrite comp_transl, COMP. eauto.
  constructor. auto.
(* builtin *)
  econstructor; split.
  eapply exec_Ibuiltin; eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto. eapply reach_succ; eauto. simpl; auto.
(* cond *)
  econstructor; split.
  eapply exec_Icond; eauto.
  replace (if b then renum_pc (pnum f) ifso else renum_pc (pnum f) ifnot)
     with (renum_pc (pnum f) (if b then ifso else ifnot)).
  constructor; auto. eapply reach_succ; eauto. simpl. destruct b; auto.
  destruct b; auto.
(* jumptbl *)
  econstructor; split.
  eapply exec_Ijumptable; eauto. rewrite list_nth_z_map. rewrite H1. simpl; eauto.
  constructor; auto. eapply reach_succ; eauto. simpl. eapply list_nth_z_in; eauto.
(* return *)
  econstructor; split.
  eapply exec_Ireturn; eauto.
  constructor; auto.
(* internal function *)
  simpl. econstructor; split.
  eapply exec_function_internal; eauto.
  constructor; auto. unfold reach. constructor.
(* external function *)
  econstructor; split.
  eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto.
     apply senv_preserved.
  constructor; auto.
(* return *)
  inv STACKS. inv H1.
  econstructor; split.
  eapply exec_return; eauto.
  rewrite comp_transf_function.
  now eapply return_trace_eq; eauto using senv_preserved.
  constructor; auto.
Qed.

Lemma transf_initial_states:
  forall S1, RTL.initial_state prog S1 ->
  exists S2, RTL.initial_state tprog S2 /\ match_states S1 S2.
Proof.
  intros. inv H. econstructor; split.
  econstructor.
    eapply (Genv.init_mem_transf TRANSL); eauto.
    rewrite symbols_preserved. rewrite (match_program_main TRANSL). eauto.
    eapply function_ptr_translated; eauto.
    rewrite <- H3; apply sig_preserved.
  constructor. constructor.
Qed.

Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> RTL.final_state S1 r -> RTL.final_state S2 r.
Proof.
  intros. inv H0. inv H. inv STACKS. constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_step.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact step_simulation.
Qed.

End PRESERVATION.
