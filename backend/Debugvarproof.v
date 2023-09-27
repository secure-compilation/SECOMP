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

(** Correctness proof for the [Debugvar] pass. *)

Require Import Axioms Coqlib Maps Iteration Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Machregs Locations Conventions Op Linear.
Require Import Debugvar.

(** * Relational characterization of the transformation *)

Definition match_prog (p tp: program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Instance comp_transf_function: has_comp_transl_partial transf_function.
Proof.
  unfold transf_function.
  intros f ? H.
  now destruct ana_function; inv H.
Qed.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Inductive match_code: compartment -> code -> code -> Prop :=
  | match_code_nil: forall cp,
      match_code cp nil nil
  | match_code_cons: forall cp i before after c c',
      match_code cp c c' ->
      match_code cp (i :: c) (i :: add_delta_ranges cp before after c').

Remark diff_same:
  forall s, diff s s = nil.
Proof.
  induction s as [ | [v i] s]; simpl.
  auto.
  rewrite Pos.compare_refl. rewrite dec_eq_true. auto.
Qed.

Remark delta_state_same:
  forall s, delta_state s s = (nil, nil).
Proof.
  destruct s; simpl. rewrite ! diff_same; auto. auto.
Qed.

Lemma transf_code_match:
  forall cp lm c before, match_code cp c (transf_code cp lm before c).
Proof.
  intros cp lm. fix REC 1. destruct c; intros before; simpl.
- constructor.
- assert (DEFAULT: forall before after,
            match_code cp (i :: c)
                       (i :: add_delta_ranges cp before after (transf_code cp lm after c))).
  { intros. constructor. apply REC. }
  destruct i; auto. destruct c; auto. destruct i; auto.
  set (after := get_label l0 lm).
  set (c1 := Llabel l0 :: add_delta_ranges cp before after (transf_code cp lm after c)).
  replace c1 with (add_delta_ranges cp before before c1).
  constructor. constructor. apply REC.
  unfold add_delta_ranges. rewrite delta_state_same. auto.
Qed.

Inductive match_function: function -> function -> Prop :=
  | match_function_intro: forall f c,
      match_code f.(fn_comp) f.(fn_code) c ->
      match_function f (mkfunction f.(fn_comp) f.(fn_sig) f.(fn_stacksize) c).

Lemma transf_function_match:
  forall f tf, transf_function f = OK tf -> match_function f tf.
Proof.
  unfold transf_function; intros.
  destruct (ana_function f) as [lm|]; inv H.
  constructor. apply transf_code_match.
Qed.

Remark find_label_add_delta_ranges:
  forall cp lbl c before after, find_label lbl (add_delta_ranges cp before after c) = find_label lbl c.
Proof.
  intros. unfold add_delta_ranges.
  destruct (delta_state before after) as [killed born].
  induction killed as [ | [v i] l]; simpl; auto.
  induction born as [ | [v i] l]; simpl; auto.
Qed.

Lemma find_label_match_rec:
  forall cp lbl c' c tc,
  match_code cp c tc ->
  find_label lbl c = Some c' ->
  exists before after tc', find_label lbl tc = Some (add_delta_ranges cp before after tc') /\ match_code cp c' tc'.
Proof.
  induction 1; simpl; intros.
- discriminate.
- destruct (is_label lbl i).
  inv H0. econstructor; econstructor; econstructor; eauto.
  rewrite find_label_add_delta_ranges. auto.
Qed.

Lemma find_label_match:
  forall f tf lbl c,
  match_function f tf ->
  find_label lbl f.(fn_code) = Some c ->
  exists before after tc, find_label lbl tf.(fn_code) = Some (add_delta_ranges f.(fn_comp) before after tc) /\ match_code f.(fn_comp) c tc.
Proof.
  intros. inv H. eapply find_label_match_rec; eauto.
Qed.

(** * Properties of availability sets *)

(** These properties are not used in the semantic preservation proof,
    but establish some confidence in the availability analysis. *)

Definition avail_above (v: ident) (s: avail) : Prop :=
  forall v' i', In (v', i') s -> Plt v v'.

Inductive wf_avail: avail -> Prop :=
  | wf_avail_nil:
      wf_avail nil
  | wf_avail_cons: forall v i s,
     avail_above v s ->
     wf_avail s ->
     wf_avail ((v, i) :: s).

Lemma set_state_1:
  forall v i s, In (v, i) (set_state v i s).
Proof.
  induction s as [ | [v' i'] s]; simpl.
- auto.
- destruct (Pos.compare v v'); simpl; auto.
Qed.

Lemma set_state_2:
  forall v i v' i' s,
  v' <> v -> In (v', i') s -> In (v', i') (set_state v i s).
Proof.
  induction s as [ | [v1 i1] s]; simpl; intros.
- contradiction.
- destruct (Pos.compare_spec v v1); simpl.
+ subst v1. destruct H0. congruence. auto.
+ auto.
+ destruct H0; auto.
Qed.

Lemma set_state_3:
  forall v i v' i' s,
  wf_avail s ->
  In (v', i') (set_state v i s) ->
  (v' = v /\ i' = i) \/ (v' <> v /\ In (v', i') s).
Proof.
  induction 1; simpl; intros.
- intuition congruence.
- destruct (Pos.compare_spec v v0); simpl in H1.
+ subst v0. destruct H1. inv H1; auto. right; split.
  apply not_eq_sym. apply Plt_ne. eapply H; eauto.
  auto.
+ destruct H1. inv H1; auto.
  destruct H1. inv H1. right; split; auto. apply not_eq_sym. apply Plt_ne. auto.
  right; split; auto. apply not_eq_sym. apply Plt_ne. apply Plt_trans with v0; eauto.
+ destruct H1. inv H1. right; split; auto. apply Plt_ne. auto.
  destruct IHwf_avail as [A | [A B]]; auto.
Qed.

Lemma wf_set_state:
  forall v i s, wf_avail s -> wf_avail (set_state v i s).
Proof.
  induction 1; simpl.
- constructor. red; simpl; tauto. constructor.
- destruct (Pos.compare_spec v v0).
+ subst v0. constructor; auto.
+ constructor.
  red; simpl; intros. destruct H2.
  inv H2. auto. apply Plt_trans with v0; eauto.
  constructor; auto.
+ constructor.
  red; intros. exploit set_state_3. eexact H0. eauto. intros [[A B] | [A B]]; subst; eauto.
  auto.
Qed.

Lemma remove_state_1:
  forall v i s, wf_avail s -> ~ In (v, i) (remove_state v s).
Proof.
  induction 1; simpl; red; intros.
- auto.
- destruct (Pos.compare_spec v v0); simpl in *.
+ subst v0. elim (Plt_strict v); eauto.
+ destruct H1. inv H1.  elim (Plt_strict v); eauto.
  elim (Plt_strict v). apply Plt_trans with v0; eauto.
+ destruct H1. inv H1. elim (Plt_strict v); eauto.  tauto.
Qed.

Lemma remove_state_2:
  forall v v' i' s, v' <> v -> In (v', i') s -> In (v', i') (remove_state v s).
Proof.
  induction s as [ | [v1 i1] s]; simpl; intros.
- auto.
- destruct (Pos.compare_spec v v1); simpl.
+ subst v1. destruct H0. congruence. auto.
+ auto.
+ destruct H0; auto.
Qed.

Lemma remove_state_3:
  forall v v' i' s, wf_avail s -> In (v', i') (remove_state v s) -> v' <> v /\ In (v', i') s.
Proof.
  induction 1; simpl; intros.
- contradiction.
- destruct (Pos.compare_spec v v0); simpl in H1.
+ subst v0. split; auto. apply not_eq_sym; apply Plt_ne; eauto.
+ destruct H1. inv H1. split; auto. apply not_eq_sym; apply Plt_ne; eauto.
  split; auto. apply not_eq_sym; apply Plt_ne. apply Plt_trans with v0; eauto.
+ destruct H1. inv H1. split; auto. apply Plt_ne; auto.
  destruct IHwf_avail as [A B] ; auto.
Qed.

Lemma wf_remove_state:
  forall v s, wf_avail s -> wf_avail (remove_state v s).
Proof.
  induction 1; simpl.
- constructor.
- destruct (Pos.compare_spec v v0).
+ auto.
+ constructor; auto.
+ constructor; auto. red; intros.
  exploit remove_state_3. eexact H0. eauto. intros [A B]. eauto.
Qed.

Lemma wf_filter:
  forall pred s, wf_avail s -> wf_avail (List.filter pred s).
Proof.
  induction 1; simpl.
- constructor.
- destruct (pred (v, i)) eqn:P; auto.
  constructor; auto.
  red; intros. apply filter_In in H1. destruct H1. eauto.
Qed.

Lemma join_1:
  forall v i s1, wf_avail s1 -> forall s2, wf_avail s2 ->
  In (v, i) s1 -> In (v, i) s2 -> In (v, i) (join s1 s2).
Proof.
  induction 1; simpl; try tauto; induction 1; simpl; intros I1 I2; auto.
  destruct I1, I2.
- inv H3; inv H4. rewrite Pos.compare_refl. rewrite dec_eq_true; auto with coqlib.
- inv H3.
  assert (L: Plt v1 v) by eauto. apply Pos.compare_gt_iff in L. rewrite L. auto.
- inv H4.
  assert (L: Plt v0 v) by eauto. apply Pos.compare_lt_iff in L. rewrite L. apply IHwf_avail. constructor; auto. auto. auto with coqlib.
- destruct (Pos.compare v0 v1).
+ destruct (eq_debuginfo i0 i1); auto with coqlib.
+ apply IHwf_avail; auto with coqlib. constructor; auto.
+ eauto.
Qed.

Lemma join_2:
  forall v i s1, wf_avail s1 -> forall s2, wf_avail s2 ->
  In (v, i) (join s1 s2) -> In (v, i) s1 /\ In (v, i) s2.
Proof.
  induction 1; simpl; try tauto; induction 1; simpl; intros I; try tauto.
  destruct (Pos.compare_spec v0 v1).
- subst v1. destruct (eq_debuginfo i0 i1).
  + subst i1. destruct I. auto. exploit IHwf_avail; eauto. tauto.
  + exploit IHwf_avail; eauto. tauto.
- exploit (IHwf_avail ((v1, i1) :: s0)); eauto. constructor; auto.
  simpl. tauto.
- exploit IHwf_avail0; eauto. tauto.
Qed.

Lemma wf_join:
  forall s1, wf_avail s1 -> forall s2, wf_avail s2 -> wf_avail (join s1 s2).
Proof.
  induction 1; simpl; induction 1; simpl; try constructor.
  destruct (Pos.compare_spec v v0).
- subst v0. destruct (eq_debuginfo i i0); auto. constructor; auto.
  red; intros. apply join_2 in H3; auto. destruct H3. eauto.
- apply IHwf_avail. constructor; auto.
- apply IHwf_avail0.
Qed.


(** * Semantic preservation *)

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.

Hypothesis TRANSF: match_prog prog tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\
  transf_fundef f = OK tf.
Proof. exact (Genv.find_funct_transf_partial TRANSF). Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSF).

Lemma sig_preserved:
  forall f tf,
  transf_fundef f = OK tf ->
  funsig tf = funsig f.
Proof.
  unfold transf_fundef, transf_partial_fundef; intros.
  destruct f. monadInv H.
  exploit transf_function_match; eauto. intros M; inv M; auto.
  inv H. reflexivity.
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
  forall ros ls f,
  find_function ge ros ls = Some f ->
  exists tf,
  find_function tge ros ls = Some tf /\ transf_fundef f = OK tf.
Proof.
  unfold find_function; intros.
  destruct (find_function_ptr ge ros ls) eqn:EQ; try congruence.
  apply find_function_ptr_translated in EQ; rewrite EQ.
  apply functions_translated; auto.
Qed.

Lemma allowed_call_translated:
  forall cp vf,
    Genv.allowed_call ge cp vf ->
    Genv.allowed_call tge cp vf.
Proof.
  intros cp vf H.
  eapply (Genv.match_genvs_allowed_calls TRANSF). eauto.
Qed.

Lemma find_comp_translated:
  forall vf,
    Genv.find_comp ge vf = Genv.find_comp tge vf.
Proof.
  intros vf.
  eapply (Genv.match_genvs_find_comp TRANSF).
Qed.

Lemma type_of_call_translated:
  forall cp cp',
    Genv.type_of_call ge cp cp' = Genv.type_of_call tge cp cp'.
Proof.
  intros cp cp'.
  eapply Genv.match_genvs_type_of_call.
Qed.

(** Evaluation of the debug annotations introduced by the transformation. *)

Lemma can_eval_safe_arg:
  forall (rs: locset) sp m (a: builtin_arg loc),
  safe_builtin_arg a -> exists v, eval_builtin_arg tge rs sp m a v.
Proof.
  induction a; simpl; intros; try contradiction;
  try (econstructor; now eauto with barg).
  destruct H as [S1 S2].
  destruct (IHa1 S1) as [v1 E1]. destruct (IHa2 S2) as [v2 E2].
  exists (Val.longofwords v1 v2); auto with barg.
Qed.

Lemma eval_add_delta_ranges:
  forall s f sp c rs m before after,
  star step tge (State s f sp (add_delta_ranges f.(fn_comp) before after c) rs m)
             E0 (State s f sp c rs m).
Proof.
  intros. unfold add_delta_ranges.
  destruct (delta_state before after) as [killed born].
  induction killed as [ | [v i] l]; simpl.
- induction born as [ | [v i] l]; simpl.
+ apply star_refl.
+ destruct i as [a SAFE]; simpl.
  exploit can_eval_safe_arg; eauto. intros [v1 E1].
  eapply star_step; eauto.
  econstructor.
  constructor. eexact E1. constructor.
  simpl; econstructor.
  simpl; auto.
  auto.
  traceEq.
- eapply star_step; eauto.
  econstructor.
  constructor.
  simpl; constructor.
  simpl; auto.
  auto.
  traceEq.
Qed.

(** Matching between program states. *)

Inductive match_stackframes: Linear.stackframe -> Linear.stackframe -> Prop :=
  | match_stackframe_intro:
      forall f cp sg sp rs c tf tc before after,
      match_function f tf ->
      match_code f.(fn_comp) c tc ->
      match_stackframes
        (Stackframe f cp sg sp rs c)
        (Stackframe tf cp sg sp rs (add_delta_ranges f.(fn_comp) before after tc)).

Inductive match_states: Linear.state ->  Linear.state -> Prop :=
  | match_states_instr:
      forall s f sp c rs m tf ts tc
        (STACKS: list_forall2 match_stackframes s ts)
        (TRF: match_function f tf)
        (TRC: match_code f.(fn_comp) c tc),
      match_states (State s f sp c rs m)
                   (State ts tf sp tc rs m)
  | match_states_call:
      forall s f rs m tf ts sig,
      list_forall2 match_stackframes s ts ->
      transf_fundef f = OK tf ->
      match_states (Callstate s f sig rs m)
                   (Callstate ts tf sig rs m)
  | match_states_return:
      forall s rs m ts,
      list_forall2 match_stackframes s ts ->
      match_states (Returnstate s rs m)
                   (Returnstate ts rs m).

Lemma parent_locset_match:
  forall s ts,
  list_forall2 match_stackframes s ts ->
  parent_locset ts = parent_locset s.
Proof.
  induction 1; simpl. auto. inv H; auto.
Qed.

Lemma match_stacks_call_comp:
  forall s ts,
  list_forall2 match_stackframes s ts ->
  call_comp s = call_comp ts.
Proof.
  intros s ts H.
  destruct H; trivial.
  match goal with
  | H : match_stackframes _ _ |- _ => destruct H
  end.
  now match goal with
  | H : match_function _ _ |- _ => destruct H
  end.
Qed.

(** The simulation diagram. *)

Theorem transf_step_correct:
  forall s1 t s2, step ge s1 t s2 ->
  forall ts1 (MS: match_states s1 ts1),
  exists ts2, plus step tge ts1 t ts2 /\ match_states s2 ts2.
Proof.
  induction 1; intros ts1 MS; inv MS; try (inv TRC);
   try replace (fn_comp f) with (fn_comp tf) by now inv TRF.
- (* getstack *)
  econstructor; split.
  eapply plus_left. constructor; auto.
  apply eval_add_delta_ranges. traceEq.
  constructor; auto.
- (* setstack *)
  econstructor; split.
  eapply plus_left. constructor; auto.
  apply eval_add_delta_ranges. traceEq.
  constructor; auto.
- (* op *)
  econstructor; split.
  eapply plus_left.
  econstructor; eauto.
  instantiate (1 := v). rewrite <- H; apply eval_operation_preserved; exact symbols_preserved.
  apply eval_add_delta_ranges. traceEq.
  constructor; auto.
- (* load *)
  econstructor; split.
  eapply plus_left.
  eapply exec_Lload with (a := a).
  rewrite <- H; apply eval_addressing_preserved; exact symbols_preserved.
  inv TRF; eauto. eauto.
  apply eval_add_delta_ranges. traceEq.
  constructor; auto.
- (* store *)
  econstructor; split.
  eapply plus_left.
  eapply exec_Lstore with (a := a).
  rewrite <- H; apply eval_addressing_preserved; exact symbols_preserved.
  inv TRF; eauto. eauto.
  apply eval_add_delta_ranges. traceEq.
  constructor; auto.
- (* call *)
  exploit find_function_translated; eauto. intros (tf' & A & B).
  econstructor; split.
  apply plus_one.
  econstructor. eexact A. eapply find_function_ptr_translated; eauto.
  symmetry; apply sig_preserved; auto.
  inv TRF.
  eapply allowed_call_translated; eauto.
  reflexivity.
  reflexivity.
  { intros. subst.
    assert (X: Genv.type_of_call ge (comp_of f) (Genv.find_comp ge vf) = Genv.CrossCompartmentCall).
    { erewrite find_comp_translated, type_of_call_translated; eauto.
      inv TRF. eauto. }
    specialize (NO_CROSS_PTR X).
    (* rewrite H1. rewrite X in NO_CROSS_PTR. *)
    eauto.
  }
  { erewrite <- find_comp_translated.
    inv TRF; unfold comp_of; simpl.
    eapply call_trace_eq; eauto using senv_preserved, symbols_preserved. }
  constructor; auto. constructor; auto.
  replace (fn_comp tf) with (fn_comp f) by now inv TRF.
  rewrite find_comp_translated; constructor; auto.
- (* tailcall *)
  exploit find_function_translated; eauto. intros (tf' & A & B).
  exploit parent_locset_match; eauto. intros PLS.
  econstructor; split.
  apply plus_one.
  inv TRF.
  econstructor. eauto. rewrite PLS. eexact A.
  symmetry; apply sig_preserved; auto.
  now rewrite <- (comp_transl_partial _ B).
  eauto.
  rewrite PLS. constructor; auto.
- (* builtin *)
  econstructor; split.
  eapply plus_left.
  econstructor; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  inv TRF; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  inversion TRF. simpl in *. eauto.
  apply eval_add_delta_ranges. traceEq.
  constructor; auto.
- (* label *)
  econstructor; split.
  eapply plus_left. constructor; auto. apply eval_add_delta_ranges. traceEq.
  constructor; auto.
- (* goto *)
  exploit find_label_match; eauto. intros (before' & after' & tc' & A & B).
  econstructor; split.
  eapply plus_left. constructor; eauto.
  replace (fn_comp f) with (fn_comp tf) by now inv TRF.
  apply eval_add_delta_ranges; eauto. traceEq.
  constructor; auto.
- (* cond taken *)
  exploit find_label_match; eauto. intros (before' & after' & tc' & A & B).
  econstructor; split.
  eapply plus_left. eapply exec_Lcond_true; eauto.
  replace (fn_comp f) with (fn_comp tf) by now inv TRF.
  apply eval_add_delta_ranges; eauto. traceEq.
  constructor; auto.
- (* cond not taken *)
  econstructor; split.
  eapply plus_left. eapply exec_Lcond_false; auto. apply eval_add_delta_ranges. traceEq.
  constructor; auto.
- (* jumptable *)
  exploit find_label_match; eauto. intros (before' & after' & tc' & A & B).
  econstructor; split.
  eapply plus_left. econstructor; eauto.
  replace (fn_comp f) with (fn_comp tf) by now inv TRF.
  apply eval_add_delta_ranges. reflexivity. traceEq.
  constructor; auto.
- (* return *)
  econstructor; split.
  apply plus_one.  econstructor. inv TRF; eauto. traceEq.
  rewrite (parent_locset_match _ _ STACKS).
  assert (CALLER: call_comp s = call_comp ts).
  { inv STACKS. reflexivity.
    inv H0. inv H2. reflexivity. }
  assert (CALLEE: callee_comp s = callee_comp ts).
  { inv STACKS. reflexivity.
    inv H0. reflexivity. }
  assert (SIG: parent_signature s = parent_signature ts).
  { inv STACKS. reflexivity.
    inv H0. reflexivity. }
  (* rewrite type_of_call_translated, CALLEE, CALLER, SIG. *)
  rewrite SIG.
  destruct (Genv.type_of_call tge (call_comp ts) (callee_comp ts)).
  inv TRF; constructor; auto.
  inv TRF; constructor; auto.
  (* inv TRF; constructor; auto. *)
- (* internal function *)
  monadInv H8. rename x into tf.
  assert (MF: match_function f tf) by (apply transf_function_match; auto).
  inversion MF; subst.
  econstructor; split.

  apply plus_one. eapply exec_function_internal. simpl; eauto. reflexivity. reflexivity.

  assert (CALLER: call_comp s = call_comp ts).
  { inv H7. reflexivity.
    inv H1. inv H3. reflexivity. }
  assert (SIG: parent_signature s = parent_signature ts).
  { inv H7. reflexivity.
    inv H1. reflexivity. }
  (* rewrite type_of_call_translated, CALLER, SIG. *)
  change
    (comp_of {| fn_comp := fn_comp f; fn_sig := fn_sig f; fn_stacksize := fn_stacksize f; fn_code := c |})
    with (comp_of f).
  destruct (Genv.type_of_call tge (call_comp ts) (comp_of f)).
  constructor; auto.
  constructor; auto.
  (* constructor; auto. *)
- (* external function *)
  monadInv H9. econstructor; split.
  apply plus_one. econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.
- (* return *)
  inv H3. inv H1.
  inv H8.
  econstructor; split.
  eapply plus_left. econstructor.
  auto.
  eapply return_trace_eq; eauto using senv_preserved.
  replace (fn_comp f) with
    (fn_comp {| fn_comp := fn_comp f; fn_sig := fn_sig f; fn_stacksize := fn_stacksize f; fn_code := c0 |})
    by reflexivity.
  apply eval_add_delta_ranges. traceEq.
  constructor; auto. constructor; auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists (Callstate nil tf signature_main (Locmap.init Vundef) m0); split.
  econstructor; eauto. eapply (Genv.init_mem_transf_partial TRANSF); eauto.
  rewrite (match_program_main TRANSF), symbols_preserved. auto.
  rewrite <- H3. apply sig_preserved. auto.
  constructor. constructor. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H5. econstructor; eauto.
Qed.

Theorem transf_program_correct:
  forward_simulation (semantics prog) (semantics tprog).
Proof.
  eapply forward_simulation_plus.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  eexact transf_step_correct.
Qed.

End PRESERVATION.
