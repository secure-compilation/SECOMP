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

(** Recognition of tail calls: correctness proof *)

Require Import Coqlib Maps Integers AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Conventions Tailcall.

(** * Syntactic properties of the code transformation *)

(** ** Measuring the number of instructions eliminated *)

(** The [return_measure c pc] function counts the number of instructions
  eliminated by the code transformation, where [pc] is the successor
  of a call turned into a tailcall.  This is the length of the
  move/nop/return sequence recognized by the [is_return] boolean function.
*)

Fixpoint return_measure_rec (n: nat) (c: code) (pc: node)
                            {struct n}: nat :=
  match n with
  | O => O
  | S n' =>
      match c!pc with
      | Some(Inop s) => S(return_measure_rec n' c s)
      | Some(Iop op args dst s) => S(return_measure_rec n' c s)
      | _ => O
      end
  end.

Definition return_measure (c: code) (pc: node) :=
  return_measure_rec niter c pc.

Lemma return_measure_bounds:
  forall f pc, (return_measure f pc <= niter)%nat.
Proof.
  intro f.
  assert (forall n pc, (return_measure_rec n f pc <= n)%nat).
    induction n; intros; simpl.
    omega.
    destruct (f!pc); try omega.
    destruct i; try omega.
    generalize (IHn n0). omega.
    generalize (IHn n0). omega.
  intros. unfold return_measure. apply H.
Qed.

Remark return_measure_rec_incr:
  forall f n1 n2 pc,
  (n1 <= n2)%nat ->
  (return_measure_rec n1 f pc <= return_measure_rec n2 f pc)%nat.
Proof.
  induction n1; intros; simpl.
  omega.
  destruct n2. omegaContradiction. assert (n1 <= n2)%nat by omega.
  simpl. destruct f!pc; try omega. destruct i; try omega.
  generalize (IHn1 n2 n H0). omega.
  generalize (IHn1 n2 n H0). omega.
Qed.

Lemma is_return_measure_rec:
  forall f n n' pc r,
  is_return n f pc r = true -> (n <= n')%nat ->
  return_measure_rec n f.(fn_code) pc = return_measure_rec n' f.(fn_code) pc.
Proof.
  induction n; simpl; intros.
  congruence.
  destruct n'. omegaContradiction. simpl.
  destruct (fn_code f)!pc; try congruence.
  destruct i; try congruence.
  decEq. apply IHn with r. auto. omega.
  destruct (is_move_operation o l); try congruence.
  destruct (Reg.eq r r1); try congruence.
  decEq. apply IHn with r0. auto. omega.
Qed.

(** ** Relational characterization of the code transformation *)

(** The [is_return_spec] characterizes the instruction sequences
  recognized by the [is_return] boolean function.  *)

Inductive is_return_spec (f:function): node -> reg -> Prop :=
  | is_return_none: forall pc r,
      f.(fn_code)!pc = Some(Ireturn None) ->
      is_return_spec f pc r
  | is_return_some: forall pc r,
      f.(fn_code)!pc = Some(Ireturn (Some r)) ->
      is_return_spec f pc r
  | is_return_nop: forall pc r s,
      f.(fn_code)!pc = Some(Inop s) ->
      is_return_spec f s r ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
      is_return_spec f pc r
  | is_return_move: forall pc r r' s,
      f.(fn_code)!pc = Some(Iop Omove (r::nil) r' s) ->
      is_return_spec f s r' ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
     is_return_spec f pc r.

Lemma is_return_charact:
  forall f n pc rret,
  is_return n f pc rret = true -> (n <= niter)%nat ->
  is_return_spec f pc rret.
Proof.
  induction n; intros.
  simpl in H. congruence.
  generalize H. simpl.
  caseEq ((fn_code f)!pc); try congruence.
  intro i. caseEq i; try congruence.
  intros s; intros. eapply is_return_nop; eauto. eapply IHn; eauto. omega.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc rret); auto.
  rewrite <- (is_return_measure_rec f n niter s rret); auto.
  simpl. rewrite H2. omega. omega.

  intros op args dst s EQ1 EQ2.
  caseEq (is_move_operation op args); try congruence.
  intros src IMO. destruct (Reg.eq rret src); try congruence.
  subst rret. intro.
  exploit is_move_operation_correct; eauto. intros [A B]. subst.
  eapply is_return_move; eauto. eapply IHn; eauto. omega.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc src); auto.
  rewrite <- (is_return_measure_rec f n niter s dst); auto.
  simpl. rewrite EQ2. omega. omega.

  intros or EQ1 EQ2. destruct or; intros.
  assert (r = rret). eapply proj_sumbool_true; eauto. subst r.
  apply is_return_some; auto.
  apply is_return_none; auto.
Qed.

(** The [transf_instr_spec] predicate relates one instruction in the
  initial code with its possible transformations in the optimized code. *)

Inductive transf_instr_spec (ce: compenv) (f: function): instruction -> instruction -> Prop :=
  | transf_instr_tailcall: forall sig ros args res s,
      f.(fn_stacksize) = 0 ->
      is_return_spec f s res ->
      forall INTRA: intra_compartment_call ce ros (comp_of f) = true,
      forall ALLOWED: needs_calling_comp (comp_of f) = false,
      transf_instr_spec ce f (Icall sig ros args res s) (Itailcall sig ros args)
  | transf_instr_default: forall i,
      transf_instr_spec ce f i i.

Lemma transf_instr_charact:
  forall ce f pc instr,
  f.(fn_stacksize) = 0 ->
  transf_instr_spec ce f instr (transf_instr ce f pc instr).
Proof.
  intros. unfold transf_instr. destruct instr; try constructor.
  destruct (is_return niter f n r && tailcall_is_possible s &&
            rettype_eq (sig_res s) (sig_res (fn_sig f)) &&
            intra_compartment_call ce _ (comp_of f) &&
            negb (needs_calling_comp _)) eqn:B.
- InvBooleans. eapply transf_instr_tailcall; eauto.
+ eapply is_return_charact; eauto.
+ destruct (needs_calling_comp _); easy.
- constructor.
Qed.

Lemma transf_instr_lookup:
  forall ce f pc i,
  f.(fn_code)!pc = Some i ->
  exists i',  (transf_function ce f).(fn_code)!pc = Some i' /\ transf_instr_spec ce f i i'.
Proof.
  intros. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0).
  simpl. rewrite PTree.gmap. rewrite H. simpl.
  exists (transf_instr ce f pc i); split. auto. apply transf_instr_charact; auto.
  exists i; split. auto. constructor.
Qed.

(** * Semantic properties of the code transformation *)

(** ** The ``less defined than'' relation between register states *)

(** A call followed by a return without an argument can be turned
  into a tail call.  In this case, the original function returns
  [Vundef], while the transformed function can return any value.
  We account for this situation by using the ``less defined than''
  relation between values and between memory states.  We need to
  extend it pointwise to register states. *)

Lemma regs_lessdef_init_regs:
  forall params vl vl',
  Val.lessdef_list vl vl' ->
  regs_lessdef (init_regs vl params) (init_regs vl' params).
Proof.
  induction params; intros.
  simpl. red; intros. rewrite Regmap.gi. constructor.
  simpl. inv H.   red; intros. rewrite Regmap.gi. constructor.
  apply set_reg_lessdef. auto. auto.
Qed.

(** * Proof of semantic preservation *)

Definition match_prog (p tp: RTL.program) :=
  match_program (fun cu f tf => tf = transf_fundef (compenv_program cu) f) eq p tp.

Instance comp_transf_function cenv: has_comp_transl (transf_function cenv).
Proof.
  unfold transf_function, RTL.transf_function.
  intros f; simpl; trivial.
  now destruct zeq.
Qed.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. apply match_transform_program_contextual; auto.
Qed.

Section PRESERVATION.

Variable prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.


Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSL).

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  exists cu tf,
  Genv.find_funct tge v = Some tf /\ tf = transf_fundef (compenv_program cu) f /\ linkorder cu prog.
Proof (Genv.find_funct_match TRANSL).

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists cu tf,
  Genv.find_funct_ptr tge b = Some tf /\ tf = transf_fundef (compenv_program cu) f /\ linkorder cu prog.
Proof (Genv.find_funct_ptr_match TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSL).

Lemma sig_preserved:
  forall ce f, funsig (transf_fundef ce f) = funsig f.
Proof.
  destruct f; auto. simpl. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma stacksize_preserved:
  forall ce f, fn_stacksize (transf_function ce f) = fn_stacksize f.
Proof.
  unfold transf_function. intros.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma find_function_translated:
  forall ros rs rs' f,
  find_function ge ros rs = Some f ->
  regs_lessdef rs rs' ->
  exists cu tf,
  find_function tge ros rs' = Some tf /\
  tf = transf_fundef (compenv_program cu) f /\
  linkorder cu prog.
Proof.
  intros until f; destruct ros; simpl.
  intros.
  assert (rs'#r = rs#r).
    exploit Genv.find_funct_inv; eauto. intros [b EQ].
    generalize (H0 r). rewrite EQ. intro LD. inv LD. auto.
  rewrite H1. apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); intros.
  apply funct_ptr_translated; auto.
  discriminate.
Qed.


Lemma find_function_ptr_translated:
  forall ros rs rs' f vf,
  find_function ge ros rs = Some f ->
  regs_lessdef rs rs' ->
  find_function_ptr ge ros rs = Some vf ->
  find_function_ptr tge ros rs' = Some vf.
Proof.
  unfold find_function, find_function_ptr; intros; destruct ros; simpl.
  assert (rs'#r = rs#r).
    exploit Genv.find_funct_inv; eauto. intros [b EQ].
    generalize (H0 r). rewrite EQ. intro LD. inv LD. auto.
  congruence.
  rewrite symbols_preserved. eauto.
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
(* This part has been adapted from Inliningproof.v; perhaps everything can be
generalized and unified. *)

Definition cenv_compat (p: program) (ce: compenv) : Prop :=
  forall id cp,
  ce!id = Some cp ->
  exists f, (prog_defmap p)!id = Some (Gfun f) /\ cp = comp_of f.

Lemma compenv_program_compat:
  forall p, cenv_compat p (compenv_program p).
Proof.
  set (P := fun (dm: PTree.t (globdef fundef unit)) (cenv: compenv) =>
              forall id cp,
              cenv!id = Some cp ->
              exists f, dm!id = Some (Gfun f) /\ cp = comp_of f).
  assert (REMOVE: forall dm fenv id g,
             P dm fenv ->
             P (PTree.set id g dm) (PTree.remove id fenv)).
  { unfold P; intros. rewrite PTree.grspec in H0. destruct (PTree.elt_eq id0 id).
    discriminate.
    rewrite PTree.gso; auto.
  }
  assert (ADD: forall dm cenv idg,
             P dm cenv ->
             P (PTree.set (fst idg) (snd idg) dm) (add_globdef cenv idg)).
  { intros dm fenv [id g]; simpl; intros.
    destruct g as [f | v]; auto.
    red; intros. rewrite ! PTree.gsspec in *.
    destruct (peq id0 id); auto. inv H0; eauto.
  }
  assert (REC: forall l dm cenv,
            P dm cenv ->
            P (fold_left (fun x idg => PTree.set (fst idg) (snd idg) x) l dm)
              (fold_left add_globdef l cenv)).
  { induction l; simpl; intros.
  - auto.
  - apply IHl. apply ADD; auto.
  }
  intros. apply REC. red; intros.  rewrite PTree.gempty in H; discriminate.
Qed.

Lemma cenv_compat_linkorder:
  forall cunit prog cenv,
  linkorder cunit prog -> cenv_compat cunit cenv -> cenv_compat prog cenv.
Proof.
  intros; red; intros. apply H0 in H1.
  destruct H1 as (f & GET & Ecp). subst cp.
  destruct (prog_defmap_linkorder _ _ _ _ H GET) as (gd' & P & Q).
  inv Q. inv H2; eauto.
Qed.

Lemma find_function_intra_compartment_call ce ros rs fd cp:
  cenv_compat prog ce ->
  find_function ge ros rs = Some fd ->
  intra_compartment_call ce ros cp = true ->
  comp_of fd = cp.
Proof.
  destruct ros as [?|id]; try easy.
  simpl. destruct (ce ! id) as [cp'|] eqn:GETce; try easy.
  intros COMPAT. specialize (COMPAT _ _ GETce).
  destruct COMPAT as (f & GETprog & ?). subst cp'.
  apply Genv.find_def_symbol in GETprog.
  destruct GETprog as (b & FIND1 & FIND2).
  unfold ge. rewrite FIND1.
  unfold Genv.find_funct_ptr. rewrite FIND2.
  intros ? EQ. apply proj_sumbool_true in EQ. congruence.
Qed.

(** Consider an execution of a call/move/nop/return sequence in the
  original code and the corresponding tailcall in the transformed code.
  The transition sequences are of the following form
  (left: original code, right: transformed code).
  [f] is the calling function and [fd] the called function.
<<
     State stk f (Icall instruction)       State stk' f' (Itailcall)

     Callstate (frame::stk) fd args        Callstate stk' fd' args'
            .                                       .
            .                                       .
            .                                       .
     Returnstate (frame::stk) res          Returnstate stk' res'

     State stk f (move/nop/return seq)
            .
            .
            .
     State stk f (return instr)

     Returnstate stk res
>>
The simulation invariant must therefore account for two kinds of
mismatches between the transition sequences:
- The call stack of the original program can contain more frames
  than that of the transformed program (e.g. [frame] in the example above).
- The regular states corresponding to executing the move/nop/return
  sequence must all correspond to the single [Returnstate stk' res']
  state of the transformed program.

We first define the simulation invariant between call stacks.
The first two cases are standard, but the third case corresponds
to a frame that was eliminated by the transformation. *)

Inductive match_stackframes (m: mem) (cp: compartment): list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes m cp nil nil
  | match_stackframes_normal: forall stk stk' res sp pc rs rs' ce f,
      match_stackframes m (comp_of f) stk stk' ->
      forall (COMPAT: cenv_compat prog ce),
      forall (UPD: uptodate_caller (comp_of f) (call_comp stk) (call_comp stk')),
      forall (ACC: Mem.can_access_block m sp (Some (comp_of f))),
      regs_lessdef rs rs' ->
      match_stackframes m cp
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        (Stackframe res (transf_function ce f) (Vptr sp Ptrofs.zero) pc rs' :: stk')
  | match_stackframes_tail: forall stk stk' res sp pc rs f,
      match_stackframes m cp stk stk' ->
      is_return_spec f pc res ->
      f.(fn_stacksize) = 0 ->
      cp = comp_of f ->
      match_stackframes m cp
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        stk'.

(** Here is the invariant relating two states.  The first three
  cases are standard.  Note the ``less defined than'' conditions
  over values and register states, and the corresponding ``extends''
  relation over memory states. *)

Inductive match_states: state -> state -> Prop :=
  | match_states_normal:
      forall s sp pc rs m s' rs' m' ce f
             (STACKS: match_stackframes m' (comp_of f) s s')
             (COMPAT: cenv_compat prog ce)
             (RLD: regs_lessdef rs rs')
             (MLD: Mem.extends m m')
             (UPD: uptodate_caller (comp_of f) (call_comp s) (call_comp s'))
             (ACC: Mem.can_access_block m' sp (Some (comp_of f))),
      match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (State s' (transf_function ce f) (Vptr sp Ptrofs.zero) pc rs' m')
  | match_states_call:
      forall s ce f args m s' args' m',
      match_stackframes m' (comp_of f) s s' ->
      forall (COMPAT: cenv_compat prog ce),
      forall (UPD: uptodate_caller (comp_of f) (call_comp s) (call_comp s')),
      Val.lessdef_list args args' ->
      Mem.extends m m' ->
      match_states (Callstate s f args m)
                   (Callstate s' (transf_fundef ce f) args' m')
  | match_states_return:
      forall s v m s' v' m' cp,
      match_stackframes m' cp s s' ->
      Val.lessdef v v' ->
      Mem.extends m m' ->
      match_states (Returnstate s v m cp)
                   (Returnstate s' v' m' cp)
  | match_states_interm:
      forall s sp pc rs m s' m' f r v'
             (STACKS: match_stackframes m' (comp_of f) s s')
             (MLD: Mem.extends m m'),
      is_return_spec f pc r ->
      f.(fn_stacksize) = 0 ->
      Val.lessdef (rs#r) v' ->
      match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (Returnstate s' v' m' (comp_of f)).

(** The last case of [match_states] corresponds to the execution
  of a move/nop/return sequence in the original code that was
  eliminated by the transformation:
<<
     State stk f (move/nop/return seq)  ~~  Returnstate stk' res'
            .
            .
            .
     State stk f (return instr)         ~~  Returnstate stk' res'
>>
  To preserve non-terminating behaviors, we need to make sure
  that the execution of this sequence in the original code cannot
  diverge.  For this, we introduce the following complicated
  measure over states, which will decrease strictly whenever
  the original code makes a transition but the transformed code
  does not. *)

Definition measure (st: state) : nat :=
  match st with
  | State s f sp pc rs m => (List.length s * (niter + 2) + return_measure f.(fn_code) pc + 1)%nat
  | Callstate s f args m => 0%nat
  | Returnstate s v m cp => (List.length s * (niter + 2))%nat
  end.

Ltac TransfInstr :=
  match goal with
  | H: (PTree.get _ (fn_code _) = _),
    COMPAT: cenv_compat prog ?ce |- _ =>
      destruct (transf_instr_lookup ce _ _ _ H) as [i' [TINSTR TSPEC]]; inv TSPEC
  end.

Ltac EliminatedInstr :=
  match goal with
  | H: (is_return_spec _ _ _) |- _ => inv H; try congruence
  | _ => idtac
  end.

(** The proof of semantic preservation, then, is a simulation diagram
  of the ``option'' kind. *)

Lemma transf_step_correct:
  forall s1 t s2, step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  (exists s2', step tge s1' t s2' /\ match_states s2 s2')
  \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat.
Proof.
  induction 1; intros; inv MS; EliminatedInstr.

- (* nop *)
  TransfInstr. left. econstructor; split.
  eapply exec_Inop; eauto. constructor; auto.
- (* eliminated nop *)
  assert (s0 = pc') by congruence. subst s0.
  right. split. simpl. omega. split. auto.
  econstructor; eauto.

- (* op *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
  exploit eval_operation_lessdef; eauto.
  intros [v' [EVAL' VLD]].
  left. exists (State s' (transf_function ce f) (Vptr sp0 Ptrofs.zero) pc' (rs'#res <- v') m'); split.
  eapply exec_Iop; eauto.  rewrite <- EVAL'.
  apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto. apply set_reg_lessdef; auto.
- (* eliminated move *)
  rewrite H1 in H. clear H1. inv H.
  right. split. simpl. omega. split. auto.
  econstructor; eauto. simpl in H0. rewrite PMap.gss. congruence.

- (* load *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
  exploit eval_addressing_lessdef; eauto.
  intros [a' [ADDR' ALD]].
  exploit Mem.loadv_extends; eauto.
  intros [v' [LOAD' VLD]].
  left. exists (State s' (transf_function ce f) (Vptr sp0 Ptrofs.zero) pc' (rs'#dst <- v') m'); split.
  eapply exec_Iload with (a := a'). eauto.  rewrite <- ADDR'.
  apply eval_addressing_preserved. exact symbols_preserved.
  rewrite comp_transl. eauto.
  econstructor; eauto. apply set_reg_lessdef; auto.

- (* store *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
  exploit eval_addressing_lessdef; eauto.
  intros [a' [ADDR' ALD]].
  exploit Mem.storev_extends. 2: eexact H1. eauto. eauto. apply RLD.
  intros [m'1 [STORE' MLD']].
  left. exists (State s' (transf_function ce f) (Vptr sp0 Ptrofs.zero) pc' rs' m'1); split.
  eapply exec_Istore with (a := a'). eauto.  rewrite <- ADDR'.
  apply eval_addressing_preserved. exact symbols_preserved.
  rewrite comp_transl. eauto.
  destruct a; simpl in H1; try discriminate.
  econstructor; eauto.

  (* TODO: Should be a lemma? *)
  { clear -ALD STORE' STACKS.
    inv ALD; simpl in STORE'.
    revert STACKS. generalize (comp_of f). intros cp STACKS.
    (* generalize dependent (comp_of f). intros cp STACKS. *)
    induction STACKS.
    - constructor.
    - constructor; eauto.
      eapply Mem.store_can_access_block_inj in STORE'. eapply STORE'; eauto.
    - constructor; eauto. }
  inv ALD; simpl in STORE'. eapply Mem.store_can_access_block_inj in STORE'; eapply STORE'. eauto.

- (* call *)
  exploit find_function_translated; eauto.
  intros (cu & tf & FIND' & Etf & ORDER). subst tf.
  assert (E : (comp_of f) = comp_of (transf_function ce f)).
  { symmetry. apply comp_transl. }
  TransfInstr.
+ (* call turned tailcall *)
  assert ({ m'' | Mem.free m' sp0 0 (fn_stacksize (transf_function ce f)) (fn_comp f) = Some m''}).
    apply Mem.range_perm_free. rewrite stacksize_preserved. rewrite H7.
    red; intros; omegaContradiction.
    eauto.
  destruct X as [m'' FREE].
  assert (Efd: comp_of fd = (comp_of f)).
  { exploit find_function_intra_compartment_call; eauto. }
  left.
  exists (Callstate s' (transf_fundef (compenv_program cu) fd) (rs'##args) m''); split.
  eapply exec_Itailcall; eauto.
  { apply sig_preserved. }
  { now rewrite comp_transl, comp_transl. }
  { now rewrite <- E. }
  eapply find_function_ptr_translated; eauto.
  rewrite comp_transl. eapply allowed_call_translated; eauto.
  rewrite comp_transl; eauto.
  constructor. eapply match_stackframes_tail; eauto.
  (* TODO: Should be a lemma? *)
  { rewrite Efd.
    clear -FREE STACKS.
    revert STACKS. generalize (comp_of f). intros cp STACKS.
    induction STACKS.
    - constructor.
    - constructor; auto. eapply Mem.free_can_access_block_inj_1; eauto.
    - constructor; auto. }
    apply (cenv_compat_linkorder _ _ _ ORDER (compenv_program_compat _)).
  { red. simpl. congruence. }
  apply regs_lessdef_regs; auto.
  eapply Mem.free_right_extends; eauto.
  rewrite stacksize_preserved. rewrite H7. intros. omegaContradiction.
+ (* call that remains a call *)
  left. exists (Callstate (Stackframe res (transf_function ce f) (Vptr sp0 Ptrofs.zero) pc' rs' :: s')
                          (transf_fundef (compenv_program cu) fd) (rs'##args) m'); split.
  eapply exec_Icall; eauto. apply sig_preserved.
  eapply find_function_ptr_translated; eauto.
  rewrite comp_transl. eapply allowed_call_translated; eauto.
  rewrite <- E.
  intros CROSS.
  assert (forall rs rs',
             regs_lessdef rs rs' ->
             forall l,
               Forall not_ptr rs ## l ->
               Forall not_ptr rs' ## l).
  { clear. intros rs rs' LESSDEF.
    induction l; intros.
    - eauto.
    - inv H.
      constructor.
      + specialize (LESSDEF a). inv LESSDEF; eauto.
        rewrite <- H0 in H2; now simpl in H2.
      + eauto. }
  eapply H1; eauto.
  eapply NO_CROSS_PTR; eauto.
  erewrite find_comp_translated, type_of_call_translated; eauto.
  constructor. constructor; auto.
    apply (cenv_compat_linkorder _ _ _ ORDER (compenv_program_compat _)).
  { easy. }
  apply regs_lessdef_regs; auto. auto.

- (* tailcall *)
  exploit find_function_translated; eauto.
  intros (cu & tf & FIND' & Etf & ORDER). subst tf.
  exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
  TransfInstr.
  assert (Ef: (comp_of f) = comp_of (transf_function ce f)) by now symmetry; apply comp_transl.
  left. exists (Callstate s' (transf_fundef (compenv_program cu) fd) (rs'##args) m'1); split.
  eapply exec_Itailcall; eauto. apply sig_preserved.
    now rewrite comp_transl, COMP.
  { now rewrite Ef in ALLOWED. }
  eapply find_function_ptr_translated; eauto.
  rewrite comp_transl. eapply allowed_call_translated; eauto.
  rewrite stacksize_preserved; auto.
  rewrite comp_transl; eauto.
  constructor.
  (* TODO: Should be a lemma? *)
  { rewrite COMP. clear -FREE STACKS.
    revert STACKS. generalize (comp_of f). intros cp STACKS.
    induction STACKS.
    - constructor.
    - constructor; auto. eapply Mem.free_can_access_block_inj_1; eauto.
    - constructor; auto. }
  auto.
    apply (cenv_compat_linkorder _ _ _ ORDER (compenv_program_compat _)).
  { red. now rewrite COMP, ALLOWED. }
  apply regs_lessdef_regs; auto. auto.

- (* builtin *)
  TransfInstr.
  exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs'#r)); eauto.
  intros (vargs' & P & Q).
  exploit external_call_mem_extends; eauto.
  intros [v' [m'1 [A [B [C D]]]]].
  left. exists (State s' (transf_function ce f) (Vptr sp0 Ptrofs.zero) pc' (regmap_setres res v' rs') m'1); split.
  eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  rewrite comp_transf_function; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.
  (* TODO: Should be a lemma! *)
  { clear -A STACKS.
    revert STACKS. generalize (comp_of f). intros cp STACKS.
    induction STACKS.
    - constructor.
    - constructor; auto. eapply external_call_can_access_block; eauto.
    - constructor; auto. }
  apply set_res_lessdef; auto.
  eapply external_call_can_access_block; eauto.

- (* cond *)
  TransfInstr.
  left. exists (State s' (transf_function ce f) (Vptr sp0 Ptrofs.zero) (if b then ifso else ifnot) rs' m'); split.
  eapply exec_Icond; eauto.
  apply eval_condition_lessdef with (rs##args) m; auto. apply regs_lessdef_regs; auto.
  constructor; auto.

- (* jumptable *)
  TransfInstr.
  left. exists (State s' (transf_function ce f) (Vptr sp0 Ptrofs.zero) pc' rs' m'); split.
  eapply exec_Ijumptable; eauto.
  generalize (RLD arg). rewrite H0. intro. inv H2. auto.
  constructor; auto.

- (* return *)
  exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
  TransfInstr.
  left. exists (Returnstate s' (regmap_optget or Vundef rs') m'1 (comp_of (transf_function ce f))); split.
  eapply exec_Ireturn; eauto.
  rewrite stacksize_preserved, comp_transl; eauto.
  rewrite comp_transf_function. constructor.
  (* TODO: Should be a lemma? *)
  { clear -FREE STACKS.
    revert STACKS. generalize (comp_of f). intros cp STACKS.
    induction STACKS.
    - constructor.
    - constructor; auto. eapply Mem.free_can_access_block_inj_1; eauto.
    - constructor; auto. }
  destruct or; simpl. apply RLD. constructor.
  auto.

- (* eliminated return None *)
  assert (or = None) by congruence. subst or.
  right. split. simpl. omega. split. auto.
  constructor. auto.
  simpl. constructor.
  eapply Mem.free_left_extends; eauto.

- (* eliminated return Some *)
  assert (or = Some r) by congruence. subst or.
  right. split. simpl. omega. split. auto.
  constructor. auto.
  simpl. auto.
  eapply Mem.free_left_extends; eauto.

- (* internal call *)
  exploit Mem.alloc_extends; eauto.
    instantiate (1 := 0). omega.
    instantiate (1 := fn_stacksize f). omega.
  intros [m'1 [ALLOC EXT]].
  assert (fn_stacksize (transf_function ce f) = fn_stacksize f /\
          fn_entrypoint (transf_function ce f) = fn_entrypoint f /\
          fn_params (transf_function ce f) = fn_params f /\
          comp_of (transf_function ce f) = comp_of f).
    unfold transf_function. destruct (zeq (fn_stacksize f) 0); auto.
  destruct H0 as [EQ1 [EQ2 [EQ3 EQ4]]].
  left. econstructor; split.
  simpl. eapply exec_function_internal; eauto. rewrite EQ1, EQ4; eauto.
  rewrite EQ2. rewrite EQ3. constructor; auto.
  (* TODO: Should be a lemma? *)
  { clear -ALLOC H5. unfold comp_of in H5; simpl in H5.
    revert H5. generalize (comp_of f). intros cp STACKS.
    induction STACKS.
    - constructor.
    - constructor; auto.
      eapply Mem.alloc_can_access_block_other_inj_1; eauto.
    - constructor; auto. }
  apply regs_lessdef_init_regs. auto.
  eapply Mem.owned_new_block; eauto.

- (* external call *)
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [A [B [C D]]]]].
  left. exists (Returnstate s' res' m2' (comp_of ef)); split.
  simpl. econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  destruct (needs_calling_comp (comp_of ef)) eqn:ALLOWED.
  { now rewrite <- (UPD ALLOWED). }
  exploit external_call_caller_independent; eauto.
  constructor; auto.
  (* TODO: Should be a lemma? *)
  { clear -A H5.
    remember (call_comp s) as cp. clear Heqcp. unfold comp_of in H5; simpl in H5.
    induction H5.
    - constructor.
    - constructor; auto. eapply external_call_can_access_block; eauto.
    - constructor; auto. }

- (* returnstate *)
  inv H4.
+ (* synchronous return in both programs *)
  left. econstructor; split.
  apply exec_return.
  rewrite comp_transf_function, <- type_of_call_translated.
  { intros G. specialize (NO_CROSS_PTR G).
    inv H5; auto; contradiction. }
  constructor; auto. apply set_reg_lessdef; auto.
+ (* return instr in source program, eliminated because of tailcall *)
  right. split. unfold measure. simpl length.
  change (S (length s) * (niter + 2))%nat
   with ((niter + 2) + (length s) * (niter + 2))%nat.
  generalize (return_measure_bounds (fn_code f) pc). omega.
  split. auto.
  econstructor; eauto.
  rewrite Regmap.gss. auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit funct_ptr_translated; eauto.
  intros (cu & tf & FIND & Etf & ORDER). subst tf.
  exists (Callstate nil (transf_fundef (compenv_program cu) f) nil m0); split.
  econstructor; eauto.
  eapply (Genv.init_mem_match TRANSL); eauto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry; eapply match_program_main; eauto.
  rewrite <- H3. apply sig_preserved.
  constructor. constructor.
    apply (cenv_compat_linkorder _ _ _ ORDER (compenv_program_compat _)).
  easy.
  constructor. apply Mem.extends_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H5. inv H6. constructor.
Qed.


(** The preservation of the observable behavior of the program then
  follows. *)

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_opt with (measure := measure); eauto.
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transf_step_correct.
Qed.

End PRESERVATION.
