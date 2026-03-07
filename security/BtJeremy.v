Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Split.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Stacklayout.
Require Import Conventions.

Require Import Exec Determinism.

Notation offset_arg := Stacklayout.offset_arg.

Require Import Asm MemoryDelta.


Definition bt_event := (event * mem_delta)%type.
Definition bt_trace := list bt_event.

Inductive step: state -> bt_trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m' b' ofs' st cp,
      rs PC = Vptr b ofs ->
      Genv.find_def ge b = Some (Gfun (Internal f)) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m (comp_of f) = Next rs' m' ->
      sig_call i = None ->
      is_return i = false ->
      forall (NEXTPC: rs' PC = Vptr b' ofs'),
      forall (ALLOWED: comp_of f = Genv.find_comp_of_block ge b'),
      step (State st rs m cp) E0 (State st rs' m' (comp_of f))

  | exec_step_load_arg_cross:
      forall b ofs f ch rd ra rs m st cp dsp o o' sp v rs' ty,
      rs PC = Vptr b ofs ->
      Genv.find_def ge b = Some (Gfun (Internal f)) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some (Pld_arg ch rd ra o) ->
      asm_parent_dummy_sp st = Vptr dsp Ptrofs.zero ->
      rs ra = Vptr dsp o' ->
      asm_parent_sp st = sp ->
      Stacklayout.is_valid_param_loc (parent_signature st)
        (Ptrofs.unsigned (Ptrofs.add o' (eval_offset o))) ty ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr sp (Ptrofs.add o' (eval_offset o))) top = Some v ->
      (forall ird, rd = inl ird -> rs' = nextinstr rs # ird <- v) ->
      (forall frd, rd = inr frd -> rs' = nextinstr rs # frd <- v) ->
      step (State st rs m cp) E0 (State st rs' m (comp_of f))

  | exec_step_load_arg_int:
      forall b ofs f ch rd ra rs m st cp o rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_def ge b = Some (Gfun (Internal f)) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some (Pld_arg ch rd ra o) ->
      forall (EXECi: forall ird, rd = inl ird ->
                       exec_load ch rs m ird ra o (comp_of f) false = Next rs' m'),
      forall (EXECf: forall frd, rd = inr frd ->
                       exec_load ch rs m frd ra o (comp_of f) false = Next rs' m'),
      step (State st rs m cp) E0 (State st rs' m' (comp_of f))

  | exec_step_internal_call:
      forall b ofs f i sig rs m rs' m' m'' b'  st st' args t rs'' rs''' f',
      rs PC = Vptr b ofs ->
      Genv.find_def ge b = Some (Gfun (Internal f)) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m (comp_of f) = Next rs' m' ->
      sig_call i = Some sig ->
      forall (NEXTPC: rs' PC = Vptr b' Ptrofs.zero), (* Only allow to call to ofs zero *)
      forall (NEXT_INT: Genv.find_def ge b' = Some (Gfun (Internal f'))),
      forall (ALLOWED: Genv.allowed_call ge (comp_of f) (Vptr b' Ptrofs.zero)),
      forall cp' (NEXTCOMP: Genv.find_comp_of_block ge b' = cp'),
      forall (STUPD: update_stack_call st sig (comp_of f) rs' m' = Some (st', rs'', m'')),
      forall (ARGS: Genv.type_of_call (comp_of f) cp' = Genv.CrossCompartmentCall ->
               call_arguments rs' (rs'#SP) m' sig args),
      forall (CALLSIG:
          Genv.type_of_call (comp_of f) cp' = Genv.CrossCompartmentCall ->
        (exists fd, Genv.find_def ge b' = Some (Gfun fd) /\ sig = funsig fd)),
      forall (NO_CROSS_PTR:
          Genv.type_of_call (comp_of f) cp' = Genv.CrossCompartmentCall ->
          List.Forall not_ptr args),
      forall (EV: call_trace ge (comp_of f) cp' (Vptr b' Ptrofs.zero)
              args (proj_sig_args sig) t),
      forall (INVALIDATE: invalidate_call rs'' sig = rs'''),
      step (State st rs m (comp_of f)) t (State st' rs''' m'' (comp_of f))
  | exec_step_internal_return:
      forall b ofs f i rs m rs' m' st cp,
      rs PC = Vptr b ofs ->
      Genv.find_def ge b = Some (Gfun (Internal f)) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m (comp_of f) = Next rs' m' ->
      is_return i = true ->
      step (State st rs m cp) E0 (ReturnState st rs' m' (fn_sig f) (comp_of f))
  | exec_step_return:
      forall st rs rs' m rec_cp cp b ofs fd sg,
        rs PC <> Vnullptr ->
        rs PC <> Vundef ->
        forall (ATPC: rs PC = Vptr b ofs),
        forall (FD: Genv.find_def ge b = Some (Gfun (Internal fd))),
        forall (NEXTCOMP: Genv.find_comp_in_genv ge (rs PC) = cp),
        forall (INTERNAL_RET: rec_cp = cp),
        forall (INVALIDATE: invalidate_return rs sg = rs'),
          step (ReturnState st rs m sg rec_cp) E0 (State st rs' m cp)
  | exec_step_return_cross:
      forall st st' rs rs' rs'' m m' sg t rec_cp cp',
        rs PC <> Vnullptr ->
        rs PC <> Vundef ->
        rs PC = asm_parent_dummy_ra st ->
        forall (CROSS_RET: rec_cp <> cp'),
        forall (RESTORE_SP: rs SP = asm_parent_dummy_sp st),
        forall (STUPD: update_stack_return st = Some st'),
        forall (SIG_STACK: sig_res (sig_of_call st) = sig_res sg),
        forall (NO_CROSS_PTR: Genv.type_of_call cp' rec_cp = Genv.CrossCompartmentCall ->
                         not_ptr (return_value rs sg)),
        forall (COMP: Genv.find_comp_in_genv ge (asm_parent_ra st) = cp'),
        forall (EV: return_trace ge cp' rec_cp (return_value rs sg) (sig_res sg) t),
      forall (INVALIDATE: invalidate_return rs sg = rs'),
      forall (INVALIDATE: invalidate_cross_return rs' st = rs''),
      forall (MAKE_FREEABLE: Some m' = match asm_parent_sp st with
                             | Vptr bsp _ => Mem.set_perm m bsp Freeable
                             | _ => None
                             end),
          step (ReturnState st rs m sg rec_cp) t (State st' rs'' m' cp')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m' st,
      rs PC = Vptr b ofs ->
      Genv.find_def ge b= Some (Gfun (Internal f)) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge (comp_of f) rs (rs SP) m args vargs ->
      external_call ef ge (comp_of f) vargs m t vres m' ->
      forall (RES_NOT_PC: exists reg, res = map_builtin_res preg_of reg),
      forall (ALLOWED: Genv.allowed_syscall ge (comp_of f) ef),
      rs' = nextinstr
              (set_res res vres
                (undef_regs (map preg_of (destroyed_by_builtin ef))
                   (rs #X1 <- Vundef #X31 <- Vundef))) ->
      step (State st rs m (comp_of f)) t (State st rs' m' (comp_of f))
  | exec_step_external_call:
      forall b ofs f i sig rs m rs' rs'' m' m'' b'  st args t ef res,
      rs PC = Vptr b ofs ->
      Genv.find_def ge b = Some (Gfun (Internal f)) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m (comp_of f) = Next rs' m' ->
      sig_call i = Some sig ->
      forall (NEXTPC: rs' PC = Vptr b' Ptrofs.zero), (* Only allow to call to ofs zero *)
      forall (NEXT_EXT: Genv.find_def ge b' = Some (Gfun (External ef))),
      forall (ALLOWED: Genv.allowed_syscall ge (comp_of f) ef),
      external_call ef ge (comp_of f) args m' t res m'' ->
      extcall_arguments rs' (rs' # SP) m' (ef_sig ef) args ->
      rs'' = (invalidate_return
              (set_pair (loc_external_result (ef_sig ef))
                 res rs')
              (ef_sig ef)) # PC <- (Val.offset_ptr (rs PC) Ptrofs.one) ->

      step (State st rs m (comp_of f)) t (State st rs'' m'' (comp_of f))
.

End RELSEM.

(** Execution of whole programs. *)
Definition comp_of_main (p: program) :=
  let ge := Genv.globalenv p in
  Genv.find_comp_of_ident ge (prog_main p).

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0 b fi,
      Genv.find_symbol (Genv.globalenv p) p.(prog_main) = Some b ->
      Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal fi) ->
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
        # SP <- Vnullptr
        # RA <- Vnullptr in
      Genv.init_mem p = Some m0 ->
      initial_state p (State nil rs0 m0 (comp_of_main p)).

Inductive final_state (p: program): state -> int -> Prop :=
  | final_state_intro: forall rs m r sg cp,
      rs PC = Vnullptr ->
      rs X10 = Vint r ->
      final_state p (ReturnState nil rs m sg cp) r
.

Definition semantics (p: program) :=
  Semantics step (initial_state p) (final_state p) (Genv.globalenv p).
(** Determinacy of the [Asm] semantics. *)

Remark extcall_arguments_determ:
  forall rs sp m sg args1 args2,
  extcall_arguments rs sp m sg args1 -> extcall_arguments rs sp m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             extcall_arg rs sp m l v1 -> extcall_arg rs sp m l v2 -> v1 = v2).
  { intros. inv H; inv H0. congruence.
    destruct sp; try discriminate.
    simpl in H2, H5.
    apply Mem.load_result in H2.
    apply Mem.load_result in H5. congruence. }
  assert (B: forall p v1 v2,
             extcall_arg_pair rs sp m p v1 -> extcall_arg_pair rs sp m p v2 -> v1 = v2).
  { intros. inv H; inv H0.
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs sp m) ll vl1 ->
             forall vl2, list_forall2 (extcall_arg_pair rs sp m) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

Remark call_arguments_determ:
  forall rs sp m sg args1 args2,
  call_arguments rs sp m sg args1 -> call_arguments rs sp m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             call_arg rs sp m l v1 -> call_arg rs sp m l v2 -> v1 = v2).
  { intros. inv H; inv H0. congruence.
    destruct sp; try discriminate.
    simpl in H2, H5.
    apply Mem.load_result in H2.
    apply Mem.load_result in H5. congruence. }
  assert (B: forall p v1 v2,
             call_arg_pair rs sp m p v1 -> call_arg_pair rs sp m p v2 -> v1 = v2).
  { intros. inv H; inv H0.
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (call_arg_pair rs sp m) ll vl1 ->
             forall vl2, list_forall2 (call_arg_pair rs sp m) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

(* RB: NOTE: In the next proof, the wrapped [exec_instr] would require extra
   processing, such as this. *)
(* Ltac peel_exec_instr := *)
(*   match goal with *)
(*   | Hexec : exec_instr _ _ _ ?RS ?M = _, *)
(*     Hpc : ?RS PC = Vptr ?B _ |- _ *)
(*     => *)
(*     unfold exec_instr in Hexec; *)
(*     rewrite Hpc in Hexec; *)
(*     destruct ((Mem.mem_compartments M) ! B) *)
(*   end. *)

Lemma in_param_one_same_ty: forall ofs_arg ty ty0 sg,
    In (One (S Incoming ofs_arg ty)) (loc_parameters sg) ->
    In (One (S Incoming ofs_arg ty0)) (loc_parameters sg) ->
    ty = ty0.
Proof.
  unfold loc_parameters.
  intros ofs_arg ty ty0 sg A B.
  apply list_in_map_inv in A as [x [A A']].
  apply list_in_map_inv in B as [y [B B']].
  destruct x; simpl in A; try congruence.
  destruct y; simpl in B; try congruence.
Admitted.

Lemma in_param_twolong_hi_same_ty: forall ofs_arg ty ty0 lo lo0 sg,
    In (Twolong (S Incoming ofs_arg ty) lo) (loc_parameters sg) ->
    In (Twolong (S Incoming ofs_arg ty0) lo0) (loc_parameters sg) ->
    ty = ty0.
Proof.
Admitted.

Lemma in_param_twolong_lo_same_ty: forall ofs_arg ty ty0 hi hi0 sg,
    In (Twolong hi (S Incoming ofs_arg ty)) (loc_parameters sg) ->
    In (Twolong hi0 (S Incoming ofs_arg ty0)) (loc_parameters sg) ->
    ty = ty0.
Proof.
Admitted.

Lemma in_param_twolong_hi_lo: forall ofs_arg ty ty0 hi lo sg,
    In (Twolong hi (S Incoming ofs_arg ty)) (loc_parameters sg) ->
    In (Twolong (S Incoming ofs_arg ty0) lo) (loc_parameters sg) ->
    False.
Proof.
Admitted.

Lemma in_param_one_twolong_hi: forall ofs_arg ty ty0 lo sg,
    In (One (S Incoming ofs_arg ty)) (loc_parameters sg) ->
    In (Twolong (S Incoming ofs_arg ty0) lo) (loc_parameters sg) ->
    False.
Proof.
Admitted.

Lemma in_param_one_twolong_lo: forall ofs_arg ty ty0 hi sg,
    In (One (S Incoming ofs_arg ty)) (loc_parameters sg) ->
    In (Twolong hi (S Incoming ofs_arg ty0)) (loc_parameters sg) ->
    False.
Proof.
Admitted.

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
intros; constructor; simpl; intros.
- (* determ *)
  inv H; inv H0; Equalities; try discriminate.
  + split. constructor. auto.
  + split. constructor.
    destruct rd0.
    * exploit H9; eauto. exploit H23; eauto.
      assert (ty = ty0) as <-.
      { inv H19; inv H7.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          eapply in_param_one_same_ty; eauto.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          exfalso; eapply in_param_one_twolong_hi; eauto.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          exfalso; eapply in_param_one_twolong_lo; eauto.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          exfalso; eapply in_param_one_twolong_hi; eauto.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          eapply in_param_twolong_hi_same_ty; eauto.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          exfalso; eapply in_param_twolong_hi_lo; eauto.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          exfalso; eapply in_param_one_twolong_lo; eauto.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          exfalso; eapply in_param_twolong_hi_lo; eauto.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          eapply in_param_twolong_lo_same_ty; eauto.
      }
      assert (v = v0) as <- by congruence.
      congruence.
    * exploit H10; eauto. exploit H24; eauto.
      assert (ty = ty0) as <-.
      { inv H19; inv H7.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          eapply in_param_one_same_ty; eauto.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          exfalso; eapply in_param_one_twolong_hi; eauto.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          exfalso; eapply in_param_one_twolong_lo; eauto.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          exfalso; eapply in_param_one_twolong_hi; eauto.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          eapply in_param_twolong_hi_same_ty; eauto.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          exfalso; eapply in_param_twolong_hi_lo; eauto.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          exfalso; eapply in_param_one_twolong_lo; eauto.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          exfalso; eapply in_param_twolong_hi_lo; eauto.
        - assert (ofs_arg0 = ofs_arg) as -> by lia.
          eapply in_param_twolong_lo_same_ty; eauto.
      }
      assert (v = v0) as <- by congruence.
      congruence.
  + admit.
  + admit.
  + split. constructor. auto.
    destruct rd0.
    * exploit EXECi; eauto. exploit EXECi0; eauto.
      congruence.
    * exploit EXECf; eauto. exploit EXECf0; eauto.
      congruence.
  + inv EV; inv EV0; try congruence.
    split. constructor. auto.
    assert (i1 = i) by congruence. subst.
    assert (args0 = args) by (eapply call_arguments_determ; eauto). subst.
    assert (vl0 = vl) by (eapply eventval_list_match_determ_2; eauto). subst.
    split. constructor. auto.
  + now destruct i0.
  + now destruct i0.
  + split. constructor. auto.
  + now destruct i0.
  + split; constructor; auto.
  + admit.
  + admit.
  (* + admit. *)
  (* + admit. *)
  + inv EV; inv EV0; try congruence.
    split. constructor. intros _.
    assert (m' = m'0) as <- by congruence.
    reflexivity.
    assert (res = res0) as <- by (eapply eventval_match_determ_2; eauto).
    split. constructor. intros _.
    assert (m' = m'0) as <- by congruence.
    reflexivity.
  + assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
    exploit external_call_determ. eexact H5. eexact H15. intros [A B].
    split. auto. intros. destruct B; auto. subst. auto.
  + now destruct i0.
  +
    (* assert (ef = ef0) as <- by congruence. *)
    assert (args0 = args) as ->
        by (eapply extcall_arguments_determ; eauto).
    exploit external_call_determ. eexact H6. eexact H18. intros [A B].
    split. auto. intros. destruct B; auto. subst. eauto.
- (* trace length *)
  red; intros. inv H; simpl.
  lia. lia. lia.
  inv EV; auto.
  lia. lia.
  inv EV; auto.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0. f_equal. congruence.
- (* final no step *)
  inv H.
  red; intros; red; intros.
  inv H. congruence. congruence.
- (* final states *)
  inv H; inv H0. congruence.
Admitted.

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | IR RA  => false
  | IR X31 => false
  | IR _   => true
  | FR _   => true
  | PC     => false
  end.

Section ExecSem.

  Declare Scope reducts_monad_scope.

  Notation "'do' U <- A ; B" := (match A with Some U => B | None => None end)
                                 (at level 200, U name, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation "'do' 'Vptr' U Y <- A ; B" := (match A with Vptr U Y => B | _ => None end)
                                          (at level 200, U name, Y name, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation "'do' U , Y <- A ; B" := (match A with Some (U, Y) => B | None => None end)
                                     (at level 200, U name, Y name, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation "'do' U , Y , Z <- A ; B" := (match A with Some (U, Y, Z) => B | None => None end)
                                         (at level 200, U name, Y name, Z name, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation "'do' U , Y , Z , W <- A ; B" := (match A with Some (U, Y, Z, W) => B | None => None end)
                                             (at level 200, U name, Y name, Z name, W name, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation " 'check' A ; B" := (if A then B else None)
                                 (at level 200, A at level 100, B at level 200)
      : reducts_monad_scope.

  Local Open Scope reducts_monad_scope.

  Variable do_external_function:
    string -> signature -> Senv.t -> compartment -> world -> list val -> mem -> option (world * trace * val * mem).

  Hypothesis do_external_function_sound:
    forall cp id sg ge vargs m t vres m' w w',
      do_external_function id sg ge cp w vargs m = Some(w', t, vres, m') ->
      external_functions_sem id sg ge cp vargs m t vres m' /\ possible_trace w t w'.

  Hypothesis do_external_function_complete:
    forall cp id sg ge vargs m t vres m' w w',
      external_functions_sem id sg ge cp vargs m t vres m' ->
      possible_trace w t w' ->
      do_external_function id sg ge cp w vargs m = Some(w', t, vres, m').

  Variable do_inline_assembly:
    string -> signature -> Senv.t -> compartment -> world -> list val -> mem -> option (world * trace * val * mem).

  Hypothesis do_inline_assembly_sound:
    forall txt sg ge cp vargs m t vres m' w w',
      do_inline_assembly txt sg ge cp w vargs m = Some(w', t, vres, m') ->
      inline_assembly_sem txt sg ge cp vargs m t vres m' /\ possible_trace w t w'.

  Hypothesis do_inline_assembly_complete:
    forall txt sg ge cp vargs m t vres m' w w',
      inline_assembly_sem txt sg ge cp vargs m t vres m' ->
      possible_trace w t w' ->
      do_inline_assembly txt sg ge cp w vargs m = Some(w', t, vres, m').

  Fixpoint get_builtin_arg (ge: genv) (cp: compartment) (rs: regset) (sp: val) (m: mem) (b: builtin_arg preg): option val :=
    match b with
    | BA x => Some (rs x)
    | BA_int n => Some (Vint n)
    | BA_long n => Some (Vlong n)
    | BA_float n => Some (Vfloat n)
    | BA_single n => Some (Vsingle n)
    | BA_loadstack chunk ofs => Mem.loadv chunk m (Val.offset_ptr sp ofs) top
    | BA_addrstack ofs => Some (Val.offset_ptr sp ofs)
    | BA_loadglobal chunk id ofs =>
          Mem.loadv chunk m (Genv.symbol_address ge id ofs) cp
    | BA_addrglobal id ofs => if Genv.allowed_addrof_b ge cp id then
                               Some (Genv.symbol_address ge id ofs)
                             else None
    | BA_splitlong hi lo =>
        match get_builtin_arg ge cp rs sp m hi, get_builtin_arg ge cp rs sp m lo with
        | Some vhi, Some vlo => Some (Val.longofwords vhi vlo)
        | _, _ => None
        end
    | BA_addptr a1 a2 =>
        match get_builtin_arg ge cp rs sp m a1, get_builtin_arg ge cp rs sp m a2 with
        | Some v1, Some v2 => Some (if Archi.ptr64 then Val.addl v1 v2 else Val.add v1 v2)
        | _, _ => None
        end
    end.

  Lemma get_eval_builtin_arg: forall ge cp rs sp m b v,
      get_builtin_arg ge cp rs sp m b = Some v <-> eval_builtin_arg ge cp rs sp m b v.
  Proof.
    intros until b.
    induction b; intros; simpl;
      try now (split; [intros H; inv H; constructor | intros H; inv H; auto]).
    - split; [intros H; econstructor; eauto | intros H; inv H].
      destruct (Val.offset_ptr); try discriminate; simpl in *.
      eapply Mem.load_Some_None; eauto.
    - split; [intros H (* econstructor; eauto *) | intros H; inv H].
      destruct Genv.allowed_addrof_b eqn:?. inv H.
      econstructor; eauto. congruence.
      destruct Genv.allowed_addrof_b eqn:?; auto.
      rewrite H3 in Heqb; discriminate.
      (* econstructor; eauto. congruence. *)
      (* unfold Genv.symbol_address, Senv.symbol_address in *; simpl in *. *)
      (* destruct (Genv.find_symbol ge id); try discriminate; simpl in *. *)
      (* eapply Mem.load_Some_None; eauto. *)
    - split; [intros H | intros H; inv H].
      + destruct (get_builtin_arg ge cp rs sp m b1); try discriminate.
        destruct (get_builtin_arg ge cp rs sp m b2); try discriminate.
        inv H. econstructor; [eapply IHb1 | eapply IHb2]; eauto.
      + now eapply IHb1 in H2; eapply IHb2 in H4;
          rewrite H2, H4.
    - split; [intros H | intros H; inv H].
      + destruct (get_builtin_arg ge cp rs sp m b1); try discriminate.
        destruct (get_builtin_arg ge cp rs sp m b2); try discriminate.
        inv H. econstructor; [eapply IHb1 | eapply IHb2]; eauto.
      + now eapply IHb1 in H2; eapply IHb2 in H4;
          rewrite H2, H4.
  Qed.

  Definition get_builtin_args' (ge: genv) cp (rs: regset) (v: val) (m: mem) (args: list (builtin_arg preg)): list (option val) :=
    List.map (get_builtin_arg ge cp rs v m) args.

  Definition get_builtin_args ge cp rs v m args := list_option_option_list (get_builtin_args' ge cp rs v m args).


  Lemma get_eval_builtin_args: forall ge cp rs sp m bl vl,
      get_builtin_args ge cp rs sp m bl = Some vl <-> eval_builtin_args ge cp rs sp m bl vl.
  Proof.
    intros until bl.
    induction bl; intros.
    - unfold get_builtin_args; simpl.
      split; intros H; inv H; [constructor | reflexivity].
    - unfold get_builtin_args; simpl.
      split.
      + intros H. destruct (get_builtin_arg ge cp rs sp m a) eqn:get_a.
        * destruct (list_option_option_list (get_builtin_args' ge cp rs sp m bl)) eqn:get_rest; try discriminate.
          inv H.
          constructor; [eapply get_eval_builtin_arg; eauto | eapply IHbl; exact get_rest].
        * destruct (list_option_option_list (get_builtin_args' ge cp rs sp m bl)); discriminate.
      + intros H.
        inv H.
        eapply get_eval_builtin_arg in H2; rewrite H2.
        specialize (IHbl bl0) as [IHbl1 IHbl2].
        unfold get_builtin_args in IHbl2. rewrite IHbl2; auto.
  Qed.

  Definition take_step (p: program) (ge: genv) (w: world) (s: state): option (trace * state) :=
    let comp_of_main := comp_of_main p in
    match s with
    | State st rs m cp =>
        do Vptr b ofs <- rs PC;
        do fd <- Genv.find_funct_ptr ge b;
        match fd with
        | Internal f =>
            do i <- find_instr (Ptrofs.unsigned ofs) (fn_code f);
            match i with
            | Pbuiltin ef args res =>
                do vargs <- get_builtin_args ge (comp_of f) rs (rs X2) m args;
                do res_builtin <- do_external fundef unit ge do_external_function do_inline_assembly ef cp w vargs m;
                check (Genv.allowed_syscall_b ge (comp_of f) ef);
                let '(w', t, vres, m') := res_builtin in
                let rs' := nextinstr
                          (set_res res vres (undef_regs (map preg_of (destroyed_by_builtin ef)) (rs # X1 <- Vundef) # X31 <- Vundef)) in
                Some (t, State st rs' m' (comp_of f))
            | Pld_arg ch rd ra o =>
                match rd with
                | inl ird =>
                    match exec_load ge ch rs m ird ra o (comp_of f) false with
                    | Next rs' m' => Some (E0, State st rs' m' (comp_of f))
                    | Stuck =>
                        do Vptr dsp z <- asm_parent_dummy_sp st;
                        check (Ptrofs.eq z Ptrofs.zero);
                        do Vptr dsp o' <- rs ra;
                        let sp := asm_parent_sp st in
                        do v <- Mem.loadv ch m (Val.offset_ptr sp (Ptrofs.add o' (eval_offset ge o))) top;
                        let rs' := nextinstr (rs # ird <- v) in
                        Some (E0, State st rs' m (comp_of f))
                    end
                | inr frd =>
                    match exec_load ge ch rs m frd ra o (comp_of f) false with
                    | Next rs' m' => Some (E0, State st rs' m' (comp_of f))
                    | Stuck =>
                        do Vptr dsp z <- asm_parent_dummy_sp st;
                        check (Ptrofs.eq z Ptrofs.zero);
                        do Vptr dsp o' <- rs ra;
                        let sp := asm_parent_sp st in
                        do v <- Mem.loadv ch m (Val.offset_ptr sp (Ptrofs.add o' (eval_offset ge o))) top;
                        let rs' := nextinstr (rs # frd <- v) in
                        Some (E0, State st rs' m (comp_of f))
                    end
                end
            | _ =>
                match exec_instr ge f i rs m (comp_of f) with
                | Next rs' m' =>
                    match sig_call i, is_return i with
                    | None, false => (* exec_step_internal *)
                        do Vptr b' ofs' <- rs' PC;
                        let cp' := Genv.find_comp_of_block ge b' in
                        check (cp_eq_dec (comp_of f) cp');
                        Some (E0, State st rs' m' (comp_of f))
                    | Some sig, false => (* exec_step_internal_call *)
                        do Vptr b' ofs' <- rs' PC;
                        check (Genv.allowed_call_b ge (comp_of f) (Vptr b' Ptrofs.zero));
                        do st' <- update_stack_call ge st sig (comp_of f) rs' m';
                        let '(st'', rs'', m'') := st' in
                        let cp' := Genv.find_comp_of_block ge b' in
                        do vargs <-
                             match Genv.type_of_call (comp_of f) cp' with
                             | Genv.CrossCompartmentCall =>
                                 get_call_arguments rs' (rs' X2) m' sig
                             | _ => Some nil end;
                        (* do vargs <- get_call_arguments rs'' (rs'' X2) m' sig; *)
                        check (match Genv.type_of_call (comp_of f) cp' with
                               | Genv.CrossCompartmentCall => forallb not_ptr_b vargs
                               | _ => true
                               end);
                        do t <- get_call_trace fundef unit ge (comp_of f) cp' (Vptr b' ofs') vargs (proj_sig_args sig);
                        Some (t, State st'' (invalidate_call rs'' sig) m'' (comp_of f))
                    | None, true => (* exec_step_internal_return *)
                        (* check (Genv.allowed_call_b ge (comp_of f) (rs' PC)); *)
                        Some (E0, ReturnState st rs' m' (fn_sig f) (comp_of f))
                    | Some _, true => None
                    end
                | Stuck => None
                end
            end
        | External ef =>
            check (Ptrofs.eq ofs Ptrofs.zero);
            do vargs <- get_extcall_arguments rs (rs SP) m (ef_sig ef);
            do res_external <- do_external _ _ ge do_external_function do_inline_assembly ef cp w vargs m;
            check (Genv.allowed_syscall_b ge cp ef);
            let '(w', t, res, m') := res_external in
            let rs' := (set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs)) # PC <- (rs X1) in
            Some (t, ReturnState st rs' m' (ef_sig ef) bottom)
        end
    | ReturnState st rs m sg rec_cp =>
        check (negb (Val.eq (rs PC) Vnullptr));
        let cp' :=
          match Val.eq (rs PC) (asm_parent_dummy_ra st) with
          | left _ => Genv.find_comp_in_genv ge (asm_parent_ra st)
          | right _ => Genv.find_comp_in_genv ge (rs PC)
          end in
        check (match cp_eq_dec rec_cp cp' with
               | left _ => true
               | right _ => andb (Val.eq (rs PC) (asm_parent_dummy_ra st))
                             (Val.eq (rs X2) (asm_parent_dummy_sp st))
               end);
        do st' <-
          match cp_eq_dec rec_cp cp' with
          | left _ => Some st
          | right _ => update_stack_return st
          end;
        check (match Genv.type_of_call cp' rec_cp with
               | Genv.CrossCompartmentCall => not_ptr_b (return_value rs sg)
               | _ => true end);
        do t <- get_return_trace fundef unit ge cp' rec_cp (return_value rs sg) (sig_res sg);
        let rs' :=
          match Val.eq (rs PC) (asm_parent_dummy_ra st) with
          | left _ => invalidate_cross_return (invalidate_return rs sg) st
          | right _ => invalidate_return rs sg
          end in
        do m' <-
          match Val.eq (rs PC) (asm_parent_dummy_ra st) with
          | left _ => do Vptr bsp _ <- asm_parent_sp st;
                     Mem.set_perm m bsp Freeable
          | right _ => Some m
          end;
        Some (t, State st' rs' m' cp')
    end.

  Definition at_final_state (s: state): option int :=
    match s with
    | ReturnState nil rs m _ cp =>
        match rs X10 with
        | Vint r => if Val.eq (rs PC) Vnullptr then Some r else None
        | _ => None
        end
    | _ => None
    end.

  Lemma take_step_correct: forall p w s t s',
      let ge := Genv.globalenv p in
      step ge s t s' ->
      take_step p ge w s = Some (t, s').
  Proof.
    intros p w s t s' ge H.
    inv H; simpl; eauto.
    - rewrite H0; simpl.
      rewrite <- Genv.find_funct_ptr_iff in H1.
      rewrite H1, H2, H3, H4, H5, NEXTPC, ALLOWED.
      destruct cp_eq_dec; auto; try congruence.
      destruct i; auto.
      inv H3. inv H3.
    - rewrite H0; simpl.
      rewrite <- Genv.find_funct_ptr_iff in H1.
      rewrite H1, H2, H3, H4.
      destruct rd; auto.
      + destruct exec_load eqn:?; auto.
        * admit.
        * assert (ch = chunk_of_type ty) as ->.
          { admit. }
          erewrite Ptrofs.eq_true, H7, H8; eauto.
      + destruct exec_load eqn:?; auto.
        * admit.
        * assert (ch = chunk_of_type ty) as ->.
          { admit. }
          erewrite Ptrofs.eq_true, H7, H9; eauto.
    - rewrite H0; simpl.
      rewrite <- Genv.find_funct_ptr_iff in H1.
      rewrite H1, H2.
      destruct rd; auto.
      + rewrite EXECi; auto.
      + rewrite EXECf; auto.
    - rewrite H0; simpl.
      rewrite <- Genv.find_funct_ptr_iff in H1.
      rewrite H1, H2, H3, H4.
      destruct i; try now inv H4.
      + simpl.
        rewrite NEXTPC. apply Genv.allowed_call_reflect in ALLOWED.
        rewrite ALLOWED. rewrite STUPD.
        unfold get_call_trace. unfold Genv.type_of_call in *.
        destruct flowsto_dec.
        assert (t = E0) as -> by admit. reflexivity.
        admit.
      + admit.
    - rewrite H0; simpl.
      rewrite <- Genv.find_funct_ptr_iff in H1.
      rewrite H1, H2, H3, H4.
      destruct i; try now inv H4.
    - replace (negb (Val.eq (rs PC) Vnullptr)) with true.
      destruct cp_eq_dec; try congruence.
      destruct Val.eq; try congruence.
      unfold get_return_trace, Genv.type_of_call.
      destruct flowsto_dec; auto. rewrite e; auto.
      unfold get_return_trace, Genv.type_of_call.
      admit.
      admit.
      admit.
      admit.
      admit.
    - admit.
    - admit.
    - admit.
  Admitted.
  (*   - rewrite H0, H1, H2, H3, H4, NEXTPC. *)
  (*     destruct i; inv H4; simpl. *)
  (*     + apply Genv.allowed_call_reflect in ALLOWED; rewrite ALLOWED. *)
  (*       rewrite STUPD. eapply get_call_arguments_equiv in ARGS; eauto; rewrite ARGS. *)
  (*       simpl in NO_CROSS_PTR. destruct flowsto_dec; try auto. *)
  (*       * apply get_call_trace_eq in EV; rewrite EV. reflexivity. *)
  (*       * exploit NO_CROSS_PTR; eauto; intros G. *)
  (*         rewrite Forall_forall in G. *)
  (*         pose proof forallb_forall as [X Y]. rewrite Y. *)
  (*         apply get_call_trace_eq in EV; rewrite EV. reflexivity. *)
  (*         intros. exploit G; eauto. intros. eapply not_ptr_reflect; eauto. *)
  (*     + apply Genv.allowed_call_reflect in ALLOWED; rewrite ALLOWED. *)
  (*       rewrite STUPD. eapply get_call_arguments_equiv in ARGS; eauto; rewrite ARGS. *)
  (*       simpl in NO_CROSS_PTR. destruct flowsto_dec; try auto. *)
  (*       * apply get_call_trace_eq in EV; rewrite EV. reflexivity. *)
  (*       * exploit NO_CROSS_PTR; eauto; intros G. *)
  (*         rewrite Forall_forall in G. *)
  (*         pose proof forallb_forall as [X Y]. rewrite Y. *)
  (*         apply get_call_trace_eq in EV; rewrite EV. reflexivity. *)
  (*         intros. exploit G; eauto. intros. eapply not_ptr_reflect; eauto. *)
  (*   - rewrite H0, H1, H2, H3, H4. *)
  (*     destruct i; inv H4; simpl. reflexivity. *)
  (*   - destruct Val.eq; try congruence; simpl in *. *)
  (*     rewrite STUPD. apply get_return_trace_eq in EV. rewrite EV. *)
  (*     destruct flowsto_dec; simpl; auto. *)
  (*     rewrite RESTORE_SP, PC_RA; eauto. *)
  (*     do 2 destruct Val.eq; try contradiction. simpl. *)
  (*     exploit NO_CROSS_PTR; eauto; intros G. *)
  (*     apply not_ptr_reflect in G; rewrite G. reflexivity. *)
  (*   - admit. *)
  (*   - admit. *)
  (* Admitted. *)

Definition build_initial_state (p: program): option state :=
  let ge := Genv.globalenv p in
  let rs0 :=
    (Pregmap.init Vundef)
      # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
               # SP <- Vnullptr
                        # RA <- Vnullptr in
  do m0 <- Genv.init_mem p;
  Some (State initial_stack rs0 m0 top).

End ExecSem.


Section SECURITY.

Definition asm_in_side (s: split) (lr: side) (p: Asm.program) :=
  List.Forall (fun '(id, gd) =>
                 match gd with
                 | Gfun (Internal f) => s (comp_of f) = lr
                 | _ => True
                 end)
    (prog_defs p).

#[export] Instance asm_has_side: has_side (Asm.program) :=
  { in_side s := fun p δ => asm_in_side s δ p }.

Definition asm_compatible (s: split) (p p': Asm.program) :=
  s |= p ∈ Left /\ s |= p' ∈ Right.

End SECURITY.
