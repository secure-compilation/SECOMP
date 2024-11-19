Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions.


Section PRESERVATION.
Variable return_address_offset: Mach.function -> Mach.code -> ptrofs -> Prop.

Lemma instr_dec: forall (i i': instruction),
    {i = i'} + {i <> i'}.
Proof.
  decide equality; subst; auto using mreg_eq, typ_eq, Ptrofs.eq_dec, eq_operation,
    eq_addressing, chunk_eq, signature_eq, external_function_eq, eq_condition;
    try now (decide equality; subst; auto using mreg_eq, ident_eq).
  decide equality.
  decide equality; subst;
    auto using mreg_eq, Int.eq_dec, Int64.eq_dec,
    Float.eq_dec, Float32.eq_dec, Ptrofs.eq_dec,
    chunk_eq, ident_eq.
Defined.

Lemma code_dec: forall (c c': code),
    {c = c'} + {c <> c'}.
Proof.
  decide equality; eauto using instr_dec.
Qed.

Lemma is_tail_dec: forall f c,
    {is_tail c (fn_code f)} + {~ is_tail c (fn_code f)}.
Proof.
  intros f c.
  generalize (fn_code f) as code. clear f.
  induction code.
  - destruct c.
    + left; econstructor.
    + right; intros A; inv A.
  - destruct IHcode.
    + left. constructor. assumption.
    + destruct (code_dec c (a :: code)).
      * subst; left; constructor.
      * right. intros A. inv A; eauto.
Defined.

Hypothesis return_address_offset_exists:
  forall f sg ros c,
  is_tail (Mcall sg ros :: c) (fn_code f) ->
  exists ofs, return_address_offset f c ofs.

Hypothesis return_address_offset_determinate:
  forall f c ofs1 ofs2,
    is_tail c (fn_code f) ->
    return_address_offset f c ofs1 ->
    return_address_offset f c ofs2 ->
    Ptrofs.unsigned ofs1 = Ptrofs.unsigned ofs2.

Variable prog: program.
Let ge := Genv.globalenv prog.

Remark extcall_arguments_determ:
  forall rs sp m sg args1 args2,
  extcall_arguments rs m sp sg args1 -> extcall_arguments rs m sp sg args2 -> args1 = args2. Proof.
  intros until m.
  assert (A: forall l v1 v2,
             extcall_arg rs m sp l v1 -> extcall_arg rs m sp l v2 -> v1 = v2).
  { intros. inv H; inv H0. congruence.
    destruct sp; try discriminate.
    simpl in H1, H4.
    apply Mem.load_result in H1.
    apply Mem.load_result in H4. congruence. }
  assert (B: forall p v1 v2,
             extcall_arg_pair rs m sp p v1 -> extcall_arg_pair rs m sp p v2 -> v1 = v2).
  { intros. inv H; inv H0.
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs m sp) ll vl1 ->
             forall vl2, list_forall2 (extcall_arg_pair rs m sp) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

Remark call_arguments_determ:
  forall rs sp m sg args1 args2,
  call_arguments rs m sp sg args1 -> call_arguments rs m sp sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             call_arg rs m sp l v1 -> call_arg rs m sp l v2 -> v1 = v2).
  { intros. inv H; inv H0. congruence.
    destruct sp; try discriminate.
    unfold load_stack in *.
    simpl in H1, H4.
    apply Mem.load_result in H1.
    apply Mem.load_result in H4. congruence. }
  assert (B: forall p v1 v2,
             call_arg_pair rs m sp p v1 -> call_arg_pair rs m sp p v2 -> v1 = v2).
  { intros. inv H; inv H0.
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (call_arg_pair rs m sp) ll vl1 ->
             forall vl2, list_forall2 (call_arg_pair rs m sp) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

Lemma semantics_determinate: determinate (semantics return_address_offset prog).
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
  + split. constructor. auto.
  + split. constructor. auto.
  + split. constructor. auto.
  + split. constructor. auto.
  + split. constructor. auto.
  + split. constructor. auto.
  + split. constructor.

    assert (ra0 = ra) as ->.
    { exploit return_address_offset_determinate. eauto. exact H15. exact H3.
      intros ?.
      assert (Ptrofs.repr (Ptrofs.unsigned ra0) = Ptrofs.repr (Ptrofs.unsigned ra)).
      { rewrite H; auto. }
      do 2 rewrite Ptrofs.repr_unsigned in H0. auto. }

    (* assert (args0 = args) by (eapply call_arguments_determ; eauto). subst. *)
    auto.
  + congruence.
  + congruence.
  +
    assert (ra0 = ra) as ->.
    { exploit return_address_offset_determinate. eauto. exact H15. exact H3.
      intros ?.
      assert (Ptrofs.repr (Ptrofs.unsigned ra0) = Ptrofs.repr (Ptrofs.unsigned ra)).
      { rewrite H; auto. }
      do 2 rewrite Ptrofs.repr_unsigned in H0. auto. }
    assert (args0 = args) by (eapply call_arguments_determ; eauto). subst.
    destruct fd0.
    { destruct Mem.alloc; destruct Mem.alloc; destruct sp.
      * destruct allc as (A & B & C), allc0 as (A' & B' & C'); subst.
        split; auto.
        inv EV; inv EV0; try congruence.
        constructor. Equalities.
        assert (vl0 = vl) by (eapply eventval_list_match_determ_2; eauto). subst.
        eapply match_traces_call.
      * destruct allc as (A & B & C), allc0 as (A' & B' & C'); subst.
        split; auto.
        inv EV; inv EV0; try congruence.
        constructor. Equalities.
        assert (vl0 = vl) by (eapply eventval_list_match_determ_2; eauto). subst.
        eapply match_traces_call.
      * destruct allc as (A & B & C), allc0 as (A' & B' & C'); subst.
        split; auto.
        inv EV; inv EV0; try congruence.
        constructor. Equalities.
        assert (vl0 = vl) by (eapply eventval_list_match_determ_2; eauto). subst.
        eapply match_traces_call.
      * destruct allc as (A & B & C), allc0 as (A' & B' & C'); subst.
        split; auto.
        inv EV; inv EV0; try congruence.
        constructor. Equalities.
        assert (vl0 = vl) by (eapply eventval_list_match_determ_2; eauto). subst.
        eapply match_traces_call.
      * destruct allc as (A & B & C), allc0 as (A' & B' & C'); subst.
        split; auto.
        inv EV; inv EV0; try congruence.
        constructor. Equalities.
        assert (vl0 = vl) by (eapply eventval_list_match_determ_2; eauto). subst.
        eapply match_traces_call.
      * destruct Mem.set_perm; try contradiction.
        destruct allc as (A & B & C), allc0 as (A' & B' & C'); subst.
        split; auto.
        inv EV; inv EV0; try congruence.
        constructor. Equalities.
        assert (vl0 = vl) by (eapply eventval_list_match_determ_2; eauto). subst.
        eapply match_traces_call. }
    { destruct allc as (A & B & C), allc0 as (A' & B' & C'); subst.
      split; auto.
      inv EV; inv EV0; try congruence.
      constructor. Equalities.
      assert (vl0 = vl) by (eapply eventval_list_match_determ_2; eauto). subst.
      eapply match_traces_call. }
  + split. constructor. auto.
  + assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst.
    exploit external_call_determ. eexact H2. eexact H14. intros [A B].
    split. auto. intros. destruct B; auto. subst. auto.
  + split. constructor. auto.
  + split. constructor. auto.
  + split. constructor. auto.
  + split. constructor. auto.
  + split. constructor. auto.
  + split. constructor.
    subst sp sp0. Equalities. auto.
  + assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst.
    exploit external_call_determ. eexact H3. eexact H13. intros [A B].
    split. auto. intros. destruct B; auto. subst. auto.
  + destruct dsp.
    destruct sp; try contradiction.
    destruct cp_eq_dec.
    * subst. inv EV; inv EV0; try congruence.
      split. constructor. auto.
      assert (res = res0) as <- by (eapply eventval_match_determ_2; eauto).
      split. constructor. auto.
    * destruct Mem.set_perm; try congruence.
      inv SET_PERM; inv SET_PERM0.
      inv EV; inv EV0; try congruence.
      split. constructor. auto.
      assert (res = res0) as <- by (eapply eventval_match_determ_2; eauto).
      split. constructor. auto.
    * inv EV; inv EV0; try congruence.
      split. constructor. auto.
      assert (res = res0) as <- by (eapply eventval_match_determ_2; eauto).
      split. constructor. auto.
- (* trace length *)
  red; intros. inv H; simpl; try lia.
  inv EV; auto.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
  inv EV; auto.
- (* initial states *)
  inv H; inv H0. subst ge0 ge1. f_equal.
  congruence.
  congruence.
- (* final no step *)
  inv H.
  red; intros; red; intros.
  inv H.
- (* final states *)
  inv H; inv H0. congruence.
Qed.

Variant mergeable: state -> Prop :=
  | mergeable_call_int:
    forall (s : list stackframe) (fb : block) (sp : val) (sig : signature)
      (ros : mreg + ident) (c : code) (rs : regset) (m : mem)
      (f : function) (f' : block) (* (ra : ptrofs) *)
      ef,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      (* return_address_offset f c ra -> *)
      is_tail (Mcall sig ros :: c) (fn_code f) ->
      bottom = comp_of f ->
      sig = ef_sig ef ->

      Genv.find_funct_ptr ge f' = Some (External ef) ->
      mergeable (State s fb sp (Mcall sig ros :: c) rs m)
  | mergeable_call_cross:
    forall (s : list stackframe) (fb : block) (sp : val)
      (sig : signature) (ros : mreg + ident) (c : code)
      (rs : regset) (m : mem) (f : function) (f' : block)
      (args : list val)
      (m_res : Mem.mem') ef,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      is_tail (Mcall sig ros :: c) (fn_code f) ->
      (* return_address_offset f c ra -> *)
      Genv.find_funct_ptr ge f' = Some (External ef) ->
      Genv.allowed_call ge (comp_of f) (Vptr f' Ptrofs.zero) ->
      comp_of f <> bottom ->
      call_arguments (undef_regs destroyed_at_function_entry rs) m sp sig args ->
      (Genv.type_of_call (comp_of f) bottom = Genv.CrossCompartmentCall ->
       Forall not_ptr args) ->
      sig = ef_sig ef ->
      call_trace ge (comp_of f) bottom (Vptr f' Ptrofs.zero) args
        (sig_args sig) E0 ->
      (* (let (m', dummy_ra) := Mem.alloc m bottom 0 0 in *)
      (*  let (m'', dummy_sp) := Mem.alloc m' bottom 0 0 in *)
      (*  match sp with *)
      (*  | Vptr bsp _ => *)
      (*      match Mem.set_perm m'' bsp Readable with *)
      (*      | Some m''' => m_res = m''' /\ dra = Some dummy_ra /\ dsp = Some dummy_sp *)
      (*      | None => False *)
      (*      end *)
      (*  | _ => m_res = m'' /\ dra = Some dummy_ra /\ dsp = Some dummy_sp *)
      (*  end) -> *)
      mergeable (State s fb sp (Mcall sig ros :: c) rs m).

Lemma mergeable_dec: forall s, {mergeable s} + {not (mergeable s)}.
Proof.
  intros s.
  destruct s; try now right.
  destruct c as [|[] ?]; try now right.
  destruct (find_function_ptr ge s0 rs) eqn:?.
  destruct (Genv.find_funct_ptr ge b) as [[fd | ef]|] eqn:?.
  - right. intros A; inv A; congruence.
  - destruct (Genv.find_funct_ptr ge f) as [[fi | ?]|] eqn:?.
    + destruct (cp_eq_dec (comp_of fi) bottom) as [cp_f_bottom | cp_f_not_bottom].
      * destruct (signature_eq s (ef_sig ef)).
        -- destruct (is_tail_dec fi (Mcall s s0 :: c)).
           ++ left. econstructor; eauto.
           ++ right. intros A; inv A; congruence.
        -- right. intros A; inv A; congruence.
      * destruct (Genv.allowed_call_b ge (comp_of fi) (Vptr b Ptrofs.zero)) eqn:allowed.
        -- eapply Genv.allowed_call_reflect in allowed.
           destruct (get_call_arguments (undef_regs destroyed_at_function_entry rs) sp m s) as [args|] eqn:get_args.
           ++ eapply call_arguments_equiv in get_args.
              destruct (signature_eq s (ef_sig ef));
                destruct (is_tail_dec fi (Mcall s s0 :: c)).
              **
                (* destruct (Mem.alloc m bottom 0 0) as [m' dummy_ra] eqn:alloc. *)
                (*  destruct (Mem.alloc m' bottom 0 0) as [m'' dummy_sp] eqn:alloc'. *)
                 assert (Genv.type_of_call (comp_of fi) bottom = Genv.CrossCompartmentCall -> Forall not_ptr args).
                 { simpl. destruct flowsto_dec; try congruence.
                   exfalso; apply n; auto with comps. }
                 assert (call_trace ge (comp_of fi) bottom (Vptr b Ptrofs.zero) args (sig_args s) nil).
                 { constructor. simpl. destruct flowsto_dec; try congruence.
                   exfalso; apply n; auto with comps. }
                 (* destruct sp; *)
                 (*   try now (left; eapply mergeable_call_cross; eauto; rewrite alloc, alloc'; eauto). *)
                 (* destruct (Mem.set_perm m'' b0 Readable) as [m''' |] eqn:set. *)
                 { left; eapply mergeable_call_cross; eauto. }
              ** right. intros A; inv A; congruence.
              ** right. intros A; inv A; congruence.
              ** right. intros A; inv A; congruence.
           ++ right. intros A; inv A; [congruence|].
              eapply call_arguments_equiv in H13; congruence.
        -- right. intros A; inv A; [congruence|].
           apply Genv.allowed_call_reflect in H11. congruence.
    + right. intros A; inv A; congruence.
    + right. intros A; inv A; congruence.
  - right. intros A; inv A; congruence.
  - right. intros A; inv A; congruence.
Defined.

Lemma mergeable_safe: forall s,
  mergeable s -> exists s', step return_address_offset ge s E0 s' /\ not (mergeable s').
Proof.
  intros s ?. inv H.
  - exploit (return_address_offset_exists f (ef_sig ef) ros c); eauto.
    intros [? ?].
    eexists; split; [eapply exec_Mcall_int; eauto|].
    eapply is_tail_cons_left; eauto.
    intros A; inv A.
  - exploit (return_address_offset_exists f (ef_sig ef) ros c); eauto.
    intros [? ?].
    eexists; split; [eapply exec_Mcall_cross; eauto|].
    eapply is_tail_cons_left; eauto. simpl; (split; [| split]); reflexivity.
    intros A; inv A.
Qed.

Lemma mergeable_step_not_final: forall s s' t,
    mergeable s ->
    step return_address_offset ge s t s' ->
    forall n, not (final_state s' n).
Proof.
  intros. intros A; inv A; inv H; inv H0.
Qed.

Definition merged_semantics := mergedL (semantics return_address_offset prog) mergeable.

Theorem forward_simulation_merged:
  forward_simulation (semantics return_address_offset prog) merged_semantics.
Proof.
  apply forward_simulation_merged; eauto.
  eapply semantics_determinate.
  eapply mergeable_dec.
  eapply mergeable_safe.
  eapply mergeable_step_not_final.
Qed.

End PRESERVATION.
