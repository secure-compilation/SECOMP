Require Import String.
Require Import Coqlib Maps Errors Integers.
Require Import AST Globalenvs Linking Smallstep Events Behaviors Memory Values.

Require Import Ctypes Cop Clight.
Require Import Split.

Variant match_fundef (s: split): unit -> fundef -> fundef -> Prop :=
  | match_function_left: forall cp ty cc params vars vars' temps temps' body body',
      s |= cp ∈ Left ->
      match_fundef s tt (Internal {| fn_comp := cp; fn_return := ty; fn_callconv := cc;
                                fn_params := params; fn_vars := vars; fn_temps := temps;
                                fn_body := body |})
                     (Internal {| fn_comp := cp; fn_return := ty; fn_callconv := cc;
                                fn_params := params; fn_vars := vars'; fn_temps := temps';
                                fn_body := body' |})
  | match_external_left: forall ef tys ty cc,
      s |= ef ∈ Left ->
      match_fundef s tt (External ef tys ty cc)
                     (External ef tys ty cc)
  | match_right: forall fd,
      s |= fd ∈ Right ->
      match_fundef s tt fd fd
.

#[local] Instance has_comp_match_fundef (s: split): has_comp_match (match_fundef s).
intros ? x y H.
inv H; auto.
Qed.


Definition match_varinfo (ty1 ty2: type): Prop := ty1 = ty2.

Definition match_prog (s: split) := match_program_gen (match_fundef s) match_varinfo.

Section Equivalence.
  Variable s: split.
  Variable j: meminj.

  Definition same_symbols (ge1 : genv) m1 :=
    let H := Mem.has_side_block in
    forall id loc,
      Genv.find_symbol ge1 id = Some loc ->
      (* AAA: This condition is not present in Genv.same_symbols. This is
         problematic for the invariant below because, together with same_dom, it
         means that the global environment can only have identifiers defined on
         the right. Cf. problem lemma below. *)
      (s, m1) |= loc ∈ Right ->
      j loc = Some (loc, 0).

  Lemma problem (ge1 : genv) m1 id (b : block) :
    let H := Mem.has_side_block in
    Mem.same_domain s j Right m1 ->
    Genv.same_symbols j ge1 ->
    Genv.find_symbol ge1 id = Some b ->
    (s, m1) |= b ∈ Right.
  Proof.
    simpl. intros same_dom same_sym find.
    specialize (same_sym _ _ find).
    assert (def : j b <> None) by congruence.
    now rewrite (same_dom b) in def.
  Qed.

  Record right_mem_injection (ge1 ge2: genv) (m1 m2: mem) :=
    { same_dom: Mem.same_domain s j Right m1;
      (* AAA: Mem.same_domain says that the domain of the memory injection is
         restricted to blocks that belong to the Right side according to
         s. Maybe we should change this name to something else. *)
      partial_mem_inject: Mem.inject j m1 m2;
      j_delta_zero: Mem.delta_zero j;
      same_symb: same_symbols ge1 m1;
      jinjective: Mem.meminj_injective j
      (* related_funct: same_functions j ge1 ge2; *)
      (* same_funct_right: same_functions_right s j ge1 ge2 *)
    }.


Fixpoint remove_until_right (k: cont) :=
  match k with
  | Kstop => Kstop
  | Kseq _ k' | Kloop1 _ _ k'  | Kloop2 _ _ k' | Kswitch k' => remove_until_right k'
  | Kcall id f en le k' =>
      match s (comp_of f) with
      | Right => k
      | Left => remove_until_right k'
      end
  end.

Inductive right_cont_injection: cont -> cont -> Prop :=
| right_cont_injection_kstop: right_cont_injection Kstop Kstop
| right_cont_injection_kseq: forall s k1 k2,
    right_cont_injection k1 k2 ->
    right_cont_injection (Kseq s k1) (Kseq s k2) (* TODO: write other cases *)
| right_cont_injection_kloop1: forall s s' k1 k2,
    right_cont_injection k1 k2 ->
    right_cont_injection (Kloop1 s s' k1) (Kloop1 s s' k2)
| right_cont_injection_kloop2: forall s s' k1 k2,
    right_cont_injection k1 k2 ->
    right_cont_injection (Kloop2 s s' k1) (Kloop2 s s' k2)
| right_cont_injection_kswitch: forall k1 k2,
    right_cont_injection k1 k2 ->
    right_cont_injection (Kswitch k1) (Kswitch k2)
| right_cont_injection_kcall_left: forall id1 id2 f1 f2 en1 en2 le1 le2 k1 k2,
    s |= f1 ∈ Left ->
    s |= f2 ∈ Left ->
    (* s (comp_of f1) = Left -> *)
    (* s (comp_of f2) = Left -> *)
    right_cont_injection (remove_until_right k1) (remove_until_right k2) ->
    right_cont_injection (Kcall id1 f1 en1 le1 k1) (Kcall id2 f2 en2 le2 k2)
(* TODO: is it correct to add [right_cont_injection_kcall_right]? *)
| right_cont_injection_kcall_right: forall id1 id2 f1 f2 en1 en2 le1 le2 k1 k2,
    s |= f1 ∈ Right ->
    s |= f2 ∈ Right ->
    (* s (comp_of f1) = Right -> *)
    (* s (comp_of f2) = Right -> *)
    right_cont_injection k1 k2 ->
    right_cont_injection (Kcall id1 f1 en1 le1 k1) (Kcall id2 f2 en2 le2 k2)
.

Definition right_env_injection_some (e1 e2: env): Prop :=
  forall i b ty,
    e1 ! i = Some (b, ty) ->
    exists b', j b = Some (b', 0%Z) /\
          e2 ! i = Some (b', ty).

Definition right_env_injection_none (e1 e2: env): Prop :=
  forall i,
    e1 ! i = None ->
    e2 ! i = None.

Definition right_env_injection (e1 e2: env): Prop :=
  right_env_injection_some e1 e2 /\ right_env_injection_none e1 e2.

Definition right_tenv_injection (le1 le2: temp_env): Prop :=
  forall i v,
    le1 ! i = Some v ->
    exists v', Val.inject j v v' /\
            le2 ! i = Some v'.


 (* Analogous to: [partialize ctx scs1 = partialize ctx scs2] with
    [ctx] giving us the [Left] part (the program part). Partialize keeps the context part
    and discards the program part.

  [right_state_injection] should relate the context part of the two states, and ignore
  the program part of the two states.
  *)
Variant right_executing_injection (ge1 ge2: genv): state -> state -> Prop :=
| inject_states: forall f s k1 k2 e1 e2 le1 le2 m1 m2,
    (* we forget about program memories but require injection of context memories *)
    right_mem_injection ge1 ge2 m1 m2 ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection k1 k2 ->

    (* the environments satisfy the injection *)
    right_env_injection e1 e2 ->
    right_tenv_injection le1 le2 ->

    right_executing_injection ge1 ge2 (State f s k1 e1 le1 m1) (State f s k2 e2 le2 m2)
| inject_callstates: forall f vs vs' k1 k2 m1 m2,
    (* we forget about program memories but require injection of context memories *)
    right_mem_injection ge1 ge2 m1 m2 ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection k1 k2 ->

    (* the parameters are related by the memory injection *)
    Val.inject_list j vs vs' ->

    right_executing_injection ge1 ge2 (Callstate f vs k1 m1) (Callstate f vs' k2 m2)
| inject_returnstates: forall v v' k1 k2 m1 m2 ty cp,
    (* we forget about program memories but require injection of context memories *)
    right_mem_injection ge1 ge2 m1 m2 ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection k1 k2 ->

    (* The return values are related by the injection *)
    Val.inject j v v' ->

    right_executing_injection ge1 ge2 (Returnstate v k1 m1 ty cp) (Returnstate v' k2 m2 ty cp)
.

#[export] Instance state_has_side: has_side state :=
    { in_side s := fun st δ =>
                     match st with
                     | State f _ _ _ _ _ => s |= f ∈ δ
                     | Callstate fd _ _ _ => s |= fd ∈ δ (* Should this be the compartment that's on top of the stack instead? *)
                     | Returnstate _ _ _ _ cp => s |= cp ∈ δ
                     end
    }.

Definition memory_of (st: state): mem :=
  match st with
  | State _ _ _ _ _ m | Callstate _ _ _ m
  | Returnstate _ _ m _ _ => m
  end.

Definition cont_of (st: state): cont :=
  match st with
  | State _ _ k _ _ _ | Callstate _ _ k _
  | Returnstate _ k _ _ _ => k
  end.

Variant right_state_injection (ge1 ge2: genv): state -> state -> Prop :=
| LeftControl: forall st1 st2,
    (* program (left) has control *)
    s |= st1 ∈ Left ->
    s |= st2 ∈ Left ->

    (* we forget about program memories but require injection of context memories *)
    right_mem_injection ge1 ge2 (memory_of st1) (memory_of st2) ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection (cont_of st1) (cont_of st2) ->

    right_state_injection ge1 ge2 st1 st2
| RightControl: forall st1 st2,
    (* context (right) has control *)
    s |= st1 ∈ Right ->
    s |= st2 ∈ Right ->
    right_executing_injection ge1 ge2 st1 st2 ->
    right_state_injection ge1 ge2 st1 st2.


End Equivalence.

Section Simulation.
  Context (c p1 p2: Clight.program).
  Variable s: split.

  Context (W1 W2: Clight.program).
  Hypothesis c_p1: link p1 c = Some W1.
  Hypothesis c_p2: link p2 c = Some W2.

  Hypothesis match_W1_W2: match_prog s tt W1 W2.

  (* Context (ge1 ge2: genv). *)
  Let ge1 := globalenv W1.
  Let ge2 := globalenv W2.
  (* Is this hypothesis realistic? *)
  Hypothesis same_cenv: genv_cenv ge1 = genv_cenv ge2.


  (* AAA: Right now, this statement is forcing every global identifier id that
     occurs in an expression to refer to a function or variable that is defined
     on the right.  This is because, when you evaluate an lvalue, you get
     something that is defined in the memory injection j.  Here are possible
     solutions:

     1. Modify the second implication so that, if we evaluate an lvalue that is
     not defined in the memory injection j (and, therefore, is on the Left),
     then this lvalue must be either a global function or variable.  The problem
     with this is that we would probably have to extend this to an invariant on
     memories: every pointer to a non-global-function-or-variable that is stored
     in Right memory must point to the Right. And this sounds complicated to
     reason about.

     2. Change the second implication so that we do not care if we get a
     non-global-function-or-variable pointer that is on the left.

   *)
  Lemma eval_expr_lvalue_injection:
    forall s j m1 m2 e1 e2 le1 le2 cp,
    forall inj: right_mem_injection s j ge1 ge2 m1 m2,
    forall env_inj: right_env_injection j e1 e2,
    forall lenv_inj: right_tenv_injection j le1 le2,
    (forall a v,
      eval_expr ge1 e1 cp le1 m1 a v ->
      (* forall loc ofs (EQv: v = Vptr loc ofs), *)
      exists v', Val.inject j v v' /\
                   eval_expr ge2 e2 cp le2 m2 a v')
    /\
    (forall a loc ofs bf,
      eval_lvalue ge1 e1 cp le1 m1 a loc ofs bf ->
      exists loc' ofs',
        j loc = Some (loc', ofs') /\
        eval_lvalue ge2 e2 cp le2 m2 a loc' (Ptrofs.add ofs (Ptrofs.repr ofs')) bf).
  Proof.
    intros. subst ge1 ge2.
    destruct inj as [inj_dom inj_inject j_delta_zero same_symb].
    apply eval_expr_lvalue_ind; intros;
    try now match goal with
    | |- exists _, Val.inject _ (Vint _) _ /\ _ => eexists; split; [eapply Val.inject_int | econstructor; eauto]
    | |- exists _, Val.inject _ (Vfloat _) _ /\ _ => eexists; split; [eapply Val.inject_float | econstructor; eauto]
    | |- exists _, Val.inject _ (Vsingle _) _ /\ _ => eexists; split; [eapply Val.inject_single | econstructor; eauto]
    | |- exists _, Val.inject _ (Vlong _) _ /\ _ => eexists; split; [eapply Val.inject_long | econstructor; eauto]
    end.
    - exploit lenv_inj; eauto. intros [loc' [? ?]].
      eexists; split; eauto.
      constructor; auto.
    - destruct H0 as [loc' [ofs' [? ?]]].
      eexists; split; eauto.
      econstructor; eauto.
    - destruct H0 as [v' [? ?]].
      exploit sem_unary_operation_inject; eauto.
      intros [? [? ?]].
      eexists; split; eauto.
      econstructor; eauto.
    - destruct H0 as [v1' [? ?]].
      destruct H2 as [v2' [? ?]].
      exploit sem_binary_operation_inject; eauto.
      rewrite same_cenv.
      intros [? [? ?]].
      eexists; split; eauto.
      econstructor; eauto.
    - destruct H0 as [v' [? ?]].
      exploit sem_cast_inject; eauto.
      intros [v1' [? ?]].
      eexists; split; eauto.
      econstructor; eauto.
    - rewrite same_cenv.
      eexists; split; eauto.
      econstructor; eauto.
    - rewrite same_cenv.
      eexists; split; eauto.
      econstructor; eauto.
    - destruct H0 as [loc' [ofs' [? ?]]].
      (* This assert heavily relies on the assumption that the injection always gives a delta = 0. *)
      assert (G: exists v', Val.inject j v v' /\
                         deref_loc cp (typeof a) m2 loc' (Ptrofs.add ofs (Ptrofs.repr ofs')) bf v').
      { inv H1.
        - simpl in *.
          exploit Mem.load_inject; eauto.
          intros [v' [? ?]].
          exploit j_delta_zero; eauto; intros; subst. rewrite Z.add_0_r in H1. rewrite Ptrofs.add_zero.
          eexists; split; eauto. econstructor; simpl; eauto.
        - exists (Vptr loc' (Ptrofs.add ofs (Ptrofs.repr ofs'))). split; eauto.
          eapply deref_loc_reference; eauto.
        - exists (Vptr loc' (Ptrofs.add ofs (Ptrofs.repr ofs'))). split; eauto.
          eapply deref_loc_copy; eauto.
        - inv H3.
          exploit Mem.load_inject; eauto.
          intros [v' [? ?]].
          exploit j_delta_zero; eauto; intros; subst. rewrite Z.add_0_r in H3; rewrite Ptrofs.add_zero.
          eexists; split; eauto.
          eapply deref_loc_bitfield. inv H7.
          econstructor; eauto. }
      destruct G as [v' [? ?]].
      eexists; split; eauto.
      econstructor; eauto.
    - destruct env_inj as [env_inj _].
      exploit env_inj; eauto.
      intros [b' [? ?]].
      eexists; eexists; split; eauto.
      econstructor; eauto.
    - destruct env_inj as [_ env_inj].
      exploit env_inj; eauto.
      intros ?.
      exploit same_symb; eauto.
      eapply Genv.find_symbol_match in match_W1_W2. rewrite <- match_W1_W2 in H0.
      eexists; eexists; split; eauto.
      eapply eval_Evar_global; eauto.
    - destruct H0 as [v' [? ?]].
      inv H0.
      eexists; eexists; split; eauto.
      econstructor; eauto.
    - destruct H0 as [v' [? ?]].
      inv H0.
      eexists; eexists; split; eauto.
      rewrite Ptrofs.add_assoc, (Ptrofs.add_commut (Ptrofs.repr delta)), <- Ptrofs.add_assoc.
      eapply eval_Efield_struct; try rewrite <- same_cenv; eauto.
    - destruct H0 as [v' [? ?]].
      inv H0.
      eexists; eexists; split; eauto.
      rewrite Ptrofs.add_assoc, (Ptrofs.add_commut (Ptrofs.repr delta)), <- Ptrofs.add_assoc.
      eapply eval_Efield_union; try rewrite <- same_cenv; eauto.
  Qed.

  Lemma eval_expr_injection:
    forall s j m1 m2 e1 e2 le1 le2 cp,
    forall inj: right_mem_injection s j ge1 ge2 m1 m2,
    forall env_inj: right_env_injection j e1 e2,
    forall lenv_inj: right_tenv_injection j le1 le2,
    forall a v,
      eval_expr ge1 e1 cp le1 m1 a v ->
      exists v', Val.inject j v v' /\
                     eval_expr ge2 e2 cp le2 m2 a v'.
    Proof.
      intros.
      exploit eval_expr_lvalue_injection; eauto.
      intros [? _]. eauto.
    Qed.

  Lemma eval_exprlist_injection:
    forall s j m1 m2 e1 e2 le1 le2 cp,
    forall inj: right_mem_injection s j ge1 ge2 m1 m2,
    forall env_inj: right_env_injection j e1 e2,
    forall lenv_inj: right_tenv_injection j le1 le2,
    forall al tys vs,
      eval_exprlist ge1 e1 cp le1 m1 al tys vs ->
      exists vs', Val.inject_list j vs vs' /\
              eval_exprlist ge2 e2 cp le2 m2 al tys vs'.
    Proof.
      intros.
      induction H.
      - exists nil; split; eauto. constructor.
      - destruct IHeval_exprlist as [vs' [? ?]].
        exploit eval_expr_injection; eauto.
        intros [v' [? ?]].
        destruct inj.
        exploit sem_cast_inject; eauto.
        intros [tv [? ?]].
        exists (tv :: vs'). split. constructor; eauto.
        econstructor; eauto.
    Qed.

  Lemma eval_lvalue_injection:
    forall s j m1 m2 e1 e2 le1 le2 cp,
    forall inj: right_mem_injection s j ge1 ge2 m1 m2,
    forall env_inj: right_env_injection j e1 e2,
    forall lenv_inj: right_tenv_injection j le1 le2,
    forall a loc ofs bf,
      eval_lvalue ge1 e1 cp le1 m1 a loc ofs bf ->
      exists loc' ofs', j loc = Some (loc', ofs') /\
                     eval_lvalue ge2 e2 cp le2 m2 a loc' (Ptrofs.add ofs (Ptrofs.repr ofs')) bf.
  Proof.
    intros.
    exploit eval_expr_lvalue_injection; eauto.
    intros [_ ?]. eauto.
  Qed.

  Ltac destruct_mem_inj :=
    match goal with
    | H: right_mem_injection _ _ _ _ _ _ |- _ => destruct H as [same_dom mem_inject delta_zero same_symb injective]
    end.

  Lemma parallel_concrete: forall j s1 s2 s1' t,
      right_state_injection s j ge1 ge2 s1 s2 ->
      s |= s1 ∈ Right ->
      Clight.step1 ge1 s1 t s1' ->
      exists j' s2',
        Clight.step1 ge2 s2 t s2' /\
          right_state_injection s j' ge1 ge2 s1' s2'.
  Proof.
    intros j s1 s2 s1' t rs_inj is_r step1.
    destruct rs_inj as [? | st1 st2 is_r1 is_r2 right_exec_inj].
    { (* contradiction *)
      destruct st1; simpl in *; congruence. }
    inv step1; inv right_exec_inj.
    + (* step_assign *)
      exploit eval_lvalue_injection; eauto.
      exploit eval_expr_injection; eauto.
      intros [v' [? ?]] [loc' [ofs' [? ?]]].
      destruct_mem_inj.
      exploit sem_cast_inject; eauto.
      intros [tv [? ?]].
      inv H2.
      * exploit Mem.store_mapped_inject; eauto.
        intros [? [? ?]].
        exploit delta_zero; eauto. intros ?; subst.
        rewrite Z.add_0_r in *.
        exists j; eexists; split.
        - econstructor; eauto.
          econstructor; eauto.
          rewrite Ptrofs.add_zero; eauto.
        - apply RightControl; eauto.
          constructor; eauto.
          split; eauto.
          clear -same_dom H10.
          unfold Mem.same_domain in *.
          intros.
          unfold in_side in *; simpl in *.
          erewrite Mem.store_block_compartment; eauto.
      * inv H8.
        exploit Mem.loadbytes_inj; eauto using Mem.mi_inj.
        intros [? [? ?]].
        exploit Mem.storebytes_mapped_inject; eauto using Mem.mi_inj.
        intros [? [? ?]].
        exploit delta_zero; eauto; intros; subst.
        exploit (delta_zero loc); eauto; intros; subst.
        exists j; eexists; split.
        - econstructor; eauto.
          rewrite <- same_cenv, !Z.add_0_r, !Ptrofs.add_zero in *; eauto.
          eapply assign_loc_copy; eauto.
          { destruct H15.
            - exploit injective; eauto. intros []; [now left| contradiction].
            - auto. }
        - apply RightControl; eauto.
          constructor; eauto.
          split; eauto.
          clear -same_dom H17.
          unfold Mem.same_domain in *.
          intros.
          unfold in_side in *; simpl in *.
          erewrite Mem.storebytes_block_compartment; eauto.
      * inv H9.
        exploit Mem.load_inject; eauto using Mem.mi_inj.
        intros [? [? ?]].
        exploit Mem.store_mapped_inject; eauto.
        intros [? [? ?]].
        inv H16.
        exploit delta_zero; eauto; intros; subst.
        rewrite Z.add_0_r in *.
        exists j; eexists; split.
        - econstructor; eauto.
          rewrite Ptrofs.add_zero.
          eapply assign_loc_bitfield. rewrite <- H2. inv H8.
          econstructor; eauto.
        - apply RightControl; eauto.
          constructor; eauto.
          split; eauto.
          clear -same_dom H18.
          unfold Mem.same_domain in *.
          intros.
          unfold in_side in *; simpl in *.
          erewrite Mem.store_block_compartment; eauto.
    + (* step_set *)
      exploit eval_expr_injection; eauto.
      intros [v' [? ?]].
      exists j; eexists; split.
      * econstructor; eauto.
      * apply RightControl; eauto.
        constructor; eauto.
        unfold right_tenv_injection in *.
        intros; rewrite PTree.gsspec in *.
        destruct (peq i id); eauto. inv H2; subst.
        eexists; split; eauto.
    + (* step_call *)
      exploit eval_expr_injection; eauto.
      intros [v' [? ?]].
      exploit eval_exprlist_injection; eauto.
      intros [vs' [? ?]].
      exploit (Genv.find_funct_match match_W1_W2); eauto.
      intros [? [fd' [find_fd' [match_fd' _]]]].
      assert (vf = v') by admit. subst v'.
      exists j; eexists; split.
      * econstructor; eauto.
        - inv match_fd'; eauto.
        - exploit (Genv.match_genvs_allowed_calls match_W1_W2); eauto.
        - eapply (Genv.match_genvs_not_ptr_list_inj); eauto.
          exploit (Genv.match_genvs_find_comp match_W1_W2); eauto. intros <-.
          erewrite <- (Genv.match_genvs_type_of_call); eauto.
        - exploit (Genv.match_genvs_find_comp match_W1_W2); eauto. intros <-.
          exploit (@call_trace_inj _ _ _ _ ge1 ge2); eauto.
          unfold ge2, ge1. simpl. apply Genv.globalenvs_match in match_W1_W2.
          intros sy. pose proof (Genv.mge_symb match_W1_W2 sy). unfold Genv.find_symbol; eauto.
      * (* Case analysis: are we changing side or not? *)
        destruct (s (comp_of fd)) eqn:side.
        - apply LeftControl; eauto; try now inv match_fd'; auto.
          simpl. apply right_cont_injection_kcall_right; eauto.
        - inv match_fd'; unfold in_side in *; simpl in *;
            unfold comp_of in *; simpl in side; unfold comp_of in *; simpl in side;
            try congruence.
          apply RightControl; eauto.
          constructor; eauto.
          simpl. apply right_cont_injection_kcall_right; eauto.
    + (* step_builtin *)
      exploit eval_exprlist_injection; eauto.
      intros [vs' [? ?]].
      exploit ec_mem_inject; eauto. admit. admit. admit.
      intros [j' [? [? [? [? [? [? [? [? ?]]]]]]]]].
      exists j'; eexists; split.
      econstructor; eauto.
      apply RightControl; eauto.
      constructor; eauto.
      * constructor; eauto.
        - admit.
        - admit.
        - admit.
        - admit.
      * destruct H10.
        split. intros ? ? ? ?.
        exploit H10; eauto. intros [b' [? ?]].
        exists b'; split; eauto.
        intros ? ?.
        exploit H14; eauto.
      * intros ? ? ?.
        destruct optid.
        - simpl in *. rewrite PTree.gsspec in *.
          destruct (peq i i0); subst.
          inv H14. eexists; split; eauto.
          exploit H11; eauto. intros [? [? ?]]; eauto.
        - exploit H11; eauto. intros [? [? ?]]; eauto.
    + (* step_seq*)
      exists j; eexists; split; [constructor | apply RightControl]; auto.
      constructor; auto. constructor; auto.
    + (* step_skip_seq *)
      inv H7.
      exists j; eexists; split; [constructor | apply RightControl]; auto.
      constructor; auto.
    + (* step_continue_seq *)
      inv H7.
      exists j; eexists; split; [constructor | apply RightControl]; auto.
      constructor; auto.
    + (* step_break_seq *)
      inv H7.
      exists j; eexists; split; [constructor | apply RightControl]; auto.
      constructor; auto.
    + (* step_ifthenelse *)
      exploit eval_expr_injection; eauto.
      intros [v' [? ?]].
      destruct_mem_inj.
      exploit bool_val_inject; eauto. intros ?.
      exists j; eexists; split; [econstructor | apply RightControl]; eauto.
      constructor; auto. constructor; auto.
    + (* step_loop *)
      exists j; eexists; split; [econstructor | apply RightControl]; eauto.
      constructor; auto. constructor; auto.
    + (* step_skip_or_continue_loop1 *)
      inv H8. exists j; eexists; split; [constructor | apply RightControl]; eauto.
      constructor; auto. constructor; auto.
    + (* step_break_loop1 *)
      inv H7. exists j; eexists; split; [apply step_break_loop1 | apply RightControl]; eauto.
      constructor; auto.
    + (* step_skip_loop2 *)
      inv H7. exists j; eexists; split; [apply step_skip_loop2 | apply RightControl]; eauto.
      constructor; auto.
    + (* step_break_loop2 *)
      inv H7. exists j; eexists; split; [apply step_break_loop2 | apply RightControl]; eauto.
      constructor; auto.
    + (* step_return_0 *)
      admit.
    + (* step_return_1 *)
      admit.
    + (* step_skip_call *)
      admit.
    + (* step_switch *)
      exploit eval_expr_injection; eauto.
      intros [v' [? ?]].
      assert (sem_switch_arg v (typeof a) = Some n -> sem_switch_arg v' (typeof a) = Some n).
      { intros. unfold sem_switch_arg in *.
        destruct (classify_switch (typeof a)); simpl in *; try easy; inv H1; try easy. }
      exists j; eexists; split; [econstructor | apply RightControl]; eauto.
      constructor; auto.
      constructor; auto.
    + (* step_break_switch *)
      inv H8. exists j; eexists; split; [constructor | apply RightControl]; eauto.
      constructor; auto.
    + (* step_continue_switch *)
      inv H7. exists j; eexists; split; [apply step_continue_switch | apply RightControl]; eauto.
      constructor; auto.
    + (* step_label *)
      exists j; eexists; split; [constructor | apply RightControl]; auto.
      constructor; auto.
    + (* step_goto *)
      admit.
    + (* step_internal_function *)
      admit.
    + (* step_external_function *)
      admit.
    + (* step_returnstate *)
      admit.
  Admitted.


    (* Example that shows why Blame doesn't hold in the C semantics.
       Because the semantics are not determinate we can end up in situation like this one:


    int f();
    int x;

    int main() {
      int a[2];
      a[0] = (x = 0) + f();
      if x { a[5] = 42; }
      else { }
    }

    (* 2 executions *)
    (* We know that f(y) produces the same trace. Can the value of x change? *)
    (* Let's say f() does x = 1 - x *)

    (* execution 1: assignment first: x = 1 we take the if branch *)
    (* execution 2: call first:       x = 0 we take the else branch *)
    *)


  Lemma parallel_concrete_E0: forall s1 s2 s1' s2' t,
      right_state_injection s j s1 s2 ->
      is_right s s1 -> (* in the context *)
      Csem.step ge1 s1 E0 s1' ->
      Csem.step ge2 s2 t s2' ->
      t = E0 /\ right_state_injection s j s1' s2'.
    Proof.
      intros.
      exploit parallel_concrete; eauto.
      intros [? [? ?]].
      assert (t = E0 /\ s2' = x).
      { clear -H2 H3.
        inv H2; inv H3.
        - admit.
        - inv H; inv H0; eauto.
      }
      (* rely on determinacy lemma with empty traces? *)
  Admitted.

  Lemma parallel_abstract_E0: forall s1 s2 s1' s2',
      right_state_injection s j s1 s2 ->
      is_left s s1 ->
      Csem.step ge1 s1 E0 s1' ->
      Csem.step ge2 s2 E0 s2' ->
      right_state_injection s j s1' s2'.
    Proof.
      intros s1 s2 s1' t rs_inj is_l step1.
      inv rs_inj.
      - admit.
      - admit. (* contradiction *)
  Admitted.

  Lemma parallel_abstract_t: forall s1 s2 s1' s2' t,
      right_state_injection s j s1 s2 ->
      is_left s s1 ->
      Csem.step ge1 s1 t s1' ->
      Csem.step ge2 s2 t s2' ->
      right_state_injection s j s1' s2'.

Lemma parallel_concrete p1 p2 scs1 scs2:
  left_side s p1 -> (* use definitions from RSC.v *)
  left_side s p2 -> (* use definitions from RSC.v *)
  partial_state_equivalent s scs1 scs2 -> (* to define --> using memory injections? *)
  pc_in_left_part scs1 -> (* to define *)
  CS.kstep (prepare_global_env (program_link p p1)) scs1 t scs1' -> (* use step of Csem instead *)
  exists2 scs2',
    CS.kstep (prepare_global_env (program_link p p2)) scs2 t scs2' /\ (* use step of Csem instead *)
      partial_state_equivalent s scs1' scs2'. (* to define *)
