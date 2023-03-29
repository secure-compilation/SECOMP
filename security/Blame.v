Require Import String.
Require Import Coqlib Maps Errors Integers.
Require Import AST Globalenvs Linking Smallstep Events Behaviors Memory Values.

Require Import Ctypes Cop Clight.
Require Import Split.

Definition same_domain (s: split) (j: meminj) (m: mem): Prop :=
  forall b cp, Mem.block_compartment m b = Some cp ->
          (j b <> None <-> s cp = Right).

Definition delta_zero (j: meminj): Prop :=
  forall loc loc' delta, j loc = Some (loc', delta) -> delta = 0.

Definition same_symbols (j: meminj) (ge1 ge2: genv): Prop :=
  forall id loc,
    Genv.find_symbol ge1 id = Some loc ->
    exists loc', j loc = Some (loc', 0) /\ Genv.find_symbol ge2 id = Some loc'.

Section Equivalence.
  Variable s: split.
  Variable j: meminj.

  Record right_mem_injection (ge1 ge2: genv) (m1 m2: mem) :=
    { same_dom: same_domain s j m1;
      partial_mem_inject: Mem.inject j m1 m2;
      j_delta_zero: delta_zero j;
      same_symb: same_symbols j ge1 ge2
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
    s (comp_of f1) = Left ->
    s (comp_of f2) = Left ->
    right_cont_injection (remove_until_right k1) (remove_until_right k2) ->
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
| inject_callstates: forall f vs k1 k2 m1 m2,
    (* we forget about program memories but require injection of context memories *)
    right_mem_injection ge1 ge2 m1 m2 ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection k1 k2 ->

    right_executing_injection ge1 ge2 (Callstate f vs k1 m1) (Callstate f vs k2 m2)
| inject_returnstates: forall v k1 k2 m1 m2 ty cp,
    (* we forget about program memories but require injection of context memories *)
    right_mem_injection ge1 ge2 m1 m2 ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection k1 k2 ->

    right_executing_injection ge1 ge2 (Returnstate v k1 m1 ty cp) (Returnstate v k2 m2 ty cp)
.

Definition is_left (s: split) (st: state) :=
  match st with
  | State f _ _ _ _ _ => s (comp_of f) = Left
  | Callstate fd _ _ _ => s (comp_of fd) = Left (* Should this be the compartment that's on top of the stack instead? *)
  | Returnstate _ _ _ _ cp => s cp = Left
  end.

Definition is_right (s: split) (st: state) :=
  match st with
  | State f _ _ _ _ _ => s (comp_of f) = Right
  | Callstate fd _ _ _ => s (comp_of fd) = Right
  | Returnstate _ _ _ _ cp => s cp = Right
  end.

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
    is_left s st1 ->
    is_left s st2 ->

    (* we forget about program memories but require injection of context memories *)
    right_mem_injection ge1 ge2 (memory_of st1) (memory_of st2) ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection (cont_of st1) (cont_of st2) ->

    right_state_injection ge1 ge2 st1 st2
| RightControl: forall st1 st2,
    (* context (right) has control *)
    is_right s st1 ->
    is_right s st2 ->
    right_executing_injection ge1 ge2 st1 st2 ->
    right_state_injection ge1 ge2 st1 st2.


End Equivalence.

Section Simulation.
  Context (c p1 p2: Clight.program).
  Variable s: split.


  Context (ge1 ge2: genv).
  (* Is this hypothesis realistic? *)
  Hypothesis same_cenv: genv_cenv ge1 = genv_cenv ge2.

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
      exists loc' ofs', j loc = Some (loc', ofs') /\
                     eval_lvalue ge2 e2 cp le2 m2 a loc' (Ptrofs.add ofs (Ptrofs.repr ofs')) bf).
  Proof.
    intros.
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
      intros [loc' [? ?]].
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

  Lemma parallel_concrete: forall j s1 s2 s1' t,
      right_state_injection s j ge1 ge2 s1 s2 ->
      is_right s s1 ->
      Clight.step1 ge1 s1 t s1' ->
      exists j' s2',
        Clight.step1 ge2 s2 t s2' /\
          right_state_injection s j' ge1 ge2 s1' s2'.
    Proof.
      intros j s1 s2 s1' t rs_inj is_r step1.
      destruct rs_inj as [? | st1 st2 is_r1 is_r2 right_exec_inj].
      (* inv rs_inj. *)
      - (* contradiction *)
        destruct st1; simpl in *; congruence.
      - inv step1; inv right_exec_inj.
        Ltac destruct_mem_inj :=
          match goal with
          | H: right_mem_injection _ _ _ _ _ _ |- _ => destruct H as [same_dom mem_inject delta_zero same_symb]
          end.
        + exploit eval_lvalue_injection; eauto.
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
            -- econstructor; eauto.
               econstructor; eauto.
               rewrite Ptrofs.add_zero; eauto.
            -- apply RightControl; eauto.
               constructor; eauto.
               split; eauto.
               clear -same_dom H10.
               unfold same_domain in *.
               intros. eapply same_dom.
               erewrite <- Mem.store_block_compartment; eauto.
          * inv H8.
            exploit Mem.loadbytes_inj; eauto using Mem.mi_inj.
            intros [? [? ?]].
            exploit Mem.storebytes_mapped_inject; eauto using Mem.mi_inj.
            intros [? [? ?]].
            exploit delta_zero; eauto; intros; subst.
            exploit (delta_zero loc); eauto; intros; subst.
            exists j; eexists; split.
            -- econstructor; eauto.
               rewrite <- same_cenv, !Z.add_0_r, !Ptrofs.add_zero in *; eauto.
               eapply assign_loc_copy; eauto.
               { admit. }
            -- apply RightControl; eauto.
               constructor; eauto.
               split; eauto.
               clear -same_dom H17.
               unfold same_domain in *.
               intros. eapply same_dom.
               erewrite <- Mem.storebytes_block_compartment; eauto.
          * inv H9.
            exploit Mem.load_inject; eauto using Mem.mi_inj.
            intros [? [? ?]].
            exploit Mem.store_mapped_inject; eauto.
            intros [? [? ?]].
            inv H16.
            exploit delta_zero; eauto; intros; subst.
            rewrite Z.add_0_r in *.
            exists j; eexists; split.
            -- econstructor; eauto.
               rewrite Ptrofs.add_zero.
               eapply assign_loc_bitfield. rewrite <- H2. inv H8.
               econstructor; eauto.
            -- apply RightControl; eauto.
               constructor; eauto.
               split; eauto.
               clear -same_dom H18.
               unfold same_domain in *.
               intros. eapply same_dom.
               erewrite <- Mem.store_block_compartment; eauto.
        + exploit eval_expr_injection; eauto.
          intros [v' [? ?]].
          exists j; eexists; split.
          * econstructor; eauto.
          * apply RightControl; eauto.
            constructor; eauto.
            unfold right_tenv_injection in *.
            intros; rewrite PTree.gsspec in *.
            destruct (peq i id); eauto. inv H2; subst.
            eexists; split; eauto.
        + admit.
        + admit.
        + exists j; eexists; split; [constructor | apply RightControl]; auto.
          constructor; auto. constructor; auto.
        + inv H7.
          exists j; eexists; split; [constructor | apply RightControl]; auto.
          constructor; auto.
        + inv H7.
          exists j; eexists; split; [constructor | apply RightControl]; auto.
          constructor; auto.
        + inv H7.
          exists j; eexists; split; [constructor | apply RightControl]; auto.
          constructor; auto.
        + exploit eval_expr_injection; eauto.
          intros [v' [? ?]].
          destruct_mem_inj.
          exploit bool_val_inject; eauto. intros ?.
          exists j; eexists; split; [econstructor | apply RightControl]; eauto.
          constructor; auto. constructor; auto.
        + exists j; eexists; split; [econstructor | apply RightControl]; eauto.
          constructor; auto. constructor; auto.
        + inv H8. exists j; eexists; split; [constructor | apply RightControl]; eauto.
          constructor; auto. constructor; auto.
        + inv H7. exists j; eexists; split; [apply step_break_loop1 | apply RightControl]; eauto.
          constructor; auto.
        + inv H7. exists j; eexists; split; [apply step_skip_loop2 | apply RightControl]; eauto.
          constructor; auto.
        + inv H7. exists j; eexists; split; [apply step_break_loop2 | apply RightControl]; eauto.
          constructor; auto.
        + admit.
        + admit.
        + admit.
        + exploit eval_expr_injection; eauto.
          intros [v' [? ?]].
          assert (sem_switch_arg v (typeof a) = Some n -> sem_switch_arg v' (typeof a) = Some n).
          { intros. unfold sem_switch_arg in *.
            destruct (classify_switch (typeof a)); simpl in *; try easy; inv H1; try easy. }
          exists j; eexists; split; [econstructor | apply RightControl]; eauto.
          constructor; auto.
          constructor; auto.
        + inv H8. exists j; eexists; split; [constructor | apply RightControl]; eauto.
          constructor; auto.
        + inv H7. exists j; eexists; split; [apply step_continue_switch | apply RightControl]; eauto.
          constructor; auto.
        + exists j; eexists; split; [constructor | apply RightControl]; auto.
          constructor; auto.
        + admit.
        + admit.
        + admit.
        + admit.
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
      (* doesn't seem to work because Csem doesn't seem to have a fixed evaluation order *)
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
