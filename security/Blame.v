Require Import String.
Require Import Coqlib Maps Errors Integers.
Require Import AST Linking Smallstep Events Behaviors Memory Values.

Require Import Ctypes Cop Clight.
Require Import Split.

Definition same_domain (s: split) (j: meminj) (m: mem): Prop :=
  forall b cp, Mem.block_compartment m b = Some cp ->
          (j b <> None <-> s cp = Right).

Section Equivalence.
  Variable s: split.
  Variable j: meminj.

  Record right_mem_injection (m1 m2: mem) :=
    { same_dom: same_domain s j m1;
      partial_mem_inject: Mem.inject j m1 m2;
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

Definition right_env_injection (e1 e2: env): Prop :=
  forall i b ty,
    e1 ! i = Some (b, ty) ->
    exists b', j b = Some (b', 0%Z) /\
          e2 ! i = Some (b', ty).

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
Variant right_executing_injection: state -> state -> Prop :=
| inject_states: forall f s k1 k2 e1 e2 le1 le2 m1 m2,
    (* we forget about program memories but require injection of context memories *)
    right_mem_injection m1 m2 ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection k1 k2 ->

    (* the environments satisfy the injection *)
    right_env_injection e1 e2 ->
    right_tenv_injection le1 le2 ->

    right_executing_injection (State f s k1 e1 le1 m1) (State f s k2 e2 le2 m2)
| inject_callstates: forall f vs k1 k2 m1 m2,
    (* we forget about program memories but require injection of context memories *)
    right_mem_injection m1 m2 ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection k1 k2 ->

    right_executing_injection (Callstate f vs k1 m1) (Callstate f vs k2 m2)
| inject_returnstates: forall v k1 k2 m1 m2 ty cp,
    (* we forget about program memories but require injection of context memories *)
    right_mem_injection m1 m2 ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection k1 k2 ->

    right_executing_injection (Returnstate v k1 m1 ty cp) (Returnstate v k2 m2 ty cp)
.

Axiom is_left: split -> state -> Prop.
Axiom is_right: split -> state -> Prop.

Axiom memory_of: state -> mem.
Axiom cont_of: state -> cont.

Variant right_state_injection: state -> state -> Prop :=
| LeftControl: forall st1 st2,
    (* program (left) has control *)
    is_left s st1 ->
    is_left s st2 ->

    (* we forget about program memories but require injection of context memories *)
    right_mem_injection (memory_of st1) (memory_of st2) ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection (cont_of st1) (cont_of st2) ->

    right_state_injection st1 st2
| RightControl: forall st1 st2,
    (* context (right) has control *)
    is_right s st1 ->
    is_right s st2 ->
    right_executing_injection st1 st2 ->
    right_state_injection st1 st2.


End Equivalence.

Section Simulation.
  Context (c p1 p2: Clight.program).
  Variable s: split.
  Variable j: meminj.

  Context (ge1 ge2: genv).

  Lemma eval_expr_lvalue_injection:
    forall s j m1 m2 e1 e2 le1 le2 cp,
    forall inj: right_mem_injection s j m1 m2,
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
    destruct inj as [inj_dom inj_inject].
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
      intros [? [? ?]].
      eexists; split; eauto.
      econstructor; eauto.
    -
    - (* this is a contradictory case: there is no unary operation that returns a pointer *)
      destruct op; simpl in *.
      + rewrite notbool_bool_val in H1.
        destruct (bool_val _ _ _); [| congruence].
        inv H1. now destruct b.
      + unfold sem_notint in H1. destruct (classify_notint _); [| | congruence].
        now destruct v1. now destruct v1.
      + unfold sem_neg in H1. destruct (classify_neg _); try congruence; now destruct v1.
      + unfold sem_absfloat in H1. destruct (classify_neg _); try congruence; now destruct v1.
    - assert ((exists loc0 ofs0, v1 = Vptr loc0 ofs0) \/
             (exists loc0 ofs0, v2 = Vptr loc0 ofs0)).
      { destruct op; simpl in *.
        - unfold sem_add in *.
          destruct (classify_add _ _); simpl in *.
          destruct v1, v2; simpl in *; destruct Archi.ptr64; simpl in *; inv H3; left; eexists; eexists; eauto.
          destruct v1, v2; simpl in *; destruct Archi.ptr64; simpl in *; inv H3; left; eexists; eexists; eauto.
          destruct v1, v2; simpl in *; destruct Archi.ptr64; simpl in *; inv H3; right; eexists; eexists; eauto.
          destruct v1, v2; simpl in *; destruct Archi.ptr64; simpl in *; inv H3; right; eexists; eexists; eauto.
          destruct (typeof a1), (typeof a2); unfold sem_binarith in *; simpl in *; try now inv H3.
          destruct v1, v2; simpl in *.
          unfold sem_binarith.


            try (now
              destruct v1, v2; simpl in *; destruct Archi.ptr64; simpl in *; inv H3; try (left; eexists; eexists; eauto);
               try (right; eexists; eexists; eauto)).

          destruct v2, v1; simpl in *; destruct Archi.ptr64; inv H3.
            try now (eexists; eexists; eauto).

            eexists; eexists; eauto.
          + destruct v1, v2; simpl in *; destruct Archi.ptr64; simpl in *; inv H3.
            eexists; eexists; eauto.
            eexists; eexists; eauto.
          +
            simpl in H3.
          destruct v1. simpl in H3.
            try now destruct v1.
          destruct v1; try now auto.

        - rewrite notbool_bool_val in H1.
          destruct (bool_val _ _ _); [| congruence].
          inv H1. now destruct b.
        - unfold sem_notint in H1. destruct (classify_notint _); [| | congruence].
          now destruct v1. now destruct v1.
        - unfold sem_neg in H1. destruct (classify_neg _); try congruence; now destruct v1.
        - unfold sem_absfloat in H1. destruct (classify_neg _); try congruence; now destruct v1. }
      subst v1.
      specialize (H0 _ _ eq_refl) as [loc' [ofs' [? ?]]].
      (* exploit sem_unary_operation_inject; eauto. *)
      (* intros [tv [? ?]]. *)
      (* destruct tv; try now inv H4. *)
      (* inv H4. *)
      exists loc', ofs'; split; eauto.
      econstructor; eauto.
      rewrite H3. congruence.
    -


  Lemma parallel_concrete: forall s1 s2 s1' t,
      right_state_injection s j s1 s2 ->
      is_right s s1 ->
      Clight.step1 ge1 s1 t s1' ->
      exists s2',
        Clight.step1 ge2 s2 t s2' /\
          right_state_injection s j s1' s2'.
    Proof.
      intros s1 s2 s1' t rs_inj is_r step1.
      inv rs_inj.
      - admit. (* contradiction *)
      - inv step1; inv H1.
        + assert (lemma1:
                   right_mem_injection s j m m2 ->
                   right_env_injection j e e2 ->
                   right_tenv_injection j le le2 ->
                   eval_lvalue ge1 e (comp_of f) le m a1 loc ofs bf ->
                   exists loc' ofs', j loc = Some (loc', ofs') /\
                          eval_lvalue ge2 e2 (comp_of f) le2 m2 a1 loc' (Ptrofs.add ofs (Ptrofs.repr ofs')) bf).
          { clear.
            intros inj env_inj lenv_inj ev.
            destruct inj as [inj_dom inj_inject].
            inv ev.
            - exploit env_inj; eauto. intros [loc' [? ?]].
              exists loc', 0%Z. split; eauto.
              constructor; eauto.
            - admit.
            - eexists; eexists; split; eauto. admit.
              constructor. admit.

              admit.
            - admit.
            - admit.
          }
          exploit lemma1; eauto.
          intros [loc' [ofs' [? ?]]].

          eexists; split.
          econstructor. eauto.
          intros [loc' [ofs' [? ?]]].
          eassumption.


          admit. admit. admit. admit.
          right. admit. admit.
          econstructor; eauto. admit.
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
