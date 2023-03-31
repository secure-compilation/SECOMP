Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm.

(* Require Import Coqlib. *)
Require Import Maps.
(* Require Import AST. *)
(* Require Import Integers. *)
(* Require Import Floats. *)
(* Require Import Values. *)
(* Require Import Memory. *)
(* Require Import Events. *)
(* Require Import Globalenvs. *)
(* Require Import Smallstep. *)
(* Require Import Locations. *)
(* Require Stacklayout. *)
(* Require Import Conventions. *)

Require Import Behaviors.
Require Import Split.
Require Import Complements.

(* Memory *)

(* Old style: remove components from "context"
   New style: remove components from given side *)
Definition to_partial_memory (m : mem) (lrsplit : split) (lr : side) : mem :=
  m. (* TODO *)

(* CompCertExtensions *)

Inductive finpref_behavior : Type :=
  | FTerminates: trace -> int -> finpref_behavior
  | FGoes_wrong: trace -> finpref_behavior
  | FTbc : trace -> finpref_behavior.

Definition prefix (m:finpref_behavior) (b:program_behavior) : Prop :=
  match m, b with
  | FTerminates t1 n1, Terminates t2 n2 => t1 = t2 /\ n1 = n2
  | FGoes_wrong t1, Goes_wrong t2 => t1 = t2
  | FTbc t1, b => behavior_prefix t1 b
  | _, _ => False
  end.

Definition finpref_trace (m : finpref_behavior) : trace :=
  match m with
  | FTerminates t _ | FGoes_wrong t | FTbc t => t
  end.

Definition does_prefix x m := exists b, program_behaves x b /\ prefix m b.

Lemma program_behaves_finpref_exists :
  forall L s t s',
    initial_state L s ->
    Star (semantics L) s t s' ->
  exists beh,
    program_behaves (semantics L) beh /\
    prefix (FTbc t) beh.
Proof.
  intros L s t s' Hini HStar.
  destruct (state_behaves_exists (semantics L) s') as [beh_s' Hbeh_s'].
  (* pose proof program_runs Hini (state_behaves_app HStar Hbeh_s') as Hbeh. *)
  pose proof @program_runs (semantics L) s _ Hini (state_behaves_app HStar Hbeh_s') as Hbeh.
  eexists. split.
  - exact Hbeh.
  - simpl. exists beh_s'. reflexivity.
Qed.

(* CS *)

(* is_left_component? *)
Definition is_program_component (s : state) (lrsplit : split) : Prop :=
  match s with
  | State _ rs m
  | ReturnState _ rs m =>
      match rs # PC with
      | Vptr b _ =>
          match (Mem.mem_compartments m) ! b with
          | Some cp => lrsplit cp = Left
          | None => False
          end
      | _ => False
      end
  end.

Definition state_mem (s : state) : mem :=
  match s with
  | State _ _ m
  | ReturnState _ _ m
    => m
  end.

Section SEMANTICS.

Variable p: program.

(* Hypothesis valid_program: *)
(*   well_formed_program p. *)

(* Hypothesis complete_program: *)
(*   closed_program p. *)

(* Let G := prepare_global_env p. *)

Definition sem :=
  semantics p.

Lemma program_behaves_inv:
  forall b,
    program_behaves sem b ->
  exists s,
    initial_state p s /\ state_behaves sem s b.
Proof.
  intros b [s b' Hini Hbeh | Hini]; subst.
  - now exists s.
  - simpl in Hini.
  (*   specialize (Hini (initial_machine_state p)). *)
  (*   unfold initial_state in Hini. *)
  (*     contradiction. *)
  (* Qed. *)
Admitted.

End SEMANTICS.

Theorem behavior_prefix_star {p b m} :
  program_behaves (sem p) b ->
  prefix m b ->
exists s1 s2,
  initial_state p s1 /\
  Star (sem p) s1 (finpref_trace m) s2.
Admitted.

(* Recombination *)

Section MERGE.

Variable lrsplit : split.

(* TODO Modify [b] and [sp] as needed *)
Definition merge_frames (f f'' : stackframe) : stackframe :=
  match f with
  | Stackframe b cp _ sp _ =>
      match lrsplit cp with
      | Left => f
      | Right => f''
      end
  end.

Fixpoint merge_stacks (s s'' : stack) : stack :=
  match s, s'' with
  | nil, nil => nil
  | f :: s, f'' :: s'' => merge_frames f f'' :: merge_stacks s s''
  | _, _ => nil (* Should not happen *)
  end.

(* Merging the memories of two executions can be tricky. The main reason for
   this is that in the CompCert memory model (extended with compartments) the
   mapping between memory blocks across executions is not necessarily the
   identity.

   Consider for example two parallel executions which perform different
   allocation sequences. These can be split depending on the side that is
   executing at each point in time according to the split.

            | Left    | Right   | Left    | ...
     prog   | 1, 2, 3 | 4, 5, 6 | 7, 8, 9 | ...
     prog'' | 1       | 2       | 3       | ...

   It is not possible to simply take the Left blocks from one execution and the
   Right blocks from the other, as this could result in clashes between block
   identifiers.

     prog'  | 1, 2, 3 | 2       | 7, 8, 9 | ...

   A possible solution to this problem must involve a slightly more interesting
   mapping from block identifiers and sides to block identifiers. For example,
   we could reserve even blocks for blocks coming from the Left side (2 * n) and
   odd blocks for blocks coming from the Right side (2 * n + 1). Thus:

     prog'  | 2, 4, 6 | 5       | 14, ... | ...

   A consequence of this rearrangement is that memory contents must also change
   to reflect the mapping, i.e., the same mapping must be applied to block
   identifiers in pointer values. *)

(* TODO Add side filtering *)
Definition remap
  {X : Type} (s : side) (f : X -> X)
  (t : Maps.PTree.t X) (e : positive * X) : Maps.PTree.t X :=
  let '(b, x) := e in
  let b' := match s with
            | Left => 2 * b
            | Right => 2 * b + 1
            end%positive in
  Maps.PTree.set b' (f x) t.

(* TODO Actually go from [memval] to [val], remap blocks according to the side
   and leave the rest intact (see [memory_chunk], [AST]) *)
Definition merge_value (s : side) (v : memval) : memval :=
  v.

Definition merge_contents (m m'' : mem) :=
  let (def, c) := Mem.mem_contents m in
  let (_, c'') := Mem.mem_contents m'' in (* default discarder *)
  (* TODO Filter according to side *)
  let t0 := List.fold_left (remap Left id) (Maps.PTree.elements c) (Maps.PTree.empty _) in
  let t1 := List.fold_left (remap Right id) (Maps.PTree.elements c'') t0 in
  (def, t1).

Definition merge_access (m m'' : mem) :=
  let '(def, a) := Mem.mem_access m in
  let '(_, a'') := Mem.mem_access m'' in (* default discarded *)
  (* TODO Filter according to side *)
  let t0 := List.fold_left (remap Left id) (Maps.PTree.elements a) (Maps.PTree.empty _) in
  let t1 := List.fold_left (remap Right id) (Maps.PTree.elements a'') t0 in
  (def, t1).

(* TODO Compartments must be assigned to all "allocated" blocks:
   [Plt b (merge_nextblocks m m'')] *)
Definition merge_compartments (m m'' : mem) :=
  let c := Mem.mem_compartments m in
  let c'' := Mem.mem_compartments m'' in
  (* TODO Filter according to side *)
  let t0 := List.fold_left (remap Left id) (Maps.PTree.elements c) (Maps.PTree.empty _) in
  let t1 := List.fold_left (remap Right id) (Maps.PTree.elements c'') t0 in
  t1.

Definition merge_nextblocks (m m'' : mem) :=
  let n := Mem.nextblock m in
  let n'' := Mem.nextblock m'' in
  (* TODO Tight bounds based on side *)
  Pos.max (2 * n + 1) (2 * n'' + 1).

Program Definition merge_memories (m m'' : mem) : mem :=
  {| Mem.mem_contents := merge_contents m m''
   ; Mem.mem_access := merge_access m m''
   ; Mem.mem_compartments := merge_compartments m m''
   ; Mem.nextblock := merge_nextblocks m m''
  |}.
Next Obligation.
Proof.
  unfold Mem.perm_order'', merge_access.
  destruct m as [A [def mem_access] C D access_max F G H]; simpl; clear A C D F G H.
  destruct m'' as [A [def'' mem_access''] C D access_max'' F G H]; simpl; clear A C D F G H.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Definition merge_registers (r r'' : regset) (m : mem) : regset :=
  match Mem.val_compartment m r#PC with
  | Some cp =>
      match lrsplit cp with
      | Left => r
      | Right => r''
      end
  | None =>
      r (* Should not happen *)
  end.

Definition merge_states (state state'' : state) : Asm.state :=
  match state, state'' with
  | State s r m, State s'' r'' m'' =>
      State (merge_stacks s s'') (merge_registers r r'' m) (merge_memories m m'')
  | ReturnState s r m, ReturnState s'' r'' m'' =>
      ReturnState (merge_stacks s s'') (merge_registers r r'' m) (merge_memories m m'')
  | _, _ =>
      state (* Should not happen *)
  end.

End MERGE.

Section MERGEABLE.

Variables p c p' c' : program.

(* Variable sp : split. *)

(* Hypothesis Hcompat  : asm_compatible s p  c. *)
(* Hypothesis Hcompat' : asm_compatible s p' c'. *)

Variables prog prog' prog'' : program.

Hypothesis Hprog   : link p  c  = Some prog.
Hypothesis Hprog'  : link p  c' = Some prog'.
Hypothesis Hprog'' : link p' c' = Some prog''.

Let sem   := semantics prog.
Let sem'  := semantics prog'.
Let sem'' := semantics prog''.

Inductive mergeable_states (s s'' : state) : Prop :=
  mergeable_states_intro : forall sp s0 s0'' t,
    (* Well-formedness conditions. *)
    asm_compatible sp p  c ->
    asm_compatible sp p' c' ->
    (* "Proper" definition. *)
    initial_state prog   s0   ->
    initial_state prog'' s0'' ->
    Star sem   s0   t s   ->
    Star sem'' s0'' t s'' ->
    mergeable_states s s''.

Lemma mergeable_states_ind' : forall P : state -> state -> Prop,
    (forall (s s'' : state),
        initial_state prog s ->
        initial_state prog'' s'' ->
        P s s'') ->
    (forall (s1 s2 s'' : state),
        mergeable_states s1 s'' ->
        Step sem s1 E0 s2 ->
        P s1 s'' ->
        P s2 s'') ->
    (forall (s s1'' s2'' : state),
        mergeable_states s s1'' ->
        Step sem'' s1'' E0 s2'' ->
        P s s1'' ->
        P s s2'') ->
    (forall (s1 s2 s1'' s2'' : state) (t : trace),
        t <> E0 ->
        mergeable_states s1 s1'' ->
        Step sem s1 t s2 ->
        Step sem'' s1'' t s2'' ->
        P s1 s1'' ->
        P s2 s2'') ->
    forall (s s'' : state), mergeable_states s s'' -> P s s''.
Proof.
  (*   intros P. *)
  (*   intros Hindini HindE0l HindE0r Hindstep. *)
  (*   intros s s'' Hmerg. *)
  (*   inversion Hmerg *)
  (*     as [s0 s0'' t ? ? ? ? ? ? ? ? ? Hini Hini'' Hstar Hstar'']. *)
  (*   apply star_iff_starR in Hstar. apply star_iff_starR in Hstar''. *)
  (*   generalize dependent s''. *)
  (*   induction Hstar *)
  (*     as [s | s1 t1 s2 t2 s3 ? Hstar12 IHstar Hstep23 Ht12]; *)
  (*     intros s'' Hmerg Hstar''. *)
  (*   - remember E0 as t. *)
  (*     induction Hstar''. *)
  (*     + now apply Hindini. *)
  (*     + subst. *)
  (*       assert (Ht1 : t1 = E0) by now destruct t1. *)
  (*       assert (Ht2 : t2 = E0) by now destruct t1. *)
  (*       subst. *)
  (*       specialize (IHHstar'' eq_refl HindE0l HindE0r Hindstep). *)
  (*       assert (Hmergss2 : mergeable_states s s2). *)
  (*       { apply star_iff_starR in Hstar''. *)
  (*         econstructor; try eassumption. now apply star_refl. } *)
  (*       specialize (IHHstar'' Hini'' Hmergss2). eapply HindE0r; eauto. *)
  (*   - pose proof (CS.singleton_traces (program_link p c) _ _ _ Hstep23) as Hlen. *)
  (*     assert (t2 = E0 \/ exists ev, t2 = [ev]) as [Ht2E0 | [ev Ht2ev]]. *)
  (*     { clear -Hlen. *)
  (*       inversion Hlen. *)
  (*       - right. destruct t2. simpl in *. congruence. *)
  (*         simpl in *. destruct t2; eauto. simpl in *. congruence. *)
  (*       - left. subst. destruct t2; simpl in *. reflexivity. *)
  (*         omega. } *)
  (*     + subst. *)
  (*       unfold Eapp in Hstar''; rewrite app_nil_r in Hstar''. *)
  (*       assert (Hmergs2s'' : mergeable_states s2 s''). *)
  (*       { econstructor; try eassumption. *)
  (*         apply star_iff_starR in Hstar12. apply Hstar12. *)
  (*         apply star_iff_starR in Hstar''. apply Hstar''. } *)
  (*       specialize (IHstar Hini s'' Hmergs2s'' Hstar''). *)
  (*       eapply HindE0l; eauto. *)
  (*     + subst. *)
  (*       remember (t1 ** [ev]) as t. *)
  (*       induction Hstar''; subst. *)
  (*       * assert (E0 <> t1 ** [ev]) by now induction t1. contradiction. *)
  (*       * subst. *)
  (*         specialize (IHHstar'' Hini'' IHstar). *)
  (*         pose proof (CS.singleton_traces (program_link p' c') _ _ _ H8) as Hlen2. *)
  (*         assert (t2 = E0 \/ exists ev, t2 = [ev]) as [ht2E0 | [ev' Ht2ev']]. *)
  (*         { clear -Hlen2. *)
  (*           inversion Hlen2. *)
  (*           - right. destruct t2. simpl in *; congruence. *)
  (*             simpl in *. destruct t2; eauto. simpl in *. congruence. *)
  (*           - left. inversion H0. destruct t2; simpl in *. reflexivity. *)
  (*             congruence. } *)
  (*         ** subst. *)
  (*            unfold Eapp in H9; rewrite app_nil_r in H9; subst. *)
  (*            assert (Hmergs3s4 : mergeable_states s3 s4). *)
  (*            { econstructor; eauto. *)
  (*              apply star_iff_starR. *)
  (*              eapply starR_step. *)
  (*              apply Hstar12. *)
  (*              eauto. reflexivity. *)
  (*              apply star_iff_starR in Hstar''; apply Hstar''. } *)
  (*            specialize (IHHstar'' Hmergs3s4 eq_refl). *)
  (*            eapply HindE0r; eauto. *)
  (*         ** subst. *)
  (*            assert (t1 = t0 /\ ev = ev') as [Ht1t0 Hevev'] by now apply app_inj_tail. *)
  (*            subst. clear IHHstar''. *)
  (*            specialize (IHstar Hini s4). *)
  (*            assert (Hmerge : mergeable_states s2 s4). *)
  (*            { econstructor; try eassumption. apply star_iff_starR in Hstar12; apply Hstar12. *)
  (*              apply star_iff_starR in Hstar''; apply Hstar''. } *)
  (*            specialize (IHstar Hmerge Hstar''). *)
  (*            eapply Hindstep with (t := [ev']); eauto. unfold E0. congruence. *)
  (* Qed. *)
Admitted.

End MERGEABLE.

Section THREEWAY_MULTISEM_1.

Variables p c p' c' : program.

Variable lrsplit : split.

Hypothesis Hcompat  : asm_compatible lrsplit p  c.
Hypothesis Hcompat' : asm_compatible lrsplit p' c'.

Variables prog prog' prog'' : program.

Hypothesis Hprog   : link p  c  = Some prog.
Hypothesis Hprog'  : link p  c' = Some prog'.
Hypothesis Hprog'' : link p' c' = Some prog''.

Let sem   := semantics prog.
Let sem'  := semantics prog'.
Let sem'' := semantics prog''.

Lemma to_partial_memory_epsilon_star s s1'' s2'' s3'' :
  mergeable_states p c p' c' prog prog'' s s1'' ->
  is_program_component s lrsplit ->
  Star sem'' s1'' E0 s2'' ->
  Step sem'' s2'' E0 s3'' ->
  to_partial_memory (state_mem s2'') lrsplit Left =
  to_partial_memory (state_mem s3'') lrsplit Left.
  (* Proof. *)
  (*   intros Hmerge1 Hcomp Hstar12'' Hstep23''. *)
  (*   destruct s2'' as [[[gps2'' mem2''] regs2''] pc2'']. *)
  (*   destruct s3'' as [[[gps3'' mem3''] regs3''] pc3'']. *)
  (*   inversion Hstep23''; subst; *)
  (*     (* Most cases do not touch the memory. *) *)
  (*     try reflexivity; *)
  (*     (* Rewrite memory goals, discharge side goals and homogenize shape. *) *)
  (*     match goal with *)
  (*     | Hstore : Memory.store _ _ _ = _, *)
  (*       Heq : Pointer.component _ = Pointer.component _ |- _ => *)
  (*       erewrite Memory.program_store_to_partialized_memory; eauto 1; rewrite Heq *)
  (*     | Halloc : Memory.alloc _ _ _ = _ |- _ => *)
  (*       erewrite program_allocation_to_partialized_memory; eauto 1 *)
  (*     end; *)
  (*     (* Prove the PC is in the program in both cases. *) *)
  (*     unfold ip; *)
  (*     t_to_partial_memory_epsilon_star Hmerge1 Hcomp Hstar12''. *)
  (* Qed. *)

  (* Lemma merge_states_silent_star s s1'' s2'' : *)
  (*   mergeable_states p c p' c' s s1'' -> *)
  (*   CS.is_program_component s ic -> *)
  (*   Star sem'' s1'' E0 s2'' -> *)
  (*   merge_states ip ic s s1'' = merge_states ip ic s s2''. *)
  (* Proof. *)
  (*   intros Hmerge1 Hcomp Hstar12''. *)
  (*   remember E0 as t. *)
  (*   apply star_iff_starR in Hstar12''. *)
  (*   induction Hstar12'' *)
  (*     as [s'' | s1'' t1 s2'' t2 s3'' ? Hstar12'' IHstar'' Hstep23'' Ht12]; subst. *)
  (*   - reflexivity. *)
  (*   - (* Simplify, apply IH and case analyze. *) *)
  (*     symmetry in Ht12; apply Eapp_E0_inv in Ht12 as [? ?]; subst. *)
  (*     specialize (IHstar'' Hmerge1 eq_refl). rewrite IHstar''. *)
  (*     apply star_iff_starR in Hstar12''. *)
  (*     destruct s as [[[gps mem] regs] pc]. *)
  (*     destruct s2'' as [[[gps2'' mem2''] regs2''] pc2'']. *)
  (*     destruct s3'' as [[[gps3'' mem3''] regs3''] pc3'']. *)
  (*     inversion Hstep23''; subst; *)
  (*       (* Unfold, common rewrite on PC, memory rewrite for memory goals and done. *) *)
  (*       unfold merge_states, merge_registers, merge_pcs, merge_memories, ip; *)
  (*       erewrite mergeable_states_program_component_domm; try eassumption; *)
  (*       try (pose proof to_partial_memory_epsilon_star Hmerge1 Hcomp Hstar12'' Hstep23'' as Hmem23''; *)
  (*            simpl in Hmem23''; rewrite Hmem23''); *)
  (*       reflexivity. *)
  (* Qed. *)
Admitted.

Lemma merge_states_silent_star {s s1'' s2''} :
  mergeable_states p c p' c' prog prog'' s s1'' ->
  is_program_component s lrsplit ->
  Star sem'' s1'' E0 s2'' ->
  merge_states lrsplit s s1'' = merge_states lrsplit s s2''.
  (* Proof. *)
  (*   intros Hmerge1 Hcomp Hstar12''. *)
  (*   remember E0 as t. *)
  (*   apply star_iff_starR in Hstar12''. *)
  (*   induction Hstar12'' *)
  (*     as [s'' | s1'' t1 s2'' t2 s3'' ? Hstar12'' IHstar'' Hstep23'' Ht12]; subst. *)
  (*   - reflexivity. *)
  (*   - (* Simplify, apply IH and case analyze. *) *)
  (*     symmetry in Ht12; apply Eapp_E0_inv in Ht12 as [? ?]; subst. *)
  (*     specialize (IHstar'' Hmerge1 eq_refl). rewrite IHstar''. *)
  (*     apply star_iff_starR in Hstar12''. *)
  (*     destruct s as [[[gps mem] regs] pc]. *)
  (*     destruct s2'' as [[[gps2'' mem2''] regs2''] pc2'']. *)
  (*     destruct s3'' as [[[gps3'' mem3''] regs3''] pc3'']. *)
  (*     inversion Hstep23''; subst; *)
  (*       (* Unfold, common rewrite on PC, memory rewrite for memory goals and done. *) *)
  (*       unfold merge_states, merge_registers, merge_pcs, merge_memories, ip; *)
  (*       erewrite mergeable_states_program_component_domm; try eassumption; *)
  (*       try (pose proof to_partial_memory_epsilon_star Hmerge1 Hcomp Hstar12'' Hstep23'' as Hmem23''; *)
  (*            simpl in Hmem23''; rewrite Hmem23''); *)
  (*       reflexivity. *)
  (* Qed. *)
Admitted.

Lemma context_epsilon_star_merge_states s s1 s2 :
  mergeable_states p c p' c' prog prog'' s s1 ->
  is_program_component s lrsplit ->
  Star sem'' s1 E0 s2 ->
  Star sem' (merge_states lrsplit s s1) E0 (merge_states lrsplit s s2).
Proof.
  intros Hmerg Hcomp Hstar.
  rewrite (merge_states_silent_star Hmerg Hcomp Hstar).
  apply star_refl.
Qed.

Lemma threeway_multisem_mergeable_step_E0 s1 s2 s1'' :
  is_program_component s1 lrsplit ->
  mergeable_states p c p' c' prog prog'' s1 s1'' ->
  Step sem s1 E0 s2 ->
  mergeable_states p c p' c' prog prog'' s2 s1''.
Proof.
  intros Hcomp1 Hmerge1 Hstep12.
  inversion Hmerge1 as [sp s0 s0'' t Hini1 Hini2 Hstar01 Hstar01''].
  apply mergeable_states_intro with (sp := sp) (s0 := s0) (s0'' := s0'') (t := t);
    try assumption.
  eapply star_right; try eassumption; now rewrite E0_right.
Qed.

Lemma threeway_multisem_mergeable_program s1 s1'' t s2 s2'' :
  is_program_component s1 lrsplit ->
  mergeable_states p c p' c' prog prog'' s1 s1'' ->
  Star sem   s1   t s2   ->
  Star sem'' s1'' t s2'' ->
  mergeable_states p c p' c' prog prog'' s2 s2''.
Proof.
  intros _ Hmerg Hstar Hstar''. inversion Hmerg.
  econstructor; try eassumption.
  - eapply star_trans; try eassumption; reflexivity.
  - eapply star_trans; try eassumption; reflexivity.
Qed.

Theorem threeway_multisem_step_E0 s1 s2 s1'' :
  is_program_component s1 lrsplit ->
  mergeable_states p c p' c' prog prog'' s1 s1'' ->
  Step sem  s1 E0 s2 ->
  Step sem' (merge_states lrsplit s1 s1'') E0 (merge_states lrsplit s2 s1'').
  (* Proof. *)
  (*   intros Hcomp1 Hmerge1 Hstep12. *)
  (*   inversion Hmerge1 as [??????? Hmergeable_ifaces ????????]. *)
  (*   (* Derive some useful facts and begin to expose state structure. *) *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   rewrite (mergeable_states_merge_program Hcomp1 Hmerge1). *)
  (*   pose proof CS.silent_step_preserves_program_component _ _ _ _ Hcomp1 Hstep12 as Hcomp2. *)
  (*   pose proof threeway_multisem_mergeable_step_E0 Hcomp1 Hmerge1 Hstep12 *)
  (*     as Hmerge2. *)
  (*   rewrite (mergeable_states_merge_program Hcomp2 Hmerge2). *)
  (*   destruct s1 as [[[gps1 mem1] regs1] pc1]. *)
  (*   destruct s2 as [[[gps2 mem2] regs2] pc2]. *)
  (*   destruct s1'' as [[[gps1'' mem1''] regs1''] pc1'']. *)
  (*   (* Case analysis on step. *) *)
  (*   inversion Hstep12; subst; *)
  (*     t_threeway_multisem_step_E0. *)
  (* Qed. *)
Admitted.

Theorem threeway_multisem_star_E0_program s1 s1'' s2 s2'':
  is_program_component s1 lrsplit ->
  mergeable_states p c p' c' prog prog'' s1 s1'' ->
  Star sem   s1   E0 s2   ->
  Star sem'' s1'' E0 s2'' ->
  Star sem'  (merge_states lrsplit s1 s1'') E0 (merge_states lrsplit s2 s2'').
  (* Proof. *)
  (*   intros Hcomp1 Hmerge1 Hstar12 Hstar12''. *)
  (*   inversion Hmerge1 as [?? t0 ???? Hmergeable_ifaces ? Hifacec ???? Hstar ?]. *)
  (*   pose proof mergeable_states_program_to_program Hmerge1 Hcomp1 as Hcomp1'. *)
  (*   rewrite Hifacec in Hcomp1'. *)
  (*   remember E0 as t eqn:Ht. *)
  (*   revert Ht Hmerge1 Hcomp1 Hcomp1' Hstar12''. *)
  (*   apply star_iff_starR in Hstar12. *)
  (*   induction Hstar12 as [s | s1 t1 s2 t2 s3 ? Hstar12 IHstar Hstep23]; subst; *)
  (*     intros Ht Hmerge1 Hcomp1 Hcomp1' Hstar12'. *)
  (*   - rewrite -Hifacec in Hcomp1'. *)
  (*     unfold ip, ic; erewrite merge_states_silent_star; try eassumption. *)
  (*     now apply star_refl. *)
  (*   - apply Eapp_E0_inv in Ht. destruct Ht; subst. *)
  (*     specialize (IHstar Hstar eq_refl Hmerge1 Hcomp1 Hcomp1' Hstar12'). *)
  (*     apply star_trans with (t1 := E0) (s2 := merge_states ip ic s2 s2'') (t2 := E0); *)
  (*       [assumption | | reflexivity]. *)
  (*     apply star_step with (t1 := E0) (s2 := merge_states ip ic s3 s2'') (t2 := E0). *)
  (*     + apply star_iff_starR in Hstar12. *)
  (*       pose proof threeway_multisem_mergeable_program Hcomp1 Hmerge1 Hstar12 Hstar12' *)
  (*         as Hmerge2. *)
  (*       pose proof CS.epsilon_star_preserves_program_component _ _ _ _ Hcomp1 Hstar12 *)
  (*         as Hcomp2. *)
  (*       exact (threeway_multisem_step_E0 Hcomp2 Hmerge2 Hstep23). *)
  (*     + now constructor. *)
  (*     + reflexivity. *)
  (* Qed. *)
Admitted.

Lemma threeway_multisem_event_lockstep_program_mergeable s1 s1'' e s2 s2'' :
  is_program_component s1 lrsplit ->
  mergeable_states p c p' c' prog prog'' s1 s1'' ->
  Step sem   s1   (e :: nil) s2   ->
  Step sem'' s1'' (e :: nil) s2'' ->
  mergeable_states p c p' c' prog prog'' s2 s2''.
Proof.
  intros Hcomp1 Hmerge1 Hstep12 Hstep12''. inversion Hmerge1.
  apply mergeable_states_intro with (sp := sp) (s0 := s0) (s0'' := s0'') (t := t ** (e :: nil));
    try assumption.
  - eapply star_right; try eassumption; reflexivity.
  - eapply star_right; try eassumption; reflexivity.
Qed.

Theorem threeway_multisem_event_lockstep_program_step s1 s1'' e s2 s2'' :
  is_program_component s1 lrsplit ->
  mergeable_states p c p' c' prog prog'' s1 s1'' ->
  Step sem   s1   (e :: nil) s2   ->
  Step sem'' s1'' (e :: nil) s2'' ->
  Step sem'  (merge_states lrsplit s1 s1'') (e :: nil) (merge_states lrsplit s2 s2'').
  (* Proof. *)
  (*   intros Hcomp1 Hmerge1 Hstep12 Hstep12''. *)
  (*   (* Derive some useful facts and begin to expose state structure. *) *)
  (*   inversion Hmerge1 as [??? Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec ??????]. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmain_linkability. *)
  (*   assert (Hlinkable' := Hlinkable); rewrite Hifacep Hifacec in Hlinkable'. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp' Hwfc' Hlinkable' as Hmain_linkability'. *)
  (*   rewrite (mergeable_states_merge_program Hcomp1 Hmerge1). *)
  (*   pose proof threeway_multisem_event_lockstep_program_mergeable *)
  (*        Hcomp1 Hmerge1 Hstep12 Hstep12'' as Hmerge2. *)
  (*   set s1copy := s1. destruct s1 as [[[gps1 mem1] regs1] pc1]. *)
  (*   set s2copy := s2. destruct s2 as [[[gps2 mem2] regs2] pc2]. *)
  (*   destruct s1'' as [[[gps1'' mem1''] regs1''] pc1'']. *)
  (*   destruct s2'' as [[[gps2'' mem2''] regs2''] pc2'']. *)
  (*   (* Case analysis on step. *) *)
  (*   inversion Hstep12; subst; *)
  (*     inversion Hstep12''; subst. *)
  (*   - (* Call: case analysis on call point. *) *)
  (*     pose proof is_program_component_in_domm Hcomp1 Hmerge1 as Hdomm. *)
  (*     unfold CS.state_component in Hdomm; simpl in Hdomm. unfold ip, ic. *)
  (*     rewrite <- Pointer.inc_preserves_component in Hdomm. *)
  (*     destruct (CS.is_program_component s2copy ic) eqn:Hcomp2; *)
  (*       [ pose proof mergeable_states_program_to_context Hmerge2 Hcomp2 as Hcomp2'' *)
  (*       | apply negb_false_iff in Hcomp2 ]; *)
  (*       [ erewrite mergeable_states_merge_program *)
  (*       | erewrite mergeable_states_merge_context ]; try eassumption; *)
  (*       unfold merge_states_mem, merge_states_stack; *)
  (*       rewrite merge_stacks_cons_program; try eassumption; *)
  (*       match goal with *)
  (*       | Heq : Pointer.component pc1'' = Pointer.component pc1 |- _ => *)
  (*         rewrite Heq *)
  (*       end; *)
  (*       [| erewrite Register.invalidate_eq with (regs2 := regs1); [| congruence]]; *)
  (*       t_threeway_multisem_event_lockstep_program_step_call Hcomp1 Hmerge1. *)
  (*   - (* Return: case analysis on return point. *) *)
  (*     match goal with *)
  (*     | H1 : Pointer.component pc1'' = Pointer.component pc1, *)
  (*       H2 : Pointer.component pc2'' = Pointer.component pc2 |- _ => *)
  (*       rename H1 into Heq1; rename H2 into Heq2 *)
  (*     end. *)
  (*     destruct (CS.is_program_component s2copy ic) eqn:Hcomp2; *)
  (*       [| apply negb_false_iff in Hcomp2]; *)
  (*       [ rewrite (mergeable_states_merge_program _ Hmerge2); try assumption *)
  (*       | rewrite (mergeable_states_merge_context _ Hmerge2); try assumption ]; *)
  (*       unfold merge_states_mem, merge_states_stack; simpl; *)
  (*       [ pose proof is_program_component_in_domm Hcomp2 Hmerge2 as Hcomp2''; *)
  (*         erewrite merge_frames_program; try eassumption *)
  (*       | erewrite merge_frames_context; try eassumption ]; *)
  (*       [ rewrite Heq1 Heq2 | rewrite Heq1 ]; *)
  (*       [| erewrite Register.invalidate_eq with (regs2 := regs1); [| congruence]]; *)
  (*       t_threeway_multisem_event_lockstep_program_step_return Hcomp1 Hmerge1. *)
  (* Qed. *)
Admitted.

Corollary threeway_multisem_event_lockstep_program s1 s1'' e s2 s2'' :
  is_program_component s1 lrsplit ->
  mergeable_states p c p' c' prog prog'' s1 s1'' ->
  Step sem   s1   (e :: nil) s2   ->
  Step sem'' s1'' (e :: nil) s2'' ->
  Step sem'  (merge_states lrsplit s1 s1'') (e :: nil) (merge_states lrsplit s2 s2'') /\
  mergeable_states p c p' c' prog prog'' s2 s2''.
Proof.
  split.
  - now apply threeway_multisem_event_lockstep_program_step.
  - eapply threeway_multisem_event_lockstep_program_mergeable; eassumption.
Qed.

End THREEWAY_MULTISEM_1.

Section THREEWAY_MULTISEM_2.

Variables p c p' c' : program.

Variable lrsplit : split.

Hypothesis Hcompat  : asm_compatible lrsplit p  c.
Hypothesis Hcompat' : asm_compatible lrsplit p' c'.

Variables prog prog' prog'' : program.

Hypothesis Hprog   : link p  c  = Some prog.
Hypothesis Hprog'  : link p  c' = Some prog'.
Hypothesis Hprog'' : link p' c' = Some prog''.

Let sem   := semantics prog.
Let sem'  := semantics prog'.
Let sem'' := semantics prog''.

Lemma threeway_multisem_mergeable s1 s1'' t s2 s2'' :
  mergeable_states p c p' c' prog prog'' s1 s1'' ->
  Star sem   s1   t s2   ->
  Star sem'' s1'' t s2'' ->
  mergeable_states p c p' c' prog prog'' s2 s2''.
Proof.
  intros Hmerg Hstar12 Hstar12''. inversion Hmerg.
  econstructor; try eassumption;
    eapply star_trans; try eassumption; reflexivity.
Qed.

Lemma threeway_multisem_star_E0 s1 s1'' s2 s2'':
  mergeable_states p c p' c' prog prog'' s1 s1'' ->
  Star sem   s1   E0 s2   ->
  Star sem'' s1'' E0 s2'' ->
  Star sem'  (merge_states lrsplit s1 s1'') E0 (merge_states lrsplit s2 s2'').
  (* Proof. *)
  (*   intros H H0 H1. *)
  (*   inversion H as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
  (*   destruct (CS.is_program_component s1 ic) eqn:Hprg_component. *)
  (*   - now apply threeway_multisem_star_E0_program. *)
  (*   - rewrite (merge_states_sym H); try assumption. *)
  (*     rewrite (merge_states_sym (threeway_multisem_mergeable H H0 H1)); try assumption. *)
  (*     assert (Hlinkable : linkable ip ic) by now destruct Hmergeable_ifaces. *)
  (*     unfold ic in Hlinkable. rewrite Hifacec in Hlinkable. *)
  (*     pose proof (program_linkC Hwfp Hwfc' Hlinkable) as Hprg_linkC'. *)
  (*     unfold sem', prog'. *)
  (*     rewrite Hprg_linkC'. *)
  (*     pose proof (program_linkC Hwfp' Hwfc') as Hprg_linkC''; rewrite <- Hifacep in Hprg_linkC''. *)
  (*     unfold sem'', prog'' in H1. *)
  (*     rewrite (Hprg_linkC'' Hlinkable) in H1. *)
  (*     pose proof (program_linkC Hwfp Hwfc) as Hprg_linkC; rewrite Hifacec in Hprg_linkC. *)
  (*     unfold sem, prog in H0. *)
  (*     rewrite (Hprg_linkC Hlinkable) in H0. *)
  (*     pose proof (threeway_multisem_star_E0_program) as Hmultisem. *)
  (*     specialize (Hmultisem c' p' c p). *)
  (*     rewrite <- Hifacep, <- Hifacec in Hmultisem. *)
  (*     specialize (Hmultisem s1'' s1 s2'' s2). *)
  (*     assert (His_prg_component'' : CS.is_program_component s1'' (prog_interface p)). *)
  (*     { eapply mergeable_states_context_to_program. *)
  (*       apply H. *)
  (*       unfold CS.is_program_component in Hprg_component. apply negbFE in Hprg_component. *)
  (*       assumption. *)
  (*     } *)
  (*     assert (Hmerg_sym : mergeable_states c' p' c p s1'' s1). *)
  (*     { inversion H. *)
  (*       econstructor; *)
  (*         try rewrite <- (Hprg_linkC Hlinkable); try rewrite <- (Hprg_linkC'' Hlinkable); eauto. *)
  (*       apply mergeable_interfaces_sym; congruence. *)
  (*     } *)
  (*     specialize (Hmultisem His_prg_component'' Hmerg_sym H1 H0). *)
  (*     assumption. *)
  (* Qed. *)
Admitted.

Lemma threeway_multisem_event_lockstep s1 s1'' e s2 s2'' :
  mergeable_states p c p' c' prog prog'' s1 s1'' ->
  Step sem   s1   (e :: nil) s2   ->
  Step sem'' s1'' (e :: nil) s2'' ->
  Step sem'  (merge_states lrsplit s1 s1'') (e :: nil) (merge_states lrsplit s2 s2'') /\
  mergeable_states p c p' c' prog prog'' s2 s2''.
  (* Proof. *)
  (*   intros Hmerge1 Hstep12 Hstep12''. *)
  (*   inversion Hmerge1 as [? ? ? Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec Hprog_is_closed _ Hini H1 Hstar H2]. *)
  (*   destruct (CS.is_program_component s1 ic) eqn:Hcase. *)
  (*   - now apply threeway_multisem_event_lockstep_program. *)
  (*   - inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*     pose proof @threeway_multisem_event_lockstep_program c' p' c p as H. *)
  (*     rewrite <- Hifacec, <- Hifacep in H. *)
  (*     specialize (H s1'' s1 e s2'' s2). *)
  (*     assert (Hmerge11 := Hmerge1). *)
  (*     erewrite mergeable_states_sym in Hmerge11; try eassumption. *)
  (*     erewrite mergeable_states_sym; try eassumption. *)
  (*     unfold ip, ic; erewrite merge_states_sym; try eassumption. *)
  (*     assert (Hmerge2 : mergeable_states p c p' c' s2 s2''). *)
  (*     { inversion Hmerge1. *)
  (*       econstructor; try eassumption. *)
  (*       apply star_iff_starR; eapply starR_step; try eassumption. *)
  (*       apply star_iff_starR; eassumption. reflexivity. *)
  (*       apply star_iff_starR; eapply starR_step; try eassumption. *)
  (*       apply star_iff_starR; eassumption. reflexivity. } *)
  (*     rewrite (merge_states_sym Hmerge2); try assumption. *)
  (*     unfold sem', prog'; rewrite program_linkC; try congruence. *)
  (*     apply H; try assumption. *)
  (*     + unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn. *)
  (*       pose proof mergeable_states_pc_same_component Hmerge1 as Hpc. *)
  (*       destruct s1 as [[[? ?] ?] pc1]; destruct s1'' as [[[? ?] ?] pc1'']. *)
  (*       simpl in Hpc. *)
  (*       rewrite -Hpc. *)
  (*       unfold CS.is_program_component, CS.is_context_component, turn_of, CS.state_turn in Hcase. *)
  (*       destruct (CS.star_pc_domm _ _ Hwfp Hwfc Hmergeable_ifaces Hprog_is_closed Hini Hstar) as [Hdomm | Hdomm]. *)
  (*       apply domm_partition_notin_r with (ctx2 := ic) in Hdomm. *)
  (*       move: Hcase => /idP Hcase. rewrite Hdomm in Hcase. congruence. assumption. *)
  (*       now apply domm_partition_notin with (ctx1 := ip) in Hdomm. *)
  (*     + rewrite program_linkC; try assumption. *)
  (*       apply linkable_sym; congruence. *)
  (*     + rewrite program_linkC; try assumption. *)
  (*       now apply linkable_sym. *)
  (* Qed. *)
Admitted.

Theorem threeway_multisem_star_program s1 s1'' t s2 s2'' :
  is_program_component s1 lrsplit ->
  mergeable_states p c p' c' prog prog'' s1 s1'' ->
  Star sem   s1   t s2   ->
  Star sem'' s1'' t s2'' ->
  Star sem'  (merge_states lrsplit s1 s1'') t (merge_states lrsplit s2 s2'').
  (* Proof. *)
  (*   simpl in *. intros Hcomp1 Hmerge1 Hstar12. revert s1'' s2'' Hcomp1 Hmerge1. *)
  (*   apply star_iff_starR in Hstar12. *)
  (*   induction Hstar12 as [s | s1 t1 s2 t2 s3 ? Hstar12 IHstar12' Hstep23]; subst; *)
  (*     intros s1'' s2'' Hcomp1 Hmerge1 Hstar12''. *)
  (*   - eapply context_epsilon_star_merge_states; eassumption. *)
  (*   - rename s2'' into s3''. rename Hstar12'' into Hstar13''. *)
  (*     apply (star_app_inv (@CS.singleton_traces _)) in Hstar13'' *)
  (*       as [s2'' [Hstar12'' Hstar23'']]. *)
  (*     specialize (IHstar12' _ _ Hcomp1 Hmerge1 Hstar12''). *)
  (*     (* Apply instantiated IH and case analyze step trace. *) *)
  (*     apply star_trans with (t1 := t1) (s2 := merge_states ip ic s2 s2'') (t2 := t2); *)
  (*       [assumption | | reflexivity]. *)
  (*     apply star_iff_starR in Hstar12. *)
  (*     pose proof threeway_multisem_mergeable Hmerge1 Hstar12 Hstar12'' *)
  (*       as Hmerge2. *)
  (*     destruct t2 as [| e2 [| e2' t2]]. *)
  (*     + (* An epsilon step and comparable epsilon star. One is in the context and *)
  (*          therefore silent, the other executes and leads the MultiSem star. *) *)
  (*       eapply star_step in Hstep23; [| now apply star_refl | now apply eq_refl]. *)
  (*       exact (threeway_multisem_star_E0 Hmerge2 Hstep23 Hstar23''). *)
  (*     + (* The step generates a trace event, mimicked on the other side (possibly *)
  (*          between sequences of silent steps). *) *)
  (*       change [e2] with (E0 ** e2 :: E0) in Hstar23''. *)
  (*       apply (star_middle1_inv (@CS.singleton_traces _)) in Hstar23'' *)
  (*         as [s2''1 [s2''2 [Hstar2'' [Hstep23'' Hstar3'']]]]. *)
  (*       (* Prefix star. *) *)
  (*       pose proof star_refl CS.step (prepare_global_env (program_link p c)) s2 *)
  (*         as Hstar2. *)
  (*       pose proof threeway_multisem_star_E0 Hmerge2 Hstar2 Hstar2'' *)
  (*         as Hstar2'. *)
  (*       (* Propagate mergeability, step. *) *)
  (*       pose proof threeway_multisem_mergeable Hmerge2 Hstar2 Hstar2'' as Hmerge21. *)
  (*       pose proof threeway_multisem_event_lockstep Hmerge21 Hstep23 Hstep23'' *)
  (*         as [Hstep23' Hmerge22]. *)
  (*       (* Propagate mergeability, suffix star. *) *)
  (*       pose proof star_refl CS.step (prepare_global_env (program_link p c)) s3 *)
  (*         as Hstar3. *)
  (*       pose proof threeway_multisem_star_E0 Hmerge22 Hstar3 Hstar3'' as Hstar3'. *)
  (*       (* Compose. *) *)
  (*       exact (star_trans *)
  (*                (star_right _ _ Hstar2' Hstep23' (eq_refl _)) *)
  (*                Hstar3' (eq_refl _)). *)
  (*     + (* Contradiction: a step generates at most one event. *) *)
  (*       pose proof @CS.singleton_traces _ _ _ _ Hstep23 as Hcontra. *)
  (*       simpl in Hcontra. omega. *)
  (* Qed. *)
Admitted.

End THREEWAY_MULTISEM_2.

Section THREEWAY_MULTISEM_3.

Variables p c p' c' : program.

Variable lrsplit : split.

Hypothesis Hcompat  : asm_compatible lrsplit p  c.
Hypothesis Hcompat' : asm_compatible lrsplit p' c'.

Variables prog prog' prog'' : program.

Hypothesis Hprog   : link p  c  = Some prog.
Hypothesis Hprog'  : link p  c' = Some prog'.
Hypothesis Hprog'' : link p' c' = Some prog''.

Let sem   := semantics prog.
Let sem'  := semantics prog'.
Let sem'' := semantics prog''.

Theorem threeway_multisem_star s1 s1'' t s2 s2'' :
  mergeable_states p c p' c' prog prog'' s1 s1'' ->
  Star sem   s1   t s2   ->
  Star sem'' s1'' t s2'' ->
  Star sem'  (merge_states lrsplit s1 s1'') t (merge_states lrsplit s2 s2'').
  (* /\ mergeable_states ip ic s2 s2'' *)
  (* Proof. *)
  (*   intros Hmerge1 Hstar12 Hstar12''. *)
  (*   inversion Hmerge1 as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
  (*   destruct (CS.is_program_component s1 ic) eqn:Hcomp1. *)
  (*   - now apply threeway_multisem_star_program. *)
  (*   - apply negb_false_iff in Hcomp1. *)
  (*     apply (mergeable_states_context_to_program Hmerge1) *)
  (*       in Hcomp1. *)
  (*     assert (Hmerge2: mergeable_states p c p' c' s2 s2'') *)
  (*       by (eapply threeway_multisem_mergeable; eassumption). *)
  (*     rewrite program_linkC in Hstar12; try assumption; *)
  (*       last now destruct Hmergeable_ifaces. *)
  (*     rewrite program_linkC in Hstar12''; try assumption; *)
  (*       last now destruct Hmergeable_ifaces; rewrite -Hifacec -Hifacep. *)
  (*     rewrite program_linkC; try assumption; *)
  (*       last now destruct Hmergeable_ifaces; rewrite -Hifacec. *)
  (*     unfold ip, ic. *)
  (*     setoid_rewrite merge_states_sym at 1 2; try eassumption. *)
  (*     pose proof threeway_multisem_star_program as H. *)
  (*     specialize (H c' p' c p). *)
  (*     rewrite <- Hifacep, <- Hifacec in H. *)
  (*     specialize (H s1'' s1 t s2'' s2). *)
  (*     apply H; try assumption. *)
  (*     apply mergeable_states_sym in Hmerge1; try assumption; *)
  (*       try rewrite -Hifacec; try rewrite -Hifacep; try apply mergeable_interfaces_sym; *)
  (*         now auto. *)
  (* Qed. *)
Admitted.

Corollary star_simulation {s1 s1'' t s2 s2''} :
  mergeable_states p c p' c' prog prog'' s1 s1'' ->
  Star sem   s1   t s2   ->
  Star sem'' s1'' t s2'' ->
  Star sem'  (merge_states lrsplit s1 s1'') t (merge_states lrsplit s2 s2'') /\
  mergeable_states p c p' c' prog prog'' s2 s2''.
  (* Proof. *)
  (*   intros. split. *)
  (*   - now apply threeway_multisem_star. *)
  (*   - eapply threeway_multisem_mergeable; eassumption. *)
  (* Qed. *)
Admitted.

Theorem threeway_multisem_step_inv_program s1 s1'' t s2' :
  is_program_component s1 lrsplit ->
  mergeable_states p c p' c' prog prog'' s1 s1'' ->
  Step sem' (merge_states lrsplit s1 s1'') t s2' ->
exists s2,
  Step sem                      s1       t s2.
  (* Proof. *)
  (*   intros Hpc Hmerge Hstep. *)
  (*   inversion Hmerge as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
  (*   destruct s1 as [[[gps1 mem1] regs1] pc1]. *)
  (*   destruct s1'' as [[[gps1'' mem1''] regs1''] pc1'']. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmain_linkability. *)
  (*   assert (Hlinkable' := Hlinkable); rewrite Hifacep Hifacec in Hlinkable'. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp' Hwfc' Hlinkable' as Hmain_linkability'. *)
  (*   pose proof is_program_component_pc_in_domm Hpc Hmerge as Hdomm. *)
  (*   pose proof is_program_component_pc_in_domm Hpc Hmerge as Hdomm'. *)
  (*   pose proof CS.is_program_component_pc_notin_domm _ _ Hpc as Hnotin; unfold ic in Hnotin; *)
  (*   assert (Hmains : linkable_mains p c') *)
  (*     by (apply linkable_implies_linkable_mains; congruence). *)
  (*   rewrite (mergeable_states_merge_program _ Hmerge) in Hstep; *)
  (*     try assumption. *)
  (*   pose proof linking_well_formedness Hwfp Hwfc Hlinkable as Hwfprog. *)
  (*   pose proof linking_well_formedness Hwfp' Hwfc' Hlinkable' as Hwfprog'. *)
  (*   assert (Hlinkable'' := Hlinkable); rewrite Hifacec in Hlinkable''. *)
  (*   pose proof linking_well_formedness Hwfp Hwfc' Hlinkable'' as Hwfprog''. *)

  (*   inversion Hstep; subst; *)
  (*     t_threeway_multisem_step_inv_program gps1 gps1'' Hmerge Hnotin Hifacec. *)
  (* Qed. *)
Admitted.

End THREEWAY_MULTISEM_3.

(* Theorems on initial states for main simulation. *)

Section THREEWAY_MULTISEM_4.

Variables p c p' c' : program.

Variable lrsplit : split.

Hypothesis Hcompat  : asm_compatible lrsplit p  c.
Hypothesis Hcompat' : asm_compatible lrsplit p' c'.

Variables prog prog' prog'' : program.

Hypothesis Hprog   : link p  c  = Some prog.
Hypothesis Hprog'  : link p  c' = Some prog'.
Hypothesis Hprog'' : link p' c' = Some prog''.

Let sem   := semantics prog.
Let sem'  := semantics prog'.
Let sem'' := semantics prog''.

Lemma initial_states_mergeability {s s''} :
  initial_state prog   s   ->
  initial_state prog'' s'' ->
  mergeable_states p c p' c' prog prog'' s s''.
Proof.
  intros Hini Hini''.
  econstructor;
    try eassumption;
    now apply star_refl.
Qed.

Lemma match_initial_states {s s''} :
  initial_state prog   s   ->
  initial_state prog'' s'' ->
  initial_state prog'  (merge_states lrsplit s s'') /\
  mergeable_states p c p' c' prog prog'' s s''.
Proof.
  intros Hini Hini''.
  pose proof initial_states_mergeability Hini Hini'' as Hmerge.
  split; [| assumption].
  inversion Hini as [m ge rs Hmem Hstack];
    inversion Hini'' as [m'' ge'' rs'' Hmem'' Hstack''];
    subst.
  unfold merge_states. simpl.
  assert (REGS : merge_registers lrsplit rs rs'' m =
            (((Pregmap.init Vundef) # PC
              <- (Genv.symbol_address (Genv.globalenv prog') (prog_main prog') Ptrofs.zero)) # X2
              <- Vnullptr) # X1
              <- Vnullptr).
  {
    unfold merge_registers.
    (* apply link_prog_inv in Hprog' as [Hmain' Hprog']. *)
    admit.
  }
  rewrite REGS. constructor.
  (*   intros Hini Hini''. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   pose proof initial_states_mergeability Hini Hini'' as Hmerge. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmain_linkability. *)
  (*   simpl in *. unfold CS.initial_state in *. subst. *)
  (*   split; last assumption. *)
  (*   (* Expose structure of initial states. *) *)
  (*   rewrite !CS.initial_machine_state_after_linking; try congruence; *)
  (*     last (apply interface_preserves_closedness_r with (p2 := c); try assumption; *)
  (*           now apply interface_implies_matching_mains). *)
  (*   unfold merge_states, merge_memories, merge_registers, merge_pcs; simpl. *)
  (*   (* Memory simplifictions. *) *)
  (*   rewrite (prepare_procedures_memory_left Hlinkable). *)
  (*   unfold ip. erewrite Hifacep at 1. rewrite Hifacep Hifacec in Hlinkable. *)
  (*   rewrite (prepare_procedures_memory_right Hlinkable). *)
  (*   (* Case analysis on main and related simplifications. *) *)
  (*   destruct (Component.main \in domm ip) eqn:Hcase; *)
  (*     rewrite Hcase. *)
  (*   - pose proof domm_partition_notin_r _ _ Hmergeable_ifaces _ Hcase as Hnotin. *)
  (*     rewrite (CS.prog_main_block_no_main _ Hwfc Hnotin). *)
  (*     rewrite Hifacec in Hnotin. now rewrite (CS.prog_main_block_no_main _ Hwfc' Hnotin). *)
  (*   - (* Symmetric case. *) *)
  (*     assert (Hcase' : Component.main \in domm ic). *)
  (*     { pose proof domm_partition_program_link_in_neither Hwfp Hwfc Hprog_is_closed as H. *)
  (*       rewrite Hcase in H. *)
  (*       destruct (Component.main \in domm ic) eqn:Hcase''. *)
  (*       - reflexivity. *)
  (*       - rewrite Hcase'' in H. *)
  (*         exfalso; now apply H. *)
  (*     } *)
  (*     pose proof domm_partition_notin _ _ Hmergeable_ifaces _ Hcase' as Hnotin. *)
  (*     rewrite (CS.prog_main_block_no_main _ Hwfp Hnotin). *)
  (*     rewrite Hifacep in Hnotin. now rewrite (CS.prog_main_block_no_main _ Hwfp' Hnotin). *)
  (* Qed. *)
Admitted.

End THREEWAY_MULTISEM_4.

(* Remaining theorems for main simulation.  *)
Section THREEWAY_MULTISEM_5.

Variables p c p' c' : program.

Variable rlsplit : split.

(* Hypothesis Hcompat  : asm_compatible s p  c. *)
(* Hypothesis Hcompat' : asm_compatible s p' c'. *)

Variables prog prog' prog'' : program.

Hypothesis Hprog   : link p  c  = Some prog.
Hypothesis Hprog'  : link p  c' = Some prog'.
Hypothesis Hprog'' : link p' c' = Some prog''.

Let sem   := semantics prog.
Let sem'  := semantics prog'.
Let sem'' := semantics prog''.

Theorem match_final_states s s'' n :
  mergeable_states p c p' c' prog prog'' s s'' ->
  final_state prog   s                            n ->
  final_state prog'' s''                          n ->
  final_state prog'  (merge_states rlsplit s s'') n.
Proof.
  destruct s as [gps regs mem | gps regs mem];
    destruct s'' as [gps'' regs'' mem'' | gps'' regs'' mem''];
    intros Hmergeable Hfinal Hfinal'';
    try now inversion Hfinal.
  simpl.
  inversion Hfinal; inversion Hfinal''; subst.
  simpl. constructor.
  - unfold merge_registers.
    destruct (Mem.val_compartment mem (regs PC)) as [cp |].
    + destruct (rlsplit cp); assumption.
    + assumption. (* should not happen, but the fallback works *)
  - unfold merge_registers.
    destruct (Mem.val_compartment mem (regs PC)) as [cp |].
    + destruct (rlsplit cp); assumption.
    + assumption. (* should not happen, but the fallback works *)
Qed.

Theorem match_nofinal s s'' n n'' n' :
  mergeable_states p c p' c' prog prog'' s s'' ->
  ~ final_state prog   s                            n   ->
  ~ final_state prog'' s''                          n'' ->
  ~ final_state prog'  (merge_states rlsplit s s'') n'.
Proof.
    (* destruct s as [[[gps mem] regs] pc]. *)
    (* destruct s'' as [[[gps'' mem''] regs''] pc'']. *)
    (* unfold final_state. simpl. unfold merge_pcs. *)
    (* intros Hmerge Hfinal Hfinal'' Hfinal'. *)
    (* inversion Hmerge as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _ ]. *)
    (* inversion Hmergeable_ifaces as [Hlinkable _]. *)
    (* destruct (Pointer.component pc \in domm ip) eqn:Hcase. *)
    (* - apply execution_invariant_to_linking with (c2 := c) in Hfinal'; try easy. *)
    (*   + congruence. *)
    (*   + apply linkable_implies_linkable_mains; congruence. *)
    (*   + apply linkable_implies_linkable_mains; congruence. *)
    (* - (* Symmetric case. *) *)
    (*   unfold prog', prog'' in *. *)
    (*   rewrite program_linkC in Hfinal'; try congruence. *)
    (*   rewrite program_linkC in Hfinal''; try congruence. *)
    (*   apply execution_invariant_to_linking with (c2 := p') in Hfinal'; try easy. *)
    (*   + apply linkable_sym; congruence. *)
    (*   + apply linkable_sym; congruence. *)
    (*   + apply linkable_mains_sym, linkable_implies_linkable_mains; congruence. *)
    (*   + apply linkable_mains_sym, linkable_implies_linkable_mains; congruence. *)
    (*   + setoid_rewrite <- (mergeable_states_pc_same_component Hmerge). *)
    (*     rewrite <- Hifacec. *)
    (*     apply negb_true_iff in Hcase. *)
    (*     now eapply (mergeable_states_notin_to_in Hmerge). *)
  (* Qed. *)
Admitted.

Lemma match_nostep s s'' :
  mergeable_states p c p' c' prog prog'' s s'' ->
  Nostep sem   s   ->
  Nostep sem'' s'' ->
  Nostep sem'  (merge_states rlsplit s s'').
Proof.
  rename s into s1. rename s'' into s1''.
  intros Hmerge Hstep Hstep'' t s2' Hstep'.
    (* inversion Hmerge as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
    (* inversion Hmergeable_ifaces as [Hlinkable _]. *)
    (* inversion Hmergeable_ifaces as [Hlinkable' _]; rewrite Hifacep Hifacec in Hlinkable'. *)
    (* pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmain_linkability. *)
    (* pose proof linkable_implies_linkable_mains Hwfp' Hwfc' Hlinkable' as Hmain_linkability'. *)
    (* destruct (CS.is_program_component s1 ic) eqn:Hcase. *)
    (* - pose proof threeway_multisem_step_inv_program Hcase Hmerge Hstep' *)
    (*     as [s2 Hcontra]. *)
    (*   specialize (Hstep t s2). contradiction. *)
    (* - (* Symmetric case. *) *)
    (*   apply negb_false_iff in Hcase. *)
    (*   pose proof mergeable_states_context_to_program Hmerge Hcase as Hcase'. *)
    (*   pose proof proj1 (mergeable_states_sym _ _ _ _ _ _) Hmerge as Hmerge'. *)
    (*   pose proof @threeway_multisem_step_inv_program c' p' c p as H. *)
    (*   rewrite -Hifacec -Hifacep in H. *)
    (*   specialize (H s1'' s1 t s2' Hcase' Hmerge'). *)
    (*   rewrite program_linkC in H; try assumption; [| apply linkable_sym; congruence]. *)
    (*   rewrite Hifacec Hifacep in H. *)
    (*   erewrite merge_states_sym with (p := c') (c := p') (p' := c) (c' := p) in H; *)
    (*     try eassumption; try now symmetry. *)
    (*   rewrite -Hifacec -Hifacep in H. *)
    (*   specialize (H Hstep'). *)
    (*   destruct H as [s2'' Hcontra]. *)
    (*   specialize (Hstep'' t s2''). *)
    (*   unfold sem'', prog'' in Hstep''; rewrite program_linkC in Hstep''; try assumption. *)
    (*   contradiction. *)
  (* Qed. *)
Admitted.

End THREEWAY_MULTISEM_5.

Section RECOMBINATION.

Variables p c p' c' : program.

(* Hypothesis Hwfp  : well_formed_program p. *)
(* Hypothesis Hwfc  : well_formed_program c. *)
(* Hypothesis Hwfp' : well_formed_program p'. *)
(* Hypothesis Hwfc' : well_formed_program c'. *)

(* Hypothesis Hmergeable_ifaces : *)
(*   mergeable_interfaces (prog_interface p) (prog_interface c). *)

(* Hypothesis Hifacep  : prog_interface p  = prog_interface p'. *)
(* Hypothesis Hifacec  : prog_interface c  = prog_interface c'. *)

(* Hypothesis Hprog_is_closed  : closed_program (program_link p  c ). *)
(* Hypothesis Hprog_is_closed' : closed_program (program_link p' c'). *)

(* Let ip := prog_interface p. *)
(* Let ic := prog_interface c. *)

Variable lrsplit : split.

Hypothesis Hcompat  : asm_compatible lrsplit p  c.
Hypothesis Hcompat' : asm_compatible lrsplit p' c'.

Variables prog prog' prog'' : program.

Hypothesis Hprog   : link p  c  = Some prog.
Hypothesis Hprog'  : link p  c' = Some prog'.
Hypothesis Hprog'' : link p' c' = Some prog''.

Let sem   := semantics prog.
Let sem'  := semantics prog'.
Let sem'' := semantics prog''.

(* asm_program_has_initial_trace W t *)
(* asm_program_has_initial_trace W'' t *)

Theorem recombination_prefix m :
  does_prefix sem   m ->
  does_prefix sem'' m ->
  does_prefix sem'  m.
Proof.
  unfold does_prefix.
  intros [b [Hbeh Hprefix]] [b'' [Hbeh'' Hprefix'']].
  assert (Hst_beh := Hbeh). assert (Hst_beh'' := Hbeh'').
  apply program_behaves_inv in Hst_beh   as [s1   [Hini1   Hst_beh  ]].
  apply program_behaves_inv in Hst_beh'' as [s1'' [Hini1'' Hst_beh'']].
  destruct m as [tm nm | tm | tm].
  - destruct b   as [t   n   | ? | ? | ?]; try contradiction.
    destruct b'' as [t'' n'' | ? | ? | ?]; try contradiction.
    simpl in Hprefix, Hprefix''. destruct Hprefix. destruct Hprefix''. subst t t'' n n''.
    inversion Hst_beh   as [? s2   ? Hstar12   Hfinal2   | | |]; subst.
    inversion Hst_beh'' as [? s2'' ? Hstar12'' Hfinal2'' | | |]; subst.
    exists (Terminates tm nm). split; [| now constructor].
    pose proof match_initial_states _ _ _ _ _ Hcompat Hcompat' _ _ _
      Hprog Hprog' Hprog'' Hini1 Hini1'' as [Hini1' Hmerge1].
    pose proof star_simulation
      _ _ _ _ _ Hcompat Hcompat' _ _ _ Hprog Hprog' Hprog''
      Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2].
    apply program_runs with (s := merge_states lrsplit s1 s1'');
      [simpl; assumption |].
    apply state_terminates with (s' := merge_states lrsplit s2 s2'');
      [assumption |].
    (* now apply match_final_states with (p' := p'). *)
    eapply match_final_states with (p' := p'); eassumption.
  - destruct b   as [? | ? | ? | t  ]; try contradiction.
    destruct b'' as [? | ? | ? | t'']; try contradiction.
    simpl in Hprefix, Hprefix''. subst t t''.
    inversion Hst_beh   as [| | | ? s2   Hstar12   Hstep2   Hfinal2  ]; subst.
    inversion Hst_beh'' as [| | | ? s2'' Hstar12'' Hstep2'' Hfinal2'']; subst.
    exists (Goes_wrong tm). split; [| reflexivity].
    pose proof match_initial_states
      _ _ _ _ _ Hcompat Hcompat' _ _ _ Hprog Hprog' Hprog''
      Hini1 Hini1'' as [Hini' Hmerge1].
    pose proof star_simulation
      _ _ _ _ _ Hcompat Hcompat' _ _ _ Hprog Hprog' Hprog''
      Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2].
    apply program_runs with (s := merge_states lrsplit s1 s1'');
      [assumption |].
    apply state_goes_wrong with (s' := merge_states lrsplit s2 s2'');
      [assumption | |].
    (* + eapply match_nostep; eassumption. *)
    (* + eapply match_nofinal; eassumption. *)
    + eapply (match_nostep p c p' c'); eassumption.
    + intros r. eapply (@match_nofinal p c p' c'); now eauto.
  - (* Here we talk about the stars associated to the behaviors, without
       worrying now about connecting them to the existing initial states. *)
    destruct (behavior_prefix_star Hbeh Hprefix) as [s1_ [s2 [Hini1_ Hstar12]]].
    destruct (behavior_prefix_star Hbeh'' Hprefix'') as [s1''_ [s2'' [Hini1''_ Hstar12'']]].
    pose proof match_initial_states
      _ _ _ _ _ Hcompat Hcompat' _ _ _ Hprog Hprog' Hprog''
      Hini1_ Hini1''_ as [Hini1' Hmerge1].
    pose proof star_simulation
      _ _ _ _ _ Hcompat Hcompat' _ _ _ Hprog Hprog' Hprog''
      Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2].
    eapply program_behaves_finpref_exists;
      [| now apply Hstar12'].
    assumption.
(* TODO Fix shelved variables *)
Unshelve.
  all:auto.
Qed.

End RECOMBINATION.

Corollary recomposition:
  forall W W'' p1 p2 p1'' p2'' lrsplit t,
    link p1 p2 = Some W ->
    link p1'' p2'' = Some W'' ->
    asm_compatible lrsplit p1 p2 ->
    asm_compatible lrsplit p1'' p2'' ->
    asm_program_has_initial_trace W t ->
    asm_program_has_initial_trace W'' t ->
  exists W',
    link p1 p2'' = Some W' /\
    asm_program_has_initial_trace W' t.
Admitted.
