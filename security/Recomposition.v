Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm.

(* Require Import Coqlib. *)
(* Require Import Maps. *)
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

(* CompCertExtensions *)

Require Import Behaviors.

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

Definition does_prefix x m := exists b, program_behaves x b /\ prefix m b.

(* CS *)

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

(* Recombination *)

Require Import Split.

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

Definition remap {X : Type} (s : side) (t : Maps.PTree.t X) (e : positive * X) : Maps.PTree.t X :=
  let '(b, x) := e in
  let b' := match s with
            | Left => 2 * b
            | Right => 2 * b + 1
            end%positive in
  Maps.PTree.set b' x t.

(* TODO Actually go from [memval] to [val], remap blocks according to the side
   and leave the rest intact (see [memory_chunk], [AST]) *)
Definition merge_value (s : side) (v : memval) : memval :=
  v.

Definition merge_contents (m m'' : mem) :=
  let (def, c) := Mem.mem_contents m in
  let (def'', c'') := Mem.mem_contents m'' in
  (* let set_left t '(b, o2mv) := Maps.PTree.set (2 * b) o2mv t in (* TODO Merge values *) *)
  (* let set_right t '(b, o2mv) := Maps.PTree.set (2 * b + 1) o2mv t in (* TODO Merge values *) *)
  (* let celts := Maps.PTree.elements c in *)
  (* let celts'' := Maps.PTree.elements c'' in *)
  (* let _ := List.fold_left (fun acc '(b, y) => Maps.PTree.set b y acc) celts (Maps.PTree.empty _) in *)
  (* not there yet? -- filter things not in left/right! *)
  let t0 := List.fold_left (remap Left) (Maps.PTree.elements c) (Maps.PTree.empty _) in
  let t1 := List.fold_left (remap Right) (Maps.PTree.elements c'') t0 in
  (def, t1).
  (* TODO Not a pure map function *)
  (* m. *)
  (* let cnew := Maps.PMap.map (Maps.ZMap.map (merge_value Left)) c in *)
  (* let cnew'' := Maps.PMap.map (Maps.ZMap.map (merge_value Left)) c'' in *)
  (* cnew. (* TODO Merge [cnew] and [cnew''] *) *)

Definition merge_access (m m'' : mem) :=
  let '(def, a) := Mem.mem_access m in
  let '(def'', a'') := Mem.mem_access m'' in (* default discarded *)
  (* TODO Remap and combine block identifiers according to side *)
  let t0 := List.fold_left (remap Left) (Maps.PTree.elements a) (Maps.PTree.empty _) in
  let t1 := List.fold_left (remap Right) (Maps.PTree.elements a'') t0 in
  (def, t1).


Definition merge_compartments (m m'' : mem) :=
  let c := Mem.mem_compartments m in
  let c'' := Mem.mem_compartments m'' in
  (* TODO Remap and combine block identifiers according to side
     Filter *)
  let t0 := List.fold_left (remap Left) (Maps.PTree.elements c) (Maps.PTree.empty _) in
  let t1 := List.fold_left (remap Right) (Maps.PTree.elements c'') t0 in
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

Lemma initial_states_mergeability s s'' :
  initial_state prog   s   ->
  initial_state prog'' s'' ->
  mergeable_states p c p' c' prog prog'' s s''.
Proof.
  (*   simpl. unfold CS.initial_state. *)
  (*   intros Hini Hini''. *)
  (*   apply mergeable_states_intro with (s0 := s) (s0'' := s'') (t := E0); subst; *)
  (*     try assumption; *)
  (*     reflexivity || now apply star_refl. *)
  (* Qed. *)
Admitted.

Lemma match_initial_states s s'' :
  initial_state prog   s   ->
  initial_state prog'' s'' ->
  initial_state prog'  (merge_states lrsplit s s'') /\
  mergeable_states p c p' c' prog prog'' s s''.
Proof.
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
  (*   destruct s as [[[gps mem] regs] pc]. *)
  (*   destruct s'' as [[[gps'' mem''] regs''] pc'']. *)
  (*   unfold final_state. simpl. unfold merge_pcs. *)
  (*   intros Hmerge Hfinal Hfinal''. *)
  (*   inversion Hmerge as [_ _ _ Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec _ _ _ _ _ _]. *)
  (*   inversion Hmergeable_ifaces as [Hlinkable _]. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp Hwfc Hlinkable as Hmain_linkability. *)
  (*   assert (Hlinkable' := Hlinkable); rewrite Hifacep Hifacec in Hlinkable'. *)
  (*   pose proof linkable_implies_linkable_mains Hwfp' Hwfc' Hlinkable' as Hmain_linkability'. *)
  (*   destruct (Pointer.component pc \in domm ip) eqn:Hcase. *)
  (*   - apply execution_invariant_to_linking with (c1 := c); try easy. *)
  (*     + congruence. *)
  (*     + apply linkable_implies_linkable_mains; congruence. *)
  (*   - (* Symmetric case. *) *)
  (*     unfold prog', prog'' in *. *)
  (*     rewrite program_linkC in Hfinal''; try congruence. *)
  (*     rewrite program_linkC; try congruence. *)
  (*     apply linkable_sym in Hlinkable. *)
  (*     apply linkable_mains_sym in Hmain_linkability. *)
  (*     apply linkable_mains_sym in Hmain_linkability'. *)
  (*     apply execution_invariant_to_linking with (c1 := p'); try congruence. *)
  (*     + apply linkable_implies_linkable_mains; congruence. *)
  (*     + setoid_rewrite <- (mergeable_states_pc_same_component Hmerge). *)
  (*       rewrite <- Hifacec. *)
  (*       apply negb_true_iff in Hcase. *)
  (*       now apply (mergeable_states_notin_to_in Hmerge). *)
  (* Qed. *)
Admitted.

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
    (* rename s into s1. rename s'' into s1''. *)
    (* intros Hmerge Hstep Hstep'' t s2' Hstep'. *)
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

Variable rlsplit : split.

Hypothesis Hcompat  : asm_compatible rlsplit p  c.
Hypothesis Hcompat' : asm_compatible rlsplit p' c'.

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
    inversion Hst_beh   as [? s2   Hstar12   Hfinal2   | | |]; subst.
    inversion Hst_beh'' as [? s2'' Hstar12'' Hfinal2'' | | |]; subst.
    exists (Terminates tm nm). split; [| now constructor].
    pose proof match_initial_states _ _ _ _ _ Hcompat Hcompat' _ _ _
      Hprog Hprog' Hprog'' _ _ Hini1 Hini1'' as [Hini1' Hmerge1].
    pose proof star_simulation Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2].
    apply program_runs with (s := merge_states ip ic s1 s1'');
      first assumption.
      apply state_terminates with (s' := merge_states ip ic s2 s2'');
  (*       first assumption. *)
  (*     now apply match_final_states with (p' := p'). *)
  (*   - destruct b   as [? | ? | ? | t  ]; try contradiction. *)
  (*     destruct b'' as [? | ? | ? | t'']; try contradiction. *)
  (*     simpl in Hprefix, Hprefix''. subst t t''. *)
  (*     inversion Hst_beh   as [| | | ? s2   Hstar12   Hstep2   Hfinal2  ]; subst. *)
  (*     inversion Hst_beh'' as [| | | ? s2'' Hstar12'' Hstep2'' Hfinal2'']; subst. *)
  (*     exists (Goes_wrong tm). split; last reflexivity. *)
  (*     pose proof match_initial_states Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec *)
  (*          Hprog_is_closed Hprog_is_closed' Hini1 Hini1'' as [Hini' Hmerge1]. *)
  (*     pose proof star_simulation Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2]. *)
  (*     apply program_runs with (s := merge_states ip ic s1 s1''); *)
  (*       first assumption. *)
  (*     apply state_goes_wrong with (s' := merge_states ip ic s2 s2''); *)
  (*       first assumption. *)
  (*     + eapply match_nostep; eassumption. *)
  (*     + eapply match_nofinal; eassumption. *)
  (*   - (* Here we talk about the stars associated to the behaviors, without *)
  (*        worrying now about connecting them to the existing initial states. *) *)
  (*     destruct (CS.behavior_prefix_star Hbeh Hprefix) as [s1_ [s2 [Hini1_ Hstar12]]]. *)
  (*     destruct (CS.behavior_prefix_star Hbeh'' Hprefix'') as [s1''_ [s2'' [Hini1''_ Hstar12'']]]. *)
  (*     pose proof match_initial_states Hwfp Hwfc Hwfp' Hwfc' Hmergeable_ifaces Hifacep Hifacec *)
  (*          Hprog_is_closed Hprog_is_closed' Hini1_ Hini1''_ as [Hini1' Hmerge1]. *)
  (*     pose proof star_simulation Hmerge1 Hstar12 Hstar12'' as [Hstar12' Hmerge2]. *)
  (*     eapply program_behaves_finpref_exists; *)
  (*       last now apply Hstar12'. *)
  (*     assumption. *)
  (* Qed. *)
  Admitted.

End RECOMBINATION.

Corollary recomposition:
  forall W W'' p1 p2 p1'' p2'' rlsplit t,
    link p1 p2 = Some W ->
    link p1'' p2'' = Some W'' ->
    asm_compatible rlsplit p1 p2 ->
    asm_compatible rlsplit p1'' p2'' ->
    asm_program_has_initial_trace W t ->
    asm_program_has_initial_trace W'' t ->
  exists W',
    link p1 p2'' = Some W' /\
    asm_program_has_initial_trace W' t.
