Require Import String.
Require Import Coqlib Maps Errors.
Require Import AST Linking Smallstep Events Behaviors Memory Values.

Require Import Csyntax Ctypes Ctyping Csem.
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
  | Kseq s k' => remove_until_right k'
  | Kcall f en ctx ty k' =>
      match s (comp_of f) with
      | Right => (* keep_until_left *) k
      | Left => remove_until_right k'
      end
  | _ => Kstop (* TODO!! *)
  end.
    (* with *)
    (* keep_until_left (k: cont) := *)
    (*   match k with *)
    (*   | Kseq s k' => Kseq s (keep_until_left k') *)
    (*   | *)

Inductive right_cont_injection: cont -> cont -> Prop :=
| right_cont_injection_kstop: right_cont_injection Kstop Kstop
| right_cont_injection_kseq: forall s k1 k2,
    right_cont_injection k1 k2 ->
    right_cont_injection (Kseq s k1) (Kseq s k2) (* TODO: write other cases *)
| right_cont_injection_kcall_left: forall f1 f2 en1 en2 ctx1 ctx2 ty1 ty2 k1 k2,
    s (comp_of f1) = Left ->
    s (comp_of f2) = Left ->
    right_cont_injection (remove_until_right k1) (remove_until_right k2) ->
      (* might be the same type?*)
    right_cont_injection (Kcall f1 en1 ctx1 ty1 k1) (Kcall f2 en2 ctx2 ty2 k2)
.

 (* Analogous to: [partialize ctx scs1 = partialize ctx scs2] with
    [ctx] giving us the [Left] part (the program part). Partialize keeps the context part
    and discards the program part.

  [right_state_injection] should relate the context part of the two states, and ignore
  the program part of the two states.
  *)
Variant right_executing_injection: state -> state -> Prop :=
| inject_states: forall f s k1 k2 en m1 m2,
    (* we forget about program memories but require injection of context memories *)
    right_mem_injection m1 m2 ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection k1 k2 ->

    right_execution_injection (State f s k1 en m1) (State f s k2 en m2)
| inject_exprstates: forall f e k1 k2 en m1 m2,
    (* we forget about program memories but require injection of context memories *)
    right_mem_injection m1 m2 ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection k1 k2 ->

    right_execution_injection (ExprState f e k1 en m1) (ExprState f e k2 en m2)
| inject_callstates: forall f vs k1 k2 m1 m2,
    (* we forget about program memories but require injection of context memories *)
    right_mem_injection m1 m2 ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection k1 k2 ->

    right_execution_injection (Callstate f vs k1 m1) (Callstate f vs k2 m2)
| inject_returnstates: forall v k1 k2 m1 m2 ty cp,
    (* we forget about program memories but require injection of context memories *)
    right_mem_injection m1 m2 ->

    (* we forget about program parts of the continuation but require injection of
       context continuation *)
    right_cont_injection k1 k2 ->

    right_execution_injection (Returnstate v k1 m1 ty cp) (Returnstate v k2 m2 ty cp)
| inject_stuckstates:
    right_execution_injection Stuckstate Stuckstate.


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


    right_mem_injection (memory_of st1) (memory_of st2) ->
    (* we put holes in place of context information in the stack *)
    pgps = to_partial_stack gps (domm ctx) C ->

    partial_state ctx [CState C, gps, mem, k, e, arg] (CC (C, pgps, pmem)).



Lemma parallel_concrete p1 p2 scs1 scs2:
  left_side s p1 -> (* use definitions from RSC.v *)
  left_side s p2 -> (* use definitions from RSC.v *)
  partial_state_equivalent s scs1 scs2 -> (* to define --> using memory injections? *)
  pc_in_left_part scs1 -> (* to define *)
  CS.kstep (prepare_global_env (program_link p p1)) scs1 t scs1' -> (* use step of Csem instead *)
  exists2 scs2',
    CS.kstep (prepare_global_env (program_link p p2)) scs2 t scs2' /\ (* use step of Csem instead *)
      partial_state_equivalent s scs1' scs2'. (* to define *)
