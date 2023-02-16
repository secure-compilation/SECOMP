Require Import String.
Require Import Coqlib Maps Errors.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Csyntax Ctypes Ctyping Csem.

(* TODO: should be in a common file *)
Variant side := Left | Right.

Definition split := compartment -> side.

Variable s: split.
(* … *)

Lemma parallel_concrete p1 p2 scs1 scs2:
  left_side s p1 -> (* use definitions from RSC.v *)
  left_side s p2 -> (* use definitions from RSC.v *)
  partial_state_equivalent s scs1 scs2 -> (* to define --> using memory injections? *)
  pc_in_left_part scs1 -> (* to define *)
  CS.kstep (prepare_global_env (program_link p p1)) scs1 t scs1' -> (* use step of Csem instead *)
  exists2 scs2',
    CS.kstep (prepare_global_env (program_link p p2)) scs2 t scs2' /\ (* use step of Csem instead *)
      partial_state_equivalent s scs1' scs2'. (* to define *)
