Require Import String.
Require Import Coqlib Maps Errors Integers Values Memory Globalenvs.
Require Import AST Linking Smallstep Events Behaviors.

Require Import Split.

Require Import riscV.Machregs.
Require Import riscV.Asm.
Require Import Complements.

Require Import Tactics.
Require Import BtBasics BtInfoAsm MemoryDelta MemoryWeak.



(* Section AXIOM. *)

(*   Definition extcall_observable (sem: extcall_sem) (sg: signature): Prop := *)
(*     forall ge vargs m1 t vres m2, *)
(*       sem ge vargs m1 t vres m2 -> t <> E0. *)

(*   Definition external_functions_observable := *)
(*     forall id sg, extcall_observable (external_functions_sem id sg) sg. *)

(*   Definition inline_assembly_observable := *)
(*     forall cp id sg, extcall_observable (inline_assembly_sem cp id sg) sg. *)

(*   (* Axiom external_functions_observable: *) *)
(*   (*   forall id sg, extcall_observable (external_functions_sem id sg) sg. *) *)

(*   (* Axiom inline_assembly_observable: *) *)
(*   (*   forall cp id sg, extcall_observable (inline_assembly_sem cp id sg) sg. *) *)

(* End AXIOM. *)

(* Section BOUND. *)

(*   Hypothesis EFO: external_functions_observable. *)
(*   Hypothesis IAO: inline_assembly_observable. *)

(*   Lemma external_call_observable_length *)
(*         ef ge vargs m1 tr vretv m2 *)
(*         (EC: external_call ef ge vargs m1 tr vretv m2) *)
(*         (ECCASES : external_call_unknowns ef ge m1 vargs \/ *)
(*                      external_call_known_observables ef ge m1 vargs tr vretv m2) *)
(*     : *)
(*     (1 <= length tr)%nat. *)
(*   Proof. *)
(*     des. *)
(*     - unfold external_functions_observable in EFO. unfold extcall_observable in EFO. *)
(*       unfold inline_assembly_observable in IAO. unfold extcall_observable in IAO. *)
(*       cut (tr <> E0). *)
(*       { i. destruct tr; ss. lia. } *)
(*       destruct ef; ss; eauto. *)
(*       + unfold builtin_or_external_sem in EC. des_ifs; ss; eauto. *)
(*       + unfold builtin_or_external_sem in EC. des_ifs; ss; eauto. *)
(*     - destruct ef; ss; des; clarify; try (inv EC; ss). *)
(*       + destruct tr; ss. lia. *)
(*       + destruct tr; ss. lia. *)
(*   Qed. *)

(*   Lemma bundle_trace_bounded *)
(*         ge ist ist' btr *)
(*         (ISTAR: istar (ir_step) ge ist btr ist') *)
(*     : *)
(*     (length btr <= length (unbundle_trace btr))%nat. *)
(*   Proof. *)
(*     induction ISTAR. ss. subst. ss. *)
(*     apply Nat.succ_le_mono in IHISTAR. etransitivity. eauto. clear IHISTAR. *)
(*     rewrite app_length. cut (1 <= length (unbundle ev))%nat. lia. *)
(*     unfold unbundle. *)
(*     inv H; ss. *)
(*     - inv TR; ss. *)
(*     - inv TR; ss. *)
(*     - eapply external_call_observable_length; eauto. des; auto. *)
(*     - eapply external_call_observable_length; eauto. des; auto. *)
(*     - inv TR; ss. *)
(*     - inv TR1; ss. lia. *)
(*     - inv TR1; ss. lia. *)
(*   Qed. *)

(* End BOUND. *)
