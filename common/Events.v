(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Observable events, execution traces, and semantics of external calls. *)

Require Import String.
Require Import Coqlib.
Require Import Maps.
Require Intv.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Builtins.

(** Backwards compatibility for Hint Rewrite locality attributes. *)
Set Warnings "-unsupported-attributes".

(** * Events and traces *)

(** The observable behaviour of programs is stated in terms of
  input/output events, which represent the actions of the program
  that the external world can observe.  CompCert leaves much flexibility as to
  the exact content of events: the only requirement is that they
  do not expose memory states nor pointer values
  (other than pointers to global variables), because these
  are not preserved literally during compilation.  For concreteness,
  we use the following type for events.  Each event represents either:

- A system call (e.g. an input/output operation), recording the
  name of the system call, its parameters, and its result.

- A volatile load from a global memory location, recording the chunk
  and address being read and the value just read.

- A volatile store to a global memory location, recording the chunk
  and address being written and the value stored there.

- An annotation, recording the text of the annotation and the values
  of the arguments.

  The values attached to these events are of the following form.
  As mentioned above, we do not expose pointer values directly.
  Pointers relative to a global variable are shown with the name
  of the variable instead of the block identifier.
*)

Inductive eventval: Type :=
  | EVint: int -> eventval
  | EVlong: int64 -> eventval
  | EVfloat: float -> eventval
  | EVsingle: float32 -> eventval
  | EVptr_global: ident -> ptrofs -> eventval.

Inductive event: Type :=
  | Event_syscall: string -> list eventval -> eventval -> event
  | Event_vload: memory_chunk -> ident -> ptrofs -> eventval -> event
  | Event_vstore: memory_chunk -> ident -> ptrofs -> eventval -> event
  | Event_annot: string -> list eventval -> event
  | Event_call: compartment -> compartment -> ident -> list eventval -> event
  | Event_return: compartment -> compartment -> eventval -> event.

(** The dynamic semantics for programs collect traces of events.
  Traces are of two kinds: finite (type [trace]) or infinite (type [traceinf]). *)

Definition trace := list event.

Definition E0 : trace := nil.

Definition Eapp (t1 t2: trace) : trace := t1 ++ t2.

CoInductive traceinf : Type :=
  | Econsinf: event -> traceinf -> traceinf.

Fixpoint Eappinf (t: trace) (T: traceinf) {struct t} : traceinf :=
  match t with
  | nil => T
  | ev :: t' => Econsinf ev (Eappinf t' T)
  end.

(** Concatenation of traces is written [**] in the finite case
  or [***] in the infinite case. *)

Infix "**" := Eapp (at level 60, right associativity).
Infix "***" := Eappinf (at level 60, right associativity).

Lemma E0_left: forall t, E0 ** t = t.
Proof. auto. Qed.

Lemma E0_right: forall t, t ** E0 = t.
Proof. intros. unfold E0, Eapp. rewrite <- app_nil_end. auto. Qed.

Lemma Eapp_assoc: forall t1 t2 t3, (t1 ** t2) ** t3 = t1 ** (t2 ** t3).
Proof. intros. unfold Eapp, trace. apply app_ass. Qed.

Lemma Eapp_E0_inv: forall t1 t2, t1 ** t2 = E0 -> t1 = E0 /\ t2 = E0.
Proof (@app_eq_nil event).

Lemma E0_left_inf: forall T, E0 *** T = T.
Proof. auto. Qed.

Lemma Eappinf_assoc: forall t1 t2 T, (t1 ** t2) *** T = t1 *** (t2 *** T).
Proof.
  induction t1; intros; simpl. auto. decEq; auto.
Qed.

#[global]
Hint Rewrite E0_left E0_right Eapp_assoc
             E0_left_inf Eappinf_assoc: trace_rewrite.

Opaque trace E0 Eapp Eappinf.

(** The following [traceEq] tactic proves equalities between traces
  or infinite traces. *)

Ltac substTraceHyp :=
  match goal with
  | [ H: (@eq trace ?x ?y) |- _ ] =>
       subst x || clear H
  end.

Ltac decomposeTraceEq :=
  match goal with
  | [ |- (_ ** _) = (_ ** _) ] =>
      apply (f_equal2 Eapp); auto; decomposeTraceEq
  | _ =>
      auto
  end.

Ltac traceEq :=
  repeat substTraceHyp; autorewrite with trace_rewrite; decomposeTraceEq.

(** Bisimilarity between infinite traces. *)

CoInductive traceinf_sim: traceinf -> traceinf -> Prop :=
  | traceinf_sim_cons: forall e T1 T2,
      traceinf_sim T1 T2 ->
      traceinf_sim (Econsinf e T1) (Econsinf e T2).

Lemma traceinf_sim_refl:
  forall T, traceinf_sim T T.
Proof.
  cofix COINDHYP; intros.
  destruct T. constructor. apply COINDHYP.
Qed.

Lemma traceinf_sim_sym:
  forall T1 T2, traceinf_sim T1 T2 -> traceinf_sim T2 T1.
Proof.
  cofix COINDHYP; intros. inv H; constructor; auto.
Qed.

Lemma traceinf_sim_trans:
  forall T1 T2 T3,
  traceinf_sim T1 T2 -> traceinf_sim T2 T3 -> traceinf_sim T1 T3.
Proof.
  cofix COINDHYP;intros. inv H; inv H0; constructor; eauto.
Qed.

CoInductive traceinf_sim': traceinf -> traceinf -> Prop :=
  | traceinf_sim'_cons: forall t T1 T2,
      t <> E0 -> traceinf_sim' T1 T2 -> traceinf_sim' (t *** T1) (t *** T2).

Lemma traceinf_sim'_sim:
  forall T1 T2, traceinf_sim' T1 T2 -> traceinf_sim T1 T2.
Proof.
  cofix COINDHYP; intros. inv H.
  destruct t. elim H0; auto.
Transparent Eappinf.
Transparent E0.
  simpl.
  destruct t. simpl. constructor. apply COINDHYP; auto.
  constructor. apply COINDHYP.
  constructor. unfold E0; congruence. auto.
Qed.

(** An alternate presentation of infinite traces as
  infinite concatenations of nonempty finite traces. *)

CoInductive traceinf': Type :=
  | Econsinf': forall (t: trace) (T: traceinf'), t <> E0 -> traceinf'.

Program Definition split_traceinf' (t: trace) (T: traceinf') (NE: t <> E0): event * traceinf' :=
  match t with
  | nil => _
  | e :: nil => (e, T)
  | e :: t' => (e, Econsinf' t' T _)
  end.
Next Obligation.
  elimtype False. elim NE. auto.
Qed.
Next Obligation.
  red; intro; subst; intuition eauto.
Qed.

CoFixpoint traceinf_of_traceinf' (T': traceinf') : traceinf :=
  match T' with
  | Econsinf' t T'' NOTEMPTY =>
      let (e, tl) := split_traceinf' t T'' NOTEMPTY in
      Econsinf e (traceinf_of_traceinf' tl)
  end.

Remark unroll_traceinf':
  forall T, T = match T with Econsinf' t T' NE => Econsinf' t T' NE end.
Proof.
  intros. destruct T; auto.
Qed.

Remark unroll_traceinf:
  forall T, T = match T with Econsinf t T' => Econsinf t T' end.
Proof.
  intros. destruct T; auto.
Qed.

Lemma traceinf_traceinf'_app:
  forall t T NE,
  traceinf_of_traceinf' (Econsinf' t T NE) = t *** traceinf_of_traceinf' T.
Proof.
  induction t.
  intros. elim NE. auto.
  intros. simpl.
  rewrite (unroll_traceinf (traceinf_of_traceinf' (Econsinf' (a :: t) T NE))).
  simpl. destruct t. auto.
Transparent Eappinf.
  simpl. f_equal. apply IHt.
Qed.

(** Prefixes of traces. *)

Definition trace_prefix (t1 t2: trace) :=
  exists t3, t2 = t1 ** t3.

Definition traceinf_prefix (t1: trace) (T2: traceinf) :=
  exists T3, T2 = t1 *** T3.

Lemma trace_prefix_app:
  forall t1 t2 t,
  trace_prefix t1 t2 ->
  trace_prefix (t ** t1) (t ** t2).
Proof.
  intros. destruct H as [t3 EQ]. exists t3. traceEq.
Qed.

Lemma traceinf_prefix_app:
  forall t1 T2 t,
  traceinf_prefix t1 T2 ->
  traceinf_prefix (t ** t1) (t *** T2).
Proof.
  intros. destruct H as [T3 EQ]. exists T3. subst T2. traceEq.
Qed.

(** * Relating values and event values *)

Set Implicit Arguments.

Section EVENTVAL.

(** Symbol environment used to translate between global variable names and their block identifiers. *)
Variable ge: Senv.t.

(** Translation between values and event values. *)

Inductive eventval_match: eventval -> typ -> val -> Prop :=
  | ev_match_int: forall i,
      eventval_match (EVint i) Tint (Vint i)
  | ev_match_long: forall i,
      eventval_match (EVlong i) Tlong (Vlong i)
  | ev_match_float: forall f,
      eventval_match (EVfloat f) Tfloat (Vfloat f)
  | ev_match_single: forall f,
      eventval_match (EVsingle f) Tsingle (Vsingle f)
  | ev_match_ptr: forall id b ofs,
      Senv.public_symbol ge id = true ->
      Senv.find_symbol ge id = Some b ->
      eventval_match (EVptr_global id ofs) Tptr (Vptr b ofs).

Inductive eventval_list_match: list eventval -> list typ -> list val -> Prop :=
  | evl_match_nil:
      eventval_list_match nil nil nil
  | evl_match_cons:
      forall ev1 evl ty1 tyl v1 vl,
      eventval_match ev1 ty1 v1 ->
      eventval_list_match evl tyl vl ->
      eventval_list_match (ev1::evl) (ty1::tyl) (v1::vl).

(** Some properties of these translation predicates. *)

Lemma eventval_match_type:
  forall ev ty v,
  eventval_match ev ty v -> Val.has_type v ty.
Proof.
  intros. inv H; simpl; auto. unfold Tptr; destruct Archi.ptr64; auto.
Qed.

Lemma eventval_list_match_length:
  forall evl tyl vl, eventval_list_match evl tyl vl -> List.length vl = List.length tyl.
Proof.
  induction 1; simpl; eauto.
Qed.

Lemma eventval_match_lessdef:
  forall ev ty v1 v2,
  eventval_match ev ty v1 -> Val.lessdef v1 v2 -> eventval_match ev ty v2.
Proof.
  intros. inv H; inv H0; constructor; auto.
Qed.

Lemma eventval_list_match_lessdef:
  forall evl tyl vl1, eventval_list_match evl tyl vl1 ->
  forall vl2, Val.lessdef_list vl1 vl2 -> eventval_list_match evl tyl vl2.
Proof.
  induction 1; intros. inv H; constructor.
  inv H1. constructor. eapply eventval_match_lessdef; eauto. eauto.
Qed.

(** Determinism *)

Lemma eventval_match_determ_1:
  forall ev ty v1 v2, eventval_match ev ty v1 -> eventval_match ev ty v2 -> v1 = v2.
Proof.
  intros. inv H; inv H0; auto. congruence.
Qed.

Lemma eventval_match_determ_2:
  forall ev1 ev2 ty v, eventval_match ev1 ty v -> eventval_match ev2 ty v -> ev1 = ev2.
Proof.
  intros. inv H; inv H0; auto.
  decEq. eapply Senv.find_symbol_injective; eauto.
Qed.

Lemma eventval_list_match_determ_2:
  forall evl1 tyl vl, eventval_list_match evl1 tyl vl ->
  forall evl2, eventval_list_match evl2 tyl vl -> evl1 = evl2.
Proof.
  induction 1; intros. inv H. auto. inv H1. f_equal; eauto.
  eapply eventval_match_determ_2; eauto.
Qed.

(** Validity *)

Definition eventval_valid (ev: eventval) : Prop :=
  match ev with
  | EVint _ => True
  | EVlong _ => True
  | EVfloat _ => True
  | EVsingle _ => True
  | EVptr_global id ofs => Senv.public_symbol ge id = true
  end.

Definition eventval_type (ev: eventval) : typ :=
  match ev with
  | EVint _ => Tint
  | EVlong _ => Tlong
  | EVfloat _ => Tfloat
  | EVsingle _ => Tsingle
  | EVptr_global id ofs => Tptr
  end.

Lemma eventval_match_receptive:
  forall ev1 ty v1 ev2,
  eventval_match ev1 ty v1 ->
  eventval_valid ev1 -> eventval_valid ev2 -> eventval_type ev1 = eventval_type ev2 ->
  exists v2, eventval_match ev2 ty v2.
Proof.
  intros. unfold eventval_type, Tptr in H2. remember Archi.ptr64 as ptr64.
  inversion H; subst ev1 ty v1; clear H; destruct ev2; simpl in H2; inv H2.
- exists (Vint i0); constructor.
- simpl in H1; exploit Senv.public_symbol_exists; eauto. intros [b FS].
  exists (Vptr b i1); rewrite H3. constructor; auto.
- exists (Vlong i0); constructor.
- simpl in H1; exploit Senv.public_symbol_exists; eauto. intros [b FS].
  exists (Vptr b i1); rewrite H3; constructor; auto.
- exists (Vfloat f0); constructor.
- destruct Archi.ptr64; discriminate.
- exists (Vsingle f0); constructor; auto.
- destruct Archi.ptr64; discriminate.
- exists (Vint i); unfold Tptr; rewrite H5; constructor.
- exists (Vlong i); unfold Tptr; rewrite H5; constructor.
- destruct Archi.ptr64; discriminate.
- destruct Archi.ptr64; discriminate.
- exploit Senv.public_symbol_exists. eexact H1. intros [b' FS].
  exists (Vptr b' i0); constructor; auto.
Qed.

Lemma eventval_match_valid:
  forall ev ty v, eventval_match ev ty v -> eventval_valid ev.
Proof.
  destruct 1; simpl; auto.
Qed.

Lemma eventval_match_same_type:
  forall ev1 ty v1 ev2 v2,
  eventval_match ev1 ty v1 -> eventval_match ev2 ty v2 -> eventval_type ev1 = eventval_type ev2.
Proof.
  destruct 1; intros EV; inv EV; auto.
Qed.

End EVENTVAL.

(** Invariance under changes to the global environment *)

Section EVENTVAL_INV.

Variables ge1 ge2: Senv.t.

Hypothesis public_preserved:
  forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id.

Lemma eventval_valid_preserved:
  forall ev, eventval_valid ge1 ev -> eventval_valid ge2 ev.
Proof.
  intros. destruct ev; simpl in *; auto. rewrite <- H; auto.
Qed.

Hypothesis symbols_preserved:
  forall id, Senv.find_symbol ge2 id = Senv.find_symbol ge1 id.

Lemma eventval_match_preserved:
  forall ev ty v,
  eventval_match ge1 ev ty v -> eventval_match ge2 ev ty v.
Proof.
  induction 1; constructor; auto.
  rewrite public_preserved; auto.
  rewrite symbols_preserved; auto.
Qed.

Lemma eventval_list_match_preserved:
  forall evl tyl vl,
  eventval_list_match ge1 evl tyl vl -> eventval_list_match ge2 evl tyl vl.
Proof.
  induction 1; constructor; auto. eapply eventval_match_preserved; eauto.
Qed.

End EVENTVAL_INV.

(** Compatibility with memory injections *)

Section EVENTVAL_INJECT.

Variable f: block -> option (block * Z).
Variable ge1 ge2: Senv.t.

Definition symbols_inject : Prop :=
   (forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id)
/\ (forall id b1 b2 delta,
     f b1 = Some(b2, delta) -> Senv.find_symbol ge1 id = Some b1 ->
     delta = 0 /\ Senv.find_symbol ge2 id = Some b2)
/\ (forall id b1,
     Senv.public_symbol ge1 id = true -> Senv.find_symbol ge1 id = Some b1 ->
     exists b2, f b1 = Some(b2, 0) /\ Senv.find_symbol ge2 id = Some b2)
/\ (forall b1 b2 delta,
     f b1 = Some(b2, delta) ->
     Senv.block_is_volatile ge2 b2 = Senv.block_is_volatile ge1 b1).

Hypothesis symb_inj: symbols_inject.

Lemma eventval_match_inject:
  forall ev ty v1 v2,
  eventval_match ge1 ev ty v1 -> Val.inject f v1 v2 -> eventval_match ge2 ev ty v2.
Proof.
  intros. inv H; inv H0; try constructor; auto.
  destruct symb_inj as (A & B & C & D). exploit C; eauto. intros [b3 [EQ FS]]. rewrite H4 in EQ; inv EQ.
  rewrite Ptrofs.add_zero. constructor; auto. rewrite A; auto.
Qed.

Lemma eventval_match_inject_2:
  forall ev ty v1,
  eventval_match ge1 ev ty v1 ->
  exists v2, eventval_match ge2 ev ty v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H; try (econstructor; split; eauto; constructor; fail).
  destruct symb_inj as (A & B & C & D). exploit C; eauto. intros [b2 [EQ FS]].
  exists (Vptr b2 ofs); split. econstructor; eauto.
  econstructor; eauto. rewrite Ptrofs.add_zero; auto.
Qed.

Lemma eventval_list_match_inject:
  forall evl tyl vl1, eventval_list_match ge1 evl tyl vl1 ->
  forall vl2, Val.inject_list f vl1 vl2 -> eventval_list_match ge2 evl tyl vl2.
Proof.
  induction 1; intros. inv H; constructor.
  inv H1. constructor. eapply eventval_match_inject; eauto. eauto.
Qed.

End EVENTVAL_INJECT.

(** * Matching traces. *)

Section MATCH_TRACES.

Variable ge: Senv.t.

(** Matching between traces corresponding to single transitions.
  Arguments (provided by the program) must be equal.
  Results (provided by the outside world) can vary as long as they
  can be converted safely to values. *)

Inductive match_traces: trace -> trace -> Prop :=
  | match_traces_E0:
      match_traces nil nil
  | match_traces_syscall: forall id args res1 res2,
      eventval_valid ge res1 -> eventval_valid ge res2 -> eventval_type res1 = eventval_type res2 ->
      match_traces (Event_syscall id args res1 :: nil) (Event_syscall id args res2 :: nil)
  | match_traces_vload: forall chunk id ofs res1 res2,
      eventval_valid ge res1 -> eventval_valid ge res2 -> eventval_type res1 = eventval_type res2 ->
      match_traces (Event_vload chunk id ofs res1 :: nil) (Event_vload chunk id ofs res2 :: nil)
  | match_traces_vstore: forall chunk id ofs arg,
      match_traces (Event_vstore chunk id ofs arg :: nil) (Event_vstore chunk id ofs arg :: nil)
  | match_traces_annot: forall id args,
      match_traces (Event_annot id args :: nil) (Event_annot id args :: nil)
  | match_traces_call: forall cp cp' id args,
      match_traces (Event_call cp cp' id args :: nil) (Event_call cp cp' id args :: nil)
  | match_traces_return: forall cp cp' res,
      match_traces (Event_return cp cp' res :: nil) (Event_return cp cp' res :: nil).

End MATCH_TRACES.

(** Invariance by change of global environment *)

Section MATCH_TRACES_INV.

Variables ge1 ge2: Senv.t.

Hypothesis public_preserved:
  forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id.

Lemma match_traces_preserved:
  forall t1 t2, match_traces ge1 t1 t2 -> match_traces ge2 t1 t2.
Proof.
  induction 1; constructor; auto; eapply eventval_valid_preserved; eauto.
Qed.

End MATCH_TRACES_INV.

(** An output trace is a trace composed only of output events,
  that is, events that do not take any result from the outside world. *)

Definition output_event (ev: event) : Prop :=
  match ev with
  | Event_syscall _ _ _ => False
  | Event_vload _ _ _ _ => False
  | Event_vstore _ _ _ _ => True
  | Event_annot _ _ => True
  | Event_call _ _ _ _ => True
  | Event_return _ _ _ => True
  end.

Fixpoint output_trace (t: trace) : Prop :=
  match t with
  | nil => True
  | ev :: t' => output_event ev /\ output_trace t'
  end.

(** * Semantics of volatile memory accesses *)

(* JT: NOTE: Volatile loads may appear on the trace.
   1) Does that cause any issue with compartmentalization?
   2) Cross-component volatile loads should be forbidden, probably.
 *)

(* JT: NOTE: Should the semantics of volatile loads depend on the component
 that perform them? IE, should we add a parameter [c] to the next definition? *)
(* AD: ANSWER: Probably, because we eventually want to prevent cross-component
 memory interactions. But maybe the enforcement should happen somewhere else, for
 instance in [volatile_load_sem] *)
(* RB: NOTE: For now, adding components to non-volatile versions as a bare
   minimum. *)
Inductive volatile_load (ge: Senv.t) (cp: compartment):
                   memory_chunk -> mem -> block -> ptrofs -> trace -> val -> Prop :=
  | volatile_load_vol: forall chunk m b ofs id ev v,
      Senv.block_is_volatile ge b = true ->
      Senv.find_symbol ge id = Some b ->
      eventval_match ge ev (type_of_chunk chunk) v ->
      volatile_load ge cp chunk m b ofs
                      (Event_vload chunk id ofs ev :: nil)
                      (Val.load_result chunk v)
  | volatile_load_nonvol: forall chunk m b ofs v,
      Senv.block_is_volatile ge b = false ->
      forall OWN : Mem.can_access_block m b (Some cp),
      Mem.load chunk m b (Ptrofs.unsigned ofs) (Some cp) = Some v ->
      volatile_load ge cp chunk m b ofs E0 v.

Inductive volatile_store (ge: Senv.t) (cp: compartment):
                  memory_chunk -> mem -> block -> ptrofs -> val -> trace -> mem -> Prop :=
  | volatile_store_vol: forall chunk m b ofs id ev v,
      Senv.block_is_volatile ge b = true ->
      Senv.find_symbol ge id = Some b ->
      eventval_match ge ev (type_of_chunk chunk) (Val.load_result chunk v) ->
      volatile_store ge cp chunk m b ofs v
                      (Event_vstore chunk id ofs ev :: nil)
                      m
  | volatile_store_nonvol: forall chunk m b ofs v m',
      Senv.block_is_volatile ge b = false ->
      forall OWN : Mem.can_access_block m b (Some cp),
      Mem.store chunk m b (Ptrofs.unsigned ofs) v cp = Some m' ->
      volatile_store ge cp chunk m b ofs v E0 m'.

(** * Semantics of external functions *)

(** For each external function, its behavior is defined by a predicate relating:
- the global symbol environment
- the calling compartment
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).

Most external calls do not use the calling compartment, as formalized
in extcall_caller_independent.
*)

Definition extcall_sem : Type :=
  Senv.t -> list val -> mem -> trace -> val -> mem -> Prop.

(* (** This invariant guarantees that external calls performed to [cp] can *)
(*   correctly use either [cp1] or [cp2] to find out who the calling compartment *)
(*   is. *) *)
(* Definition uptodate_caller (cp cp1 cp2: compartment) := *)
(*   needs_calling_comp cp = true -> *)
(*   cp1 = cp2. *)

(* Definition extcall_caller_independent (cp: compartment) (sem: extcall_sem) := *)
(*   forall ge cp1 cp2 args m t v m', *)
(*   uptodate_caller cp cp1 cp2 -> *)
(*   sem ge cp1 args m t v m' -> *)
(*   sem ge cp2 args m t v m'. *)

(** We now specify the expected properties of this predicate. *)

Definition loc_out_of_bounds (m: mem) (b: block) (ofs: Z) : Prop :=
  ~Mem.perm m b ofs Max Nonempty.

Definition loc_not_writable (m: mem) (b: block) (ofs: Z) : Prop :=
  ~Mem.perm m b ofs Max Writable.

Definition loc_unmapped (f: meminj) (b: block) (ofs: Z): Prop :=
  f b = None.

Definition loc_out_of_reach (f: meminj) (m: mem) (b: block) (ofs: Z): Prop :=
  forall b0 delta,
  f b0 = Some(b, delta) -> ~Mem.perm m b0 (ofs - delta) Max Nonempty.

Definition inject_separated (f f': meminj) (m1 m2: mem): Prop :=
  forall b1 b2 delta,
  f b1 = None -> f' b1 = Some(b2, delta) ->
  ~Mem.valid_block m1 b1 /\ ~Mem.valid_block m2 b2.

Record extcall_properties (sem: extcall_sem) (sg: signature) : Prop :=
  mk_extcall_properties {

(** The return value of an external call must agree with its signature. *)
  ec_well_typed:
    forall ge vargs m1 t vres m2,
    sem ge vargs m1 t vres m2 ->
    Val.has_rettype vres sg.(sig_res);

(** The semantics is invariant under change of global environment that preserves symbols. *)
  ec_symbols_preserved:
    forall ge1 ge2 vargs m1 t vres m2,
    Senv.equiv ge1 ge2 ->
    sem ge1 vargs m1 t vres m2 ->
    sem ge2 vargs m1 t vres m2;

(** External calls cannot invalidate memory blocks.  (Remember that
  freeing a block does not invalidate its block identifier.) *)
  ec_valid_block:
    forall ge vargs m1 t vres m2 b,
    sem ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.valid_block m2 b;

(** External calls cannot change the ownership of memory blocks.
  JT: lacks in generality, but if we start allowing sharing then the
      notion of [can_access_block] must be completely changed anyway
 *)
  ec_can_access_block:
    forall ge vargs m1 t vres m2 b cp,
    sem ge vargs m1 t vres m2 ->
    Mem.can_access_block m1 b cp -> Mem.can_access_block m2 b cp;

(** External calls cannot increase the max permissions of a valid block.
    They can decrease the max permissions, e.g. by freeing. *)
  ec_max_perm:
    forall ge vargs m1 t vres m2 b ofs p,
    sem ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p;

(** External call cannot modify memory unless they have [Max, Writable]
   permissions. *)
  ec_readonly:
    forall ge vargs m1 t vres m2 b ofs n bytes cp,
    sem ge vargs m1 t vres m2 ->
    Mem.valid_block m1 b ->
    Mem.loadbytes m2 b ofs n cp = Some bytes ->
    (forall i, ofs <= i < ofs + n -> ~Mem.perm m1 b i Max Writable) ->
    Mem.loadbytes m1 b ofs n cp = Some bytes;

      (** TODO: External call should not be able to modify other compartment's memory *)
  (* ec_mem_outside_compartment: *)
  (*   forall ge c vargs m1 t vres m2, *)
  (*   sem ge c vargs m1 t vres m2 -> *)
  (*   Mem.unchanged_on (loc_not_in_compartment c m1) m1 m2; *)

(** External calls must commute with memory extensions, in the
  following sense. *)
  ec_mem_extends:
    forall ge vargs m1 t vres m2 m1' vargs',
    sem ge vargs m1 t vres m2 ->
    Mem.extends m1 m1' ->
    Val.lessdef_list vargs vargs' ->
    exists vres', exists m2',
       sem ge vargs' m1' t vres' m2'
    /\ Val.lessdef vres vres'
    /\ Mem.extends m2 m2'
    /\ Mem.unchanged_on (loc_out_of_bounds m1) m1' m2';

(** External calls must commute with memory injections,
  in the following sense. *)
  ec_mem_inject:
    forall ge1 ge2 vargs m1 t vres m2 f m1' vargs',
    symbols_inject f ge1 ge2 ->
    sem ge1 vargs m1 t vres m2 ->
    Mem.inject f m1 m1' ->
    Val.inject_list f vargs vargs' ->
    exists f', exists vres', exists m2',
       sem ge2 vargs' m1' t vres' m2'
    /\ Val.inject f' vres vres'
    /\ Mem.inject f' m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1';

(** External calls produce at most one event. *)
  ec_trace_length:
    forall ge vargs m t vres m',
    sem ge vargs m t vres m' -> (length t <= 1)%nat;

(** External calls must be receptive to changes of traces by another, matching trace. *)
  ec_receptive:
    forall ge vargs m t1 vres1 m1 t2,
    sem ge vargs m t1 vres1 m1 -> match_traces ge t1 t2 ->
    exists vres2, exists m2, sem ge vargs m t2 vres2 m2;

(** External calls must be deterministic up to matching between traces. *)
  ec_determ:
    forall ge vargs m t1 vres1 m1 t2 vres2 m2,
    sem ge vargs m t1 vres1 m1 -> sem ge vargs m t2 vres2 m2 ->
    match_traces ge t1 t2 /\ (t1 = t2 -> vres1 = vres2 /\ m1 = m2)
}.

(** ** Semantics of volatile loads *)

Inductive volatile_load_sem (cp: compartment) (chunk: memory_chunk) (ge: Senv.t) :
              list val -> mem -> trace -> val -> mem -> Prop :=
  | volatile_load_sem_intro: forall b ofs m t v,
      volatile_load ge cp chunk m b ofs t v ->
      volatile_load_sem cp chunk ge (Vptr b ofs :: nil) m t v m.

Lemma volatile_load_preserved:
  forall ge1 ge2 cp chunk m b ofs t v,
  Senv.equiv ge1 ge2 ->
  volatile_load ge1 cp chunk m b ofs t v ->
  volatile_load ge2 cp chunk m b ofs t v.
Proof.
  intros. destruct H as (A & B & C). inv H0; econstructor; eauto.
  rewrite A; auto.
  eapply eventval_match_preserved; eauto.
Qed.

Lemma volatile_load_extends:
  forall ge cp chunk m b ofs t v m',
  volatile_load ge cp chunk m b ofs t v ->
  Mem.extends m m' ->
  exists v', volatile_load ge cp chunk m' b ofs t v' /\ Val.lessdef v v'.
Proof.
  intros. inv H.
  econstructor; split; eauto. econstructor; eauto.
  exploit Mem.load_extends; eauto. intros [v' [A B]]. exists v'; split; auto. econstructor; eauto.
  Local Transparent Mem.load.
  unfold Mem.load in A. destruct (Mem.valid_access_dec m' chunk b (Ptrofs.unsigned ofs) Readable (Some cp)); try discriminate.
  Local Opaque Mem.load.
  inv v0. intuition.
Qed.

Lemma volatile_load_inject:
  forall ge1 ge2 cp f chunk m b ofs t v b' ofs' m',
  symbols_inject f ge1 ge2 ->
  volatile_load ge1 cp chunk m b ofs t v ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  Mem.inject f m m' ->
  exists v', volatile_load ge2 cp chunk m' b' ofs' t v' /\ Val.inject f v v'.
Proof.
  intros until m'; intros SI VL VI MI. generalize SI; intros (A & B & C & D).
  inv VL.
- (* volatile load *)
  inv VI. exploit B; eauto. intros [U V]. subst delta.
  exploit eventval_match_inject_2; eauto. intros (v2 & X & Y).
  rewrite Ptrofs.add_zero. exists (Val.load_result chunk v2); split.
  constructor; auto.
  erewrite D; eauto.
  apply Val.load_result_inject. auto.
- (* normal load *)
  exploit Mem.loadv_inject; eauto. simpl; eauto. simpl; intros (v2 & X & Y).
  exists v2; split; auto.
  econstructor; eauto.
  inv VI. erewrite D; eauto.
  Local Transparent Mem.load.
  unfold Mem.load in X. destruct (Mem.valid_access_dec m' chunk b' (Ptrofs.unsigned ofs') Readable (Some cp)); try discriminate.
  Local Opaque Mem.load.
  inv v0. intuition.
Qed.

Lemma volatile_load_receptive:
  forall ge cp chunk m b ofs t1 t2 v1,
  volatile_load ge cp chunk m b ofs t1 v1 -> match_traces ge t1 t2 ->
  exists v2, volatile_load ge cp chunk m b ofs t2 v2.
Proof.
  intros. inv H; inv H0.
  exploit eventval_match_receptive; eauto. intros [v' EM].
  exists (Val.load_result chunk v'). constructor; auto.
  exists v1; econstructor; eauto.
Qed.

Lemma volatile_load_ok:
  forall chunk cp,
  extcall_properties (volatile_load_sem cp chunk)
                     (mksignature (Tptr :: nil) (rettype_of_chunk chunk) cc_default).
Proof.
  intros; constructor; intros.
(* well typed *)
- inv H. inv H0. apply Val.load_result_rettype.
  eapply Mem.load_rettype; eauto.
(* symbols *)
- inv H0. constructor. eapply volatile_load_preserved; eauto.
(* valid blocks *)
- inv H; auto.
(* accessiblity *)
- inv H; auto.
(* max perms *)
- inv H; auto.
(* readonly *)
- inv H; auto.
(* mem extends *)
- inv H. inv H1. inv H6. inv H4.
  exploit volatile_load_extends; eauto. intros [v' [A B]].
  exists v'; exists m1'; intuition. constructor; auto.
(* mem injects *)
- inv H0. inv H2. inv H7. inversion H5; subst.
  exploit volatile_load_inject; eauto. intros [v' [A B]].
  exists f; exists v'; exists m1'; intuition. constructor; auto.
  red; intros. congruence.
(* trace length *)
- inv H; inv H0; simpl; lia.
(* receptive *)
- inv H. exploit volatile_load_receptive; eauto. intros [v2 A].
  exists v2; exists m1; constructor; auto.
(* determ *)
- inv H; inv H0. inv H1; inv H7; try congruence.
  assert (id = id0) by (eapply Senv.find_symbol_injective; eauto). subst id0.
  split. constructor.
  eapply eventval_match_valid; eauto.
  eapply eventval_match_valid; eauto.
  eapply eventval_match_same_type; eauto.
  intros EQ; inv EQ.
  assert (v = v0) by (eapply eventval_match_determ_1; eauto). subst v0.
  auto.
  split. constructor. intuition congruence.
Qed.

(** ** Semantics of volatile stores *)

(* JT: Note: Same remarks as for volatile loads *)

Inductive volatile_store_sem (cp: compartment) (chunk: memory_chunk)(ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | volatile_store_sem_intro: forall b ofs m1 v t m2,
      volatile_store ge cp chunk m1 b ofs v t m2 ->
      volatile_store_sem cp chunk ge (Vptr b ofs :: v :: nil) m1 t Vundef m2.

Lemma volatile_store_preserved:
  forall ge1 ge2 cp chunk m1 b ofs v t m2,
  Senv.equiv ge1 ge2 ->
  volatile_store ge1 cp chunk m1 b ofs v t m2 ->
  volatile_store ge2 cp chunk m1 b ofs v t m2.
Proof.
  intros. destruct H as (A & B & C). inv H0; econstructor; eauto.
  rewrite A; auto.
  eapply eventval_match_preserved; eauto.
Qed.

Lemma unchanged_on_readonly:
  forall m1 m2 b ofs n cp bytes,
  Mem.unchanged_on (loc_not_writable m1) m1 m2 ->
  Mem.valid_block m1 b ->
  Mem.loadbytes m2 b ofs n cp = Some bytes ->
  (forall i, ofs <= i < ofs + n -> ~Mem.perm m1 b i Max Writable) ->
  Mem.loadbytes m1 b ofs n cp = Some bytes.
Proof.
  intros.
  rewrite <- H1. symmetry.
  apply Mem.loadbytes_unchanged_on_1 with (P := loc_not_writable m1); auto.
  eapply Mem.unchanged_on_own; eauto.
  eapply Mem.loadbytes_can_access_block_inj ; eauto.
Qed.

Lemma volatile_store_readonly:
  forall ge cp chunk1 m1 b1 ofs1 v t m2,
  volatile_store ge cp chunk1 m1 b1 ofs1 v t m2 ->
  Mem.unchanged_on (loc_not_writable m1) m1 m2.
Proof.
  intros. inv H.
- apply Mem.unchanged_on_refl.
- eapply Mem.store_unchanged_on; eauto.
  exploit Mem.store_valid_access_3; eauto. intros [P [Q R]].
  intros. unfold loc_not_writable. red; intros. apply H2.
  apply Mem.perm_cur_max. apply P. auto.
Qed.

Lemma volatile_store_extends:
  forall ge cp chunk m1 b ofs v t m2 m1' v',
  volatile_store ge cp chunk m1 b ofs v t m2 ->
  Mem.extends m1 m1' ->
  Val.lessdef v v' ->
  exists m2',
     volatile_store ge cp chunk m1' b ofs v' t m2'
  /\ Mem.extends m2 m2'
  /\ Mem.unchanged_on (loc_out_of_bounds m1) m1' m2'.
Proof.
  intros. inv H.
- econstructor; split. econstructor; eauto.
  eapply eventval_match_lessdef; eauto. apply Val.load_result_lessdef; auto.
  auto with mem.
- exploit Mem.store_within_extends; eauto. intros [m2' [A B]].
  exists m2'; intuition.
  + econstructor; eauto.
    eapply Mem.mext_inj in H0. eapply Mem.mi_own in H0; eauto.
    unfold inject_id. reflexivity.
+ eapply Mem.store_unchanged_on; eauto.
  unfold loc_out_of_bounds; intros.
  assert (Mem.perm m1 b i Max Nonempty).
  { apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
    exploit Mem.store_valid_access_3. eexact H3. intros [P Q]. eauto. }
  tauto.
Qed.

Lemma volatile_store_inject:
  forall ge1 ge2 cp f chunk m1 b ofs v t m2 m1' b' ofs' v',
  symbols_inject f ge1 ge2 ->
  volatile_store ge1 cp chunk m1 b ofs v t m2 ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  Val.inject f v v' ->
  Mem.inject f m1 m1' ->
  exists m2',
       volatile_store ge2 cp chunk m1' b' ofs' v' t m2'
    /\ Mem.inject f m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'.
Proof.
  intros until v'; intros SI VS AI VI MI.
  generalize SI; intros (P & Q & R & S).
  inv VS.
- (* volatile store *)
  inv AI. exploit Q; eauto. intros [A B]. subst delta.
  rewrite Ptrofs.add_zero. exists m1'; split.
  constructor; auto. erewrite S; eauto.
  eapply eventval_match_inject; eauto. apply Val.load_result_inject. auto.
  intuition auto with mem.
- (* normal store *)
  inversion AI; subst.
  assert (Mem.storev chunk m1 (Vptr b ofs) v cp = Some m2). simpl; auto.
  exploit Mem.storev_mapped_inject; eauto. intros [m2' [A B]].
  exists m2'; intuition auto.
  + econstructor; eauto.
    eapply Mem.mi_own; eauto. eapply Mem.mi_inj; eauto.
+ eapply Mem.store_unchanged_on; eauto.
  unfold loc_unmapped; intros. inv AI; congruence.
+ eapply Mem.store_unchanged_on; eauto.
  unfold loc_out_of_reach; intros. red; intros. simpl in A.
  assert (EQ: Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta)) = Ptrofs.unsigned ofs + delta)
  by (eapply Mem.address_inject; eauto with mem).
  rewrite EQ in *.
  eelim H3; eauto.
  exploit Mem.store_valid_access_3. eexact H0. intros [X Y].
  intros.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  apply X. lia.
Qed.

Lemma volatile_store_receptive:
  forall ge cp chunk m b ofs v t1 m1 t2,
  volatile_store ge cp chunk m b ofs v t1 m1 -> match_traces ge t1 t2 -> t1 = t2.
Proof.
  intros. inv H; inv H0; auto.
Qed.

Lemma volatile_store_ok:
  forall cp chunk,
  extcall_properties (volatile_store_sem cp chunk)
                     (mksignature (Tptr :: type_of_chunk chunk :: nil) Tvoid cc_default).
Proof.
  intros; constructor; intros.
(* well typed *)
- unfold proj_sig_res; simpl. inv H; constructor.
(* symbols preserved *)
- inv H0. constructor. eapply volatile_store_preserved; eauto.
(* valid block *)
- inv H. inv H1. auto. eauto with mem.
(* accessibility block *)
- inv H. inv H1. auto. eapply Mem.store_can_access_block_inj in H2. eapply H2. eauto.
(* perms *)
- inv H. inv H2. auto. eauto with mem.
(* readonly *)
- inv H. eapply unchanged_on_readonly; eauto. eapply volatile_store_readonly; eauto.
(* mem extends*)
- inv H. inv H1. inv H6. inv H7. inv H4.
  exploit volatile_store_extends; eauto. intros [m2' [A [B C]]].
  exists Vundef; exists m2'; intuition. constructor; auto.
(* mem inject *)
- inv H0. inv H2. inv H7. inv H8. inversion H5; subst.
  exploit volatile_store_inject; eauto. intros [m2' [A [B [C D]]]].
  exists f; exists Vundef; exists m2'; intuition. constructor; auto. red; intros; congruence.
(* trace length *)
- inv H; inv H0; simpl; lia.
(* receptive *)
- assert (t1 = t2). inv H. eapply volatile_store_receptive; eauto.
  subst t2; exists vres1; exists m1; auto.
(* determ *)
- inv H; inv H0. inv H1; inv H8; try congruence.
  assert (id = id0) by (eapply Senv.find_symbol_injective; eauto). subst id0.
  assert (ev = ev0) by (eapply eventval_match_determ_2; eauto). subst ev0.
  split. constructor. auto.
  split. constructor. intuition congruence.
Qed.

(** ** Semantics of dynamic memory allocation (malloc) *)

(* JT: NOTE: Same remarks as for volatile loads and stores *)

Inductive extcall_malloc_sem (cp: compartment) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_malloc_sem_intro: forall sz m m' b m'',
      Mem.alloc m cp (- size_chunk Mptr) (Ptrofs.unsigned sz) = (m', b) ->
      Mem.store Mptr m' b (- size_chunk Mptr) (Vptrofs sz) cp = Some m'' ->
      extcall_malloc_sem cp ge (Vptrofs sz :: nil) m E0 (Vptr b Ptrofs.zero) m''.

Lemma extcall_malloc_ok:
  forall cp,
  extcall_properties (extcall_malloc_sem cp)
                     (mksignature (Tptr :: nil) Tptr cc_default).
Proof.
  intros.
  assert (UNCHANGED:
    forall (P: block -> Z -> Prop) cp m lo hi v m' b m'',
    Mem.alloc m cp lo hi = (m', b) ->
    Mem.store Mptr m' b lo v cp = Some m'' ->
    Mem.unchanged_on P m m'').
  {
    intros.
    apply Mem.unchanged_on_implies with (fun b1 ofs1 => b1 <> b).
    apply Mem.unchanged_on_trans with m'.
    eapply Mem.alloc_unchanged_on; eauto.
    eapply Mem.store_unchanged_on; eauto.
    intros. eapply Mem.valid_not_valid_diff; eauto with mem.
  }
  constructor; intros.
(* well typed *)
- inv H. simpl. unfold Tptr; destruct Archi.ptr64; auto.
(* symbols preserved *)
- inv H0; econstructor; eauto.
(* valid block *)
- inv H. eauto with mem.
(* accessibility *)
- inv H. eapply Mem.store_can_access_block_inj in H2; eapply H2.
  eapply Mem.alloc_can_access_block_other_inj_1; eauto.
(* perms *)
- inv H. exploit Mem.perm_alloc_inv. eauto. eapply Mem.perm_store_2; eauto.
  rewrite dec_eq_false. auto.
  apply Mem.valid_not_valid_diff with m1; eauto with mem.
(* readonly *)
- inv H. eapply unchanged_on_readonly; eauto. 
(* mem extends *)
- inv H. inv H1. inv H7.
  assert (SZ: v2 = Vptrofs sz).
  { unfold Vptrofs in *. destruct Archi.ptr64; inv H5; auto. }
  subst v2.
  exploit Mem.alloc_extends; eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m3' [A B]].
  exploit Mem.store_within_extends. eexact B. eauto. eauto.
  intros [m2' [C D]].
  exists (Vptr b Ptrofs.zero); exists m2'; intuition.
  econstructor; eauto.
  eapply UNCHANGED; eauto.
(* mem injects *)
- inv H0. inv H2. inv H8.
  assert (SZ: v' = Vptrofs sz).
  { unfold Vptrofs in *. destruct Archi.ptr64; inv H6; auto. }
  subst v'.
  exploit Mem.alloc_parallel_inject; eauto. apply Z.le_refl. apply Z.le_refl.
  intros [f' [m3' [b' [ALLOC [A [B [C D]]]]]]].
  exploit Mem.store_mapped_inject. eexact A. eauto. eauto.
  instantiate (1 := Vptrofs sz). unfold Vptrofs; destruct Archi.ptr64; constructor.
  rewrite Z.add_0_r. intros [m2' [E G]].
  exists f'; exists (Vptr b' Ptrofs.zero); exists m2'; intuition auto.
  econstructor; eauto.
  econstructor. eauto. auto.
  eapply UNCHANGED; eauto.
  eapply UNCHANGED; eauto.
  red; intros. destruct (eq_block b1 b).
  subst b1. rewrite C in H2. inv H2. eauto with mem.
  rewrite D in H2 by auto. congruence.
(* trace length *)
- inv H; simpl; lia.
(* receptive *)
- assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
(* determ *)
- inv H. simple inversion H0.
  assert (EQ2: sz0 = sz).
  { unfold Vptrofs in H4; destruct Archi.ptr64 eqn:SF.
    rewrite <- (Ptrofs.of_int64_to_int64 SF sz0), <- (Ptrofs.of_int64_to_int64 SF sz). congruence.
    rewrite <- (Ptrofs.of_int_to_int SF sz0), <- (Ptrofs.of_int_to_int SF sz). congruence.
  }
  subst.
  split. constructor. intuition congruence.
Qed.

(** ** Semantics of dynamic memory deallocation (free) *)

(* JT: NOTE: Same remarks as before. *)

Inductive extcall_free_sem (cp: compartment) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_free_sem_ptr: forall b lo sz m m',
      Mem.load Mptr m b (Ptrofs.unsigned lo - size_chunk Mptr) (Some cp) = Some (Vptrofs sz) ->
      Ptrofs.unsigned sz > 0 ->
      Mem.free m b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) cp = Some m' ->
      extcall_free_sem cp ge (Vptr b lo :: nil) m E0 Vundef m'
  | extcall_free_sem_null: forall m,
      extcall_free_sem cp ge (Vnullptr :: nil) m E0 Vundef m.

Lemma extcall_free_ok:
  forall cp,
  extcall_properties (extcall_free_sem cp)
                     (mksignature (Tptr :: nil) Tvoid cc_default).
Proof.
  intros.
  constructor; intros.
(* well typed *)
- inv H; simpl; auto.
(* symbols preserved *)
- inv H0; econstructor; eauto.
(* valid block *)
- inv H; eauto with mem.
(* accessibility *)
- inv H; eauto. eapply Mem.free_can_access_block_inj_1; eauto.
(* perms *)
- inv H; eauto using Mem.perm_free_3.
(* readonly *)
- eapply unchanged_on_readonly; eauto. inv H.
+ eapply Mem.free_unchanged_on; eauto.
  intros. red; intros. elim H6.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.free_range_perm; eauto.
+ apply Mem.unchanged_on_refl.
(* mem extends *)
- inv H.
+ inv H1. inv H8. inv H6.
  exploit Mem.load_extends; eauto. intros [v' [A B]].
  assert (v' = Vptrofs sz).
  { unfold Vptrofs in *; destruct Archi.ptr64; inv B; auto. }
  subst v'.
  exploit Mem.free_parallel_extends; eauto. intros [m2' [C D]].
  exists Vundef; exists m2'; intuition auto.
  econstructor; eauto.
  eapply Mem.free_unchanged_on; eauto.
  unfold loc_out_of_bounds; intros.
  assert (Mem.perm m1 b i Max Nonempty).
  { apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
    eapply Mem.free_range_perm. eexact H4. eauto. }
  tauto.
+ inv H1. inv H5. replace v2 with Vnullptr.
  exists Vundef; exists m1'; intuition auto.
  constructor.
  apply Mem.unchanged_on_refl.
  unfold Vnullptr in *; destruct Archi.ptr64; inv H3; auto.
(* mem inject *)
- inv H0.
+ inv H2. inv H7. inv H9.
  exploit Mem.load_inject; eauto. intros [v' [A B]].
  assert (v' = Vptrofs sz).
  { unfold Vptrofs in *; destruct Archi.ptr64; inv B; auto. }
  subst v'.
  assert (P: Mem.range_perm m1 b (Ptrofs.unsigned lo - size_chunk Mptr) (Ptrofs.unsigned lo + Ptrofs.unsigned sz) Cur Freeable).
    eapply Mem.free_range_perm; eauto.
  exploit Mem.address_inject; eauto.
    apply Mem.perm_implies with Freeable; auto with mem.
    apply P. instantiate (1 := lo).
    generalize (size_chunk_pos Mptr); lia.
  intro EQ.
  exploit Mem.free_parallel_inject; eauto. intros (m2' & C & D).
  exists f, Vundef, m2'; split.
  apply extcall_free_sem_ptr with (sz := sz) (m' := m2').
    rewrite EQ. rewrite <- A. f_equal. lia.
    auto. auto.
    rewrite ! EQ. rewrite <- C. f_equal; lia.
  split. auto.
  split. auto.
  split. eapply Mem.free_unchanged_on; eauto. unfold loc_unmapped. intros; congruence.
  split. eapply Mem.free_unchanged_on; eauto. unfold loc_out_of_reach.
    intros. red; intros. eelim H2; eauto.
    apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
    apply P. lia.
  split. auto.
  red; intros. congruence.
+ inv H2. inv H6. replace v' with Vnullptr.
  exists f, Vundef, m1'; intuition auto using Mem.unchanged_on_refl.
  constructor.
  red; intros; congruence.
  unfold Vnullptr in *; destruct Archi.ptr64; inv H4; auto.
(* trace length *)
- inv H; simpl; lia.
(* receptive *)
- assert (t1 = t2) by (inv H; inv H0; auto). subst t2.
  exists vres1; exists m1; auto.
(* determ *)
- inv H; inv H0; try (unfold Vnullptr in *; destruct Archi.ptr64; discriminate).
+ assert (EQ1: Vptrofs sz0 = Vptrofs sz) by congruence.
  assert (EQ2: sz0 = sz).
  { unfold Vptrofs in EQ1; destruct Archi.ptr64 eqn:SF.
    rewrite <- (Ptrofs.of_int64_to_int64 SF sz0), <- (Ptrofs.of_int64_to_int64 SF sz). congruence.
    rewrite <- (Ptrofs.of_int_to_int SF sz0), <- (Ptrofs.of_int_to_int SF sz). congruence.
  }
  subst sz0.
  split. constructor. intuition congruence.
+ split. constructor. intuition auto.
Qed.

(** ** Semantics of [memcpy] operations. *)

(* JT: NOTE: Same remarks as before. *)
(* RB: NOTE: This operation seems particularly interesting in the sense that it
   copies between two blocks, and their respective ownerships must agree. *)

Inductive extcall_memcpy_sem (cp: compartment) (sz al: Z) (ge: Senv.t):
                        list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_memcpy_sem_intro: forall bdst odst bsrc osrc m bytes m',
      al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz >= 0 -> (al | sz) ->
      (sz > 0 -> (al | Ptrofs.unsigned osrc)) ->
      (sz > 0 -> (al | Ptrofs.unsigned odst)) ->
      bsrc <> bdst \/ Ptrofs.unsigned osrc = Ptrofs.unsigned odst
                   \/ Ptrofs.unsigned osrc + sz <= Ptrofs.unsigned odst
                   \/ Ptrofs.unsigned odst + sz <= Ptrofs.unsigned osrc ->
      Mem.loadbytes m bsrc (Ptrofs.unsigned osrc) sz (Some cp) = Some bytes ->
      Mem.storebytes m bdst (Ptrofs.unsigned odst) bytes cp = Some m' ->
      extcall_memcpy_sem cp sz al ge (Vptr bdst odst :: Vptr bsrc osrc :: nil) m E0 Vundef m'.

Lemma extcall_memcpy_ok:
  forall cp sz al,
  extcall_properties (extcall_memcpy_sem cp sz al)
                     (mksignature (Tptr :: Tptr :: nil) Tvoid cc_default).
Proof.
  intros. constructor.
- (* return type *)
  intros. inv H. exact I.
- (* change of globalenv *)
  intros. inv H0. econstructor; eauto.
- (* valid blocks *)
  intros. inv H. eauto with mem.
- (* accessibility *)
  intros. inv H. eapply Mem.storebytes_can_access_block_inj_1; eauto.
- (* perms *)
  intros. inv H. eapply Mem.perm_storebytes_2; eauto.
- (* readonly *)
  intros. inv H. eapply unchanged_on_readonly; eauto. 
  eapply Mem.storebytes_unchanged_on; eauto.
  intros; red; intros. elim H11.
  apply Mem.perm_cur_max. eapply Mem.storebytes_range_perm; eauto.
- (* extensions *)
  intros. inv H.
  inv H1. inv H13. inv H14. inv H10. inv H11.
  exploit Mem.loadbytes_length; eauto. intros LEN.
  exploit Mem.loadbytes_extends; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_within_extends; eauto. intros [m2' [C D]].
  exists Vundef; exists m2'.
  split. econstructor; eauto.
  split. constructor.
  split. auto.
  eapply Mem.storebytes_unchanged_on; eauto. unfold loc_out_of_bounds; intros.
  assert (Mem.perm m1 bdst i Max Nonempty).
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  eapply Mem.storebytes_range_perm; eauto.
  erewrite list_forall2_length; eauto.
  tauto.
- (* injections *)
  intros. inv H0. inv H2. inv H14. inv H15. inv H11. inv H12.
  destruct (zeq sz 0).
+ (* special case sz = 0 *)
  assert (bytes = nil).
  { exploit (Mem.loadbytes_empty m1 bsrc (Ptrofs.unsigned osrc) sz (Some cp)). lia.
    eapply Mem.loadbytes_can_access_block_inj; eauto.
    congruence. }
  subst.
  destruct (Mem.range_perm_storebytes m1' b0 (Ptrofs.unsigned (Ptrofs.add odst (Ptrofs.repr delta0))) nil cp)
  as [m2' SB].
  simpl. red; intros; extlia.
  eapply Mem.mi_own; eauto. eapply Mem.mi_inj; eauto.
  eapply Mem.storebytes_can_access_block_1; eauto.
  exists f, Vundef, m2'.
  split. econstructor; eauto.
  intros; extlia.
  intros; extlia.
  right; lia.
  apply Mem.loadbytes_empty. lia.
  eapply Mem.mi_own; eauto. eapply Mem.mi_inj; eauto.
  eapply Mem.loadbytes_can_access_block_inj; eauto.
  split. auto.
  split. eapply Mem.storebytes_empty_inject; eauto.
  split. eapply Mem.storebytes_unchanged_on; eauto. unfold loc_unmapped; intros.
  congruence.
  split. eapply Mem.storebytes_unchanged_on; eauto.
  simpl; intros; extlia.
  split. apply inject_incr_refl.
  red; intros; congruence.
+ (* general case sz > 0 *)
  exploit Mem.loadbytes_length; eauto. intros LEN.
  assert (RPSRC: Mem.range_perm m1 bsrc (Ptrofs.unsigned osrc) (Ptrofs.unsigned osrc + sz) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
  assert (RPDST: Mem.range_perm m1 bdst (Ptrofs.unsigned odst) (Ptrofs.unsigned odst + sz) Cur Nonempty).
    replace sz with (Z.of_nat (length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply Z2Nat.id. lia.
  assert (PSRC: Mem.perm m1 bsrc (Ptrofs.unsigned osrc) Cur Nonempty).
    apply RPSRC. lia.
  assert (PDST: Mem.perm m1 bdst (Ptrofs.unsigned odst) Cur Nonempty).
    apply RPDST. lia.
  exploit Mem.address_inject.  eauto. eexact PSRC. eauto. intros EQ1.
  exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
  exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_mapped_inject; eauto. intros [m2' [C D]].
  exists f; exists Vundef; exists m2'.
  split. econstructor; try rewrite EQ1; try rewrite EQ2; eauto.
  intros; eapply Mem.aligned_area_inject with (m := m1); eauto.
  eapply Mem.loadbytes_can_access_block_inj; eauto.
  intros; eapply Mem.aligned_area_inject with (m := m1); eauto.
  eapply Mem.storebytes_can_access_block_1; eauto.
  eapply Mem.disjoint_or_equal_inject with (m := m1); eauto.
  apply Mem.range_perm_max with Cur; auto.
  apply Mem.range_perm_max with Cur; auto. lia.
  split. constructor.
  split. auto.
  split. eapply Mem.storebytes_unchanged_on; eauto. unfold loc_unmapped; intros.
  congruence.
  split. eapply Mem.storebytes_unchanged_on; eauto. unfold loc_out_of_reach; intros. red; intros.
  eelim H2; eauto.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Writable; auto with mem.
  eapply Mem.storebytes_range_perm; eauto.
  erewrite list_forall2_length; eauto.
  lia.
  split. apply inject_incr_refl.
  red; intros; congruence.
- (* trace length *)
  intros; inv H. simpl; lia.
- (* receptive *)
  intros.
  assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
- (* determ *)
  intros; inv H; inv H0. split. constructor. intros; split; congruence.
Qed.

(** ** Semantics of annotations. *)

(* JT: NOTE: Same as before *)

Inductive extcall_annot_sem (cp: compartment) (text: string) (targs: list typ) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_annot_sem_intro: forall vargs m args,
      eventval_list_match ge args targs vargs ->
      extcall_annot_sem cp text targs ge vargs m (Event_annot text args :: E0) Vundef m.

Lemma extcall_annot_ok:
  forall cp text targs,
  extcall_properties (extcall_annot_sem cp text targs)
                     (mksignature targs Tvoid cc_default).
Proof.
  intros; constructor; intros.
(* well typed *)
- inv H. simpl. auto.
(* symbols *)
- destruct H as (A & B & C). inv H0. econstructor; eauto.
  eapply eventval_list_match_preserved; eauto.
(* valid blocks *)
- inv H; auto.
(* accessibility *)
- inv H; auto.
(* perms *)
- inv H; auto.
(* readonly *)
- inv H; auto.
(* mem extends *)
- inv H.
  exists Vundef; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_lessdef; eauto.
(* mem injects *)
- inv H0.
  exists f; exists Vundef; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_list_match_inject; eauto.
  red; intros; congruence.
(* trace length *)
- inv H; simpl; lia.
(* receptive *)
- assert (t1 = t2). inv H; inv H0; auto.
  exists vres1; exists m1; congruence.
(* determ *)
- inv H; inv H0.
  assert (args = args0). eapply eventval_list_match_determ_2; eauto. subst args0.
  split. constructor. auto.
Qed.

Inductive extcall_annot_val_sem (cp: compartment) (text: string) (targ: typ) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_annot_val_sem_intro: forall varg m arg,
      eventval_match ge arg targ varg ->
      extcall_annot_val_sem cp text targ ge (varg :: nil) m (Event_annot text (arg :: nil) :: E0) varg m.

Lemma extcall_annot_val_ok:
  forall cp text targ,
  extcall_properties (extcall_annot_val_sem cp text targ)
                     (mksignature (targ :: nil) targ cc_default).
Proof.
  intros; constructor; intros.
(* well typed *)
- inv H. eapply eventval_match_type; eauto.
(* symbols *)
- destruct H as (A & B & C). inv H0. econstructor; eauto.
  eapply eventval_match_preserved; eauto.
(* valid blocks *)
- inv H; auto.
(* accessibility *)
- inv H; auto.
(* perms *)
- inv H; auto.
(* readonly *)
- inv H; auto.
(* mem extends *)
- inv H. inv H1. inv H6.
  exists v2; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_match_lessdef; eauto.
(* mem inject *)
- inv H0. inv H2. inv H7.
  exists f; exists v'; exists m1'; intuition.
  econstructor; eauto.
  eapply eventval_match_inject; eauto.
  red; intros; congruence.
(* trace length *)
- inv H; simpl; lia.
(* receptive *)
- assert (t1 = t2). inv H; inv H0; auto. subst t2.
  exists vres1; exists m1; auto.
(* determ *)
- inv H; inv H0.
  assert (arg = arg0). eapply eventval_match_determ_2; eauto. subst arg0.
  split. constructor. auto.
Qed.

Inductive extcall_debug_sem (cp: compartment) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | extcall_debug_sem_intro: forall vargs m,
      extcall_debug_sem cp ge vargs m E0 Vundef m.

Lemma extcall_debug_ok:
  forall cp targs,
  extcall_properties (extcall_debug_sem cp)
                     (mksignature targs Tvoid cc_default).
Proof.
  intros; constructor; intros.
(* well typed *)
- inv H. simpl. auto.
(* symbols *)
- inv H0. econstructor; eauto.
(* valid blocks *)
- inv H; auto.
(* accessibility *)
- inv H; auto.
(* perms *)
- inv H; auto.
(* readonly *)
- inv H; auto.
(* mem extends *)
- inv H.
  exists Vundef; exists m1'; intuition.
  econstructor; eauto.
(* mem injects *)
- inv H0.
  exists f; exists Vundef; exists m1'; intuition.
  econstructor; eauto.
  red; intros; congruence.
(* trace length *)
- inv H; simpl; lia.
(* receptive *)
- inv H; inv H0. exists Vundef, m1; constructor.
(* determ *)
- inv H; inv H0.
  split. constructor. auto.
Qed.

(** ** Semantics of known built-in functions. *)

(* JT: NOTE: Same as before *)
(* JT: NOTE: Also, this is the kind of functions that should be inlinable even
  when they are used in another component *)

(** Some built-in functions and runtime support functions have known semantics
  as defined in the [Builtin] modules.
  These built-in functions have no observable effects and do not access memory. *)

Inductive known_builtin_sem (bf: builtin_function) (ge: Senv.t):
              list val -> mem -> trace -> val -> mem -> Prop :=
  | known_builtin_sem_intro: forall vargs vres m,
      builtin_function_sem bf vargs = Some vres ->
      known_builtin_sem bf ge vargs m E0 vres m.

Lemma known_builtin_ok: forall bf,
  extcall_properties (known_builtin_sem bf) (builtin_function_sig bf).
Proof.
  intros. set (bsem := builtin_function_sem bf). constructor; intros.
(* well typed *)
- inv H.
  specialize (bs_well_typed  _ bsem vargs).
  unfold val_opt_has_rettype, bsem; rewrite H0.
  auto.
(* symbols *)
- inv H0. econstructor; eauto.
(* valid blocks *)
- inv H; auto.
(* accessibility *)
- inv H; auto.
(* perms *)
- inv H; auto.
(* readonly *)
- inv H; auto.
(* mem extends *)
- inv H. fold bsem in H2. apply val_inject_list_lessdef in H1.
  specialize (bs_inject _ bsem _ _ _ H1).
  unfold val_opt_inject; rewrite H2; intros.
  destruct (bsem vargs') as [vres'|] eqn:?; try contradiction.
  exists vres', m1'; intuition auto using Mem.extends_refl, Mem.unchanged_on_refl.
  constructor; auto.
  apply val_inject_lessdef; auto.
(* mem injects *)
- inv H0. fold bsem in H3.
  specialize (bs_inject _ bsem _ _ _ H2).
  unfold val_opt_inject; rewrite H3; intros.
  destruct (bsem vargs') as [vres'|] eqn:?; try contradiction.
  exists f, vres', m1'; intuition auto using Mem.extends_refl, Mem.unchanged_on_refl.
  constructor; auto.
  red; intros; congruence.
(* trace length *)
- inv H; simpl; lia.
(* receptive *)
- inv H; inv H0. exists vres1, m1; constructor; auto. 
(* determ *)
- inv H; inv H0.
  split. constructor. intuition congruence. 
Qed.

(** ** Semantics of external functions. *)

(** For functions defined outside the program ([EF_external]),
  we do not define their semantics, but only assume that it satisfies
  [extcall_properties], and that they do not depend on the calling compartment.
  We do the same for built-in functions and runtime support functions that
  are not described in [Builtins].
*)

Parameter external_functions_sem: String.string -> signature -> extcall_sem.

Axiom external_functions_properties:
  forall id sg, extcall_properties (external_functions_sem id sg) sg.

(* Axiom external_functions_caller_independent: *)
(*   forall cp id sg, extcall_caller_independent cp (external_functions_sem id sg). *)
(* Hint Resolve external_functions_caller_independent : caller_independent. *)

(** We treat inline assembly similarly. *)

Parameter inline_assembly_sem: compartment -> String.string -> signature -> extcall_sem.

Axiom inline_assembly_properties:
  forall cp id sg, extcall_properties (inline_assembly_sem cp id sg) sg.

(* Axiom inline_assembly_caller_independent: *)
(*   forall cp id sg, extcall_caller_independent cp (inline_assembly_sem id sg). *)
(* Hint Resolve inline_assembly_caller_independent : caller_independent. *)

(** ** Combined semantics of external calls *)

Definition builtin_or_external_sem name sg :=
  match lookup_builtin_function name sg with
  | Some bf => known_builtin_sem bf
  | None => external_functions_sem name sg
  end.

Lemma builtin_or_external_sem_ok: forall name sg,
  extcall_properties (builtin_or_external_sem name sg) sg.
Proof.
  unfold builtin_or_external_sem; intros. 
  destruct (lookup_builtin_function name sg) as [bf|] eqn:L.
- exploit lookup_builtin_function_sig; eauto. intros EQ; subst sg.
  apply known_builtin_ok.
- apply external_functions_properties.
Qed.

(* Lemma builtin_or_external_caller_independent: *)
(*   forall cp name sg, *)
(*   extcall_caller_independent cp (builtin_or_external_sem name sg). *)
(* Proof. *)
(*   unfold builtin_or_external_sem. *)
(*   intros cp name sg. *)
(*   destruct (lookup_builtin_function name sg). *)
(*   - now intros ????????? H; inv H; constructor. *)
(*   - now apply external_functions_caller_independent. *)
(* Qed. *)
(* Hint Resolve builtin_or_external_caller_independent : caller_independent. *)

(** Combining the semantics given above for the various kinds of external calls,
  we define the predicate [external_call] that relates:
- the external function being invoked
- the values of the arguments passed to this function
- the memory state before the call
- the result value of the call
- the memory state after the call
- the trace generated by the call (can be empty).

This predicate is used in the semantics of all CompCert languages. *)

Definition external_call (ef: external_function): extcall_sem :=
  match ef with
  | EF_external cp name sg  => external_functions_sem name sg
  | EF_builtin cp name sg      => builtin_or_external_sem name sg
  | EF_runtime cp name sg      => builtin_or_external_sem name sg
  | EF_vload cp chunk          => volatile_load_sem cp chunk
  | EF_vstore cp chunk         => volatile_store_sem cp chunk
  | EF_malloc cp                => extcall_malloc_sem cp
  | EF_free cp                 => extcall_free_sem cp
  | EF_memcpy cp sz al         => extcall_memcpy_sem cp sz al
  | EF_annot cp kind txt targs   => extcall_annot_sem cp txt targs
  | EF_annot_val cp kind txt targ => extcall_annot_val_sem cp txt targ
  | EF_inline_asm cp txt sg clb => inline_assembly_sem cp txt sg
  | EF_debug kind cp txt targs => extcall_debug_sem cp
  end.

Ltac external_call_caller_independent :=
  intros ????????? CALL;
  inv CALL;
  econstructor;
  eauto.

(* Lemma external_call_caller_independent: *)
(*   forall ef: external_function, *)
(*   extcall_caller_independent (comp_of ef) (external_call ef). *)
(* Proof. *)
(*   destruct ef; simpl; try easy; *)
(*   eauto with caller_independent; *)
(*   try solve [external_call_caller_independent]. *)
(*   { *)
(*   intros ge cp1 cp2 args m t v m'. *)
(*   unfold uptodate_caller, needs_calling_comp, needs_calling_comp_map. simpl. *)
(*   rewrite PMap.gsspec, PMap.gi. *)
(*   destruct (peq cp default_compartment) as [|neq]; try easy. *)
(*   intros E. rewrite E; trivial. *)
(*   } *)
(*   { *)
(*   intros ge cp1 cp2 args m t v m'. *)
(*   unfold uptodate_caller, needs_calling_comp, needs_calling_comp_map. simpl. *)
(*   rewrite PMap.gsspec, PMap.gi. *)
(*   destruct (peq (comp_of (EF_vstore chunk)) privileged_compartment) as [|neq]; try easy. *)
(*   intros E. rewrite E; trivial. *)
(*   } *)
(*   intros ge cp1 cp2 args m t v m'. *)
(*   unfold uptodate_caller, needs_calling_comp, needs_calling_comp_map. simpl. *)
(*   rewrite PMap.gsspec, PMap.gi. *)
(*   destruct (peq (comp_of EF_malloc) privileged_compartment) as [|neq]; try easy. *)
(*   intros E. rewrite E; trivial. *)
(*   (* RB: NOTE: Two new goals left to solve. One of them can be solved by an *)
(*      identical procedure. *) *)
(*   intros ge cp1 cp2 args m t v m'. *)
(*   unfold uptodate_caller, needs_calling_comp, needs_calling_comp_map. simpl. *)
(*   rewrite PMap.gsspec, PMap.gi. *)
(*   destruct (peq (comp_of EF_free) privileged_compartment) as [|neq]; try easy. *)
(*   intros E. rewrite E; trivial. *)
(*   (* RB: NOTE: The last goal, on EF_memcpy, cannot be solved by means of this *)
(*      strategy, and needs a closer look. *) *)
(*   intros ge cp1 cp2 args m t v m'. *)
(*   unfold uptodate_caller, needs_calling_comp, needs_calling_comp_map. simpl. *)
(*   rewrite PMap.gsspec, PMap.gi. *)
(*   destruct (peq (comp_of (EF_memcpy sz al)) privileged_compartment) as [|neq]; try easy. *)
(*   intros E. rewrite E; trivial. *)
(* Qed. *)

Theorem external_call_spec:
  forall ef,
  extcall_properties (external_call ef) (ef_sig ef).
Proof.
  intros. unfold external_call, ef_sig; destruct ef.
  apply external_functions_properties.
  apply builtin_or_external_sem_ok.
  apply builtin_or_external_sem_ok.
  apply volatile_load_ok.
  apply volatile_store_ok.
  apply extcall_malloc_ok.
  apply extcall_free_ok.
  apply extcall_memcpy_ok.
  apply extcall_annot_ok.
  apply extcall_annot_val_ok.
  apply inline_assembly_properties.
  apply extcall_debug_ok.
Qed.

Definition external_call_well_typed_gen ef := ec_well_typed (external_call_spec ef).
Definition external_call_symbols_preserved ef := ec_symbols_preserved (external_call_spec ef).
Definition external_call_valid_block ef := ec_valid_block (external_call_spec ef).
Definition external_call_can_access_block ef := ec_can_access_block (external_call_spec ef).
Definition external_call_max_perm ef := ec_max_perm (external_call_spec ef).
Definition external_call_readonly ef := ec_readonly (external_call_spec ef).
Definition external_call_mem_extends ef := ec_mem_extends (external_call_spec ef).
Definition external_call_mem_inject_gen ef := ec_mem_inject (external_call_spec ef).
Definition external_call_trace_length ef := ec_trace_length (external_call_spec ef).
Definition external_call_receptive ef := ec_receptive (external_call_spec ef).
Definition external_call_determ ef := ec_determ (external_call_spec ef).

(** Corollary of [external_call_well_typed_gen]. *)

Lemma external_call_well_typed:
  forall ef ge vargs m1 t vres m2,
  external_call ef ge vargs m1 t vres m2 ->
  Val.has_type vres (proj_sig_res (ef_sig ef)).
Proof.
  intros. apply Val.has_proj_rettype. eapply external_call_well_typed_gen; eauto.
Qed.

(** Corollary of [external_call_valid_block]. *)

Lemma external_call_nextblock:
  forall ef ge vargs m1 t vres m2,
  external_call ef ge vargs m1 t vres m2 ->
  Ple (Mem.nextblock m1) (Mem.nextblock m2).
Proof.
  intros. destruct (plt (Mem.nextblock m2) (Mem.nextblock m1)).
  exploit external_call_valid_block; eauto. intros.
  eelim Plt_strict; eauto.
  unfold Plt, Ple in *; zify; lia.
Qed.

(** Special case of [external_call_mem_inject_gen] (for backward compatibility) *)

Definition meminj_preserves_globals (F V: Type) (ge: Genv.t F V) (f: block -> option (block * Z)) : Prop :=
     (forall id b, Genv.find_symbol ge id = Some b -> f b = Some(b, 0))
  /\ (forall b gv, Genv.find_var_info ge b = Some gv -> f b = Some(b, 0))
  /\ (forall b1 b2 delta gv, Genv.find_var_info ge b2 = Some gv -> f b1 = Some(b2, delta) -> b2 = b1).

Lemma external_call_mem_inject:
  forall ef F V (ge: Genv.t F V) vargs m1 t vres m2 f m1' vargs',
  meminj_preserves_globals ge f ->
  external_call ef ge vargs m1 t vres m2 ->
  Mem.inject f m1 m1' ->
  Val.inject_list f vargs vargs' ->
  exists f', exists vres', exists m2',
     external_call ef ge vargs' m1' t vres' m2'
    /\ Val.inject f' vres vres'
    /\ Mem.inject f' m2 m2'
    /\ Mem.unchanged_on (loc_unmapped f) m1 m2
    /\ Mem.unchanged_on (loc_out_of_reach f m1) m1' m2'
    /\ inject_incr f f'
    /\ inject_separated f f' m1 m1'.
Proof.
  intros. destruct H as (A & B & C). eapply external_call_mem_inject_gen with (ge1 := ge); eauto.
  repeat split; intros.
  + simpl in H3. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H3. exploit A; eauto. intros EQ; rewrite EQ in H; inv H. auto.
  + simpl in H3. exists b1; split; eauto.
  + simpl; unfold Genv.block_is_volatile.
    destruct (Genv.find_var_info ge b1) as [[c1 gv1]|] eqn:V1.
    * exploit B; eauto. intros EQ; rewrite EQ in H; inv H. rewrite V1; auto.
    * destruct (Genv.find_var_info ge b2) as [[c2 gv2]|] eqn:V2; auto.
      exploit C; eauto. intros EQ; subst b2. congruence.
Qed.

(** Corollaries of [external_call_determ]. *)

Lemma external_call_match_traces:
  forall ef ge vargs m t1 vres1 m1 t2 vres2 m2,
  external_call ef ge vargs m t1 vres1 m1 ->
  external_call ef ge vargs m t2 vres2 m2 ->
  match_traces ge t1 t2.
Proof.
  intros. exploit external_call_determ. eexact H. eexact H0. tauto.
Qed.

Lemma external_call_deterministic:
  forall ef ge vargs m t vres1 m1 vres2 m2,
  external_call ef ge vargs m t vres1 m1 ->
  external_call ef ge vargs m t vres2 m2 ->
  vres1 = vres2 /\ m1 = m2.
Proof.
  intros. exploit external_call_determ. eexact H. eexact H0. intuition.
Qed.

(** * Evaluation of builtin arguments *)

Section EVAL_BUILTIN_ARG.

Variable A: Type.
Variable ge: Senv.t.
Variable e: A -> val.
Variable sp: val.
Variable m: mem.

Inductive eval_builtin_arg: builtin_arg A -> val -> Prop :=
  | eval_BA: forall x,
      eval_builtin_arg (BA x) (e x)
  | eval_BA_int: forall n,
      eval_builtin_arg (BA_int n) (Vint n)
  | eval_BA_long: forall n,
      eval_builtin_arg (BA_long n) (Vlong n)
  | eval_BA_float: forall n,
      eval_builtin_arg (BA_float n) (Vfloat n)
  | eval_BA_single: forall n,
      eval_builtin_arg (BA_single n) (Vsingle n)
  | eval_BA_loadstack: forall chunk ofs cp v,
      Mem.loadv chunk m (Val.offset_ptr sp ofs) cp = Some v ->
      eval_builtin_arg (BA_loadstack chunk ofs) v
  | eval_BA_addrstack: forall ofs,
      eval_builtin_arg (BA_addrstack ofs) (Val.offset_ptr sp ofs)
  | eval_BA_loadglobal: forall chunk id ofs cp v,
      Mem.loadv chunk m (Senv.symbol_address ge id ofs) cp = Some v ->
      eval_builtin_arg (BA_loadglobal chunk id ofs) v
  | eval_BA_addrglobal: forall id ofs,
      eval_builtin_arg (BA_addrglobal id ofs) (Senv.symbol_address ge id ofs)
  | eval_BA_splitlong: forall hi lo vhi vlo,
      eval_builtin_arg hi vhi -> eval_builtin_arg lo vlo ->
      eval_builtin_arg (BA_splitlong hi lo) (Val.longofwords vhi vlo)
  | eval_BA_addptr: forall a1 a2 v1 v2,
      eval_builtin_arg a1 v1 -> eval_builtin_arg a2 v2 ->
      eval_builtin_arg (BA_addptr a1 a2)
                       (if Archi.ptr64 then Val.addl v1 v2 else Val.add v1 v2).

Definition eval_builtin_args (al: list (builtin_arg A)) (vl: list val) : Prop :=
  list_forall2 eval_builtin_arg al vl.

Lemma eval_builtin_arg_determ:
  forall a v, eval_builtin_arg a v -> forall v', eval_builtin_arg a v' -> v' = v.
Proof.
  induction 1; intros v' EV; inv EV; try congruence.
  { unfold Mem.loadv in H, H3.
    destruct (Val.offset_ptr sp ofs) eqn:E; try discriminate.
    apply Mem.load_result in H.
    apply Mem.load_result in H3. now subst. }
  { unfold Mem.loadv in H, H4.
    destruct (Senv.symbol_address ge id ofs) eqn:E; try discriminate.
    apply Mem.load_result in H.
    apply Mem.load_result in H4. now subst. }
  f_equal; eauto.
  apply IHeval_builtin_arg1 in H3. apply IHeval_builtin_arg2 in H5. subst; auto.
Qed.

Lemma eval_builtin_args_determ:
  forall al vl, eval_builtin_args al vl -> forall vl', eval_builtin_args al vl' -> vl' = vl.
Proof.
  induction 1; intros v' EV; inv EV; f_equal; eauto using eval_builtin_arg_determ.
Qed.

End EVAL_BUILTIN_ARG.

Global Hint Constructors eval_builtin_arg: barg.

(** Invariance by change of global environment. *)

Section EVAL_BUILTIN_ARG_PRESERVED.

Variables A F1 V1 F2 V2: Type.
Variable ge1: Genv.t F1 V1.
Variable ge2: Genv.t F2 V2.
Variable e: A -> val.
Variable sp: val.
Variable m: mem.

Hypothesis symbols_preserved:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.

Lemma eval_builtin_arg_preserved:
  forall a v, eval_builtin_arg ge1 e sp m a v -> eval_builtin_arg ge2 e sp m a v.
Proof.
  assert (EQ: forall id ofs, Senv.symbol_address ge2 id ofs = Senv.symbol_address ge1 id ofs).
  { unfold Senv.symbol_address; simpl; intros. rewrite symbols_preserved; auto. }
  induction 1; eauto with barg. rewrite <- EQ in H; eauto with barg. rewrite <- EQ; eauto with barg.
Qed.

Lemma eval_builtin_args_preserved:
  forall al vl, eval_builtin_args ge1 e sp m al vl -> eval_builtin_args ge2 e sp m al vl.
Proof.
  induction 1; constructor; auto; eapply eval_builtin_arg_preserved; eauto.
Qed.

End EVAL_BUILTIN_ARG_PRESERVED.

(** Compatibility with the "is less defined than" relation. *)

Section EVAL_BUILTIN_ARG_LESSDEF.

Variable A: Type.
Variable ge: Senv.t.
Variables e1 e2: A -> val.
Variable sp: val.
Variables m1 m2: mem.

Hypothesis env_lessdef: forall x, Val.lessdef (e1 x) (e2 x).
Hypothesis mem_extends: Mem.extends m1 m2.

Lemma eval_builtin_arg_lessdef:
  forall a v1, eval_builtin_arg ge e1 sp m1 a v1 ->
  exists v2, eval_builtin_arg ge e2 sp m2 a v2 /\ Val.lessdef v1 v2.
Proof.
  induction 1.
- exists (e2 x); auto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_extends; eauto. intros (v' & P & Q). exists v'; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_extends; eauto. intros (v' & P & Q). exists v'; eauto with barg.
- econstructor; eauto with barg.
- destruct IHeval_builtin_arg1 as (vhi' & P & Q).
  destruct IHeval_builtin_arg2 as (vlo' & R & S).
  econstructor; split; eauto with barg. apply Val.longofwords_lessdef; auto.
- destruct IHeval_builtin_arg1 as (vhi' & P & Q).
  destruct IHeval_builtin_arg2 as (vlo' & R & S).
  econstructor; split; eauto with barg. 
  destruct Archi.ptr64; auto using Val.add_lessdef, Val.addl_lessdef.
Qed.

Lemma eval_builtin_args_lessdef:
  forall al vl1, eval_builtin_args ge e1 sp m1 al vl1 ->
  exists vl2, eval_builtin_args ge e2 sp m2 al vl2 /\ Val.lessdef_list vl1 vl2.
Proof.
  induction 1.
- econstructor; split. constructor. auto.
- exploit eval_builtin_arg_lessdef; eauto. intros (v1' & P & Q).
  destruct IHlist_forall2 as (vl' & U & V).
  exists (v1'::vl'); split; constructor; auto.
Qed.

End EVAL_BUILTIN_ARG_LESSDEF.

Section INFORM_TRACES.

Variable F V: Type.
Variable ge: Genv.t F V.

Inductive call_trace: compartment -> compartment -> val -> list val -> list typ -> trace -> Prop :=
  | call_trace_intra: forall cp cp' vf vargs ty,
    Genv.type_of_call ge cp cp' <> Genv.CrossCompartmentCall ->
    call_trace cp cp' vf vargs ty E0
  | call_trace_cross: forall cp cp' vf vargs vl ty b ofs i,
      Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall ->
      vf = Vptr b ofs ->
      Genv.invert_symbol ge b = Some i ->
      eventval_list_match ge vl ty vargs ->
      call_trace cp cp' vf vargs ty (Event_call cp cp' i vl :: nil).

Lemma call_trace_same_cp:
  forall cp vf vargs tyargs t,
    call_trace cp cp vf vargs tyargs t ->
    t = E0.
Proof.
  intros. inv H; auto.
  now apply Genv.type_of_call_same_cp in H0.
Qed.

Inductive return_trace: compartment -> compartment -> val -> rettype -> trace -> Prop :=
| return_trace_intra: forall cp cp' v ty,
    Genv.type_of_call ge cp cp' <> Genv.CrossCompartmentCall ->
    return_trace cp cp' v ty E0
| return_trace_cross: forall cp cp' res v ty,
    Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall ->
    eventval_match ge res (proj_rettype ty) v ->
    return_trace cp cp' v ty (Event_return cp cp' res :: nil)
.

End INFORM_TRACES.

Section INFORM_TRACES_INJECT.
  Variable F V: Type.
  Variable F' V': Type.
  Variable ge: Genv.t F V.
  Variable ge': Genv.t F' V'.

  Variable j: meminj.

  (* I couldn't find a way to prove that with using [symbols_preserved]. *)
  Lemma call_trace_inj (symbols_preserved: forall (s: ident), Genv.find_symbol ge' s = Genv.find_symbol ge s):
    forall cp cp' vf vs vs' tys t,
      Val.inject_list j vs vs' ->
      (Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall -> Forall not_ptr vs) ->
      call_trace ge cp cp' vf vs tys t ->
      call_trace ge' cp cp' vf vs' tys t.
  Proof.
    intros cp cp' vf vs vs' tys t LD NPTR EV.
    inv EV.
    - constructor; auto.
    - specialize (NPTR H).
      econstructor; eauto. apply Genv.find_invert_symbol.
      rewrite symbols_preserved.
      eapply Genv.invert_find_symbol; eauto.
      clear -LD NPTR H2.
      revert vs vs' tys vl LD NPTR H2.
      induction vs; intros vs' tys vl LD NPTR Hmatch.
      + inv LD; inv Hmatch; constructor.
      + inv LD; inv Hmatch; inv NPTR.
        constructor; eauto.
        inv H1; inv H5; try contradiction; econstructor; eauto.
  Qed.

  Lemma return_trace_inj:
    forall cp cp' v v' ty t,
      Val.inject j v v' ->
      (Genv.type_of_call ge cp cp' = Genv.CrossCompartmentCall -> not_ptr v) ->
      return_trace ge cp cp' v ty t ->
      return_trace ge' cp cp' v' ty t.
  Proof.
    intros cp cp' v v' ty t LD NPTR EV.
    inv EV.
    - constructor; auto.
    - constructor; auto.
      specialize (NPTR H).
      inv LD; inv H0; try econstructor; eauto.
      inv NPTR.
  Qed.

End INFORM_TRACES_INJECT.

Section INFORM_TRACES_PRESERVED.
  Variable F V: Type.
  Variable F' V': Type.
  Variable ge: Genv.t F V.
  Variable ge': Genv.t F' V'.

  Variable symbols_preserved: forall (s: ident), Genv.find_symbol ge' s = Genv.find_symbol ge s.
  Variable senv_preserved: Senv.equiv ge ge'.

  Lemma call_trace_lessdef:
    forall cp cp' vf vs vs' tys t,
      Val.lessdef_list vs vs' ->
      call_trace ge cp cp' vf vs tys t ->
      call_trace ge' cp cp' vf vs' tys t.
  Proof.
    intros cp cp' vf vs vs' tys t LD EV.
    inv EV.
    - constructor; auto.
    - econstructor; eauto.
      apply Genv.invert_find_symbol in H1.
      apply Genv.find_invert_symbol.
      now rewrite symbols_preserved.
      eapply eventval_list_match_lessdef; eauto.
      eapply eventval_list_match_preserved with (ge1 := ge); try eapply senv_preserved; eauto.
  Qed.

  Lemma call_trace_eq:
    forall cp cp' vf vs tys t,
      call_trace ge cp cp' vf vs tys t ->
      call_trace ge' cp cp' vf vs tys t.
    Proof.
      intros.
      eapply call_trace_lessdef; eauto.
      clear.
      induction vs; eauto.
    Qed.

  Lemma return_trace_lessdef:
    forall cp cp' v v' ty t,
      Val.lessdef v v' ->
      return_trace ge cp cp' v ty t ->
      return_trace ge' cp cp' v' ty t.
  Proof.
    intros cp cp' v v' ty t LD EV.
    inv EV.
    - constructor; auto.
    - constructor; auto.
      eapply eventval_match_lessdef; eauto.
      eapply eventval_match_preserved with (ge1 := ge); try eapply senv_preserved; eauto.
  Qed.

  Lemma return_trace_eq:
    forall cp cp' v ty t,
      return_trace ge cp cp' v ty t ->
      return_trace ge' cp cp' v ty t.
  Proof.
    intros.
    eapply return_trace_lessdef; eauto using Val.lessdef_refl.
  Qed.

End INFORM_TRACES_PRESERVED.


Section VISIBLE.

  (* Memory location has only sequence of bytes *)
  Definition loc_first_order (m: mem) (b: block) (ofs: Z) : Prop :=
    match (ZMap.get ofs (Mem.mem_contents m) !! b) with
    | Byte _ => True
    | _ => False
    end.

  (* Public symbols are visible outside the compilation unit, 
     so when interacting via external calls, limit them to first-order (if Readable). *)
  Definition public_first_order (ge: Senv.t) (m: mem) :=
    forall id b ofs
      (PUBLIC: Senv.public_symbol ge id = true)
      (FIND: Senv.find_symbol ge id = Some b)
      (READABLE: Mem.perm m b ofs Cur Readable),
      loc_first_order m b ofs.

  Definition block_public (ge: Senv.t) (b: block): Prop :=
    exists id, Senv.invert_symbol ge b = Some id /\ Senv.public_symbol ge id = true.

  Variant val_public (ge: Senv.t) : typ -> val -> Prop :=
    | val_public_int: forall i, val_public ge Tint (Vint i)
    | val_public_long: forall i, val_public ge Tlong (Vlong i)
    | val_public_float: forall f, val_public ge Tfloat (Vfloat f)
    | val_public_single: forall f, val_public ge Tsingle (Vsingle f)
    | val_public_ptr: forall b ofs, block_public ge b -> val_public ge Tptr (Vptr b ofs).

  Definition vals_public (ge: Senv.t) (ts: list typ) (vs: list val): Prop :=
    Forall2 (val_public ge) ts vs.

  Definition visible_fo (ge: Senv.t) (m: mem) (tys: list typ) (args: list val): Prop :=
    public_first_order ge m /\ vals_public ge tys args.

  Definition EF_memcpy_dest_not_pub (ge: Senv.t) (args: list val) :=
    match args with
    | (Vptr bdst _) :: tl => ~ (block_public ge bdst)
    | _ => True
    end.

  Definition visible_fo_if_unknown
             (ef: external_function) (ge: Senv.t) (m: mem) (args: list val) : Prop :=
    match ef with
    | EF_external cp name sg => visible_fo ge m (sig_args sg) args
    | EF_builtin cp name sg | EF_runtime cp name sg =>
                             match lookup_builtin_function name sg with
                             | None => visible_fo ge m (sig_args sg) args
                             | _ => True
                             end
    | EF_inline_asm cp txt sg clb => visible_fo ge m (sig_args sg) args
    | EF_memcpy cp sz al => EF_memcpy_dest_not_pub ge args
    | _ => True
    end.

  Definition visible_fo_and_unknown
             (ef: external_function) (ge: Senv.t) (m: mem) (args: list val) : Prop :=
    match ef with
    | EF_external cp name sg => visible_fo ge m (sig_args sg) args
    | EF_builtin cp name sg | EF_runtime cp name sg =>
                             match lookup_builtin_function name sg with
                             | None => visible_fo ge m (sig_args sg) args
                             | _ => False
                             end
    | EF_inline_asm cp txt sg clb => visible_fo ge m (sig_args sg) args
    | _ => False
    end.


  (* Should be ensured by the user *)
  Definition unknown_returns_fo_pub
             (ef: external_function) (ge: Senv.t) (m: mem) (args: list val) : Prop :=
    match ef with
    | EF_external cp name sg =>
        forall ge args m0 tr rv m1, (external_functions_sem name sg ge args m0 tr rv m1) -> public_first_order ge m1
    | EF_builtin cp name sg
    | EF_runtime cp name sg =>
        match lookup_builtin_function name sg with
        | None => forall ge args m0 tr rv m1, (external_functions_sem name sg ge args m0 tr rv m1) -> public_first_order ge m1
        | _ => True
        end
    | EF_inline_asm cp txt sg clb =>
        forall ge args m0 tr rv m1, (inline_assembly_sem cp txt sg ge args m0 tr rv m1) -> public_first_order ge m1
    | _ => True
    end.

End VISIBLE.
