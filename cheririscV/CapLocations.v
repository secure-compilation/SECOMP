(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Locations are a refinement of RTL pseudo-registers, used to reflect
  the results of register allocation (file [Allocation]). *)

Require Import OrderedType.
Require Import Coqlib.
Require Import Maps.
Require Import Ordered.
Require Import CapAST.
Require Import OCapValues.
Require Export Machregs.
Require Export Locations.

(** * Representation of locations *)

(** On a capability machine, register that can hold capabilities are
twice as large. In CHERI Risc V, we model a merged register file,
which means longs and floats can be stored in a single
register. However, to keep compilation consistent, we still split them
up into two registers as if on a typical riscv machine. *)

Lemma slot_eq: forall (p q: slot), {p = q} + {p <> q}.
Proof.
  decide equality.
Defined.

Open Scope Z_scope.

Definition captypesize (ty: captyp) : Z :=
  match ty with
  | CTint => 1
  | CTlong => 2
  | CTfloat => 2
  | CTsingle => 1
  | CTany32 => 1
  | CTany64 => 2
  | CTany128 => 2
  | CTcap64 => 1
  | CTcap128 => 2
  end.

Lemma typesize_pos:
  forall (ty: typ), typesize ty > 0.
Proof.
  destruct ty; compute; auto.
Qed.

Definition typealign (ty: captyp) : Z :=
  match ty with
  | CTint => 1
  | CTlong => 2
  | CTfloat => 1
  | CTsingle => 1
  | CTany32 => 1
  | CTany64 => 1
  | CTany128 => 2
  | CTcap64 => 1
  | CTcap128 => 2
  end.

Lemma captypesize_pos:
  forall (ty: captyp), captypesize ty > 0.
Proof.
  destruct ty; compute; auto.
Qed.

(** ** Locations *)

(** Locations are just the disjoint union of machine registers and
  activation record slots. *)

(** ** Locations *)

(** Locations are just the disjoint union of machine registers and
  activation record slots. *)

Inductive caploc : Type :=
  | R (r: mreg)
  | S (sl: slot) (pos: Z) (ty: captyp).

Module Loc.

  Definition type (l: caploc) : captyp :=
    match l with
    | R r => mreg_captype r
    | S sl pos ty => ty
    end.

  Lemma eq: forall (p q: caploc), {p = q} + {p <> q}.
  Proof.
    decide equality.
    apply mreg_eq.
    apply captyp_eq.
    apply zeq.
    apply slot_eq.
  Defined.

(** As mentioned previously, two locations can be different (in the sense
  of the [<>] mathematical disequality), yet denote
  overlapping memory chunks within the activation record.
  Given two locations, three cases are possible:
- They are equal (in the sense of the [=] equality)
- They are different and non-overlapping.
- They are different but overlapping.

  The second case (different and non-overlapping) is characterized
  by the following [Loc.diff] predicate.
*)
  Definition diff (l1 l2: caploc) : Prop :=
    match l1, l2 with
    | R r1, R r2 =>
        r1 <> r2
    | S s1 d1 t1, S s2 d2 t2 =>
        s1 <> s2 \/ d1 + (captypesize t1) <= d2 \/ d2 + (captypesize t2) <= d1
    | _, _ =>
        True
    end.

  Lemma same_not_diff:
    forall l, ~(diff l l).
  Proof.
    destruct l; unfold diff; auto.
    red; intros. destruct H; auto. generalize (captypesize_pos ty). lia.
  Qed.

  Lemma diff_not_eq:
    forall l1 l2, diff l1 l2 -> l1 <> l2.
  Proof.
    unfold not; intros. subst l2. elim (same_not_diff l1 H).
  Qed.

  Lemma diff_sym:
    forall l1 l2, diff l1 l2 -> diff l2 l1.
  Proof.
    destruct l1; destruct l2; unfold diff; auto.
    intuition.
  Qed.

  Definition diff_dec (l1 l2: caploc) : { Loc.diff l1 l2 } + { ~Loc.diff l1 l2 }.
  Proof.
    intros. destruct l1; destruct l2; simpl.
  - destruct (mreg_eq r r0). right; tauto. left; auto.
  - left; auto.
  - left; auto.
  - destruct (slot_eq sl sl0).
    destruct (zle (pos + captypesize ty) pos0).
    left; auto.
    destruct (zle (pos0 + captypesize ty0) pos).
    left; auto.
    right; red; intros [P | [P | P]]. congruence. lia. lia.
    left; auto.
  Defined.

(** We now redefine some standard notions over lists, using the [Loc.diff]
  predicate instead of standard disequality [<>].

  [Loc.notin l ll] holds if the location [l] is different from all locations
  in the list [ll]. *)

  Fixpoint notin (l: caploc) (ll: list caploc) {struct ll} : Prop :=
    match ll with
    | nil => True
    | l1 :: ls => diff l l1 /\ notin l ls
    end.

  Lemma notin_iff:
    forall l ll, notin l ll <-> (forall l', In l' ll -> Loc.diff l l').
  Proof.
    induction ll; simpl.
    tauto.
    rewrite IHll. intuition. subst a. auto.
  Qed.

  Lemma notin_not_in:
    forall l ll, notin l ll -> ~(In l ll).
  Proof.
    intros; red; intros. rewrite notin_iff in H.
    elim (diff_not_eq l l); auto.
  Qed.

  Lemma notin_dec (l: caploc) (ll: list caploc) : {notin l ll} + {~notin l ll}.
  Proof.
    induction ll; simpl.
    left; auto.
    destruct (diff_dec l a).
    destruct IHll.
    left; auto.
    right; tauto.
    right; tauto.
  Defined.

(** [Loc.disjoint l1 l2] is true if the locations in list [l1]
  are different from all locations in list [l2]. *)

  Definition disjoint (l1 l2: list caploc) : Prop :=
    forall x1 x2, In x1 l1 -> In x2 l2 -> diff x1 x2.

  Lemma disjoint_cons_left:
    forall a l1 l2,
    disjoint (a :: l1) l2 -> disjoint l1 l2.
  Proof.
    unfold disjoint; intros. auto with coqlib.
  Qed.
  Lemma disjoint_cons_right:
    forall a l1 l2,
    disjoint l1 (a :: l2) -> disjoint l1 l2.
  Proof.
    unfold disjoint; intros. auto with coqlib.
  Qed.

  Lemma disjoint_sym:
    forall l1 l2, disjoint l1 l2 -> disjoint l2 l1.
  Proof.
    unfold disjoint; intros. apply diff_sym; auto.
  Qed.

  Lemma in_notin_diff:
    forall l1 l2 ll, notin l1 ll -> In l2 ll -> diff l1 l2.
  Proof.
    intros. rewrite notin_iff in H. auto.
  Qed.

  Lemma notin_disjoint:
    forall l1 l2,
    (forall x, In x l1 -> notin x l2) -> disjoint l1 l2.
  Proof.
    intros; red; intros. exploit H; eauto. rewrite notin_iff; intros. auto.
  Qed.

  Lemma disjoint_notin:
    forall l1 l2 x, disjoint l1 l2 -> In x l1 -> notin x l2.
  Proof.
    intros; rewrite notin_iff; intros. red in H. auto.
  Qed.

(** [Loc.norepet ll] holds if the locations in list [ll] are pairwise
  different. *)

  Inductive norepet : list caploc -> Prop :=
  | norepet_nil:
      norepet nil
  | norepet_cons:
      forall hd tl, notin hd tl -> norepet tl -> norepet (hd :: tl).

  Lemma norepet_dec (ll: list caploc) : {norepet ll} + {~norepet ll}.
  Proof.
    induction ll.
    left; constructor.
    destruct (notin_dec a ll).
    destruct IHll.
    left; constructor; auto.
    right; red; intros P; inv P; contradiction.
    right; red; intros P; inv P; contradiction.
  Defined.

(** [Caploc.no_overlap l1 l2] holds if elements of [l1] never overlap partially
  with elements of [l2]. *)

  Definition no_overlap (l1 l2 : list caploc) :=
   forall r, In r l1 -> forall s, In s l2 ->  r = s \/ Loc.diff r s.

End Loc.

(** * Mappings from locations to values *)

(** The [Locmap] module defines mappings from locations to values,
  used as evaluation environments for the semantics of the [LTL]
  and [Linear] intermediate languages.  *)

Set Implicit Arguments.

Module Locmap.

  Definition t := caploc -> ocval.

  Definition init (x: ocval) : t := fun (_: caploc) => x.

  Definition get (l: caploc) (m: t) : ocval := m l.

  (** The [set] operation over location mappings reflects the overlapping
      properties of locations: changing the value of a location [l]
      invalidates (sets to [Vundef]) the locations that partially overlap
      with [l].  In other terms, the result of [set l v m]
      maps location [l] to value [v], locations that overlap with [l]
      to [Vundef], and locations that are different (and non-overlapping)
      from [l] to their previous values in [m].  This is apparent in the
      ``good variables'' properties [Locmap.gss] and [Locmap.gso].

      Additionally, the [set] operation also anticipates the fact that
      abstract stack slots are mapped to concrete memory locations
      in the [Stacking] phase.  Hence, values stored in stack slots
      are normalized according to the type of the slot. *)

  Definition set (l: caploc) (v: ocval) (m: t) : t :=
    fun (p: caploc) =>
      if Loc.eq l p then
        match l with R r => v | S sl ofs ty => Val.load_result (chunk_of_type ty) v end
      else if Loc.diff_dec l p then
        m p
      else OCVundef.

  Lemma gss: forall l v m,
    (set l v m) l =
    match l with R r => v | S sl ofs ty => Val.load_result (chunk_of_type ty) v end.
  Proof.
    intros. unfold set. apply dec_eq_true.
  Qed.

  Lemma gss_reg: forall r v m, (set (R r) v m) (R r) = v.
  Proof.
    intros. unfold set. rewrite dec_eq_true. auto.
  Qed.

  Lemma gss_typed: forall l v m, Val.has_type v (Loc.type l) -> (set l v m) l = v.
  Proof.
    intros. rewrite gss. destruct l. auto. apply Val.load_result_same; auto.
  Qed.

  Lemma gso: forall l v m p, Loc.diff l p -> (set l v m) p = m p.
  Proof.
    intros. unfold set. destruct (Loc.eq l p).
    subst p. elim (Loc.same_not_diff _ H).
    destruct (Loc.diff_dec l p).
    auto.
    contradiction.
  Qed.

  Fixpoint undef (ll: list caploc) (m: t) {struct ll} : t :=
    match ll with
    | nil => m
    | l1 :: ll' => undef ll' (set l1 OCVundef m)
    end.

  Lemma guo: forall ll l m, Loc.notin l ll -> (undef ll m) l = m l.
  Proof.
    induction ll; simpl; intros. auto.
    destruct H. rewrite IHll; auto. apply gso. apply Loc.diff_sym; auto.
  Qed.

  Lemma gus: forall ll l m, In l ll -> (undef ll m) l = OCVundef.
  Proof.
    assert (P: forall ll l m, m l = OCVundef -> (undef ll m) l = OCVundef).
      induction ll; simpl; intros. auto. apply IHll.
      unfold set. destruct (Loc.eq a l).
      destruct a. auto. destruct ty; reflexivity.
      destruct (Loc.diff_dec a l); auto.
    induction ll; simpl; intros. contradiction.
    destruct H. apply P. subst a. apply gss_typed. exact I.
    auto.
  Qed.

  Definition getpair (p: rpair caploc) (m: t) : ocval :=
    match p with
    | One l => m l
    | Twolong l1 l2 => Val.longofwords (m l1) (m l2)
    end.

  Definition setpair (p: rpair mreg) (v: ocval) (m: t) : t :=
    match p with
    | One r => set (R r) v m
    | Twolong hi lo => set (R lo) (Val.loword  v) (set (R hi) (Val.hiword v) m)
    end.

  Lemma getpair_exten:
    forall p ls1 ls2,
    (forall l, In l (regs_of_rpair p) -> ls2 l = ls1 l) ->
    getpair p ls2 = getpair p ls1.
  Proof.
    intros. destruct p; simpl.
    apply H; simpl; auto.
    f_equal; apply H; simpl; auto.
  Qed.

  Lemma gpo:
    forall p v m l,
    forall_rpair (fun r => Loc.diff l (R r)) p -> setpair p v m l = m l.
  Proof.
    intros; destruct p; simpl in *.
  - apply gso. apply Loc.diff_sym; auto.
  - destruct H. rewrite ! gso by (apply Loc.diff_sym; auto). auto.
  Qed.

  Fixpoint setres (res: builtin_res mreg) (v: ocval) (m: t) : t :=
    match res with
    | BR r => set (R r) v m
    | BR_none => m
    | BR_splitlong hi lo =>
        setres lo (Val.loword v) (setres hi (Val.hiword v) m)
    end.

End Locmap.

(** * Total ordering over locations *)

Module IndexedTyp <: INDEXED_TYPE.
  Definition t := captyp.
  Definition index (x: t) :=
    match x with
    | CTany32 => 1%positive
    | CTint => 2%positive
    | CTsingle => 3%positive
    | CTany64 => 4%positive
    | CTfloat => 5%positive
    | CTlong => 6%positive
    | CTany128 => 7%positive
    | CTcap64 => 8%positive
    | CTcap128 => 9%positive
    end.
  Lemma index_inj: forall x y, index x = index y -> x = y.
  Proof. destruct x; destruct y; simpl; congruence. Qed.
  Definition eq := captyp_eq.
End IndexedTyp.

Module OrderedTyp := OrderedIndexed(IndexedTyp).

Module IndexedSlot <: INDEXED_TYPE.
  Definition t := slot.
  Definition index (x: t) :=
    match x with Local => 1%positive | Incoming => 2%positive | Outgoing => 3%positive end.
  Lemma index_inj: forall x y, index x = index y -> x = y.
  Proof. destruct x; destruct y; simpl; congruence. Qed.
  Definition eq := slot_eq.
End IndexedSlot.

Module OrderedSlot := OrderedIndexed(IndexedSlot).

Module OrderedLoc <: OrderedType.
  Definition t := caploc.
  Definition eq (x y: t) := x = y.
  Definition lt (x y: t) :=
    match x, y with
    | R r1, R r2 => Plt (IndexedMreg.index r1) (IndexedMreg.index r2)
    | R _, S _ _ _ => True
    | S _ _ _, R _ => False
    | S sl1 ofs1 ty1, S sl2 ofs2 ty2 =>
        OrderedSlot.lt sl1 sl2 \/ (sl1 = sl2 /\
        (ofs1 < ofs2 \/ (ofs1 = ofs2 /\ OrderedTyp.lt ty1 ty2)))
    end.
  Lemma eq_refl : forall x : t, eq x x.
  Proof. apply (@eq_refl t). Defined.
  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof (@eq_sym t).
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof (@eq_trans t).
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; intros.
    destruct x; destruct y; destruct z; try tauto.
    eapply Plt_trans; eauto.
    destruct H.
    destruct H0. left; eapply OrderedSlot.lt_trans; eauto.
    destruct H0. subst sl0. auto.
    destruct H. subst sl.
    destruct H0. auto.
    destruct H.
    right.  split. auto.
    intuition.
    right; split. congruence. eapply OrderedTyp.lt_trans; eauto.
  Qed.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold lt, eq; intros; red; intros. subst y.
    destruct x.
    eelim Plt_strict; eauto.
    destruct H. eelim OrderedSlot.lt_not_eq; eauto. red; auto.
    destruct H. destruct H0. lia.
    destruct H0. eelim OrderedTyp.lt_not_eq; eauto. red; auto.
  Qed.
  Definition compare : forall x y : t, Compare lt eq x y.
  Proof.
    intros. destruct x; destruct y.
  - destruct (OrderedPositive.compare (IndexedMreg.index r) (IndexedMreg.index r0)).
    + apply LT. red. auto.
    + apply EQ. red. f_equal. apply IndexedMreg.index_inj. auto.
    + apply GT. red. auto.
  - apply LT. red; auto.
  - apply GT. red; auto.
  - destruct (OrderedSlot.compare sl sl0).
    + apply LT. red; auto.
    + destruct (OrderedZ.compare pos pos0).
      * apply LT. red. auto.
      * destruct (OrderedTyp.compare ty ty0).
        apply LT. red; auto.
        apply EQ. red; red in e; red in e0; red in e1. congruence.
        apply GT. red; auto.
      * apply GT. red. auto.
    + apply GT. red; auto.
  Defined.
  Definition eq_dec := Loc.eq.

End OrderedLoc.
