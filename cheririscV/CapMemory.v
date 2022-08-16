(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*          with contributions from Andrew Appel, Rob Dockins,         *)
(*          and Gordon Stewart (Princeton University)                  *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This file develops the memory model that is used in the dynamic
  semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

Require Import Zwf.
Require Import Axioms.
Require Import Coqlib.
Require Intv.
Require Import Maps.
Require Archi.
Require Import CapAST.
Require Import Integers.
Require Import Floats.
(* Require Import Values. *)
Require Import OCapValues.
Require Export CapMemdata.
Require Export CapMemtype.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Local Notation "a # b" := (PMap.get b a) (at level 1).

Module Mem <: MEM.

Definition perm_order' (po: option permission) (p: permission) :=
  match po with
  | Some p' => perm_order p' p
  | None => False
 end.

Definition perm_order'' (po1 po2: option permission) :=
  match po1, po2 with
  | Some p1, Some p2 => perm_order p1 p2
  | _, None => True
  | None, Some _ => False
  end.

Record mem' : Type :=
  mkmem
{
  mem_contents: (ZMap.t memval);  (**r [offset -> memval] flattened memory *)
  mem_access: (Z -> perm_kind -> option permission);
                                  (**r [offset -> kind -> option permission] *)
  mem_compartments: PMap.t (list occap); (**r [compartment -> list occap] *)
  mem_next: Z;                    (**r the next address to be allocated *)
  mem_min: Z;                     (**r the lower bound to the heap *)
  access_max:
    forall ofs, perm_order'' (mem_access ofs Max) (mem_access ofs Cur);
  contents_default: fst mem_contents = Undef;
  mem_min_next: mem_min <= mem_next;
  mem_compartments_global:
    forall c l, mem_compartments !! c = l -> Forall (fun cap => isGlobalCap cap = true) l 
}.

Definition mem := mem'.

Lemma mkmem_ext:
  forall cont1 cont2 acc1 acc2 comp1 comp2,
  forall a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2,
    cont1=cont2 -> acc1=acc2 -> comp1=comp2 -> a1 = a2 -> b1 = b2 ->
  mkmem cont1 acc1 comp1 a1 b1 c1 d1 e1 f1 =
  mkmem cont2 acc2 comp2 a2 b2 c2 d2 e2 f2.
Proof.
  intros. subst. f_equal; apply proof_irr.
Qed.

(** * Validity of blocks and accesses *)

(** [block_compartment m c] returns the list of capabilities
    associated to compartment [c] *)

Definition block_compartment (m: mem) (c: compartment) :=
  m.(mem_compartments)!!c.

(** Permissions *)

Definition perm (m: mem) (ofs: Z) (k: perm_kind) (p: permission): Prop :=
  perm_order' (m.(mem_access) ofs k) p.

Theorem perm_implies:
  forall m ofs k p1 p2, perm m ofs k p1 -> perm_order p1 p2 -> perm m ofs k p2.
Proof.
  unfold perm, perm_order'; intros.
  destruct (m.(mem_access) ofs k); auto.
  eapply perm_order_trans; eauto.
Qed.

Local Hint Resolve perm_implies: mem.

Theorem perm_cur_max:
  forall m ofs p, perm m ofs Cur p -> perm m ofs Max p.
Proof.
  assert (forall po1 po2 p,
          perm_order' po2 p -> perm_order'' po1 po2 -> perm_order' po1 p).
  unfold perm_order', perm_order''. intros.
  destruct po2; try contradiction.
  destruct po1; try contradiction.
  eapply perm_order_trans; eauto.
  unfold perm; intros.
  generalize (access_max m ofs). eauto.
Qed.

Theorem perm_cur:
  forall m ofs k p, perm m ofs Cur p -> perm m ofs k p.
Proof.
  intros. destruct k; auto. apply perm_cur_max. auto.
Qed.

Theorem perm_max:
  forall m ofs k p, perm m ofs k p -> perm m ofs Max p.
Proof.
  intros. destruct k; auto. apply perm_cur_max. auto.
Qed.

Local Hint Resolve perm_cur perm_max: mem.

Remark perm_order_dec:
  forall p1 p2, {perm_order p1 p2} + {~perm_order p1 p2}.
Proof.
  intros. destruct p1; destruct p2; (left; constructor) || (right; intro PO; inversion PO).
Defined.

Remark perm_order'_dec:
  forall op p, {perm_order' op p} + {~perm_order' op p}.
Proof.
  intros. destruct op; unfold perm_order'.
  apply perm_order_dec.
  right; tauto.
Defined.

Theorem perm_dec:
  forall m ofs k p, {perm m ofs k p} + {~ perm m ofs k p}.
Proof.
  unfold perm; intros.
  apply perm_order'_dec.
Defined.

(* NOTE: RB: Keeping this limited to range checks instead of building in
   ownership checks as well. *)
Definition range_perm (m: mem) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m ofs k p.

Theorem range_perm_implies:
  forall m lo hi k p1 p2,
    range_perm m lo hi k p1 -> perm_order p1 p2 -> range_perm m lo hi k p2.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Theorem range_perm_cur:
  forall m lo hi k p,
  range_perm m lo hi Cur p -> range_perm m lo hi k p.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Theorem range_perm_max:
  forall m lo hi k p,
  range_perm m lo hi k p -> range_perm m lo hi Max p.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Local Hint Resolve range_perm_implies range_perm_cur range_perm_max: mem.

Lemma range_perm_dec:
  forall m lo hi k p, {range_perm m lo hi k p} + {~ range_perm m lo hi k p}.
Proof.
  intros.
  induction lo using (well_founded_induction_type (Zwf_up_well_founded hi)).
  destruct (zlt lo hi).
  destruct (perm_dec m lo k p).
  destruct (H (lo + 1)). red. omega.
  left; red; intros. destruct (zeq lo ofs). congruence. apply r. omega.
  right; red; intros. elim n. red; intros; apply H0; omega.
  right; red; intros. elim n. apply H0. omega.
  left; red; intros. omegaContradiction.
Defined.

(** [can_access_block m c cp] holds if a component [cp] has control
    over cap [c] in memory [m]. In the capability memory model without
    sharing, this means that [c] is derived from a capability owned by
    [cp] in the map from components to capabilities. *)

(** [can_access_block m c (Some cp)] holds if capability [c] is owned
    by compartment [cp] in memory [m]. *)

Lemma derived_cap_dec: forall c c', {derived_cap c c'} + {~ derived_cap c c'}.
Proof.
  intros. destruct c,c';auto;[| |right;intros Hcontr;inversion Hcontr;auto..|].
  - destruct o,o0;[|right;intros Hcontr;inversion Hcontr;auto..].
    destruct (Z_le_dec (Ptrofs.unsigned i) (Ptrofs.unsigned i2)).
    destruct (Z_le_dec (Ptrofs.unsigned i3) (Ptrofs.unsigned i0)).
    destruct (locFlowsTo l0 l) eqn:L.
    destruct (permFlowsTo p0 p) eqn:P.
    left. constructor;auto.
    all: right;intros Hcontr;inversion Hcontr;auto;congruence.
  - destruct o,o0;[|right;intros Hcontr;inversion Hcontr;inversion H1;auto..].
    destruct (Z_le_dec (Ptrofs.unsigned i) (Ptrofs.unsigned i2)).
    destruct (Z_le_dec (Ptrofs.unsigned i3) (Ptrofs.unsigned i0)).
    destruct (locFlowsTo l0 l) eqn:L.
    destruct (permFlowsTo p0 p) eqn:P.
    left. constructor;constructor;auto.
    all: right;intros Hcontr;inversion Hcontr;inversion H1;auto;congruence.
  - right. intros Hcontr. inversion Hcontr. inversion H1.
Qed.

Lemma disjoint_cap_dec: forall c c', {disjoint_cap c c'} + {~ disjoint_cap c c'}.
Proof.
  intros.
  destruct (Z_le_dec (Ptrofs.unsigned (get_hi c)) (Ptrofs.unsigned (get_lo c'))).
  left;left;auto.
  destruct (Z_ge_dec (Ptrofs.unsigned (get_lo c)) (Ptrofs.unsigned (get_hi c'))).
  left;right;auto.
  right. intros [Hcontr|Hcontr];omega.
Qed.  

Definition can_access_block (m: mem) (c: occap) (cp: option compartment): Prop :=
  match cp with
  | None => True
  | Some cp => Exists (fun c' => derived_cap c' c) (block_compartment m cp)
  end.

Remark can_access_block_dec:
  forall m b cp, {can_access_block m b cp} + {~can_access_block m b cp}.
Proof.
  unfold can_access_block.
  intros m b [cp |]; [| left; trivial].
  induction (block_compartment m cp).
  - right. easy.
  - induction (derived_cap_dec a b).
    + left. apply Exists_cons_hd. auto.
    + destruct IHl.
      * left. apply Exists_cons_tl. auto.
      * right. intros Hcontr.
        apply Exists_cons in Hcontr as [Hcontr|Hcontr];auto.
Defined.

(** [derive_offset a c ofs] derives the physical address from the
    capability [c] at offset [ofs], by applying the action kind [a] *)
Definition derive_offset (a: act_kind) (c: occap) (ofs: Z) : Z :=
  match a with
  | DIR => Ptrofs.unsigned (get_addr c)
  | UNINIT => Ptrofs.unsigned (get_addr c) + ofs
  | DEFAULT => Ptrofs.unsigned (get_lo c) + ofs
  end.

(** [max_read_auth c] derives the maximal read authority of a
    capability: the current address of an uninitialized capability,
    the upper bound of a non uninitialized capability or a sealed
    capability. In other words, it returns the maxmimum stack address
    a capability may potentially give access to, or None if there is
    no such address *)
Definition max_read_auth (c: occap): option ptrofs :=
  match c with
  | OCsealable c'
  | OCsealed _ c' =>
      match c' with
      | OCVmem perm l lo hi a => if isU perm then Some a else Some hi
      | _ => None
      end
  end.

(** [in_bounds k c ofs] checks that the accessed addressed is within
    the bounds of capability [c] *)
Definition in_bounds (k: act_kind) (c: occap) (ofs: Z) (len: nat): Prop :=
  match c with
  | OCsealable (OCVmem perm l lo hi a) => Ptrofs.unsigned lo <= derive_offset k c ofs
                                         /\ derive_offset k c ofs + Z.of_nat len < Ptrofs.unsigned hi
  | _ => False
  end.

(** [is_directed_store k c ofs v] checks that the maximum read
    authority of [v] is at most equal to the address [v] is stored at *)
Definition is_directed_store (k: act_kind) (c: occap) (ofs: Z) (v: ocval): Prop :=
  match v with
  | OCVcap c =>
      match max_read_auth c with
      | Some a' => Ptrofs.unsigned a' <= derive_offset k c ofs
      | None => True
      end
  | _ => True
  end.

Definition offset_le_cap (ofs: Z) (c: occap): Prop :=
  match c with
  | OCsealable (OCVmem perm l b e a) => ofs <= Ptrofs.unsigned a
  | _ => False
  end.

Definition offset_lt_cap (ofs: Z) (c: occap): Prop :=
  match c with
  | OCsealable (OCVmem perm l b e a) => ofs < Ptrofs.unsigned a
  | _ => False
  end.

(** [can_store_val k c ofs len v] holds if [v] can be stored via
    capability [c] at the derived address based on [c] and [ofs] *)
Definition can_store_val (k: act_kind) (c: occap) (ofs: Z) (len: nat) (v: ocval): Prop :=
  in_bounds k c ofs len
  /\ (if isUCap c then offset_le_cap (derive_offset k c ofs) c else writeAllowedCap c = true)
  /\ (if (is_global_or_imm v)
    then True
    else (pwlUCap c = true \/ pwlCap c = true) /\ is_directed_store k c ofs v).

(** [can_load_val k c ofs len] holfs if [c] can load bytes of length
    [len] at the derived offset from [c] and [ofs] *)
Definition can_load_val (k: act_kind) (c: occap) (ofs: Z) (len: nat): Prop :=
  in_bounds k c ofs len
  /\ (if isUCap c then offset_lt_cap (derive_offset k c ofs + Z.of_nat len) c else readAllowedCap c = true).



Theorem can_store_implies_can_load :
  forall k c ofs l v, (isUCap c = true -> offset_lt_cap (derive_offset k c ofs + Z.of_nat l) c)
                 -> can_store_val k c ofs l v
                 -> can_load_val k c ofs l.
Proof.
  intros until v.
  intros C L.
  inv L. destruct (isUCap c) eqn:Hc.
  - pose proof (C eq_refl).
    split;auto. rewrite Hc. auto.
  - split;auto. rewrite Hc.
    inv H0. destruct c,o; try easy.
    apply writeA_implies_readA;auto.
Qed.
  
Definition dynamic_access (k: act_kind) (c: occap) (ofs: Z) (l: nat) (v: option ocval) :=
  match v with
  | None => can_load_val k c ofs l
  | Some v => can_store_val k c ofs l v
  end.
           
Definition storeU_increase_derive (v: option ocval) (c: occap) (ofs: Z) (len: nat) : occap :=
  if (ofs =? 0) && isUCap c then
    match incr_addr_stk c (Z.of_nat len) with
    | Some c' => c'
    | _ => c
    end
  else c.
Definition storeU_increase_authority (v: option ocval) (c: occap) (ofs: Z) (len: nat) (c': option occap) :=
  match v with
  | Some _ =>
      if (ofs =? 0) && isUCap c
      then c' = match incr_addr_stk c (Z.of_nat len) with
                | Some c' => Some c'
                | _ => Some c
                end
      else c' = Some c
  | _ => c' = None
  end.

Lemma storeU_increase_authority_eq:
  forall v c ofs len c',
    storeU_increase_authority (Some v) c ofs len c' ->
    c' = Some (storeU_increase_derive (Some v) c ofs len).
Proof.
  intros.
  simpl in *.
  unfold storeU_increase_derive.
  destruct ((ofs =? 0) && isUCap c);auto.
  destruct (incr_addr_stk c (Z.of_nat len));auto.
Qed.

(** An access to a memory quantity [chunk] at address [c, ofs] with
  permission [p] is valid in [m] if the accessed addresses all have
  current permission [p] and moreover the offset is properly aligned, 
  if [v] is specified, [c] has sufficient authority to store it,
  and [c] belongs to compartment [cp]. *)
Definition valid_access_cap (k: act_kind) (chunk: cap_memory_chunk) (c: occap) (ofs: Z)
           (v: option ocval) (c': option occap): Prop :=
  dynamic_access k c ofs (size_chunk_nat chunk) v
  /\ storeU_increase_authority v c ofs (size_chunk_nat chunk) c'.
Definition valid_access_ptr (k: act_kind) (m: mem) (chunk: cap_memory_chunk) (c: occap) (ofs: Z)
           (p: permission) (cp: option compartment) : Prop :=
  range_perm m (derive_offset k c ofs) (derive_offset k c ofs + size_chunk chunk) Cur p
  /\ can_access_block m c cp
  /\ (align_chunk chunk | (derive_offset k c ofs)).
  
Definition valid_access (k: act_kind) (m: mem) (chunk: cap_memory_chunk) (c: occap) (ofs: Z)
           (p: permission) (cp: option compartment) (v: option ocval) (c': option occap): Prop :=
  valid_access_cap k chunk c ofs v c'
  /\ valid_access_ptr k m chunk c ofs p cp.

  (* range_perm m (derive_offset k c ofs) (derive_offset k c ofs + size_chunk chunk) Cur p *)
  (* /\ can_access_block m c cp *)
  (* /\ dynamic_access k c ofs (size_chunk_nat chunk) v *)
  (* /\ (align_chunk chunk | (derive_offset k c ofs)) *)
  (* /\ storeU_increase_authority v c ofs (size_chunk_nat chunk) c'. *)

Theorem valid_access_implies:
  forall k m chunk c ofs p1 p2 cp v c',
  valid_access k m chunk c ofs p1 cp v c' -> perm_order p1 p2 ->
  valid_access k m chunk c ofs p2 cp v c'.
Proof.
  intros until c'; intros V P.
  inv V. split;auto. inv H0.
  split;auto. eapply range_perm_implies;eauto.
Qed.

Theorem valid_access_perm:
  forall a k m chunk c ofs p cp v c',
    valid_access a m chunk c ofs p cp v c' ->
    perm m (derive_offset a c ofs) k p.
Proof.
  intros until c'. intros V.
  inv V. inv H0. apply perm_cur. apply H1.
  generalize (size_chunk_pos chunk). omega.
Qed.
  
Theorem valid_access_freeable_any:
  forall k m chunk ptr ofs p cp v ptr',
  valid_access k m chunk ptr ofs Freeable cp v ptr' ->
  valid_access k m chunk ptr ofs p cp v ptr'.
Proof.
  intros.
  eapply valid_access_implies; eauto. constructor.
Qed.

Local Hint Resolve valid_access_implies: mem.

Definition dynamic_conditions_ptr (m: mem) (c: occap) (cp: option compartment) : Prop :=
  can_access_block m c cp.
Definition dynamic_conditions_cap (k: act_kind) (c: occap) (ofs: Z) (len: Z)
           (v: option ocval) (c': option occap) : Prop :=
  dynamic_access k c ofs (Z.to_nat len) v
  /\ storeU_increase_authority v c ofs (Z.to_nat len) c'.             
Definition dynamic_conditions (m: mem) (k: act_kind) (c: occap) (ofs: Z) (len: Z)
           (v: option ocval) (cp: option compartment) (c': option occap) : Prop :=
  dynamic_conditions_ptr m c cp
  /\ dynamic_conditions_cap k c ofs len v c'.

Theorem dynamic_conditions_in_bounds:
  forall m k c ofs len v cp c',
    dynamic_conditions m k c ofs len v cp c' ->
    in_bounds k c ofs (Z.to_nat len).
Proof.
  intros until c'. intros [_ [D _]].
  destruct v;destruct D as [? ?];auto.
Qed.

Theorem valid_access_in_bounds:
  forall k m chunk c ofs p cp v c',
    valid_access k m chunk c ofs p cp v c' ->
    in_bounds k c ofs (size_chunk_nat chunk).
Proof.
  intros until c'. intros [[C _] _].
  destruct v;simpl in *; destruct C as [C _];auto.
Qed.

Local Hint Resolve dynamic_conditions_in_bounds valid_access_in_bounds.
  
(** [valid_capability m c] - where c is an unsealed capability -
     checks that it does not point to an empty region *)

Definition valid_capability (m: mem) (k: act_kind) (c: occap) (ofs: Z): bool :=
  match c with
  | OCsealable (OCVmem p l b e a) =>
      perm_dec m (derive_offset k c ofs) Cur Nonempty
  | _ => false
  end.
Inductive is_valid_capability : mem -> act_kind -> occap -> Z -> Prop :=
| valid_cap p l b e a m k ofs:
  perm m (derive_offset k (OCsealable (OCVmem p l b e a)) ofs) Cur Nonempty ->
  is_valid_capability m k (OCsealable (OCVmem p l b e a)) ofs.

Lemma is_valid_capability_iff:
  forall m k c ofs, valid_capability m k c ofs = true <-> is_valid_capability m k c ofs.
Proof.
  intros. split;intros C.
  - destruct c,o; try easy. constructor. 
    inv C.
    destruct (perm_dec m (derive_offset k (OCsealable (OCVmem p l i i0 i1)) ofs) Cur Nonempty);auto.
    simpl in *. congruence.
  - inv C. simpl.
    destruct (perm_dec m (derive_offset k (OCsealable (OCVmem p l b e a)) ofs) Cur Nonempty);auto.
Qed.    

Theorem valid_pointer_nonempty_perm:
  forall m k c ofs, is_mem_cap c ->
    valid_capability m k c ofs = true <-> perm m (derive_offset k c ofs) Cur Nonempty.
Proof.
  intros.
  split;intros C.
  - apply is_valid_capability_iff in C. inv C.
    auto.
  - apply is_valid_capability_iff.
    inv H. constructor. simpl in *.
    auto.
Qed.    

Lemma in_bounds_weaken:
  forall k c ofs l1 l2,
    (l1 <= l2)%nat ->
    in_bounds k c ofs l2 ->
    in_bounds k c ofs l1.
Proof.
  intros until l2. intros LE B.
  destruct c,o;try easy.
  inv B. split;auto.
  simpl in *. (* rewrite Z2Nat.id in H0;[|destruct chunk;simpl;omega]. *)
  (* generalize (size_chunk_pos chunk). *)
  omega.
Qed.
  
Theorem valid_pointer_valid_access:
  forall m k c ofs cp v c',
    dynamic_conditions m k c ofs 1 v cp c' ->
    valid_capability m k c ofs = true <-> valid_access k m CMint8unsigned c ofs Nonempty cp v c'.
Proof.
  intros until c'. intros D.
  apply dynamic_conditions_in_bounds in D as B.
  destruct D as [D1 [D2 D3]].
  split; intros V.
  - apply is_valid_capability_iff in V. inv V.
    repeat constructor;auto.
    + intros x [Hx1 Hx2]. simpl in *.
      assert (x = derive_offset k (OCsealable (OCVmem p l b e a)) ofs) as ->;[omega|].
      auto.
    + simpl. apply Z.divide_1_l.
  - apply is_valid_capability_iff.
    destruct c,o;try easy.
    constructor. destruct V as [_ [V _]].
    apply V. simpl. omega.
Qed.
    
Lemma size_chunk_nat_eq:
  forall chunk1 chunk2,
    size_chunk chunk1 = size_chunk chunk2 ->
    size_chunk_nat chunk1 = size_chunk_nat chunk2.
Proof.
  intros. destruct chunk1,chunk2;easy.
Qed.

Lemma valid_access_compat:
  forall m chunk1 chunk2 ptr p cp v ptr' k ofs,
  size_chunk chunk1 = size_chunk chunk2 ->
  align_chunk chunk2 <= align_chunk chunk1 ->
  valid_access k m chunk1 ptr ofs p cp v ptr' ->
  valid_access k m chunk2 ptr ofs p cp v ptr'.
Proof.
  intros until ofs. intros S A V.
  destruct V as [[V1 V2] [V3 [V4 V5]]].
  repeat constructor;auto.
  - erewrite size_chunk_nat_eq;eauto.
  - erewrite size_chunk_nat_eq;eauto.
  - intros x Hx. apply V3. omega.
  - eapply Z.divide_trans; eauto. eapply align_le_divides; eauto.  
Qed.

Lemma in_bounds_dec:
  forall k c ofs l, {in_bounds k c ofs l} + {~ in_bounds k c ofs l}.
Proof.
  intros. destruct c,o;auto.
  destruct (Z_le_dec (Ptrofs.unsigned i)
                     (derive_offset k (OCsealable (OCVmem p l0 i i0 i1)) ofs)).
  destruct (Z_lt_dec (derive_offset k (OCsealable (OCVmem p l0 i i0 i1)) ofs + Z.of_nat l)
                     (Ptrofs.unsigned i0)).
  left;split;auto.
  all:right;intros [Hcontr Hcontr'];easy.
Defined.
Lemma offset_le_cap_dec:
  forall a c, {offset_le_cap a c} + {~ offset_le_cap a c}.
Proof.
  intros. destruct c,o;auto.
  simpl. apply Z_le_dec.
Defined.
Lemma offset_lt_cap_dec:
  forall a c, {offset_lt_cap a c} + {~ offset_lt_cap a c}.
Proof.
  intros. destruct c,o;auto.
  simpl. apply Z_lt_dec.
Defined.
Lemma is_directed_store_dec:
  forall k c ofs v, {is_directed_store k c ofs v} + {~ is_directed_store k c ofs v}.
Proof.
  intros. unfold is_directed_store. destruct v;auto.
  destruct o,o;simpl;auto.
  all: destruct (isU p);auto;apply Z_le_dec.
Defined.
  
Lemma can_store_val_dec:
  forall k c ofs len v, {can_store_val k c ofs len v} + {~can_store_val k c ofs len v}.
Proof.
  intros.
  destruct (in_bounds_dec k c ofs len).
  unfold can_store_val.
  destruct (isUCap c).
  - destruct (offset_le_cap_dec (derive_offset k c ofs) c).
    destruct (is_global_or_imm v);auto.
    destruct (is_directed_store_dec k c ofs v).
    destruct (pwlUCap c).
    left; repeat split;auto.
    destruct (pwlCap c).
    left; repeat split;auto.
    1,2: right;intros [? [? [[?|?] ?]]];easy.
    right;intros [? [? ?]];easy.
  - destruct (writeAllowedCap c).
    destruct (is_global_or_imm v);auto.
    destruct (is_directed_store_dec k c ofs v).
    destruct (pwlUCap c).
    left; repeat split;auto.
    destruct (pwlCap c).
    left; repeat split;auto.
    1,2: right;intros [? [? [[?|?] ?]]];easy.
    right;intros [? [? ?]];easy.
  - right. intros [? ?];easy.
Defined.
Lemma can_load_val_dec:
  forall k c ofs len, {can_load_val k c ofs len} + {~can_load_val k c ofs len}.
Proof.
  intros.
  destruct (in_bounds_dec k c ofs len).
  unfold can_load_val.
  destruct (isUCap c).
  - destruct (offset_lt_cap_dec (derive_offset k c ofs + Z.of_nat len) c).
    left; repeat split;auto.
    all: right;intros [? ?];easy.
  - destruct (readAllowedCap c).
    left; repeat split;auto.
    all: right;intros [? ?];easy.
  - right. intros [? ?];easy.
Defined.

Lemma dynamic_access_dec:
  forall k c ofs l v, {dynamic_access k c ofs l v} + {~ dynamic_access k c ofs l v}.
Proof.
  intros. destruct v.
  apply can_store_val_dec.
  apply can_load_val_dec.
Defined.

Lemma storeU_increase_authority_dec:
  forall v c ofs l c', {storeU_increase_authority v c ofs l c'} + {~ storeU_increase_authority v c ofs l c'}.
Proof.
  intros. destruct v,c';simpl;auto;[..|right; intros Hcontr; easy].
  all: destruct ((ofs =? 0) && isUCap c); try destruct o1;auto.
  3: destruct c,o0;auto; try (right; intros Hcontr; easy).
  3: try (right; intros Hcontr; easy).
  1: destruct c,o1;auto; try (right; intros Hcontr; easy).
  set (o1:=(OCsealable (OCVmem p l0 i i0 (Ptrofs.repr (Ptrofs.unsigned i1 + Z.of_nat l))))).
  2: set (o1:=(OCsealable (OCVseal s s0 s1))).
  3: set (o1:=(OCsealed s (OCVmem p l0 i i0 i1))).
  4: set (o1:=(OCsealed s (OCVseal s0 s1 s2))).
  5: set (o1:=c).
  all: destruct (occap_dec o0 o1);subst;auto.
  all: right; intros Hcontr; inv Hcontr; easy.
Defined.

Lemma dynamic_conditions_ptr_dec:
  forall m c cp, {dynamic_conditions_ptr m c cp} + {~ dynamic_conditions_ptr m c cp}.
Proof. apply can_access_block_dec. Defined.
Lemma dynamic_conditions_cap_dec:
  forall k c ofs len v c', {dynamic_conditions_cap k c ofs len v c'} + {~ dynamic_conditions_cap k c ofs len v c'}.
Proof.
  intros.
  destruct (dynamic_access_dec k c ofs (Z.to_nat len) v).
  destruct (storeU_increase_authority_dec v c ofs (Z.to_nat len) c').
  left;repeat split;auto.
  all: right;intros [? ?];easy.
Defined.  
Lemma dynamic_conditions_dec:
  forall m k c ofs len v cp c',
    {dynamic_conditions m k c ofs len v cp c'} + {~ dynamic_conditions m k c ofs len v cp c'}.
Proof.
  intros.
  destruct (dynamic_conditions_ptr_dec m c cp).
  destruct (dynamic_conditions_cap_dec k c ofs len v c').
  left;split;auto.
  all: right;intros [? ?];easy.
Defined.

Lemma valid_access_cap_dec:
  forall k chunk c ofs v c', {valid_access_cap k chunk c ofs v c'} + {~ valid_access_cap k chunk c ofs v c'}.
Proof.
  intros. unfold valid_access_cap.
  destruct (dynamic_access_dec k c ofs (size_chunk_nat chunk) v).
  destruct (storeU_increase_authority_dec v c ofs (size_chunk_nat chunk) c').
  left;repeat split;auto.
  all: right;intros [? ?];easy.
Defined.
Lemma valid_access_ptr_dec:
  forall k m chunk c ofs p cp, {valid_access_ptr k m chunk c ofs p cp} + {~ valid_access_ptr k m chunk c ofs p cp}.
Proof.
  intros. unfold valid_access_ptr.
  destruct (range_perm_dec m (derive_offset k c ofs)
     (derive_offset k c ofs + size_chunk chunk) Cur p).
  destruct (can_access_block_dec m c cp).
  destruct (Zdivide_dec (align_chunk chunk) (derive_offset k c ofs)).
  left;repeat split;auto.
  all: right;intros [? [? ?]];easy.
Defined.
  
Lemma valid_access_dec:
  forall k m chunk c ofs p cp v c',
    {valid_access k m chunk c ofs p cp v c'} + {~ valid_access k m chunk c ofs p cp v c'}.
Proof.
  intros. unfold valid_access.
  destruct (valid_access_cap_dec k chunk c ofs v c').
  destruct (valid_access_ptr_dec k m chunk c ofs p cp).
  left;split;auto.
  all: right;intros [? ?];easy.
Defined.

(*
(** C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)

Definition weak_valid_pointer (m: mem) (b: block) (ofs: Z) :=
  valid_pointer m b ofs || valid_pointer m b (ofs - 1).

Lemma weak_valid_pointer_spec:
  forall m b ofs,
  weak_valid_pointer m b ofs = true <->
    valid_pointer m b ofs = true \/ valid_pointer m b (ofs - 1) = true.
Proof.
  intros. unfold weak_valid_pointer. now rewrite orb_true_iff.
Qed.
Lemma valid_pointer_implies:
  forall m b ofs,
  valid_pointer m b ofs = true -> weak_valid_pointer m b ofs = true.
Proof.
  intros. apply weak_valid_pointer_spec. auto.
Qed.
 *)

(** * Operations over memory stores *)

(** The initial store *)

Program Definition empty (stack_max:Z): mem :=
  mkmem (ZMap.init Undef)
        (fun ofs k => if ofs <=? stack_max then Some Writable else None)
        (PMap.init nil)
        (stack_max + 1) (stack_max) _ _ _ _.
Next Obligation.
  destruct (ofs <=? stack_max);constructor.
Qed.
Next Obligation. omega. Qed.
Next Obligation. rewrite PMap.gi. auto. Qed.
  
(** Allocation of a fresh block with the given bounds.  Return an updated
  memory state and the capability of the fresh region, which initially contains
  undefined cells.  Note that allocation never fails: we model an
  infinite memory. *)

Program Definition alloc (m: mem) (c: compartment) (len: nat) : occap * mem :=
  let cap := OCsealable (OCVmem RWX Global (Ptrofs.repr m.(mem_next))
                                (Ptrofs.repr (m.(mem_next) + Z.of_nat len))
                                (Ptrofs.repr (m.(mem_next) + Z.of_nat len))) in
  (cap, mkmem (m.(mem_contents))
         (fun ofs k => if (m.(mem_min) <=? ofs) && (ofs <? m.(mem_next)) then Some Freeable else m.(mem_access) ofs k)
         (PMap.set c (cap :: PMap.get c m.(mem_compartments)) m.(mem_compartments))
         (m.(mem_next) + Z.of_nat len)
         (m.(mem_min))
         _ _ _ _
  ).
Next Obligation.
  destruct ((mem_min m <=? ofs) && (ofs <? mem_next m));simpl.
  apply perm_refl. apply access_max.
Qed.
Next Obligation.
  apply contents_default.
Qed.
Next Obligation.
  pose proof mem_min_next m.
  omega.
Qed.
Next Obligation.
  destruct (eq_compartment c c0);subst.
  - rewrite PMap.gss. apply Forall_cons;auto.
    eapply mem_compartments_global;eauto.
  - rewrite PMap.gso;auto.
    eapply mem_compartments_global;eauto.
Qed.

(** Freeing a block between the given bounds.
  Return the updated memory state where the given range of the given block
  has been invalidated: future reads and writes to this
  range will fail.  Requires freeable permission on the given range. *)

Program Definition unchecked_free (m: mem) (lo hi: Z): mem :=
  mkmem m.(mem_contents)
        (fun ofs k => if zle lo ofs && zlt ofs hi then None else m.(mem_access) ofs k)
        m.(mem_compartments)
        m.(mem_next)
        m.(mem_min) _ _ _ _.
Next Obligation.
  destruct (zle lo ofs && zlt ofs hi). red; auto. apply access_max.
Qed.
Next Obligation.
  apply contents_default.
Qed.
Next Obligation.
  apply mem_min_next.
Qed.
Next Obligation.
  eapply mem_compartments_global;eauto.
Qed.

Definition is_pointer (v: ocval) : bool :=
  match v with
  | OCVptr _ | OCVcap _ => true
  | _ => false
  end.

Definition free (m: mem) (c: occap) (cp: compartment): mem + error_kind :=
  let lo := Ptrofs.unsigned (get_lo c) in
  let hi := Ptrofs.unsigned (get_hi c) in
  if range_perm_dec m lo hi Cur Freeable &&
     can_access_block_dec m c (Some cp) &&
     is_mem_cap_b c (* no freeing of sealed regions, or from a sealkey capability *)
  then inl (unchecked_free m lo hi)
  else inr CapErr.

(* RB: NOTE: Add compartments to each item in the list? *)
Fixpoint free_list (m: mem) (l: list (occap)) (cp: compartment) {struct l}: mem + error_kind :=
  match l with
  | nil => inl m
  | c :: l' =>
      match free m c cp with
      | inr err => inr err
      | inl m' => free_list m' l' cp
      end
  end.

(** Memory reads. *)

(** Reading N adjacent bytes in a block content. *)

Fixpoint getN (n: nat) (p: Z) (c: ZMap.t memval) {struct n}: list memval :=
  match n with
  | 0%nat => nil
  | S n' => ZMap.get p c :: getN n' (p + 1) c
  end.

(** [load chunk m b ofs cp] performs a read in memory state [m], at address
  [b] and offset [ofs], from compartment [cp].  It returns the value of the
  memory chunk at that address.  [None] is returned if the accessed bytes
  are not readable. *)

Definition load (a: act_kind) (chunk: cap_memory_chunk) (m: mem) (ptr: occap) (ofs: Z) (cp: option compartment)
  : ocval + error_kind :=
  if valid_access_cap_dec a chunk ptr ofs None None
  then if valid_access_ptr_dec a m chunk ptr ofs Readable cp
    then inl(decode_val chunk (getN (size_chunk_nat chunk) (derive_offset a ptr ofs) (m.(mem_contents))))
    else inr PtrErr
  else inr CapErr.

(** [loadv chunk m addr cp] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition loadv (a: act_kind) (chunk: cap_memory_chunk) (m: mem) (c: occap) (addr: ocval) (cp: option compartment) : ocval + error_kind :=
  match addr with
  | OCVptr (heap_ptr ofs) => load a chunk m c (Ptrofs.unsigned ofs) cp
  | OCVptr (stack_ptr ofs) => load a chunk m c (Ptrofs.unsigned ofs) cp
  | _ => inr PtrErr
  end.

(** [loadbytes m b ofs n cp] reads [n] consecutive bytes starting at
  location [(b, ofs)].  Returns [None] if the accessed locations are
  not readable. *)

Definition loadbytes (a: act_kind) (m: mem) (ptr: occap) (ofs: Z) (n: Z) (cp: option compartment)
  : (list memval) + error_kind :=
  if dynamic_conditions_cap_dec a ptr ofs n None None
  then if
      range_perm_dec m (derive_offset a ptr ofs) ((derive_offset a ptr ofs) + n) Cur Readable &&
      dynamic_conditions_ptr_dec m ptr cp
    then inl (getN (Z.to_nat n) (derive_offset a ptr ofs) (m.(mem_contents)))
    else inr PtrErr
  else inr CapErr.

(** Memory stores. *)

(** Writing N adjacent bytes in a block content. *)

Fixpoint setN (vl: list memval) (p: Z) (c: ZMap.t memval) {struct vl}: ZMap.t memval :=
  match vl with
  | nil => c
  | v :: vl' => setN vl' (p + 1) (ZMap.set p v c)
  end.

Remark setN_other:
  forall vl c p q,
  (forall r, p <= r < p + Z.of_nat (length vl) -> r <> q) ->
  ZMap.get q (setN vl p c) = ZMap.get q c.
Proof.
  induction vl; intros; simpl.
  auto.
  simpl length in H. rewrite Nat2Z.inj_succ in H.
  transitivity (ZMap.get q (ZMap.set p a c)).
  apply IHvl. intros. apply H. omega.
  apply ZMap.gso. apply not_eq_sym. apply H. omega.
Qed.

Remark setN_outside:
  forall vl c p q,
  q < p \/ q >= p + Z.of_nat (length vl) ->
  ZMap.get q (setN vl p c) = ZMap.get q c.
Proof.
  intros. apply setN_other.
  intros. omega.
Qed.

Remark getN_setN_same:
  forall vl p c,
  getN (length vl) p (setN vl p c) = vl.
Proof.
  induction vl; intros; simpl.
  auto.
  decEq.
  rewrite setN_outside. apply ZMap.gss. omega.
  apply IHvl.
Qed.

Remark getN_exten:
  forall c1 c2 n p,
  (forall i, p <= i < p + Z.of_nat n -> ZMap.get i c1 = ZMap.get i c2) ->
  getN n p c1 = getN n p c2.
Proof.
  induction n; intros. auto. rewrite Nat2Z.inj_succ in H. simpl. decEq.
  apply H. omega. apply IHn. intros. apply H. omega.
Qed.

Remark getN_setN_disjoint:
  forall vl q c n p,
  Intv.disjoint (p, p + Z.of_nat n) (q, q + Z.of_nat (length vl)) ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply getN_exten. intros. apply setN_other.
  intros; red; intros; subst r. eelim H; eauto.
Qed.

Remark getN_setN_outside:
  forall vl q c n p,
  p + Z.of_nat n <= q \/ q + Z.of_nat (length vl) <= p ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply getN_setN_disjoint. apply Intv.disjoint_range. auto.
Qed.

Remark setN_default:
  forall vl q c, fst (setN vl q c) = fst c.
Proof.
  induction vl; simpl; intros. auto. rewrite IHvl. auto.
Qed.

(** [store chunk m b ofs v cp] performs a write in memory state [m].
  Value [v] is stored at address [b] and offset [ofs]
  on behalf of component [cp].
  Return the updated memory store, or [None] if the accessed bytes
  are not writable. *)

Program Definition store (a: act_kind) (chunk: cap_memory_chunk) (m: mem) (ptr: occap) (ofs: Z) (v: ocval) (cp: compartment): (occap * mem) + error_kind :=
  let c' := storeU_increase_derive (Some v) ptr ofs (size_chunk_nat chunk) in
  if valid_access_cap_dec a chunk ptr ofs (Some v) (Some c')
  then if valid_access_ptr_dec a m chunk ptr ofs Writable (Some cp)
       then inl (c', mkmem (setN (encode_val chunk v) (derive_offset a ptr ofs) (m.(mem_contents)))
                m.(mem_access)
                m.(mem_compartments)
                m.(mem_next)         
                m.(mem_min)
                _ _ _ _)
       else
         inr PtrErr
  else inr CapErr.
Next Obligation. apply access_max. Qed.
Next Obligation.
  rewrite setN_default. apply contents_default.
Qed.
Next Obligation.
  apply mem_min_next.
Qed.
Next Obligation.
  eapply mem_compartments_global;eauto.
Qed.

(** [storev chunk m addr v cp] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition storev (a: act_kind) (chunk: cap_memory_chunk) (m: mem) (c: occap) (addr v: ocval) (cp: compartment) : (occap * mem) + error_kind :=
  match addr with
  | OCVptr (heap_ptr ofs) => store a chunk m c (Ptrofs.unsigned ofs) v cp
  | OCVptr (stack_ptr ofs) => store a chunk m c (Ptrofs.unsigned ofs) v cp
  | _ => inr PtrErr
  end.

(** [storebytes m b ofs bytes cp] has component [cp] store the given list of
  bytes [bytes] starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)

Program Definition storebytes (a: act_kind) (m: mem) (ptr: occap) (ofs: Z) (bytes: list memval) (chunk: cap_memory_chunk) (cp: compartment)
  : (occap * mem) + error_kind :=
  let v := decode_val chunk bytes in
  let c' := storeU_increase_derive (Some v) ptr ofs (length bytes) in
  if dynamic_conditions_cap_dec a ptr ofs (Z.of_nat (length bytes)) (Some v) (Some c')
  then if
      (range_perm_dec m (derive_offset a ptr ofs) ((derive_offset a ptr ofs) + Z.of_nat (length bytes)) Cur Writable) &&
      (dynamic_conditions_ptr_dec m ptr (Some cp)) &&
      (size_chunk_nat chunk =? length bytes)%nat
    then
      inl (c', mkmem
             (setN bytes (derive_offset a ptr ofs) (m.(mem_contents)))
             m.(mem_access)
             m.(mem_compartments)
             m.(mem_next)         
             m.(mem_min)
             _ _ _ _)
    else inr PtrErr
  else inr CapErr.
Next Obligation. apply access_max. Qed.
Next Obligation.
  rewrite setN_default. apply contents_default.
Qed.
Next Obligation. apply mem_min_next. Qed.
Next Obligation.
  eapply mem_compartments_global;eauto.
Qed.

(** [drop_perm m b lo hi p cp] sets the max permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p] performed from compartment [cp].  These
    bytes must have current permissions [Freeable] in the initial memory state
    [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

(* RB: NOTE: Ownership permissions added by nested conditionals to work around
   funny [Program Definition] misbehavior in the second [Obligation]. *)
Program Definition drop_perm (m: mem) (ptr: occap) (p: permission) (cp: compartment) : mem + error_kind :=
  let lo := (Ptrofs.unsigned (get_lo ptr)) in
  let hi := (Ptrofs.unsigned (get_hi ptr)) in
  if range_perm_dec m lo hi Cur Freeable then
    if can_access_block_dec m ptr (Some cp) then
      inl (mkmem m.(mem_contents)
                    (fun ofs k => if zle lo ofs && zlt ofs hi then Some p else m.(mem_access) ofs k)
                    m.(mem_compartments)
                    m.(mem_next) (m.(mem_min)) _ _ _ _)
    else inr PtrErr
  else inr PtrErr.
Next Obligation.
  destruct (zle (Ptrofs.unsigned (get_lo ptr)) ofs &&
              zlt ofs (Ptrofs.unsigned (get_hi ptr))). red; auto with mem. apply access_max.
Qed.
Next Obligation.
  apply contents_default.
Qed.
Next Obligation. apply mem_min_next. Qed.
Next Obligation.
  eapply mem_compartments_global;eauto.
Qed.

(** * Properties of the memory operations *)

(** ** Properties related to [load] *)

Theorem valid_access_load:
  forall m chunk ptr ofs cp k,
  valid_access k m chunk ptr ofs Readable cp None None ->
  exists v, load k chunk m ptr ofs cp = inl v.
Proof.
  intros until k. intros [V1 V2].
  econstructor. unfold load. rewrite !pred_dec_true; eauto.
Qed.

Theorem load_valid_access:
  forall m chunk ptr ofs cp v k,
  load k chunk m ptr ofs cp = inl v ->
  valid_access k m chunk ptr ofs Readable cp None None.
Proof.
  intros until k. unfold load.
  destruct (valid_access_cap_dec k chunk ptr ofs None None);
  destruct (valid_access_ptr_dec k m chunk ptr ofs Readable cp);intros.
  split;auto.
  all: congruence.
Qed.

Lemma load_result:
  forall k chunk m ptr ofs cp v,
  load k chunk m ptr ofs cp = inl v ->
  v = decode_val chunk (getN (size_chunk_nat chunk) (derive_offset k ptr ofs) (m.(mem_contents))).
Proof.
  intros until v. unfold load.
  destruct (valid_access_cap_dec k chunk ptr ofs None None);
  destruct (valid_access_ptr_dec k m chunk ptr ofs Readable cp); intros;congruence.
Qed.

Lemma load_Some_None:
  forall k chunk m ptr ofs cp v,
    Mem.load k chunk m ptr ofs cp = inl v ->
    Mem.load k chunk m ptr ofs None = inl v.
Proof.
    intros. destruct cp as [cp |]; [|auto].
    unfold load in *.
    destruct (valid_access_cap_dec k chunk ptr ofs None None);try discriminate.
    destruct (valid_access_ptr_dec k m chunk ptr ofs Readable (Some cp));try discriminate.
    inv H.
    destruct (valid_access_ptr_dec k m chunk ptr ofs Readable None).
    reflexivity. destruct v1 as [? [? ?]]. destruct v0 as [? ?].
    unfold valid_access_ptr in n.
    repeat apply Classical_Prop.not_and_or in n as [? | n]; try contradiction.
    unfold can_access_block in H4. easy.
Qed.

Local Hint Resolve load_valid_access valid_access_load: mem.

Theorem load_type:
  forall m chunk ptr ofs cp v k,
  load k chunk m ptr ofs cp = inl v ->
  Val.has_type v (type_of_chunk chunk).
Proof.
  intros. exploit load_result; eauto; intros. rewrite H0.
  apply decode_val_type.
Qed.

Theorem load_rettype:
  forall m chunk ptr ofs cp v k,
  load k chunk m ptr ofs cp = inl v ->
  Val.has_rettype v (rettype_of_chunk chunk).
Proof.
  intros. exploit load_result; eauto; intros. rewrite H0.
  apply decode_val_rettype.
Qed.

Theorem load_cast:
  forall m chunk ptr ofs cp v k,
  load k chunk m ptr ofs cp = inl v ->
  match chunk with
  | CMint8signed => v = Val.sign_ext 8 v
  | CMint8unsigned => v = Val.zero_ext 8 v
  | CMint16signed => v = Val.sign_ext 16 v
  | CMint16unsigned => v = Val.zero_ext 16 v
  | _ => True
  end.
Proof.
  intros. exploit load_result; eauto.
  set (l := getN (size_chunk_nat chunk) ofs m.(mem_contents)).
  intros. subst v. apply decode_val_cast.
Qed.

Theorem load_int8_signed_unsigned:
  forall m ptr ofs cp k,
  load k CMint8signed m ptr ofs cp = sum_left_map (Val.sign_ext 8) (load k CMint8unsigned m ptr ofs cp).
Proof.
  intros. unfold load.
  change (size_chunk_nat CMint8signed) with (size_chunk_nat CMint8unsigned).
  set (cl := getN (size_chunk_nat CMint8unsigned) (derive_offset k ptr ofs) m.(mem_contents)).
  destruct (valid_access_cap_dec k CMint8signed ptr ofs None None).
  destruct (valid_access_ptr_dec k m CMint8signed ptr ofs Readable cp).
  rewrite !pred_dec_true; auto. unfold decode_val.
  destruct (proj_bytes cl); auto.
  simpl. decEq. rewrite Int.sign_ext_zero_ext. auto. compute; auto.
  rewrite pred_dec_true;auto. rewrite pred_dec_false; auto.
  rewrite pred_dec_false;auto.
Qed.

Theorem load_int16_signed_unsigned:
  forall m ptr ofs cp k,
  load k CMint16signed m ptr ofs cp = sum_left_map (Val.sign_ext 16) (load k CMint16unsigned m ptr ofs cp).
Proof.
  intros. unfold load.
  change (size_chunk_nat CMint16signed) with (size_chunk_nat CMint16unsigned).
  set (cl := getN (size_chunk_nat CMint16unsigned) (derive_offset k ptr ofs) m.(mem_contents)).
  destruct (valid_access_cap_dec k CMint16signed ptr ofs None None).
  destruct (valid_access_ptr_dec k m CMint16signed ptr ofs Readable cp).
  rewrite !pred_dec_true; auto. unfold decode_val.
  destruct (proj_bytes cl); auto.
  simpl. decEq. decEq. rewrite Int.sign_ext_zero_ext. auto. compute; auto.
  rewrite pred_dec_true; auto; rewrite pred_dec_false; auto.
  rewrite pred_dec_false;auto.
Qed.

(** ** Properties related to [loadbytes] *)

Theorem range_perm_loadbytes:
  forall k m ptr ofs len cp,
    range_perm m (derive_offset k ptr ofs) (derive_offset k ptr ofs + len) Cur Readable ->
    dynamic_conditions m k ptr ofs len None cp None ->
    exists bytes, loadbytes k m ptr ofs len cp = inl bytes.
Proof.
  intros until cp. intros R [D1 D2]. econstructor. unfold loadbytes. rewrite andb_lazy_alt.
  setoid_rewrite pred_dec_true; eauto.
  setoid_rewrite pred_dec_true; eauto.
  setoid_rewrite pred_dec_true; eauto.
Qed.

Theorem loadbytes_range_perm:
  forall k m ptr ofs len cp bytes,
    loadbytes k m ptr ofs len cp = inl bytes ->
    range_perm m (derive_offset k ptr ofs) (derive_offset k ptr ofs + len) Cur Readable.
Proof.
  intros until bytes. unfold loadbytes.
  destruct (dynamic_conditions_cap_dec k ptr ofs len None None);[|easy].
  destruct (range_perm_dec m (derive_offset k ptr ofs)
                           (derive_offset k ptr ofs + len) Cur Readable);[|easy].
  destruct (dynamic_conditions_ptr_dec m ptr cp) eqn:H;[|easy].
  simpl. auto.
Qed.

Theorem loadbytes_load:
  forall k chunk m ptr ofs cp bytes,
    loadbytes k m ptr ofs (size_chunk chunk) cp = inl bytes ->
    (align_chunk chunk | derive_offset k ptr ofs) ->
    load k chunk m ptr ofs cp = inl (decode_val chunk bytes).
Proof.
  unfold loadbytes, load; intros.
  destruct (dynamic_conditions_cap_dec k ptr ofs (size_chunk chunk) None None).
  destruct (range_perm_dec m (derive_offset k ptr ofs)
          (derive_offset k ptr ofs + size_chunk chunk) Cur Readable).
  destruct (dynamic_conditions_ptr_dec m ptr cp).
  all:simpl in H. inv H.
  rewrite !pred_dec_true;auto. split;auto.
  all: easy.
Qed.

Theorem load_loadbytes:
  forall k chunk m ptr cp v ofs,
    load k chunk m ptr ofs cp = inl v ->
    exists bytes, loadbytes k m ptr ofs (size_chunk chunk) cp = inl bytes
             /\ v = decode_val chunk bytes.
Proof.
  intros. exploit load_valid_access; eauto. intros [A [B [C D]]].
  exploit load_result; eauto. intros.
  exists (getN (size_chunk_nat chunk) (derive_offset k ptr ofs) m.(mem_contents)); split.
  unfold loadbytes. rewrite andb_lazy_alt.
  setoid_rewrite pred_dec_true; auto.
  setoid_rewrite pred_dec_true; auto.
  setoid_rewrite pred_dec_true; auto.
  auto.
Qed.

Lemma getN_length:
  forall c n p, length (getN n p c) = n.
Proof.
  induction n; simpl; intros. auto. decEq; auto.
Qed.

Theorem loadbytes_length:
  forall k m ptr ofs n cp bytes,
  loadbytes k m ptr ofs n cp = inl bytes ->
  length bytes = Z.to_nat n.
Proof.
  unfold loadbytes; intros.
  destruct (dynamic_conditions_cap_dec k ptr ofs n None None);
    destruct (range_perm_dec m (derive_offset k ptr ofs)
                             (derive_offset k ptr ofs + n) Cur Readable);
    destruct (dynamic_conditions_ptr_dec m ptr cp);simpl in H;
    inv H;
    try congruence.
  apply getN_length.
Qed.

(* RB: NOTE: Had to add an [can_access_block] hypothesis here because that check is
   part of the overall access check; Some nil and None may be somewhat similar,
   but the difference seems significant. One could adjust the definition of
   [loadbytes], but it is too early to measure the consequences of such a
   change, which seems less principled, against the proofs that will need to
   resort to this result. *)
(* AG: In a capability machine model, this actually fits the machine
   semantics better, since the dynamic checks happens prior to any memory
   action *)
Theorem loadbytes_empty:
  forall m k ptr ofs len cp,
  len <= 0 ->
  dynamic_conditions m k ptr ofs len None cp None ->
  loadbytes k m ptr ofs len cp = inl nil.
Proof.
  intros. unfold loadbytes.
  destruct H0 as [? ?].
  rewrite andb_lazy_alt.
  setoid_rewrite pred_dec_true;auto.
  setoid_rewrite pred_dec_true;auto.
  setoid_rewrite pred_dec_true;auto.
  - rewrite Z_to_nat_neg; auto.
  - red;intros. omegaContradiction.
Qed.

Lemma getN_concat:
  forall c n1 n2 p,
  getN (n1 + n2)%nat p c = getN n1 p c ++ getN n2 (p + Z.of_nat n1) c.
Proof.
  induction n1; intros.
  simpl. decEq. omega.
  rewrite Nat2Z.inj_succ. simpl. decEq.
  replace (p + Z.succ (Z.of_nat n1)) with ((p + 1) + Z.of_nat n1) by omega.
  auto.
Qed.

(** Composing or decomposing [loadbytes] operations at adjacent addresses. *)
Definition incr_pointer (a: act_kind) (ptr: occap) (ofs: Z) (n: Z) : option (occap * Z) :=
  match a with
  | DIR => option_map (fun c => (c,ofs)) (incr_addr_stk ptr n)
  | UNINIT => Some (ptr,ofs + n)
  | DEFAULT => Some (ptr,ofs + n)
  end.

Lemma incr_pointer_derive_offset:
  forall k ptr1 ofs1 n1 ptr2 ofs2,
    n1 >= 0 ->
    derive_offset k ptr1 ofs1 + n1 < Ptrofs.modulus ->
    incr_pointer k ptr1 ofs1 n1 = Some (ptr2, ofs2) ->
    derive_offset k ptr1 ofs1 + n1 = derive_offset k ptr2 ofs2.
Proof.
  intros until ofs2. intros L M P.
  assert (Ptrofs.unsigned (get_addr ptr1) >= 0) as L'.
  { pose proof (Ptrofs.unsigned_range (get_addr ptr1)). omega. }
  destruct k, ptr1, o;simpl in *;inv P.
  all: simpl; try omega.
  rewrite !Ptrofs.unsigned_repr_eq.
  rewrite !Zmod_small;auto. split;omega.
Qed.

Theorem loadbytes_concat:
  forall k m ptr1 ofs1 ptr2 ofs2 n1 n2 cp bytes1 bytes2,
    incr_pointer k ptr1 ofs1 n1 = Some (ptr2,ofs2) ->
    loadbytes k m ptr1 ofs1 n1 cp = inl bytes1 ->
    loadbytes k m ptr2 ofs2 n2 cp = inl bytes2 ->
    n1 >= 0 -> n2 >= 0 -> derive_offset k ptr1 ofs1 + n1 < Ptrofs.modulus ->
    loadbytes k m ptr1 ofs1 (n1 + n2) cp = inl(bytes1 ++ bytes2).
Proof.
  unfold loadbytes; intros.
  destruct (dynamic_conditions_cap_dec k ptr1 ofs1 n1 None None);[|congruence].
  destruct (range_perm_dec m (derive_offset k ptr1 ofs1)
           (derive_offset k ptr1 ofs1 + n1) Cur Readable);[|simpl in *;congruence].
  destruct (dynamic_conditions_ptr_dec m ptr1 cp);[|simpl in *;congruence].
  simpl in *.
  destruct (dynamic_conditions_cap_dec k ptr2 ofs2 n2 None None);[|congruence].
  destruct (range_perm_dec m (derive_offset k ptr2 ofs2)
           (derive_offset k ptr2 ofs2 + n2) Cur Readable);[|simpl in *;congruence].
  destruct (dynamic_conditions_ptr_dec m ptr2 cp);[|simpl in *; congruence].
  simpl in *.
  inv H0; inv H1.
  setoid_rewrite pred_dec_true. setoid_rewrite pred_dec_true. rewrite Z2Nat.inj_add by omega.
  rewrite getN_concat. rewrite Z2Nat.id by omega.
  simpl in *. erewrite incr_pointer_derive_offset;eauto.
  red; intros.
  assert (ofs < derive_offset k ptr1 ofs1 + n1 \/ ofs >= derive_offset k ptr1 ofs1 + n1) as [?|?] by omega.
  apply r;omega. apply r0. erewrite incr_pointer_derive_offset in H1;eauto.
  inv H0. split;try omega. rewrite Z.add_assoc in H6.
  erewrite <- incr_pointer_derive_offset;eauto.
Admitted.

Theorem loadbytes_split:
  forall k m ptr ofs n1 n2 cp bytes,
  loadbytes k m ptr ofs (n1 + n2) cp = inl bytes ->
  n1 >= 0 -> n2 >= 0 -> derive_offset k ptr ofs + n1 < Ptrofs.modulus ->
  exists bytes1, exists bytes2, exists ptr2, exists ofs2,
    incr_pointer k ptr ofs n1 = Some (ptr2, ofs2)
    /\ loadbytes k m ptr ofs n1 cp = inl bytes1
    /\ loadbytes k m ptr2 ofs2 n2 cp = inl bytes2
    /\ bytes = bytes1 ++ bytes2.
Proof. Admitted.
(*   unfold loadbytes; intros. *)
(*   destruct (can_access_block_dec m b cp); *)
(*     [| rewrite andb_comm in *; simpl in *; congruence]. *)
(*   destruct (range_perm_dec m b ofs (ofs + (n1 + n2)) Cur Readable); *)
(*   try (simpl in *; congruence). *)
(*   rewrite Z2Nat.inj_add in H by omega. rewrite getN_concat in H. *)
(*   rewrite Z2Nat.id in H by omega. *)
(*   repeat setoid_rewrite pred_dec_true. *)
(*   econstructor; econstructor. *)
(*   split. reflexivity. split. reflexivity. simpl in *. congruence. *)
(*   red; intros; apply r; omega. *)
(*   red; intros; apply r; omega. *)
(* Qed. *)

Theorem load_rep:
 forall a chunk m1 m2 ptr ofs cp1 cp2 v1 v2,
   (forall z, 0 <= z < size_chunk chunk -> ZMap.get (derive_offset a ptr ofs + z) m1.(mem_contents) =
                                    ZMap.get (derive_offset a ptr ofs + z) m2.(mem_contents)) ->
  load a chunk m1 ptr ofs cp1 = inl v1 ->
  load a chunk m2 ptr ofs cp2 = inl v2 ->
  v1 = v2.
Proof.
  intros.
  apply load_result in H0.
  apply load_result in H1.
  subst.
  f_equal.
  rewrite size_chunk_conv in H.
  remember (size_chunk_nat chunk) as n; clear Heqn.
  remember (derive_offset a ptr ofs) as m; clear Heqm.
  revert m H; induction n; intros; simpl; auto.
  f_equal.
  rewrite Nat2Z.inj_succ in H.
  replace m with (m +0) by omega.
  apply H; omega.
  apply IHn.
  intros.
  rewrite <- Z.add_assoc.
  apply H.
  rewrite Nat2Z.inj_succ. omega.
Qed.

(*Theorem load_int64_split:
  forall m b ofs cp v,
  load Mint64 m b ofs cp = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     load Mint32 m b ofs cp = Some (if Archi.big_endian then v1 else v2)
  /\ load Mint32 m b (ofs + 4) cp = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2).
Proof.
  intros.
  exploit load_valid_access; eauto. intros [A [B C]]. simpl in *.
  exploit load_loadbytes. eexact H. simpl. intros [bytes [LB EQ]].
  change 8 with (4 + 4) in LB.
  exploit loadbytes_split. eexact LB. omega. omega.
  intros (bytes1 & bytes2 & LB1 & LB2 & APP).
  change 4 with (size_chunk Mint32) in LB1.
  exploit loadbytes_load. eexact LB1.
  simpl. apply Z.divide_trans with 8; auto. exists 2; auto.
  intros L1.
  change 4 with (size_chunk Mint32) in LB2.
  exploit loadbytes_load. eexact LB2.
  simpl. apply Z.divide_add_r. apply Z.divide_trans with 8; auto. exists 2; auto. exists 1; auto.
  intros L2.
  exists (decode_val Mint32 (if Archi.big_endian then bytes1 else bytes2));
  exists (decode_val Mint32 (if Archi.big_endian then bytes2 else bytes1)).
  split. destruct Archi.big_endian; auto.
  split. destruct Archi.big_endian; auto.
  rewrite EQ. rewrite APP. apply decode_val_int64; auto.
  erewrite loadbytes_length; eauto. reflexivity.
  erewrite loadbytes_length; eauto. reflexivity.
Qed.

Lemma addressing_int64_split:
  forall i,
  Archi.ptr64 = false ->
  (8 | Ptrofs.unsigned i) ->
  Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.repr 4))) = Ptrofs.unsigned i + 4.
Proof.
  intros.
  rewrite Ptrofs.add_unsigned.
  replace (Ptrofs.unsigned (Ptrofs.of_int (Int.repr 4))) with (Int.unsigned (Int.repr 4))
    by (symmetry; apply Ptrofs.agree32_of_int; auto).
  change (Int.unsigned (Int.repr 4)) with 4.
  apply Ptrofs.unsigned_repr.
  exploit (Zdivide_interval (Ptrofs.unsigned i) Ptrofs.modulus 8).
  omega. apply Ptrofs.unsigned_range. auto.
  exists (two_p (Ptrofs.zwordsize - 3)).
  unfold Ptrofs.modulus, Ptrofs.zwordsize, Ptrofs.wordsize.
  unfold Wordsize_Ptrofs.wordsize. destruct Archi.ptr64; reflexivity.
  unfold Ptrofs.max_unsigned. omega.
Qed.

Theorem loadv_int64_split:
  forall m a cp v,
  loadv Mint64 m a cp = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     loadv Mint32 m a cp = Some (if Archi.big_endian then v1 else v2)
  /\ loadv Mint32 m (Val.add a (Vint (Int.repr 4))) cp = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2).
Proof.
  intros. destruct a; simpl in H; inv H.
  exploit load_int64_split; eauto. intros (v1 & v2 & L1 & L2 & EQ).
  unfold Val.add; rewrite H0.
  assert (NV: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.repr 4))) = Ptrofs.unsigned i + 4).
  { apply addressing_int64_split; auto.
    exploit load_valid_access. eexact H2. intros [P [Q R]]. auto. }
  exists v1, v2.
Opaque Ptrofs.repr.
  split. auto.
  split. simpl. rewrite NV. auto.
  auto.
Qed.*)

(** ** Properties related to [store] *)

Lemma valid_access_cap_inj:
  forall a m chunk ptr ofs p cp v ptr1 ptr2,
    valid_access a m chunk ptr ofs p cp (Some v) (Some ptr1) ->
    valid_access a m chunk ptr ofs p cp (Some v) (Some ptr2) ->
    ptr1 = ptr2.
Proof.
  intros until ptr2. intros [[_ V1] _] [[_ V2] _].
  apply storeU_increase_authority_eq in V1.
  apply storeU_increase_authority_eq in V2. inv V1; inv V2.
  auto.
Qed.

Theorem valid_access_store:
  forall m1 chunk ptr ofs cp v k ptr',
  valid_access k m1 chunk ptr ofs Writable (Some cp) (Some v) (Some ptr') ->
  { m2: mem | store k chunk m1 ptr ofs v cp = inl (ptr',m2) }.
Proof.
  intros.
  unfold store.
  destruct (valid_access_cap_dec k chunk ptr ofs (Some v)
           (Some (storeU_increase_derive (Some v) ptr ofs (size_chunk_nat chunk)))).
  destruct (valid_access_ptr_dec k m1 chunk ptr ofs Writable (Some cp)).
  apply valid_access_cap_inj with (ptr1:=(storeU_increase_derive (Some v)
                                         ptr ofs (size_chunk_nat chunk))) in H as Heq.
  subst ptr'. eauto. split;auto.
  destruct H as [H1 H2].
  contradiction.
  destruct H as [[V1 V2] V3].
  apply storeU_increase_authority_eq in V2 as Heq. inv Heq.
  assert (valid_access_cap k chunk ptr ofs (Some v)
         (Some (storeU_increase_derive (Some v) ptr ofs (size_chunk_nat chunk)))).
  split;auto.
  contradiction.
Defined.

Local Hint Resolve valid_access_store: mem.

Section STORE.
Variable k: act_kind.
Variable chunk: cap_memory_chunk.
Variable m1: mem.
Variable ptr: occap.
Variable ofs: Z.
Variable v: ocval.
Variable cp : compartment.
Variable m2: mem.
Variable ptr': occap.
Hypothesis STORE: store k chunk m1 ptr ofs v cp = inl (ptr',m2).

Lemma store_access: mem_access m2 = mem_access m1.
Proof.
  unfold store in STORE. destruct (valid_access_cap_dec k chunk ptr ofs (Some v)
              (Some
                 (storeU_increase_derive (Some v) ptr ofs
                                         (size_chunk_nat chunk))));
  destruct (valid_access_ptr_dec k m1 chunk ptr ofs Writable (Some cp)); inv STORE.
  auto.
Qed.

Lemma store_mem_contents:
  mem_contents m2 = (setN (encode_val chunk v) (derive_offset k ptr ofs) m1.(mem_contents)).
Proof.
  unfold store in STORE.
  destruct (valid_access_cap_dec k chunk ptr ofs (Some v)
              (Some
                 (storeU_increase_derive (Some v) ptr ofs
                                         (size_chunk_nat chunk))));
    destruct (valid_access_ptr_dec k m1 chunk ptr ofs Writable (Some cp)); inv STORE.
  auto.
Qed.

Theorem perm_store_1:
  forall ofs' k p, perm m1 ofs' k p -> perm m2 ofs' k p.
Proof.
  intros.
 unfold perm in *. rewrite store_access; auto.
Qed.

Theorem perm_store_2:
  forall ofs' k p, perm m2 ofs' k p -> perm m1 ofs' k p.
Proof.
  intros. unfold perm in *.  rewrite store_access in H; auto.
Qed.

Local Hint Resolve perm_store_1 perm_store_2: mem.

Theorem store_valid_access_1:
  forall chunk' p ofs perm cp' v' p',
  valid_access k m1 chunk' p ofs perm cp' v' p' -> valid_access k m2 chunk' p ofs perm cp' v' p'.
Proof.
  intros. inv H. destruct H1 as [H1 [H2 H3]]. constructor; try red; auto with mem. split.
  - unfold store in STORE.
    destruct (valid_access_cap_dec k chunk ptr ofs (Some v)
              (Some
                 (storeU_increase_derive (Some v) ptr ofs
                                         (size_chunk_nat chunk))));
    destruct (valid_access_ptr_dec k m1 chunk ptr ofs Writable (Some cp)); inv STORE.
    auto.
  - unfold store in STORE.
    destruct (valid_access_cap_dec k chunk ptr ofs (Some v)
              (Some
                 (storeU_increase_derive (Some v) ptr ofs
                                         (size_chunk_nat chunk))));
      destruct (valid_access_ptr_dec k m1 chunk ptr ofs Writable (Some cp)); inv STORE.
    split; auto.
Qed.

Theorem store_valid_access_2:
  forall chunk' p p' ofs perm cp' v',
  valid_access k m2 chunk' p ofs perm cp' v' p' -> valid_access k m1 chunk' p ofs perm cp' v' p'.
Proof.
  intros. inv H. destruct H1 as [H1 H2]. constructor; try red; auto with mem. split.
  - unfold store in STORE.
    destruct (valid_access_cap_dec k chunk ptr ofs (Some v)
              (Some
                 (storeU_increase_derive (Some v) ptr ofs
                                         (size_chunk_nat chunk))));
    destruct (valid_access_ptr_dec k m1 chunk ptr ofs Writable (Some cp)); inv STORE.
    auto.
  - unfold store in STORE.
    destruct (valid_access_cap_dec k chunk ptr ofs (Some v)
              (Some
                 (storeU_increase_derive (Some v) ptr ofs
                                         (size_chunk_nat chunk))));
    destruct (valid_access_ptr_dec k m1 chunk ptr ofs Writable (Some cp)); inv STORE.
    auto.
Qed.

Theorem store_valid_access_3:
  valid_access k m1 chunk ptr ofs Writable (Some cp) (Some v) (Some ptr').
Proof.
  unfold store in STORE.
  destruct (valid_access_cap_dec k chunk ptr ofs (Some v)
              (Some
                 (storeU_increase_derive (Some v) ptr ofs
                                         (size_chunk_nat chunk))));
    destruct (valid_access_ptr_dec k m1 chunk ptr ofs Writable (Some cp)); inv STORE.
  split;auto.
Qed.

Theorem store_valid_access_4:
  valid_access k m1 chunk ptr ofs Writable None (Some v) (Some ptr').
Proof.
  unfold store in STORE.
  destruct (valid_access_cap_dec k chunk ptr ofs (Some v)
              (Some
                 (storeU_increase_derive (Some v) ptr ofs
                                         (size_chunk_nat chunk))));
    destruct (valid_access_ptr_dec k m1 chunk ptr ofs Writable (Some cp)); inv STORE.
  split;auto. destruct v1. split;auto. now simpl.
Qed.

Local Hint Resolve store_valid_access_1 store_valid_access_2
      store_valid_access_3 store_valid_access_4: mem.

Theorem store_block_compartment:
  forall b',
  block_compartment m2 b' = block_compartment m1 b'.
Proof.
  unfold store in STORE.
  destruct valid_access_cap_dec; try easy.
  destruct valid_access_ptr_dec; try easy.
  injection STORE.
  now intros <- b'.
Qed.

Lemma valid_access_store_load:
  forall k m chunk c ofs p cp v c',
    (isUCap c = true ->
     offset_lt_cap (derive_offset k c ofs + Z.of_nat (size_chunk_nat chunk)) c) ->
    valid_access k m chunk c ofs p cp (Some v) (Some c') ->
    valid_access k m chunk c ofs p cp None None.
Proof.
  intros until c'. intros C [[V1 V2] V3].
  split;auto. split;[|simpl; auto].
  unfold dynamic_access in V1.
  eapply can_store_implies_can_load;eauto.
Qed.
  
Theorem load_store_similar:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v', load k chunk' m2 ptr ofs (Some cp) = inl v' /\ decode_encode_val v chunk chunk' v'.
Proof.
Admitted.
(*   intros. *)
(*   unfold store in STORE. *)
(*   destruct valid_access_cap_dec; try easy. *)
(*   destruct valid_access_ptr_dec; try easy. *)
(*   exploit (valid_access_load m2 chunk'). *)
(*   eapply valid_access_compat. symmetry; eauto. auto. *)
(*     instantiate (1 := Some cp). split; eauto with mem. *)
(*   intros [v' LOAD]. *)
(*   exists v'; split; auto. *)
(*   exploit load_result; eauto. intros B. *)
(*   rewrite B. rewrite store_mem_contents; simpl. *)
(*   rewrite PMap.gss. *)
(*   replace (size_chunk_nat chunk') with (length (encode_val chunk v)). *)
(*   rewrite getN_setN_same. apply decode_encode_val_general. *)
(*   rewrite encode_val_length. repeat rewrite size_chunk_conv in H. *)
(*   apply Nat2Z.inj; auto. *)
(* Qed. *)

(* Theorem load_store_similar_2: *)
(*   forall chunk', *)
(*   size_chunk chunk' = size_chunk chunk -> *)
(*   align_chunk chunk' <= align_chunk chunk -> *)
(*   type_of_chunk chunk' = type_of_chunk chunk -> *)
(*   load chunk' m2 b ofs (Some cp) = Some (Val.load_result chunk' v). *)
(* Proof. *)
(*   intros. destruct (load_store_similar chunk') as [v' [A B]]; auto. *)
(*   rewrite A. decEq. eapply decode_encode_val_similar with (chunk1 := chunk); eauto. *)
(* Qed. *)

(*Theorem load_store_same:
  load chunk m2 b ofs (Some cp) = Some (Val.load_result chunk v).
Proof.
  apply load_store_similar_2; auto. omega.
Qed.

Theorem load_store_other:
  forall chunk' b' ofs' cp',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' cp' = load chunk' m1 b' ofs' cp'.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m1 chunk' b' ofs' Readable cp').
  rewrite pred_dec_true.
  decEq. decEq. rewrite store_mem_contents; simpl.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  apply getN_setN_outside. rewrite encode_val_length. repeat rewrite <- size_chunk_conv.
  intuition.
  auto.
  eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.*)

(* ALG: TODO: fix formulation to change ofs in case the capability did change and relative offset needs to change *)
Theorem loadbytes_store_same:
  loadbytes k m2 ptr' ofs (size_chunk chunk) (Some cp) = inl(encode_val chunk v).
Proof.
  intros.
(*   assert (valid_access m2 chunk b ofs Readable (Some cp)) by eauto with mem. *)
(*   destruct (can_access_block_dec m2 b (Some cp)); *)
(*     [ | inversion H as [_ [Hcontra _]]; contradiction]. *)
(*   unfold loadbytes. *)
(*   rewrite andb_lazy_alt. setoid_rewrite pred_dec_true. setoid_rewrite pred_dec_true. *)
(*   rewrite store_mem_contents; simpl. *)
(*   rewrite PMap.gss. *)
(*   replace (Z.to_nat (size_chunk chunk)) with (length (encode_val chunk v)). *)
(*   rewrite getN_setN_same. auto. *)
(*   rewrite encode_val_length. auto. *)
(*   auto. *)
(*   apply H. *)
  (* Qed. *)
Admitted.

(*
Theorem loadbytes_store_same_priv:
  loadbytes m2 b ofs (size_chunk chunk) None = Some(encode_val chunk v).
Proof.
  intros.
  assert (valid_access m2 chunk b ofs Readable None) by (eauto with mem).
  destruct (can_access_block_dec m2 b None);
    [ | inversion H as [_ [Hcontra _]]; contradiction].
  unfold loadbytes.
  rewrite andb_lazy_alt. setoid_rewrite pred_dec_true. setoid_rewrite pred_dec_true.
  rewrite store_mem_contents; simpl.
  rewrite PMap.gss.
  replace (Z.to_nat (size_chunk chunk)) with (length (encode_val chunk v)).
  rewrite getN_setN_same. auto.
  rewrite encode_val_length. auto.
  auto.
  apply H.
Qed.*)

(* RB: NOTE: Split in _1 and _2 directions? *)
Remark store_range_perm_inj :
  forall ofs' n,
  range_perm m1 ofs' (ofs' + n) Cur Readable <->
  range_perm m2 ofs' (ofs' + n) Cur Readable.
Proof.
  split; intros;
    destruct (range_perm_dec m1 ofs' (ofs' + n) Cur Readable);
    destruct (range_perm_dec m2 ofs' (ofs' + n) Cur Readable);
    try contradiction; try assumption;
    (unfold store in STORE;
     destruct (valid_access_cap_dec k chunk ptr ofs (Some v)
              (Some
                 (storeU_increase_derive (Some v) ptr ofs
                                         (size_chunk_nat chunk))));
     destruct (valid_access_ptr_dec k m1 chunk ptr ofs Writable (Some cp));
     inv STORE; now auto).
Qed.

Remark store_can_access_block_1 :
  can_access_block m1 ptr (Some cp).
Proof.
  unfold store in STORE.
  destruct (valid_access_cap_dec k chunk ptr ofs (Some v)
              (Some
                 (storeU_increase_derive (Some v) ptr ofs
                                         (size_chunk_nat chunk))));try easy.
  destruct (valid_access_ptr_dec k m1 chunk ptr ofs Writable (Some cp));try easy.
  destruct v1 as [? [? ?]]. auto.
Qed.

Remark store_can_access_block_2 :
  can_access_block m2 ptr (Some cp).
Proof.
  unfold store in STORE.
  destruct (valid_access_cap_dec k chunk ptr ofs (Some v)
              (Some
                 (storeU_increase_derive (Some v) ptr ofs
                                         (size_chunk_nat chunk))));try easy.
  destruct (valid_access_ptr_dec k m1 chunk ptr ofs Writable (Some cp));try easy.
  destruct v1 as [? [? ?]]. inv STORE.
  auto.
Qed.

Remark store_can_access_block_inj :
  forall b' cp',
  can_access_block m1 b' cp' <-> can_access_block m2 b' cp'.
Proof.
  split; intros;
    destruct (can_access_block_dec m1 b' cp');
    destruct (can_access_block_dec m2 b' cp');
    try contradiction; try assumption;
    (unfold store in STORE;
     destruct (valid_access_cap_dec k chunk ptr ofs (Some v)
              (Some
                 (storeU_increase_derive (Some v) ptr ofs
                                         (size_chunk_nat chunk))));
     destruct (valid_access_ptr_dec k m1 chunk ptr ofs Writable (Some cp));
     inv STORE; now auto).
Qed.


Theorem loadbytes_store_other:
  forall k p' ofs' ofs n cp',
    n <= 0 \/ ofs' + n <= ofs \/ ofs + size_chunk chunk <= ofs' ->
    loadbytes k m2 p' n cp' = loadbytes k m1 p' n cp'.
Proof.
  intros. unfold loadbytes. Admitted. (*
  destruct (range_perm_dec m1 b' ofs' (ofs' + n) Cur Readable).
- rewrite andb_lazy_alt. setoid_rewrite pred_dec_true at 1.
+ destruct (can_access_block_dec m1 b' cp').
* setoid_rewrite pred_dec_true. simpl.
  decEq. rewrite store_mem_contents; simpl.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  destruct H. congruence.
  destruct (zle n 0) as [z | n0].
  rewrite (Z_to_nat_neg _ z). auto.
  destruct H. omegaContradiction.
  apply getN_setN_outside. rewrite encode_val_length. rewrite <- size_chunk_conv.
  rewrite Z2Nat.id. auto. omega.
  auto.
  apply store_can_access_block_inj; auto.
* setoid_rewrite pred_dec_false; auto.
  intro Hcontra. apply store_can_access_block_inj in Hcontra. contradiction.
+ red; intros. eauto with mem.
- setoid_rewrite pred_dec_false at 1.
+ auto.
+ red; intro; elim n0; red; intros; eauto with mem.
Qed.*)

Lemma setN_in:
  forall vl p q c,
  p <= q < p + Z.of_nat (length vl) ->
  In (ZMap.get q (setN vl p c)) vl.
Proof.
  induction vl; intros.
  simpl in H. omegaContradiction.
  simpl length in H. rewrite Nat2Z.inj_succ in H. simpl.
  destruct (zeq p q). subst q. rewrite setN_outside. rewrite ZMap.gss.
  auto with coqlib. omega.
  right. apply IHvl. omega.
Qed.

Lemma getN_in:
  forall c q n p,
  p <= q < p + Z.of_nat n ->
  In (ZMap.get q c) (getN n p c).
Proof.
  induction n; intros.
  simpl in H; omegaContradiction.
  rewrite Nat2Z.inj_succ in H. simpl. destruct (zeq p q).
  subst q. auto.
  right. apply IHn. omega.
Qed.

End STORE.

Local Hint Resolve perm_store_1 perm_store_2: mem.
(* Local Hint Resolve store_valid_block_1 store_valid_block_2: mem. *)
Local Hint Resolve store_valid_access_1 store_valid_access_2
             store_valid_access_3: mem.

(* RB: NOTE: [cp] and [cp'] must be equal, but the result does not rely on
   this fact, and similarly for other related theorems. *)
(*
Lemma load_store_overlap:
  forall chunk m1 b ofs v cp m2 chunk' ofs' cp' v',
  store chunk m1 b ofs v cp = Some m2 ->
  load chunk' m2 b ofs' cp' = Some v' ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  exists mv1 mvl mv1' mvl',
      shape_encoding chunk v (mv1 :: mvl)
  /\  shape_decoding chunk' (mv1' :: mvl') v'
  /\  (   (ofs' = ofs /\ mv1' = mv1)
       \/ (ofs' > ofs /\ In mv1' mvl)
       \/ (ofs' < ofs /\ In mv1 mvl')).
Proof.
  intros.
  exploit load_result; eauto. erewrite store_mem_contents by eauto; simpl.
  rewrite PMap.gss.
  set (c := (mem_contents m1)#b). intros V'.
  destruct (size_chunk_nat_pos chunk) as [sz SIZE].
  destruct (size_chunk_nat_pos chunk') as [sz' SIZE'].
  destruct (encode_val chunk v) as [ | mv1 mvl] eqn:ENC.
  generalize (encode_val_length chunk v); rewrite ENC; simpl; congruence.
  set (c' := setN (mv1::mvl) ofs c) in *.
  exists mv1, mvl, (ZMap.get ofs' c'), (getN sz' (ofs' + 1) c').
  split. rewrite <- ENC. apply encode_val_shape.
  split. rewrite V', SIZE'. apply decode_val_shape.
  destruct (zeq ofs' ofs).
- subst ofs'. left; split. auto. unfold c'. simpl.
  rewrite setN_outside by omega. apply ZMap.gss.
- right. destruct (zlt ofs ofs').
(* If ofs < ofs':  the load reads (at ofs') a continuation byte from the write.
       ofs   ofs'   ofs+|chunk|
        [-------------------]       write
             [-------------------]  read
*)
+ left; split. omega. unfold c'. simpl. apply setN_in.
  assert (Z.of_nat (length (mv1 :: mvl)) = size_chunk chunk).
  { rewrite <- ENC; rewrite encode_val_length. rewrite size_chunk_conv; auto. }
  simpl length in H3. rewrite Nat2Z.inj_succ in H3. omega.
(* If ofs > ofs':  the load reads (at ofs) the first byte from the write.
       ofs'   ofs   ofs'+|chunk'|
               [-------------------]  write
         [----------------]           read
*)
+ right; split. omega. replace mv1 with (ZMap.get ofs c').
  apply getN_in.
  assert (size_chunk chunk' = Z.succ (Z.of_nat sz')).
  { rewrite size_chunk_conv. rewrite SIZE'. rewrite Nat2Z.inj_succ; auto. }
  omega.
  unfold c'. simpl. rewrite setN_outside by omega. apply ZMap.gss.
Qed.*)

Definition compat_pointer_chunks (chunk1 chunk2: cap_memory_chunk) (storev: ocval) : Prop :=
  match chunk1, chunk2, storev with
  | (CMint32 | CMany32), (CMint32 | CMany32), OCVptr _ => True
  | (CMint64 | CMany64), (CMint64 | CMany64), OCVptr _ => True
  | (CMcap64 | CMany64), (CMcap64 | CMany64), OCVcap _ => True
  | (CMcap128 | CMany128), (CMcap128 | CMany128), OCVcap _ => True
  | _, _, _ => False
  end.

(* Lemma compat_pointer_chunks_true: *)
(*   forall chunk1 chunk2, *)
(*   (chunk1 = Mint32 \/ chunk1 = Many32 \/ chunk1 = Mint64 \/ chunk1 = Many64) -> *)
(*   (chunk2 = Mint32 \/ chunk2 = Many32 \/ chunk2 = Mint64 \/ chunk2 = Many64) -> *)
(*   quantity_chunk chunk1 = quantity_chunk chunk2 -> *)
(*   compat_pointer_chunks chunk1 chunk2. *)
(* Proof. *)
(*   intros. destruct H as [P|[P|[P|P]]]; destruct H0 as [Q|[Q|[Q|Q]]]; *)
(*   subst; red; auto; discriminate. *)
(* Qed. *)

Theorem load_pointer_store:
  forall k chunk m1 ptr ofs v cp m2 chunk' ptr' ofs' cp' v' ptr2,
  is_pointer v = true ->
  store k chunk m1 ptr ofs v cp = inl (ptr2,m2) ->
  load k chunk' m2 ptr' ofs' cp' = inl v' ->
  (v = v' /\ compat_pointer_chunks chunk chunk' v /\ ofs = ofs')
  \/ (ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').
Proof.
  Admitted.
(*   intros. *)
(*   destruct (peq b' b); auto. subst b'. *)
(*   destruct (zle (ofs' + size_chunk chunk') ofs); auto. *)
(*   destruct (zle (ofs + size_chunk chunk) ofs'); auto. *)
(*   exploit load_store_overlap; eauto. *)
(*   intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES). *)
(*   inv DEC; try contradiction. *)
(*   destruct CASES as [(A & B) | [(A & B) | (A & B)]]. *)
(* - (* Same offset *) *)
(*   subst. inv ENC. *)
(*   assert (chunk = Mint32 \/ chunk = Many32 \/ chunk = Mint64 \/ chunk = Many64) *)
(*   by (destruct chunk; auto || contradiction). *)
(*   left; split. rewrite H3. *)
(*   destruct H4 as [P|[P|[P|P]]]; subst chunk'; destruct v0; simpl in H3; *)
(*   try congruence; destruct Archi.ptr64; congruence. *)
(*   split. apply compat_pointer_chunks_true; auto. *)
(*   auto. *)
(* - (* ofs' > ofs *) *)
(*   inv ENC. *)
(*   + exploit H10; eauto. intros (j & P & Q). inv P. congruence. *)
(*   + exploit H8; eauto. intros (n & P); congruence. *)
(*   + exploit H2; eauto. congruence. *)
(* - (* ofs' < ofs *) *)
(*   exploit H7; eauto. intros (j & P & Q). subst mv1. inv ENC. congruence. *)
(* Qed. *)

Theorem load_store_pointer_overlap:
  forall k chunk m1 ofs v1 v2 storev cp m2 chunk' ofs' cp' v ptr2,
  is_pointer storev = true ->
  store k chunk m1 v1 ofs storev cp = inl (ptr2,m2) ->
  load k chunk' m2 v2 ofs' cp' = inl v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = OCVundef.
Proof. Admitted.
(*   intros. *)
(*   exploit load_store_overlap; eauto. *)
(*   intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES). *)
(*   destruct CASES as [(A & B) | [(A & B) | (A & B)]]. *)
(* - congruence. *)
(* - inv ENC. *)
(*   + exploit H9; eauto. intros (j & P & Q). subst mv1'. inv DEC. congruence. auto. *)
(*   + contradiction. *)
(*   + exploit H5; eauto. intros; subst. inv DEC; auto. *)
(* - inv DEC. *)
(*   + exploit H10; eauto. intros (j & P & Q). subst mv1. inv ENC. congruence. *)
(*   + exploit H8; eauto. intros (n & P). subst mv1. inv ENC. contradiction. *)
(*   + auto. *)
(* Qed. *)

Theorem load_store_pointer_mismatch:
  forall k chunk m1 ptr storev cp m2 chunk' cp' v ptr' ofs ofs',
  is_pointer storev = true ->
  store k chunk m1 ptr ofs storev cp = inl (ptr',m2) ->
  load k chunk' m2 ptr' ofs' cp' = inl v ->
  ~compat_pointer_chunks chunk chunk' storev ->
  v = OCVundef.
Proof. Admitted.
(*   intros. *)
(*   exploit load_store_overlap; eauto. *)
(*   generalize (size_chunk_pos chunk'); omega. *)
(*   generalize (size_chunk_pos chunk); omega. *)
(*   intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES). *)
(*   destruct CASES as [(A & B) | [(A & B) | (A & B)]]; try omegaContradiction. *)
(*   inv ENC; inv DEC; auto. *)
(* - elim H1. apply compat_pointer_chunks_true; auto. *)
(* - contradiction. *)
(* Qed. *)

Lemma store_similar_chunks:
  forall k chunk1 chunk2 v1 m ptr ofs cp,
  encode_val chunk1 v1 = encode_val chunk2 v1 ->
  align_chunk chunk1 = align_chunk chunk2 ->
  store k chunk1 m ptr ofs v1 cp = store k chunk2 m ptr ofs v1 cp.
Proof.
  intros. unfold store.
  assert (size_chunk chunk1 = size_chunk chunk2).
    repeat rewrite size_chunk_conv.
    rewrite <- (encode_val_length chunk1 v1).
    rewrite <- (encode_val_length chunk2 v1).
    congruence.
  unfold store.
  destruct (valid_access_cap_dec k chunk1 ptr ofs (Some v1)
            (Some (storeU_increase_derive (Some v1) ptr ofs (size_chunk_nat chunk1)))).
  assert (valid_access_cap k chunk2 ptr ofs (Some v1)
            (Some (storeU_increase_derive (Some v1) ptr ofs (size_chunk_nat chunk2)))).
  { unfold valid_access_cap. erewrite size_chunk_nat_eq;eauto. }
  destruct (valid_access_ptr_dec k m chunk1 ptr ofs Writable (Some cp)).
  assert (valid_access_ptr k m chunk2 ptr ofs Writable (Some cp)).
  { destruct v0 as [? [? ?]]. unfold valid_access_ptr.
    rewrite <- H1; rewrite <- H0. auto. }
  { rewrite !pred_dec_true.
    f_equal. f_equal. erewrite size_chunk_nat_eq;eauto.
    apply mkmem_ext;auto. rewrite H. auto. auto. auto. }
  rewrite pred_dec_true;auto.
  rewrite pred_dec_false;auto.
  2: rewrite pred_dec_false;auto.
  - unfold valid_access_ptr. rewrite <- H1. rewrite <- H0. auto.
  - unfold valid_access_cap. erewrite size_chunk_nat_eq;eauto.
Qed.

Lemma store_similar_chunks_2:
  forall k chunk1 v1 v2 m ptr ofs cp,
  encode_val chunk1 (OCVint v1) = encode_val chunk1 (OCVint v2) ->
  store k chunk1 m ptr ofs (OCVint v1) cp = store k chunk1 m ptr ofs (OCVint v2) cp.
Proof.
  intros. unfold store.
  destruct (valid_access_cap_dec k chunk1 ptr ofs (Some (OCVint v1))
      (Some (storeU_increase_derive (Some (OCVint v1)) ptr ofs (size_chunk_nat chunk1)))).
  assert (valid_access_cap k chunk1 ptr ofs (Some (OCVint v2))
      (Some (storeU_increase_derive (Some (OCVint v2)) ptr ofs (size_chunk_nat chunk1)))).
  { unfold valid_access_cap. auto. }
  destruct (valid_access_ptr_dec k m chunk1 ptr ofs Writable (Some cp)).
  { rewrite !pred_dec_true.
    f_equal. f_equal. apply mkmem_ext;auto. rewrite H. auto. auto. }
  rewrite pred_dec_true;auto.
  rewrite pred_dec_false;auto.
Qed.

Theorem store_signed_unsigned_8:
  forall k m ptr ofs v cp,
  store k CMint8signed m ptr ofs v cp = store k CMint8unsigned m ptr ofs v cp.
Proof. intros. apply store_similar_chunks. apply encode_val_int8_signed_unsigned. auto. Qed.

Theorem store_signed_unsigned_16:
  forall k m ptr ofs v cp,
  store k CMint16signed m ptr ofs v cp = store k CMint16unsigned m ptr ofs v cp.
Proof. intros. apply store_similar_chunks. apply encode_val_int16_signed_unsigned. auto. Qed.

Theorem store_int8_zero_ext:
  forall k m ptr ofs n cp,
  store k CMint8unsigned m ptr ofs (OCVint (Int.zero_ext 8 n)) cp =
  store k CMint8unsigned m ptr ofs (OCVint n) cp.
Proof. intros. apply store_similar_chunks_2. apply encode_val_int8_zero_ext. Qed.

Theorem store_int8_sign_ext:
  forall k m ptr ofs n cp,
  store k CMint8signed m ptr ofs (OCVint (Int.sign_ext 8 n)) cp =
  store k CMint8signed m ptr ofs (OCVint n) cp.
Proof. intros. apply store_similar_chunks_2. apply encode_val_int8_sign_ext. Qed.

Theorem store_int16_zero_ext:
  forall k m ptr ofs n cp,
  store k CMint16unsigned m ptr ofs (OCVint (Int.zero_ext 16 n)) cp =
  store k CMint16unsigned m ptr ofs (OCVint n) cp.
Proof. intros. apply store_similar_chunks_2. apply encode_val_int16_zero_ext. Qed.

Theorem store_int16_sign_ext:
  forall k m ptr ofs n cp,
  store k CMint16signed m ptr ofs (OCVint (Int.sign_ext 16 n)) cp =
  store k CMint16signed m ptr ofs (OCVint n) cp.
Proof. intros. apply store_similar_chunks_2. apply encode_val_int16_sign_ext. Qed.

(*
Theorem store_float64al32:
  forall m b ofs v m',
  store Mfloat64 m b ofs v = Some m' -> store Mfloat64al32 m b ofs v = Some m'.
Proof.
  unfold store; intros.
  destruct (valid_access_dec m Mfloat64 b ofs Writable); try discriminate.
  destruct (valid_access_dec m Mfloat64al32 b ofs Writable).
  rewrite <- H. f_equal. apply mkmem_ext; auto.
  elim n. apply valid_access_compat with Mfloat64; auto. simpl; omega.
Qed.

Theorem storev_float64al32:
  forall m a v m',
  storev Mfloat64 m a v = Some m' -> storev Mfloat64al32 m a v = Some m'.
Proof.
  unfold storev; intros. destruct a; auto. apply store_float64al32; auto.
Qed.
*)

(** ** Properties related to [storebytes]. *)

(* RB: NOTE: Like [loadbytes], [storebytes] builds in the ownership check and
   some results are best complemented by ownership hypotheses, at least at this
   stage. *)
Theorem range_perm_storebytes:
  forall k m1 ptr ofs bytes cp ptr' chunk,
    range_perm m1 (derive_offset k ptr ofs) ((derive_offset k ptr ofs) + Z.of_nat (length bytes)) Cur Writable ->
    length bytes = size_chunk_nat chunk ->
    dynamic_conditions m1 k ptr ofs (size_chunk chunk) (Some (decode_val chunk bytes)) (Some cp) (Some ptr') ->
    { m2 : mem | storebytes k m1 ptr ofs bytes chunk cp = inl (ptr',m2) }.
Proof.
  intros. 
  assert (ptr' = (storeU_increase_derive (Some (decode_val chunk bytes)) ptr ofs (size_chunk_nat chunk))).
  { destruct H1 as [? [? ?]].
    apply storeU_increase_authority_eq in H3. inv H3. auto. }
  subst ptr'.
  unfold storebytes.
  econstructor. setoid_rewrite pred_dec_true;auto.
  setoid_rewrite pred_dec_true;auto. simpl.
  destruct (size_chunk_nat chunk =? Datatypes.length bytes)%nat eqn:n.
  rewrite H0;eauto.
  apply Nat.eqb_neq in n. congruence.
  all:destruct H1 as [? ?];auto.
  rewrite H0, <- size_chunk_conv;auto.
Defined.
  
Theorem storebytes_store:
  forall k m1 ptr chunk v cp ptr2 m2 ofs,
  storebytes k m1 ptr ofs (encode_val chunk v) chunk cp = inl (ptr2,m2) ->
  (align_chunk chunk | derive_offset k ptr ofs) ->
  store k chunk m1 ptr ofs v cp = inl (ptr2,m2).
Proof.
  unfold storebytes, store. intros.
  destruct (dynamic_conditions_cap_dec k ptr ofs
          (Z.of_nat (Datatypes.length (encode_val chunk v)))
          (Some (decode_val chunk (encode_val chunk v)))
          (Some (storeU_increase_derive
                (Some (decode_val chunk (encode_val chunk v))) ptr ofs
                (Datatypes.length (encode_val chunk v)))));[|inv H].
  destruct (range_perm_dec m1 (derive_offset k ptr ofs)
           (derive_offset k ptr ofs + Z.of_nat (Datatypes.length (encode_val chunk v))) Cur Writable);[|inv H].
  destruct (dynamic_conditions_ptr_dec m1 ptr (Some cp));[|inv H].
  destruct (size_chunk_nat chunk =? Datatypes.length (encode_val chunk v))%nat;[|inv H].
  simpl in H. inv H.
  rewrite !pred_dec_true.
  f_equal. f_equal. all:admit.
  (* ALG: need decode_val chunk (encode_val chunk v) = v to prove this theorem. *)
Admitted.

  (* rewrite encode_val_length in r. rewrite size_chunk_conv. auto. *)
(* Qed. *)

Theorem store_storebytes:
  forall k m1 ptr ofs chunk v cp ptr2 m2,
  store k chunk m1 ptr ofs v cp = inl (ptr2,m2) ->
  storebytes k m1 ptr ofs (encode_val chunk v) chunk cp = inl (ptr2,m2).
Proof.
  unfold storebytes, store. intros.
  destruct (valid_access_cap_dec k chunk ptr ofs (Some v)
          (Some (storeU_increase_derive (Some v) ptr ofs (size_chunk_nat chunk))));[|inv H].
  destruct (valid_access_ptr_dec k m1 chunk ptr ofs Writable (Some cp));inv H.
  rewrite pred_dec_true.
  destruct (range_perm_dec).
  destruct dynamic_conditions_ptr_dec.
  destruct (size_chunk_nat chunk =? Datatypes.length (encode_val chunk v))%nat.
  simpl. all:admit.
  (* ALG: need decode_val chunk (encode_val chunk v) = v to prove this theorem. *)
Admitted.

Lemma storebytes_ptr_same:
  forall k m1 ptr ofs bytes chunk cp m2,
    storebytes k m1 ptr ofs bytes chunk cp = inl (ptr,m2) ->
    isUCap ptr = true ->
    offset_lt_cap (derive_offset k ptr ofs + Z.of_nat (size_chunk_nat chunk)) ptr.
Proof.
Admitted.            

Theorem loadbytes_storebytes_same:
  forall k m1 ptr ofs bytes chunk cp m2, storebytes k m1 ptr ofs bytes chunk cp = inl (ptr,m2) ->
  loadbytes k m2 ptr ofs (Z.of_nat (length bytes)) (Some cp) = inl bytes.
Proof.
  intros until m2. intros STORE2.
  unfold storebytes in STORE2. unfold loadbytes.
  destruct dynamic_conditions_cap_dec;[|inv STORE2];
    destruct range_perm_dec;[|inv STORE2];
    destruct dynamic_conditions_ptr_dec;[|inv STORE2];
    destruct (size_chunk_nat chunk =? Datatypes.length bytes)%nat eqn:neq;inv STORE2.
  rewrite pred_dec_true.
  destruct range_perm_dec,dynamic_conditions_ptr_dec;simpl.
  decEq. rewrite Nat2Z.id. apply getN_setN_same.
  1,2:exfalso; apply n; red; eauto with mem.
  all: admit.
Admitted.

Section STOREBYTES.
Variable k: act_kind.
Variable m1: mem.
Variable ptr: occap.
Variable ofs: Z.
Variable bytes: list memval.
Variable chunk: cap_memory_chunk.
Variable cp: compartment.
Variable ptr': occap.
Variable m2: mem.

Hypothesis STORE: storebytes k m1 ptr ofs bytes chunk cp = inl (ptr',m2).

Lemma storebytes_can_access_block_1 : can_access_block m1 ptr (Some cp).
Proof.
  unfold storebytes in STORE.
  destruct dynamic_conditions_cap_dec;[|inv STORE].
  destruct range_perm_dec;[|inv STORE].
  destruct dynamic_conditions_ptr_dec;[|inv STORE].
  destruct (size_chunk_nat chunk =? Datatypes.length bytes)%nat;inv STORE.
  auto.
Qed.

Lemma storebytes_can_access_block_2 : can_access_block m2 ptr (Some cp).
Proof.
  unfold storebytes in STORE.
  destruct dynamic_conditions_cap_dec;[|inv STORE].
  destruct range_perm_dec;[|inv STORE].
  destruct dynamic_conditions_ptr_dec;[|inv STORE].
  destruct (size_chunk_nat chunk =? Datatypes.length bytes)%nat;inv STORE.
  auto.
Qed.

(* RB: NOTE: Names and split adapted from storebytes_valid_block_1 and _2 below,
   similar auxiliary results could follow the same pattern (with preservation
   suffix, see lemmas above). *)
Lemma storebytes_can_access_block_inj_1 :
  forall ptr' cp', can_access_block m1 ptr' cp' -> can_access_block m2 ptr' cp'.
Proof.
  unfold can_access_block, storebytes in *;
    intros b' cp' H;
    destruct dynamic_conditions_cap_dec;[|inv STORE];
    destruct range_perm_dec;[|inv STORE];
    destruct dynamic_conditions_ptr_dec;[|inv STORE];
    destruct (size_chunk_nat chunk =? Datatypes.length bytes)%nat;inv STORE.
  destruct cp';auto.
Qed.

Lemma storebytes_can_access_block_inj_2 :
  forall ptr' cp', can_access_block m2 ptr' cp' -> can_access_block m1 ptr' cp'.
Proof.
  unfold can_access_block, storebytes in *;
    destruct dynamic_conditions_cap_dec;[|inv STORE];
    destruct range_perm_dec;[|inv STORE];
    destruct dynamic_conditions_ptr_dec;[|inv STORE];
    destruct (size_chunk_nat chunk =? Datatypes.length bytes)%nat;inv STORE.
  destruct cp';auto.
Qed.

Lemma storebytes_access: mem_access m2 = mem_access m1.
Proof.
  unfold storebytes in STORE.
  destruct dynamic_conditions_cap_dec;[|inv STORE];
    destruct range_perm_dec;[|inv STORE];
    destruct dynamic_conditions_ptr_dec;[|inv STORE];
    destruct (size_chunk_nat chunk =? Datatypes.length bytes)%nat;inv STORE.
  auto.
Qed.

Lemma storebytes_mem_contents:
   mem_contents m2 = (setN bytes (derive_offset k ptr ofs) m1.(mem_contents)).
Proof.
  unfold storebytes in STORE.
  destruct dynamic_conditions_cap_dec;[|inv STORE];
    destruct range_perm_dec;[|inv STORE];
    destruct dynamic_conditions_ptr_dec;[|inv STORE];
    destruct (size_chunk_nat chunk =? Datatypes.length bytes)%nat;inv STORE.
  auto.
Qed.

Theorem perm_storebytes_1:
  forall ofs' k p, perm m1 ofs' k p -> perm m2 ofs' k p.
Proof.
  intros. unfold perm in *. rewrite storebytes_access; auto.
Qed.

Theorem perm_storebytes_2:
  forall ofs' k p, perm m2 ofs' k p -> perm m1 ofs' k p.
Proof.
  intros. unfold perm in *. rewrite storebytes_access in H; auto.
Qed.

Local Hint Resolve perm_storebytes_1 perm_storebytes_2: mem.

Theorem storebytes_valid_access_1:
  forall k' chunk' ptr' ofs' p cp' o ptr'',
  valid_access k' m1 chunk' ptr' ofs' p cp' (Some o) ptr'' -> valid_access k' m2 chunk' ptr' ofs' p cp' (Some o) ptr''.
Proof.
  intros. destruct H as [H1 [H2 [H3 H4]]].
  split;auto. split;try red;auto with mem.
  split;auto.
  apply storebytes_can_access_block_inj_1; eassumption.
Qed.

Theorem storebytes_valid_access_2:
  forall k' chunk' ptr' ofs' p cp' o ptr'',
  valid_access k' m2 chunk' ptr' ofs' p cp' (Some o) ptr'' -> valid_access k' m1 chunk' ptr' ofs' p cp' (Some o) ptr''.
Proof.
  intros. destruct H as [H1 [H2 [H3 H4]]].
  split;auto. split;try red;auto with mem.
  split;auto.
  apply storebytes_can_access_block_inj_2; eassumption.
Qed.

Local Hint Resolve storebytes_valid_access_1 storebytes_valid_access_2: mem.

Theorem storebytes_range_perm:
  range_perm m1 (derive_offset k ptr ofs) ((derive_offset k ptr ofs) + Z.of_nat (length bytes)) Cur Writable.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct dynamic_conditions_cap_dec;[|inv STORE];
    destruct range_perm_dec;[|inv STORE];
    destruct dynamic_conditions_ptr_dec;[|inv STORE];
    destruct (size_chunk_nat chunk =? Datatypes.length bytes)%nat;inv STORE.
  auto.
Qed.

Theorem loadbytes_storebytes_same_None:
  loadbytes k m2 ptr ofs (Z.of_nat (length bytes)) None = inl bytes.
Proof.
(*   intros. assert (STORE2:=STORE). unfold storebytes in STORE2. unfold loadbytes. *)
(*   destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable); *)
(*   destruct (can_access_block_dec m1 b (Some cp)); *)
(*   try discriminate. *)
(*   setoid_rewrite pred_dec_true. simpl. *)
(*   decEq. inv STORE2; simpl. rewrite PMap.gss. rewrite Nat2Z.id. *)
(*   apply getN_setN_same. *)
(*   red; eauto with mem. *)
(*   reflexivity. *)
  (* Qed. *)
Admitted.

Theorem loadbytes_storebytes_disjoint:
  forall k' ptr' ofs' len cp',
  len >= 0 ->
  Intv.disjoint (derive_offset k' ptr' ofs', derive_offset k' ptr' ofs' + len)
                (derive_offset k ptr ofs, derive_offset k ptr ofs + Z.of_nat (length bytes)) ->
  loadbytes k' m2 ptr' ofs' len cp' = loadbytes k' m1 ptr' ofs' len cp'.
Proof.
(*   intros. unfold loadbytes. *)
(*   destruct (range_perm_dec m1 b' ofs' (ofs' + len) Cur Readable); *)
(*   destruct (can_access_block_dec m1 b' cp'). *)
(* - setoid_rewrite pred_dec_true; simpl. *)
(* + rewrite storebytes_mem_contents. decEq. *)
(*   rewrite PMap.gsspec. destruct (peq b' b). subst b'. *)
(*   apply getN_setN_disjoint. rewrite Z2Nat.id by omega. intuition congruence. *)
(*   auto. *)
(* + red; auto with mem. *)
(* + apply storebytes_can_access_block_inj_1; assumption. *)
(* - setoid_rewrite pred_dec_false at 2. *)
(* + do 2 rewrite andb_false_r. reflexivity. *)
(* + intro Hcontra. apply storebytes_can_access_block_inj_2 in Hcontra. contradiction. *)
(* - setoid_rewrite pred_dec_false at 1; simpl. reflexivity. *)
(*   red; intros; elim n. red; auto with mem. *)
(* - setoid_rewrite pred_dec_false at 1; simpl. reflexivity. *)
(*   red; intros; elim n. red; auto with mem. *)
  (* Qed. *)
Admitted.

Theorem loadbytes_storebytes_other:
  forall k' ptr' ofs' len cp',
  len >= 0 ->
  derive_offset k' ptr' ofs' + len <= derive_offset k ptr ofs
  \/ derive_offset k ptr ofs + Z.of_nat (length bytes) <= derive_offset k' ptr' ofs' ->
  loadbytes k' m2 ptr' ofs' len cp' = loadbytes k' m1 ptr' ofs' len cp'.
Proof.
  intros. apply loadbytes_storebytes_disjoint; auto.
  destruct H0; auto; apply Intv.disjoint_range; auto.
Qed.

Theorem load_storebytes_other:
  forall k' chunk ptr' ofs' cp',
  (derive_offset k' ptr' ofs') + size_chunk chunk <= derive_offset k ptr ofs
  \/ derive_offset k ptr ofs + Z.of_nat (length bytes) <= derive_offset k' ptr' ofs' ->
  load k' chunk m2 ptr' ofs' cp' = load k' chunk m1 ptr' ofs' cp'.
Proof.
  (* intros. unfold load. *)
(*   destruct (valid_access_dec m1 chunk b' ofs' Readable cp'). *)
(*   rewrite pred_dec_true. *)
(*   rewrite storebytes_mem_contents. decEq. *)
(*   rewrite PMap.gsspec. destruct (peq b' b). subst b'. *)
(*   rewrite getN_setN_outside. auto. rewrite <- size_chunk_conv. intuition congruence. *)
(*   auto. *)
(*   destruct v; split; auto. red; auto with mem. *)
(*   destruct H1 as [H1 H2]. split. *)
(*   apply storebytes_can_access_block_inj_1; assumption. *)
(*   assumption. *)
(*   apply pred_dec_false. *)
(*   red; intros; elim n. destruct H0. split; auto. red; auto with mem. *)
(*   destruct H1 as [H1 H2]. split. *)
(*   apply storebytes_can_access_block_inj_2; assumption. *)
(*   assumption. *)
  (* Qed. *)
Admitted.

End STOREBYTES.

Lemma setN_concat:
  forall bytes1 bytes2 ofs c,
  setN (bytes1 ++ bytes2) ofs c = setN bytes2 (ofs + Z.of_nat (length bytes1)) (setN bytes1 ofs c).
Proof.
  induction bytes1; intros.
  simpl. decEq. omega.
  simpl length. rewrite Nat2Z.inj_succ. simpl. rewrite IHbytes1. decEq. omega.
Qed.

(* ALG: not obvious how to formulate splitting stores in the cap machine for uninitialized capabilities *)

(* RB: NOTE: Different compartment variables could be used in each premise (and
   the conclusion), as those would effectively be equal. *)
(*Theorem storebytes_concat:
  forall m b ofs bytes1 cp m1 bytes2 m2,
  storebytes m b ofs bytes1 cp = Some m1 ->
  storebytes m1 b (ofs + Z.of_nat(length bytes1)) bytes2 cp = Some m2 ->
  storebytes m b ofs (bytes1 ++ bytes2) cp = Some m2.
Proof.
  intros. generalize H; intro ST1. generalize H0; intro ST2.
  unfold storebytes; unfold storebytes in ST1; unfold storebytes in ST2.
  destruct (range_perm_dec m b ofs (ofs + Z.of_nat(length bytes1)) Cur Writable);
  destruct (can_access_block_dec m b (Some cp));
  simpl in *;
  try congruence.
  destruct (range_perm_dec m1 b (ofs + Z.of_nat(length bytes1)) (ofs + Z.of_nat(length bytes1) + Z.of_nat(length bytes2)) Cur Writable);
    simpl in *; try congruence.
  destruct (can_access_block_dec m1 b (Some cp)) eqn:rewr; simpl in rewr; rewrite rewr in ST2;
  simpl in *;
  try congruence.
  destruct (range_perm_dec m b ofs (ofs + Z.of_nat (length (bytes1 ++ bytes2))) Cur Writable).
  inv ST1; inv ST2; simpl. decEq. apply mkmem_ext; auto.
  rewrite PMap.gss.  rewrite setN_concat. symmetry. apply PMap.set2.
  elim n.
  rewrite app_length. rewrite Nat2Z.inj_add. red; intros.
  destruct (zlt ofs0 (ofs + Z.of_nat(length bytes1))).
  apply r. omega.
  eapply perm_storebytes_2; eauto. apply r0. omega.
Qed.

Theorem storebytes_split:
  forall m b ofs bytes1 bytes2 cp m2,
  storebytes m b ofs (bytes1 ++ bytes2) cp = Some m2 ->
  exists m1,
     storebytes m b ofs bytes1 cp = Some m1
  /\ storebytes m1 b (ofs + Z.of_nat(length bytes1)) bytes2 cp = Some m2.
Proof.
  intros.
  destruct (range_perm_storebytes m b ofs bytes1 cp) as [m1 ST1].
  red; intros. exploit storebytes_range_perm; eauto. rewrite app_length.
  rewrite Nat2Z.inj_add. omega.
  eapply storebytes_can_access_block_1; eassumption.
  destruct (range_perm_storebytes m1 b (ofs + Z.of_nat (length bytes1)) bytes2 cp) as [m2' ST2].
  red; intros. eapply perm_storebytes_1; eauto. exploit storebytes_range_perm.
  eexact H. instantiate (1 := ofs0). rewrite app_length. rewrite Nat2Z.inj_add. omega.
  auto.
  eapply storebytes_can_access_block_2; eassumption.
  assert (Some m2 = Some m2').
  rewrite <- H. eapply storebytes_concat; eauto.
  inv H0.
  exists m1; split; auto.
Qed.

Theorem store_int64_split:
  forall m b ofs v cp m',
  store Mint64 m b ofs v cp = Some m' -> Archi.ptr64 = false ->
  exists m1,
     store Mint32 m b ofs (if Archi.big_endian then Val.hiword v else Val.loword v) cp = Some m1
  /\ store Mint32 m1 b (ofs + 4) (if Archi.big_endian then Val.loword v else Val.hiword v) cp = Some m'.
Proof.
  intros.
  exploit store_valid_access_3; eauto. intros [A [B C]]. simpl in *.
  exploit store_storebytes. eexact H. intros SB.
  rewrite encode_val_int64 in SB by auto.
  exploit storebytes_split. eexact SB. intros [m1 [SB1 SB2]].
  rewrite encode_val_length in SB2. simpl in SB2.
  exists m1; split.
  apply storebytes_store. exact SB1.
  simpl. apply Z.divide_trans with 8; auto. exists 2; auto.
  apply storebytes_store. exact SB2.
  simpl. apply Z.divide_add_r. apply Z.divide_trans with 8; auto. exists 2; auto. exists 1; auto.
Qed.

Theorem storev_int64_split:
  forall m a v cp m',
  storev Mint64 m a v cp = Some m' -> Archi.ptr64 = false ->
  exists m1,
     storev Mint32 m a (if Archi.big_endian then Val.hiword v else Val.loword v) cp = Some m1
  /\ storev Mint32 m1 (Val.add a (Vint (Int.repr 4))) (if Archi.big_endian then Val.loword v else Val.hiword v) cp = Some m'.
Proof.
  intros. destruct a; simpl in H; inv H. rewrite H2.
  exploit store_int64_split; eauto. intros [m1 [A B]].
  exists m1; split.
  exact A.
  unfold storev, Val.add. rewrite H0.
  rewrite addressing_int64_split; auto.
  exploit store_valid_access_3. eexact H2. intros [P [R Q]]. exact Q.
Qed.*)

(** ** Properties related to [alloc]. *)

Section ALLOC.

Variable m1: mem.
Variable c: compartment.
Variables l: nat.
Variable m2: mem.
Variable ptr: occap.
Hypothesis ALLOC: alloc m1 c l = (ptr, m2).

(* ALG: TODO: add invariant to mem that each capability is owned by at most one compartment *)
(* Theorem unowned_fresh_block: *)
(*   forall c', ~can_access_block m1 ptr (Some c'). *)
(* Proof. *)
(*   unfold can_access_block. intros c'. *)
(*   injection ALLOC as _ <-. *)
(*   rewrite block_compartment_nextblock. *)
(*   congruence. *)
(* Qed. *)

Theorem owned_new_block:
  can_access_block m2 ptr (Some c).
Proof.
  unfold can_access_block.
  unfold alloc in ALLOC. destruct m1. inv ALLOC.
  unfold block_compartment. simpl.
  rewrite PMap.gss. apply Exists_cons_hd.
  constructor. omega. omega. reflexivity. reflexivity.
Qed.

Theorem perm_alloc_1:
  forall ofs k p, perm m1 ofs k p -> perm m2 ofs k p.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H0; simpl in *.
  destruct (mem_min m1 <=? ofs).
  destruct (ofs <? mem_next m1).
  simpl. constructor.
  all: simpl; auto.
Qed.

(* ALG: for the following to be true, we need to have partial alloc ->
currently there is mismatch between infinite memory and finite
representation of bounds and address of capabilities *)
Theorem perm_alloc_2:
  forall ofs k, Ptrofs.unsigned (get_lo ptr) <= ofs < Ptrofs.unsigned (get_hi ptr) -> perm m2 ofs k Freeable.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H0; simpl in *.
  rewrite <- H1 in H. simpl in *.
  pose proof (Ptrofs.eqm_unsigned_repr ofs).
Admitted.

Theorem perm_alloc_inv:
  forall ofs k p,
  perm m2 ofs k p ->
  Ptrofs.unsigned (get_lo ptr) <= ofs < Ptrofs.unsigned (get_hi ptr) \/ perm m1 ofs k p.
Proof.
  intros until p; unfold perm. inv ALLOC. simpl.
Admitted.
(*   rewrite PMap.gsspec. unfold eq_block. destruct (peq b' (nextblock m1)); intros. *)
(*   destruct (zle lo ofs); try contradiction. destruct (zlt ofs hi); try contradiction. *)
(*   split; auto. *)
(*   auto. *)
(* Qed. *)

Theorem perm_alloc_3:
  forall ofs k p, perm m2 ofs k p -> Ptrofs.unsigned (get_lo ptr) <= ofs < Ptrofs.unsigned (get_hi ptr).
Proof.
  intros. exploit perm_alloc_inv; eauto.
Admitted.

(* Theorem perm_alloc_4: *)
(*   forall c1 k p, perm m2 c1 k p -> disjoint_cap ptr c1 -> perm m1 c1 k p. *)
(* Proof. *)
(*   intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_false; auto. *)
(* Qed. *)

Local Hint Resolve perm_alloc_1 perm_alloc_2 perm_alloc_3: mem.

Theorem alloc_block_compartment:
    In ptr (block_compartment m2 c).
Proof.
  injection ALLOC as <- <-. unfold block_compartment; simpl.
  rewrite PMap.gss. apply in_eq.
Qed.

(* ALG: can only be proved if we add invariant about unique ownership *)
Lemma alloc_can_access_block_inj :
  forall b' c', can_access_block m1 b' (Some c') -> ptr <> b'.
Proof.
  intros b' c' Hown Heq; subst b'.
  unfold can_access_block in Hown.
Admitted.

Lemma alloc_can_access_block_other_inj_1 :
  forall b' c', can_access_block m1 b' c' -> can_access_block m2 b' c'.
Proof.
  unfold can_access_block. intros b' [c' |] Hown; [| trivial].
  (* injection ALLOC as <- <-. unfold block_compartment. *)
Admitted.

Lemma alloc_can_access_block_other_inj_2 :
  forall b' c', disjoint_cap b' ptr -> can_access_block m2 b' c' -> can_access_block m1 b' c'.
Proof.
  unfold can_access_block. intros b' [c' |] Hneq Hown; [| trivial].
  injection ALLOC as <- <-. unfold block_compartment in Hown. simpl in *.
Admitted.

Theorem valid_access_alloc_other:
  forall k' chunk ptr' ofs' p cp' o ptr'',
  valid_access k' m1 chunk ptr' ofs' p cp' o ptr'' ->
  valid_access k' m2 chunk ptr' ofs' p cp' o ptr''.
Proof.
  intros. inv H. destruct H1 as [H1 [H2 H3]]. constructor; auto with mem.
  red; auto with mem. split. red;auto with mem.
  split;auto.
  apply alloc_can_access_block_other_inj_1; assumption.
Qed.

Theorem valid_access_alloc_same:
  forall k chunk ofs o ptr'',
      dynamic_conditions m2 k ptr ofs (size_chunk chunk) o (Some c) ptr'' ->
      (align_chunk chunk | derive_offset k ptr ofs) ->
      valid_access k m2 chunk ptr ofs Freeable (Some c) o ptr''.
Proof.
  intros.
  apply dynamic_conditions_in_bounds in H as Hb.
  destruct H as [? [? ?]].
  red;auto with mem.
  split;[|split];auto.
  red;auto with mem.
  red;intros.
  apply perm_alloc_2. unfold in_bounds in Hb.
  destruct ptr,o0;[|easy..]. destruct Hb as [? ?].
  simpl. destruct H3. split; try omega.
  pose proof (size_chunk_pos chunk).
  rewrite Z2Nat.id in H5;[|omega]. omega.
Qed.

Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

Theorem valid_access_alloc_inv:
  forall k chunk ptr' p c' o ptr'' ofs,
      valid_access k m2 chunk ptr' ofs p c' o ptr'' ->
      if derived_cap_dec ptr ptr'
      then in_bounds k ptr' ofs (size_chunk_nat chunk)
           /\ (align_chunk chunk | (derive_offset k ptr' ofs))
           /\ dynamic_conditions m2 k ptr' ofs (size_chunk chunk) o (Some c) ptr''
      else valid_access k m1 chunk ptr' ofs p c' o ptr''.
Proof.
  intros. inv H. destruct H1 as [H1 Hx].
  generalize (size_chunk_pos chunk); intro.
(*   destruct (eq_block b' b). subst b'. *)
(*   assert (perm m2 b ofs Cur p). apply H0. omega. *)
(*   assert (perm m2 b (ofs + size_chunk chunk - 1) Cur p). apply H0. omega. *)
(*   exploit perm_alloc_inv. eexact H2. rewrite dec_eq_true. intro. *)
(*   exploit perm_alloc_inv. eexact H3. rewrite dec_eq_true. intro. *)
(*   intuition omega. *)
(*   split; auto. red; intros. *)
(*   exploit perm_alloc_inv. apply H0. eauto. rewrite dec_eq_false; auto. *)
(*   split. *)
(*   apply alloc_can_access_block_other_inj_2; assumption. *)
(*   assumption. *)
  (* Qed. *)
Admitted.

Lemma disjoint_not_derived:
  forall ptr ptr',
    Ptrofs.unsigned (get_lo ptr) < Ptrofs.unsigned (get_hi ptr) ->
    Ptrofs.unsigned (get_lo ptr') < Ptrofs.unsigned (get_hi ptr') ->
    disjoint_cap ptr ptr' ->
    derived_cap ptr ptr' -> False.
Proof.
  intros until ptr'. intros Hle1 Hle2 D1 D2.
  inv D1;inv D2.
  + simpl in *. omega.
  + inv H0;simpl in *. omega.
  + simpl in *. omega.
  + inv H0;simpl in *. omega.
Qed.

Theorem load_alloc_unchanged:
  forall k chunk ptr' ofs' c' ,
      disjoint_cap ptr ptr' ->
      load k chunk m2 ptr' ofs' c' = load k chunk m1 ptr' ofs' c'.
Proof.
  intros. unfold load.
  destruct valid_access_cap_dec;auto.
  destruct valid_access_ptr_dec;auto.
  - rewrite pred_dec_true;auto.
    injection ALLOC; intros. rewrite <- H0; simpl.
    auto.
    exploit valid_access_alloc_inv;[split;eauto|].
    rewrite pred_dec_false.
    intros [? ?]. auto.
    destruct v as [[Hb _] _].
    unfold in_bounds in Hb.
    intros D.
    eapply disjoint_not_derived;eauto.
    + injection ALLOC as <- <-; simpl in *.
      admit.
    + injection ALLOC as <- <-; simpl in *.
      admit.
  - rewrite pred_dec_false;auto.
    intros v'. apply n.
    unfold valid_access_ptr in *.
    admit.
Admitted.

Theorem load_alloc_other:
  forall k chunk ptr' ofs c' v,
  load k chunk m1 ptr' ofs c' = inl v ->
  load k chunk m2 ptr' ofs c' = inl v.
Proof.
  intros. rewrite <- H. apply load_alloc_unchanged.
Admitted.

Theorem load_alloc_same:
  forall k chunk ofs c' v,
      load k chunk m2 ptr ofs c' = inl v ->
      v = OCVundef.
Proof.
  intros. exploit load_result; eauto. intro. rewrite H0.
  injection ALLOC; intros. rewrite <- H2; simpl. rewrite <- H1.
(*   rewrite PMap.gss. destruct (size_chunk_nat_pos chunk) as [n E]. rewrite E. simpl. *)
(*   rewrite ZMap.gi. apply decode_val_undef. *)
  (* Qed. *)
Admitted.

(* RB: NOTE: In keeping with the style of the lemma, we add the missing
   assumption to it, however it is unclear whether this is the best choice.
   Clearly, c' can only be c, and block ownership can be established from
   known facts. *)
Theorem load_alloc_same':
  forall k ptr' chunk ofs,
      derived_cap ptr ptr' ->
      dynamic_conditions m2 k ptr' ofs (size_chunk chunk) None (Some c) None ->
      (align_chunk chunk | derive_offset k ptr' ofs) ->
      load k chunk m2 ptr' ofs (Some c) = inl OCVundef.
Proof.
  intros. (* assert (exists v, load chunk m2 b ofs (Some c) = Some v). *)
(*     apply valid_access_load. constructor; auto. *)
(*     red; intros. eapply perm_implies. apply perm_alloc_2. omega. auto with mem. *)
(*   destruct H3 as [v LOAD]. rewrite LOAD. decEq. *)
(*   eapply load_alloc_same; eauto. *)
  (* Qed. *)
Admitted.

(*
Theorem loadbytes_alloc_unchanged:
  forall b' ofs n c',
  valid_block m1 b' ->
  loadbytes m2 b' ofs n c' = loadbytes m1 b' ofs n c'.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs (ofs + n) Cur Readable).
- destruct (can_access_block_dec m1 b' c').
+ setoid_rewrite pred_dec_true. simpl.
  injection ALLOC; intros A B. rewrite <- B; simpl.
  rewrite PMap.gso. auto. rewrite A. eauto with mem.
  red; intros. eapply perm_alloc_1; eauto.
  apply alloc_can_access_block_other_inj_1; assumption.
+ setoid_rewrite pred_dec_false at 2.
* rewrite andb_comm. reflexivity.
* intro Hcontra. apply n0.
  apply alloc_can_access_block_other_inj_2; auto.
  apply valid_block_alloc_inv'; assumption.
- setoid_rewrite pred_dec_false at 1; auto.
  red; intros; elim n0. red; intros. eapply perm_alloc_4; eauto. eauto with mem.
Qed.

(* RB: NOTE: Could also use c here. *)
Theorem loadbytes_alloc_same:
  forall n ofs c' bytes byte,
  loadbytes m2 b ofs n c' = Some bytes ->
  In byte bytes -> byte = Undef.
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable);
  destruct (can_access_block_dec m2 b c');
  inv H.
  revert H0.
  injection ALLOC; intros A B. rewrite <- A; rewrite <- B; simpl. rewrite PMap.gss.
  generalize (Z.to_nat n) ofs. induction n0; simpl; intros.
  contradiction.
  rewrite ZMap.gi in H0. destruct H0; eauto.
Qed.*)

End ALLOC.

(* Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem. *)
Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

(** ** Properties related to [free]. *)

Theorem range_perm_free:
  forall m1 ptr cp,
  range_perm m1 (Ptrofs.unsigned (get_lo ptr)) (Ptrofs.unsigned (get_hi ptr)) Cur Freeable ->
  can_access_block m1 ptr (Some cp) ->
  is_mem_cap ptr ->
  { m2: mem | free m1 ptr cp = inl m2 }.
Proof.
  intros; unfold free. econstructor.
  setoid_rewrite pred_dec_true; auto.
  rewrite is_mem_cap_reflect in H1. rewrite H1. simpl. eauto.
Defined.

Section FREE.

Variable m1: mem.
Variable ptr: occap.
Variable cp: compartment.
Variable m2: mem.
Hypothesis FREE: free m1 ptr cp = inl m2.

Theorem free_range_perm:
  range_perm m1 (Ptrofs.unsigned (get_lo ptr)) (Ptrofs.unsigned (get_hi ptr)) Cur Freeable.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 (Ptrofs.unsigned (get_lo ptr))
             (Ptrofs.unsigned (get_hi ptr)) Cur Freeable);[|inv FREE]. 
  destruct (can_access_block_dec m1 ptr (Some cp)); inv FREE.
  auto.
Qed.

Lemma free_result:
  m2 = unchecked_free m1 (Ptrofs.unsigned (get_lo ptr)) (Ptrofs.unsigned (get_hi ptr)).
Proof.
  unfold free in FREE.
  destruct range_perm_dec;[|inv FREE].
  destruct can_access_block_dec;[|inv FREE].
  destruct is_mem_cap_b;inv FREE.
  auto.
Qed.

Theorem perm_free_1:
  forall ofs k p,
  ofs < (Ptrofs.unsigned (get_lo ptr)) \/ (Ptrofs.unsigned (get_hi ptr)) <= ofs ->
  perm m1 ofs k p ->
  perm m2 ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  destruct zle,zlt;simpl.
  elimtype False;intuition.
  all: auto.
Qed.

Theorem perm_free_2:
  forall ofs k p, (Ptrofs.unsigned (get_lo ptr)) <= ofs < (Ptrofs.unsigned (get_hi ptr)) -> ~ perm m2 ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  intros v. destruct zle,zlt;simpl in *;easy.
Qed.

Theorem perm_free_3:
  forall ofs k p,
  perm m2 ofs k p -> perm m1 ofs k p.
Proof.
  intros until p. rewrite free_result. unfold perm, unchecked_free; simpl.
  destruct zle,zlt;simpl. easy.
  all: auto.
Qed.

Theorem perm_free_inv:
  forall ofs k p,
  perm m1 ofs k p ->
  (Ptrofs.unsigned (get_lo ptr) <= ofs < Ptrofs.unsigned (get_hi ptr)) \/ perm m2 ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  destruct zle;simpl;auto.
  destruct zlt;simpl;auto.
Qed.

Lemma free_can_access_block_1 : can_access_block m1 ptr (Some cp).
Proof.
  unfold free in FREE.
  destruct range_perm_dec;[|inv FREE].
  destruct can_access_block_dec;inv FREE.
  auto.
Qed.

Lemma free_can_access_block_2 : can_access_block m2 ptr (Some cp).
Proof.
  unfold free in FREE.
  destruct range_perm_dec;[|inv FREE].
  destruct can_access_block_dec;[|inv FREE].
  destruct is_mem_cap_b;inv FREE.
  auto.
Qed.

Lemma free_can_access_block_inj_1 :
  forall b cp', can_access_block m1 b cp' -> can_access_block m2 b cp'.
Proof.
  unfold can_access_block.
  intros b [cp' |] Hown; [| trivial].
  unfold free in FREE.
  destruct range_perm_dec;[|inv FREE].
  destruct can_access_block_dec;[|inv FREE].
  destruct is_mem_cap_b;inv FREE.
  auto.
Qed.

Lemma free_can_access_block_inj_2 :
  forall b cp', can_access_block m2 b cp' -> can_access_block m1 b cp'.
Proof.
  unfold can_access_block.
  intros b [cp' |] Hown; [| trivial].
  unfold free in FREE.
  destruct range_perm_dec;[|inv FREE].
  destruct can_access_block_dec;[|inv FREE].
  destruct is_mem_cap_b;inv FREE.
  auto.
Qed.

Theorem valid_access_free_1:
  forall k chunk ptr' p cp' o ptr'' ofs,
      valid_access k m1 chunk ptr' ofs p cp' o ptr'' ->
      disjoint_cap ptr ptr' ->
      valid_access k m2 chunk ptr' ofs p cp' o ptr''.
Proof.
  intros.
  inv H. destruct H2 as [H2 [H3 H4]].
  assert (in_bounds k ptr' ofs (size_chunk_nat chunk)).
  { destruct H1 as [? ?].
    destruct o; destruct H as [? ?];auto. }
  constructor; auto with mem.
  destruct ptr',o0;[|easy..].
  simpl in *. rewrite <- size_chunk_conv in H.
  pose proof (size_chunk_pos chunk).
  red; intros. split;[|split];auto.
  - red;intros; eapply perm_free_1; eauto.    
    inv H0; simpl in *; omega.
  - apply free_can_access_block_inj_1; auto.
Qed.

Theorem valid_access_free_2:
  forall k chunk ptr' p cp' ofs o ptr'',
      derived_cap ptr ptr' ->
      ~(valid_access k m2 chunk ptr' ofs p cp' o ptr'') .
Proof.
  intros; red; intros.
  apply valid_access_in_bounds in H0 as B.
  destruct H0 as [_ [? _]].
  unfold free in FREE.
  elim (perm_free_2 (derive_offset k ptr' ofs) Cur p).
  - inv H;[|inv H1];simpl;inv B.
    split;omega.
  - apply H0.
    generalize (size_chunk_pos chunk). omega.
Qed.

Theorem valid_access_free_inv_1:
  forall k chunk ptr' ofs p cp' o ptr'',
  valid_access k m2 chunk ptr' ofs p cp' o ptr'' ->
  valid_access k m1 chunk ptr' ofs p cp' o ptr''.
Proof.
  intros. destruct H as [[? ?] [? [? ?]]]. repeat split; auto.
  - red; intros. generalize (H1 ofs0 H4).
    rewrite free_result. unfold perm, unchecked_free; simpl.
    destruct zle,zlt;simpl;auto. tauto.
  - apply free_can_access_block_inj_2; easy.
Qed.

Lemma not_disjoint_nonemptycap_exists:
  forall c c',
    (Ptrofs.unsigned (get_lo c)) < (Ptrofs.unsigned (get_hi c)) ->
    (Ptrofs.unsigned (get_lo c')) < (Ptrofs.unsigned (get_hi c')) ->
    ~ disjoint_cap c c' ->
    exists ofs, (Ptrofs.unsigned (get_lo c)) <= ofs < (Ptrofs.unsigned (get_hi c))
           /\ (Ptrofs.unsigned (get_lo c')) <= ofs < (Ptrofs.unsigned (get_hi c')).
Proof.
  intros.
  apply Classical_Prop.not_or_and in H1 as [n1 n2].
  apply Znot_le_gt in n1.
  apply Znot_ge_lt in n2.
Admitted.  

Theorem valid_access_free_inv_2:
  forall k chunk ptr' ofs p cp' o ptr'',
      valid_access k m2 chunk ptr' ofs p cp' o ptr'' ->
      disjoint_cap ptr ptr' \/ no_auth ptr.
Proof.
  intros.
  destruct (disjoint_cap_dec ptr ptr');auto.
  apply valid_access_in_bounds in H as B.
  destruct ptr',o0;[|easy..]. destruct B as [B1 B2].
  destruct (Z_le_dec (Ptrofs.unsigned (get_hi ptr)) (Ptrofs.unsigned (get_lo ptr)));cycle 1.
  - eapply not_disjoint_nonemptycap_exists in n;[..|omega|simpl;omega].
    destruct n as [ofs' [D1 D2]].
    destruct H as [_ [H _]]. simpl in *.
    admit.
  - admit.
Admitted.

Theorem load_free:
  forall k chunk ptr' ofs cp',
      disjoint_cap ptr ptr' ->
      load k chunk m2 ptr' ofs cp' = load k chunk m1 ptr' ofs cp'.
Proof.
  intros. unfold load.
  destruct (valid_access_cap_dec);auto.
  destruct valid_access_ptr_dec;auto.
  rewrite pred_dec_true.
  rewrite free_result; auto.
  eapply valid_access_free_inv_1; split;eauto.
  rewrite pred_dec_false; auto.
  red; intro; elim n. eapply valid_access_free_1;auto. split;eauto.
Qed.

Theorem load_free_2:
  forall k chunk b ofs v cp',
  load k chunk m2 b ofs cp' = inl v -> load k chunk m1 b ofs cp' = inl v.
Proof.
  intros.
  pose proof valid_access_free_inv_1 as L.
  unfold load. rewrite !pred_dec_true.
  rewrite (load_result _ _ _ _ _ _ _ H). rewrite free_result; auto.
  all: edestruct L as [? ?];eauto with mem.
Qed.

Theorem loadbytes_free:
  forall k ptr' ofs n cp',
  disjoint_cap ptr ptr' ->
  loadbytes k m2 ptr' ofs n cp' = loadbytes k m1 ptr' ofs n cp'.
Proof.
  intros. unfold loadbytes.
  destruct dynamic_conditions_cap_dec;auto.
  destruct range_perm_dec,dynamic_conditions_ptr_dec;simpl;auto.
  - setoid_rewrite pred_dec_true.
    rewrite free_result; auto.
    red; intros. eapply perm_free_3; eauto.
    apply free_can_access_block_inj_2; assumption.
  - setoid_rewrite pred_dec_false at 2.
    rewrite andb_comm. reflexivity.
    intro Hcontra. apply n0. apply free_can_access_block_inj_1; assumption.
  - setoid_rewrite pred_dec_false at 1; auto.
    red; intros. apply n0. elim n0; red; intros.
    eapply perm_free_1; eauto.
    assert (in_bounds k ptr' ofs (Z.to_nat n)) as B.
    { inv d. inv H2. auto. }
    destruct ptr',o;[|easy..].
    simpl in *.
    destruct H.
    + simpl in *. omega.
    + simpl in *. rewrite Z2Nat.id in B. omega. omega.
  - setoid_rewrite pred_dec_false at 1; auto.
    red; intros. apply n0. elim n0; red; intros.
    eapply perm_free_1; eauto.
    assert (in_bounds k ptr' ofs (Z.to_nat n)) as B.
    { inv d. inv H2. auto. }
    destruct ptr',o;[|easy..].
    simpl in *.
    destruct H.
    + simpl in *. omega.
    + simpl in *. rewrite Z2Nat.id in B. omega. omega.
Qed.    

Theorem loadbytes_free_2:
  forall k ptr' ofs n cp' bytes,
  loadbytes k m2 ptr' ofs n cp' = inl bytes -> loadbytes k m1 ptr' ofs n cp' = inl bytes.
Proof.
  intros. unfold loadbytes in *.
  destruct dynamic_conditions_cap_dec;[|inv H].
  destruct range_perm_dec;[|inv H].
  destruct (dynamic_conditions_ptr_dec);inv H.
  setoid_rewrite pred_dec_true;simpl;auto. rewrite free_result;auto.
  red; intros. apply perm_free_3; auto.
  apply free_can_access_block_inj_2; assumption.
Qed.

End FREE.

Local Hint Resolve perm_free_1 perm_free_2 perm_free_3
             valid_access_free_1 valid_access_free_inv_1: mem.

(** ** Properties related to [drop_perm] *)

Theorem range_perm_drop_1:
  forall m c p cp m', drop_perm m c p cp = inl m' ->
  range_perm m (Ptrofs.unsigned (get_lo c)) (Ptrofs.unsigned (get_hi c)) Cur Freeable.
Proof.
  unfold drop_perm; intros.
  destruct (range_perm_dec). auto. discriminate.
Qed.

Theorem range_perm_drop_2_heap:
  forall m cp p ptr,
  range_perm m (Ptrofs.unsigned (get_lo ptr)) (Ptrofs.unsigned (get_hi ptr)) Cur Freeable ->
  can_access_block m ptr (Some cp) ->
  { m' | drop_perm m ptr p cp = inl m' }.
Proof.
  unfold drop_perm; intros.
  destruct (range_perm_dec).
- destruct (can_access_block_dec).
+ econstructor. eauto.
+ contradiction.
- contradiction.
Defined.

Section DROP.

Variable m: mem.  
Variable ptr: occap.
Variable p: permission.
Variable cp: compartment.
Variable m': mem.
Hypothesis DROP: drop_perm m ptr p cp = inl m'.

Theorem drop_block_compartment:
  forall b', block_compartment m' b' = block_compartment m b'.
Proof.
unfold drop_perm in *.
destruct range_perm_dec; try discriminate.
destruct can_access_block_dec; try discriminate.
injection DROP as <-. intros b'. reflexivity.
Qed.

Theorem perm_drop_1:
  forall ofs k, Ptrofs.unsigned (get_lo ptr) <= ofs < Ptrofs.unsigned (get_hi ptr) -> perm m' ofs k p.
Proof.
  intros.
  unfold drop_perm in DROP.
  destruct range_perm_dec;
  destruct (can_access_block_dec m ptr (Some cp));inv DROP.
  unfold perm. simpl. (* rewrite PMap.gss. unfold proj_sumbool. *)
  destruct zle,zlt; simpl. constructor.
  all: omega.
Qed.

Theorem perm_drop_2:
  forall ofs k p', (Ptrofs.unsigned (get_lo ptr)) <= ofs < (Ptrofs.unsigned (get_hi ptr)) -> perm m' ofs k p' -> perm_order p p'.
Proof.
  intros.
  unfold drop_perm in DROP.
  destruct range_perm_dec;
  destruct (can_access_block_dec m ptr (Some cp));inv DROP.
  revert H0.
  apply r in H as P.
  unfold perm in *;simpl.  
  destruct zle,zlt; simpl;auto.
  all: byContradiction; intuition omega.
Qed.

Theorem perm_drop_3:
  forall ofs k p', ofs < (Ptrofs.unsigned (get_lo ptr)) \/ (Ptrofs.unsigned (get_hi ptr)) <= ofs -> perm m ofs k p' -> perm m' ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP.
  destruct range_perm_dec;
  destruct (can_access_block_dec m ptr (Some cp));inv DROP.
  unfold perm; simpl.
  unfold proj_sumbool. destruct (zle). destruct (zlt).
  byContradiction. intuition omega.
  auto. auto.
Qed.

Theorem perm_drop_4:
  forall ofs k p', perm m' ofs k p' -> perm m ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP.
  destruct range_perm_dec;
  destruct (can_access_block_dec m ptr (Some cp));inv DROP.
  revert H. unfold perm; simpl.
  unfold proj_sumbool. destruct (zle). destruct (zlt).
  simpl. intros. apply perm_implies with p. apply perm_implies with Freeable. apply perm_cur.
  apply r. tauto. auto with mem. auto.
  auto. auto.
Qed.

Theorem can_access_block_drop_1:
  forall b' cp', can_access_block m b' cp' -> can_access_block m' b' cp'.
Proof.
  unfold can_access_block. intros b' cp' Hown.
  unfold drop_perm in DROP.
  destruct range_perm_dec;
  destruct (can_access_block_dec m ptr (Some cp));inv DROP.
  assumption.
Qed.

Theorem can_access_block_drop_2:
  forall b' cp', can_access_block m' b' cp' -> can_access_block m b' cp'.
Proof.
  unfold can_access_block. intros b' cp' Hown.
  unfold drop_perm in DROP.
  destruct range_perm_dec;
  destruct (can_access_block_dec m ptr (Some cp));inv DROP.
  assumption.
Qed.

Theorem can_access_block_drop_3:
  can_access_block m ptr (Some cp).
  unfold drop_perm in DROP.
  destruct range_perm_dec;
  destruct (can_access_block_dec m ptr (Some cp));inv DROP.
  assumption.
Qed.

Theorem can_access_block_drop_4:
  can_access_block m' ptr (Some cp).
  unfold drop_perm in DROP.
  destruct range_perm_dec;
  destruct (can_access_block_dec m ptr (Some cp));inv DROP.
  destruct m. unfold can_access_block in *. simpl in *.
  assumption.
Qed.

(* RB: NOTE: Other lemmas in the style of perm_drop_*? *)

Lemma valid_access_drop_1:
  forall k chunk ptr' ofs p' cp' v' ptr'',
  disjoint_cap ptr ptr' ->
  valid_access k m chunk ptr' ofs p' cp' v' ptr'' -> valid_access k m' chunk ptr' ofs p' cp' v' ptr''.
Proof.
  intros. destruct H0. split; auto.
  red; intros.
Admitted.
(*   destruct (eq_block b' b). subst b'. *)
(*   destruct (zlt ofs0 lo). eapply perm_drop_3; eauto. *)
(*   destruct (zle hi ofs0). eapply perm_drop_3; eauto. *)
(*   apply perm_implies with p. eapply perm_drop_1; eauto. omega. *)
(*   generalize (size_chunk_pos chunk); intros. intuition. *)
(*   eapply perm_drop_3; eauto. *)
(*   split. apply can_access_block_drop_1; easy. easy. *)
(* Qed. *)

Lemma valid_access_drop_2:
  forall k chunk ptr' ofs p' cp' v' ptr'',
  valid_access k m' chunk ptr' ofs p' cp' v' ptr'' -> valid_access k m chunk ptr' ofs p' cp' v' ptr''.
Proof.
  intros. destruct H; split; auto.
  destruct H0 as [? [? ?]].
  repeat split;auto. red; intros. eapply perm_drop_4; eauto.
  apply can_access_block_drop_2; easy.
Qed.

Theorem load_drop:
  forall k chunk ptr ofs cp',
  derive_offset k ptr ofs + size_chunk chunk <= (Ptrofs.unsigned (get_lo ptr)) \/ (Ptrofs.unsigned (get_hi ptr)) <= derive_offset k ptr ofs \/ perm_order p Readable ->
  load k chunk m' ptr ofs cp' = load k chunk m ptr ofs cp'.
Proof.
  intros.
  unfold load.
(*   destruct (valid_access_dec m chunk b' ofs Readable). *)
(*   rewrite pred_dec_true. *)
(*   unfold drop_perm in DROP. *)
(*   destruct (range_perm_dec m b lo hi Cur Freeable); *)
(*   destruct (can_access_block_dec m b (Some cp)); *)
(*   inv DROP. simpl. auto. *)
(*   eapply valid_access_drop_1; eauto. *)
(*   rewrite pred_dec_false. auto. *)
(*   red; intros; elim n. eapply valid_access_drop_2; eauto. *)
  (* Qed. *)
Admitted.

(*Theorem loadbytes_drop:
  forall b' ofs n cp',
  b' <> b \/ ofs + n <= lo \/ hi <= ofs \/ perm_order p Readable ->
  loadbytes m' b' ofs n cp' = loadbytes m b' ofs n cp'.
Proof.
  intros.
  unfold loadbytes.
  destruct (range_perm_dec m b' ofs (ofs + n) Cur Readable).
- destruct (can_access_block_dec m b' cp').
+ setoid_rewrite pred_dec_true.
* unfold drop_perm in DROP.
  destruct (range_perm_dec m b lo hi Cur Freeable);
  destruct (can_access_block_dec m b (Some cp));
  inv DROP. simpl. auto.
* red; intros.
  destruct (eq_block b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto.
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. omega. intuition.
  eapply perm_drop_3; eauto.
* apply can_access_block_drop_1; assumption.
+ setoid_rewrite pred_dec_false at 2.
* rewrite andb_comm. reflexivity.
* intro Hcontra. apply n0. apply can_access_block_drop_2; assumption.
- setoid_rewrite pred_dec_false at 1; eauto.
  red; intros; elim n0; red; intros.
  eapply perm_drop_4; eauto.
Qed.*)

End DROP.

End Mem.

Notation mem := Mem.mem.

Global Opaque Mem.alloc Mem.free Mem.store Mem.load Mem.storebytes Mem.loadbytes.

Hint Resolve
  (* Mem.valid_not_valid_diff *)
  Mem.perm_implies
  Mem.perm_cur
  Mem.perm_max
  (* Mem.perm_valid_block *)
  Mem.range_perm_implies
  Mem.range_perm_cur
  Mem.range_perm_max
  Mem.valid_access_implies
  (* Mem.valid_access_valid_block *)
  Mem.valid_access_perm
  Mem.valid_access_load
  Mem.load_valid_access
  Mem.loadbytes_range_perm
  Mem.valid_access_store
  Mem.perm_store_1
  Mem.perm_store_2
  (* Mem.nextblock_store *)
  (* Mem.store_valid_block_1 *)
  (* Mem.store_valid_block_2 *)
  Mem.store_valid_access_1
  Mem.store_valid_access_2
  Mem.store_valid_access_3
  Mem.storebytes_range_perm
  Mem.perm_storebytes_1
  Mem.perm_storebytes_2
  Mem.storebytes_valid_access_1
  Mem.storebytes_valid_access_2
  (* Mem.nextblock_storebytes *)
  (* Mem.storebytes_valid_block_1 *)
  (* Mem.storebytes_valid_block_2 *)
  (* Mem.nextblock_alloc *)
  (* Mem.alloc_result *)
  (* Mem.valid_block_alloc *)
  (* Mem.fresh_block_alloc *)
  (* Mem.valid_new_block *)
  Mem.perm_alloc_1
  Mem.perm_alloc_2
  Mem.perm_alloc_3
  (* Mem.perm_alloc_4 *)
  Mem.perm_alloc_inv
  Mem.valid_access_alloc_other
  Mem.valid_access_alloc_same
  Mem.valid_access_alloc_inv
  Mem.range_perm_free
  Mem.free_range_perm
  (* Mem.nextblock_free *)
  (* Mem.valid_block_free_1 *)
  (* Mem.valid_block_free_2 *)
  Mem.perm_free_1
  Mem.perm_free_2
  Mem.perm_free_3
  Mem.valid_access_free_1
  Mem.valid_access_free_2
  Mem.valid_access_free_inv_1
  Mem.valid_access_free_inv_2
  (* Mem.unchanged_on_refl *)
: mem.
