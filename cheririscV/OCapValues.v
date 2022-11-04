(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This module defines the type of values that is used in the dynamic
  semantics of a capability machine backend *)

Require Import Coqlib.
Require Import CapAST.
Require Import Integers.
Require Import Floats.
Require Import ValType.

Definition seal := ptrofs.

(** A value is either:
- a machine integer;
- a floating-point number;
- a heap capability: a tuple with: permission, locality, bounds, address
- a stack capability: a tuple with: stack depth, permission bounds, address
- a data return capability: a tuple with: bounds
- a code return capability: a tuple with: bounds, address 
- a seal: a tuple with bounds and seal address
- a sealed heap/stack/data/code/seal capability
- the [Vundef] value denoting an arbitrary bit pattern, such as the
  value of an uninitialized variable.
 *)

Inductive permission: Type :=
| O
| RO
| RW
| RWL
| RX
| E
| RWX
| RWLX
| URW
| URWL
| URWX
| URWLX.

Definition perm_dec (x y: permission): {x=y} + {x<>y}.
Proof. decide equality. Defined.
Global Opaque perm_dec.

Inductive locality: Type :=
| Global
| Local
| Directed.

Definition loc_dec (x y: locality): {x=y} + {x<>y}.
Proof. decide equality. Defined.

Definition locFlowsTo (l1 l2: locality): bool :=
  match l1 with
  | Directed => true
  | Local => match l2 with
            | Directed => false
            | _ => true
            end
  | Global => match l2 with
             | Global => true
             | _ => false
             end
  end.

Definition locFlows : locality -> locality -> Prop :=
  fun p1 p2 => locFlowsTo p1 p2 = true.

Lemma locFlowsTransitive:
  forall p1 p2 p3, locFlows p1 p2 -> locFlows p2 p3 -> locFlows p1 p3.
Proof.
  red; intros; destruct p1; destruct p2; destruct p3; try congruence; auto.
Qed.

Lemma locFlowsReflexive:
  forall p, locFlows p p.
Proof.
  intros; unfold locFlows; destruct p; simpl; auto.
Qed.

Definition permFlowsTo (p1 p2: permission): bool :=
  match p1 with
  | O => true
  | E => match p2 with
        | E | RX | RWX | RWLX => true
        | _ => false
        end
  | RX => match p2 with
         | RX | RWX | RWLX => true
         | _ => false
         end
  | RWX => match p2 with
          | RWX | RWLX => true
          | _ => false
          end
  | RWLX => match p2 with
           | RWLX => true
           | _ => false
           end
  | RO => match p2 with
         | E | O | URW | URWL | URWX | URWLX => false
         | _ => true
         end
  | RW => match p2 with
         | RW | RWX | RWL | RWLX => true
         | _ => false
         end
  | RWL => match p2 with
          | RWL | RWLX => true
          | _ => false
          end
  | URW => match p2 with
          | URW | URWL | URWX | URWLX | RW | RWX | RWL | RWLX => true
          | _ => false
          end
  | URWL => match p2 with
           | URWL | RWL | RWLX | URWLX => true
           | _ => false
           end
  | URWX => match p2 with
           | URWX | RWX | RWLX | URWLX => true
           | _ => false
           end
  | URWLX => match p2 with
            | URWLX | RWLX => true
            | _ => false
            end
  end.

(* perm-flows-to as a predicate *)
Definition permFlows : permission -> permission -> Prop :=
  fun p1 p2 => permFlowsTo p1 p2 = true.

Lemma permFlowsTransitive:
  forall p1 p2 p3, permFlows p1 p2 -> permFlows p2 p3 -> permFlows p1 p3.
Proof.
  red; intros; destruct p1; destruct p2; destruct p3; try congruence; auto.
Qed.

Lemma permFlowsReflexive:
  forall p, permFlows p p.
Proof.
  intros; unfold permFlows; destruct p; simpl; auto.
Qed.

(* Auxiliary definitions to work on permissions *)
Definition isU (p: permission) :=
  match p with
  | URW | URWL | URWX | URWLX => true
  | _ => false
  end.

Definition pwl p : bool :=
  match p with
  | RWLX | RWL => true
  | _ => false
  end.

Definition pwlU p : bool :=
  match p with
  | RWLX | RWL | URWLX | URWL => true
  | _ => false
  end.

Definition isGlobal l: bool :=
  match l with
  | Global => true
  | _ => false
  end.

(* Uninitialized capabilities are neither read nor write allowed *)
Definition readAllowed (p: permission): bool :=
  match p with
  | RWX | RWLX | RX | RW | RWL | RO => true
  | _ => false
  end.

Definition writeAllowed (p: permission): bool :=
  match p with
  | RWX | RWLX | RW | RWL => true
  | _ => false
  end.

Definition promote_perm (p: permission): permission :=
  match p with
  | URW => RW
  | URWL => RWL
  | URWX => RWX
  | URWLX => RWLX
  | _ => p
  end.

Lemma writeA_implies_readA p :
  writeAllowed p = true -> readAllowed p = true.
Proof. destruct p; auto. Qed.

Inductive ocsealable: Type :=
| OCVmem: permission -> locality -> ptrofs -> ptrofs -> ptrofs -> ocsealable
| OCVseal: seal -> seal -> seal -> ocsealable.

Definition sealable_dec (x y: ocsealable): {x=y} + {x<>y}.
Proof.
  decide equality;
    (apply perm_dec || apply loc_dec || apply Ptrofs.eq_dec || apply eq_block).
Defined.
Global Opaque sealable_dec.

Inductive occap: Type :=
| OCsealable : ocsealable -> occap
| OCsealed : seal -> ocsealable -> occap.

Definition occap_dec (x y : occap): {x=y} + {x<>y}.
Proof.
  decide equality; (apply sealable_dec || apply Ptrofs.eq_dec).
Defined.
Global Opaque occap_dec.

Definition permFlowsCap (c c': occap): Prop :=
  match c,c' with
  | OCsealable (OCVmem perm l b e a),OCsealable (OCVmem perm' l' b' e' a') => permFlows perm perm'
  | _,_ => False
  end.

Definition locFlowsCap (c c': occap): Prop :=
  match c,c' with
  | OCsealable (OCVmem perm l b e a),OCsealable (OCVmem perm' l' b' e' a') => locFlows l l'
  | _,_ => False
  end.

Definition promote_cap (c: occap): option occap :=
  match c with
  | OCsealable (OCVmem perm l b e a) => Some (OCsealable (OCVmem (promote_perm perm) l b e a))
  | _ => None
  end.

Definition readAllowedCap (c: occap) : bool :=
  match c with
  | OCsealable (OCVmem perm _ _ _ _) => readAllowed perm
  | _ => false
  end.

Definition writeAllowedCap (c: occap) : bool :=
  match c with
  | OCsealable (OCVmem perm _ _ _ _) => writeAllowed perm
  | _ => false
  end.

Definition isGlobalCap (c: occap) : bool :=
  match c with
  | OCsealable (OCVmem _ l _ _ _) => isGlobal l
  | _ => false
  end.

Definition isUCap (c: occap) : bool :=
  match c with
  | OCsealable (OCVmem perm _ _ _ _) => isU perm
  | _ => false
  end.

Definition pwlCap (c: occap) : bool :=
  match c with
  | OCsealable (OCVmem perm _ _ _ _) => pwl perm
  | _ => false
  end.

Definition pwlUCap (c: occap) : bool :=
  match c with
  | OCsealable (OCVmem perm _ _ _ _) => pwlU perm
  | _ => false
  end.

Definition get_lo_seal (σ : ocsealable) : ptrofs :=
  match σ with
  | OCVmem sf perm lo hi a => lo
  | OCVseal σlo σhi σa => σlo
  end.
Definition get_lo (v : occap) : ptrofs :=
  match v with
  | OCsealable σ => get_lo_seal σ
  | OCsealed _ σ => get_lo_seal σ
  end.

Definition get_hi_seal (σ : ocsealable) : ptrofs :=
  match σ with
  | OCVmem sf perm lo hi a => hi
  | OCVseal σlo σhi σa => σhi
  end.
Definition get_hi (v : occap) : ptrofs :=
  match v with
  | OCsealable σ => get_hi_seal σ
  | OCsealed _ σ => get_hi_seal σ
  end.

Definition get_region_size (c: occap) : Z :=
  Ptrofs.unsigned (get_hi c) - Ptrofs.unsigned (get_lo c).
Definition get_region_size_nat (c: occap) : nat :=
  Z.to_nat (get_region_size c).

Definition get_addr_seal (σ : ocsealable) : ptrofs :=
  match σ with
  | OCVmem perm l lo hi a => a
  | OCVseal σlo σhi σa => σa
  end.
Definition get_addr (v : occap) : ptrofs :=
  match v with
  | OCsealable σ => get_addr_seal σ
  | OCsealed _ σ => get_addr_seal σ
  end.

Definition get_locality_seal (σ: ocsealable) : option locality :=
  match σ with
  | OCVmem perm l lo hi a => Some l
  | OCVseal σlo σhi σa => None
  end.
Definition get_locality (v: occap): option locality :=
  match v with
  | OCsealable σ | OCsealed _ σ => get_locality_seal σ
  end.

Definition stack_derived_seal (σ: ocsealable): Prop :=
  match σ with
  | OCVmem _ Directed _ _ _ => True
  | _ => False
  end.
Definition stack_derived (v: occap): Prop :=
  match v with
  | OCsealable σ | OCsealed _ σ => stack_derived_seal σ
  end.

Definition incr_addr_stk (v: occap) (ofs: Z) : option occap :=
  match v with
  | OCsealable (OCVmem perm l lo hi a) =>
      Some (OCsealable (OCVmem perm l lo hi (Ptrofs.repr ((Ptrofs.unsigned a) + ofs))))
  | _ => None
  end.

Module Ptr : VAL.

(*
Error:
The kernel does not recognize yet that a parameter can be instantiated by an inductive type. Hint: you can rename the inductive type and give a definition to map the old name to the new name.
*)
Inductive pointer': Type :=
| heap_ptr: ptrofs -> pointer'
| stack_ptr: ptrofs -> pointer'.

Let pointer := pointer'.

Theorem eq_dec_pointer: forall (p1 p2: pointer), {p1 = p2} + {~ p1 = p2}.
Proof.
  decide equality.
  - now apply Ptrofs.eq_dec.
  - now apply Ptrofs.eq_dec.
Qed.

Definition pointer_arith (f: ptrofs -> ptrofs -> ptrofs) (ptr1: pointer) (ofs: ptrofs): pointer :=
  match ptr1 with
  | heap_ptr ofs1 => heap_ptr (f ofs1 ofs)
  | stack_ptr ofs1 => stack_ptr (f ofs1 ofs)
  end.

Definition pointer_add (ptr: pointer) (n2: ptrofs) : option pointer :=
  if Archi.ptr64 then None else Some (pointer_arith Ptrofs.add ptr n2).

Definition pointer_sub (ptr: pointer) (n2: ptrofs) : option pointer :=
  if Archi.ptr64 then None else Some (pointer_arith Ptrofs.sub ptr n2).

Definition pointer_pointer_sub (ptr1 ptr2: pointer) : option ptrofs :=
  match ptr1, ptr2 with
  | heap_ptr ofs1, heap_ptr ofs2
  | stack_ptr ofs1, stack_ptr ofs2 =>
      if Archi.ptr64 then None else
        Some (Ptrofs.sub ofs1 ofs2)
  | _, _ => None
  end.

(** Comparisons *)

Section COMPARISONS.

(* Variable valid_ptr: Z -> bool. *)
(* TODO Check interface *)
Definition valid_ptr: Z -> bool := fun _ => true.
Let weak_valid_ptr (ofs: Z) := valid_ptr ofs || valid_ptr (ofs - 1).

Definition pointer_pointer_cmpu (diff_blocks: option bool) (c: comparison) (ptr1 ptr2: pointer) : option bool :=
  match ptr1, ptr2 with
  | stack_ptr ofs1, stack_ptr ofs2
  | heap_ptr ofs1, heap_ptr ofs2 =>
      if Archi.ptr64 then None else
        if weak_valid_ptr (Ptrofs.unsigned (ofs1))
           && weak_valid_ptr (Ptrofs.unsigned (ofs2))
        then Some (Ptrofs.cmpu c (ofs1) (ofs2))
        else None
  | _, _ => None
  end.

End COMPARISONS.

Theorem pointer_add_assoc_int:
  forall ptr i1 i2,
    Archi.ptr64 = false ->
    pointer_add ptr (Ptrofs.of_int (Int.add i1 i2)) =
      match pointer_add ptr (Ptrofs.of_int i1) with
      | Some ptr' => pointer_add ptr' (Ptrofs.of_int i2)
      | None => None
      end.
Proof.
  intros ptr i1 i2 ARCHI.
  unfold pointer_add, pointer_arith.
  rewrite ARCHI.
  destruct ptr as [ofs | ofs].
  - rewrite Ptrofs.add_assoc.
    erewrite Ptrofs.agree32_of_int_eq; [reflexivity |].
    apply Ptrofs.agree32_add;
      [assumption | |];
      now apply Ptrofs.agree32_of_int.
  - rewrite Ptrofs.add_assoc.
    erewrite Ptrofs.agree32_of_int_eq; [reflexivity |].
    apply Ptrofs.agree32_add;
      [assumption | |];
      now apply Ptrofs.agree32_of_int.
Qed.

Theorem pointer_add_assoc_long:
  forall ptr i1 i2,
    Archi.ptr64 = true ->
    pointer_add ptr (Ptrofs.of_int64 (Int64.add i1 i2)) =
      match pointer_add ptr (Ptrofs.of_int64 i1) with
      | Some ptr' => pointer_add ptr' (Ptrofs.of_int64 i2)
      | None => None
      end.
Proof.
  intros ptr i1 i2 ARCHI.
  unfold pointer_add.
  rewrite ARCHI.
  reflexivity.
Qed.

Theorem pointer_add_commut:
  forall ptr i1 i2,
    match pointer_add ptr i1 with
    | Some ptr' => pointer_add ptr' i2
    | None => None
    end =
    match pointer_add ptr i2 with
    | Some ptr' => pointer_add ptr' i1
    | None => None
    end.
Proof.
  intros ptr i1 i2.
  unfold pointer_add, pointer_arith.
  destruct Archi.ptr64 eqn:ARCHI; [reflexivity |].
  destruct ptr as [ofs | ofs].
  - rewrite !Ptrofs.add_assoc.
    now rewrite (Ptrofs.add_commut i2 i1).
  - rewrite !Ptrofs.add_assoc.
    now rewrite (Ptrofs.add_commut i2 i1).
Qed.

Theorem pointer_add_sub_l:
  forall ptr i1 i2,
    match pointer_add ptr i1 with
    | Some ptr' => pointer_sub ptr' i2
    | None => None
    end =
    match pointer_sub ptr i2 with
    | Some ptr' => pointer_add ptr' i1
    | None => None
    end.
  intros ptr i1 i2.
  unfold pointer_add, pointer_sub, pointer_arith.
  destruct Archi.ptr64 eqn:ARCHI; [reflexivity |].
  destruct ptr as [ofs | ofs].
  - now rewrite Ptrofs.sub_add_l.
  - now rewrite Ptrofs.sub_add_l.
Qed.

Theorem pointer_pointer_add_sub_l:
  forall ptr i1 i2,
    match pointer_add ptr i1 with
    | Some ptr' => pointer_pointer_sub ptr' i2
    | None => None
    end =
    match pointer_pointer_sub ptr i2 with
    | Some ptrofs => Some (Ptrofs.add i1 ptrofs)
    | None => None
    end.
Proof.
  intros ptr1 i ptr2.
  unfold pointer_add, pointer_pointer_sub, pointer_arith.
  destruct Archi.ptr64 eqn:ARCHI;
    [destruct ptr1; destruct ptr2; reflexivity |].
  destruct ptr1 as [ofs1 | ofs1]; destruct ptr2 as [ofs2 | ofs2].
  - rewrite Ptrofs.sub_add_l.
    now rewrite Ptrofs.add_commut.
  - reflexivity.
  - reflexivity.
  - rewrite Ptrofs.sub_add_l.
    now rewrite Ptrofs.add_commut.
Qed.

Theorem pointer_add_sub_neg_int:
  forall p y,
    pointer_sub p (Ptrofs.of_int y) = pointer_add p (Ptrofs.of_int (Int.neg y)).
Proof.
  intros ptr y.
  unfold pointer_sub, pointer_add, pointer_arith.
  destruct Archi.ptr64 eqn:ARCHI; [reflexivity |].
  f_equal. f_equal.
  destruct ptr as [ofs | ofs].
  - erewrite (Ptrofs.agree32_of_int_eq _ (Int.neg y)).
    + now rewrite Ptrofs.sub_add_opp.
    + apply Ptrofs.agree32_neg; [assumption |].
      now apply Ptrofs.agree32_of_int.
  - erewrite (Ptrofs.agree32_of_int_eq _ (Int.neg y)).
    + now rewrite Ptrofs.sub_add_opp.
    + apply Ptrofs.agree32_neg; [assumption |].
      now apply Ptrofs.agree32_of_int.
Qed.

Theorem pointer_add_sub_neg_long:
  forall p y,
    pointer_sub p (Ptrofs.of_int64 y) = pointer_add p (Ptrofs.of_int64 (Int64.neg y)).
Proof.
  intros ptr y.
  unfold pointer_sub, pointer_add, pointer_arith.
  destruct Archi.ptr64 eqn:ARCHI; [reflexivity |].
  destruct ptr as [ofs | ofs].
  (* this one's a bit trickier *)
Admitted.

Definition offset_pointer (ptr: pointer) (delta: ptrofs) : option pointer :=
  Some (pointer_arith Ptrofs.add ptr delta).

Theorem offset_pointer_zero:
  forall p, offset_pointer p (Ptrofs.zero) = Some p.
Proof.
  intros ptr.
  unfold offset_pointer, pointer_arith.
  destruct ptr as [ofs | ofs].
  - now rewrite Ptrofs.add_zero.
  - now rewrite Ptrofs.add_zero.
Qed.

(* TODO *)
Definition normalize_pointer (p: pointer) (t: AST.captyp) : bool :=
  match t with
  | AST.CTint | AST.CTany32 => negb Archi.ptr64
  | AST.CTlong => Archi.ptr64
  | AST.CTany64 => true
  | AST.CTany128 => true
  | _ => false (* "new" fallback *)
  end.

(* TODO *)
Definition pointer_load_result (chunk: AST.cap_memory_chunk) (p: pointer) : bool :=
  match chunk with
  | AST.CMint32 => negb Archi.ptr64
  | AST.CMint64 => Archi.ptr64
  | AST.CMany32 => negb Archi.ptr64
  | AST.CMany64 => true
  | AST.CMany128 => true
  | _ => false (* "new" fallback *)
  end.

(* TODO *)
Definition has_type_pointer (_: pointer) (t: AST.captyp) : Prop := (* remove parameter? *)
  match t with
  | AST.CTint => Archi.ptr64 = false
  | AST.CTlong => Archi.ptr64 = true
  | AST.CTany64 => True
  | AST.CTany32 => Archi.ptr64 = false
  | AST.CTany128 => True
  | _ => False (* "new" fallback *)
  end.

Theorem has_type_pointer_dec:
  forall p t, {has_type_pointer p t} + {~ has_type_pointer p t}.
Proof.
  unfold has_type_pointer.
  intros _ []; auto; decide equality.
Qed.

Theorem has_subtype_pointer:
  forall ty1 ty2 v,
    AST.subtype ty1 ty2 = true -> has_type_pointer v ty1 -> has_type_pointer v ty2.
Proof.
  intros [] [] [|] SUB PTR;
    easy.
Qed.

Theorem has_type_pointer_int:
  forall p, has_type_pointer p AST.CTint -> Archi.ptr64 = false.
Proof.
  simpl. now auto.
Qed.

Theorem has_type_pointer_long:
  forall p, has_type_pointer p AST.CTlong -> Archi.ptr64 = true.
Proof.
  simpl. now auto.
Qed.

Theorem has_type_pointer_cap64:
  forall p, has_type_pointer p AST.CTcap64 -> Archi.ptr64 = false.
Proof.
  simpl. now auto.
Qed.

Theorem has_type_pointer_cap128:
  forall p, has_type_pointer p AST.CTcap128 -> Archi.ptr64 = true.
Proof.
  simpl. now auto.
Qed.

Theorem has_type_pointer_cases:
  forall p ty,
    has_type_pointer p ty ->
    ty = AST.CTint \/ ty = AST.CTlong \/ ty = AST.CTcap64 \/ ty = AST.CTcap128.
Proof.
  intros [|] []; try now auto.
  (* doesn't work *)
Abort.

Theorem has_type_pointer_load_result:
  forall p chunk,
    pointer_load_result chunk p = true ->
    has_type_pointer p (type_of_cap_chunk chunk).
Proof.
  intros ptr []; try easy.
  - simpl. now apply negb_true_iff.
  - simpl. now apply negb_true_iff.
Qed.

Theorem load_result_has_type_pointer:
  forall p ty,
    has_type_pointer p ty ->
    pointer_load_result (chunk_of_captype ty) p = true.
Proof.
  intros ptr []; try easy.
  - simpl. now apply negb_true_iff.
  - simpl. now apply negb_true_iff.
Qed.

Theorem normalize_has_type_pointer:
  forall p ty,
    normalize_pointer p ty = true ->
    has_type_pointer p ty.
Proof.
  intros ptr []; try easy.
  - simpl. now apply negb_true_iff.
  - simpl. now apply negb_true_iff.
Qed.

Theorem has_type_pointer_normalize:
  forall p ty,
    has_type_pointer p ty ->
    normalize_pointer p ty = true.
Proof.
  intros ptr []; try easy.
  - simpl. now apply negb_true_iff.
  - simpl. now apply negb_true_iff.
Qed.

Theorem normalize_any:
  forall p, normalize_pointer p AST.CTany128 = true.
Proof.
  reflexivity.
Qed.

Inductive val: Type :=
| Vundef: val
| Vint: int -> val
| Vlong: int64 -> val
| Vfloat: float -> val
| Vsingle: float32 -> val
| Vptr: pointer -> val.

Definition Vzero: val := Vint Int.zero.
Definition Vone: val := Vint Int.one.
Definition Vmone: val := Vint Int.mone.

Definition Vtrue: val := Vint Int.one.
Definition Vfalse: val := Vint Int.zero.

Definition Vnullptr :=
  if Archi.ptr64 then Vlong Int64.zero else Vint Int.zero.

Definition Vptrofs (n: ptrofs) :=
  if Archi.ptr64 then Vlong (Ptrofs.to_int64 n) else Vint (Ptrofs.to_int n).

End Ptr.

Definition pointer_ofs (ptr: pointer): ptrofs :=
  match ptr with
  | heap_ptr ofs | stack_ptr ofs => ofs
  end.
      
Inductive ocval: Type :=
| OCVundef: ocval
| OCVint: int -> ocval
| OCVlong: int64 -> ocval
| OCVfloat: float -> ocval
| OCVsingle: float32 -> ocval
| OCVcap: occap -> ocval
| OCVptr: pointer -> ocval.

(* not_ptr means more accurately "never a pointer", i.e. it's a value that is
   never refined into a pointer *)
Definition not_ptr (v: ocval) :=
  match v with
  | OCVptr _ | OCVundef => False
  | _ => True
  end.

Definition not_ptr_b (v: ocval) :=
  match v with
  | OCVptr _ | OCVundef => false
  | _ => true
  end.

Lemma not_ptr_reflect: forall v,
    not_ptr v <-> not_ptr_b v = true.
Proof.
  intros; unfold not_ptr, not_ptr_b;
    destruct v; split; auto. 
  discriminate.
  discriminate.
Qed.

Inductive is_mem_cap : occap -> Prop :=
| is_mem_cap_base p l b e a: is_mem_cap (OCsealable (OCVmem p l b e a)).

Definition is_mem_cap_b (v: occap) :=
  match v with
  | OCsealable (OCVmem _ _ _ _ _) => true
  | _ => false
  end.

Lemma is_mem_cap_reflect: forall v,
    is_mem_cap v <-> is_mem_cap_b v = true.
Proof.
  intros;unfold is_mem_cap_b;
    destruct v,o;split;auto.
  all:try discriminate.
  intros;constructor.
  all: intros H;inv H.
Qed.

Definition is_cap (v: ocval) :=
  match v with
  | OCVcap _ => True
  | _ => False
  end.

Definition is_cap_b (v: ocval) :=
  match v with
  | OCVcap _ => true
  | _ => false
  end.

Lemma is_cap_reflect: forall v,
    is_cap v <-> is_cap_b v = true.
Proof.
  intros;unfold is_cap, is_cap_b;
    destruct v;split;auto.
  all:discriminate.
Qed.

Definition is_global_or_imm (v: ocval) :=
  match v with
  | OCVcap c => isGlobalCap c
  | _ => true
  end.

Definition OCVmemcap p l base e a : occap :=
  OCsealable (OCVmem p l base e a).
Definition OCVcapptr p l base e a : ocval :=
  OCVcap (OCsealable (OCVmem p l base e a)).

Definition OCVzero: ocval := OCVint Int.zero.
Definition OCVone: ocval := OCVint Int.one.
Definition OCVmone: ocval := OCVint Int.mone.

Definition OCVtrue: ocval := OCVint Int.one.
Definition OCVfalse: ocval := OCVint Int.zero.

(** in CHERI, the NULL cap does not have the tag bit set, and has base
    and length 0. NULL is the integer zero stored as a non capability
    value in a capability register. Here we represent the NULL pointer
    (stack) capability with the tag bit set on (alternatively, one
    would have to use a 128 bit integer for NULL on 64 bit arch ) *)
Definition OCVnullmemcap := OCVmemcap O Global Ptrofs.zero Ptrofs.zero Ptrofs.zero.
Definition OCVnullcap := OCVcapptr O Global Ptrofs.zero Ptrofs.zero Ptrofs.zero.

(** A null pointer *)
Definition Vnullptr :=
  if Archi.ptr64 then OCVlong Int64.zero else OCVint Int.zero.

Definition OCVptrofs (n: ptrofs) :=
  if Archi.ptr64 then OCVlong (Ptrofs.to_int64 n) else OCVint (Ptrofs.to_int n).

(** * Operations over values *)

(** The module [Val] defines a number of arithmetic and logical operations
  over type [val].  Most of these operations are straightforward extensions
  of the corresponding integer or floating-point operations. *)

Module Val.

Definition eq (x y: ocval): {x=y} + {x<>y}.
Proof.
  decide equality.
  apply Int.eq_dec.
  apply Int64.eq_dec.
  apply Float.eq_dec.
  apply Float32.eq_dec.
  apply occap_dec.
  decide equality;
  apply Ptrofs.eq_dec.
Defined.
Global Opaque eq.

Definition has_type (v: ocval) (t: captyp) : Prop :=
  match v, t with
  | OCVundef, _ => True
  | OCVint _, CTint => True
  | OCVlong _, CTlong => True
  | OCVfloat _, CTfloat => True
  | OCVsingle _, CTsingle => True
  | OCVptr _, CTint => Archi.ptr64 = false
  | OCVptr _, CTlong => Archi.ptr64 = true 
  | OCVcap _, CTcap64 => Archi.ptr64 = false
  | OCVcap _, CTcap128 => Archi.ptr64 = true                    
  | (OCVint _ | OCVsingle _), CTany32 => True
  | (OCVint _ | OCVlong _ | OCVsingle _ | OCVptr _ | OCVfloat _), CTany64 => True
  | OCVptr _, CTany32 => Archi.ptr64 = false
  | OCVcap _, CTany64 => Archi.ptr64 = false
  | _, CTany128 => True
  | _, _ => False
  end.

Fixpoint has_type_list (vl: list ocval) (tl: list captyp) {struct vl} : Prop :=
  match vl, tl with
  | nil, nil => True
  | v1 :: vs, t1 :: ts => has_type v1 t1 /\ has_type_list vs ts
  | _, _ => False
  end.

Definition has_opttype (v: ocval) (ot: option captyp) : Prop :=
  match ot with
  | None => v = OCVundef
  | Some t => has_type v t
  end.

Lemma Vptr_has_type:
  forall ptr, has_type (OCVptr ptr) CTptr.
Proof.
  intros. unfold CTptr, has_type; destruct Archi.ptr64; reflexivity.
Qed.

Lemma Vcap_has_type:
  forall c, has_type (OCVcap c) CTcap.
Proof.
  intros. unfold CTcap, has_type; destruct Archi.ptr64; reflexivity.
Qed.

Lemma Vnullptr_has_type:
  has_type Vnullptr CTptr.
Proof.
  unfold has_type, Vnullptr, CTptr; destruct Archi.ptr64; reflexivity.
Qed.


Lemma has_subtype:
  forall ty1 ty2 v,
  subtype ty1 ty2 = true -> has_type v ty1 -> has_type v ty2.
Proof.
  intros. destruct ty1; destruct ty2; simpl in H;
  (contradiction || discriminate || assumption || idtac);
  unfold has_type in *; destruct v; auto; contradiction.
Qed.

Lemma has_subtype_list:
  forall tyl1 tyl2 vl,
  subtype_list tyl1 tyl2 = true -> has_type_list vl tyl1 -> has_type_list vl tyl2.
Proof.
  induction tyl1; intros; destruct tyl2; try discriminate; destruct vl; try contradiction.
  red; auto.
  simpl in *. InvBooleans. destruct H0. split; auto. eapply has_subtype; eauto.
Qed.

Definition has_type_dec (v: ocval) (t: captyp) : { has_type v t } + { ~ has_type v t }.
Proof.
  unfold has_type; destruct v.
- auto.
- destruct t; auto.
- destruct t; auto.
- destruct t; auto.
- destruct t; auto.
- destruct t;auto. 
  all: apply bool_dec.
- destruct t;auto. 
  all: apply bool_dec.  
Defined.

Definition has_rettype (v: ocval) (r: caprettype) : Prop :=
  match r, v with
  | CTret t, _ => has_type v t
  | CTint8signed, OCVint n => n = Int.sign_ext 8 n
  | CTint8unsigned, OCVint n => n = Int.zero_ext 8 n
  | CTint16signed, OCVint n => n = Int.sign_ext 16 n
  | CTint16unsigned, OCVint n => n = Int.zero_ext 16 n
  | _, OCVundef => True
  | _, _ => False
  end.

Lemma has_proj_rettype: forall v r,
  has_rettype v r -> has_type v (proj_rettype r).
Proof.
  destruct r; simpl; intros; auto; destruct v; try contradiction; exact I.
Qed.

(** Truth values.  Non-zero integers are treated as [True].
  The integer 0 (also used to represent the null pointer) is [False].
  Other values are neither true nor false. *)

Inductive bool_of_val: ocval -> bool -> Prop :=
  | bool_of_val_int:
      forall n, bool_of_val (OCVint n) (negb (Int.eq n Int.zero)).

(** Arithmetic operations *)

Definition neg (v: ocval) : ocval :=
  match v with
  | OCVint n => OCVint (Int.neg n)
  | _ => OCVundef
  end.

Definition negf (v: ocval) : ocval :=
  match v with
  | OCVfloat f => OCVfloat (Float.neg f)
  | _ => OCVundef
  end.

Definition absf (v: ocval) : ocval :=
  match v with
  | OCVfloat f => OCVfloat (Float.abs f)
  | _ => OCVundef
  end.

Definition negfs (v: ocval) : ocval :=
  match v with
  | OCVsingle f => OCVsingle (Float32.neg f)
  | _ => OCVundef
  end.

Definition absfs (v: ocval) : ocval :=
  match v with
  | OCVsingle f => OCVsingle (Float32.abs f)
  | _ => OCVundef
  end.

Definition maketotal (ov: option ocval) : ocval :=
  match ov with Some v => v | None => OCVundef end.

Definition intoffloat (v: ocval) : option ocval :=
  match v with
  | OCVfloat f => option_map OCVint (Float.to_int f)
  | _ => None
  end.

Definition intuoffloat (v: ocval) : option ocval :=
  match v with
  | OCVfloat f => option_map OCVint (Float.to_intu f)
  | _ => None
  end.

Definition floatofint (v: ocval) : option ocval :=
  match v with
  | OCVint n => Some (OCVfloat (Float.of_int n))
  | _ => None
  end.

Definition floatofintu (v: ocval) : option ocval :=
  match v with
  | OCVint n => Some (OCVfloat (Float.of_intu n))
  | _ => None
  end.

Definition intofsingle (v: ocval) : option ocval :=
  match v with
  | OCVsingle f => option_map OCVint (Float32.to_int f)
  | _ => None
  end.

Definition intuofsingle (v: ocval) : option ocval :=
  match v with
  | OCVsingle f => option_map OCVint (Float32.to_intu f)
  | _ => None
  end.

Definition singleofint (v: ocval) : option ocval :=
  match v with
  | OCVint n => Some (OCVsingle (Float32.of_int n))
  | _ => None
  end.

Definition singleofintu (v: ocval) : option ocval :=
  match v with
  | OCVint n => Some (OCVsingle (Float32.of_intu n))
  | _ => None
  end.

Definition negint (v: ocval) : ocval :=
  match v with
  | OCVint n => OCVint (Int.neg n)
  | _ => OCVundef
  end.

Definition notint (v: ocval) : ocval :=
  match v with
  | OCVint n => OCVint (Int.not n)
  | _ => OCVundef
  end.

Definition of_bool (b: bool): ocval := if b then OCVtrue else OCVfalse.

Definition boolocval (v: ocval) : ocval :=
  match v with
  | OCVint n => of_bool (negb (Int.eq n Int.zero))
  | OCVptr ptr => OCVtrue
  | _ => OCVundef
  end.

Definition notbool (v: ocval) : ocval :=
  match v with
  | OCVint n => of_bool (Int.eq n Int.zero)
  | OCVptr ptr => OCVfalse
  | _ => OCVundef
  end.

Definition zero_ext (nbits: Z) (v: ocval) : ocval :=
  match v with
  | OCVint n => OCVint(Int.zero_ext nbits n)
  | _ => OCVundef
  end.

Definition sign_ext (nbits: Z) (v: ocval) : ocval :=
  match v with
  | OCVint n => OCVint(Int.sign_ext nbits n)
  | _ => OCVundef
  end.

Definition singleoffloat (v: ocval) : ocval :=
  match v with
  | OCVfloat f => OCVsingle (Float.to_single f)
  | _ => OCVundef
  end.

Definition floatofsingle (v: ocval) : ocval :=
  match v with
  | OCVsingle f => OCVfloat (Float.of_single f)
  | _ => OCVundef
  end.

Definition pointer_arith (f: ptrofs -> ptrofs -> ptrofs) (ptr1: pointer) (ofs: ptrofs): pointer :=
  match ptr1 with
  | heap_ptr ofs1 => heap_ptr (f ofs1 ofs)
  | stack_ptr ofs1 => stack_ptr (f ofs1 ofs)
  end.
(* TODO: currently copied in Ptr above *)

Definition add (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 => OCVint(Int.add n1 n2)
  | OCVptr ptr1, OCVint n2 => if Archi.ptr64 then OCVundef else OCVptr (pointer_arith Ptrofs.add ptr1 (Ptrofs.of_int n2))
  | OCVint n1, OCVptr ptr2 => if Archi.ptr64 then OCVundef else OCVptr (pointer_arith Ptrofs.add ptr2 (Ptrofs.of_int n1))
  | _, _ => OCVundef
  end.

Definition sub (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 => OCVint(Int.sub n1 n2)
  | OCVptr ptr1, OCVint n2 => if Archi.ptr64 then OCVundef else OCVptr (pointer_arith Ptrofs.sub ptr1 (Ptrofs.of_int n2))
  | OCVptr (heap_ptr ofs1), OCVptr (heap_ptr ofs2) =>
      if Archi.ptr64 then OCVundef else
        OCVint(Ptrofs.to_int (Ptrofs.sub ofs1 ofs2))
  | OCVptr (stack_ptr ofs1), OCVptr (stack_ptr ofs2) =>
      if Archi.ptr64 then OCVundef else
        OCVint(Ptrofs.to_int (Ptrofs.sub ofs1 ofs2))
  | _, _ => OCVundef
  end.

Definition mul (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 => OCVint(Int.mul n1 n2)
  | _, _ => OCVundef
  end.

Definition mulhs (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 => OCVint(Int.mulhs n1 n2)
  | _, _ => OCVundef
  end.

Definition mulhu (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 => OCVint(Int.mulhu n1 n2)
  | _, _ => OCVundef
  end.

Definition divs (v1 v2: ocval): option ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 =>
      if Int.eq n2 Int.zero
      || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
      then None
      else Some(OCVint(Int.divs n1 n2))
  | _, _ => None
  end.

Definition mods (v1 v2: ocval): option ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 =>
      if Int.eq n2 Int.zero
      || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
      then None
      else Some(OCVint(Int.mods n1 n2))
  | _, _ => None
  end.

Definition divu (v1 v2: ocval): option ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 =>
      if Int.eq n2 Int.zero then None else Some(OCVint(Int.divu n1 n2))
  | _, _ => None
  end.

Definition modu (v1 v2: ocval): option ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 =>
      if Int.eq n2 Int.zero then None else Some(OCVint(Int.modu n1 n2))
  | _, _ => None
  end.

Definition add_carry (v1 v2 cin: ocval): ocval :=
  match v1, v2, cin with
  | OCVint n1, OCVint n2, OCVint c => OCVint(Int.add_carry n1 n2 c)
  | _, _, _ => OCVundef
  end.

Definition sub_overflow (v1 v2: ocval) : ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 => OCVint(Int.sub_overflow n1 n2 Int.zero)
  | _, _ => OCVundef
  end.

Definition negative (v: ocval) : ocval :=
  match v with
  | OCVint n => OCVint (Int.negative n)
  | _ => OCVundef
  end.

Definition and (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 => OCVint(Int.and n1 n2)
  | _, _ => OCVundef
  end.

Definition or (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 => OCVint(Int.or n1 n2)
  | _, _ => OCVundef
  end.

Definition xor (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 => OCVint(Int.xor n1 n2)
  | _, _ => OCVundef
  end.

Definition shl (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 =>
     if Int.ltu n2 Int.iwordsize
     then OCVint(Int.shl n1 n2)
     else OCVundef
  | _, _ => OCVundef
  end.

Definition shr (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 =>
     if Int.ltu n2 Int.iwordsize
     then OCVint(Int.shr n1 n2)
     else OCVundef
  | _, _ => OCVundef
  end.

Definition shr_carry (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 =>
     if Int.ltu n2 Int.iwordsize
     then OCVint(Int.shr_carry n1 n2)
     else OCVundef
  | _, _ => OCVundef
  end.

Definition shrx (v1 v2: ocval): option ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 =>
     if Int.ltu n2 (Int.repr 31)
     then Some(OCVint(Int.shrx n1 n2))
     else None
  | _, _ => None
  end.

Definition shru (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 =>
     if Int.ltu n2 Int.iwordsize
     then OCVint(Int.shru n1 n2)
     else OCVundef
  | _, _ => OCVundef
  end.

Definition rol (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 => OCVint(Int.rol n1 n2)
  | _, _ => OCVundef
  end.

Definition rolm (v: ocval) (amount mask: int): ocval :=
  match v with
  | OCVint n => OCVint(Int.rolm n amount mask)
  | _ => OCVundef
  end.

Definition ror (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 => OCVint(Int.ror n1 n2)
  | _, _ => OCVundef
  end.

Definition addf (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVfloat f1, OCVfloat f2 => OCVfloat(Float.add f1 f2)
  | _, _ => OCVundef
  end.

Definition subf (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVfloat f1, OCVfloat f2 => OCVfloat(Float.sub f1 f2)
  | _, _ => OCVundef
  end.

Definition mulf (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVfloat f1, OCVfloat f2 => OCVfloat(Float.mul f1 f2)
  | _, _ => OCVundef
  end.

Definition divf (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVfloat f1, OCVfloat f2 => OCVfloat(Float.div f1 f2)
  | _, _ => OCVundef
  end.

Definition floatofwords (v1 v2: ocval) : ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 => OCVfloat (Float.from_words n1 n2)
  | _, _ => OCVundef
  end.

Definition addfs (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVsingle f1, OCVsingle f2 => OCVsingle(Float32.add f1 f2)
  | _, _ => OCVundef
  end.

Definition subfs (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVsingle f1, OCVsingle f2 => OCVsingle(Float32.sub f1 f2)
  | _, _ => OCVundef
  end.

Definition mulfs (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVsingle f1, OCVsingle f2 => OCVsingle(Float32.mul f1 f2)
  | _, _ => OCVundef
  end.

Definition divfs (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVsingle f1, OCVsingle f2 => OCVsingle(Float32.div f1 f2)
  | _, _ => OCVundef
  end.

(** Operations on 64-bit integers *)

Definition longofwords (v1 v2: ocval) : ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 => OCVlong (Int64.ofwords n1 n2)
  | _, _ => OCVundef
  end.

Definition loword (v: ocval) : ocval :=
  match v with
  | OCVlong n  => OCVint (Int64.loword n)
  | _ => OCVundef
  end.

Definition hiword (v: ocval) : ocval :=
  match v with
  | OCVlong n  => OCVint (Int64.hiword n)
  | _ => OCVundef
  end.

Definition negl (v: ocval) : ocval :=
  match v with
  | OCVlong n => OCVlong (Int64.neg n)
  | _ => OCVundef
  end.

Definition notl (v: ocval) : ocval :=
  match v with
  | OCVlong n => OCVlong (Int64.not n)
  | _ => OCVundef
  end.

Definition longofint (v: ocval) : ocval :=
  match v with
  | OCVint n => OCVlong (Int64.repr (Int.signed n))
  | _ => OCVundef
  end.

Definition longofintu (v: ocval) : ocval :=
  match v with
  | OCVint n => OCVlong (Int64.repr (Int.unsigned n))
  | _ => OCVundef
  end.

Definition longoffloat (v: ocval) : option ocval :=
  match v with
  | OCVfloat f => option_map OCVlong (Float.to_long f)
  | _ => None
  end.

Definition longuoffloat (v: ocval) : option ocval :=
  match v with
  | OCVfloat f => option_map OCVlong (Float.to_longu f)
  | _ => None
  end.

Definition longofsingle (v: ocval) : option ocval :=
  match v with
  | OCVsingle f => option_map OCVlong (Float32.to_long f)
  | _ => None
  end.

Definition longuofsingle (v: ocval) : option ocval :=
  match v with
  | OCVsingle f => option_map OCVlong (Float32.to_longu f)
  | _ => None
  end.

Definition floatoflong (v: ocval) : option ocval :=
  match v with
  | OCVlong n => Some (OCVfloat (Float.of_long n))
  | _ => None
  end.

Definition floatoflongu (v: ocval) : option ocval :=
  match v with
  | OCVlong n => Some (OCVfloat (Float.of_longu n))
  | _ => None
  end.

Definition singleoflong (v: ocval) : option ocval :=
  match v with
  | OCVlong n => Some (OCVsingle (Float32.of_long n))
  | _ => None
  end.

Definition singleoflongu (v: ocval) : option ocval :=
  match v with
  | OCVlong n => Some (OCVsingle (Float32.of_longu n))
  | _ => None
  end.

Definition addl (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVlong n1, OCVlong n2 => OCVlong(Int64.add n1 n2)
  | OCVptr ptr1, OCVlong n2 => if Archi.ptr64 then OCVptr (pointer_arith Ptrofs.add ptr1 (Ptrofs.of_int64 n2)) else OCVundef
  | OCVlong n1, OCVptr ptr2 => if Archi.ptr64 then OCVptr (pointer_arith Ptrofs.add ptr2 (Ptrofs.of_int64 n1)) else OCVundef
  | _, _ => OCVundef
  end.

Definition subl (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVlong n1, OCVlong n2 => OCVlong(Int64.sub n1 n2)
  | OCVptr ofs1, OCVlong n2 =>
      if Archi.ptr64 then OCVptr (pointer_arith Ptrofs.sub ofs1 (Ptrofs.of_int64 n2)) else OCVundef
  | OCVptr (heap_ptr ofs1), OCVptr (heap_ptr ofs2) =>
      if negb Archi.ptr64 then OCVundef else OCVlong(Ptrofs.to_int64 (Ptrofs.sub ofs1 ofs2))
  | OCVptr (stack_ptr ofs1), OCVptr (stack_ptr ofs2) =>
      if negb Archi.ptr64 then OCVundef else OCVlong(Ptrofs.to_int64 (Ptrofs.sub ofs1 ofs2))
  | _, _ => OCVundef
  end.

Definition mull (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVlong n1, OCVlong n2 => OCVlong(Int64.mul n1 n2)
  | _, _ => OCVundef
  end.

Definition mull' (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVint n1, OCVint n2 => OCVlong(Int64.mul' n1 n2)
  | _, _ => OCVundef
  end.

Definition mullhs (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVlong n1, OCVlong n2 => OCVlong(Int64.mulhs n1 n2)
  | _, _ => OCVundef
  end.

Definition mullhu (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVlong n1, OCVlong n2 => OCVlong(Int64.mulhu n1 n2)
  | _, _ => OCVundef
  end.

Definition divls (v1 v2: ocval): option ocval :=
  match v1, v2 with
  | OCVlong n1, OCVlong n2 =>
      if Int64.eq n2 Int64.zero
      || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
      then None
      else Some(OCVlong(Int64.divs n1 n2))
  | _, _ => None
  end.

Definition modls (v1 v2: ocval): option ocval :=
  match v1, v2 with
  | OCVlong n1, OCVlong n2 =>
      if Int64.eq n2 Int64.zero
      || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
      then None
      else Some(OCVlong(Int64.mods n1 n2))
  | _, _ => None
  end.

Definition divlu (v1 v2: ocval): option ocval :=
  match v1, v2 with
  | OCVlong n1, OCVlong n2 =>
      if Int64.eq n2 Int64.zero then None else Some(OCVlong(Int64.divu n1 n2))
  | _, _ => None
  end.

Definition modlu (v1 v2: ocval): option ocval :=
  match v1, v2 with
  | OCVlong n1, OCVlong n2 =>
      if Int64.eq n2 Int64.zero then None else Some(OCVlong(Int64.modu n1 n2))
  | _, _ => None
  end.

Definition addl_carry (v1 v2 cin: ocval): ocval :=
  match v1, v2, cin with
  | OCVlong n1, OCVlong n2, OCVlong c => OCVlong(Int64.add_carry n1 n2 c)
  | _, _, _ => OCVundef
  end.

Definition subl_overflow (v1 v2: ocval) : ocval :=
  match v1, v2 with
  | OCVlong n1, OCVlong n2 => OCVint (Int.repr (Int64.unsigned (Int64.sub_overflow n1 n2 Int64.zero)))
  | _, _ => OCVundef
  end.

Definition negativel (v: ocval) : ocval :=
  match v with
  | OCVlong n => OCVint (Int.repr (Int64.unsigned (Int64.negative n)))
  | _ => OCVundef
  end.

Definition andl (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVlong n1, OCVlong n2 => OCVlong(Int64.and n1 n2)
  | _, _ => OCVundef
  end.

Definition orl (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVlong n1, OCVlong n2 => OCVlong(Int64.or n1 n2)
  | _, _ => OCVundef
  end.

Definition xorl (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVlong n1, OCVlong n2 => OCVlong(Int64.xor n1 n2)
  | _, _ => OCVundef
  end.

Definition shll (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVlong n1, OCVint n2 =>
     if Int.ltu n2 Int64.iwordsize'
     then OCVlong(Int64.shl' n1 n2)
     else OCVundef
  | _, _ => OCVundef
  end.

Definition shrl (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVlong n1, OCVint n2 =>
     if Int.ltu n2 Int64.iwordsize'
     then OCVlong(Int64.shr' n1 n2)
     else OCVundef
  | _, _ => OCVundef
  end.

Definition shrlu (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVlong n1, OCVint n2 =>
     if Int.ltu n2 Int64.iwordsize'
     then OCVlong(Int64.shru' n1 n2)
     else OCVundef
  | _, _ => OCVundef
  end.

Definition shrxl (v1 v2: ocval): option ocval :=
  match v1, v2 with
  | OCVlong n1, OCVint n2 =>
     if Int.ltu n2 (Int.repr 63)
     then Some(OCVlong(Int64.shrx' n1 n2))
     else None
  | _, _ => None
  end.

Definition shrl_carry (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVlong n1, OCVint n2 =>
     if Int.ltu n2 Int64.iwordsize'
     then OCVlong(Int64.shr_carry' n1 n2)
     else OCVundef
  | _, _ => OCVundef
  end.

Definition roll (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVlong n1, OCVint n2 => OCVlong(Int64.rol n1 (Int64.repr (Int.unsigned n2)))
  | _, _ => OCVundef
  end.

Definition rorl (v1 v2: ocval): ocval :=
  match v1, v2 with
  | OCVlong n1, OCVint n2 => OCVlong(Int64.ror n1 (Int64.repr (Int.unsigned n2)))
  | _, _ => OCVundef
  end.

Definition rolml (v: ocval) (amount: int) (mask: int64): ocval :=
  match v with
  | OCVlong n => OCVlong(Int64.rolm n (Int64.repr (Int.unsigned amount)) mask)
  | _ => OCVundef
  end.

Definition zero_ext_l (nbits: Z) (v: ocval) : ocval :=
  match v with
  | OCVlong n => OCVlong(Int64.zero_ext nbits n)
  | _ => OCVundef
  end.

Definition sign_ext_l (nbits: Z) (v: ocval) : ocval :=
  match v with
  | OCVlong n => OCVlong(Int64.sign_ext nbits n)
  | _ => OCVundef
  end.

(** Comparisons *)

Section COMPARISONS.

Variable valid_ptr: Z -> bool.
Let weak_valid_ptr (ofs: Z) := valid_ptr ofs || valid_ptr (ofs - 1).

Definition cmp_bool (c: comparison) (v1 v2: ocval): option bool :=
  match v1, v2 with
  | OCVint n1, OCVint n2 => Some (Int.cmp c n1 n2)
  | _, _ => None
  end.

Definition cmp_different_blocks (c: comparison): option bool :=
  match c with
  | Ceq => Some false
  | Cne => Some true
  | _   => None
  end.

Definition cmpu_bool (c: comparison) (v1 v2: ocval): option bool :=
  match v1, v2 with
  | OCVint n1, OCVint n2 =>
      Some (Int.cmpu c n1 n2)
  | OCVint n1, OCVptr ofs2 =>
      if Archi.ptr64 then None else
      if Int.eq n1 Int.zero && weak_valid_ptr (Ptrofs.unsigned (pointer_ofs ofs2))
      then cmp_different_blocks c
      else None
  | OCVptr (stack_ptr ofs1), OCVptr (stack_ptr ofs2) | OCVptr (heap_ptr ofs1), OCVptr (heap_ptr ofs2) =>
      if Archi.ptr64 then None else
        if weak_valid_ptr (Ptrofs.unsigned (ofs1))
           && weak_valid_ptr (Ptrofs.unsigned (ofs2))
        then Some (Ptrofs.cmpu c (ofs1) (ofs2))
        else None
  | OCVptr ofs1, OCVint n2 =>
      if Archi.ptr64 then None else
      if Int.eq n2 Int.zero && weak_valid_ptr (Ptrofs.unsigned (pointer_ofs ofs1))
      then cmp_different_blocks c
      else None
  | _, _ => None
  end.

Definition cmpf_bool (c: comparison) (v1 v2: ocval): option bool :=
  match v1, v2 with
  | OCVfloat f1, OCVfloat f2 => Some (Float.cmp c f1 f2)
  | _, _ => None
  end.

Definition cmpfs_bool (c: comparison) (v1 v2: ocval): option bool :=
  match v1, v2 with
  | OCVsingle f1, OCVsingle f2 => Some (Float32.cmp c f1 f2)
  | _, _ => None
  end.

Definition cmpl_bool (c: comparison) (v1 v2: ocval): option bool :=
  match v1, v2 with
  | OCVlong n1, OCVlong n2 => Some (Int64.cmp c n1 n2)
  | _, _ => None
  end.

Definition cmplu_bool (c: comparison) (v1 v2: ocval): option bool :=
  match v1, v2 with
  | OCVlong n1, OCVlong n2 => Some (Int64.cmpu c n1 n2)
  | OCVlong n1, OCVptr ofs2 =>
      if negb Archi.ptr64 then None else
      if Int64.eq n1 Int64.zero && weak_valid_ptr (Ptrofs.unsigned (pointer_ofs ofs2))
      then cmp_different_blocks c
      else None
  | OCVptr (stack_ptr ofs1), OCVptr (stack_ptr ofs2) | OCVptr (heap_ptr ofs1), OCVptr (heap_ptr ofs2) =>
      if negb Archi.ptr64 then None else
        if weak_valid_ptr (Ptrofs.unsigned (ofs1))
           && weak_valid_ptr (Ptrofs.unsigned (ofs2))
        then Some (Ptrofs.cmpu c (ofs1) (ofs2))
        else None
  | OCVptr ofs1, OCVlong n2 =>
      if negb Archi.ptr64 then None else
      if Int64.eq n2 Int64.zero && weak_valid_ptr (Ptrofs.unsigned (pointer_ofs ofs1))
      then cmp_different_blocks c
      else None
  | _, _ => None
  end.

Definition of_optbool (ob: option bool): ocval :=
  match ob with Some true => OCVtrue | Some false => OCVfalse | None => OCVundef end.

Definition cmp (c: comparison) (v1 v2: ocval): ocval :=
  of_optbool (cmp_bool c v1 v2).

Definition cmpu (c: comparison) (v1 v2: ocval): ocval :=
  of_optbool (cmpu_bool c v1 v2).

Definition cmpf (c: comparison) (v1 v2: ocval): ocval :=
  of_optbool (cmpf_bool c v1 v2).

Definition cmpfs (c: comparison) (v1 v2: ocval): ocval :=
  of_optbool (cmpfs_bool c v1 v2).

Definition cmpl (c: comparison) (v1 v2: ocval): option ocval :=
  option_map of_bool (cmpl_bool c v1 v2).

Definition cmplu (c: comparison) (v1 v2: ocval): option ocval :=
  option_map of_bool (cmplu_bool c v1 v2).

Definition maskzero_bool (v: ocval) (mask: int): option bool :=
  match v with
  | OCVint n => Some (Int.eq (Int.and n mask) Int.zero)
  | _ => None
  end.

End COMPARISONS.

(** Add the given offset to the given pointer or capability. *)
(** The following definition is partial and fails if the capability is
    sealed *)
Definition offset_cap (c: occap) (delta: ptrofs) : option occap :=
  match c with
  | (OCsealable (OCVmem p l b e a)) => Some (OCsealable (OCVmem p l b e (Ptrofs.add a delta)))
  | (OCsealable (OCVseal b e a)) => Some (OCsealable (OCVseal b e (Ptrofs.add a delta)))
  | (OCsealed _ _) => None
  end.
  
Definition offset_ptr (v: ocval) (delta: ptrofs) : option ocval :=
  match v with
  | OCVptr ofs => Some (OCVptr (pointer_arith Ptrofs.add ofs delta))
  | OCVcap (OCsealable (OCVmem p l b e a)) => Some (OCVcap (OCsealable (OCVmem p l b e (Ptrofs.add a delta))))
  | OCVcap (OCsealable (OCVseal b e a)) => Some (OCVcap (OCsealable (OCVseal b e (Ptrofs.add a delta))))
  | OCVcap (OCsealed _ _) => None
  | _ => Some OCVundef
  end.

(** Normalize a value to the given type, turning it into Vundef if it does not
    match the type. *)

Definition normalize (v: ocval) (ty: captyp) : ocval :=
  match v, ty with
  | OCVundef, _ => OCVundef
  | OCVint _, CTint => v
  | OCVlong _, CTlong => v
  | OCVfloat _, CTfloat => v
  | OCVsingle _, CTsingle => v
  | OCVptr _, (CTint | CTany32) => if Archi.ptr64 then OCVundef else v
  | OCVptr _, CTlong => if Archi.ptr64 then v else OCVundef
  | (OCVint _ | OCVsingle _), CTany32 => v
  | (OCVint _ | OCVsingle _ | OCVlong _ | OCVfloat _ | OCVptr _), CTany64 => v
  | OCVcap _, CTcap64 => if Archi.ptr64 then OCVundef else v
  | OCVcap _, CTcap128 => if Archi.ptr64 then v else OCVundef
  | OCVcap _, CTany64 => if Archi.ptr64 then OCVundef else v
  | OCVcap _, CTany128 => v
  | _, CTany128 => v
  | _, _ => OCVundef
  end.

Lemma normalize_type:
  forall v ty, has_type (normalize v ty) ty.
Proof.
  intros; destruct v; simpl.
- auto.
- destruct ty; exact I.
- destruct ty; exact I.
- destruct ty; exact I.
- destruct ty; exact I.
- unfold has_type; destruct ty, Archi.ptr64; auto.
- unfold has_type; destruct ty, Archi.ptr64; auto.
Qed.

Lemma normalize_idem:
  forall v ty, has_type v ty -> normalize v ty = v.
Proof.
  unfold has_type, normalize; intros. destruct v.
- auto.
- destruct ty; intuition auto.
- destruct ty; intuition auto.
- destruct ty; intuition auto.
- destruct ty; intuition auto.
- destruct ty, Archi.ptr64; intuition congruence.
- destruct ty, Archi.ptr64; intuition congruence.
Qed.

(** Select between two values based on the result of a comparison. *)

Definition select (cmp: option bool) (v1 v2: ocval) (ty: captyp) :=
  match cmp with
  | Some b => normalize (if b then v1 else v2) ty
  | None => OCVundef
  end.

(** [load_result] reflects the effect of storing a value with a given
  memory chunk, then reading it back with the same chunk.  Depending
  on the chunk and the type of the value, some normalization occurs.
  For instance, consider storing the integer value [0xFFF] on 1 byte
  at a given address, and reading it back.  If it is read back with
  chunk [Mint8unsigned], zero-extension must be performed, resulting
  in [0xFF].  If it is read back as a [Mint8signed], sign-extension is
  performed and [0xFFFFFFFF] is returned. *)

Definition load_result (chunk: cap_memory_chunk) (v: ocval) :=
  match chunk, v with
  | CMint8signed, OCVint n => OCVint (Int.sign_ext 8 n)
  | CMint8unsigned, OCVint n => OCVint (Int.zero_ext 8 n)
  | CMint16signed, OCVint n => OCVint (Int.sign_ext 16 n)
  | CMint16unsigned, OCVint n => OCVint (Int.zero_ext 16 n)
  | CMint32, OCVint n => OCVint n
  | CMint32, OCVptr ofs => if Archi.ptr64 then OCVundef else OCVptr ofs
  | CMint64, OCVlong n => OCVlong n
  | CMint64, OCVptr ofs => if Archi.ptr64 then OCVptr ofs else OCVundef
  | CMfloat32, OCVsingle f => OCVsingle f
  | CMfloat64, OCVfloat f => OCVfloat f
  | CMany32, (OCVint _ | OCVsingle _) => v
  | CMany32, OCVptr _ => if Archi.ptr64 then OCVundef else v
  | CMany64, (OCVint _ | OCVsingle _ | OCVlong _ | OCVfloat _ | OCVptr _) => v
  | CMcap64, OCVcap _ => if Archi.ptr64 then OCVundef else v
  | CMcap128, OCVcap _ => if Archi.ptr64 then v else OCVundef
  | CMany64, OCVcap _ => if Archi.ptr64 then OCVundef else v
  | CMany128, _ => v
  | _, _ => OCVundef
  end.

Lemma load_result_rettype:
  forall chunk v, has_rettype (load_result chunk v) (rettype_of_chunk chunk).
Proof.
  intros. unfold has_rettype; destruct chunk; destruct v; simpl; auto.
- rewrite Int.sign_ext_idem by omega; auto.
- rewrite Int.zero_ext_idem by omega; auto.
- rewrite Int.sign_ext_idem by omega; auto.
- rewrite Int.zero_ext_idem by omega; auto.
- destruct Archi.ptr64 eqn:SF; simpl; auto.
- destruct Archi.ptr64 eqn:SF; simpl; auto.
- destruct Archi.ptr64 eqn:SF; simpl; auto.
- destruct Archi.ptr64 eqn:SF; simpl; auto.
- destruct Archi.ptr64 eqn:SF; simpl; auto.
- destruct Archi.ptr64 eqn:SF; simpl; auto.
Qed.

Lemma load_result_type:
  forall chunk v, has_type (load_result chunk v) (type_of_chunk chunk).
Proof.
  intros. rewrite <- proj_rettype_of_chunk. apply has_proj_rettype.
  apply load_result_rettype.
Qed.

Lemma load_result_same:
  forall v ty, has_type v ty -> load_result (chunk_of_type ty) v = v.
Proof.
  unfold has_type, load_result; intros.
  destruct v; destruct ty; destruct Archi.ptr64; try contradiction; try discriminate; auto.
Qed.

(** Theorems on arithmetic operations. *)

Theorem cast8unsigned_and:
  forall x, zero_ext 8 x = and x (OCVint(Int.repr 255)).
Proof.
  destruct x; simpl; auto. decEq.
  change 255 with (two_p 8 - 1). apply Int.zero_ext_and. omega.
Qed.

Theorem cast16unsigned_and:
  forall x, zero_ext 16 x = and x (OCVint(Int.repr 65535)).
Proof.
  destruct x; simpl; auto. decEq.
  change 65535 with (two_p 16 - 1). apply Int.zero_ext_and. omega.
Qed.

Theorem bool_of_val_of_bool:
  forall b1 b2, bool_of_val (of_bool b1) b2 -> b1 = b2.
Proof.
  intros. destruct b1; simpl in H; inv H; auto.
Qed.

Theorem bool_of_val_of_optbool:
  forall ob b, bool_of_val (of_optbool ob) b -> ob = Some b.
Proof.
  intros. destruct ob; simpl in H.
  destruct b0; simpl in H; inv H; auto.
  inv H.
Qed.

Theorem notbool_negb_1:
  forall b, of_bool (negb b) = notbool (of_bool b).
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_negb_2:
  forall b, of_bool b = notbool (of_bool (negb b)).
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_negb_3:
  forall ob, of_optbool (option_map negb ob) = notbool (of_optbool ob).
Proof.
  destruct ob; auto. destruct b; auto.
Qed.

Theorem notbool_idem2:
  forall b, notbool(notbool(of_bool b)) = of_bool b.
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_idem3:
  forall x, notbool(notbool(notbool x)) = notbool x.
Proof.
  destruct x; simpl; auto.
  case (Int.eq i Int.zero); reflexivity.
Qed.

Theorem notbool_idem4:
  forall ob, notbool (notbool (of_optbool ob)) = of_optbool ob.
Proof.
  destruct ob; auto. destruct b; auto.
Qed.

Theorem add_commut: forall x y, add x y = add y x.
Proof.
  destruct x; destruct y; simpl; auto.
  decEq. apply Int.add_commut.
Qed.

Theorem add_assoc: forall x y z, add (add x y) z = add x (add y z).
Proof.
  unfold add; intros; destruct Archi.ptr64 eqn:SF, x, y, z; simpl; auto.
- rewrite Int.add_assoc; auto.
- rewrite Int.add_assoc; auto.
- destruct p; simpl; rewrite ! Ptrofs.add_assoc; f_equal; f_equal; f_equal.
  all: rewrite Ptrofs.add_commut; auto with ptrofs.
- destruct p; simpl; rewrite ! Ptrofs.add_assoc; f_equal; f_equal; f_equal.
  all: rewrite Ptrofs.add_commut; auto with ptrofs.
- destruct p; simpl; rewrite ! Ptrofs.add_assoc; f_equal; f_equal; f_equal.
  all: symmetry; auto with ptrofs.
Qed.

Theorem add_permut: forall x y z, add x (add y z) = add y (add x z).
Proof.
  intros. rewrite (add_commut y z). rewrite <- add_assoc. apply add_commut.
Qed.

Theorem add_permut_4:
  forall x y z t, add (add x y) (add z t) = add (add x z) (add y t).
Proof.
  intros. rewrite add_permut. rewrite add_assoc.
  rewrite add_permut. symmetry. apply add_assoc.
Qed.

Theorem neg_zero: neg OCVzero = OCVzero.
Proof.
  reflexivity.
Qed.

Theorem neg_add_distr: forall x y, neg(add x y) = add (neg x) (neg y).
Proof.
  unfold neg, add; intros; destruct Archi.ptr64 eqn:SF, x, y; simpl; auto;
  rewrite Int.neg_add_distr; auto.
Qed.

Theorem sub_zero_r: forall x, sub OCVzero x = neg x.
Proof.
  destruct x; simpl; auto.
Qed.

Theorem sub_add_opp: forall x y, sub x (OCVint y) = add x (OCVint (Int.neg y)).
Proof.
  unfold sub, add; intros; destruct Archi.ptr64 eqn:SF, x; auto.
- rewrite Int.sub_add_opp; auto.
- destruct p; auto.
- simpl; rewrite Int.sub_add_opp; auto.
- destruct p; simpl; rewrite Ptrofs.sub_add_opp; f_equal; f_equal; f_equal.
  all: symmetry; auto with ptrofs.
Qed.

Theorem sub_opp_add: forall x y, sub x (OCVint (Int.neg y)) = add x (OCVint y).
Proof.
  intros. rewrite sub_add_opp. rewrite Int.neg_involutive. auto.
Qed.

Theorem sub_add_l:
  forall v1 v2 i, sub (add v1 (OCVint i)) v2 = add (sub v1 v2) (OCVint i).
Proof.
  unfold sub, add; intros; destruct Archi.ptr64 eqn:SF, v1, v2; auto;
    try (destruct p;simpl;auto); try (destruct p0;simpl;auto).
- rewrite Int.sub_add_l; auto.
- rewrite Int.sub_add_l; auto.
- rewrite Ptrofs.sub_add_l; auto.
- f_equal. rewrite Ptrofs.sub_add_l. auto with ptrofs.
- f_equal. rewrite Ptrofs.sub_add_l. auto with ptrofs.
- f_equal. rewrite Ptrofs.sub_add_l. auto with ptrofs.
Qed.

Theorem sub_add_r:
  forall v1 v2 i, sub v1 (add v2 (OCVint i)) = add (sub v1 v2) (OCVint (Int.neg i)).
Proof.
  unfold sub, add; intros; destruct Archi.ptr64 eqn:SF, v1, v2; auto;
    try (destruct p;simpl;auto); try (destruct p0;simpl;auto).
- rewrite Int.add_commut. rewrite Int.sub_add_r. auto.
- rewrite Int.add_commut. rewrite Int.sub_add_r. auto.
- f_equal. f_equal. replace (Ptrofs.of_int (Int.add i0 i)) with (Ptrofs.add (Ptrofs.of_int i) (Ptrofs.of_int i0)).
  rewrite Ptrofs.sub_add_r. f_equal.
  symmetry. auto with ptrofs.
  symmetry. rewrite Int.add_commut. auto with ptrofs.
- f_equal. f_equal. replace (Ptrofs.of_int (Int.add i0 i)) with (Ptrofs.add (Ptrofs.of_int i) (Ptrofs.of_int i0)).
  rewrite Ptrofs.sub_add_r. f_equal.
  symmetry. auto with ptrofs.
  symmetry. rewrite Int.add_commut. auto with ptrofs.
- f_equal. f_equal. rewrite Ptrofs.add_commut. rewrite Ptrofs.sub_add_r. auto with ptrofs.
- f_equal. f_equal. rewrite Ptrofs.add_commut. rewrite Ptrofs.sub_add_r. auto with ptrofs.
Qed.

Theorem mul_commut: forall x y, mul x y = mul y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.mul_commut.
Qed.

Theorem mul_assoc: forall x y z, mul (mul x y) z = mul x (mul y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.mul_assoc.
Qed.

Theorem mul_add_distr_l:
  forall x y z, mul (add x y) z = add (mul x z) (mul y z).
Proof.
  unfold mul, add; intros; destruct Archi.ptr64 eqn:SF, x, y, z; simpl; auto;
  rewrite Int.mul_add_distr_l; auto.
Qed.

Theorem mul_add_distr_r:
  forall x y z, mul x (add y z) = add (mul x y) (mul x z).
Proof.
  unfold mul, add; intros; destruct Archi.ptr64 eqn:SF, x, y, z; simpl; auto;
  rewrite Int.mul_add_distr_r; auto.
Qed.

Theorem mul_pow2:
  forall x n logn,
  Int.is_power2 n = Some logn ->
  mul x (OCVint n) = shl x (OCVint logn).
Proof.
  intros; destruct x; simpl; auto.
  change 32 with Int.zwordsize.
  rewrite (Int.is_power2_range _ _ H). decEq. apply Int.mul_pow2. auto.
Qed.

Theorem mods_divs:
  forall x y z,
  mods x y = Some z -> exists v, divs x y = Some v /\ z = sub x (mul v y).
Proof.
  intros. destruct x; destruct y; simpl in *; try discriminate.
  destruct (Int.eq i0 Int.zero
        || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H.
  exists (OCVint (Int.divs i i0)); split; auto.
  simpl. rewrite Int.mods_divs. auto.
Qed.

Theorem modu_divu:
  forall x y z,
  modu x y = Some z -> exists v, divu x y = Some v /\ z = sub x (mul v y).
Proof.
  intros. destruct x; destruct y; simpl in *; try discriminate.
  destruct (Int.eq i0 Int.zero) eqn:?; inv H.
  exists (OCVint (Int.divu i i0)); split; auto.
  simpl. rewrite Int.modu_divu. auto.
  generalize (Int.eq_spec i0 Int.zero). rewrite Heqb; auto.
Qed.

Theorem modls_divls:
  forall x y z,
  modls x y = Some z -> exists v, divls x y = Some v /\ z = subl x (mull v y).
Proof.
  intros. destruct x; destruct y; simpl in *; try discriminate.
  destruct (Int64.eq i0 Int64.zero
        || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H.
  exists (OCVlong (Int64.divs i i0)); split; auto.
  simpl. rewrite Int64.mods_divs. auto.
Qed.

Theorem modlu_divlu:
  forall x y z,
  modlu x y = Some z -> exists v, divlu x y = Some v /\ z = subl x (mull v y).
Proof.
  intros. destruct x; destruct y; simpl in *; try discriminate.
  destruct (Int64.eq i0 Int64.zero) eqn:?; inv H.
  exists (OCVlong (Int64.divu i i0)); split; auto.
  simpl. rewrite Int64.modu_divu. auto.
  generalize (Int64.eq_spec i0 Int64.zero). rewrite Heqb; auto.
Qed.

Theorem divs_pow2:
  forall x n logn y,
  Int.is_power2 n = Some logn -> Int.ltu logn (Int.repr 31) = true ->
  divs x (OCVint n) = Some y ->
  shrx x (OCVint logn) = Some y.
Proof.
  intros; destruct x; simpl in H1; inv H1.
  destruct (Int.eq n Int.zero
         || Int.eq i (Int.repr Int.min_signed) && Int.eq n Int.mone); inv H3.
  simpl. rewrite H0. decEq. decEq. symmetry. apply Int.divs_pow2. auto.
Qed.

Theorem divs_one:
  forall s , divs (OCVint s) (OCVint Int.one) = Some (OCVint s).
Proof.
   intros.
   unfold divs. rewrite Int.eq_false; try discriminate.
   simpl. rewrite (Int.eq_false Int.one Int.mone); try discriminate.
   rewrite andb_false_intro2; auto. f_equal. f_equal.
   rewrite Int.divs_one; auto. replace Int.zwordsize with 32; auto. omega.
Qed.

Theorem divu_pow2:
  forall x n logn y,
  Int.is_power2 n = Some logn ->
  divu x (OCVint n) = Some y ->
  shru x (OCVint logn) = y.
Proof.
  intros; destruct x; simpl in H0; inv H0.
  destruct (Int.eq n Int.zero); inv H2.
  simpl.
  rewrite (Int.is_power2_range _ _ H).
  decEq. symmetry. apply Int.divu_pow2. auto.
Qed.

Theorem divu_one:
  forall s, divu (OCVint s) (OCVint Int.one) = Some (OCVint s).
Proof.
  intros. simpl. rewrite Int.eq_false; try discriminate.
  f_equal. f_equal. apply Int.divu_one.
Qed.

Theorem modu_pow2:
  forall x n logn y,
  Int.is_power2 n = Some logn ->
  modu x (OCVint n) = Some y ->
  and x (OCVint (Int.sub n Int.one)) = y.
Proof.
  intros; destruct x; simpl in H0; inv H0.
  destruct (Int.eq n Int.zero); inv H2.
  simpl. decEq. symmetry. eapply Int.modu_and; eauto.
Qed.

Theorem and_commut: forall x y, and x y = and y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.and_commut.
Qed.

Theorem and_assoc: forall x y z, and (and x y) z = and x (and y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.and_assoc.
Qed.

Theorem or_commut: forall x y, or x y = or y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.or_commut.
Qed.

Theorem or_assoc: forall x y z, or (or x y) z = or x (or y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.or_assoc.
Qed.

Theorem xor_commut: forall x y, xor x y = xor y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.xor_commut.
Qed.

Theorem xor_assoc: forall x y z, xor (xor x y) z = xor x (xor y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.xor_assoc.
Qed.

Theorem not_xor: forall x, notint x = xor x (OCVint Int.mone).
Proof.
  destruct x; simpl; auto.
Qed.

Theorem shl_mul: forall x y, mul x (shl OCVone y) = shl x y.
Proof.
  destruct x; destruct y; simpl; auto.
  case (Int.ltu i0 Int.iwordsize); auto.
  decEq. symmetry. apply Int.shl_mul.
Qed.

Theorem shl_rolm:
  forall x n,
  Int.ltu n Int.iwordsize = true ->
  shl x (OCVint n) = rolm x n (Int.shl Int.mone n).
Proof.
  intros; destruct x; simpl; auto.
  rewrite H. decEq. apply Int.shl_rolm. exact H.
Qed.

Theorem shll_rolml:
  forall x n,
  Int.ltu n Int64.iwordsize' = true ->
  shll x (OCVint n) = rolml x n (Int64.shl Int64.mone (Int64.repr (Int.unsigned n))).
Proof.
  intros. destruct x; auto. simpl. rewrite H. rewrite <- Int64.shl_rolm. unfold Int64.shl.
  rewrite Int64.int_unsigned_repr. constructor. unfold Int64.ltu. rewrite Int64.int_unsigned_repr.
  apply H.
Qed.

Theorem shru_rolm:
  forall x n,
  Int.ltu n Int.iwordsize = true ->
  shru x (OCVint n) = rolm x (Int.sub Int.iwordsize n) (Int.shru Int.mone n).
Proof.
  intros; destruct x; simpl; auto.
  rewrite H. decEq. apply Int.shru_rolm. exact H.
Qed.

Theorem shrlu_rolml:
  forall x n,
    Int.ltu n Int64.iwordsize' = true ->
    shrlu x (OCVint n) = rolml x (Int.sub Int64.iwordsize' n) (Int64.shru Int64.mone (Int64.repr (Int.unsigned n))).
Proof.
  intros. destruct x; auto. simpl. rewrite H.
  rewrite Int64.int_sub_ltu by apply H. rewrite Int64.repr_unsigned. rewrite <- Int64.shru_rolm. unfold Int64.shru'.  unfold Int64.shru.
  rewrite Int64.unsigned_repr. reflexivity. apply Int64.int_unsigned_range.
  unfold Int64.ltu. rewrite Int64.int_unsigned_repr. auto.
Qed.

Theorem shrx_carry:
  forall x y z,
  shrx x y = Some z ->
  add (shr x y) (shr_carry x y) = z.
Proof.
  intros. destruct x; destruct y; simpl in H; inv H.
  destruct (Int.ltu i0 (Int.repr 31)) eqn:?; inv H1.
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 31)) with 31. intros.
  assert (Int.ltu i0 Int.iwordsize = true).
    unfold Int.ltu. apply zlt_true. change (Int.unsigned Int.iwordsize) with 32. omega.
  simpl. rewrite H0. simpl. decEq. rewrite Int.shrx_carry; auto.
Qed.

Theorem shrx_shr:
  forall x y z,
  shrx x y = Some z ->
  exists p, exists q,
    x = OCVint p /\ y = OCVint q /\
    z = shr (if Int.lt p Int.zero then add x (OCVint (Int.sub (Int.shl Int.one q) Int.one)) else x) (OCVint q).
Proof.
  intros. destruct x; destruct y; simpl in H; inv H.
  destruct (Int.ltu i0 (Int.repr 31)) eqn:?; inv H1.
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 31)) with 31. intros.
  assert (Int.ltu i0 Int.iwordsize = true).
    unfold Int.ltu. apply zlt_true. change (Int.unsigned Int.iwordsize) with 32. omega.
  exists i; exists i0; intuition.
  rewrite Int.shrx_shr; auto. destruct (Int.lt i Int.zero); simpl; rewrite H0; auto.
Qed.

Theorem shrx_shr_2:
  forall n x z,
  shrx x (OCVint n) = Some z ->
  z = (if Int.eq n Int.zero then x else
         shr (add x (shru (shr x (OCVint (Int.repr 31)))
                    (OCVint (Int.sub (Int.repr 32) n))))
             (OCVint n)).
Proof.
  intros. destruct x; simpl in H; try discriminate.
  destruct (Int.ltu n (Int.repr 31)) eqn:LT; inv H.
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 31)) with 31; intros LT'.
  predSpec Int.eq Int.eq_spec n Int.zero.
- subst n. unfold Int.shrx. rewrite Int.shl_zero. unfold Int.divs. change (Int.signed Int.one) with 1.
  rewrite Z.quot_1_r. rewrite Int.repr_signed; auto.
- simpl. change (Int.ltu (Int.repr 31) Int.iwordsize) with true. simpl.
  replace (Int.ltu (Int.sub (Int.repr 32) n) Int.iwordsize) with true. simpl.
  replace (Int.ltu n Int.iwordsize) with true.
  f_equal; apply Int.shrx_shr_2; assumption.
  symmetry; apply zlt_true. change (Int.unsigned n < 32); omega.
  symmetry; apply zlt_true. unfold Int.sub. change (Int.unsigned (Int.repr 32)) with 32.
  assert (Int.unsigned n <> 0). { red; intros; elim H. rewrite <- (Int.repr_unsigned n), H0. auto. }
  rewrite Int.unsigned_repr.
  change (Int.unsigned Int.iwordsize) with 32; omega.
  assert (32 < Int.max_unsigned) by reflexivity. omega.
Qed.

Theorem or_rolm:
  forall x n m1 m2,
  or (rolm x n m1) (rolm x n m2) = rolm x n (Int.or m1 m2).
Proof.
  intros; destruct x; simpl; auto.
  decEq. apply Int.or_rolm.
Qed.

Theorem rolm_rolm:
  forall x n1 m1 n2 m2,
  rolm (rolm x n1 m1) n2 m2 =
    rolm x (Int.modu (Int.add n1 n2) Int.iwordsize)
           (Int.and (Int.rol m1 n2) m2).
Proof.
  intros; destruct x; simpl; auto.
  decEq.
  apply Int.rolm_rolm. apply int_wordsize_divides_modulus.
Qed.

Theorem rolm_zero:
  forall x m,
  rolm x Int.zero m = and x (OCVint m).
Proof.
  intros; destruct x; simpl; auto. decEq. apply Int.rolm_zero.
Qed.

Theorem addl_commut: forall x y, addl x y = addl y x.
Proof.
  destruct x; destruct y; simpl; auto.
  decEq. apply Int64.add_commut.
Qed.

Theorem addl_assoc: forall x y z, addl (addl x y) z = addl x (addl y z).
Proof.
  unfold addl; intros; destruct Archi.ptr64 eqn:SF, x, y, z; simpl; auto;
    try (destruct p;simpl;auto); try (destruct p0;simpl;auto).
- rewrite Int64.add_assoc; auto.
- rewrite ! Ptrofs.add_assoc. f_equal. f_equal. f_equal.
  rewrite Ptrofs.add_commut. auto with ptrofs.
- rewrite ! Ptrofs.add_assoc. f_equal. f_equal. f_equal.
  rewrite Ptrofs.add_commut. auto with ptrofs.
- rewrite ! Ptrofs.add_assoc. f_equal. f_equal. f_equal.
  apply Ptrofs.add_commut.
- rewrite ! Ptrofs.add_assoc. f_equal. f_equal. f_equal.
  rewrite Ptrofs.add_commut. auto with ptrofs.
- rewrite ! Ptrofs.add_assoc. f_equal. f_equal. f_equal.
  symmetry. auto with ptrofs.
- rewrite ! Ptrofs.add_assoc. f_equal. f_equal. f_equal.
  symmetry. auto with ptrofs.
- rewrite Int64.add_assoc; auto.
Qed.

Theorem addl_permut: forall x y z, addl x (addl y z) = addl y (addl x z).
Proof.
  intros. rewrite (addl_commut y z). rewrite <- addl_assoc. apply addl_commut.
Qed.

Theorem addl_permut_4:
  forall x y z t, addl (addl x y) (addl z t) = addl (addl x z) (addl y t).
Proof.
  intros. rewrite addl_permut. rewrite addl_assoc.
  rewrite addl_permut. symmetry. apply addl_assoc.
Qed.

Theorem negl_addl_distr: forall x y, negl(addl x y) = addl (negl x) (negl y).
Proof.
  unfold negl, addl; intros; destruct Archi.ptr64 eqn:SF; destruct x; destruct y; simpl; auto;
  decEq; apply Int64.neg_add_distr.
Qed.

Theorem subl_addl_opp: forall x y, subl x (OCVlong y) = addl x (OCVlong (Int64.neg y)).
Proof.
  unfold subl, addl; intros; destruct Archi.ptr64 eqn:SF, x; auto;
    try (destruct p;simpl;auto); try (destruct p0;simpl;auto).
- rewrite Int64.sub_add_opp; auto.
- rewrite Ptrofs.sub_add_opp. f_equal. f_equal. f_equal. symmetry. auto with ptrofs.
- rewrite Ptrofs.sub_add_opp. f_equal. f_equal. f_equal. symmetry. auto with ptrofs.
- rewrite Int64.sub_add_opp; auto.
Qed.

Theorem subl_opp_addl: forall x y, subl x (OCVlong (Int64.neg y)) = addl x (OCVlong y).
Proof.
  intros. rewrite subl_addl_opp. rewrite Int64.neg_involutive. auto.
Qed.

Theorem subl_addl_l:
  forall v1 v2 i, subl (addl v1 (OCVlong i)) v2 = addl (subl v1 v2) (OCVlong i).
Proof.
  unfold subl, addl; intros; destruct Archi.ptr64 eqn:SF, v1, v2; auto;
    try (destruct p;simpl;auto); try (destruct p0;simpl;auto).
- rewrite Int64.sub_add_l; auto.
- rewrite Ptrofs.sub_add_l; auto.
- rewrite Ptrofs.sub_add_l; auto.
- simpl. f_equal. rewrite Ptrofs.sub_add_l. auto with ptrofs.
- simpl. f_equal. rewrite Ptrofs.sub_add_l. auto with ptrofs.
- rewrite Int64.sub_add_l; auto.
Qed.

Theorem subl_addl_r:
  forall v1 v2 i, subl v1 (addl v2 (OCVlong i)) = addl (subl v1 v2) (OCVlong (Int64.neg i)).
Proof.
  unfold subl, addl; intros; destruct Archi.ptr64 eqn:SF, v1, v2; auto;
    try (destruct p;simpl;auto); try (destruct p0;simpl;auto).
- rewrite Int64.add_commut. rewrite Int64.sub_add_r. auto.
- f_equal. replace (Ptrofs.of_int64 (Int64.add i0 i)) with (Ptrofs.add (Ptrofs.of_int64 i) (Ptrofs.of_int64 i0)).
  rewrite Ptrofs.sub_add_r. f_equal. f_equal.
  symmetry. auto with ptrofs.
  symmetry. rewrite Int64.add_commut. auto with ptrofs.
- f_equal. replace (Ptrofs.of_int64 (Int64.add i0 i)) with (Ptrofs.add (Ptrofs.of_int64 i) (Ptrofs.of_int64 i0)).
  rewrite Ptrofs.sub_add_r. f_equal. f_equal.
  symmetry. auto with ptrofs.
  symmetry. rewrite Int64.add_commut. auto with ptrofs.
- simpl; f_equal. f_equal. rewrite Ptrofs.add_commut. rewrite Ptrofs.sub_add_r. auto with ptrofs.
- simpl; f_equal. f_equal. rewrite Ptrofs.add_commut. rewrite Ptrofs.sub_add_r. auto with ptrofs.
- rewrite Int64.add_commut. rewrite Int64.sub_add_r. auto.
Qed.

Theorem mull_commut: forall x y, mull x y = mull y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int64.mul_commut.
Qed.

Theorem mull_assoc: forall x y z, mull (mull x y) z = mull x (mull y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int64.mul_assoc.
Qed.

Theorem mull_addl_distr_l:
  forall x y z, mull (addl x y) z = addl (mull x z) (mull y z).
Proof.
  unfold mull, addl; intros; destruct Archi.ptr64 eqn:SF; destruct x; destruct y; destruct z; simpl; auto;
  decEq; apply Int64.mul_add_distr_l.
Qed.

Theorem mull_addl_distr_r:
  forall x y z, mull x (addl y z) = addl (mull x y) (mull x z).
Proof.
  unfold mull, addl; intros; destruct Archi.ptr64 eqn:SF; destruct x; destruct y; destruct z; simpl; auto;
  decEq; apply Int64.mul_add_distr_r.
Qed.

Theorem andl_commut: forall x y, andl x y = andl y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int64.and_commut.
Qed.

Theorem andl_assoc: forall x y z, andl (andl x y) z = andl x (andl y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int64.and_assoc.
Qed.

Theorem orl_commut: forall x y, orl x y = orl y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int64.or_commut.
Qed.

Theorem orl_assoc: forall x y z, orl (orl x y) z = orl x (orl y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int64.or_assoc.
Qed.

Theorem xorl_commut: forall x y, xorl x y = xorl y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int64.xor_commut.
Qed.

Theorem xorl_assoc: forall x y z, xorl (xorl x y) z = xorl x (xorl y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int64.xor_assoc.
Qed.

Theorem notl_xorl: forall x, notl x = xorl x (OCVlong Int64.mone).
Proof.
  destruct x; simpl; auto.
Qed.

Theorem divls_pow2:
  forall x n logn y,
  Int64.is_power2' n = Some logn -> Int.ltu logn (Int.repr 63) = true ->
  divls x (OCVlong n) = Some y ->
  shrxl x (OCVint logn) = Some y.
Proof.
  intros; destruct x; simpl in H1; inv H1.
  destruct (Int64.eq n Int64.zero
         || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq n Int64.mone); inv H3.
  simpl. rewrite H0. decEq. decEq.
  generalize (Int64.is_power2'_correct _ _ H); intro.
  unfold Int64.shrx'. rewrite Int64.shl'_mul_two_p. rewrite <- H1.
  rewrite Int64.mul_commut. rewrite Int64.mul_one.
  rewrite Int64.repr_unsigned. auto.
Qed.

Theorem divls_one:
  forall n, divls (OCVlong n) (OCVlong Int64.one) = Some (OCVlong n).
Proof.
  intros. unfold divls. rewrite Int64.eq_false; try discriminate.
  rewrite (Int64.eq_false Int64.one Int64.mone); try discriminate.
  rewrite andb_false_intro2; auto.
  simpl. f_equal. f_equal. apply Int64.divs_one.
  replace Int64.zwordsize with 64; auto. omega.
Qed.

Theorem divlu_pow2:
  forall x n logn y,
  Int64.is_power2' n = Some logn ->
  divlu x (OCVlong n) = Some y ->
  shrlu x (OCVint logn) = y.
Proof.
  intros; destruct x; simpl in H0; inv H0.
  destruct (Int64.eq n Int64.zero); inv H2.
  simpl.
  rewrite (Int64.is_power2'_range _ _ H).
  decEq. symmetry. apply Int64.divu_pow2'. auto.
Qed.

Theorem divlu_one:
  forall n, divlu (OCVlong n) (OCVlong Int64.one) = Some (OCVlong n).
Proof.
  intros. unfold divlu. rewrite Int64.eq_false; try discriminate.
  simpl. f_equal. f_equal. apply Int64.divu_one.
Qed.

Theorem modlu_pow2:
  forall x n logn y,
  Int64.is_power2 n = Some logn ->
  modlu x (OCVlong n) = Some y ->
  andl x (OCVlong (Int64.sub n Int64.one)) = y.
Proof.
  intros; destruct x; simpl in H0; inv H0.
  destruct (Int64.eq n Int64.zero); inv H2.
  simpl. decEq. symmetry. eapply Int64.modu_and; eauto.
Qed.

Theorem shrxl_carry:
  forall x y z,
  shrxl x y = Some z ->
  addl (shrl x y) (shrl_carry x y) = z.
Proof.
  intros. destruct x; destruct y; simpl in H; inv H.
  destruct (Int.ltu i0 (Int.repr 63)) eqn:?; inv H1.
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 63)) with 63. intros.
  assert (Int.ltu i0 Int64.iwordsize' = true).
    unfold Int.ltu. apply zlt_true. change (Int.unsigned Int64.iwordsize') with 64. omega.
  simpl. rewrite H0. simpl. decEq. rewrite Int64.shrx'_carry; auto.
Qed.

Theorem shrxl_shrl_2:
  forall n x z,
  shrxl x (OCVint n) = Some z ->
  z = (if Int.eq n Int.zero then x else
         shrl (addl x (shrlu (shrl x (OCVint (Int.repr 63)))
                      (OCVint (Int.sub (Int.repr 64) n))))
              (OCVint n)).
Proof.
  intros. destruct x; simpl in H; try discriminate.
  destruct (Int.ltu n (Int.repr 63)) eqn:LT; inv H.
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 63)) with 63; intros LT'.
  predSpec Int.eq Int.eq_spec n Int.zero.
- subst n. rewrite Int64.shrx'_zero. auto.
- simpl. change (Int.ltu (Int.repr 63) Int64.iwordsize') with true.  simpl.
  replace (Int.ltu (Int.sub (Int.repr 64) n) Int64.iwordsize') with true. simpl.
  replace (Int.ltu n Int64.iwordsize') with true.
  f_equal; apply Int64.shrx'_shr_2; assumption.
  symmetry; apply zlt_true. change (Int.unsigned n < 64); omega.
  symmetry; apply zlt_true. unfold Int.sub. change (Int.unsigned (Int.repr 64)) with 64.
  assert (Int.unsigned n <> 0). { red; intros; elim H. rewrite <- (Int.repr_unsigned n), H0. auto. }
  rewrite Int.unsigned_repr.
  change (Int.unsigned Int64.iwordsize') with 64; omega.
  assert (64 < Int.max_unsigned) by reflexivity. omega.
Qed.

Theorem negate_cmp_bool:
  forall c x y, cmp_bool (negate_comparison c) x y = option_map negb (cmp_bool c x y).
Proof.
  destruct x; destruct y; simpl; auto. rewrite Int.negate_cmp. auto.
Qed.

Theorem negate_cmpu_bool:
  forall valid_ptr c x y,
  cmpu_bool valid_ptr (negate_comparison c) x y = option_map negb (cmpu_bool valid_ptr c x y).
Proof.
  assert (forall c,
    cmp_different_blocks (negate_comparison c) = option_map negb (cmp_different_blocks c)).
  { destruct c; auto. }
  unfold cmpu_bool; intros; destruct Archi.ptr64 eqn:SF, x, y; auto;
    try (destruct p;simpl;auto); try (destruct p0;simpl;auto).
- rewrite Int.negate_cmpu;auto.
- rewrite Int.negate_cmpu;auto.
- destruct (Int.eq i Int.zero && (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1))); auto.
- destruct (Int.eq i Int.zero && (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1))); auto.
- destruct (Int.eq i Int.zero && (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1))); auto.
- destruct (Int.eq i Int.zero && (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1))); auto.
- destruct ((valid_ptr (Ptrofs.unsigned i) || valid_ptr (Ptrofs.unsigned i - 1)) &&
            (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1))).
  rewrite Ptrofs.negate_cmpu. auto.
  destruct (valid_ptr (Ptrofs.unsigned i) && valid_ptr (Ptrofs.unsigned i0)); auto.
- destruct ((valid_ptr (Ptrofs.unsigned i) || valid_ptr (Ptrofs.unsigned i - 1)) &&
            (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1))).
  rewrite Ptrofs.negate_cmpu. auto.
  destruct (valid_ptr (Ptrofs.unsigned i) && valid_ptr (Ptrofs.unsigned i0)); auto.
Qed.

Theorem negate_cmpl_bool:
  forall c x y, cmpl_bool (negate_comparison c) x y = option_map negb (cmpl_bool c x y).
Proof.
  destruct x; destruct y; simpl; auto. rewrite Int64.negate_cmp. auto.
Qed.

Theorem negate_cmplu_bool:
  forall valid_ptr c x y,
  cmplu_bool valid_ptr (negate_comparison c) x y = option_map negb (cmplu_bool valid_ptr c x y).
Proof.
  assert (forall c,
    cmp_different_blocks (negate_comparison c) = option_map negb (cmp_different_blocks c)).
  { destruct c; auto. }
  unfold cmplu_bool; intros; destruct Archi.ptr64 eqn:SF, x, y; auto;
    try (destruct p;simpl;auto); try (destruct p0;simpl;auto).
  all: try (simpl; destruct (Int64.eq i Int64.zero && (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1))); auto).
- rewrite Int64.negate_cmpu. auto.
- simpl.
  destruct ((valid_ptr (Ptrofs.unsigned i) || valid_ptr (Ptrofs.unsigned i - 1)) &&
            (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1))).
  rewrite Ptrofs.negate_cmpu. auto.
  destruct (valid_ptr (Ptrofs.unsigned i) && valid_ptr (Ptrofs.unsigned i0)); auto.
- simpl.
  destruct ((valid_ptr (Ptrofs.unsigned i) || valid_ptr (Ptrofs.unsigned i - 1)) &&
            (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1))).
  rewrite Ptrofs.negate_cmpu. auto.
  destruct (valid_ptr (Ptrofs.unsigned i) && valid_ptr (Ptrofs.unsigned i0)); auto.
- rewrite Int64.negate_cmpu. auto.
Qed.

Lemma not_of_optbool:
  forall ob, of_optbool (option_map negb ob) = notbool (of_optbool ob).
Proof.
  destruct ob; auto. destruct b; auto.
Qed.

Theorem negate_cmp:
  forall c x y,
  cmp (negate_comparison c) x y = notbool (cmp c x y).
Proof.
  intros. unfold cmp. rewrite negate_cmp_bool. apply not_of_optbool.
Qed.

Theorem negate_cmpu:
  forall valid_ptr c x y,
  cmpu valid_ptr (negate_comparison c) x y =
    notbool (cmpu valid_ptr c x y).
Proof.
  intros. unfold cmpu. rewrite negate_cmpu_bool. apply not_of_optbool.
Qed.

Theorem swap_cmp_bool:
  forall c x y,
  cmp_bool (swap_comparison c) x y = cmp_bool c y x.
Proof.
  destruct x; destruct y; simpl; auto. rewrite Int.swap_cmp. auto.
Qed.

Theorem swap_cmpu_bool:
  forall valid_ptr c x y,
  cmpu_bool valid_ptr (swap_comparison c) x y =
    cmpu_bool valid_ptr c y x.
Proof.
  assert (E: forall c, cmp_different_blocks (swap_comparison c) = cmp_different_blocks c).
  { destruct c; auto. }
  intros; unfold cmpu_bool. rewrite ! E. destruct Archi.ptr64 eqn:SF, x, y; auto;
  try (destruct p;simpl;auto); try (destruct p0;simpl;auto); try (rewrite Int.swap_cmpu;auto).
  all: subst.
  all: destruct (valid_ptr (Ptrofs.unsigned i) || valid_ptr (Ptrofs.unsigned i - 1));
  destruct (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1));
  simpl; auto.
  all: try rewrite Ptrofs.swap_cmpu; auto.
  all:destruct (valid_ptr (Ptrofs.unsigned i));
    destruct (valid_ptr (Ptrofs.unsigned i0)); simpl; auto.
Qed.

Theorem swap_cmpl_bool:
  forall c x y,
  cmpl_bool (swap_comparison c) x y = cmpl_bool c y x.
Proof.
  destruct x; destruct y; simpl; auto. rewrite Int64.swap_cmp. auto.
Qed.

Theorem swap_cmplu_bool:
  forall valid_ptr c x y,
  cmplu_bool valid_ptr (swap_comparison c) x y = cmplu_bool valid_ptr c y x.
Proof.
  assert (E: forall c, cmp_different_blocks (swap_comparison c) = cmp_different_blocks c).
  { destruct c; auto. }
  intros; unfold cmplu_bool. rewrite ! E. destruct Archi.ptr64 eqn:SF, x, y; auto;
  try (destruct p;simpl;auto);try (destruct p0;simpl;auto).
all: try rewrite Int64.swap_cmpu; auto.
all: destruct (valid_ptr (Ptrofs.unsigned i) || valid_ptr (Ptrofs.unsigned i - 1));
  destruct (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1));
  simpl; auto.
all: try rewrite Ptrofs.swap_cmpu; auto.
all: destruct (valid_ptr (Ptrofs.unsigned i));
    destruct (valid_ptr (Ptrofs.unsigned i0)); simpl; auto.
Qed.

Theorem negate_cmpf_eq:
  forall v1 v2, notbool (cmpf Cne v1 v2) = cmpf Ceq v1 v2.
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool.
  rewrite Float.cmp_ne_eq. destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem negate_cmpf_ne:
  forall v1 v2, notbool (cmpf Ceq v1 v2) = cmpf Cne v1 v2.
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool.
  rewrite Float.cmp_ne_eq. destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem cmpf_le:
  forall v1 v2, cmpf Cle v1 v2 = or (cmpf Clt v1 v2) (cmpf Ceq v1 v2).
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool.
  rewrite Float.cmp_le_lt_eq.
  destruct (Float.cmp Clt f f0); destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem cmpf_ge:
  forall v1 v2, cmpf Cge v1 v2 = or (cmpf Cgt v1 v2) (cmpf Ceq v1 v2).
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool.
  rewrite Float.cmp_ge_gt_eq.
  destruct (Float.cmp Cgt f f0); destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem cmp_ne_0_optbool:
  forall ob, cmp Cne (of_optbool ob) (OCVint Int.zero) = of_optbool ob.
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto.
Qed.

Theorem cmp_eq_1_optbool:
  forall ob, cmp Ceq (of_optbool ob) (OCVint Int.one) = of_optbool ob.
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto.
Qed.

Theorem cmp_eq_0_optbool:
  forall ob, cmp Ceq (of_optbool ob) (OCVint Int.zero) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto.
Qed.

Theorem cmp_ne_1_optbool:
  forall ob, cmp Cne (of_optbool ob) (OCVint Int.one) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto.
Qed.

Theorem cmpu_ne_0_optbool:
  forall valid_ptr ob,
  cmpu valid_ptr Cne (of_optbool ob) (OCVint Int.zero) = of_optbool ob.
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto.
Qed.

Theorem cmpu_eq_1_optbool:
  forall valid_ptr ob,
  cmpu valid_ptr Ceq (of_optbool ob) (OCVint Int.one) = of_optbool ob.
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto.
Qed.

Theorem cmpu_eq_0_optbool:
  forall valid_ptr ob,
  cmpu valid_ptr Ceq (of_optbool ob) (OCVint Int.zero) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto.
Qed.

Theorem cmpu_ne_1_optbool:
  forall valid_ptr ob,
  cmpu valid_ptr Cne (of_optbool ob) (OCVint Int.one) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto.
Qed.

Lemma zero_ext_and:
  forall n v,
  0 <= n ->
  Val.zero_ext n v = Val.and v (OCVint (Int.repr (two_p n - 1))).
Proof.
  intros. destruct v; simpl; auto. decEq. apply Int.zero_ext_and; auto.
Qed.

Lemma zero_ext_andl:
  forall n v,
  0 <= n ->
  Val.zero_ext_l n v = Val.andl v (OCVlong (Int64.repr (two_p n - 1))).
Proof.
  intros. destruct v; simpl; auto. decEq. apply Int64.zero_ext_and; auto.
Qed.

Lemma rolm_lt_zero:
  forall v, rolm v Int.one Int.one = cmp Clt v (OCVint Int.zero).
Proof.
  intros. unfold cmp, cmp_bool; destruct v; simpl; auto.
  transitivity (OCVint (Int.shru i (Int.repr (Int.zwordsize - 1)))).
  decEq. symmetry. rewrite Int.shru_rolm. auto. auto.
  rewrite Int.shru_lt_zero. destruct (Int.lt i Int.zero); auto.
Qed.

Lemma rolm_ge_zero:
  forall v,
  xor (rolm v Int.one Int.one) (OCVint Int.one) = cmp Cge v (OCVint Int.zero).
Proof.
  intros. rewrite rolm_lt_zero. destruct v; simpl; auto.
  unfold cmp; simpl. destruct (Int.lt i Int.zero); auto.
Qed.

(** The ``is less defined'' relation between values.
    A value is less defined than itself, and [OCVundef] is
    less defined than any value. *)

(*TODO: disallow capabilities from beinf lessdef*)
Inductive lessdef: ocval -> ocval -> Prop :=
| lessdef_refl: forall v, lessdef v v
| lessdef_undef_int: forall v, lessdef OCVundef (OCVint v)
| lessdef_undef_long: forall v, lessdef OCVundef (OCVlong v)
| lessdef_undef_float: forall v, lessdef OCVundef (OCVfloat v)
| lessdef_undef_single: forall v, lessdef OCVundef (OCVsingle v)
| lessdef_undef_ptr: forall v, lessdef OCVundef (OCVptr v).

Lemma lessdef_same:
  forall v1 v2, v1 = v2 -> lessdef v1 v2.
Proof.
  intros. subst v2. constructor.
Qed.

Lemma lessdef_trans:
  forall v1 v2 v3, lessdef v1 v2 -> lessdef v2 v3 -> lessdef v1 v3.
Proof.
  intros. inv H; inv H0; auto; constructor.
Qed.

Inductive lessdef_list: list ocval -> list ocval -> Prop :=
  | lessdef_list_nil:
      lessdef_list nil nil
  | lessdef_list_cons:
      forall v1 v2 vl1 vl2,
      lessdef v1 v2 -> lessdef_list vl1 vl2 ->
      lessdef_list (v1 :: vl1) (v2 :: vl2).

Hint Resolve lessdef_refl
     lessdef_undef_int
     lessdef_undef_long
     lessdef_undef_float
     lessdef_undef_single
     lessdef_undef_ptr
     lessdef_list_nil
     lessdef_list_cons : core.


Lemma lessdef_list_not_ptr: forall vl vl',
    lessdef_list vl vl' ->
    Forall not_ptr vl ->
    Forall not_ptr vl'.
Proof.
  induction vl; intros.
  - inv H. eauto.
  - inv H. inv H0.
    constructor.
    + inv H3; auto; inv H2.
    + eauto.
Qed.

Lemma lessdef_list_inv:
  forall vl1 vl2, lessdef_list vl1 vl2 -> vl1 = vl2 \/ In OCVundef vl1.
Proof.
  induction 1; simpl.
  tauto.
  inv H; destruct IHlessdef_list.
  left; congruence.
  all: tauto.
Qed.

Lemma lessdef_list_trans:
  forall vl1 vl2, lessdef_list vl1 vl2 -> forall vl3, lessdef_list vl2 vl3 -> lessdef_list vl1 vl3.
Proof.
  induction 1; intros vl3 LD; inv LD; constructor; eauto using lessdef_trans.
Qed.

(** Compatibility of operations with the [lessdef] relation. *)

Lemma load_result_lessdef:
  forall chunk v1 v2,
  lessdef v1 v2 -> lessdef (load_result chunk v1) (load_result chunk v2).
Proof.
  intros. inv H; auto;  destruct chunk; simpl; auto.
  all: destruct Archi.ptr64;auto.
Qed.

Lemma zero_ext_lessdef:
  forall n v1 v2, lessdef v1 v2 -> lessdef (zero_ext n v1) (zero_ext n v2).
Proof.
  intros; inv H; simpl; auto.
Qed.

Lemma sign_ext_lessdef:
  forall n v1 v2, lessdef v1 v2 -> lessdef (sign_ext n v1) (sign_ext n v2).
Proof.
  intros; inv H; simpl; auto.
Qed.

Lemma singleoffloat_lessdef:
  forall v1 v2, lessdef v1 v2 -> lessdef (singleoffloat v1) (singleoffloat v2).
Proof.
  intros; inv H; simpl; auto.
Qed.

Lemma add_lessdef:
  forall v1 v1' v2 v2',
  lessdef v1 v1' -> lessdef v2 v2' -> lessdef (add v1 v2) (add v1' v2').
Proof.
  intros. inv H; inv H0; auto.
  all: try destruct v1'; simpl; auto.
  all: destruct Archi.ptr64; simpl;auto.
  all: destruct v2';auto.
Qed.

Lemma addl_lessdef:
  forall v1 v1' v2 v2',
  lessdef v1 v1' -> lessdef v2 v2' -> lessdef (addl v1 v2) (addl v1' v2').
Proof.
  intros. inv H; inv H0; auto.
  all: try destruct v1'; simpl; auto.
  all: destruct Archi.ptr64; simpl;auto.
  all: destruct v2';auto.
Qed.

Lemma cmpu_bool_lessdef:
  forall valid_ptr valid_ptr' c v1 v1' v2 v2' b,
  (forall ofs, valid_ptr ofs = true -> valid_ptr' ofs = true) ->
  lessdef v1 v1' -> lessdef v2 v2' ->
  cmpu_bool valid_ptr c v1 v2 = Some b ->
  cmpu_bool valid_ptr' c v1' v2' = Some b.
Proof.
  intros.
  assert (X: forall ofs,
             valid_ptr ofs || valid_ptr (ofs - 1) = true ->
             valid_ptr' ofs || valid_ptr' (ofs - 1) = true).
  { intros. apply orb_true_intro. destruct (orb_prop _ _ H3).
    rewrite (H ofs); auto.
    rewrite (H (ofs - 1)); auto. }
  inv H0; [ | discriminate..].
  inv H1;auto.
  2,3: destruct v1'; try destruct p; discriminate.
  unfold cmpu_bool in *; remember Archi.ptr64 as ptr64;
  destruct v1'; auto; destruct v2'; auto; destruct ptr64; auto;
  try (destruct p;simpl;auto); try (destruct p0;simpl;auto).
  - destruct (Int.eq i Int.zero); auto. simpl in *.
    destruct (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1)) eqn:A; inv H2.
    rewrite X; simpl; auto.
  - destruct (Int.eq i Int.zero); auto. simpl in *.
    destruct (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1)) eqn:A; inv H2.
    rewrite X; simpl; auto.
  - destruct (Int.eq i Int.zero); auto. simpl in *.
    destruct (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1)) eqn:A; inv H2.
    rewrite X; simpl; auto.
  - destruct (Int.eq i Int.zero); auto. simpl in *.
    destruct (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1)) eqn:A; inv H2.
    rewrite X; simpl; auto.
  - destruct (valid_ptr (Ptrofs.unsigned i) || valid_ptr (Ptrofs.unsigned i - 1)) eqn:A; inv H2.
    destruct (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1)) eqn:B; inv H1.
    rewrite ! X;simpl;auto.
  - destruct (valid_ptr (Ptrofs.unsigned i) || valid_ptr (Ptrofs.unsigned i - 1)) eqn:A; inv H2.
    destruct (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1)) eqn:B; inv H1.
    rewrite ! X;simpl;auto.
Qed.

Lemma cmplu_bool_lessdef:
  forall valid_ptr valid_ptr' c v1 v1' v2 v2' b,
  (forall ofs, valid_ptr ofs = true -> valid_ptr' ofs = true) ->
  lessdef v1 v1' -> lessdef v2 v2' ->
  cmplu_bool valid_ptr c v1 v2 = Some b ->
  cmplu_bool valid_ptr' c v1' v2' = Some b.
Proof.
  intros.
  assert (X: forall ofs,
             valid_ptr ofs || valid_ptr (ofs - 1) = true ->
             valid_ptr' ofs || valid_ptr' (ofs - 1) = true).
  { intros. apply orb_true_intro. destruct (orb_prop _ _ H3).
    rewrite (H ofs); auto.
    rewrite (H (ofs - 1)); auto. }
  inv H0; [ | discriminate..].
  inv H1;auto; [ | destruct v1'; try destruct p; discriminate .. ].
  unfold cmplu_bool in *. remember Archi.ptr64 as ptr64.
  destruct v1'; auto; destruct v2'; auto; destruct ptr64; auto;
    try (destruct p;auto); try destruct p0;auto; simpl in *.
- destruct (Int64.eq i Int64.zero); auto.
  destruct (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1)) eqn:A; inv H2.
  rewrite X; auto.
- destruct (Int64.eq i Int64.zero); auto.
  destruct (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1)) eqn:A; inv H2.
  rewrite X; auto.
- destruct (Int64.eq i Int64.zero); auto.
  destruct (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1)) eqn:A; inv H2.
  rewrite X; auto.
- destruct (Int64.eq i Int64.zero); auto.
  destruct (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1)) eqn:A; inv H2.
  rewrite X; auto.
- destruct (valid_ptr (Ptrofs.unsigned i) || valid_ptr (Ptrofs.unsigned i - 1)) eqn:A; inv H2.
  destruct (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1)) eqn:B; inv H1.
  rewrite ! X; auto.
- destruct (valid_ptr (Ptrofs.unsigned i) || valid_ptr (Ptrofs.unsigned i - 1)) eqn:A; inv H2.
  destruct (valid_ptr (Ptrofs.unsigned i0) || valid_ptr (Ptrofs.unsigned i0 - 1)) eqn:B; inv H1.
  rewrite ! X; auto.
Qed.

Lemma of_optbool_lessdef:
  forall ob ob',
  (forall b, ob = Some b -> ob' = Some b) ->
  lessdef (of_optbool ob) (of_optbool ob').
Proof.
  intros. destruct ob; simpl; auto. rewrite (H b); auto.
  destruct ob'; auto; destruct b; simpl; [unfold OCVtrue|unfold OCVfalse];auto.
Qed.

Lemma longofwords_lessdef:
  forall v1 v2 v1' v2',
  lessdef v1 v1' -> lessdef v2 v2' -> lessdef (longofwords v1 v2) (longofwords v1' v2').
Proof.
  intros. unfold longofwords. inv H; auto. inv H0; auto. destruct v1'; auto.
  destruct v2';auto.
Qed.

Lemma loword_lessdef:
  forall v v', lessdef v v' -> lessdef (loword v) (loword v').
Proof.
  intros. inv H; auto. constructor.
Qed.

Lemma hiword_lessdef:
  forall v v', lessdef v v' -> lessdef (hiword v) (hiword v').
Proof.
  intros. inv H; auto. constructor.
Qed.

Lemma offset_ptr_zero:
  forall v v', offset_ptr v Ptrofs.zero = Some v' ->
          lessdef v' v.
Proof.
  intros. destruct v,v'; simpl; auto; inv H.
  all: try (destruct o,o;inv H1).
  3: destruct p;simpl.
  all: rewrite Ptrofs.add_zero; auto.
Qed.

Lemma offset_ptr_assoc:
  forall v d1 d2 v1 v2 v3,
    offset_ptr v d1 = Some v1 ->
    offset_ptr v1 d2 = Some v3 ->
    offset_ptr v (Ptrofs.add d1 d2) = Some v2 ->
    v2 = v3.
Proof.
  intros. destruct v; simpl; auto; inv H; inv H1; inv H0;auto.
  destruct o,o;inv H2; inv H3; inv H1.
  3: destruct p;simpl.
  all: f_equal ; f_equal. 1,2: f_equal.
  all: rewrite Ptrofs.add_assoc;auto.  
Qed.

Lemma lessdef_normalize:
  forall v ty, (is_cap v -> ty = CTcap \/ ty = CTanycap) -> lessdef (normalize v ty) v.
Proof.
  intros v ty H. destruct v; simpl.
  - auto.
  - destruct ty; auto.
  - destruct ty; auto.
  - destruct ty; auto.
  - destruct ty; auto.
  - destruct H as [-> | ->];[easy|..].
    unfold CTcap. 2: unfold CTanycap.
    all: destruct Archi.ptr64; constructor.
  - destruct ty, Archi.ptr64;auto.
Qed.

Lemma normalize_lessdef:
  forall v v' ty, lessdef v v' -> lessdef (normalize v ty) (normalize v' ty).
Proof.
  intros. inv H; auto; simpl.
  all: destruct ty,Archi.ptr64; auto.
Qed.

Lemma lessdef_is_not_cap:
  forall v, is_cap_b v = false -> lessdef OCVundef v.
Proof.
  intros. destruct v; try constructor.
  discriminate.
Qed.

Lemma select_lessdef:
  forall ob ob' v1 v1' v2 v2' ty,
  ob = None /\ (is_cap_b (select ob' v1' v2' ty) = false) \/ ob = ob' ->
  lessdef v1 v1' -> lessdef v2 v2' ->
  lessdef (select ob v1 v2 ty) (select ob' v1' v2' ty).
Proof.
intros; unfold select. destruct H.
- destruct H. subst ob; auto. destruct ob';auto.
  apply lessdef_is_not_cap.
  auto.
- subst ob'; destruct ob as [b|]; auto.
  apply normalize_lessdef. destruct b; auto.
Qed.

(* (** * Values and memory injections *) *)

(* (** A memory injection [f] is a function from addresses to either [None] *)
(*   or [Some] of an address and an offset.  It defines a correspondence *)
(*   between the blocks of two memory states [m1] and [m2]: *)
(* - if [f b = None], the block [b] of [m1] has no equivalent in [m2]; *)
(* - if [f b = Some(b', ofs)], the block [b] of [m2] corresponds to *)
(*   a sub-block at offset [ofs] of the block [b'] in [m2]. *)
(* *) *)

(* Definition meminj : Type := block -> option (block * Z). *)

(* (** A memory injection defines a relation between values that is the *)
(*   identity relation, except for pointer values which are shifted *)
(*   as prescribed by the memory injection.  Moreover, [Vundef] values *)
(*   inject into any other value. *) *)

(* Inductive inject (mi: meminj): ocval -> ocval -> Prop := *)
(*   | inject_int: *)
(*       forall i, inject mi (OCVint i) (OCVint i) *)
(*   | inject_long: *)
(*       forall i, inject mi (OCVlong i) (OCVlong i) *)
(*   | inject_float: *)
(*       forall f, inject mi (OCVfloat f) (OCVfloat f) *)
(*   | inject_single: *)
(*       forall f, inject mi (OCVsingle f) (OCVsingle f) *)
(*   | inject_ptr: *)
(*       forall b1 ofs1 b2 ofs2 delta, *)
(*       mi b1 = Some (b2, delta) -> *)
(*       ofs2 = Ptrofs.add ofs1 (Ptrofs.repr delta) -> *)
(*       inject mi (Vptr b1 ofs1) (Vptr b2 ofs2) *)
(*   | val_inject_undef: forall v, *)
(*       inject mi Vundef v. *)

(* Hint Constructors inject : core. *)

(* Inductive inject_list (mi: meminj): list val -> list val-> Prop:= *)
(*   | inject_list_nil : *)
(*       inject_list mi nil nil *)
(*   | inject_list_cons : forall v v' vl vl' , *)
(*       inject mi v v' -> inject_list mi vl vl'-> *)
(*       inject_list mi (v :: vl) (v' :: vl'). *)

(* Hint Resolve inject_list_nil inject_list_cons : core. *)


(* Lemma inject_list_not_ptr (mi: meminj): *)
(*   forall vl vl', *)
(*     inject_list mi vl vl' -> *)
(*     Forall not_ptr vl -> *)
(*     Forall not_ptr vl'. *)
(* Proof. *)
(*   intros vl. induction vl. *)
(*   - intros. inv H. eauto. *)
(*   - intros. inv H. inv H0. *)
(*     constructor. *)
(*     + inv H3; auto. inv H2. *)
(*     + eauto. *)
(* Qed. *)


(* Lemma inject_ptrofs: *)
(*   forall mi i, inject mi (Vptrofs i) (Vptrofs i). *)
(* Proof. *)
(*   unfold Vptrofs; intros. destruct Archi.ptr64; auto. *)
(* Qed. *)

(* Hint Resolve inject_ptrofs : core. *)

(* Section VAL_INJ_OPS. *)

(* Variable f: meminj. *)

(* Lemma load_result_inject: *)
(*   forall chunk v1 v2, *)
(*   inject f v1 v2 -> *)
(*   inject f (Val.load_result chunk v1) (Val.load_result chunk v2). *)
(* Proof. *)
(*   intros. inv H; destruct chunk; simpl; try constructor; destruct Archi.ptr64; econstructor; eauto. *)
(* Qed. *)

(* Remark add_inject: *)
(*   forall v1 v1' v2 v2', *)
(*   inject f v1 v1' -> *)
(*   inject f v2 v2' -> *)
(*   inject f (Val.add v1 v2) (Val.add v1' v2'). *)
(* Proof. *)
(*   intros. unfold Val.add. destruct Archi.ptr64 eqn:SF. *)
(* - inv H; inv H0; constructor. *)
(* - inv H; inv H0; simpl; auto. *)
(* + econstructor; eauto. *)
(*   rewrite ! Ptrofs.add_assoc. decEq. apply Ptrofs.add_commut. *)
(* + econstructor; eauto. *)
(*   rewrite ! Ptrofs.add_assoc. decEq. apply Ptrofs.add_commut. *)
(* Qed. *)

(* Remark sub_inject: *)
(*   forall v1 v1' v2 v2', *)
(*   inject f v1 v1' -> *)
(*   inject f v2 v2' -> *)
(*   inject f (Val.sub v1 v2) (Val.sub v1' v2'). *)
(* Proof. *)
(*   intros. unfold Val.sub. destruct Archi.ptr64 eqn:SF. *)
(* - inv H; inv H0; constructor. *)
(* - inv H; inv H0; simpl; auto. *)
(* + econstructor; eauto. *)
(*   rewrite Ptrofs.sub_add_l. auto. *)
(* + destruct (eq_block b1 b0); auto. *)
(*   subst. rewrite H1 in H. inv H. rewrite dec_eq_true. *)
(*   rewrite Ptrofs.sub_shifted. auto. *)
(* Qed. *)

(* Remark addl_inject: *)
(*   forall v1 v1' v2 v2', *)
(*   inject f v1 v1' -> *)
(*   inject f v2 v2' -> *)
(*   inject f (Val.addl v1 v2) (Val.addl v1' v2'). *)
(* Proof. *)
(*   intros. unfold Val.addl. destruct Archi.ptr64 eqn:SF. *)
(* - inv H; inv H0; simpl; auto. *)
(* + econstructor; eauto. *)
(*   rewrite ! Ptrofs.add_assoc. decEq. apply Ptrofs.add_commut. *)
(* + econstructor; eauto. *)
(*   rewrite ! Ptrofs.add_assoc. decEq. apply Ptrofs.add_commut. *)
(* - inv H; inv H0; constructor. *)
(* Qed. *)

(* Remark subl_inject: *)
(*   forall v1 v1' v2 v2', *)
(*   inject f v1 v1' -> *)
(*   inject f v2 v2' -> *)
(*   inject f (Val.subl v1 v2) (Val.subl v1' v2'). *)
(* Proof. *)
(*   intros. unfold Val.subl. destruct Archi.ptr64 eqn:SF. *)
(* - inv H; inv H0; simpl; auto. *)
(* + econstructor; eauto. *)
(*   rewrite Ptrofs.sub_add_l. auto. *)
(* + destruct (eq_block b1 b0); auto. *)
(*   subst. rewrite H1 in H. inv H. rewrite dec_eq_true. *)
(*   rewrite Ptrofs.sub_shifted. auto. *)
(* - inv H; inv H0; constructor. *)
(* Qed. *)

(* Lemma offset_ptr_inject: *)
(*   forall v v' ofs, inject f v v' -> inject f (offset_ptr v ofs) (offset_ptr v' ofs). *)
(* Proof. *)
(*   intros. inv H; simpl; econstructor; eauto. *)
(*   rewrite ! Ptrofs.add_assoc. f_equal. apply Ptrofs.add_commut. *)
(* Qed. *)

(* Lemma cmp_bool_inject: *)
(*   forall c v1 v2 v1' v2' b, *)
(*   inject f v1 v1' -> *)
(*   inject f v2 v2' -> *)
(*   Val.cmp_bool c v1 v2 = Some b -> *)
(*   Val.cmp_bool c v1' v2' = Some b. *)
(* Proof. *)
(*   intros. inv H; simpl in H1; try discriminate; inv H0; simpl in H1; try discriminate; simpl; auto. *)
(* Qed. *)

(* Variable (valid_ptr1 valid_ptr2 : block -> Z -> bool). *)

(* Let weak_valid_ptr1 b ofs := valid_ptr1 b ofs || valid_ptr1 b (ofs - 1). *)
(* Let weak_valid_ptr2 b ofs := valid_ptr2 b ofs || valid_ptr2 b (ofs - 1). *)

(* Hypothesis valid_ptr_inj: *)
(*   forall b1 ofs b2 delta, *)
(*   f b1 = Some(b2, delta) -> *)
(*   valid_ptr1 b1 (Ptrofs.unsigned ofs) = true -> *)
(*   valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true. *)

(* Hypothesis weak_valid_ptr_inj: *)
(*   forall b1 ofs b2 delta, *)
(*   f b1 = Some(b2, delta) -> *)
(*   weak_valid_ptr1 b1 (Ptrofs.unsigned ofs) = true -> *)
(*   weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr delta))) = true. *)

(* Hypothesis weak_valid_ptr_no_overflow: *)
(*   forall b1 ofs b2 delta, *)
(*   f b1 = Some(b2, delta) -> *)
(*   weak_valid_ptr1 b1 (Ptrofs.unsigned ofs) = true -> *)
(*   0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned. *)

(* Hypothesis valid_different_ptrs_inj: *)
(*   forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2, *)
(*   b1 <> b2 -> *)
(*   valid_ptr1 b1 (Ptrofs.unsigned ofs1) = true -> *)
(*   valid_ptr1 b2 (Ptrofs.unsigned ofs2) = true -> *)
(*   f b1 = Some (b1', delta1) -> *)
(*   f b2 = Some (b2', delta2) -> *)
(*   b1' <> b2' \/ *)
(*   Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <> Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)). *)

(* Lemma cmpu_bool_inject: *)
(*   forall c v1 v2 v1' v2' b, *)
(*   inject f v1 v1' -> *)
(*   inject f v2 v2' -> *)
(*   Val.cmpu_bool valid_ptr1 c v1 v2 = Some b -> *)
(*   Val.cmpu_bool valid_ptr2 c v1' v2' = Some b. *)
(* Proof. *)
(*   Local Opaque Int.add Ptrofs.add. *)
(*   intros. *)
(*   unfold cmpu_bool in *; destruct Archi.ptr64; *)
(*   inv H; simpl in H1; try discriminate; inv H0; simpl in H1; try discriminate; simpl; auto. *)
(* - fold (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) in H1. *)
(*   fold (weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))). *)
(*   destruct (Int.eq i Int.zero); auto. *)
(*   destruct (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) eqn:E; try discriminate. *)
(*   erewrite weak_valid_ptr_inj by eauto. auto. *)
(* - fold (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) in H1. *)
(*   fold (weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))). *)
(*   destruct (Int.eq i Int.zero); auto. *)
(*   destruct (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) eqn:E; try discriminate. *)
(*   erewrite weak_valid_ptr_inj by eauto. auto. *)
(* - fold (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) in H1. *)
(*   fold (weak_valid_ptr1 b0 (Ptrofs.unsigned ofs0)) in H1. *)
(*   fold (weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))). *)
(*   fold (weak_valid_ptr2 b3 (Ptrofs.unsigned (Ptrofs.add ofs0 (Ptrofs.repr delta0)))). *)
(*   destruct (eq_block b1 b0); subst. *)
(*   rewrite H in H2. inv H2. rewrite dec_eq_true. *)
(*   destruct (weak_valid_ptr1 b0 (Ptrofs.unsigned ofs1)) eqn:?; try discriminate. *)
(*   destruct (weak_valid_ptr1 b0 (Ptrofs.unsigned ofs0)) eqn:?; try discriminate. *)
(*   erewrite !weak_valid_ptr_inj by eauto. simpl. *)
(*   rewrite <-H1. simpl. decEq. apply Ptrofs.translate_cmpu; eauto. *)
(*   destruct (valid_ptr1 b1 (Ptrofs.unsigned ofs1)) eqn:?; try discriminate. *)
(*   destruct (valid_ptr1 b0 (Ptrofs.unsigned ofs0)) eqn:?; try discriminate. *)
(*   destruct (eq_block b2 b3); subst. *)
(*   assert (valid_ptr_implies: forall b ofs, valid_ptr1 b ofs = true -> weak_valid_ptr1 b ofs = true). *)
(*     intros. unfold weak_valid_ptr1. rewrite H0; auto. *)
(*   erewrite !weak_valid_ptr_inj by eauto using valid_ptr_implies. simpl. *)
(*   exploit valid_different_ptrs_inj; eauto. intros [?|?]; [congruence |]. *)
(*   destruct c; simpl in H1; inv H1. *)
(*   simpl; decEq. rewrite Ptrofs.eq_false; auto. congruence. *)
(*   simpl; decEq. rewrite Ptrofs.eq_false; auto. congruence. *)
(*   now erewrite !valid_ptr_inj by eauto. *)
(* Qed. *)

(* Lemma cmplu_bool_inject: *)
(*   forall c v1 v2 v1' v2' b, *)
(*   inject f v1 v1' -> *)
(*   inject f v2 v2' -> *)
(*   Val.cmplu_bool valid_ptr1 c v1 v2 = Some b -> *)
(*   Val.cmplu_bool valid_ptr2 c v1' v2' = Some b. *)
(* Proof. *)
(*   Local Opaque Int64.add Ptrofs.add. *)
(*   intros. *)
(*   unfold cmplu_bool in *; destruct Archi.ptr64; *)
(*   inv H; simpl in H1; try discriminate; inv H0; simpl in H1; try discriminate; simpl; auto. *)
(* - fold (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) in H1. *)
(*   fold (weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))). *)
(*   destruct (Int64.eq i Int64.zero); auto. *)
(*   destruct (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) eqn:E; try discriminate. *)
(*   erewrite weak_valid_ptr_inj by eauto. auto. *)
(* - fold (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) in H1. *)
(*   fold (weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))). *)
(*   destruct (Int64.eq i Int64.zero); auto. *)
(*   destruct (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) eqn:E; try discriminate. *)
(*   erewrite weak_valid_ptr_inj by eauto. auto. *)
(* - fold (weak_valid_ptr1 b1 (Ptrofs.unsigned ofs1)) in H1. *)
(*   fold (weak_valid_ptr1 b0 (Ptrofs.unsigned ofs0)) in H1. *)
(*   fold (weak_valid_ptr2 b2 (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))). *)
(*   fold (weak_valid_ptr2 b3 (Ptrofs.unsigned (Ptrofs.add ofs0 (Ptrofs.repr delta0)))). *)
(*   destruct (eq_block b1 b0); subst. *)
(*   rewrite H in H2. inv H2. rewrite dec_eq_true. *)
(*   destruct (weak_valid_ptr1 b0 (Ptrofs.unsigned ofs1)) eqn:?; try discriminate. *)
(*   destruct (weak_valid_ptr1 b0 (Ptrofs.unsigned ofs0)) eqn:?; try discriminate. *)
(*   erewrite !weak_valid_ptr_inj by eauto. simpl. *)
(*   rewrite <-H1. simpl. decEq. apply Ptrofs.translate_cmpu; eauto. *)
(*   destruct (valid_ptr1 b1 (Ptrofs.unsigned ofs1)) eqn:?; try discriminate. *)
(*   destruct (valid_ptr1 b0 (Ptrofs.unsigned ofs0)) eqn:?; try discriminate. *)
(*   destruct (eq_block b2 b3); subst. *)
(*   assert (valid_ptr_implies: forall b ofs, valid_ptr1 b ofs = true -> weak_valid_ptr1 b ofs = true). *)
(*     intros. unfold weak_valid_ptr1. rewrite H0; auto. *)
(*   erewrite !weak_valid_ptr_inj by eauto using valid_ptr_implies. simpl. *)
(*   exploit valid_different_ptrs_inj; eauto. intros [?|?]; [congruence |]. *)
(*   destruct c; simpl in H1; inv H1. *)
(*   simpl; decEq. rewrite Ptrofs.eq_false; auto. congruence. *)
(*   simpl; decEq. rewrite Ptrofs.eq_false; auto. congruence. *)
(*   now erewrite !valid_ptr_inj by eauto. *)
(* Qed. *)

(* Lemma longofwords_inject: *)
(*   forall v1 v2 v1' v2', *)
(*   inject f v1 v1' -> inject f v2 v2' -> inject f (Val.longofwords v1 v2) (Val.longofwords v1' v2'). *)
(* Proof. *)
(*   intros. unfold Val.longofwords. inv H; auto. inv H0; auto. *)
(* Qed. *)

(* Lemma loword_inject: *)
(*   forall v v', inject f v v' -> inject f (Val.loword v) (Val.loword v'). *)
(* Proof. *)
(*   intros. unfold Val.loword; inv H; auto. *)
(* Qed. *)

(* Lemma hiword_inject: *)
(*   forall v v', inject f v v' -> inject f (Val.hiword v) (Val.hiword v'). *)
(* Proof. *)
(*   intros. unfold Val.hiword; inv H; auto. *)
(* Qed. *)

(* Lemma normalize_inject: *)
(*   forall v v' ty, inject f v v' -> inject f (normalize v ty) (normalize v' ty). *)
(* Proof. *)
(*   intros. inv H. *)
(* - destruct ty; constructor. *)
(* - destruct ty; constructor. *)
(* - destruct ty; constructor. *)
(* - destruct ty; constructor. *)
(* - simpl. destruct ty. *)
(* + destruct Archi.ptr64; econstructor; eauto. *)
(* + auto. *)
(* + destruct Archi.ptr64; econstructor; eauto. *)
(* + auto. *)
(* + destruct Archi.ptr64; econstructor; eauto. *)
(* + econstructor; eauto. *)
(* - constructor. *)
(* Qed. *)

(* Lemma select_inject: *)
(*   forall ob ob' v1 v1' v2 v2' ty, *)
(*   ob = None \/ ob = ob' -> *)
(*   inject f v1 v1' -> inject f v2 v2' -> *)
(*   inject f (select ob v1 v2 ty) (select ob' v1' v2' ty). *)
(* Proof. *)
(*   intros; unfold select. destruct H. *)
(* - subst ob; auto. *)
(* - subst ob'; destruct ob as [b|]; auto. *)
(*   apply normalize_inject. destruct b; auto. *)
(* Qed. *)

(* End VAL_INJ_OPS. *)

End Val.

(* Notation meminj := Val.meminj. *)

(* (** Monotone evolution of a memory injection. *) *)

(* Definition inject_incr (f1 f2: meminj) : Prop := *)
(*   forall b b' delta, f1 b = Some(b', delta) -> f2 b = Some(b', delta). *)

(* Lemma inject_incr_refl : *)
(*    forall f , inject_incr f f . *)
(* Proof. unfold inject_incr. auto. Qed. *)

(* Lemma inject_incr_trans : *)
(*   forall f1 f2 f3, *)
(*   inject_incr f1 f2 -> inject_incr f2 f3 -> inject_incr f1 f3 . *)
(* Proof. *)
(*   unfold inject_incr; intros. eauto. *)
(* Qed. *)

(* Lemma val_inject_incr: *)
(*   forall f1 f2 v v', *)
(*   inject_incr f1 f2 -> *)
(*   Val.inject f1 v v' -> *)
(*   Val.inject f2 v v'. *)
(* Proof. *)
(*   intros. inv H0; eauto. *)
(* Qed. *)

(* Lemma val_inject_list_incr: *)
(*   forall f1 f2 vl vl' , *)
(*   inject_incr f1 f2 -> Val.inject_list f1 vl vl' -> *)
(*   Val.inject_list f2 vl vl'. *)
(* Proof. *)
(*   induction vl; intros; inv H0. auto. *)
(*   constructor. eapply val_inject_incr; eauto. auto. *)
(* Qed. *)

(* Hint Resolve inject_incr_refl val_inject_incr val_inject_list_incr : core. *)

(* Lemma val_inject_lessdef: *)
(*   forall v1 v2, Val.lessdef v1 v2 <-> Val.inject (fun b => Some(b, 0)) v1 v2. *)
(* Proof. *)
(*   intros; split; intros. *)
(*   inv H; auto. destruct v2; econstructor; eauto. rewrite Ptrofs.add_zero; auto. *)
(*   inv H; auto. inv H0. rewrite Ptrofs.add_zero; auto. *)
(* Qed. *)

(* Lemma val_inject_list_lessdef: *)
(*   forall vl1 vl2, Val.lessdef_list vl1 vl2 <-> Val.inject_list (fun b => Some(b, 0)) vl1 vl2. *)
(* Proof. *)
(*   intros; split. *)
(*   induction 1; constructor; auto. apply val_inject_lessdef; auto. *)
(*   induction 1; constructor; auto. apply val_inject_lessdef; auto. *)
(* Qed. *)

(* (** The identity injection gives rise to the "less defined than" relation. *) *)

(* Definition inject_id : meminj := fun b => Some(b, 0). *)

(* Lemma val_inject_id: *)
(*   forall v1 v2, *)
(*   Val.inject inject_id v1 v2 <-> Val.lessdef v1 v2. *)
(* Proof. *)
(*   intros; split; intros. *)
(*   inv H; auto. *)
(*   unfold inject_id in H0. inv H0. rewrite Ptrofs.add_zero. constructor. *)
(*   inv H. destruct v2; econstructor. unfold inject_id; reflexivity. rewrite Ptrofs.add_zero; auto. *)
(*   constructor. *)
(* Qed. *)

(* (** Composing two memory injections *) *)

(* Definition compose_meminj (f f': meminj) : meminj := *)
(*   fun b => *)
(*     match f b with *)
(*     | None => None *)
(*     | Some(b', delta) => *)
(*         match f' b' with *)
(*         | None => None *)
(*         | Some(b'', delta') => Some(b'', delta + delta') *)
(*         end *)
(*     end. *)

(* Lemma val_inject_compose: *)
(*   forall f f' v1 v2 v3, *)
(*   Val.inject f v1 v2 -> Val.inject f' v2 v3 -> *)
(*   Val.inject (compose_meminj f f') v1 v3. *)
(* Proof. *)
(*   intros. inv H; auto; inv H0; auto. econstructor. *)
(*   unfold compose_meminj; rewrite H1; rewrite H3; eauto. *)
(*   rewrite Ptrofs.add_assoc. decEq. unfold Ptrofs.add. apply Ptrofs.eqm_samerepr. auto with ints. *)
(* Qed. *)
