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

(** This file defines the interface for the memory model that
  is used in the dynamic semantics of a capability backend
  It defines a type [mem] of memory states, the following 6 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [stkload]: read a memory chunk given a stack capability with proper authority;
- [stkstore]: store a memory chunk given a stack capability with proper authority;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.

  Note that all capability checks are handled by the opsem
 *)

(* TODO: should the capability checks also be parameters? *)


Require Import Coqlib.
Require Import CapAST.
Require Import Integers.
Require Import Floats.
Require Import OCapValues.
Require Import CapMemdata.

(** Memory states are accessed by addresses [b, ofs]: pairs of a block
  identifier [b] and a byte offset [ofs] within that block.
  Each address is associated to permissions, also known as access rights.
  The following permissions are expressible:
- Freeable (exclusive access): all operations permitted
- Writable: load, store and pointer comparison operations are permitted,
  but freeing is not.
- Readable: only load and pointer comparison operations are permitted.
- Nonempty: valid, but only pointer comparisons are permitted.
- Empty: not yet allocated or previously freed; no operation permitted.

The first four cases are represented by the following type of permissions.
Being empty is represented by the absence of any permission.
*)

Inductive permission: Type :=
  | Freeable: permission
  | Writable: permission
  | Readable: permission
  | Nonempty: permission.

(** In the list, each permission implies the other permissions further down the
    list.  We reflect this fact by the following order over permissions. *)

Inductive perm_order: permission -> permission -> Prop :=
  | perm_refl:  forall p, perm_order p p
  | perm_F_any: forall p, perm_order Freeable p
  | perm_W_R:   perm_order Writable Readable
  | perm_any_N: forall p, perm_order p Nonempty.

Hint Constructors perm_order: mem.

Lemma perm_order_trans:
  forall p1 p2 p3, perm_order p1 p2 -> perm_order p2 p3 -> perm_order p1 p3.
Proof.
  intros. inv H; inv H0; constructor.
Qed.

(** Each address has not one, but two permissions associated
  with it.  The first is the current permission.  It governs whether
  operations (load, store, free, etc) over this address succeed or
  not.  The other is the maximal permission.  It is always at least as
  strong as the current permission.  Once a block is allocated, the
  maximal permission of an address within this block can only
  decrease, as a result of [free] or [drop_perm] operations, or of
  external calls.  In contrast, the current permission of an address
  can be temporarily lowered by an external call, then raised again by
  another external call. *)

Inductive perm_kind: Type :=
| Max: perm_kind
| Cur: perm_kind.

(* TODO:placeholder *)
Inductive error_kind: Type :=
| CompErr: error_kind
| CapErr: error_kind
| PermErr: error_kind
| PtrErr: error_kind.

(** High level representation of the offset and capability pair
necessary for all loads and stores at the machine level. Note that it
does not represent the compiler representation of a heap or stack
pointer, but rather the machine prerequisits for a load and store
operation *)
Definition mem_pointer: Type := occap * Z.

(** There are three hardware memory accesses:
    - DIR is a direct access to the address of the capability, does
      not use an offset
    - UNINIT is an uninitialized access that takes a negative offset
      from the capability address
    - DEFAULT is the DDR or PCC access that takes a positive offset
      from the capability lower bound *)
Inductive act_kind: Type:=
| DIR: act_kind
| UNINIT: act_kind
| DEFAULT: act_kind.

Definition eq_error_kind (x y: error_kind): {x = y} + {x <> y}.
Proof. decide equality. Defined.
Global Opaque eq_error_kind.

Definition eq_pointer (x y: mem_pointer): {x = y} + {x <> y}.
Proof.
  decide equality. apply Z.eq_dec. apply occap_dec.
Defined.
Global Opaque eq_pointer.

Module Type MEM.

(** The abstract type of memory states. *)
Parameter mem: Type.

(** * Operations on memory states *)

(** [empty] is the initial memory state. *)
Parameter empty: mem.

(** [alloc m cp lo hi] allocates a fresh block of size [hi - lo]
  bytes, and assigns its ownership to compartment [cp].  Valid offsets
  in this block are between [lo] included and [hi] excluded.  These
  offsets are writable in the returned memory state.  This block is
  not initialized: its contents are initially undefined.  Returns a
  pair [(m', b)] of the updated memory state [m'] and the identifier
  [b] of the newly-allocated block.  Note that [alloc] never fails: we
  are modeling an infinite memory. Alloc only allocates heap memory *)
Parameter alloc: forall (m: mem) (c: compartment) (len: Z), occap * mem.

(** [free m b lo hi cp] frees (deallocates) the range of offsets from [lo]
  included to [hi] excluded in block [b], which must be owned by
  compartment [cp].  Returns the updated memory state, or [None] if the
  freed addresses are not freeable. Free only deallocates heap memory *)
Parameter free: forall (m: mem) (c: occap) (cp: compartment), mem + error_kind.

(** [load chunk m b ofs cp] reads a memory quantity [chunk] from
  addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] belonging to
  compartment [cp] in memory state [m].  Returns the value read, or
  [err] if the accessed addresses are not readable. *)
Parameter load: forall (a: act_kind) (chunk: cap_memory_chunk) (m: mem) (ptr: mem_pointer) (cp: option compartment), ocval + error_kind.

(** [store chunk m b ofs v cp] writes value [v] as memory quantity
  [chunk] from addresses [b, ofs] to [b, ofs + size_chunk chunk - 1]
  in memory state [m].  Returns the updated memory state, or [err] if
  the accessed addresses are not writable, which includes the case
  where principal compartment [cp] does not own block [b], as well as
  the case where the stored value is a stack capability. *)
Parameter store: forall (a: act_kind) (chunk: cap_memory_chunk) (m: mem) (ptr: mem_pointer) (v: ocval) (cp: compartment), (occap * mem) + error_kind.

(** [loadv] and [storev] are variants of [load] and [store] where
  the address being accessed is passed as a value (of the [Vptr] kind). *)

Definition loadv (a: act_kind) (chunk: cap_memory_chunk) (m: mem) (c: occap) (addr: ocval) (cp: option compartment) : ocval + error_kind :=
  match addr with
  | OCVptr (heap_ptr ofs) => load a chunk m (c, Ptrofs.unsigned ofs) cp
  | OCVptr (stack_ptr ofs) => load a chunk m (c, Ptrofs.unsigned ofs) cp
  | _ => inr PtrErr
  end.

Definition storev (a: act_kind) (chunk: cap_memory_chunk) (m: mem) (c: occap) (addr v: ocval) (cp: compartment) : (occap * mem) + error_kind :=
  match addr with
  | OCVptr (heap_ptr ofs) => store a chunk m (c, Ptrofs.unsigned ofs) v cp
  | OCVptr (stack_ptr ofs) => store a chunk m (c, Ptrofs.unsigned ofs) v cp
  | _ => inr PtrErr
  end.

(** [loadbytes m b ofs n cp] reads and returns the byte-level representation of
  the values contained at offsets [ofs] to [ofs + n - 1] within block [b]
  in memory state [m].
  [err] is returned if the accessed addresses are not readable,
  which includes the case where the reading compartment [cp] does not
  own block [b]. *)
Parameter loadbytes: forall (a: act_kind) (m: mem) (ptr: mem_pointer) (n: Z) (cp: option compartment), (list memval) + error_kind.

(** [storebytes m b ofs bytes cp] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [err] if the accessed locations are not writable, which includes
  the case where the reading compartment [cp] does not own block [b]. *)
Parameter storebytes: forall (a: act_kind) (m: mem) (ptr: mem_pointer) (bytes: list memval) (cp: compartment), (occap * mem) + error_kind.

(** [free_list] frees all the given (block, lo, hi) triples. *)
Fixpoint free_list (m: mem) (l: list (occap)) (cp: compartment) {struct l}: mem + error_kind :=
  match l with
  | nil => inl m
  | c :: l' =>
      match free m c cp with
      | inr err => inr err
      | inl m' => free_list m' l' cp
      end
  end.

(** [drop_perm m b lo hi p cp] sets the permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have [Freeable] permissions
    in the initial memory state [m].
    Returns updated memory state, or [err] if insufficient permissions,
    including the case where the principal compartment [cp] does not own
    block [b]. Only the heap can have its permission dropped *)

Parameter drop_perm: forall (m: mem) (lo hi: Z) (p: permission) (cp: compartment), mem + error_kind.

(** * Permissions, block validity, access validity, compartments, and bounds *)

(** [block_compartment m c] returns the list of heap capabilities internal to
    compartment [c] *)

Parameter block_compartment: forall (m: mem) (c: compartment), list occap.

(** [perm m b ofs k p] holds if the address [b, ofs] in memory state [m]
  has permission [p]: one of freeable, writable, readable, and nonempty.
  If the address is empty, [perm m b ofs p] is false for all values of [p].
  [k] is the kind of permission we are interested in: either the current
  permissions or the maximal permissions. *)
Parameter perm: forall (m: mem) (ofs: Z) (k: perm_kind) (p: permission), Prop.

(** Logical implications between permissions *)

Axiom perm_implies:
  forall m ofs k p1 p2, perm m ofs k p1 -> perm_order p1 p2 -> perm m ofs k p2.

(** The current permission is always less than or equal to the maximal permission. *)

Axiom perm_cur_max:
  forall m ofs p, perm m ofs Cur p -> perm m ofs Max p.
Axiom perm_cur:
  forall m ofs k p, perm m ofs Cur p -> perm m ofs k p.
Axiom perm_max:
  forall m ofs k p, perm m ofs k p -> perm m ofs Max p.

(* Unused?
(** The [Mem.perm] predicate is decidable. *)
Axiom perm_dec:
  forall m b ofs k p, {perm m b ofs k p} + {~ perm m b ofs k p}.
*)

(** [range_perm m b lo hi p] holds iff the addresses [b, lo] to [b, hi-1]
  all have permission [p] of kind [k]. *)
Definition range_perm (m: mem) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m ofs k p.

Axiom range_perm_implies:
  forall m lo hi k p1 p2,
    range_perm m lo hi k p1 -> perm_order p1 p2 -> range_perm m lo hi k p2.

(** [derive_offset a c ofs] derives the physical address from the
    capability [c] at offset [ofs], by applying the action kind [a] *)
Parameter derive_offset: forall (a: act_kind) (c: occap) (ofs: Z), Z.

(** [can_access_block m c (Some cp)] holds if capability [c] is owned
    by compartment [cp] in memory [m]. *)
Definition derived_cap (c c': occap): Prop :=
  Ptrofs.unsigned (get_hi c') <= Ptrofs.unsigned (get_hi c)
  /\ Ptrofs.unsigned (get_lo c) <= Ptrofs.unsigned (get_lo c')
  /\ locFlowsCap c' c
  /\ permFlowsCap c' c.
Definition disjoint_cap (c c': occap): Prop :=
  Ptrofs.unsigned (get_hi c) <= Ptrofs.unsigned (get_lo c')
  \/ Ptrofs.unsigned (get_lo c) <= Ptrofs.unsigned (get_hi c').

Axiom derived_cap_dec: forall c c', {derived_cap c c'} + {~ derived_cap c c'}.
Axiom disjoint_cap_dec: forall c c', {disjoint_cap c c'} + {~ disjoint_cap c c'}.

Definition can_access_block (m: mem) (c: occap) (cp: option compartment): Prop :=
  match cp with
  | None => True
  | Some cp => Exists (fun c' => derived_cap c' c) (block_compartment m cp)
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


Axiom can_store_implies_can_load :
  forall k c ofs l v, (isUCap c = true -> offset_lt_cap (derive_offset k c ofs + Z.of_nat l) c)
                 -> can_store_val k c ofs l v
                 -> can_load_val k c ofs l.

Definition dynamic_access (k: act_kind) (c: occap) (ofs: Z) (l: nat) (v: option ocval) :=
  match v with
  | None => can_load_val k c ofs l
  | Some v => can_store_val k c ofs l v
  end.
           

Definition storeU_increase_authority (v: option ocval) (c: occap) (ofs: Z) (len: nat) (c': option occap) :=
  match v with
  | Some _ =>
      if (ofs =? 0) && isUCap c
      then c' = Val.offset_cap c (Ptrofs.repr (Z.of_nat len))
      else True
  | _ => True
  end.

(** An access to a memory quantity [chunk] at address [c, ofs] with
  permission [p] is valid in [m] if the accessed addresses all have
  current permission [p] and moreover the offset is properly aligned, 
  if [v] is specified, [c] has sufficient authority to store it,
  and [c] belongs to compartment [cp]. *)
Definition valid_access (k: act_kind) (m: mem) (chunk: cap_memory_chunk) (c: occap) (ofs: Z)
           (p: permission) (cp: option compartment) (v: option ocval) (c': option occap): Prop :=
  range_perm m (derive_offset k c ofs) (derive_offset k c ofs + size_chunk chunk) Cur p
  /\ can_access_block m c cp
  /\ dynamic_access k c ofs (size_chunk_nat chunk) v
  /\ (align_chunk chunk | (derive_offset k c ofs))
  /\ storeU_increase_authority v c ofs (size_chunk_nat chunk) c'.


Axiom valid_access_implies:
  forall k m chunk c ofs p1 p2 cp v c',
  valid_access k m chunk c ofs p1 cp v c' -> perm_order p1 p2 ->
  valid_access k m chunk c ofs p2 cp v c'.

Axiom valid_access_perm:
  forall a k m chunk c ofs p cp v c',
    valid_access a m chunk c ofs p cp v c' ->
    perm m (derive_offset a c ofs) k p.

(** [valid_capability m c] - where c is an unsealed capability -
     checks that it does not point to an empty region *)

Parameter valid_capability: forall (m: mem) (c: occap), bool.

Axiom valid_pointer_nonempty_perm:
  forall m c,
    valid_capability m c = true <-> (forall ofs, Ptrofs.unsigned (get_lo c) <= ofs < Ptrofs.unsigned (get_hi c)
                                          -> perm m ofs Cur Nonempty).


(** [dynamic_conditions ptr] defines the dynamic conditions not
    captured by [valid_pointer] *)

Definition dynamic_conditions (m: mem) (k: act_kind) (c: occap) (ofs: Z) (len: Z)
           (v: option ocval) (cp: option compartment) (c': option occap) : Prop :=
  dynamic_access k c ofs (Z.to_nat len) v
  /\ can_access_block m c cp
  /\ storeU_increase_authority v c ofs (Z.to_nat len) c'.

Axiom valid_pointer_valid_access:
  forall m k c ofs l v cp c',
    dynamic_conditions m k c ofs l v cp c' ->
    valid_capability m c = true <-> valid_access k m CMint8unsigned c ofs Nonempty cp v c'.


(* TODO: discuss weak valid pointers in the presence of
capabilities. My intuition tells me we do NOT want to allow this for
the stack pointer *)
(** C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)

(* Definition weak_valid_pointer (m: mem) (c: occap) (ofs: Z) := *)
(*   valid_capability m c ofs || valid_capability m c (ofs - 1). *)

(* Axiom weak_valid_pointer_spec: *)
(*   forall m b ofs, *)
(*   weak_valid_pointer m b ofs = true <-> *)
(*     valid_heap_pointer m b ofs = true \/ valid_heap_pointer m b (ofs - 1) = true. *)
(* Axiom valid_pointer_implies: *)
(*   forall m b ofs, *)
(*   valid_heap_pointer m b ofs = true -> weak_valid_pointer m b ofs = true. *)

(** * Properties of the memory operations *)

(** ** Properties of the initial memory state. *)

(** Heap *)
Axiom perm_empty: forall ofs k p, ~perm empty ofs k p.
Axiom valid_access_empty:
  forall k chunk c ofs p cp v c', ~valid_access k empty chunk c ofs p cp v c'.

(** ** Properties of [load]. *)

(** A load succeeds if and only if the access is valid for reading *)
Axiom valid_access_load:
  forall m chunk ptr ofs cp k,
  valid_access k m chunk ptr ofs Readable cp None None ->
  exists v, load k chunk m (ptr,ofs) cp = inl v.
Axiom load_valid_access:
  forall m chunk ptr ofs cp v k,
  load k chunk m (ptr,ofs) cp = inl v ->
  valid_access k m chunk ptr ofs Readable cp None None.

(** If a stack load fails but the capability is valid, the error must be a load error *)
Axiom valid_capability_stkload_error:
  forall k m c ofs err,
    load k CMint8unsigned m (c,ofs) None = inr err ->
    valid_capability m c = true ->
    err = CapErr.

(** The value returned by [load] belongs to the type of the memory
  quantity accessed: [Vundef], [Vint] or [Vptr] for an integer
  quantity, [Vundef] or [Vfloat] for a float quantity, [Vundef] or
  [Vcap] for a capability quantity. *)
Axiom load_type:
  forall m chunk ptr cp v k,
  load k chunk m ptr cp = inl v ->
  Val.has_type v (type_of_chunk chunk).

Axiom load_rettype:
  forall m chunk ptr cp v k,
  load k chunk m ptr cp = inl v ->
  Val.has_rettype v (rettype_of_chunk chunk).

(** For a small integer or float type, the value returned by [load]
  is invariant under the corresponding cast. *)
Axiom load_cast:
  forall m chunk ptr cp v k,
  load k chunk m ptr cp = inl v ->
  match chunk with
  | CMint8signed => v = Val.sign_ext 8 v
  | CMint8unsigned => v = Val.zero_ext 8 v
  | CMint16signed => v = Val.sign_ext 16 v
  | CMint16unsigned => v = Val.zero_ext 16 v
  | _ => True
  end.

Axiom load_int8_signed_unsigned:
  forall m ptr cp k,
  load k CMint8signed m ptr cp = sum_left_map (Val.sign_ext 8) (load k CMint8unsigned m ptr cp).

Axiom load_int16_signed_unsigned:
  forall m ptr cp k,
  load k CMint16signed m ptr cp = sum_left_map (Val.sign_ext 16) (load k CMint16unsigned m ptr cp).


(** ** Properties of [loadbytes]. *)

(** [loadbytes] succeeds if and only if we have read permissions on the accessed
    memory area. *)

Axiom range_perm_loadbytes:
  forall k m ptr ofs len cp,
    range_perm m (derive_offset k ptr ofs) (derive_offset k ptr ofs + len) Cur Readable ->
    dynamic_conditions m k ptr ofs len None cp None ->
    exists bytes, loadbytes k m (ptr,ofs) len cp = inl bytes.
Axiom loadbytes_range_perm:
  forall k m ptr ofs len cp bytes,
    loadbytes k m (ptr,ofs) len cp = inl bytes ->
    range_perm m (derive_offset k ptr ofs) (derive_offset k ptr ofs + len) Cur Readable.


(** If [loadbytes] succeeds, the corresponding [load] succeeds and
  returns a value that is determined by the
  bytes read by [loadbytes]. *)
Axiom loadbytes_load:
  forall k chunk m ptr ofs cp bytes,
    loadbytes k m (ptr,ofs) (size_chunk chunk) cp = inl bytes ->
    (align_chunk chunk | derive_offset k ptr ofs) ->
    load k chunk m (ptr,ofs) cp = inl (decode_val chunk bytes).

(** Conversely, if [load] returns a value, the corresponding
  [loadbytes] succeeds and returns a list of bytes which decodes into the
  result of [load]. *)
Axiom load_loadbytes:
  forall k chunk m ptr cp v ofs,
    load k chunk m (ptr,ofs) cp = inl v ->
    exists bytes, loadbytes k m (ptr,ofs) (size_chunk chunk) cp = inl bytes
             /\ v = decode_val chunk bytes.

(** [loadbytes] returns a list of length [n] (the number of bytes read). *)
Axiom loadbytes_length:
  forall k m ptr n cp bytes,
  loadbytes k m ptr n cp = inl bytes ->
  length bytes = Z.to_nat n.

Axiom loadbytes_empty:
  forall m k ptr ofs len cp,
  len <= 0 ->
  dynamic_conditions m k ptr ofs len None cp None ->
  loadbytes k m (ptr,ofs) len cp = inl nil.

(** Composing or decomposing [loadbytes] operations at adjacent addresses. *)
Definition incr_pointer (a: act_kind) (ptr:mem_pointer) (n: Z) : option mem_pointer  :=
  match a,ptr with
  | DIR, (c,ofs) => option_map (fun c => (c,ofs)) (incr_addr_stk c (Ptrofs.repr n))
  | UNINIT, (c,ofs) => Some (c,ofs + n)
  | DEFAULT, (c,ofs) => Some (c,ofs + n)
  end.

Axiom loadbytes_concat:
  forall k m ptr1 ptr2 n1 n2 cp bytes1 bytes2,
    incr_pointer k ptr1 n1 = Some ptr2 ->
    loadbytes k m ptr1 n1 cp = inl bytes1 ->
    loadbytes k m ptr2 n2 cp = inl bytes2 ->
    n1 >= 0 -> n2 >= 0 ->
    loadbytes k m ptr1 (n1 + n2) cp = inl(bytes1 ++ bytes2).
Axiom loadbytes_split:
  forall k m ptr n1 n2 cp bytes,
  loadbytes k m ptr (n1 + n2) cp = inl bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2, exists ptr2,
    incr_pointer k ptr n1 = Some ptr2
    /\ loadbytes k m ptr n1 cp = inl bytes1
    /\ loadbytes k m ptr2 n2 cp = inl bytes2
    /\ bytes = bytes1 ++ bytes2.


(** ** Properties of [store]. *)

(** [store] preserves block validity, permissions, access validity,
  compartments, and bounds.  Moreover, a [store] succeeds if and only if the
  corresponding access is valid for writing. *)

Axiom perm_store_1:
  forall mk chunk m1 ptr v cp m2 ptr',
    store mk chunk m1 ptr v cp = inl (ptr',m2) ->
    forall ofs' k p, perm m1 ofs' k p -> perm m2 ofs' k p.
Axiom perm_store_2:
  forall mk chunk m1 ptr v cp m2 ptr',
    store mk chunk m1 ptr v cp = inl (ptr',m2) ->
  forall ofs' k p, perm m2 ofs' k p -> perm m1 ofs' k p.


Axiom valid_access_store:
  forall a m1 chunk ptr ofs cp v k ptr',
  valid_access a m1 chunk ptr ofs Writable (Some cp) (Some v) (Some ptr') ->
  { m2: mem | store k chunk m1 (ptr,ofs) v cp = inl (ptr',m2) }.
Axiom store_valid_access_1:
  forall k chunk m1 ptr v cp m2 ptr', store k chunk m1 ptr v cp = inl (ptr',m2) ->
  forall chunk' p ofs perm cp' v' p',
  valid_access k m1 chunk' p ofs perm cp' v' p' -> valid_access k m2 chunk' p ofs perm cp' v' p'.
Axiom store_valid_access_2:
  forall k chunk m1 ptr v cp m2 ptr', store k chunk m1 ptr v cp = inl (ptr',m2) ->
  forall chunk' p p' ofs perm cp' v',
  valid_access k m2 chunk' p ofs perm cp' v' p' -> valid_access k m1 chunk' p ofs perm cp' v' p'.
Axiom store_valid_access_3:
  forall k chunk m1 ptr ofs v cp m2 ptr', store k chunk m1 (ptr,ofs) v cp = inl (ptr',m2) ->
  valid_access k m1 chunk ptr ofs Writable (Some cp) (Some v) (Some ptr').

Axiom store_block_compartment:
  forall k chunk m1 ptr v cp m2 ptr', store k chunk m1 ptr v cp = inl (ptr',m2) ->
  forall b',
  block_compartment m2 b' = block_compartment m1 b'.

(** Load-store properties. *)

Axiom load_store_similar:
  forall k chunk m1 ptr v cp m2 ptr', store k chunk m1 ptr v cp = inl (ptr',m2) ->
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v', load k chunk' m2 ptr (Some cp) = inl v' /\ decode_encode_val v chunk chunk' v'.

(* TODO: find good way to formulate following *) (*
Axiom load_store_same:
  forall k chunk m1 ptr ofs v cp m2 ptr' ofs',
    store k chunk m1 (ptr,ofs) v cp = inl (ptr',m2) ->
    load k chunk m2 (ptr',ofs) (Some cp) = inl (Val.load_result chunk v). *)

(*
Axiom load_store_other:
  forall k chunk m1 ptr v cp m2 ofs ptr2,
    store k chunk m1 (ptr,ofs) v cp = inl (ptr2,m2) ->
    forall chunk' ptr' cp' ofs',
      ofs' + size_chunk chunk' <= ofs
      \/ ofs + size_chunk chunk <= ofs' ->
      load k chunk' m2 ptr' cp' = load k chunk' m1 ptr' cp'.*)

(** Integrity of pointer values. *)

Definition compat_pointer_chunks (chunk1 chunk2: cap_memory_chunk) (storev: ocval) : Prop :=
  match chunk1, chunk2, storev with
  | (CMint32 | CMany32), (CMint32 | CMany32), OCVptr _ => True
  | (CMint64 | CMany64), (CMint64 | CMany64), OCVptr _ => True
  | (CMcap64 | CMany64), (CMcap64 | CMany64), OCVcap _ => True
  | (CMcap128 | CMany128), (CMcap128 | CMany128), OCVcap _ => True
  | _, _, _ => False
  end.

Definition is_pointer (v: ocval) : bool :=
  match v with
  | OCVptr _ | OCVcap _ => true
  | _ => false
  end.

Axiom load_store_pointer_overlap:
  forall k chunk m1 ofs v1 v2 storev cp m2 chunk' ofs' cp' v ptr2,
  is_pointer storev = true ->
  store k chunk m1 (v1,ofs) storev cp = inl (ptr2,m2) ->
  load k chunk' m2 (v2,ofs') cp' = inl v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = OCVundef.
Axiom load_store_pointer_mismatch:
  forall k chunk m1 ptr storev cp m2 chunk' cp' v ptr' ofs ofs',
  is_pointer storev = true ->
  store k chunk m1 (ptr,ofs) storev cp = inl (ptr',m2) ->
  load k chunk' m2 (ptr',ofs') cp' = inl v ->
  ~compat_pointer_chunks chunk chunk' storev ->
  v = OCVundef.
Axiom load_pointer_store:
  forall k chunk m1 ptr ofs v cp m2 chunk' ptr' ofs' cp' v' ptr2,
  is_pointer v = true ->
  store k chunk m1 (ptr,ofs) v cp = inl (ptr2,m2) ->
  load k chunk' m2 (ptr',ofs') cp' = inl v' ->
  (v = v' /\ compat_pointer_chunks chunk chunk' v /\ ofs = ofs')
  \/ (ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').

(** Load-store properties for [loadbytes]. *)

Axiom loadbytes_store_same:
  forall k chunk m1 ptr ofs v cp ptr' ofs' m2, store k chunk m1 (ptr,ofs) v cp = inl (ptr',m2) ->
  loadbytes k m2 (ptr',ofs') (size_chunk chunk) (Some cp) = inl(encode_val chunk v).
Axiom loadbytes_store_other:
  forall k chunk m1 p v cp m2 ptr2, store k chunk m1 p v cp = inl (ptr2,m2) ->
  forall k p' ofs' ofs n cp',
    n <= 0 \/ ofs' + n <= ofs \/ ofs + size_chunk chunk <= ofs' ->
    loadbytes k m2 p' n cp' = loadbytes k m1 p' n cp'.

(** [store] is insensitive to the signedness or the high bits of
  small integer quantities. *)

Axiom store_signed_unsigned_8:
  forall k m ptr v cp,
  store k CMint8signed m ptr v cp = store k CMint8unsigned m ptr v cp.
Axiom store_signed_unsigned_16:
  forall k m ptr v cp,
  store k CMint16signed m ptr v cp = store k CMint16unsigned m ptr v cp.
Axiom store_int8_zero_ext:
  forall k m ptr n cp,
  store k CMint8unsigned m ptr (OCVint (Int.zero_ext 8 n)) cp =
  store k CMint8unsigned m ptr (OCVint n) cp.
Axiom store_int8_sign_ext:
  forall k m ptr n cp,
  store k CMint8signed m ptr (OCVint (Int.sign_ext 8 n)) cp =
  store k CMint8signed m ptr (OCVint n) cp.
Axiom store_int16_zero_ext:
  forall k m ptr n cp,
  store k CMint16unsigned m ptr (OCVint (Int.zero_ext 16 n)) cp =
  store k CMint16unsigned m ptr (OCVint n) cp.
Axiom store_int16_sign_ext:
  forall k m ptr n cp,
  store k CMint16signed m ptr (OCVint (Int.sign_ext 16 n)) cp =
  store k CMint16signed m ptr (OCVint n) cp.

(** ** Properties of [storebytes]. *)

(** [storebytes] preserves block validity, permissions, access validity, and bounds.
  Moreover, a [storebytes] succeeds if and only if we have write permissions
  on the addressed memory area. *)

(* Now I see for example _valid_access_1 actually has two cp and the conclusion picks one, arbitrarily ... *)
Axiom range_perm_storebytes:
  forall k m1 ptr ofs bytes cp ptr' chunk,
    range_perm m1 (derive_offset k ptr ofs) ((derive_offset k ptr ofs) + Z.of_nat (length bytes)) Cur Writable ->
    length bytes = size_chunk_nat chunk ->
    dynamic_conditions m1 k ptr ofs (size_chunk chunk) (Some (decode_val chunk bytes)) (Some cp) (Some ptr') ->
    { m2 : mem | storebytes k m1 (ptr,ofs) bytes cp = inl (ptr',m2) }.
Axiom storebytes_range_perm:
  forall k m1 ptr bytes cp ptr2 m2 ofs,
    storebytes k m1 (ptr,ofs) bytes cp = inl (ptr2,m2) ->
    range_perm m1 (derive_offset k ptr ofs) ((derive_offset k ptr ofs) + Z.of_nat (length bytes)) Cur Writable.
Axiom perm_storebytes_1:
  forall k m1 ptr bytes cp ptr2 m2, storebytes k m1 ptr bytes cp = inl (ptr2,m2) ->
  forall ofs' k p, perm m1 ofs' k p -> perm m2 ofs' k p.
Axiom perm_storebytes_2:
  forall k m1 ptr bytes cp ptr2 m2, storebytes k m1 ptr bytes cp = inl (ptr2,m2) ->
  forall ofs' k p, perm m2 ofs' k p -> perm m1 ofs' k p.
Axiom storebytes_valid_access_1:
  forall k m1 ptr bytes cp ptr2 m2, storebytes k m1 ptr bytes cp = inl (ptr2,m2) ->
  forall k' chunk' ptr' ofs' p cp' o ptr'',
  valid_access k' m1 chunk' ptr' ofs' p cp' (Some o) ptr'' -> valid_access k' m2 chunk' ptr' ofs' p cp' (Some o) ptr''.
Axiom storebytes_valid_access_2:
  forall k m1 ptr bytes cp ptr2 m2, storebytes k m1 ptr bytes cp = inl (ptr2,m2) ->
  forall k' chunk' ptr' ofs' p cp' o ptr'',
  valid_access k' m2 chunk' ptr' ofs' p cp' (Some o) ptr'' -> valid_access k' m1 chunk' ptr' ofs' p cp' (Some o) ptr''.

(** Connections between [store] and [storebytes]. *)

Axiom storebytes_store:
  forall k m1 ptr chunk v cp ptr2 m2 ofs,
  storebytes k m1 (ptr,ofs) (encode_val chunk v) cp = inl (ptr2,m2) ->
  (align_chunk chunk | derive_offset k ptr ofs) ->
  store k chunk m1 (ptr,ofs) v cp = inl (ptr2,m2).

Axiom store_storebytes:
  forall k m1 ptr chunk v cp ptr2 m2,
  store k chunk m1 ptr v cp = inl (ptr2,m2) ->
  storebytes k m1 ptr (encode_val chunk v) cp = inl (ptr2,m2).

(** Load-store properties. *)

Axiom loadbytes_storebytes_same:
  forall k m1 ptr ofs bytes cp m2, storebytes k m1 (ptr,ofs) bytes cp = inl (ptr,m2) ->
  loadbytes k m2 (ptr,ofs) (Z.of_nat (length bytes)) (Some cp) = inl bytes.
Axiom loadbytes_storebytes_other:
  forall k m1 ptr ptr2 bytes cp m2 ofs,
    storebytes k m1 (ptr,ofs) bytes cp = inl (ptr2,m2) ->
  forall k' ptr' ofs' len cp',
  len >= 0 ->
  derive_offset k ptr' ofs' + len <= derive_offset k ptr ofs
  \/ derive_offset k ptr ofs + Z.of_nat (length bytes) <= derive_offset k ptr' ofs' ->
  loadbytes k' m2 (ptr',ofs') len cp' = loadbytes k' m1 (ptr',ofs') len cp'.
Axiom load_storebytes_other:
  forall k m1 ptr bytes cp ptr2 m2 ofs,
    storebytes k m1 (ptr,ofs) bytes cp = inl (ptr2,m2) ->
  forall k' chunk ptr' ofs' cp',
  (derive_offset k ptr' ofs') + size_chunk chunk <= derive_offset k ptr ofs
  \/ derive_offset k ptr ofs + Z.of_nat (length bytes) <= derive_offset k ptr' ofs' ->
  load k' chunk m2 (ptr',ofs') cp' = load k' chunk m1 (ptr',ofs') cp'.

(** Composing or decomposing [storebytes] operations at adjacent addresses. *)

Axiom storebytes_concat:
  forall k m ptr bytes1 cp ptr1 m1 bytes2 ptr2 m2 ptr',
  incr_pointer k ptr (Z.of_nat(length bytes1)) = Some ptr' ->
  storebytes k m ptr bytes1 cp = inl (ptr1,m1) ->
  storebytes k m1 ptr' bytes2 cp = inl (ptr2,m2) ->
  storebytes k m ptr (bytes1 ++ bytes2) cp = inl (ptr2,m2).
Axiom storebytes_split:
  forall k m ptr bytes1 bytes2 cp ptr2 m2,
  storebytes k m ptr (bytes1 ++ bytes2) cp = inl (ptr2,m2) ->
  exists ptr' ptr1 m1,
    storebytes k m ptr bytes1 cp = inl (ptr1,m1)
    /\ incr_pointer k ptr (Z.of_nat(length bytes1)) = Some ptr'
    /\ storebytes k m1 ptr' bytes2 cp = inl (ptr2,m2).

(** ** Properties of [alloc]. *)

(** Effect of [alloc] on permissions. *)

Axiom perm_alloc_1:
  forall m1 c len m2 ptr, alloc m1 c len = (ptr,m2) ->
  forall ofs k p, perm m1 ofs k p -> perm m2 ofs k p.
Axiom perm_alloc_2:
  forall m1 c l m2 ptr, alloc m1 c l = (ptr,m2) ->
  forall ofs k, Ptrofs.unsigned (get_lo ptr) <= ofs < Ptrofs.unsigned (get_hi ptr) -> perm m2 ofs k Freeable.
Axiom perm_alloc_inv:
  forall m1 c l m2 ptr, alloc m1 c l = (ptr,m2) ->
  forall ofs k p,
  perm m2 ofs k p ->
  Ptrofs.unsigned (get_lo ptr) <= ofs < Ptrofs.unsigned (get_hi ptr) \/ perm m1 ofs k p.

(** Effect of [alloc] on compartments. *)

Axiom alloc_block_compartment:
  forall m1 c l m2 ptr,
    alloc m1 c l = (ptr,m2) ->
    In ptr (block_compartment m2 c).

(** Effect of [alloc] on access validity. *)

Axiom valid_access_alloc_other:
  forall m1 c l m2 ptr, alloc m1 c l = (ptr,m2) ->
  forall k' chunk ptr' ofs' p cp' o ptr'',
  valid_access k' m1 chunk ptr' ofs' p cp' o ptr'' ->
  valid_access k' m2 chunk ptr' ofs' p cp' o ptr''.
Axiom valid_access_alloc_same:
  forall m1 c l m2 ptr,
    alloc m1 c l = (ptr,m2) ->
    forall k chunk ptr' ofs o ptr'',
      dynamic_conditions m2 k ptr' ofs (size_chunk chunk) o (Some c) ptr'' ->
      Ptrofs.unsigned (get_lo ptr) <= derive_offset k ptr' ofs ->
      derive_offset k ptr' ofs + size_chunk chunk <= Ptrofs.unsigned (get_hi ptr) ->
      (align_chunk chunk | derive_offset k ptr' ofs) ->
      valid_access k m2 chunk ptr' ofs Freeable (Some c) o ptr''.
Axiom valid_access_alloc_inv:
  forall m1 c l m2 ptr,
    alloc m1 c l = (ptr,m2) ->
    forall k chunk ptr' p c' o ptr'' ofs,
      valid_access k m2 chunk ptr' ofs p c' o ptr'' ->
      if derived_cap_dec ptr ptr'
      then in_bounds k ptr' ofs (size_chunk_nat chunk)
           /\ (align_chunk chunk | (derive_offset k ptr' ofs))
           /\ dynamic_conditions m2 k ptr' ofs (size_chunk chunk) o (Some c) ptr''
      else valid_access k m1 chunk ptr' ofs p c' o ptr''.

(** Load-alloc properties. *)

Axiom load_alloc_unchanged:
  forall m1 c l m2 ptr,
    alloc m1 c l = (ptr,m2) ->
    forall k chunk ptr' ofs' c' ,
      disjoint_cap ptr ptr' ->
      load k chunk m2 (ptr',ofs') c' = load k chunk m1 (ptr',ofs') c'.
Axiom load_alloc_same:
  forall m1 c l m2 ptr,
    alloc m1 c l = (ptr,m2) ->
    forall k chunk ofs c' v,
      load k chunk m2 (ptr,ofs) c' = inl v ->
      v = OCVundef.
Axiom load_alloc_same':
  forall m1 c l m2 ptr,
    alloc m1 c l = (ptr,m2) ->
    forall k ptr' chunk ofs,
      derived_cap ptr ptr' ->
      dynamic_conditions m2 k ptr' ofs (size_chunk chunk) None (Some c) None ->
      (align_chunk chunk | derive_offset k ptr' ofs) ->
      load k chunk m2 (ptr',ofs) (Some c) = inl OCVundef.

(** ** Properties of [free]. *)

(** [free] succeeds if and only if the correspond range of addresses
  has [Freeable] current permission. *)

Axiom range_perm_free:
  forall m1 b ptr cp,
  range_perm m1 (Ptrofs.unsigned (get_hi ptr)) (Ptrofs.unsigned (get_lo ptr)) Cur Freeable ->
  can_access_block m1 b (Some cp) ->
  { m2: mem | free m1 ptr cp = inl m2 }.
Axiom free_range_perm:
  forall m1 ptr cp m2, free m1 ptr cp = inl m2 ->
  range_perm m1 (Ptrofs.unsigned (get_hi ptr)) (Ptrofs.unsigned (get_lo ptr)) Cur Freeable.

(** Effect of [free] on permissions. *)

Axiom perm_free_1:
  forall m1 ptr cp m2, free m1 ptr cp = inl m2 ->
  forall ofs k p,
  ofs < (Ptrofs.unsigned (get_lo ptr)) \/ (Ptrofs.unsigned (get_hi ptr)) <= ofs ->
  perm m1 ofs k p ->
  perm m2 ofs k p.
Axiom perm_free_2:
  forall m1 ptr cp m2, free m1 ptr cp = inl m2 ->
  forall ofs k p, (Ptrofs.unsigned (get_lo ptr)) <= ofs < (Ptrofs.unsigned (get_hi ptr)) -> ~ perm m2 ofs k p.
Axiom perm_free_3:
  forall m1 ptr cp m2, free m1 ptr cp = inl m2 ->
  forall ofs k p,
  perm m2 ofs k p -> perm m1 ofs k p.

(** Effect of [free] on access validity. *)

Axiom valid_access_free_1:
  forall m1 ptr cp m2,
    free m1 ptr cp = inl m2 ->
    forall k chunk ptr' p cp' o ptr'' ofs,
      valid_access k m1 chunk ptr' ofs p cp' o ptr'' ->
      disjoint_cap ptr ptr' ->
      valid_access k m2 chunk ptr' ofs p cp' o ptr''.
Axiom valid_access_free_2:
  forall m1 ptr cp m2,
    free m1 ptr cp = inl m2 ->
    forall k chunk ptr' p cp' ofs o ptr'',
      derived_cap ptr ptr' ->
      ~(valid_access k m2 chunk ptr' ofs p cp' o ptr'') .
Axiom valid_access_free_inv_1:
  forall m1 ptr cp m2, free m1 ptr cp = inl m2 ->
  forall k chunk ptr' ofs p cp' o ptr'',
  valid_access k m2 chunk ptr' ofs p cp' o ptr'' ->
  valid_access k m1 chunk ptr' ofs p cp' o ptr''.
Axiom valid_access_free_inv_2:
  forall m1 ptr cp m2,
    free m1 ptr cp = inl m2 ->
    forall k chunk ptr' ofs p cp' o ptr'',
      valid_access k m2 chunk ptr' ofs p cp' o ptr'' ->
      disjoint_cap ptr ptr'.

(** Load-free properties *)

Axiom load_free:
  forall m1 ptr cp m2,
    free m1 ptr cp = inl m2 ->
    forall k chunk ptr' ofs cp',
      disjoint_cap ptr ptr' ->
      load k chunk m2 (ptr',ofs) cp' = load k chunk m1 (ptr',ofs) cp'.

(** ** Properties of [drop_perm]. *)

Axiom drop_block_compartment:
  forall m lo hi p cp m', drop_perm m lo hi p cp = inl m' ->
  forall b', block_compartment m' b' = block_compartment m b'.

Axiom range_perm_drop_1:
  forall m lo hi p cp m', drop_perm m lo hi p cp = inl m' ->
  range_perm m lo hi Cur Freeable.
Axiom range_perm_drop_2_heap:
  forall m cp p ptr,
  range_perm m (Ptrofs.unsigned (get_lo ptr)) (Ptrofs.unsigned (get_hi ptr)) Cur Freeable ->
  can_access_block m ptr (Some cp) ->
  { m' | drop_perm m (Ptrofs.unsigned (get_lo ptr)) (Ptrofs.unsigned (get_hi ptr)) p cp = inl m' }.

Axiom perm_drop_1:
  forall m lo hi p cp m', drop_perm m lo hi p cp = inl m' ->
  forall ofs k, lo <= ofs < hi -> perm m' ofs k p.
Axiom perm_drop_2:
  forall m lo hi p cp m', drop_perm m lo hi p cp = inl m' ->
  forall ofs k p', lo <= ofs < hi -> perm m' ofs k p' -> perm_order p p'.
Axiom perm_drop_3:
  forall m lo hi p cp m', drop_perm m lo hi p cp = inl m' ->
  forall ofs k p', ofs < lo \/ hi <= ofs -> perm m ofs k p' -> perm m' ofs k p'.
Axiom perm_drop_4:
  forall m lo hi p cp m', drop_perm m lo hi p cp = inl m' ->
  forall ofs k p', perm m' ofs k p' -> perm m ofs k p'.

Axiom load_drop:
  forall m lo hi p cp m', drop_perm m lo hi p cp = inl m' ->
  forall k chunk ptr ofs cp',
  derive_offset k ptr ofs + size_chunk chunk <= lo \/ hi <= derive_offset k ptr ofs \/ perm_order p Readable ->
  load k chunk m' (ptr,ofs) cp' = load k chunk m (ptr,ofs) cp'.


End MEM.
