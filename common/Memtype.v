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

(** This file defines the interface for the memory model that
  is used in the dynamic semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memdata.

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

Global Hint Constructors perm_order: mem.

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

Module Type MEM.

(** The abstract type of memory states. *)
Parameter mem: Type.

(** * Operations on memory states *)

(** [empty] is the initial memory state. *)
Parameter empty: mem.

(** [alloc m cp lo hi] allocates a fresh block of size [hi - lo] bytes,
  and assigns its ownership to compartment [cp].
  Valid offsets in this block are between [lo] included and [hi] excluded.
  These offsets are writable in the returned memory state.
  This block is not initialized: its contents are initially undefined.
  Returns a pair [(m', b)] of the updated memory state [m'] and
  the identifier [b] of the newly-allocated block.
  Note that [alloc] never fails: we are modeling an infinite memory. *)
Parameter alloc: forall (m: mem) (c: compartment) (lo hi: Z), mem * block.

(** [free m b lo hi cp] frees (deallocates) the range of offsets from [lo]
  included to [hi] excluded in block [b], which must be owned by
  compartment [cp].  Returns the updated memory state, or [None] if the
  freed addresses are not freeable. *)
Parameter free: forall (m: mem) (b: block) (lo hi: Z) (cp: compartment), option mem.

(** [load chunk m b ofs cp] reads a memory quantity [chunk] from
  addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] belonging to
  compartment [cp] in memory state [m].  Returns the value read, or
  [None] if the accessed addresses are not readable. *)
Parameter load: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (cp: option compartment), option val.

(** [store chunk m b ofs v cp] writes value [v] as memory quantity [chunk]
  from addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the updated memory state, or [None] if the accessed addresses
  are not writable, which includes the case where principal compartment [cp]
  does not own block [b]. *)
Parameter store: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val) (cp: compartment), option mem.

(** [loadv] and [storev] are variants of [load] and [store] where
  the address being accessed is passed as a value (of the [Vptr] kind). *)

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) (cp: option compartment) : option val :=
  match addr with
  | Vptr b ofs => load chunk m b (Ptrofs.unsigned ofs) cp
  | _ => None
  end.

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) (cp: compartment) : option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Ptrofs.unsigned ofs) v cp
  | _ => None
  end.

(** [loadbytes m b ofs n cp] reads and returns the byte-level representation of
  the values contained at offsets [ofs] to [ofs + n - 1] within block [b]
  in memory state [m].
  [None] is returned if the accessed addresses are not readable,
  which includes the case where the reading compartment [cp] does not
  own block [b]. *)
Parameter loadbytes: forall (m: mem) (b: block) (ofs n: Z) (cp: option compartment), option (list memval).

(** [storebytes m b ofs bytes cp] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable, which includes
  the case where the reading compartment [cp] does not own block [b]. *)
Parameter storebytes: forall (m: mem) (b: block) (ofs: Z) (bytes: list memval) (cp: compartment), option mem.

(** [free_list] frees all the given (block, lo, hi) triples. *)
Fixpoint free_list (m: mem) (l: list (block * Z * Z)) (cp: compartment) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi cp with
      | None => None
      | Some m' => free_list m' l' cp
      end
  end.

(** [drop_perm m b lo hi p cp] sets the permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have [Freeable] permissions
    in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions,
    including the case where the principal compartment [cp] does not own
    block [b]. *)

Parameter drop_perm: forall (m: mem) (b: block) (lo hi: Z) (p: permission) (cp: compartment), option mem.

(** * Permissions, block validity, access validity, compartments, and bounds *)

(** The next block of a memory state is the block identifier for the
  next allocation.  It increases by one at each allocation.
  Block identifiers below [nextblock] are said to be valid, meaning
  that they have been allocated previously.  Block identifiers above
  [nextblock] are fresh or invalid, i.e. not yet allocated.  Note that
  a block identifier remains valid after a [free] operation over this
  block. *)

Parameter nextblock: mem -> block.

Definition valid_block (m: mem) (b: block) := Plt b (nextblock m).

Axiom valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.

(** [block_compartment m b] returns the compartment associated with the block
  [b] in the memory [m], or [None] if [b] is not allocated in [m]. *)

Parameter block_compartment: forall (m: mem) (b: block), option compartment.

Axiom block_compartment_valid_block:
  forall (m: mem) (b: block),
  ~valid_block m b <->
  block_compartment m b = None.

Definition val_compartment (m: mem) (v: val): option compartment :=
  match v with
  | Vptr b _ => block_compartment m b
  | _ => None
  end.

(** [perm m b ofs k p] holds if the address [b, ofs] in memory state [m]
  has permission [p]: one of freeable, writable, readable, and nonempty.
  If the address is empty, [perm m b ofs p] is false for all values of [p].
  [k] is the kind of permission we are interested in: either the current
  permissions or the maximal permissions. *)
Parameter perm: forall (m: mem) (b: block) (ofs: Z) (k: perm_kind) (p: permission), Prop.

(** Logical implications between permissions *)

Axiom perm_implies:
  forall m b ofs k p1 p2, perm m b ofs k p1 -> perm_order p1 p2 -> perm m b ofs k p2.

(** The current permission is always less than or equal to the maximal permission. *)

Axiom perm_cur_max:
  forall m b ofs p, perm m b ofs Cur p -> perm m b ofs Max p.
Axiom perm_cur:
  forall m b ofs k p, perm m b ofs Cur p -> perm m b ofs k p.
Axiom perm_max:
  forall m b ofs k p, perm m b ofs k p -> perm m b ofs Max p.

(** Having a (nonempty) permission implies that the block is valid.
  In other words, invalid blocks, not yet allocated, are all empty. *)
Axiom perm_valid_block:
  forall m b ofs k p, perm m b ofs k p -> valid_block m b.

(** If a pointer has some permission, it has nonempty permission. *)
Axiom perm_nonempty:
  forall m b ofs k p k', perm m b ofs k p -> perm m b ofs k' Nonempty.

(* Unused?
(** The [Mem.perm] predicate is decidable. *)
Axiom perm_dec:
  forall m b ofs k p, {perm m b ofs k p} + {~ perm m b ofs k p}.
*)

(** [range_perm m b lo hi p] holds iff the addresses [b, lo] to [b, hi-1]
  all have permission [p] of kind [k]. *)
Definition range_perm (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs k p.

Axiom range_perm_implies:
  forall m b lo hi k p1 p2,
  range_perm m b lo hi k p1 -> perm_order p1 p2 -> range_perm m b lo hi k p2.

(** [can_access_block m b (Some cp)] holds if block [b] is mapped to compartment [cp]
    in memory [m]. *)
Definition can_access_block (m: mem) (b: block) (cp: option compartment): Prop :=
  match cp with
  | None => True
  | Some cp => block_compartment m b = Some cp
  end.

(** An access to a memory quantity [chunk] at address [b, ofs] with
  permission [p] is valid in [m] if the accessed addresses all have
  current permission [p] and moreover the offset is properly aligned
  and the block, [b], belongs to compartment [cp]. *)
Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z)
           (p: permission) (cp: option compartment): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) Cur p
  /\ can_access_block m b cp
  /\ (align_chunk chunk | ofs).

Axiom valid_access_implies:
  forall m chunk b ofs p1 cp p2,
  valid_access m chunk b ofs p1 cp -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2 cp.

Axiom valid_access_valid_block:
  forall m chunk b ofs cp,
  valid_access m chunk b ofs Nonempty cp ->
  valid_block m b.

Axiom valid_access_perm:
  forall m chunk b ofs k p cp,
  valid_access m chunk b ofs p cp ->
  perm m b ofs k p.

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)

Parameter valid_pointer: forall (m: mem) (b: block) (ofs: Z), bool.

Axiom valid_pointer_nonempty_perm:
  forall m b ofs,
  valid_pointer m b ofs = true <-> perm m b ofs Cur Nonempty.
Axiom valid_pointer_valid_access:
  forall m b cp ofs,
  can_access_block m b cp ->
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty cp.

(** C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)

Definition weak_valid_pointer (m: mem) (b: block) (ofs: Z) :=
  valid_pointer m b ofs || valid_pointer m b (ofs - 1).

Axiom weak_valid_pointer_spec:
  forall m b ofs,
  weak_valid_pointer m b ofs = true <->
    valid_pointer m b ofs = true \/ valid_pointer m b (ofs - 1) = true.
Axiom valid_pointer_implies:
  forall m b ofs,
  valid_pointer m b ofs = true -> weak_valid_pointer m b ofs = true.

(** * Properties of the memory operations *)

(** ** Properties of the initial memory state. *)

Axiom nextblock_empty: nextblock empty = 1%positive.
Axiom perm_empty: forall b ofs k p, ~perm empty b ofs k p.
Axiom valid_access_empty:
  forall chunk b ofs p cp, ~valid_access empty chunk b ofs p cp.

(** ** Properties of [load]. *)

(** A load succeeds if and only if the access is valid for reading *)
Axiom valid_access_load:
  forall m chunk b ofs cp,
  valid_access m chunk b ofs Readable cp ->
  exists v, load chunk m b ofs cp  = Some v.
Axiom load_valid_access:
  forall m chunk b ofs cp v,
  load chunk m b ofs cp = Some v ->
  valid_access m chunk b ofs Readable cp.

(** The value returned by [load] belongs to the type of the memory quantity
  accessed: [Vundef], [Vint] or [Vptr] for an integer quantity,
  [Vundef] or [Vfloat] for a float quantity. *)
Axiom load_type:
  forall m chunk b ofs cp v,
  load chunk m b ofs cp = Some v ->
  Val.has_type v (type_of_chunk chunk).

Axiom load_rettype:
  forall m chunk b ofs cp v,
  load chunk m b ofs cp = Some v ->
  Val.has_rettype v (rettype_of_chunk chunk).

(** For a small integer or float type, the value returned by [load]
  is invariant under the corresponding cast. *)
Axiom load_cast:
  forall m chunk b ofs cp v,
  load chunk m b ofs cp = Some v ->
  match chunk with
  | Mint8signed => v = Val.sign_ext 8 v
  | Mint8unsigned => v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | _ => True
  end.

Axiom load_int8_signed_unsigned:
  forall m b ofs cp,
  load Mint8signed m b ofs cp = option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs cp).

Axiom load_int16_signed_unsigned:
  forall m b ofs cp,
  load Mint16signed m b ofs cp = option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs cp).


(** ** Properties of [loadbytes]. *)

(** [loadbytes] succeeds if and only if we have read permissions on the accessed
    memory area. *)

Axiom range_perm_loadbytes:
  forall m b ofs len cp,
  range_perm m b ofs (ofs + len) Cur Readable ->
  can_access_block m b cp ->
  exists bytes, loadbytes m b ofs len cp = Some bytes.
Axiom loadbytes_range_perm:
  forall m b ofs len cp bytes,
  loadbytes m b ofs len cp = Some bytes ->
  range_perm m b ofs (ofs + len) Cur Readable.

(** If [loadbytes] succeeds, the corresponding [load] succeeds and
  returns a value that is determined by the
  bytes read by [loadbytes]. *)
Axiom loadbytes_load:
  forall chunk m b ofs cp bytes,
  loadbytes m b ofs (size_chunk chunk) cp = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs cp = Some(decode_val chunk bytes).

(** Conversely, if [load] returns a value, the corresponding
  [loadbytes] succeeds and returns a list of bytes which decodes into the
  result of [load]. *)
Axiom load_loadbytes:
  forall chunk m b ofs cp v,
  load chunk m b ofs cp = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) cp = Some bytes
             /\ v = decode_val chunk bytes.

(** [loadbytes] returns a list of length [n] (the number of bytes read). *)
Axiom loadbytes_length:
  forall m b ofs n cp bytes,
  loadbytes m b ofs n cp = Some bytes ->
  length bytes = Z.to_nat n.

Axiom loadbytes_empty:
  forall m b ofs n cp,
  n <= 0 ->
  can_access_block m b cp ->
  loadbytes m b ofs n cp = Some nil.

(** Composing or decomposing [loadbytes] operations at adjacent addresses. *)
Axiom loadbytes_concat:
  forall m b ofs n1 n2 cp bytes1 bytes2,
  loadbytes m b ofs n1 cp = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 cp = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) cp = Some(bytes1 ++ bytes2).
Axiom loadbytes_split:
  forall m b ofs n1 n2 cp bytes,
  loadbytes m b ofs (n1 + n2) cp = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 cp = Some bytes1
  /\ loadbytes m b (ofs + n1) n2 cp = Some bytes2
  /\ bytes = bytes1 ++ bytes2.

(** ** Properties of [store]. *)

(** [store] preserves block validity, permissions, access validity,
  compartments, and bounds.  Moreover, a [store] succeeds if and only if the
  corresponding access is valid for writing. *)

Axiom nextblock_store:
  forall chunk m1 b ofs v cp m2, store chunk m1 b ofs v cp = Some m2 ->
  nextblock m2 = nextblock m1.
Axiom store_valid_block_1:
  forall chunk m1 b ofs v cp m2, store chunk m1 b ofs v cp = Some m2 ->
  forall b', valid_block m1 b' -> valid_block m2 b'.
Axiom store_valid_block_2:
  forall chunk m1 b ofs v cp m2, store chunk m1 b ofs v cp = Some m2 ->
  forall b', valid_block m2 b' -> valid_block m1 b'.

Axiom perm_store_1:
  forall chunk m1 b ofs v cp m2, store chunk m1 b ofs v cp = Some m2 ->
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Axiom perm_store_2:
  forall chunk m1 b ofs v cp m2, store chunk m1 b ofs v cp = Some m2 ->
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.

Axiom valid_access_store:
  forall m1 chunk b ofs cp v,
  valid_access m1 chunk b ofs Writable (Some cp) ->
  { m2: mem | store chunk m1 b ofs v cp = Some m2 }.
Axiom store_valid_access_1:
  forall chunk m1 b ofs v cp m2, store chunk m1 b ofs v cp = Some m2 ->
  forall chunk' b' ofs' p cp',
  valid_access m1 chunk' b' ofs' p cp' -> valid_access m2 chunk' b' ofs' p cp'.
Axiom store_valid_access_2:
  forall chunk m1 b ofs v cp m2, store chunk m1 b ofs v cp = Some m2 ->
  forall chunk' b' ofs' p cp',
  valid_access m2 chunk' b' ofs' p cp' -> valid_access m1 chunk' b' ofs' p cp'.
Axiom store_valid_access_3:
  forall chunk m1 b ofs v cp m2, store chunk m1 b ofs v cp = Some m2 ->
  valid_access m1 chunk b ofs Writable (Some cp).

Axiom store_block_compartment:
  forall chunk m1 b ofs v cp m2, store chunk m1 b ofs v cp = Some m2 ->
  forall b',
  block_compartment m2 b' = block_compartment m1 b'.

(** Load-store properties. *)

Axiom load_store_similar:
  forall chunk m1 b ofs v cp m2, store chunk m1 b ofs v cp = Some m2 ->
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v', load chunk' m2 b ofs (Some cp) = Some v' /\ decode_encode_val v chunk chunk' v'.

Axiom load_store_same:
  forall chunk m1 b ofs v cp m2, store chunk m1 b ofs v cp = Some m2 ->
  load chunk m2 b ofs (Some cp) = Some (Val.load_result chunk v).

Axiom load_store_other:
  forall chunk m1 b ofs v cp m2, store chunk m1 b ofs v cp = Some m2 ->
  forall chunk' b' ofs' cp',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' cp' = load chunk' m1 b' ofs' cp'.

(** Integrity of pointer values. *)

Definition compat_pointer_chunks (chunk1 chunk2: memory_chunk) : Prop :=
  match chunk1, chunk2 with
  | (Mint32 | Many32), (Mint32 | Many32) => True
  | (Mint64 | Many64), (Mint64 | Many64) => True
  | _, _ => False
  end.

Axiom load_store_pointer_overlap:
  forall chunk m1 b ofs v_b v_o cp m2 chunk' ofs' cp' v,
  store chunk m1 b ofs (Vptr v_b v_o) cp = Some m2 ->
  load chunk' m2 b ofs' cp' = Some v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = Vundef.
Axiom load_store_pointer_mismatch:
  forall chunk m1 b ofs v_b v_o cp m2 chunk' cp' v,
  store chunk m1 b ofs (Vptr v_b v_o) cp = Some m2 ->
  load chunk' m2 b ofs cp' = Some v ->
  ~compat_pointer_chunks chunk chunk' ->
  v = Vundef.
Axiom load_pointer_store:
  forall chunk m1 b ofs v cp m2 chunk' b' ofs' cp' v_b v_o,
  store chunk m1 b ofs v cp = Some m2 ->
  load chunk' m2 b' ofs' cp' = Some(Vptr v_b v_o) ->
  (v = Vptr v_b v_o /\ compat_pointer_chunks chunk chunk' /\ b' = b /\ ofs' = ofs)
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').

(** Load-store properties for [loadbytes]. *)

Axiom loadbytes_store_same:
  forall chunk m1 b ofs v cp m2, store chunk m1 b ofs v cp = Some m2 ->
  loadbytes m2 b ofs (size_chunk chunk) (Some cp) = Some(encode_val chunk v).
Axiom loadbytes_store_other:
  forall chunk m1 b ofs v cp m2, store chunk m1 b ofs v cp = Some m2 ->
  forall b' ofs' n cp',
  b' <> b \/ n <= 0 \/ ofs' + n <= ofs \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n cp' = loadbytes m1 b' ofs' n cp'.

(** [store] is insensitive to the signedness or the high bits of
  small integer quantities. *)

Axiom store_signed_unsigned_8:
  forall m b ofs v cp,
  store Mint8signed m b ofs v cp = store Mint8unsigned m b ofs v cp.
Axiom store_signed_unsigned_16:
  forall m b ofs v cp,
  store Mint16signed m b ofs v cp = store Mint16unsigned m b ofs v cp.
Axiom store_int8_zero_ext:
  forall m b ofs n cp,
  store Mint8unsigned m b ofs (Vint (Int.zero_ext 8 n)) cp =
  store Mint8unsigned m b ofs (Vint n) cp.
Axiom store_int8_sign_ext:
  forall m b ofs n cp,
  store Mint8signed m b ofs (Vint (Int.sign_ext 8 n)) cp =
  store Mint8signed m b ofs (Vint n) cp.
Axiom store_int16_zero_ext:
  forall m b ofs n cp,
  store Mint16unsigned m b ofs (Vint (Int.zero_ext 16 n)) cp =
  store Mint16unsigned m b ofs (Vint n) cp.
Axiom store_int16_sign_ext:
  forall m b ofs n cp,
  store Mint16signed m b ofs (Vint (Int.sign_ext 16 n)) cp =
  store Mint16signed m b ofs (Vint n) cp.

(** ** Properties of [storebytes]. *)

(** [storebytes] preserves block validity, permissions, access validity, and bounds.
  Moreover, a [storebytes] succeeds if and only if we have write permissions
  on the addressed memory area. *)

(* Now I see for example _valid_access_1 actually has two cp and the conclusion picks one, arbitrarily ... *)
Axiom range_perm_storebytes:
  forall m1 b ofs bytes cp,
  range_perm m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable ->
  can_access_block m1 b (Some cp) ->
  { m2 : mem | storebytes m1 b ofs bytes cp = Some m2 }.
Axiom storebytes_range_perm:
  forall m1 b ofs bytes cp m2, storebytes m1 b ofs bytes cp = Some m2 ->
  range_perm m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable.
Axiom perm_storebytes_1:
  forall m1 b ofs bytes cp m2, storebytes m1 b ofs bytes cp = Some m2 ->
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Axiom perm_storebytes_2:
  forall m1 b ofs bytes cp m2, storebytes m1 b ofs bytes cp = Some m2 ->
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Axiom storebytes_valid_access_1:
  forall m1 b ofs bytes cp m2, storebytes m1 b ofs bytes cp = Some m2 ->
  forall chunk' b' ofs' p cp',
  valid_access m1 chunk' b' ofs' p cp' -> valid_access m2 chunk' b' ofs' p cp'.
Axiom storebytes_valid_access_2:
  forall m1 b ofs bytes cp m2, storebytes m1 b ofs bytes cp = Some m2 ->
  forall chunk' b' ofs' p cp',
  valid_access m2 chunk' b' ofs' p cp' -> valid_access m1 chunk' b' ofs' p cp'.
Axiom nextblock_storebytes:
  forall m1 b ofs bytes cp m2, storebytes m1 b ofs bytes cp = Some m2 ->
  nextblock m2 = nextblock m1.
Axiom storebytes_valid_block_1:
  forall m1 b ofs bytes cp m2, storebytes m1 b ofs bytes cp = Some m2 ->
  forall b', valid_block m1 b' -> valid_block m2 b'.
Axiom storebytes_valid_block_2:
  forall m1 b ofs bytes cp m2, storebytes m1 b ofs bytes cp = Some m2 ->
  forall b', valid_block m2 b' -> valid_block m1 b'.

(** Connections between [store] and [storebytes]. *)

Axiom storebytes_store:
  forall m1 b ofs chunk v cp m2,
  storebytes m1 b ofs (encode_val chunk v) cp = Some m2 ->
  (align_chunk chunk | ofs) ->
  store chunk m1 b ofs v cp = Some m2.

Axiom store_storebytes:
  forall m1 b ofs chunk v cp m2,
  store chunk m1 b ofs v cp = Some m2 ->
  storebytes m1 b ofs (encode_val chunk v) cp = Some m2.

(** Load-store properties. *)

Axiom loadbytes_storebytes_same:
  forall m1 b ofs bytes cp m2, storebytes m1 b ofs bytes cp = Some m2 ->
  loadbytes m2 b ofs (Z.of_nat (length bytes)) (Some cp) = Some bytes.
Axiom loadbytes_storebytes_other:
  forall m1 b ofs bytes cp m2, storebytes m1 b ofs bytes cp = Some m2 ->
  forall b' ofs' len cp',
  len >= 0 ->
  b' <> b
  \/ ofs' + len <= ofs
  \/ ofs + Z.of_nat (length bytes) <= ofs' ->
  loadbytes m2 b' ofs' len cp' = loadbytes m1 b' ofs' len cp'.
Axiom load_storebytes_other:
  forall m1 b ofs bytes cp m2, storebytes m1 b ofs bytes cp = Some m2 ->
  forall chunk b' ofs' cp',
  b' <> b
  \/ ofs' + size_chunk chunk <= ofs
  \/ ofs + Z.of_nat (length bytes) <= ofs' ->
  load chunk m2 b' ofs' cp' = load chunk m1 b' ofs' cp'.

(** Composing or decomposing [storebytes] operations at adjacent addresses. *)

Axiom storebytes_concat:
  forall m b ofs bytes1 cp m1 bytes2 m2,
  storebytes m b ofs bytes1 cp = Some m1 ->
  storebytes m1 b (ofs + Z.of_nat(length bytes1)) bytes2 cp = Some m2 ->
  storebytes m b ofs (bytes1 ++ bytes2) cp = Some m2.
Axiom storebytes_split:
  forall m b ofs bytes1 bytes2 cp m2,
  storebytes m b ofs (bytes1 ++ bytes2) cp = Some m2 ->
  exists m1,
     storebytes m b ofs bytes1 cp = Some m1
  /\ storebytes m1 b (ofs + Z.of_nat(length bytes1)) bytes2 cp = Some m2.

(** ** Properties of [alloc]. *)

(** The identifier of the freshly allocated block is the next block
  of the initial memory state. *)

Axiom alloc_result:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  b = nextblock m1.

(** Effect of [alloc] on block validity. *)

Axiom nextblock_alloc:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  nextblock m2 = Pos.succ (nextblock m1).

Axiom valid_block_alloc:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  forall b', valid_block m1 b' -> valid_block m2 b'.
Axiom fresh_block_alloc:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  ~(valid_block m1 b).
Axiom valid_new_block:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  valid_block m2 b.
Axiom valid_block_alloc_inv:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.

(** Effect of [alloc] on permissions. *)

Axiom perm_alloc_1:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  forall b' ofs k p, perm m1 b' ofs k p -> perm m2 b' ofs k p.
Axiom perm_alloc_2:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  forall ofs k, lo <= ofs < hi -> perm m2 b ofs k Freeable.
Axiom perm_alloc_3:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  forall ofs k p, perm m2 b ofs k p -> lo <= ofs < hi.
Axiom perm_alloc_4:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  forall b' ofs k p, perm m2 b' ofs k p -> b' <> b -> perm m1 b' ofs k p.
Axiom perm_alloc_inv:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  forall b' ofs k p,
  perm m2 b' ofs k p ->
  if eq_block b' b then lo <= ofs < hi else perm m1 b' ofs k p.

(** Effect of [alloc] on compartments. *)

Axiom alloc_block_compartment:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  forall b', block_compartment m2 b' =
  if eq_block b' b then Some c else block_compartment m1 b'.

(** Effect of [alloc] on access validity. *)

Axiom valid_access_alloc_other:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  forall chunk b' ofs p cp',
  valid_access m1 chunk b' ofs p cp' ->
  valid_access m2 chunk b' ofs p cp'.
Axiom valid_access_alloc_same:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable (Some c).
Axiom valid_access_alloc_inv:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  forall chunk b' ofs p c',
  valid_access m2 chunk b' ofs p c' ->
  if eq_block b' b
  then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p c'.

(** Load-alloc properties. *)

Axiom load_alloc_unchanged:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  forall chunk b' ofs c',
  valid_block m1 b' ->
  load chunk m2 b' ofs c' = load chunk m1 b' ofs c'.
Axiom load_alloc_other:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  forall chunk b' ofs c' v,
  load chunk m1 b' ofs c' = Some v ->
  load chunk m2 b' ofs c' = Some v.
Axiom load_alloc_same:
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  forall chunk ofs c' v,
  load chunk m2 b ofs c' = Some v ->
  v = Vundef.
Axiom load_alloc_same':
  forall m1 c lo hi m2 b, alloc m1 c lo hi = (m2, b) ->
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi ->
  can_access_block m2 b (Some c) ->
  (align_chunk chunk | ofs) ->
  load chunk m2 b ofs (Some c) = Some Vundef.

(** ** Properties of [free]. *)

(** [free] succeeds if and only if the correspond range of addresses
  has [Freeable] current permission. *)

Axiom range_perm_free:
  forall m1 b lo hi cp,
  range_perm m1 b lo hi Cur Freeable ->
  can_access_block m1 b (Some cp) ->
  { m2: mem | free m1 b lo hi cp = Some m2 }.
Axiom free_range_perm:
  forall m1 bf lo hi cp m2, free m1 bf lo hi cp = Some m2 ->
  range_perm m1 bf lo hi Cur Freeable.

(** Block validity is preserved by [free]. *)

Axiom nextblock_free:
  forall m1 bf lo hi cp m2, free m1 bf lo hi cp = Some m2 ->
  nextblock m2 = nextblock m1.
Axiom valid_block_free_1:
  forall m1 bf lo hi cp m2, free m1 bf lo hi cp = Some m2 ->
  forall b, valid_block m1 b -> valid_block m2 b.
Axiom valid_block_free_2:
  forall m1 bf lo hi cp m2, free m1 bf lo hi cp = Some m2 ->
  forall b, valid_block m2 b -> valid_block m1 b.

(** Effect of [free] on permissions. *)

Axiom perm_free_1:
  forall m1 bf lo hi cp m2, free m1 bf lo hi cp = Some m2 ->
  forall b ofs k p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs k p ->
  perm m2 b ofs k p.
Axiom perm_free_2:
  forall m1 bf lo hi cp m2, free m1 bf lo hi cp = Some m2 ->
  forall ofs k p, lo <= ofs < hi -> ~ perm m2 bf ofs k p.
Axiom perm_free_3:
  forall m1 bf lo hi cp m2, free m1 bf lo hi cp = Some m2 ->
  forall b ofs k p,
  perm m2 b ofs k p -> perm m1 b ofs k p.

(** Effect of [free] on access validity. *)

Axiom valid_access_free_1:
  forall m1 bf lo hi cp m2, free m1 bf lo hi cp = Some m2 ->
  forall chunk b ofs p cp',
  valid_access m1 chunk b ofs p cp' ->
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p cp'.
Axiom valid_access_free_2:
  forall m1 bf lo hi cp m2, free m1 bf lo hi cp = Some m2 ->
  forall chunk ofs p cp',
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p cp').
Axiom valid_access_free_inv_1:
  forall m1 bf lo hi cp m2, free m1 bf lo hi cp = Some m2 ->
  forall chunk b ofs p cp',
  valid_access m2 chunk b ofs p cp' ->
  valid_access m1 chunk b ofs p cp'.
Axiom valid_access_free_inv_2:
  forall m1 bf lo hi cp m2, free m1 bf lo hi cp = Some m2 ->
  forall chunk ofs p cp',
  valid_access m2 chunk bf ofs p cp' ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.

(** Load-free properties *)

Axiom load_free:
  forall m1 bf lo hi cp m2, free m1 bf lo hi cp = Some m2 ->
  forall chunk b ofs cp',
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs cp' = load chunk m1 b ofs cp'.

(** ** Properties of [drop_perm]. *)

Axiom nextblock_drop:
  forall m b lo hi p cp m', drop_perm m b lo hi p cp = Some m' ->
  nextblock m' = nextblock m.
Axiom drop_perm_valid_block_1:
  forall m b lo hi p cp m', drop_perm m b lo hi p cp = Some m' ->
  forall b', valid_block m b' -> valid_block m' b'.
Axiom drop_perm_valid_block_2:
  forall m b lo hi p cp m', drop_perm m b lo hi p cp = Some m' ->
  forall b', valid_block m' b' -> valid_block m b'.

Axiom drop_block_compartment:
  forall m b lo hi p cp m', drop_perm m b lo hi p cp = Some m' ->
  forall b', block_compartment m' b' = block_compartment m b'.

Axiom range_perm_drop_1:
  forall m b lo hi p cp m', drop_perm m b lo hi p cp = Some m' ->
  range_perm m b lo hi Cur Freeable.
Axiom range_perm_drop_2:
  forall m b lo hi cp p,
  range_perm m b lo hi Cur Freeable ->
  can_access_block m b (Some cp) ->
  { m' | drop_perm m b lo hi p cp = Some m' }.

Axiom perm_drop_1:
  forall m b lo hi p cp m', drop_perm m b lo hi p cp = Some m' ->
  forall ofs k, lo <= ofs < hi -> perm m' b ofs k p.
Axiom perm_drop_2:
  forall m b lo hi p cp m', drop_perm m b lo hi p cp = Some m' ->
  forall ofs k p', lo <= ofs < hi -> perm m' b ofs k p' -> perm_order p p'.
Axiom perm_drop_3:
  forall m b lo hi p cp m', drop_perm m b lo hi p cp = Some m' ->
  forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs k p' -> perm m' b' ofs k p'.
Axiom perm_drop_4:
  forall m b lo hi p cp m', drop_perm m b lo hi p cp = Some m' ->
  forall b' ofs k p', perm m' b' ofs k p' -> perm m b' ofs k p'.

Axiom load_drop:
  forall m b lo hi p cp m', drop_perm m b lo hi p cp = Some m' ->
  forall chunk b' ofs cp',
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs cp' = load chunk m b' ofs cp'.

(** * Relating two memory states. *)

(** ** Memory extensions *)

(**  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by relaxing the permissions of [m1] (for instance, allocating larger
  blocks) and replacing some of the [Vundef] values stored in [m1] by
  more defined values stored in [m2] at the same addresses. *)

Parameter extends: mem -> mem -> Prop.

Axiom extends_refl:
  forall m, extends m m.

Axiom load_extends:
  forall chunk m1 m2 b ofs cp v1,
  extends m1 m2 ->
  load chunk m1 b ofs cp = Some v1 ->
  exists v2, load chunk m2 b ofs cp = Some v2 /\ Val.lessdef v1 v2.

Axiom loadv_extends:
  forall chunk m1 m2 addr1 cp addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 cp = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 cp = Some v2 /\ Val.lessdef v1 v2.

Axiom loadbytes_extends:
  forall m1 m2 b ofs len cp bytes1,
  extends m1 m2 ->
  loadbytes m1 b ofs len cp = Some bytes1 ->
  exists bytes2, loadbytes m2 b ofs len cp = Some bytes2
              /\ list_forall2 memval_lessdef bytes1 bytes2.

Axiom store_within_extends:
  forall chunk m1 m2 b ofs v1 cp m1' v2,
  extends m1 m2 ->
  store chunk m1 b ofs v1 cp = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 b ofs v2 cp = Some m2'
  /\ extends m1' m2'.

Axiom store_outside_extends:
  forall chunk m1 m2 b ofs v cp m2',
  extends m1 m2 ->
  store chunk m2 b ofs v cp = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + size_chunk chunk -> False) ->
  extends m1 m2'.

Axiom storev_extends:
  forall chunk m1 m2 addr1 v1 cp m1' addr2 v2,
  extends m1 m2 ->
  storev chunk m1 addr1 v1 cp = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 cp = Some m2'
  /\ extends m1' m2'.

Axiom storebytes_within_extends:
  forall m1 m2 b ofs bytes1 cp m1' bytes2,
  extends m1 m2 ->
  storebytes m1 b ofs bytes1 cp = Some m1' ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2',
     storebytes m2 b ofs bytes2 cp = Some m2'
  /\ extends m1' m2'.

Axiom storebytes_outside_extends:
  forall m1 m2 b ofs bytes2 cp m2',
  extends m1 m2 ->
  storebytes m2 b ofs bytes2 cp = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + Z.of_nat (length bytes2) -> False) ->
  extends m1 m2'.

Axiom alloc_extends:
  forall m1 m2 c lo1 hi1 b m1' lo2 hi2,
  extends m1 m2 ->
  alloc m1 c lo1 hi1 = (m1', b) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 c lo2 hi2 = (m2', b)
  /\ extends m1' m2'.

Axiom free_left_extends:
  forall m1 m2 b lo hi cp m1',
  extends m1 m2 ->
  free m1 b lo hi cp = Some m1' ->
  extends m1' m2.

Axiom free_right_extends:
  forall m1 m2 b lo hi cp m2',
  extends m1 m2 ->
  free m2 b lo hi cp = Some m2' ->
  (forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  extends m1 m2'.

Axiom free_parallel_extends:
  forall m1 m2 b lo hi cp m1',
  extends m1 m2 ->
  free m1 b lo hi cp = Some m1' ->
  exists m2',
     free m2 b lo hi cp = Some m2'
  /\ extends m1' m2'.

Axiom valid_block_extends:
  forall m1 m2 b,
  extends m1 m2 ->
  (valid_block m1 b <-> valid_block m2 b).
Axiom perm_extends:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m1 b ofs k p -> perm m2 b ofs k p.
Axiom valid_access_extends:
  forall m1 m2 chunk b ofs p cp,
  extends m1 m2 -> valid_access m1 chunk b ofs p cp -> valid_access m2 chunk b ofs p cp.
Axiom valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 -> valid_pointer m1 b ofs = true -> valid_pointer m2 b ofs = true.
Axiom weak_valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 ->
  weak_valid_pointer m1 b ofs = true -> weak_valid_pointer m2 b ofs = true.

(** * Memory injections *)

(** A memory injection [f] is a function from addresses to either [None]
  or [Some] of an address and an offset.  It defines a correspondence
  between the blocks of two memory states [m1] and [m2]:
- if [f b = None], the block [b] of [m1] has no equivalent in [m2];
- if [f b = Some(b', ofs)], the block [b] of [m2] corresponds to
  a sub-block at offset [ofs] of the block [b'] in [m2].

A memory injection [f] defines a relation [Val.inject] between values
that is the identity for integer and float values, and relocates pointer
values as prescribed by [f].  (See module [Values].)

Likewise, a memory injection [f] defines a relation between memory states
that we now axiomatize. *)

Parameter inject: meminj -> mem -> mem -> Prop.

Axiom valid_block_inject_1:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m1 b1.

Axiom valid_block_inject_2:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m2 b2.

Axiom perm_inject:
  forall f m1 m2 b1 b2 delta ofs k p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  perm m1 b1 ofs k p -> perm m2 b2 (ofs + delta) k p.

Axiom valid_access_inject:
  forall f m1 m2 chunk b1 ofs b2 delta p cp,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_access m1 chunk b1 ofs p cp ->
  valid_access m2 chunk b2 (ofs + delta) p cp.

Axiom valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true.

Axiom weak_valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  weak_valid_pointer m1 b1 ofs = true ->
  weak_valid_pointer m2 b2 (ofs + delta) = true.

Axiom address_inject:
  forall f m1 m2 b1 ofs1 b2 delta p,
  inject f m1 m2 ->
  perm m1 b1 (Ptrofs.unsigned ofs1) Cur p ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.

Axiom valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' delta,
  inject f m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.

Axiom weak_valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' delta,
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.

Axiom valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.

Axiom weak_valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.

Axiom inject_no_overlap:
  forall f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject f m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Max Nonempty ->
  perm m1 b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

Axiom different_pointers_inject:
  forall f m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  inject f m m' ->
  b1 <> b2 ->
  valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <>
  Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).

Axiom load_inject:
  forall f m1 m2 chunk b1 ofs cp b2 delta v1,
  inject f m1 m2 ->
  load chunk m1 b1 ofs cp = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) cp = Some v2 /\ Val.inject f v1 v2.

Axiom loadv_inject:
  forall f m1 m2 chunk a1 cp a2 v1,
  inject f m1 m2 ->
  loadv chunk m1 a1 cp = Some v1 ->
  Val.inject f a1 a2 ->
  exists v2, loadv chunk m2 a2 cp = Some v2 /\ Val.inject f v1 v2.

Axiom loadbytes_inject:
  forall f m1 m2 b1 ofs len cp b2 delta bytes1,
  inject f m1 m2 ->
  loadbytes m1 b1 ofs len cp = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len cp = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2.

Axiom store_mapped_inject:
  forall f chunk m1 b1 ofs v1 cp n1 m2 b2 delta v2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 cp = Some n1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 cp = Some n2
    /\ inject f n1 n2.

Axiom store_unmapped_inject:
  forall f chunk m1 b1 ofs v1 cp n1 m2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 cp = Some n1 ->
  f b1 = None ->
  inject f n1 m2.

Axiom store_outside_inject:
  forall f m1 m2 chunk b ofs v cp m2',
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v cp = Some m2' ->
  inject f m1 m2'.

Axiom storev_mapped_inject:
  forall f chunk m1 a1 v1 cp n1 m2 a2 v2,
  inject f m1 m2 ->
  storev chunk m1 a1 v1 cp = Some n1 ->
  Val.inject f a1 a2 ->
  Val.inject f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 cp = Some n2 /\ inject f n1 n2.

Axiom storebytes_mapped_inject:
  forall f m1 b1 ofs bytes1 cp n1 m2 b2 delta bytes2,
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 cp = Some n1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 cp = Some n2
    /\ inject f n1 n2.

Axiom storebytes_unmapped_inject:
  forall f m1 b1 ofs bytes1 cp n1 m2,
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 cp = Some n1 ->
  f b1 = None ->
  inject f n1 m2.

Axiom storebytes_outside_inject:
  forall f m1 m2 b ofs bytes2 cp m2',
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z.of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 cp = Some m2' ->
  inject f m1 m2'.

Axiom alloc_right_inject:
  forall f m1 m2 c lo hi b2 m2',
  inject f m1 m2 ->
  alloc m2 c lo hi = (m2', b2) ->
  inject f m1 m2'.

(* FIXME: If this result holds, why do we need alloc_left_unmapped_inject? *)
Axiom alloc_left_unmapped_inject_strong:
  forall f m1 m2 c lo hi m1' b1,
  inject f m1 m2 ->
  alloc m1 c lo hi = (m1', b1) ->
  inject f m1' m2.

Axiom alloc_left_unmapped_inject:
  forall f m1 m2 c lo hi m1' b1,
  inject f m1 m2 ->
  alloc m1 c lo hi = (m1', b1) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b).

Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

Axiom alloc_left_mapped_inject:
  forall f m1 m2 c lo hi m1' b1 b2 delta,
  inject f m1 m2 ->
  alloc m1 c lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  can_access_block m2 b2 (Some c) ->
  0 <= delta <= Ptrofs.max_unsigned ->
  (forall ofs k p, perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Ptrofs.max_unsigned) ->
  (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
  inj_offset_aligned delta (hi-lo) ->
  (forall b delta' ofs k p,
   f b = Some (b2, delta') ->
   perm m1 b ofs k p ->
   lo + delta <= ofs + delta' < hi + delta -> False) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> f' b = f b).

Axiom alloc_parallel_inject:
  forall f m1 m2 c lo1 hi1 m1' b1 lo2 hi2,
  inject f m1 m2 ->
  alloc m1 c lo1 hi1 = (m1', b1) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists f', exists m2', exists b2,
  alloc m2 c lo2 hi2 = (m2', b2)
  /\ inject f' m1' m2'
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, 0)
  /\ (forall b, b <> b1 -> f' b = f b).

Axiom free_inject:
  forall f m1 l cp1 m1' m2 b lo hi cp2 m2',
  inject f m1 m2 ->
  free_list m1 l cp1 = Some m1' ->
  free m2 b lo hi cp2 = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p -> lo <= ofs + delta < hi ->
    exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
  inject f m1' m2'.

Axiom free_parallel_inject:
  forall f m1 m2 b lo hi cp m1' b' delta,
  inject f m1 m2 ->
  free m1 b lo hi cp = Some m1' ->
  f b = Some(b', delta) ->
  exists m2',
     free m2 b' (lo + delta) (hi + delta) cp = Some m2'
  /\ inject f m1' m2'.

Axiom drop_outside_inject:
  forall f m1 m2 b lo hi p cp m2',
  inject f m1 m2 ->
  drop_perm m2 b lo hi p cp = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  inject f m1 m2'.

(** Memory states that inject into themselves. *)

Definition flat_inj (thr: block) : meminj :=
  fun (b: block) => if plt b thr then Some(b, 0) else None.

Parameter inject_neutral: forall (thr: block) (m: mem), Prop.

Axiom neutral_inject:
  forall m, inject_neutral (nextblock m) m ->
  inject (flat_inj (nextblock m)) m m.

Axiom empty_inject_neutral:
  forall thr, inject_neutral thr empty.

Axiom alloc_inject_neutral:
  forall thr m c lo hi b m',
  alloc m c lo hi = (m', b) ->
  inject_neutral thr m ->
  Plt (nextblock m) thr ->
  inject_neutral thr m'.

Axiom store_inject_neutral:
  forall chunk m b ofs v cp m' thr,
  store chunk m b ofs v cp = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  Val.inject (flat_inj thr) v v ->
  inject_neutral thr m'.

Axiom drop_inject_neutral:
  forall m b lo hi p cp m' thr,
  drop_perm m b lo hi p cp = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  inject_neutral thr m'.

End MEM.
