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

Inductive pointer: Type :=
| int_ptr: block -> Z -> pointer
| cap_ptr: occap -> pointer
| Ucap_ptr: occap -> Z -> pointer.

Inductive mem_block: Type:=
| heap_block: block -> mem_block
| stack_block: sf -> mem_block.

Inductive mem_kind: Type:=
| HEAP: mem_kind
| STACK: mem_kind.

Definition eq_mem_kind (x y: mem_kind): {x = y} + {x <> y}.
Proof. decide equality. Defined.
Global Opaque eq_mem_kind.
                        
Definition eq_mem_block (x y: mem_block): {x=y} + {x<>y}.
Proof. decide equality; apply eq_block.  Defined.
Global Opaque eq_mem_block.

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
  are modeling an infinite memory. *)
Parameter alloc: forall (k: mem_kind) (m: mem) (c: compartment) (lo hi: Z), mem * pointer.

(** [free m b lo hi cp] frees (deallocates) the range of offsets from [lo]
  included to [hi] excluded in block [b], which must be owned by
  compartment [cp].  Returns the updated memory state, or [None] if the
  freed addresses are not freeable. *)
Parameter free: forall (k: mem_kind) (m: mem) (b: mem_block) (lo hi: Z) (cp: compartment), mem + error_kind.

(** [load chunk m b ofs cp] reads a memory quantity [chunk] from
  addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] belonging to
  compartment [cp] in memory state [m].  Returns the value read, or
  [err] if the accessed addresses are not readable. *)
Parameter load: forall (k: mem_kind) (chunk: cap_memory_chunk) (m: mem) (ptr: pointer) (cp: option compartment), ocval + error_kind.

(** [store chunk m b ofs v cp] writes value [v] as memory quantity
  [chunk] from addresses [b, ofs] to [b, ofs + size_chunk chunk - 1]
  in memory state [m].  Returns the updated memory state, or [err] if
  the accessed addresses are not writable, which includes the case
  where principal compartment [cp] does not own block [b], as well as
  the case where the stored value is a stack capability. *)
Parameter store: forall (k: mem_kind) (chunk: cap_memory_chunk) (m: mem) (ptr: pointer) (v: ocval) (cp: compartment), (pointer * mem) + error_kind.

(** [loadv] and [storev] are variants of [load] and [store] where
  the address being accessed is passed as a value (of the [Vptr] kind). *)

Definition loadv (chunk: cap_memory_chunk) (m: mem) (addr: ocval) (cp: option compartment) : ocval + error_kind :=
  match addr with
  | OCVptr b ofs => load HEAP chunk m (int_ptr b (Ptrofs.unsigned ofs)) cp
  | OCVcap c => load STACK chunk m (cap_ptr c) cp
  | _ => inr PtrErr
  end.

Definition storev (chunk: cap_memory_chunk) (m: mem) (addr v: ocval) (cp: compartment) : (pointer * mem) + error_kind :=
  match addr with
  | OCVptr b ofs => store HEAP chunk m (int_ptr b (Ptrofs.unsigned ofs)) v cp
  | OCVcap c => store STACK chunk m (cap_ptr c) v cp
  | _ => inr PtrErr
  end.

(** [loadbytes m b ofs n cp] reads and returns the byte-level representation of
  the values contained at offsets [ofs] to [ofs + n - 1] within block [b]
  in memory state [m].
  [err] is returned if the accessed addresses are not readable,
  which includes the case where the reading compartment [cp] does not
  own block [b]. *)
Parameter loadbytes: forall (k: mem_kind) (m: mem) (ptr: pointer) (n: Z) (cp: option compartment), (list memval) + error_kind.

(** [storebytes m b ofs bytes cp] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [err] if the accessed locations are not writable, which includes
  the case where the reading compartment [cp] does not own block [b]. *)
Parameter storebytes: forall (k: mem_kind) (m: mem) (ptr: pointer) (bytes: list memval) (cp: compartment), (pointer * mem) + error_kind.

(** [free_list] frees all the given (block, lo, hi) triples. *)
Fixpoint free_list (k: mem_kind) (m: mem) (l: list (mem_block * Z * Z)) (cp: compartment) {struct l}: mem + error_kind :=
  match l with
  | nil => inl m
  | (b, lo, hi) :: l' =>
      match free k m b lo hi cp with
      | inr err => inr err
      | inl m' => free_list k m' l' cp
      end
  end.

(** [drop_perm m b lo hi p cp] sets the permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have [Freeable] permissions
    in the initial memory state [m].
    Returns updated memory state, or [err] if insufficient permissions,
    including the case where the principal compartment [cp] does not own
    block [b]. *)

Parameter drop_perm: forall (k: mem_kind) (m: mem) (b: mem_block) (lo hi: Z) (p: permission) (cp: compartment), mem + error_kind.

(** * Permissions, block validity, access validity, compartments, and bounds *)

(** The next block of a memory state is the block identifier for the
  next allocation.  It increases by one at each allocation.
  Block identifiers below [nextblock] are said to be valid, meaning
  that they have been allocated previously.  Block identifiers above
  [nextblock] are fresh or invalid, i.e. not yet allocated.  Note that
  a block identifier remains valid after a [free] operation over this
  block. *)

(* TODO: discuss whether there is not a finite block one can use
instead of these permission maps.... "freeing" (popping) frames is not
the same as freeing memory. *)

Parameter nextblock: mem -> block.

Parameter nextframe: mem -> sf.

Definition valid_block (m: mem) (b: mem_block) :=
  match b with
  | heap_block b => Plt b (nextblock m)
  | stack_block b => Plt b (nextframe m) end.

Axiom valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.

(** [block_compartment m b] returns the compartment associated with the block
  [b] in the memory [m], or [None] if [b] is not allocated in [m]. *)

Parameter block_compartment: forall (m: mem) (b: block), option compartment.

Axiom block_compartment_valid_block:
  forall (m: mem) (b: block),
  ~valid_block m (heap_block b) <->
  block_compartment m b = None.

Definition val_compartment (m: mem) (v: ocval): option compartment :=
  match v with
  | OCVptr b _ => block_compartment m b
  | _ => None
  end.

(** [perm m b ofs k p] holds if the address [b, ofs] in memory state [m]
  has permission [p]: one of freeable, writable, readable, and nonempty.
  If the address is empty, [perm m b ofs p] is false for all values of [p].
  [k] is the kind of permission we are interested in: either the current
  permissions or the maximal permissions. *)
Parameter perm: forall (mk: mem_kind) (m: mem) (b: mem_block) (ofs: Z) (k: perm_kind) (p: permission), Prop.

(** Logical implications between permissions *)

Axiom perm_implies:
  forall mk m b ofs k p1 p2, perm mk m b ofs k p1 -> perm_order p1 p2 -> perm mk m b ofs k p2.

(** The current permission is always less than or equal to the maximal permission. *)

Axiom perm_cur_max:
  forall mk m b ofs p, perm mk m b ofs Cur p -> perm mk m b ofs Max p.
Axiom perm_cur:
  forall mk m b ofs k p, perm mk m b ofs Cur p -> perm mk m b ofs k p.
Axiom perm_max:
  forall mk m b ofs k p, perm mk m b ofs k p -> perm mk m b ofs Max p.

(** Having a (nonempty) permission implies that the block is valid.
  In other words, invalid blocks, not yet allocated, are all empty. *)
Axiom perm_valid_block:
  forall mk m b ofs k p, perm mk m b ofs k p -> valid_block m b.

(* Unused?
(** The [Mem.perm] predicate is decidable. *)
Axiom perm_dec:
  forall m b ofs k p, {perm m b ofs k p} + {~ perm m b ofs k p}.
*)

(** [range_perm m b lo hi p] holds iff the addresses [b, lo] to [b, hi-1]
  all have permission [p] of kind [k]. *)
Definition range_perm (mk: mem_kind) (m: mem) (b: mem_block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm mk m b ofs k p.

Axiom range_perm_implies:
  forall mk m b lo hi k p1 p2,
    range_perm mk m b lo hi k p1 -> perm_order p1 p2 -> range_perm mk m b lo hi k p2.


(** [can_access_block m b (Some cp)] holds if block [b] is mapped to compartment [cp]
    in memory [m]. *)
Definition can_access_block (m: mem) (b: block) (cp: option compartment): Prop :=
  match cp with
  | None => True
  | Some cp => block_compartment m b = Some cp
  end.

(** [can_store_val v] holds if [v] can be stored in the heap: if it is
    either an immediate, a seal or a return code capability *)
Definition can_store_val (v: option ocval): Prop :=
  match v with
  | Some val =>
      match val with
      | OCVundef | OCVint _ | OCVlong _ | OCVfloat _ | OCVsingle _ | OCVptr _ _ => True
      | OCVcap c =>
          match c with
          | OCsealable σ | OCsealed _ σ =>
                             match σ with
                             | OCVseal _ _ _ | OCVretcode _ _ _ => True
                             | _ => False
                             end
          end
      end
  | None => True
  end.

(** [max_read_auth c] derives the maximal read authority of a stack
    derived capability: the current address of an uninitialized
    capability, the upper bound of a non uninitialized capability or a
    sealed capability. In other words, it returns the maxmimum stack
    address a capability may potentially give access to, or None if
    there is no such address *)
Definition max_read_auth (c: ocval): option ptrofs :=
  match c with
  | OCVundef | OCVint _ | OCVlong _ | OCVfloat _ | OCVsingle _ | OCVptr _ _ => None
  | OCVcap c =>
      match c with
      | OCsealed _ _ => None
      | OCsealable σ =>
          match σ with
          | OCVretcode _ _ _ | OCVseal _ _ _ => None
          | OCVretdata lo hi => Some hi
          | OCVstk sf perm lo hi a => if isU perm then Some a else Some hi
          end
      end
  end.

(** [can_load_val_stk c] holds if [c] has sufficient authority to load
    the address of [c] *)
Definition can_load_val_stk (c: occap) (len:nat): Prop :=
  match c with
  | OCsealed _ _ => False
  | OCsealable σ =>
      match σ with
      | OCVretdata _ _ | OCVretcode _ _ _ | OCVseal _ _ _ => False
      | OCVstk sf perm lo hi a => readAllowed perm = true
                                 /\ Ptrofs.unsigned lo <= Ptrofs.unsigned a /\ Ptrofs.unsigned a + Z.of_nat len < Ptrofs.unsigned hi
      end
  end.

(** [can_loadU_val_stk c] holds if [c] has sufficient authority to
    load [c.addr + ofs] *)
Definition can_loadU_val_stk (c: occap) (len:nat) (ofs: Z): Prop :=
  match c with
  | OCsealed _ _ => False
  | OCsealable σ =>
      match σ with
      | OCVretdata _ _ | OCVretcode _ _ _ | OCVseal _ _ _ => False
      | OCVstk sf perm lo hi a => isU perm = true
                                 /\ Ptrofs.unsigned lo <= Ptrofs.unsigned a + ofs
                                 /\ Ptrofs.unsigned a + ofs + Z.of_nat len < Ptrofs.unsigned hi
                                 /\ ofs + Z.of_nat len < 0 (* [ofs] is strictly negative: [a] can't be read from *)
      end
  end.

(** [can_store_val_stk c v] holds if [c] has sufficient authority to
    store [v] at [c.addr]. Note that [v] might be a stack capability:
    to uphold the directed property, the maximal read authority of v
    must be at most equal to the address it is stored into. *)
Definition can_store_val_stk (c: occap) (len:nat) (v: ocval): Prop :=
  match c with
  | OCsealed _ _ => False
  | OCsealable σ =>
      match σ with
      | OCVretdata _ _ | OCVretcode _ _ _ | OCVseal _ _ _ => False
      | OCVstk sf perm lo hi a => writeAllowed perm = true
                                 /\ Ptrofs.unsigned lo <= Ptrofs.unsigned a /\ Ptrofs.unsigned a + Z.of_nat len < Ptrofs.unsigned hi
                                 /\ match max_read_auth v with | None => True | Some a' => Ptrofs.unsigned a' <= Ptrofs.unsigned a + Z.of_nat len end
      end
  end.

(** [can_storeU_val_stk c ofs v] does the same as above, but for an
    uninitialized stack capability *)
Definition can_storeU_val_stk (c: occap) (ofs: Z) (v: ocval) (len: nat) (c': occap): Prop :=
  match c with
  | OCsealed _ _ => False
  | OCsealable σ =>
      match σ with
      | OCVretdata _ _ | OCVretcode _ _ _ | OCVseal _ _ _ => False
      | OCVstk sf perm lo hi a => isU perm = true
                                 /\ Ptrofs.unsigned lo <= Ptrofs.unsigned a + ofs
                                 /\ Ptrofs.unsigned a + ofs + Z.of_nat len < Ptrofs.unsigned hi
                                 /\ ofs <= 0 (* [ofs] is less than or equal to 0: a can be written to *)
                                 /\ match max_read_auth v with | None => True | Some a' => Ptrofs.unsigned a' <= Ptrofs.unsigned a + Z.of_nat len end
                                 /\ if ofs =? 0 then c' = OCsealable (OCVstk sf perm lo hi (Ptrofs.add a (Ptrofs.repr (Z.of_nat len)))) else c = c'
      end
  end.

Axiom can_store_implies_can_load :
  forall c l v, can_store_val_stk c l v -> can_load_val_stk c l.

Axiom can_storeU_implies_can_loadU :
  forall c v c' ofs len, can_storeU_val_stk c ofs v len c' ->
  ofs + (Z.of_nat len) < 0 ->
  can_loadU_val_stk c len ofs.
  
(** An access to a memory quantity [chunk] at address [b, ofs] with
  permission [p] is valid in [m] if the accessed addresses all have
  current permission [p] and moreover the offset is properly aligned, 
  if [v] is specified, it is not a stack derived capability,
  and the block, [b], belongs to compartment [cp]. *)
Definition valid_access_heap (m: mem) (chunk: cap_memory_chunk) (b: block) (ofs: Z)
           (p: permission) (cp: option compartment) (v: option ocval): Prop :=
  range_perm HEAP m (heap_block b) ofs (ofs + size_chunk chunk) Cur p
  /\ can_access_block m b cp
  /\ can_store_val v
  /\ (align_chunk chunk | ofs).

(** An access to a memory quantity [chunk] at the stack frame pointed
    to by [c] with permission [p] is valid in [m] if the accessed
    addresses all have current permission [p] and moreover the offset
    is propely aligned, the capability [c] is an unsealed stack
    capability with sufficient authority to load, and if [v] is
    specified, with sufficient authority to store [v]. *)

(** Dynamic checks of the capability machine during a stack access *)
Definition dynamic_access_stack (c: occap) (len:nat) (v: option ocval): Prop :=
  match v with
  | None => can_load_val_stk c len
  | Some v' => can_store_val_stk c len v' end.

Definition dynamic_access_stackU (c: occap) (ofs: Z) (v: option ocval) (len: nat) (c': occap): Prop :=
  match v with
  | None => can_loadU_val_stk c len ofs
  | Some v' => can_storeU_val_stk c ofs v' len c' end.

Definition valid_access_stack (m: mem) (chunk: cap_memory_chunk) (c: occap)
           (p: permission) (v: option ocval): Prop :=
  match c with
  | OCsealable (OCVstk f' perm lo hi a) =>
      range_perm STACK m (stack_block f') (Ptrofs.unsigned a) ((Ptrofs.unsigned a) + size_chunk chunk) Cur p
      /\ dynamic_access_stack c (size_chunk_nat chunk) v
      /\ (align_chunk chunk | (Ptrofs.unsigned a))
  | _ => False
  end.

(** Similar to above, but for an uninitialized stack capability *)
Definition valid_access_stackU (m: mem) (chunk: cap_memory_chunk) (c: occap) (ofs: Z)
           (p: permission) (v: option ocval) (c': occap): Prop :=
  match c with
  | OCsealable (OCVstk f' perm lo hi a) =>
      range_perm STACK m (stack_block f') (Ptrofs.unsigned a) ((Ptrofs.unsigned a) + size_chunk chunk) Cur p
      /\ dynamic_access_stackU c ofs v (size_chunk_nat chunk) c'
      /\ (align_chunk chunk | (Ptrofs.unsigned a))
  | _ => False
  end.

Definition valid_access (m: mem) (chunk: cap_memory_chunk) (ptr: pointer)
           (p: permission) (cp: option compartment) (v: option ocval) (ptr': pointer): Prop :=
  match ptr,ptr' with
  | int_ptr b ofs,_ => ptr = ptr' /\ valid_access_heap m chunk b ofs p cp v
  | cap_ptr c,_ => ptr = ptr' /\ valid_access_stack m chunk c p v
  | Ucap_ptr c ofs,Ucap_ptr c' ofs' => ofs = ofs' /\ valid_access_stackU m chunk c ofs p v c'
  | _,_ => False
  end.

Axiom valid_access_implies:
  forall m chunk b p1 cp p2 o ptr' ,
  valid_access m chunk b p1 cp o ptr' -> perm_order p1 p2 ->
  valid_access m chunk b p2 cp o ptr'.

Definition get_mem_block (p: pointer) : option mem_block :=
  match p with
  | int_ptr b _ => Some (heap_block b)
  | cap_ptr c => option_map (fun v => stack_block v) (get_stack_frame c)
  | Ucap_ptr c _ => option_map (fun v => stack_block v) (get_stack_frame c)
  end.

Axiom valid_access_get_mem_block:
  forall m chunk ptr p cp v ptr',
    valid_access m chunk ptr p cp v ptr' ->
    exists b, get_mem_block ptr = Some b.

Axiom valid_access_valid_block:
  forall m chunk p cp o b p',
    valid_access m chunk p Nonempty cp o p' ->
    get_mem_block p = Some b ->
    valid_block m b.

Definition infer_mem_kind (ptr: pointer): mem_kind :=
  match ptr with
  | int_ptr _ _ => HEAP
  | cap_ptr _ => STACK
  | Ucap_ptr _ _ => STACK
  end.

Definition infer_ofs (ptr: pointer): option Z :=
  match ptr with
  | int_ptr _ ofs => Some ofs
  | cap_ptr c => option_map (fun a => Ptrofs.unsigned a) (get_addr c)
  | Ucap_ptr c ofs => option_map (fun a => Ptrofs.unsigned a + ofs) (get_addr c)
  end.

Axiom valid_access_infer_ofs:
  forall m chunk ptr p cp v p',
    valid_access m chunk ptr p cp v p' ->
    exists ofs, infer_ofs ptr = Some ofs.

Axiom valid_access_perm:
  forall m chunk ptr p cp v b k ofs ptr',
    valid_access m chunk ptr p cp v ptr' ->
    get_mem_block ptr = Some b ->
    infer_ofs ptr = Some ofs ->
    perm (infer_mem_kind ptr) m b ofs k p.

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)

Parameter valid_heap_pointer: forall (m: mem) (b: block) (ofs: Z), bool.

(** [valid_capability m c] - where c is a stack derived unsealed
    capability - similarly checks that it does not point to a non
    empty frame and offset, for each address in its range of
    authority, however, it does not include the capability checks
    needed for a successful load/store *)

Parameter valid_capability: forall (m: mem) (c: occap), bool.

Definition valid_pointer (m: mem) (ptr: pointer) : bool :=
  match ptr with
  | int_ptr b ofs => valid_heap_pointer m b ofs
  | cap_ptr c => valid_capability m c
  | Ucap_ptr c _ => valid_capability m c
  end.

Definition get_lo_pointer (ptr: pointer) : Z :=
  match ptr with
  | int_ptr b ofs => ofs
  | cap_ptr c => Ptrofs.unsigned (get_lo c)
  | Ucap_ptr c ofs => Ptrofs.unsigned (get_lo c)
  end.

Definition get_hi_pointer (ptr: pointer) : Z :=
  match ptr with
  | int_ptr b ofs => ofs + 1
  | cap_ptr c => Ptrofs.unsigned (get_hi c)
  | Ucap_ptr c ofs => Ptrofs.unsigned (get_hi c)
  end.

Axiom valid_pointer_nonempty_perm:
  forall m ptr b,
    get_mem_block ptr = Some b ->
    valid_pointer m ptr = true <-> (forall ofs, (get_lo_pointer ptr) <= ofs < (get_hi_pointer ptr)
                                         -> perm (infer_mem_kind ptr) m b ofs Cur Nonempty).


(** [dynamic_conditions ptr] defines the dynamic conditions not
    captured by [valid_pointer] *)

Definition dynamic_conditions (m: mem) (ptr: pointer) (cp: option compartment) (o: option ocval) (len: nat) (ptr': pointer) : Prop :=
  match ptr,ptr' with
  | int_ptr b ofs,_ => ptr = ptr' /\ can_access_block m b cp /\ can_store_val o
  | cap_ptr c,_ => ptr = ptr' /\ dynamic_access_stack c len o
  | Ucap_ptr c ofs,Ucap_ptr c' ofs' => if ofs =? 0 then ofs' = - (Z.of_nat len) else True /\ dynamic_access_stackU c ofs o len c'
  | _,_ => False
  end.

Axiom valid_pointer_valid_access:
  forall m ptr cp o chunk ptr',
    dynamic_conditions m ptr cp o chunk ptr' ->
    valid_pointer m ptr = true <-> valid_access m CMint8unsigned ptr Nonempty cp o ptr'.


(* TODO: discuss weak valid pointers in the presence of
capabilities. My intuition tells me we do NOT want to allow this for
the stack pointer *)
(** C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)

Definition weak_valid_pointer (m: mem) (b: block) (ofs: Z) :=
  valid_heap_pointer m b ofs || valid_heap_pointer m b (ofs - 1).

Axiom weak_valid_pointer_spec:
  forall m b ofs,
  weak_valid_pointer m b ofs = true <->
    valid_heap_pointer m b ofs = true \/ valid_heap_pointer m b (ofs - 1) = true.
Axiom valid_pointer_implies:
  forall m b ofs,
  valid_heap_pointer m b ofs = true -> weak_valid_pointer m b ofs = true.

(** * Properties of the memory operations *)

(** ** Properties of the initial memory state. *)

(** Heap *)
Axiom nextblock_empty: nextblock empty = 1%positive.
Axiom perm_empty: forall b ofs k p, ~perm HEAP empty b ofs k p.
Axiom valid_access_empty:
  forall chunk ptr p cp o p', ~valid_access empty chunk ptr p cp o p'.

(** Stack *)
Axiom nextframe_empty: nextframe empty = 1%positive.
Axiom stack_perm_empty: forall b ofs k p, ~perm STACK empty b ofs k p.
Axiom valid_access_stack_empty:
  forall chunk f c p o p', ~valid_access empty chunk f c p o p'.

(** ** Properties of [load]. *)

(** A load succeeds if and only if the access is valid for reading *)
Axiom valid_access_load:
  forall m chunk ptr cp k,
  valid_access m chunk ptr Readable cp None ptr ->
  exists v, load k chunk m ptr cp  = inl v.
Axiom load_valid_access:
  forall m chunk ptr cp v k,
  load k chunk m ptr cp = inl v ->
  valid_access m chunk ptr Readable cp None ptr.

(** If a stack load fails but the capability is valid, the error must be a load error *)
Axiom valid_capability_stkload_error:
  forall m c err,
    load STACK CMint8unsigned m c None = inr err ->
    valid_pointer m c = true ->
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
  forall k m ptr b ofs len cp,
    infer_ofs ptr = Some ofs ->
    get_mem_block ptr = Some b ->
    range_perm k m b ofs (ofs + Z.of_nat len) Cur Readable ->
    dynamic_conditions m ptr cp None len ptr ->
    exists bytes, loadbytes k m ptr (Z.of_nat len) cp = inl bytes.
Axiom loadbytes_range_perm:
  forall k m ptr b ofs len cp bytes,
    infer_ofs ptr = Some ofs ->
    get_mem_block ptr = Some b ->
    loadbytes k m ptr len cp = inl bytes ->
    range_perm k m b ofs (ofs + len) Cur Readable.


(** If [loadbytes] succeeds, the corresponding [load] succeeds and
  returns a value that is determined by the
  bytes read by [loadbytes]. *)
Axiom loadbytes_load:
  forall k chunk m ptr cp bytes ofs,
    infer_ofs ptr = Some ofs ->
    loadbytes k m ptr (size_chunk chunk) cp = inl bytes ->
    (align_chunk chunk | ofs) ->
    load k chunk m ptr cp = inl (decode_val chunk bytes).

(** Conversely, if [load] returns a value, the corresponding
  [loadbytes] succeeds and returns a list of bytes which decodes into the
  result of [load]. *)
Axiom load_loadbytes:
  forall k chunk m ptr cp v ofs,
    infer_ofs ptr = Some ofs ->
    load k chunk m ptr cp = inl v ->
    exists bytes, loadbytes k m ptr (size_chunk chunk) cp = inl bytes
             /\ v = decode_val chunk bytes.

(** [loadbytes] returns a list of length [n] (the number of bytes read). *)
Axiom loadbytes_length:
  forall k m ptr n cp bytes,
  loadbytes k m ptr n cp = inl bytes ->
  length bytes = Z.to_nat n.

Axiom loadbytes_empty:
  forall m ptr n cp k chunk,
  n <= 0 ->
  dynamic_conditions m ptr cp None chunk ptr ->
  loadbytes k m ptr n cp = inl nil.

(** Composing or decomposing [loadbytes] operations at adjacent addresses. *)
Definition incr_pointer (ptr: pointer) (n: Z) : option pointer :=
  match ptr with
  | int_ptr b ofs => Some (int_ptr b (ofs + n))
  | cap_ptr c => option_map (fun c => cap_ptr c) (incr_addr_stk c (Ptrofs.repr n))
  | Ucap_ptr c ofs => Some (Ucap_ptr c (ofs + n))
  end.

Axiom loadbytes_concat:
  forall k m ptr1 ptr2 n1 n2 cp bytes1 bytes2,
    incr_pointer ptr1 n1 = Some ptr2 ->
    loadbytes k m ptr1 n1 cp = inl bytes1 ->
    loadbytes k m ptr2 n2 cp = inl bytes2 ->
    n1 >= 0 -> n2 >= 0 ->
    loadbytes k m ptr1 (n1 + n2) cp = inl(bytes1 ++ bytes2).
Axiom loadbytes_split:
  forall k m ptr n1 n2 cp bytes,
  loadbytes k m ptr (n1 + n2) cp = inl bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2, exists ptr2,
    incr_pointer ptr n1 = Some ptr2
    /\ loadbytes k m ptr n1 cp = inl bytes1
    /\ loadbytes k m ptr2 n2 cp = inl bytes2
    /\ bytes = bytes1 ++ bytes2.


(** ** Properties of [store]. *)

(** [store] preserves block validity, permissions, access validity,
  compartments, and bounds.  Moreover, a [store] succeeds if and only if the
  corresponding access is valid for writing. *)

Axiom nextblock_store:
  forall k chunk m1 ptr v cp m2 ptr',
    store k chunk m1 ptr v cp = inl (ptr',m2) ->
    nextblock m2 = nextblock m1.
Axiom nextbframe_stkstore:
  forall k chunk m1 ptr v m2 cp ptr',
    store k chunk m1 ptr v cp = inl (ptr',m2) ->
    nextframe m2 = nextframe m1.

Axiom store_valid_block_1:
  forall k chunk m1 ptr v cp m2 ptr',
    store k chunk m1 ptr v cp = inl (ptr',m2) ->
    forall b', valid_block m1 b' -> valid_block m2 b'.
Axiom store_valid_block_2:
  forall k chunk m1 ptr v cp m2 ptr',
    store k chunk m1 ptr v cp = inl (ptr',m2) ->
    forall b', valid_block m2 b' -> valid_block m1 b'.

Axiom perm_store_1:
  forall mk chunk m1 ptr v cp m2 ptr',
    store mk chunk m1 ptr v cp = inl (ptr',m2) ->
    forall mk b' ofs' k p, perm mk m1 b' ofs' k p -> perm mk m2 b' ofs' k p.
Axiom perm_store_2:
  forall mk chunk m1 ptr v cp m2 ptr',
    store mk chunk m1 ptr v cp = inl (ptr',m2) ->
  forall mk b' ofs' k p, perm mk m2 b' ofs' k p -> perm mk m1 b' ofs' k p.


Axiom valid_access_store:
  forall m1 chunk ptr cp v k ptr',
  valid_access m1 chunk ptr Writable (Some cp) (Some v) ptr' ->
  { m2: mem | store k chunk m1 ptr v cp = inl (ptr',m2) }.
Axiom store_valid_access_1:
  forall k chunk m1 ptr v cp m2 ptr', store k chunk m1 ptr v cp = inl (ptr',m2) ->
  forall chunk' p perm cp' v' p',
  valid_access m1 chunk' p perm cp' v' p' -> valid_access m2 chunk' p perm cp' v' p'.
Axiom store_valid_access_2:
  forall k chunk m1 ptr v cp m2 ptr', store k chunk m1 ptr v cp = inl (ptr',m2) ->
  forall chunk' p p' perm cp' v',
  valid_access m2 chunk' p perm cp' v' p' -> valid_access m1 chunk' p perm cp' v' p'.
Axiom store_valid_access_3:
  forall k chunk m1 ptr v cp m2 ptr', store k chunk m1 ptr v cp = inl (ptr',m2) ->
  valid_access m1 chunk ptr Writable (Some cp) (Some v) ptr'.

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

Axiom load_store_same:
  forall k chunk m1 ptr v cp m2 ptr', store k chunk m1 ptr v cp = inl (ptr',m2) ->
  load k chunk m2 ptr' (Some cp) = inl (Val.load_result chunk v).

Axiom load_store_other:
  forall k chunk m1 ptr v cp m2 b ofs ptr2,
    store k chunk m1 ptr v cp = inl (ptr2,m2) ->
    infer_ofs ptr = Some ofs ->
    get_mem_block ptr = Some b ->
    forall k' chunk' ptr' cp' b' ofs',
      infer_ofs ptr' = Some ofs' ->
      get_mem_block ptr' = Some b' ->
      b' <> b
      \/ k' <> k
      \/ ofs' + size_chunk chunk' <= ofs
      \/ ofs + size_chunk chunk <= ofs' ->
      load k' chunk' m2 ptr' cp' = load k' chunk' m1 ptr' cp'.

(** Integrity of pointer values. *)

Definition compat_pointer_chunks (chunk1 chunk2: cap_memory_chunk) (storev: ocval) : Prop :=
  match chunk1, chunk2, storev with
  | (CMint32 | CMany32), (CMint32 | CMany32), OCVptr _ _ => True
  | (CMint64 | CMany64), (CMint64 | CMany64), OCVptr _ _ => True
  | (CMcap64 | CMany64), (CMcap64 | CMany64), OCVcap _ => True
  | (CMcap128 | CMany128), (CMcap128 | CMany128), OCVcap _ => True
  | _, _, _ => False
  end.

Definition is_pointer (v: ocval) : bool :=
  match v with
  | OCVptr _ _ | OCVcap _ => true
  | _ => false
  end.

Axiom load_store_pointer_overlap:
  forall k chunk m1 ofs v1 v2 storev cp m2 chunk' ofs' cp' v ptr2,
  is_pointer storev = true ->
  store k chunk m1 v1 storev cp = inl (ptr2,m2) ->
  load k chunk' m2 v2 cp' = inl v ->
  infer_ofs v1 = Some ofs ->
  infer_ofs v2 = Some ofs' ->
  get_mem_block v1 = get_mem_block v2 ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = OCVundef.
Axiom load_store_pointer_mismatch:
  forall k chunk m1 ptr storev cp m2 chunk' cp' v ptr',
  is_pointer storev = true ->
  store k chunk m1 ptr storev cp = inl (ptr',m2) ->
  load k chunk' m2 ptr' cp' = inl v ->
  ~compat_pointer_chunks chunk chunk' storev ->
  v = OCVundef.
Axiom load_pointer_store:
  forall k chunk m1 ptr b ofs v cp m2 chunk' ptr' b' ofs' cp' v' ptr2,
  is_pointer v = true ->
  get_mem_block ptr = Some b ->
  infer_ofs ptr = Some ofs ->
  get_mem_block ptr' = Some b' ->
  infer_ofs ptr' = Some ofs' ->
  store k chunk m1 ptr v cp = inl (ptr2,m2) ->
  load k chunk' m2 ptr' cp' = inl v' ->
  (v = v' /\ compat_pointer_chunks chunk chunk' v /\ b' = b /\ ofs = ofs')
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').

(** Load-store properties for [loadbytes]. *)

Axiom loadbytes_store_same:
  forall k chunk m1 ptr v cp ptr' m2, store k chunk m1 ptr v cp = inl (ptr',m2) ->
  loadbytes k m2 ptr' (size_chunk chunk) (Some cp) = inl(encode_val chunk v).
Axiom loadbytes_store_other:
  forall k chunk m1 p v cp m2 ptr2, store k chunk m1 p v cp = inl (ptr2,m2) ->
  forall k p' b' ofs' b ofs n cp',
  get_mem_block p' = Some b' -> get_mem_block p = Some b ->
  infer_ofs p' = Some ofs' -> infer_ofs p = Some ofs ->
  b' <> b \/ n <= 0 \/ ofs' + n <= ofs \/ ofs + size_chunk chunk <= ofs' ->
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
  forall k m1 ptr b ofs bytes cp ptr' chunk,
    get_mem_block ptr = Some b ->
    infer_ofs ptr = Some ofs ->
    range_perm k m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable ->
    length bytes = size_chunk_nat chunk ->
    dynamic_conditions m1 ptr (Some cp) (Some (decode_val chunk bytes)) (length bytes) ptr' ->
    { m2 : mem | storebytes k m1 ptr bytes cp = inl (ptr',m2) }.
Axiom storebytes_range_perm:
  forall k m1 ptr bytes cp ptr2 m2 b ofs,
    storebytes k m1 ptr bytes cp = inl (ptr2,m2) ->
    get_mem_block ptr = Some b ->
    infer_ofs ptr = Some ofs ->
    range_perm k m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable.
Axiom perm_storebytes_1:
  forall k m1 ptr bytes cp ptr2 m2, storebytes k m1 ptr bytes cp = inl (ptr2,m2) ->
  forall mk b' ofs' k p, perm mk m1 b' ofs' k p -> perm mk m2 b' ofs' k p.
Axiom perm_storebytes_2:
  forall k m1 ptr bytes cp ptr2 m2, storebytes k m1 ptr bytes cp = inl (ptr2,m2) ->
  forall mk b' ofs' k p, perm mk m2 b' ofs' k p -> perm mk m1 b' ofs' k p.
Axiom storebytes_valid_access_1:
  forall k m1 ptr bytes cp ptr2 m2, storebytes k m1 ptr bytes cp = inl (ptr2,m2) ->
  forall chunk' ptr' p cp' o ptr'',
  valid_access m1 chunk' ptr' p cp' (Some o) ptr'' -> valid_access m2 chunk' ptr' p cp' (Some o) ptr''.
Axiom storebytes_valid_access_2:
  forall k m1 ptr bytes cp ptr2 m2, storebytes k m1 ptr bytes cp = inl (ptr2,m2) ->
  forall chunk' ptr' p cp' o ptr'',
  valid_access m2 chunk' ptr' p cp' (Some o) ptr'' -> valid_access m1 chunk' ptr' p cp' (Some o) ptr''.
Axiom nextblock_storebytes:
  forall k m1 ptr bytes cp ptr2 m2, storebytes k m1 ptr bytes cp = inl (ptr2,m2) ->
  nextblock m2 = nextblock m1.
Axiom storebytes_valid_block_1:
  forall k m1 ptr bytes cp ptr2 m2, storebytes k m1 ptr bytes cp = inl (ptr2,m2) ->
  forall b', valid_block m1 b' -> valid_block m2 b'.
Axiom storebytes_valid_block_2:
  forall k m1 ptr bytes cp ptr2 m2, storebytes k m1 ptr bytes cp = inl (ptr2,m2) ->
  forall b', valid_block m2 b' -> valid_block m1 b'.

(** Connections between [store] and [storebytes]. *)

Axiom storebytes_store:
  forall k m1 ptr chunk v cp ptr2 m2 ofs,
  infer_ofs ptr = Some ofs ->
  storebytes k m1 ptr (encode_val chunk v) cp = inl (ptr2,m2) ->
  (align_chunk chunk | ofs) ->
  store k chunk m1 ptr v cp = inl (ptr2,m2).

Axiom store_storebytes:
  forall k m1 ptr chunk v cp ptr2 m2 ofs,
  infer_ofs ptr = Some ofs ->
  store k chunk m1 ptr v cp = inl (ptr2,m2) ->
  storebytes k m1 ptr (encode_val chunk v) cp = inl (ptr2,m2).

(** Load-store properties. *)

Axiom loadbytes_storebytes_same:
  forall k m1 ptr bytes cp ptr2 m2, storebytes k m1 ptr bytes cp = inl (ptr2,m2) ->
  loadbytes k m2 ptr2 (Z.of_nat (length bytes)) (Some cp) = inl bytes.
Axiom loadbytes_storebytes_other:
  forall k m1 ptr bytes cp ptr2 m2 b ofs,
    storebytes k m1 ptr bytes cp = inl (ptr2,m2) ->
    get_mem_block ptr = Some b ->
    infer_ofs ptr = Some ofs ->
  forall k' ptr' b' ofs' len cp',
  get_mem_block ptr' = Some b' ->
  infer_ofs ptr' = Some ofs' ->
  len >= 0 ->
  b' <> b
  \/ ofs' + len <= ofs
  \/ ofs + Z.of_nat (length bytes) <= ofs' ->
  loadbytes k' m2 ptr' len cp' = loadbytes k' m1 ptr' len cp'.
Axiom load_storebytes_other:
  forall k m1 ptr bytes cp ptr2 m2 b ofs,
    storebytes k m1 ptr bytes cp = inl (ptr2,m2) ->
    get_mem_block ptr = Some b ->
    infer_ofs ptr = Some ofs ->
  forall k' chunk ptr' b' ofs' cp',
  get_mem_block ptr' = Some b' -> 
  infer_ofs ptr' = Some ofs' ->
  b' <> b
  \/ ofs' + size_chunk chunk <= ofs
  \/ ofs + Z.of_nat (length bytes) <= ofs' ->
  load k' chunk m2 ptr' cp' = load k' chunk m1 ptr' cp'.

(** Composing or decomposing [storebytes] operations at adjacent addresses. *)

Axiom storebytes_concat:
  forall k m ptr bytes1 cp ptr1 m1 bytes2 ptr2 m2 ptr',
  incr_pointer ptr (Z.of_nat(length bytes1)) = Some ptr' ->
  storebytes k m ptr bytes1 cp = inl (ptr1,m1) ->
  storebytes k m1 ptr' bytes2 cp = inl (ptr2,m2) ->
  storebytes k m ptr (bytes1 ++ bytes2) cp = inl (ptr2,m2).
Axiom storebytes_split:
  forall k m ptr bytes1 bytes2 cp ptr2 m2,
  storebytes k m ptr (bytes1 ++ bytes2) cp = inl (ptr2,m2) ->
  exists ptr' ptr1 m1,
    storebytes k m ptr bytes1 cp = inl (ptr1,m1)
    /\ incr_pointer ptr (Z.of_nat(length bytes1)) = Some ptr'
    /\ storebytes k m1 ptr' bytes2 cp = inl (ptr2,m2).

(** ** Properties of [alloc]. *)

(** The identifier of the freshly allocated block is the next block
  of the initial memory state. *)

Axiom alloc_result:
  forall k m1 c lo hi m2 ptr b,
    alloc k m1 c lo hi = (m2, ptr) ->
    get_mem_block ptr = Some b ->
    match b with
    | heap_block b => b = nextblock m1
    | stack_block f => f = nextframe m1
    end.

Axiom alloc_block:
  forall k m1 c lo hi m2 ptr,
    alloc k m1 c lo hi = (m2, ptr) ->
    exists b, get_mem_block ptr = Some b.

(** Effect of [alloc] on block validity. *)

Axiom nextblock_alloc:
  forall k m1 c lo hi m2 b,
    alloc k m1 c lo hi = (m2, b) ->
    nextblock m2 = Pos.succ (nextblock m1).
Axiom nextframe_alloc:
  forall k m1 c lo hi m2 b,
    alloc k m1 c lo hi = (m2, b) ->
    nextframe m2 = Pos.succ (nextframe m1).

Axiom valid_block_alloc:
  forall k m1 c lo hi m2 b, alloc k m1 c lo hi = (m2, b) ->
  forall b', valid_block m1 b' -> valid_block m2 b'.
Axiom fresh_block_alloc:
  forall k m1 c lo hi m2 ptr b,
    alloc k m1 c lo hi = (m2, ptr) ->
    get_mem_block ptr = Some b ->
    ~(valid_block m1 b).
Axiom valid_new_block:
  forall k m1 c lo hi m2 ptr b,
    alloc k m1 c lo hi = (m2, ptr) ->
    get_mem_block ptr = Some b ->
    valid_block m2 b.
Axiom valid_block_alloc_inv:
  forall k m1 c lo hi m2 ptr b,
    alloc k m1 c lo hi = (m2, ptr) ->
    get_mem_block ptr = Some b ->
    forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.

(** Effect of [alloc] on permissions. *)

Axiom perm_alloc_1:
  forall k m1 c lo hi m2 ptr b,
    alloc k m1 c lo hi = (m2, ptr) ->
    get_mem_block ptr = Some b ->
    forall mk b' ofs k p, perm mk m1 b' ofs k p -> perm mk m2 b' ofs k p.
Axiom perm_alloc_2:
  forall k m1 c lo hi m2 ptr b,
    alloc k m1 c lo hi = (m2, ptr) ->
    get_mem_block ptr = Some b ->
    forall ofs x, lo <= ofs < hi -> perm k m2 b ofs x Freeable.
Axiom perm_alloc_3:
  forall k m1 c lo hi m2 ptr b,
    alloc k m1 c lo hi = (m2, ptr) ->
    get_mem_block ptr = Some b ->
    forall ofs x p, perm k m2 b ofs x p -> lo <= ofs < hi.
Axiom perm_alloc_4:
  forall k m1 c lo hi m2 ptr b,
    alloc k m1 c lo hi = (m2, ptr) ->
    get_mem_block ptr = Some b ->
    forall k' b' ofs x p, perm k' m2 b' ofs x p -> b' <> b \/ k <> k' -> perm k' m1 b' ofs x p.
Axiom perm_alloc_inv:
  forall k m1 c lo hi m2 ptr b,
    alloc k m1 c lo hi = (m2, ptr) ->
    get_mem_block ptr = Some b ->
    forall k' b' ofs x p,
      perm k' m2 b' ofs x p ->
      if eq_mem_block b' b && eq_mem_kind k k' then lo <= ofs < hi else perm k' m1 b' ofs x p.

(** Effect of [alloc] on compartments. *)

Axiom alloc_block_compartment:
  forall m1 c lo hi m2 ptr b,
    alloc HEAP m1 c lo hi = (m2, ptr) ->
    get_mem_block ptr = Some b ->
    forall b', block_compartment m2 b' =
            if eq_mem_block (heap_block b') b then Some c else block_compartment m1 b'.

(** Effect of [alloc] on access validity. *)

Axiom valid_access_alloc_other:
  forall k m1 c lo hi m2 ptr, alloc k m1 c lo hi = (m2, ptr) ->
  forall chunk ptr' p cp' o ptr'',
  valid_access m1 chunk ptr' p cp' o ptr'' ->
  valid_access m2 chunk ptr' p cp' o ptr''.
Axiom valid_access_alloc_same:
  forall k m1 c lo hi m2 ptr b,
    alloc k m1 c lo hi = (m2, ptr) ->
    get_mem_block ptr = Some b ->
    forall chunk ptr' ofs o ptr'',
      dynamic_conditions m2 ptr' (Some c) o (size_chunk_nat chunk) ptr'' ->
      get_mem_block ptr' = Some b -> infer_ofs ptr' = Some ofs ->
      lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
      valid_access m2 chunk ptr' Freeable (Some c) o ptr''.
Axiom valid_access_alloc_inv:
  forall k m1 c lo hi m2 ptr b,
    alloc k m1 c lo hi = (m2, ptr) ->
    get_mem_block ptr = Some b ->
    forall chunk ptr' p c' o ptr'' b' ofs,
      get_mem_block ptr' = Some b' ->
      infer_ofs ptr' = Some ofs ->
      valid_access m2 chunk ptr' p c' o ptr'' ->
      if eq_mem_block b' b && eq_mem_kind k (infer_mem_kind ptr')
      then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
           /\ dynamic_conditions m2 ptr' (Some c) o (size_chunk_nat chunk) ptr''
      else valid_access m1 chunk ptr' p c' o ptr''.

(** Load-alloc properties. *)

Axiom load_alloc_unchanged:
  forall k m1 c lo hi m2 ptr,
    alloc k m1 c lo hi = (m2, ptr) ->
    forall k chunk ptr' b' c' ,
      get_mem_block ptr' = Some b' ->
      valid_block m1 b' ->
      load k chunk m2 ptr' c' = load k chunk m1 ptr' c'.
Axiom load_alloc_other:
  forall k m1 c lo hi m2 ptr, alloc k m1 c lo hi = (m2, ptr) ->
  forall k chunk ptr' c' v,
  load k chunk m1 ptr' c' = inl v ->
  load k chunk m2 ptr' c' = inl v.
Axiom load_alloc_same:
  forall m1 c lo hi m2 ptr b,
    alloc HEAP m1 c lo hi = (m2, ptr) ->
    get_mem_block ptr = Some (heap_block b) ->
    forall chunk ofs c' v,
      load HEAP chunk m2 (int_ptr b ofs) c' = inl v ->
      v = OCVundef.
(** the stack pointer to a fresh frame starts out fully uninitialized
    and cannot be loaded from *)
Axiom load_alloc_same_stack:
  forall m1 c lo hi m2 ptr,
    alloc STACK m1 c lo hi = (m2, ptr) ->
    forall chunk c' err,
      load STACK chunk m2 ptr c' = inr err.
Axiom load_alloc_same':
  forall m1 c lo hi m2 ptr b,
    alloc HEAP m1 c lo hi = (m2, ptr) ->
    get_mem_block ptr = Some (heap_block b) ->
    forall chunk ofs,
      lo <= ofs -> ofs + size_chunk chunk <= hi ->
      can_access_block m2 b (Some c) ->
      (align_chunk chunk | ofs) ->
      load HEAP chunk m2 (int_ptr b  ofs) (Some c) = inl OCVundef.

(** ** Properties of [free]. *)

(** [free] succeeds if and only if the correspond range of addresses
  has [Freeable] current permission. *)

Axiom range_perm_free:
  forall m1 b lo hi cp,
  range_perm HEAP m1 (heap_block b) lo hi Cur Freeable ->
  can_access_block m1 b (Some cp) ->
  { m2: mem | free HEAP m1 (heap_block b) lo hi cp = inl m2 }.
Axiom range_perm_free_stack:
  forall m1 b lo hi cp,
  range_perm STACK m1 b lo hi Cur Freeable ->
  { m2: mem | free STACK m1 b lo hi cp = inl m2 }.
Axiom free_range_perm:
  forall k m1 bf lo hi cp m2, free k m1 bf lo hi cp = inl m2 ->
  range_perm k m1 bf lo hi Cur Freeable.

(** Block validity is preserved by [free]. *)

Axiom nextblock_free:
  forall k m1 bf lo hi cp m2, free k m1 bf lo hi cp = inl m2 ->
  nextblock m2 = nextblock m1.
Axiom nextframe_free:
  forall k m1 bf lo hi cp m2, free k m1 bf lo hi cp = inl m2 ->
  nextframe m2 = nextframe m1.
Axiom valid_block_free_1:
  forall k m1 bf lo hi cp m2, free k m1 bf lo hi cp = inl m2 ->
  forall b, valid_block m1 b -> valid_block m2 b.
Axiom valid_block_free_2:
  forall k m1 bf lo hi cp m2, free k m1 bf lo hi cp = inl m2 ->
  forall b, valid_block m2 b -> valid_block m1 b.

(** Effect of [free] on permissions. *)

Axiom perm_free_1:
  forall k m1 bf lo hi cp m2, free k m1 bf lo hi cp = inl m2 ->
  forall mk b ofs k p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm mk m1 b ofs k p ->
  perm mk m2 b ofs k p.
Axiom perm_free_2:
  forall k m1 bf lo hi cp m2, free k m1 bf lo hi cp = inl m2 ->
  forall mk ofs k p, lo <= ofs < hi -> ~ perm mk m2 bf ofs k p.
Axiom perm_free_3:
  forall k m1 bf lo hi cp m2, free k m1 bf lo hi cp = inl m2 ->
  forall mk b ofs k p,
  perm mk m2 b ofs k p -> perm mk m1 b ofs k p.

(** Effect of [free] on access validity. *)

Axiom valid_access_free_1:
  forall k m1 bf lo hi cp m2,
    free k m1 bf lo hi cp = inl m2 ->
    forall chunk ptr p cp' o ptr' b ofs,
      get_mem_block ptr = Some b ->
      infer_ofs ptr = Some ofs ->
      valid_access m1 chunk ptr p cp' o ptr' ->
      b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
      valid_access m2 chunk ptr p cp' o ptr'.
Axiom valid_access_free_2:
  forall k m1 bf lo hi cp m2,
    free k m1 bf lo hi cp = inl m2 ->
    forall chunk ptr p cp' b ofs o ptr',
      get_mem_block ptr = Some b ->
      infer_ofs ptr = Some ofs ->
      lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
      ~(valid_access m2 chunk ptr p cp' o ptr') .
Axiom valid_access_free_inv_1:
  forall k m1 bf lo hi cp m2, free k m1 bf lo hi cp = inl m2 ->
  forall chunk ptr p cp' o ptr',
  valid_access m2 chunk ptr p cp' o ptr' ->
  valid_access m1 chunk ptr p cp' o ptr'.
Axiom valid_access_free_inv_2:
  forall k m1 bf lo hi cp m2,
    free k m1 bf lo hi cp = inl m2 ->
    forall chunk ptr p cp' o ptr' ofs,
      get_mem_block ptr = Some bf ->
      infer_ofs ptr = Some ofs ->
      valid_access m2 chunk ptr p cp' o ptr' ->
      lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.

(** Load-free properties *)

Axiom load_free:
  forall k m1 bf lo hi cp m2,
    free k m1 bf lo hi cp = inl m2 ->
    forall k chunk ptr b ofs cp',
      get_mem_block ptr = Some b ->
      infer_ofs ptr = Some ofs ->
      b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
      load k chunk m2 ptr cp' = load k chunk m1 ptr cp'.

(** ** Properties of [drop_perm]. *)

Axiom nextblock_drop:
  forall k m b lo hi p cp m', drop_perm k m b lo hi p cp = inl m' ->
  nextblock m' = nextblock m.
Axiom drop_perm_valid_block_1:
  forall k m b lo hi p cp m', drop_perm k m b lo hi p cp = inl m' ->
  forall b', valid_block m b' -> valid_block m' b'.
Axiom drop_perm_valid_block_2:
  forall k m b lo hi p cp m', drop_perm k m b lo hi p cp = inl m' ->
  forall b', valid_block m' b' -> valid_block m b'.

Axiom drop_block_compartment:
  forall k m b lo hi p cp m', drop_perm k m b lo hi p cp = inl m' ->
  forall b', block_compartment m' b' = block_compartment m b'.

Axiom range_perm_drop_1:
  forall k m b lo hi p cp m', drop_perm k m b lo hi p cp = inl m' ->
  range_perm k m b lo hi Cur Freeable.
Axiom range_perm_drop_2_heap:
  forall m b lo hi cp p,
  range_perm HEAP m (heap_block b) lo hi Cur Freeable ->
  can_access_block m b (Some cp) ->
  { m' | drop_perm HEAP m (heap_block b) lo hi p cp = inl m' }.
Axiom range_perm_drop_2_stack:
  forall m b lo hi cp p,
  range_perm STACK m b lo hi Cur Freeable ->
  { m' | drop_perm STACK m b lo hi p cp = inl m' }.

Axiom perm_drop_1:
  forall mk m b lo hi p cp m', drop_perm mk m b lo hi p cp = inl m' ->
  forall ofs k, lo <= ofs < hi -> perm mk m' b ofs k p.
Axiom perm_drop_2:
  forall mk m b lo hi p cp m', drop_perm mk m b lo hi p cp = inl m' ->
  forall ofs k p', lo <= ofs < hi -> perm mk m' b ofs k p' -> perm_order p p'.
Axiom perm_drop_3:
  forall mk m b lo hi p cp m', drop_perm mk m b lo hi p cp = inl m' ->
  forall mk' b' ofs k p', b' <> b \/ mk <> mk' \/ ofs < lo \/ hi <= ofs -> perm mk' m b' ofs k p' -> perm mk' m' b' ofs k p'.
Axiom perm_drop_4:
  forall mk m b lo hi p cp m', drop_perm mk m b lo hi p cp = inl m' ->
  forall mk b' ofs k p', perm mk m' b' ofs k p' -> perm mk m b' ofs k p'.

Axiom load_drop:
  forall mk m b lo hi p cp m', drop_perm mk m b lo hi p cp = inl m' ->
  forall mk' chunk ptr b' ofs cp', get_mem_block ptr = Some b' -> infer_ofs ptr = Some ofs ->
  b' <> b \/ mk <> mk' \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load mk' chunk m' ptr cp' = load mk' chunk m ptr cp'.


End MEM.
