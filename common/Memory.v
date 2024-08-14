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
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
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
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Split.
Require Export Memdata.
Require Export Memtype.

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

Record mem' : Type := mkmem {
  mem_contents: PMap.t (ZMap.t memval);  (**r [block -> offset -> memval] *)
  mem_access: PMap.t (Z -> perm_kind -> option permission);
                                         (**r [block -> offset -> kind -> option permission] *)
  mem_compartments: PMap.t (compartment); (**r [block -> compartment] *)
  nextblock: block;
  access_max:
    forall b ofs, perm_order'' (mem_access#b ofs Max) (mem_access#b ofs Cur);
  nextblock_noaccess:
    forall b ofs k, ~(Plt b nextblock) -> mem_access#b ofs k = None;
  contents_default:
    forall b, fst mem_contents#b = Undef;
  nextblock_compartments:
    forall b, ~Plt b nextblock -> mem_compartments#b = top;
}.

Definition mem := mem'.

Lemma mkmem_ext:
 forall cont1 cont2 acc1 acc2 comp1 comp2 next1 next2,
 forall a1 a2 b1 b2 c1 c2 d1 d2,
  cont1=cont2 -> acc1=acc2 -> comp1=comp2 -> next1=next2 ->
  mkmem cont1 acc1 comp1 next1 a1 b1 c1 d1 =
  mkmem cont2 acc2 comp2 next2 a2 b2 c2 d2.
Proof.
  intros. subst. f_equal; apply proof_irr.
Qed.

(** * Validity of blocks and accesses *)

(** A block address is valid if it was previously allocated. It remains valid
  even after being freed. *)

Definition valid_block (m: mem) (b: block) := Plt b (nextblock m).

Theorem valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.
Proof.
  intros; red; intros. subst b'. contradiction.
Qed.

Local Hint Resolve valid_not_valid_diff: mem.

(** [block_compartment m b] returns the compartment associated with the block
  [b] in the memory [m], or [None] if [b] is not allocated in [m]. *)

Definition block_compartment (m: mem) (b: block) :=
  m.(mem_compartments)#b.

Theorem block_compartment_valid_block:
  forall m b,
  ~valid_block m b ->
  block_compartment m b = top.
Proof.
  apply nextblock_compartments.
Qed.

Definition val_compartment (m: mem) (v: val): compartment :=
  match v with
  | Vptr b _ => block_compartment m b
  | _ => top
  end.

(* Lemma nextblock_compartments_pos: *)
(*   forall m b, *)
(*   Plt b (nextblock m) <-> exists cp, block_compartment m b = Some cp. *)
(* Proof. *)
(*   unfold block_compartment. intros m b. split; intro H. *)
(*   - destruct ((mem_compartments m) ! b) as [cp |] eqn:Hcase. *)
(*     + exists cp. reflexivity. *)
(*     + apply nextblock_compartments in Hcase. contradiction. *)
(*   - destruct (plt b (nextblock m)) as [Hlt | Hlt]. *)
(*     + assumption. *)
(*     + apply PTree.get_not_none_get_some in H. *)
(*       pose proof nextblock_compartments m b as Hcomp. *)
(*       apply not_iff_compat in Hcomp. *)
(*       apply Hcomp in H. *)
(*       contradiction. *)
(* Qed. *)

(** Permissions *)

Definition perm (m: mem) (b: block) (ofs: Z) (k: perm_kind) (p: permission) : Prop :=
   perm_order' (m.(mem_access)#b ofs k) p.

Theorem perm_implies:
  forall m b ofs k p1 p2, perm m b ofs k p1 -> perm_order p1 p2 -> perm m b ofs k p2.
Proof.
  unfold perm, perm_order'; intros.
  destruct (m.(mem_access)#b ofs k); auto.
  eapply perm_order_trans; eauto.
Qed.

Local Hint Resolve perm_implies: mem.

Theorem perm_cur_max:
  forall m b ofs p, perm m b ofs Cur p -> perm m b ofs Max p.
Proof.
  assert (forall po1 po2 p,
          perm_order' po2 p -> perm_order'' po1 po2 -> perm_order' po1 p).
  unfold perm_order', perm_order''. intros.
  destruct po2; try contradiction.
  destruct po1; try contradiction.
  eapply perm_order_trans; eauto.
  unfold perm; intros.
  generalize (access_max m b ofs). eauto.
Qed.

Theorem perm_cur:
  forall m b ofs k p, perm m b ofs Cur p -> perm m b ofs k p.
Proof.
  intros. destruct k; auto. apply perm_cur_max. auto.
Qed.

Theorem perm_max:
  forall m b ofs k p, perm m b ofs k p -> perm m b ofs Max p.
Proof.
  intros. destruct k; auto. apply perm_cur_max. auto.
Qed.

Local Hint Resolve perm_cur perm_max: mem.

Theorem perm_valid_block:
  forall m b ofs k p, perm m b ofs k p -> valid_block m b.
Proof.
  unfold perm; intros.
  destruct (plt b m.(nextblock)).
  auto.
  assert (m.(mem_access)#b ofs k = None).
  eapply nextblock_noaccess; eauto.
  rewrite H0 in H.
  contradiction.
Qed.

Local Hint Resolve perm_valid_block: mem.

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
  forall m b ofs k p, {perm m b ofs k p} + {~ perm m b ofs k p}.
Proof.
  unfold perm; intros.
  apply perm_order'_dec.
Defined.

(* NOTE: RB: Keeping this limited to range checks instead of building in
   ownership checks as well. *)
Definition range_perm (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs k p.

Theorem range_perm_implies:
  forall m b lo hi k p1 p2,
  range_perm m b lo hi k p1 -> perm_order p1 p2 -> range_perm m b lo hi k p2.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Theorem range_perm_cur:
  forall m b lo hi k p,
  range_perm m b lo hi Cur p -> range_perm m b lo hi k p.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Theorem range_perm_max:
  forall m b lo hi k p,
  range_perm m b lo hi k p -> range_perm m b lo hi Max p.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Local Hint Resolve range_perm_implies range_perm_cur range_perm_max: mem.

Lemma range_perm_dec:
  forall m b lo hi k p, {range_perm m b lo hi k p} + {~ range_perm m b lo hi k p}.
Proof.
  intros.
  induction lo using (well_founded_induction_type (Zwf_up_well_founded hi)).
  destruct (zlt lo hi).
  destruct (perm_dec m b lo k p).
  destruct (H (lo + 1)). red. lia.
  left; red; intros. destruct (zeq lo ofs). congruence. apply r. lia.
  right; red; intros. elim n. red; intros; apply H0; lia.
  right; red; intros. elim n. apply H0. lia.
  left; red; intros. extlia.
Defined.

(** [can_access_block m b cp] holds if a component [cp] has control over block [b] in
    memory [m]. In the simple memory model without sharing, this simple means
    that [cp] is the compartment associated to [b] in [m]'s map from blocks to
    components.
*)

Definition can_access_block (m: mem) (b: block) (cp: compartment): Prop :=
  block_compartment m b ⊆ cp.

Arguments can_access_block /.

#[export] Hint Unfold can_access_block: comps.


Remark can_access_block_dec:
  forall m b cp, {can_access_block m b cp} + {~can_access_block m b cp}.
Proof.
  unfold can_access_block.
  intros m b cp.
  destruct (flowsto_dec (block_compartment m b) cp); auto.
Defined.

(** [valid_access m chunk b ofs p cp] holds if a memory access
    of the given chunk is possible in [m] at address [b, ofs]
    with current permissions [p] and from compartment [cp].
    This means:
- The range of bytes accessed all have current permission [p].
- The block [b] belongs to the accessing compartment [cp].
- The offset [ofs] is aligned.
*)

Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission) (cp: compartment): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) Cur p
  /\ can_access_block m b cp
  /\ (align_chunk chunk | ofs).

Theorem valid_access_implies:
  forall m chunk b ofs p1 cp p2,
  valid_access m chunk b ofs p1 cp -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2 cp.
Proof.
  intros. inv H. constructor; eauto with mem.
Qed.

Theorem valid_access_freeable_any:
  forall m chunk b ofs p cp,
  valid_access m chunk b ofs Freeable cp ->
  valid_access m chunk b ofs p cp.
Proof.
  intros.
  eapply valid_access_implies; eauto. constructor.
Qed.

Local Hint Resolve valid_access_implies: mem.

Theorem valid_access_valid_block:
  forall m chunk b ofs cp,
  valid_access m chunk b ofs Nonempty cp ->
  valid_block m b.
Proof.
  intros. destruct H.
  assert (perm m b ofs Cur Nonempty).
    apply H. generalize (size_chunk_pos chunk). lia.
  eauto with mem.
Qed.

Local Hint Resolve valid_access_valid_block: mem.

Lemma valid_access_perm:
  forall m chunk b ofs k p cp,
  valid_access m chunk b ofs p cp ->
  perm m b ofs k p.
Proof.
  intros. destruct H. apply perm_cur. apply H. generalize (size_chunk_pos chunk). lia.
Qed.

Lemma valid_access_compat:
  forall m chunk1 chunk2 b ofs p cp,
  size_chunk chunk1 = size_chunk chunk2 ->
  align_chunk chunk2 <= align_chunk chunk1 ->
  valid_access m chunk1 b ofs p cp ->
  valid_access m chunk2 b ofs p cp.
Proof.
  intros. inv H1. rewrite H in H2. destruct H3. constructor; auto.
  constructor; auto.
  eapply Z.divide_trans; eauto. eapply align_le_divides; eauto.
Qed.

Lemma valid_access_dec:
  forall m chunk b ofs p cp,
  {valid_access m chunk b ofs p cp} + {~ valid_access m chunk b ofs p cp}.
Proof.
  intros.
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Cur p).
  destruct (Zdivide_dec (align_chunk chunk) ofs).
  destruct (can_access_block_dec m b cp).
  left; constructor; auto.
  right; red; intro V; inversion V as [V1 [V2 V3]]; congruence.
  right; red; intro V; inversion V as [V1 [V2 V3]]; congruence.
  right; red; intro V; inversion V as [V1 [V2 V3]]; congruence.
Defined.

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)
Definition valid_pointer (m: mem) (b: block) (ofs: Z): bool :=
  perm_dec m b ofs Cur Nonempty.

Theorem valid_pointer_nonempty_perm:
  forall m b ofs,
  valid_pointer m b ofs = true <-> perm m b ofs Cur Nonempty.
Proof.
  intros. unfold valid_pointer.
  destruct (perm_dec m b ofs Cur Nonempty); simpl;
  intuition congruence.
Qed.

Theorem valid_pointer_valid_access:
  forall m b cp ofs,
    block_compartment m b ⊆ cp ->
    valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty cp.
Proof.
  intros. rewrite valid_pointer_nonempty_perm.
  split; intros.
  split. simpl; red; intros. replace ofs0 with ofs by lia. auto.
  split; [unfold can_access_block; auto with comps|].
  simpl. apply Z.divide_1_l.
  destruct H0. apply H0. simpl. lia.
Qed.

(* Theorem valid_pointer_valid_access_priv: *)
(*   forall m b ofs, *)
(*     valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty top. *)
(* Proof. *)
(*   intros. rewrite valid_pointer_nonempty_perm. *)
(*   split; intros. *)
(*   split. simpl; red; intros. replace ofs0 with ofs by lia. auto. *)
(*   split; auto. unfold can_access_block. destruct (block_compartment m b); auto with comps. *)
(*   simpl. apply Z.divide_1_l. *)
(*   destruct H. apply H. simpl. lia. *)
(* Qed. *)

(* Theorem valid_pointer_valid_access: *)
(*   forall m b cp ofs, *)
(*     can_access_block m b cp -> *)
(*     valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty cp. *)
(* Proof. *)
(*   intros. *)
(*   destruct (cp_eq_dec cp top); subst; auto using valid_pointer_valid_access_priv. *)
(*   destruct (Mem.block_compartment m b) eqn:?; *)
(*     auto using valid_pointer_valid_access_nonpriv, valid_pointer_valid_access_priv with comps. *)
(* Qed. *)

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

(** Some useful facts relating the various notions of validity and access
    permissions. *)

(* Theorem valid_block_can_access_block: *)
(*   forall m b, *)
(*   valid_block m b -> *)
(*   exists cp, *)
(*   can_access_block m b (Some cp). *)
(* Proof. *)
(*   unfold valid_block, can_access_block. intros m b Hvalid. *)
(*   apply nextblock_compartments_pos in Hvalid. *)
(*   assumption. *)
(* Qed. *)

Theorem valid_block_can_access_block_priv:
  forall m b,
  valid_block m b ->
  can_access_block m b top.
Proof.
  unfold can_access_block. intros. simpl; auto with comps.
Qed.

(* Theorem can_access_block_valid_block: *)
(*   forall m b cp, *)
(*   can_access_block m b cp -> *)
(*   valid_block m b. *)
(* Proof. *)
(*   unfold valid_block, can_access_block. intros m b cp Hown. *)
(*   apply nextblock_compartments_pos. exists cp. assumption. *)
(* Qed. *)

(* Theorem valid_pointer_can_access_block: *)
(*   forall m b ofs, *)
(*   valid_pointer m b ofs = true -> *)
(*   exists cp, *)
(*   can_access_block m b (Some cp). *)
(* Proof. *)
(*   unfold valid_pointer. intros m b ofs Hperm. *)
(*   destruct (perm_dec m b ofs Cur Nonempty) as [Hperm' | Hperm']; *)
(*     simpl in Hperm. *)
(*   - apply perm_valid_block in Hperm'. *)
(*     apply valid_block_can_access_block in Hperm'. *)
(*     assumption. *)
(*   - congruence. *)
(* Qed. *)

(** * Operations over memory stores *)

(** The initial store *)

Program Definition empty: mem :=
  mkmem (PMap.init (ZMap.init Undef))
        (PMap.init (fun ofs k => None))
        (PMap.init top)
        1%positive _ _ _ _.
(** Allocation of a fresh block with the given bounds.  Return an updated
  memory state and the address of the fresh block, which initially contains
  undefined cells.  Note that allocation never fails: we model an
  infinite memory. *)

Program Definition alloc (m: mem) (c: compartment) (lo hi: Z) :=
  (mkmem (PMap.set m.(nextblock)
                   (ZMap.init Undef)
                   m.(mem_contents))
         (PMap.set m.(nextblock)
                   (fun ofs k => if zle lo ofs && zlt ofs hi then Some Freeable else None)
                   m.(mem_access))
         (PMap.set m.(nextblock) c m.(mem_compartments))
         (Pos.succ m.(nextblock))
         _ _ _ _,
   m.(nextblock)).
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b (nextblock m)).
  subst b. destruct (zle lo ofs && zlt ofs hi); red; auto with mem.
  apply access_max.
Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b (nextblock m)).
  subst b. elim H. apply Plt_succ.
  apply nextblock_noaccess. red; intros; elim H.
  apply Plt_trans_succ; auto.
Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b (nextblock m)). auto. apply contents_default.
Qed.
Next Obligation.
  rewrite PMap.gsspec.
  destruct (peq b (nextblock m)) as [->|ne].
- exfalso. apply H. apply Plt_succ.
- erewrite <- nextblock_compartments. reflexivity.
  intros H'.
  apply H.
  now apply Plt_trans_succ.
Qed.

(** Freeing a block between the given bounds.
  Return the updated memory state where the given range of the given block
  has been invalidated: future reads and writes to this
  range will fail.  Requires freeable permission on the given range. *)

Program Definition unchecked_free (m: mem) (b: block) (lo hi: Z): mem :=
  if zle hi lo then m else
  mkmem m.(mem_contents)
        (PMap.set b
                (fun ofs k => if zle lo ofs && zlt ofs hi then None else m.(mem_access)#b ofs k)
                m.(mem_access))
        m.(mem_compartments)
        m.(nextblock) _ _ _ _.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b).
  destruct (zle lo ofs && zlt ofs hi). red; auto. apply access_max.
  apply access_max.
Qed.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b). subst.
  destruct (zle lo ofs && zlt ofs hi). auto. apply nextblock_noaccess; auto.
  apply nextblock_noaccess; auto.
Qed.
Next Obligation.
  apply contents_default.
Qed.
Next Obligation.
  eapply nextblock_compartments; eauto.
Qed.

Definition free (m: mem) (b: block) (lo hi: Z) (cp: compartment): option mem :=
  if Z_le_dec hi lo then Some m else
    if range_perm_dec m b lo hi Cur Freeable &&
         can_access_block_dec m b cp
    then Some(unchecked_free m b lo hi)
    else None.

(* RB: NOTE: Add compartments to each item in the list? *)
Fixpoint free_list (m: mem) (l: list (block * Z * Z)) (cp: compartment) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi cp with
      | None => None
      | Some m' => free_list m' l' cp
      end
  end.

(** Memory reads. *)

(** Reading N adjacent bytes in a block content. *)

Fixpoint getN (n: nat) (p: Z) (c: ZMap.t memval) {struct n}: list memval :=
  match n with
  | O => nil
  | S n' => ZMap.get p c :: getN n' (p + 1) c
  end.

(** [load chunk m b ofs cp] performs a read in memory state [m], at address
  [b] and offset [ofs], from compartment [cp].  It returns the value of the
  memory chunk at that address.  [None] is returned if the accessed bytes
  are not readable. *)

Definition load (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (cp: compartment): option val :=
  if valid_access_dec m chunk b ofs Readable cp
  then Some(decode_val chunk (getN (size_chunk_nat chunk) ofs (m.(mem_contents)#b)))
  else None.

(** [loadv chunk m addr cp] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) (cp: compartment) : option val :=
  match addr with
  | Vptr b ofs => load chunk m b (Ptrofs.unsigned ofs) cp
  | _ => None
  end.

(** [loadbytes m b ofs n cp] reads [n] consecutive bytes starting at
  location [(b, ofs)].  Returns [None] if the accessed locations are
  not readable. *)

Definition loadbytes (m: mem) (b: block) (ofs n: Z) (cp: compartment): option (list memval) :=
  if range_perm_dec m b ofs (ofs + n) Cur Readable &&
     (can_access_block_dec m b cp || Z_le_dec n 0)
  then Some (getN (Z.to_nat n) ofs (m.(mem_contents)#b))
  else None.

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
  apply IHvl. intros. apply H. lia.
  apply ZMap.gso. apply not_eq_sym. apply H. lia.
Qed.

Remark setN_outside:
  forall vl c p q,
  q < p \/ q >= p + Z.of_nat (length vl) ->
  ZMap.get q (setN vl p c) = ZMap.get q c.
Proof.
  intros. apply setN_other.
  intros. lia.
Qed.

Remark getN_setN_same:
  forall vl p c,
  getN (length vl) p (setN vl p c) = vl.
Proof.
  induction vl; intros; simpl.
  auto.
  decEq.
  rewrite setN_outside. apply ZMap.gss. lia.
  apply IHvl.
Qed.

Remark getN_exten:
  forall c1 c2 n p,
  (forall i, p <= i < p + Z.of_nat n -> ZMap.get i c1 = ZMap.get i c2) ->
  getN n p c1 = getN n p c2.
Proof.
  induction n; intros. auto. rewrite Nat2Z.inj_succ in H. simpl. decEq.
  apply H. lia. apply IHn. intros. apply H. lia.
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

Program Definition store (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val) (cp : compartment): option mem :=
  if valid_access_dec m chunk b ofs Writable cp then
    Some (mkmem (PMap.set b
                          (setN (encode_val chunk v) ofs (m.(mem_contents)#b))
                          m.(mem_contents))
                m.(mem_access)
                m.(mem_compartments)
                m.(nextblock)
                _ _ _ _)
  else
    None.
Next Obligation. apply access_max. Qed.
Next Obligation. apply nextblock_noaccess; auto. Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b0 b).
  rewrite setN_default. apply contents_default.
  apply contents_default.
Qed.
Next Obligation.
  eapply nextblock_compartments; eauto.
Qed.

(** [storev chunk m addr v cp] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) (cp : compartment) : option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Ptrofs.unsigned ofs) v cp
  | _ => None
  end.

(** [storebytes m b ofs bytes cp] has component [cp] store the given list of
  bytes [bytes] starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)

Program Definition storebytes (m: mem) (b: block) (ofs: Z) (bytes: list memval) (cp: compartment) : option mem :=
  if range_perm_dec m b ofs (ofs + Z.of_nat (length bytes)) Cur Writable &&
     (can_access_block_dec m b cp || Nat.eq_dec (length bytes) 0)
  then
    Some (mkmem
             (PMap.set b (setN bytes ofs (m.(mem_contents)#b)) m.(mem_contents))
             m.(mem_access)
             m.(mem_compartments)
             m.(nextblock)
             _ _ _ _)
  else
    None.
Next Obligation. apply access_max. Qed.
Next Obligation. apply nextblock_noaccess; auto. Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b0 b).
  rewrite setN_default. apply contents_default.
  apply contents_default.
Qed.
Next Obligation.
  now apply nextblock_compartments.
Qed.

(** [drop_perm m b lo hi p cp] sets the max permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p] performed from compartment [cp].  These
    bytes must have current permissions [Freeable] in the initial memory state
    [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

(* RB: NOTE: Ownership permissions added by nested conditionals to work around
   funny [Program Definition] misbehavior in the second [Obligation]. *)
Program Definition drop_perm (m: mem) (b: block) (lo hi: Z) (p: permission) (cp: compartment): option mem :=
  if Z_le_dec hi lo then Some m else
    if range_perm_dec m b lo hi Cur Freeable then
      if can_access_block_dec m b cp then
        Some (mkmem m.(mem_contents)
                        (PMap.set b
                           (fun ofs k => if zle lo ofs && zlt ofs hi then Some p else m.(mem_access)#b ofs k)
                           m.(mem_access))
                        m.(mem_compartments)
                            m.(nextblock) _ _ _ _)
      else None
    else None.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b). subst b0.
  destruct (zle lo ofs && zlt ofs hi). red; auto with mem. apply access_max.
  apply access_max.
Qed.
Next Obligation.
  exploit (nextblock_noaccess m b0 ofs k). auto. intros NOACC.
  rewrite PMap.gsspec. destruct (peq b0 b). subst b0.
  destruct (zle lo ofs). destruct (zlt ofs hi).
  assert (P: perm m b ofs k Freeable) by auto using perm_cur.
  unfold perm in P. rewrite NOACC in P. contradiction.
  auto. auto. auto.
Qed.
Next Obligation.
  apply contents_default.
Qed.
Next Obligation.
  now apply nextblock_compartments.
Qed.

(* [set_perm] sets the permission of an entire block *)
Program Definition set_perm (m: mem) (b: block) (p: permission): option mem :=
  if plt b m.(nextblock) then
    Some (mkmem m.(mem_contents)
               (PMap.set b
                  (fun ofs k => if m.(mem_access)#b ofs k then Some p else None)
                  m.(mem_access))
               m.(mem_compartments)
                   m.(nextblock) _ _ _ _)
  else
    None.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b). subst b0.
  destruct ((mem_access m) # b ofs Max) eqn:?.
  destruct ((mem_access m) # b ofs Cur).
  red; auto with mem. red; auto with mem.
  exploit access_max; eauto. rewrite Heqo.
  intros H'. destruct ((mem_access m) # b ofs Cur). contradiction. auto.
  apply access_max.
Qed.
Next Obligation.
  exploit (nextblock_noaccess m b0 ofs k). auto. intros NOACC.
  rewrite PMap.gsspec. destruct (peq b0 b). subst b0.
  rewrite NOACC. auto.
  auto.
Qed.
Next Obligation.
  apply contents_default.
Qed.
Next Obligation.
  now apply nextblock_compartments.
Qed.

(** * Properties of the memory operations *)

(** Properties of the empty store. *)

Theorem nextblock_empty: nextblock empty = 1%positive.
Proof. reflexivity. Qed.

Theorem perm_empty: forall b ofs k p, ~perm empty b ofs k p.
Proof.
  intros. unfold perm, empty; simpl. tauto.
Qed.

Theorem valid_access_empty: forall chunk b ofs p cp, ~valid_access empty chunk b ofs p cp.
Proof.
  intros. red; intros. elim (perm_empty b ofs Cur p). apply H.
  generalize (size_chunk_pos chunk); lia.
Qed.

(** ** Properties related to [load] *)

Theorem valid_access_load:
  forall m chunk b ofs cp,
  valid_access m chunk b ofs Readable cp ->
  exists v, load chunk m b ofs cp = Some v.
Proof.
  intros. econstructor. unfold load. rewrite pred_dec_true; eauto.
Qed.

Theorem load_valid_access:
  forall m chunk b ofs cp v,
  load chunk m b ofs cp = Some v ->
  valid_access m chunk b ofs Readable cp.
Proof.
  intros until v. unfold load.
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  auto.
  congruence.
Qed.

Lemma load_result:
  forall chunk m b ofs cp v,
  load chunk m b ofs cp = Some v ->
  v = decode_val chunk (getN (size_chunk_nat chunk) ofs (m.(mem_contents)#b)).
Proof.
  intros until v. unfold load.
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  congruence.
  congruence.
Qed.

Lemma load_Some_None:
  forall chunk m sp ofs cp v,
    Mem.load chunk m sp ofs cp = Some v ->
    Mem.load chunk m sp ofs top = Some v.
Proof.
    intros. destruct (cp_eq_dec cp top) as [e | n0]; [subst; auto|].
    unfold load in *.
    destruct (Mem.valid_access_dec m chunk sp ofs Readable cp); try discriminate.
    inv H.
    destruct v0 as [? [? ?]].
    destruct (Mem.valid_access_dec m chunk sp ofs Readable top).
    reflexivity.
    apply Classical_Prop.not_and_or in n as [? | n]; try contradiction.
    apply Classical_Prop.not_and_or in n as [? | ?]; try contradiction.
    unfold can_access_block in H2. pose proof (flowsto_top (block_compartment m sp)); contradiction.
Qed.

Local Hint Resolve load_valid_access valid_access_load: mem.

Theorem load_type:
  forall m chunk b ofs cp v,
  load chunk m b ofs cp = Some v ->
  Val.has_type v (type_of_chunk chunk).
Proof.
  intros. exploit load_result; eauto; intros. rewrite H0.
  apply decode_val_type.
Qed.

Theorem load_rettype:
  forall m chunk b ofs cp v,
  load chunk m b ofs cp = Some v ->
  Val.has_rettype v (rettype_of_chunk chunk).
Proof.
  intros. exploit load_result; eauto; intros. rewrite H0.
  apply decode_val_rettype.
Qed.

Theorem load_cast:
  forall m chunk b ofs cp v,
  load chunk m b ofs cp = Some v ->
  match chunk with
  | Mint8signed => v = Val.sign_ext 8 v
  | Mint8unsigned => v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | _ => True
  end.
Proof.
  intros. exploit load_result; eauto.
  set (l := getN (size_chunk_nat chunk) ofs m.(mem_contents)#b).
  intros. subst v. apply decode_val_cast.
Qed.

Theorem load_int8_signed_unsigned:
  forall m b ofs cp,
  load Mint8signed m b ofs cp = option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs cp).
Proof.
  intros. unfold load.
  change (size_chunk_nat Mint8signed) with (size_chunk_nat Mint8unsigned).
  set (cl := getN (size_chunk_nat Mint8unsigned) ofs m.(mem_contents)#b).
  destruct (valid_access_dec m Mint8signed b ofs Readable).
  rewrite pred_dec_true; auto. unfold decode_val.
  destruct (proj_bytes cl); auto.
  simpl. decEq. decEq. rewrite Int.sign_ext_zero_ext. auto. compute; auto.
  rewrite pred_dec_false; auto.
Qed.

Theorem load_int16_signed_unsigned:
  forall m b ofs cp,
  load Mint16signed m b ofs cp = option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs cp).
Proof.
  intros. unfold load.
  change (size_chunk_nat Mint16signed) with (size_chunk_nat Mint16unsigned).
  set (cl := getN (size_chunk_nat Mint16unsigned) ofs m.(mem_contents)#b).
  destruct (valid_access_dec m Mint16signed b ofs Readable).
  rewrite pred_dec_true; auto. unfold decode_val.
  destruct (proj_bytes cl); auto.
  simpl. decEq. decEq. rewrite Int.sign_ext_zero_ext. auto. compute; auto.
  rewrite pred_dec_false; auto.
Qed.

(** ** Properties related to [loadbytes] *)

Theorem range_perm_loadbytes:
  forall m b ofs len cp,
  range_perm m b ofs (ofs + len) Cur Readable ->
  can_access_block m b cp ->
  exists bytes, loadbytes m b ofs len cp = Some bytes.
Proof.
  intros. econstructor. unfold loadbytes. rewrite andb_lazy_alt.
  setoid_rewrite pred_dec_true; eauto.
  setoid_rewrite (pred_dec_true (can_access_block_dec _ _ _)); eauto.
  rewrite orb_true_l; eauto.
Qed.

Theorem loadbytes_range_perm:
  forall m b ofs len cp bytes,
  loadbytes m b ofs len cp = Some bytes ->
  range_perm m b ofs (ofs + len) Cur Readable.
Proof.
  intros until bytes. unfold loadbytes.
  destruct (range_perm_dec m b ofs (ofs + len) Cur Readable). auto. easy.
Qed.

Theorem loadbytes_load:
  forall chunk m b ofs cp bytes,
  loadbytes m b ofs (size_chunk chunk) cp = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs cp = Some(decode_val chunk bytes).
Proof.
  unfold loadbytes, load; intros.
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Cur Readable);
    destruct (Z_le_dec (size_chunk chunk) 0);
    destruct (can_access_block_dec m b cp);
    inv H.
  rewrite pred_dec_true. auto.
  repeat split; auto.
  destruct chunk; simpl in *; lia.
  rewrite pred_dec_true. auto.
  repeat split; auto.
Qed.

Theorem load_loadbytes:
  forall chunk m b ofs cp v,
  load chunk m b ofs cp = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) cp = Some bytes
             /\ v = decode_val chunk bytes.
Proof.
  intros. exploit load_valid_access; eauto. intros [A [B C]].
  exploit load_result; eauto. intros.
  exists (getN (size_chunk_nat chunk) ofs m.(mem_contents)#b); split.
  unfold loadbytes. rewrite andb_lazy_alt. setoid_rewrite pred_dec_true; auto.
  setoid_rewrite (pred_dec_true (can_access_block_dec _ _ _)); auto.
  auto.
Qed.

Lemma getN_length:
  forall c n p, length (getN n p c) = n.
Proof.
  induction n; simpl; intros. auto. decEq; auto.
Qed.

Theorem loadbytes_length:
  forall m b ofs n cp bytes,
  loadbytes m b ofs n cp = Some bytes ->
  length bytes = Z.to_nat n.
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + n) Cur Readable);
    destruct (can_access_block_dec m b cp);
    inv H;
    try congruence.
  apply getN_length.
  destruct (Z_le_dec n 0); inv H1.
  apply getN_length.
Qed.

(* RB: NOTE: Had to add an [can_access_block] hypothesis here because that check is
   part of the overall access check; Some nil and None may be somewhat similar,
   but the difference seems significant. One could adjust the definition of
   [loadbytes], but it is too early to measure the consequences of such a
   change, which seems less principled, against the proofs that will need to
   resort to this result. *)
Theorem loadbytes_empty:
  forall m b ofs n cp,
  n <= 0 ->
  (* can_access_block m b cp -> *)
  loadbytes m b ofs n cp = Some nil.
Proof.
  intros. unfold loadbytes. rewrite andb_lazy_alt.
  setoid_rewrite pred_dec_true.
  - destruct (Z_le_dec n 0); try lia.
    rewrite orb_true_r.
    rewrite Z_to_nat_neg; auto.
  - red; intros. extlia.
Qed.

Lemma getN_concat:
  forall c n1 n2 p,
  getN (n1 + n2)%nat p c = getN n1 p c ++ getN n2 (p + Z.of_nat n1) c.
Proof.
  induction n1; intros.
  simpl. decEq. lia.
  rewrite Nat2Z.inj_succ. simpl. decEq.
  replace (p + Z.succ (Z.of_nat n1)) with ((p + 1) + Z.of_nat n1) by lia.
  auto.
Qed.

Theorem loadbytes_concat:
  forall m b ofs n1 n2 cp bytes1 bytes2,
  loadbytes m b ofs n1 cp = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 cp = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) cp = Some(bytes1 ++ bytes2).
Proof.
  unfold loadbytes; intros.
  destruct (can_access_block_dec m b cp); destruct (Z_le_dec (n1 + n2) 0); simpl in *;
    try now (rewrite andb_comm in *; simpl in *; congruence).
  - destruct (range_perm_dec m b ofs (ofs + n1) Cur Readable); try (simpl in *; congruence).
    destruct (range_perm_dec m b (ofs + n1) (ofs + n1 + n2) Cur Readable); try (simpl in *; congruence).
    setoid_rewrite pred_dec_true. rewrite Z2Nat.inj_add by lia.
    rewrite getN_concat. rewrite Z2Nat.id by lia.
    simpl in *. congruence.
    red; intros.
    assert (ofs0 < ofs + n1 \/ ofs0 >= ofs + n1) by lia.
    destruct H4. apply r; lia. apply r0; lia.
  - destruct (range_perm_dec m b ofs (ofs + n1) Cur Readable); try (simpl in *; congruence).
    destruct (range_perm_dec m b (ofs + n1) (ofs + n1 + n2) Cur Readable); try (simpl in *; congruence).
    setoid_rewrite pred_dec_true. rewrite Z2Nat.inj_add by lia.
    rewrite getN_concat. rewrite Z2Nat.id by lia.
    simpl in *. congruence.
    red; intros.
    assert (ofs0 < ofs + n1 \/ ofs0 >= ofs + n1) by lia.
    destruct H4. apply r; lia. apply r0; lia.
  - destruct (range_perm_dec m b ofs (ofs + n1) Cur Readable); try (simpl in *; congruence).
    destruct (range_perm_dec m b (ofs + n1) (ofs + n1 + n2) Cur Readable); try (simpl in *; congruence).
    setoid_rewrite pred_dec_true. rewrite Z2Nat.inj_add by lia.
    rewrite getN_concat. rewrite Z2Nat.id by lia.
    simpl in *.
    assert (n1 = 0) by lia; subst. assert (n2 = 0) by lia; subst. simpl in *. inv H0; inv H; auto.
    red; intros.
    assert (ofs0 < ofs + n1 \/ ofs0 >= ofs + n1) by lia.
    destruct H4. apply r; lia. apply r0; lia.
  - assert (n1 <> 0 \/ n2 <> 0) as [? | ?] by lia.
    destruct (Z_le_dec n1 0); try congruence. rewrite andb_comm in H; simpl in *; lia.
    rewrite andb_comm in H; simpl in *; congruence.
    destruct (Z_le_dec n2 0); try congruence. rewrite andb_comm in H0; simpl in *; lia.
    rewrite andb_comm in H0; simpl in *; try congruence.
Qed.

Theorem loadbytes_split:
  forall m b ofs n1 n2 cp bytes,
  loadbytes m b ofs (n1 + n2) cp = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 cp = Some bytes1
  /\ loadbytes m b (ofs + n1) n2 cp = Some bytes2
  /\ bytes = bytes1 ++ bytes2.
Proof.
  unfold loadbytes; intros.
  destruct (can_access_block_dec m b cp); destruct (Z_le_dec (n1 + n2) 0);
    [| | | rewrite andb_comm in *; simpl in *; congruence].
  - destruct (range_perm_dec m b ofs (ofs + (n1 + n2)) Cur Readable);
      try (simpl in *; congruence).
    rewrite Z2Nat.inj_add in H by lia. rewrite getN_concat in H.
    rewrite Z2Nat.id in H by lia. simpl.
    repeat setoid_rewrite pred_dec_true; simpl.
    econstructor; econstructor.
    split. reflexivity. split. reflexivity. simpl in *. congruence.
    red; intros; apply r; lia.
    red; intros; apply r; lia.
  - destruct (range_perm_dec m b ofs (ofs + (n1 + n2)) Cur Readable);
      try (simpl in *; congruence).
    rewrite Z2Nat.inj_add in H by lia. rewrite getN_concat in H.
    rewrite Z2Nat.id in H by lia. simpl.
    repeat setoid_rewrite pred_dec_true; simpl.
    econstructor; econstructor.
    split. reflexivity. split. reflexivity. simpl in *. congruence.
    red; intros; apply r; lia.
    red; intros; apply r; lia.
  - destruct (range_perm_dec m b ofs (ofs + (n1 + n2)) Cur Readable);
      try (simpl in *; congruence).
    rewrite Z2Nat.inj_add in H by lia. rewrite getN_concat in H.
    rewrite Z2Nat.id in H by lia. simpl.
    assert (n1 = 0) by lia; subst. assert (n2 = 0) by lia; subst. simpl in *. inv H; eauto.
    repeat setoid_rewrite pred_dec_true; simpl.
    econstructor; econstructor.
    split. reflexivity. split. reflexivity. simpl in *. congruence.
    red; intros; apply r; lia.
    red; intros; apply r; lia.
Qed.

Theorem load_rep:
 forall ch m1 m2 b ofs cp1 cp2 v1 v2,
  (forall z, 0 <= z < size_chunk ch -> ZMap.get (ofs + z) m1.(mem_contents)#b = ZMap.get (ofs + z) m2.(mem_contents)#b) ->
  load ch m1 b ofs cp1 = Some v1 ->
  load ch m2 b ofs cp2 = Some v2 ->
  v1 = v2.
Proof.
  intros.
  apply load_result in H0.
  apply load_result in H1.
  subst.
  f_equal.
  rewrite size_chunk_conv in H.
  remember (size_chunk_nat ch) as n; clear Heqn.
  revert ofs H; induction n; intros; simpl; auto.
  f_equal.
  rewrite Nat2Z.inj_succ in H.
  replace ofs with (ofs+0) by lia.
  apply H; lia.
  apply IHn.
  intros.
  rewrite <- Z.add_assoc.
  apply H.
  rewrite Nat2Z.inj_succ. lia.
Qed.

Theorem load_int64_split:
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
  exploit loadbytes_split. eexact LB. lia. lia.
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
  lia. apply Ptrofs.unsigned_range. auto.
  exists (two_p (Ptrofs.zwordsize - 3)).
  unfold Ptrofs.modulus, Ptrofs.zwordsize, Ptrofs.wordsize.
  unfold Wordsize_Ptrofs.wordsize. destruct Archi.ptr64; reflexivity.
  unfold Ptrofs.max_unsigned. lia.
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
Qed.

(** ** Properties related to [store] *)

Theorem valid_access_store:
  forall m1 chunk b ofs cp v,
  valid_access m1 chunk b ofs Writable cp ->
  { m2: mem | store chunk m1 b ofs v cp = Some m2 }.
Proof.
  intros.
  unfold store.
  destruct (valid_access_dec m1 chunk b ofs Writable).
  eauto.
  contradiction.
Defined.

Local Hint Resolve valid_access_store: mem.

Section STORE.
Variable chunk: memory_chunk.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable v: val.
Variable cp : compartment.
Variable m2: mem.
Hypothesis STORE: store chunk m1 b ofs v cp = Some m2.

Lemma store_access: mem_access m2 = mem_access m1.
Proof.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Lemma store_mem_contents:
  mem_contents m2 = PMap.set b (setN (encode_val chunk v) ofs m1.(mem_contents)#b) m1.(mem_contents).
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem perm_store_1:
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Proof.
  intros.
 unfold perm in *. rewrite store_access; auto.
Qed.

Theorem perm_store_2:
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Proof.
  intros. unfold perm in *.  rewrite store_access in H; auto.
Qed.

Local Hint Resolve perm_store_1 perm_store_2: mem.

Theorem nextblock_store:
  nextblock m2 = nextblock m1.
Proof.
  intros.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem store_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_store; auto.
Qed.

Theorem store_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_store in H; auto.
Qed.

Local Hint Resolve store_valid_block_1 store_valid_block_2: mem.

Theorem store_valid_access_1:
  forall chunk' b' ofs' p cp',
  valid_access m1 chunk' b' ofs' p cp' -> valid_access m2 chunk' b' ofs' p cp'.
Proof.
  intros. inv H. destruct H1 as [H1 H2]. constructor; try red; auto with mem. split.
  - unfold store in STORE.
    destruct (valid_access_dec m1 chunk b ofs Writable cp); [| congruence].
    inv STORE. auto.
  - auto.
Qed.

Theorem store_valid_access_2:
  forall chunk' b' ofs' p cp',
  valid_access m2 chunk' b' ofs' p cp' -> valid_access m1 chunk' b' ofs' p cp'.
Proof.
  intros. inv H. destruct H1 as [H1 H2]. constructor; try red; auto with mem. split.
  - unfold store in STORE.
    destruct (valid_access_dec m1 chunk b ofs Writable cp); [| congruence].
    inv STORE. auto.
  - auto.
Qed.

Theorem store_valid_access_3:
  valid_access m1 chunk b ofs Writable cp.
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 chunk b ofs Writable cp).
  auto.
  congruence.
Qed.

Theorem store_valid_access_4:
  valid_access m1 chunk b ofs Writable top.
Proof.
  unfold store in STORE.
  destruct (valid_access_dec m1 chunk b ofs Writable cp) as [[? [? ?]] |].
  split; [| split]; try now simpl; auto with comps.
  congruence.
Qed.

Local Hint Resolve store_valid_access_1 store_valid_access_2
      store_valid_access_3 store_valid_access_4: mem.

Theorem store_block_compartment:
  forall b',
  block_compartment m2 b' = block_compartment m1 b'.
Proof.
  unfold store in STORE.
  destruct valid_access_dec; try easy.
  injection STORE.
  now intros <- b'.
Qed.

Theorem load_store_similar:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v', load chunk' m2 b ofs cp = Some v' /\ decode_encode_val v chunk chunk' v'.
Proof.
  intros.
  exploit (valid_access_load m2 chunk').
  eapply valid_access_compat. symmetry; eauto. auto.
    instantiate (1 := cp). eauto with mem.
  intros [v' LOAD].
  exists v'; split; auto.
  exploit load_result; eauto. intros B.
  rewrite B. rewrite store_mem_contents; simpl.
  rewrite PMap.gss.
  replace (size_chunk_nat chunk') with (length (encode_val chunk v)).
  rewrite getN_setN_same. apply decode_encode_val_general.
  rewrite encode_val_length. repeat rewrite size_chunk_conv in H.
  apply Nat2Z.inj; auto.
Qed.

Theorem load_store_similar_2:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  type_of_chunk chunk' = type_of_chunk chunk ->
  load chunk' m2 b ofs cp = Some (Val.load_result chunk' v).
Proof.
  intros. destruct (load_store_similar chunk') as [v' [A B]]; auto.
  rewrite A. decEq. eapply decode_encode_val_similar with (chunk1 := chunk); eauto.
Qed.

Theorem load_store_same:
  load chunk m2 b ofs cp = Some (Val.load_result chunk v).
Proof.
  apply load_store_similar_2; auto. lia.
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
Qed.

Theorem loadbytes_store_same:
  loadbytes m2 b ofs (size_chunk chunk) cp = Some(encode_val chunk v).
Proof.
  intros.
  assert (valid_access m2 chunk b ofs Readable cp) by eauto with mem.
  destruct (can_access_block_dec m2 b cp);
    [ | inversion H as [_ [Hcontra _]]; contradiction].
  unfold loadbytes.
  rewrite andb_lazy_alt. setoid_rewrite pred_dec_true. setoid_rewrite (pred_dec_true (can_access_block_dec _ _ _)).
  rewrite store_mem_contents; simpl.
  rewrite PMap.gss.
  replace (Z.to_nat (size_chunk chunk)) with (length (encode_val chunk v)).
  rewrite getN_setN_same. auto.
  rewrite encode_val_length. auto.
  auto.
  apply H.
Qed.

Theorem loadbytes_store_same_priv:
  loadbytes m2 b ofs (size_chunk chunk) top = Some(encode_val chunk v).
Proof.
  intros.
  assert (valid_access m2 chunk b ofs Readable top) by (eauto with mem).
  destruct (can_access_block_dec m2 b top);
    [ | inversion H as [_ [Hcontra _]]; contradiction].
  unfold loadbytes.
  rewrite andb_lazy_alt. setoid_rewrite pred_dec_true. setoid_rewrite (pred_dec_true (can_access_block_dec _ _ _)).
  rewrite store_mem_contents; simpl.
  rewrite PMap.gss.
  replace (Z.to_nat (size_chunk chunk)) with (length (encode_val chunk v)).
  rewrite getN_setN_same. auto.
  rewrite encode_val_length. auto.
  auto.
  apply H.
Qed.

(* RB: NOTE: Split in _1 and _2 directions? *)
Remark store_range_perm_inj :
  forall b' ofs' n,
  range_perm m1 b' ofs' (ofs' + n) Cur Readable <->
  range_perm m2 b' ofs' (ofs' + n) Cur Readable.
Proof.
  split; intros;
    destruct (range_perm_dec m1 b' ofs' (ofs' + n) Cur Readable);
    destruct (range_perm_dec m2 b' ofs' (ofs' + n) Cur Readable);
    try contradiction; try assumption;
    (unfold store in STORE;
     destruct (valid_access_dec m1 chunk b ofs Writable cp);
     inv STORE; now auto).
Qed.

Remark store_can_access_block_1 :
  can_access_block m1 b cp.
Proof.
  unfold store in STORE.
  destruct (valid_access_dec m1 chunk b ofs Writable cp)
    as [[_ [OWN _]] |];
    easy.
Qed.

Remark store_can_access_block_2 :
  can_access_block m2 b cp.
Proof.
  unfold store in STORE.
  destruct (Mem.valid_access_dec m1 chunk b ofs Writable cp)
    as [[_ [OWN _]] |]; try discriminate.
  inv STORE. easy.
Qed.

Remark store_preserves_comp :
  forall b',
    block_compartment m1 b' = block_compartment m2 b'.
Proof.
  intros;
    (unfold store in STORE;
     destruct (valid_access_dec m1 chunk b ofs Writable cp);
     inv STORE; now auto).
Qed.

Remark store_can_access_block_inj :
  forall b' cp',
  can_access_block m1 b' cp' <-> can_access_block m2 b' cp'.
Proof.
  intros b' cp'; simpl. rewrite store_preserves_comp; intuition.
Qed.


Lemma store_can_access_block_inj_1 :
  forall b' cp', can_access_block m1 b' cp' -> can_access_block m2 b' cp'.
Proof.
  simpl; intros; rewrite <- store_preserves_comp; eauto.
Qed.

Theorem loadbytes_store_other:
  forall b' ofs' n cp',
  b' <> b
  \/ n <= 0
  \/ ofs' + n <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n cp' = loadbytes m1 b' ofs' n cp'.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs' (ofs' + n) Cur Readable).
- rewrite andb_lazy_alt. setoid_rewrite pred_dec_true at 1.
+ destruct (can_access_block_dec m1 b' cp').
* setoid_rewrite (pred_dec_true (can_access_block_dec _ _ _)). simpl.
  decEq. rewrite store_mem_contents; simpl.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  destruct H. congruence.
  destruct (zle n 0) as [z | n0].
  rewrite (Z_to_nat_neg _ z). auto.
  destruct H. extlia.
  apply getN_setN_outside. rewrite encode_val_length. rewrite <- size_chunk_conv.
  rewrite Z2Nat.id. auto. lia.
  auto.
  simpl; rewrite <- store_preserves_comp; auto.
* destruct (Z_le_dec n 0).
  rewrite !orb_true_r. subst; simpl.
  rewrite Z_to_nat_neg; auto.
  setoid_rewrite pred_dec_false; auto.
  simpl; rewrite <- store_preserves_comp; auto.
+ red; intros. eauto with mem.
- setoid_rewrite pred_dec_false at 1.
+ auto.
+ red; intro; elim n0; red; intros; eauto with mem.
Qed.

Lemma setN_in:
  forall vl p q c,
  p <= q < p + Z.of_nat (length vl) ->
  In (ZMap.get q (setN vl p c)) vl.
Proof.
  induction vl; intros.
  simpl in H. extlia.
  simpl length in H. rewrite Nat2Z.inj_succ in H. simpl.
  destruct (zeq p q). subst q. rewrite setN_outside. rewrite ZMap.gss.
  auto with coqlib. lia.
  right. apply IHvl. lia.
Qed.

Lemma getN_in:
  forall c q n p,
  p <= q < p + Z.of_nat n ->
  In (ZMap.get q c) (getN n p c).
Proof.
  induction n; intros.
  simpl in H; extlia.
  rewrite Nat2Z.inj_succ in H. simpl. destruct (zeq p q).
  subst q. auto.
  right. apply IHn. lia.
Qed.

End STORE.

Local Hint Resolve perm_store_1 perm_store_2: mem.
Local Hint Resolve store_valid_block_1 store_valid_block_2: mem.
Local Hint Resolve store_valid_access_1 store_valid_access_2
             store_valid_access_3: mem.

(* RB: NOTE: [cp] and [cp'] must be equal, but the result does not rely on
   this fact, and similarly for other related theorems. *)
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
  rewrite setN_outside by lia. apply ZMap.gss.
- right. destruct (zlt ofs ofs').
(* If ofs < ofs':  the load reads (at ofs') a continuation byte from the write.
       ofs   ofs'   ofs+|chunk|
        [-------------------]       write
             [-------------------]  read
*)
+ left; split. lia. unfold c'. simpl. apply setN_in.
  assert (Z.of_nat (length (mv1 :: mvl)) = size_chunk chunk).
  { rewrite <- ENC; rewrite encode_val_length. rewrite size_chunk_conv; auto. }
  simpl length in H3. rewrite Nat2Z.inj_succ in H3. lia.
(* If ofs > ofs':  the load reads (at ofs) the first byte from the write.
       ofs'   ofs   ofs'+|chunk'|
               [-------------------]  write
         [----------------]           read
*)
+ right; split. lia. replace mv1 with (ZMap.get ofs c').
  apply getN_in.
  assert (size_chunk chunk' = Z.succ (Z.of_nat sz')).
  { rewrite size_chunk_conv. rewrite SIZE'. rewrite Nat2Z.inj_succ; auto. }
  lia.
  unfold c'. simpl. rewrite setN_outside by lia. apply ZMap.gss.
Qed.

Definition compat_pointer_chunks (chunk1 chunk2: memory_chunk) : Prop :=
  match chunk1, chunk2 with
  | (Mint32 | Many32), (Mint32 | Many32) => True
  | (Mint64 | Many64), (Mint64 | Many64) => True
  | _, _ => False
  end.

Lemma compat_pointer_chunks_true:
  forall chunk1 chunk2,
  (chunk1 = Mint32 \/ chunk1 = Many32 \/ chunk1 = Mint64 \/ chunk1 = Many64) ->
  (chunk2 = Mint32 \/ chunk2 = Many32 \/ chunk2 = Mint64 \/ chunk2 = Many64) ->
  quantity_chunk chunk1 = quantity_chunk chunk2 ->
  compat_pointer_chunks chunk1 chunk2.
Proof.
  intros. destruct H as [P|[P|[P|P]]]; destruct H0 as [Q|[Q|[Q|Q]]];
  subst; red; auto; discriminate.
Qed.

Theorem load_pointer_store:
  forall chunk m1 b ofs v cp m2 chunk' b' ofs' cp' v_b v_o,
  store chunk m1 b ofs v cp = Some m2 ->
  load chunk' m2 b' ofs' cp' = Some(Vptr v_b v_o) ->
  (v = Vptr v_b v_o /\ compat_pointer_chunks chunk chunk' /\ b' = b /\ ofs' = ofs)
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').
Proof.
  intros.
  destruct (peq b' b); auto. subst b'.
  destruct (zle (ofs' + size_chunk chunk') ofs); auto.
  destruct (zle (ofs + size_chunk chunk) ofs'); auto.
  exploit load_store_overlap; eauto.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  inv DEC; try contradiction.
  destruct CASES as [(A & B) | [(A & B) | (A & B)]].
- (* Same offset *)
  subst. inv ENC.
  assert (chunk = Mint32 \/ chunk = Many32 \/ chunk = Mint64 \/ chunk = Many64)
  by (destruct chunk; auto || contradiction).
  left; split. rewrite H3.
  destruct H4 as [P|[P|[P|P]]]; subst chunk'; destruct v0; simpl in H3;
  try congruence; destruct Archi.ptr64; congruence.
  split. apply compat_pointer_chunks_true; auto.
  auto.
- (* ofs' > ofs *)
  inv ENC.
  + exploit H10; eauto. intros (j & P & Q). inv P. congruence.
  + exploit H8; eauto. intros (n & P); congruence.
  + exploit H2; eauto. congruence.
- (* ofs' < ofs *)
  exploit H7; eauto. intros (j & P & Q). subst mv1. inv ENC. congruence.
Qed.

Theorem load_store_pointer_overlap:
  forall chunk m1 b ofs v_b v_o cp m2 chunk' ofs' cp' v,
  store chunk m1 b ofs (Vptr v_b v_o) cp = Some m2 ->
  load chunk' m2 b ofs' cp' = Some v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = Vundef.
Proof.
  intros.
  exploit load_store_overlap; eauto.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  destruct CASES as [(A & B) | [(A & B) | (A & B)]].
- congruence.
- inv ENC.
  + exploit H9; eauto. intros (j & P & Q). subst mv1'. inv DEC. congruence. auto.
  + contradiction.
  + exploit H5; eauto. intros; subst. inv DEC; auto.
- inv DEC.
  + exploit H10; eauto. intros (j & P & Q). subst mv1. inv ENC. congruence.
  + exploit H8; eauto. intros (n & P). subst mv1. inv ENC. contradiction.
  + auto.
Qed.

Theorem load_store_pointer_mismatch:
  forall chunk m1 b ofs v_b v_o cp m2 chunk' cp' v,
  store chunk m1 b ofs (Vptr v_b v_o) cp = Some m2 ->
  load chunk' m2 b ofs cp' = Some v ->
  ~compat_pointer_chunks chunk chunk' ->
  v = Vundef.
Proof.
  intros.
  exploit load_store_overlap; eauto.
  generalize (size_chunk_pos chunk'); lia.
  generalize (size_chunk_pos chunk); lia.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  destruct CASES as [(A & B) | [(A & B) | (A & B)]]; try extlia.
  inv ENC; inv DEC; auto.
- elim H1. apply compat_pointer_chunks_true; auto.
- contradiction.
Qed.

Lemma store_similar_chunks:
  forall chunk1 chunk2 v1 v2 m b ofs cp,
  encode_val chunk1 v1 = encode_val chunk2 v2 ->
  align_chunk chunk1 = align_chunk chunk2 ->
  store chunk1 m b ofs v1 cp = store chunk2 m b ofs v2 cp.
Proof.
  intros. unfold store.
  assert (size_chunk chunk1 = size_chunk chunk2).
    repeat rewrite size_chunk_conv.
    rewrite <- (encode_val_length chunk1 v1).
    rewrite <- (encode_val_length chunk2 v2).
    congruence.
  unfold store.
  destruct (valid_access_dec m chunk1 b ofs Writable);
  destruct (valid_access_dec m chunk2 b ofs Writable); auto.
  f_equal. apply mkmem_ext; auto. congruence.
  elim n. apply valid_access_compat with chunk1; auto. lia.
  elim n. apply valid_access_compat with chunk2; auto. lia.
Qed.

Theorem store_signed_unsigned_8:
  forall m b ofs v cp,
  store Mint8signed m b ofs v cp = store Mint8unsigned m b ofs v cp.
Proof. intros. apply store_similar_chunks. apply encode_val_int8_signed_unsigned. auto. Qed.

Theorem store_signed_unsigned_16:
  forall m b ofs v cp,
  store Mint16signed m b ofs v cp = store Mint16unsigned m b ofs v cp.
Proof. intros. apply store_similar_chunks. apply encode_val_int16_signed_unsigned. auto. Qed.

Theorem store_int8_zero_ext:
  forall m b ofs n cp,
  store Mint8unsigned m b ofs (Vint (Int.zero_ext 8 n)) cp =
  store Mint8unsigned m b ofs (Vint n) cp.
Proof. intros. apply store_similar_chunks. apply encode_val_int8_zero_ext. auto. Qed.

Theorem store_int8_sign_ext:
  forall m b ofs n cp,
  store Mint8signed m b ofs (Vint (Int.sign_ext 8 n)) cp =
  store Mint8signed m b ofs (Vint n) cp.
Proof. intros. apply store_similar_chunks. apply encode_val_int8_sign_ext. auto. Qed.

Theorem store_int16_zero_ext:
  forall m b ofs n cp,
  store Mint16unsigned m b ofs (Vint (Int.zero_ext 16 n)) cp =
  store Mint16unsigned m b ofs (Vint n) cp.
Proof. intros. apply store_similar_chunks. apply encode_val_int16_zero_ext. auto. Qed.

Theorem store_int16_sign_ext:
  forall m b ofs n cp,
  store Mint16signed m b ofs (Vint (Int.sign_ext 16 n)) cp =
  store Mint16signed m b ofs (Vint n) cp.
Proof. intros. apply store_similar_chunks. apply encode_val_int16_sign_ext. auto. Qed.

(*
Theorem store_float64al32:
  forall m b ofs v m',
  store Mfloat64 m b ofs v = Some m' -> store Mfloat64al32 m b ofs v = Some m'.
Proof.
  unfold store; intros.
  destruct (valid_access_dec m Mfloat64 b ofs Writable); try discriminate.
  destruct (valid_access_dec m Mfloat64al32 b ofs Writable).
  rewrite <- H. f_equal. apply mkmem_ext; auto.
  elim n. apply valid_access_compat with Mfloat64; auto. simpl; lia.
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
  forall m1 b ofs bytes cp,
  range_perm m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable ->
  can_access_block m1 b cp \/ (length bytes = 0)%nat ->
  { m2 : mem | storebytes m1 b ofs bytes cp = Some m2 }.
Proof.
  intros. unfold storebytes.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable).
  econstructor.
  destruct H0.
  setoid_rewrite pred_dec_true at 1. reflexivity. assumption.
  setoid_rewrite pred_dec_true at 2. rewrite orb_true_r. reflexivity. assumption.
  contradiction.
Defined.

Theorem storebytes_store:
  forall m1 b ofs chunk v cp m2,
  storebytes m1 b ofs (encode_val chunk v) cp = Some m2 ->
  (align_chunk chunk | ofs) ->
  store chunk m1 b ofs v cp = Some m2.
Proof.
  unfold storebytes, store. intros.
  destruct (can_access_block_dec m1 b cp); destruct (Nat.eq_dec); [| | | rewrite andb_false_r in H; now inversion H].
  - destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length (encode_val chunk v))) Cur Writable); inv H.
    destruct (valid_access_dec m1 chunk b ofs Writable).
    f_equal. apply mkmem_ext; auto.
    elim n. constructor; auto.
    rewrite encode_val_length in r. rewrite size_chunk_conv. auto.
  - destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length (encode_val chunk v))) Cur Writable); inv H.
    destruct (valid_access_dec m1 chunk b ofs Writable).
    f_equal. apply mkmem_ext; auto.
    elim n0. constructor; auto.
    rewrite encode_val_length in r. rewrite size_chunk_conv. auto.
  - destruct v, chunk; simpl in e; try congruence;
      try (clear H; rewrite length_inj_bytes, encode_int_length in e; lia).
    clear H. destruct Archi.ptr64; simpl in *; lia.
    clear H. destruct Archi.ptr64; simpl in *; lia.
Qed.

Theorem store_storebytes:
  forall m1 b ofs chunk v cp m2,
  store chunk m1 b ofs v cp = Some m2 ->
  storebytes m1 b ofs (encode_val chunk v) cp = Some m2.
Proof.
  unfold storebytes, store. intros.
  destruct (valid_access_dec m1 chunk b ofs Writable); inv H.
  inversion v0 as [_ [Hown _]].
  destruct (can_access_block_dec m1 b cp); [| contradiction].
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length (encode_val chunk v))) Cur Writable).
  simpl.
  f_equal. apply mkmem_ext; auto.
  destruct v0.  elim n.
  rewrite encode_val_length. rewrite <- size_chunk_conv. auto.
Qed.

Section STOREBYTES.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable bytes: list memval.
Variable cp: compartment.
Variable m2: mem.
Hypothesis STORE: storebytes m1 b ofs bytes cp = Some m2.

Lemma storebytes_can_access_block_1 : can_access_block m1 b cp \/ (length bytes = 0)%nat.
Proof.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (Datatypes.length bytes)) Cur Writable);
    [| now inversion STORE].
  destruct (Nat.eq_dec); try lia.
  destruct (can_access_block_dec m1 b cp);
    [| now inversion STORE].
  left; assumption.
Qed.

Lemma storebytes_can_access_block_2 : can_access_block m2 b cp \/ (length bytes = 0)%nat.
Proof.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (Datatypes.length bytes)) Cur Writable);
    [| now inversion STORE].
  destruct (Nat.eq_dec); try lia.
  destruct (can_access_block_dec m1 b cp);
    inv STORE.
  left; assumption.
Qed.

Lemma storebytes_preserves_comp:
  forall b', block_compartment m1 b' = block_compartment m2 b'.
Proof.
  unfold storebytes in *. intros b'.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (Datatypes.length bytes)) Cur Writable);
    destruct (can_access_block_dec m1 b cp);
    destruct Nat.eq_dec;
    inv STORE; simpl in *; reflexivity.
Qed.

(* RB: NOTE: Names and split adapted from storebytes_valid_block_1 and _2 below,
   similar auxiliary results could follow the same pattern (with preservation
   suffix, see lemmas above). *)
Lemma storebytes_can_access_block_inj_1 :
  forall b' cp', can_access_block m1 b' cp' -> can_access_block m2 b' cp'.
Proof.
  unfold can_access_block, storebytes in *;
    intros b' cp' H;
    destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (Datatypes.length bytes)) Cur Writable);
    destruct (can_access_block_dec m1 b cp);
    destruct Nat.eq_dec;
    inv STORE;
    assumption.
Qed.

Lemma storebytes_can_access_block_inj_2 :
  forall b' cp', can_access_block m2 b' cp' -> can_access_block m1 b' cp'.
Proof.
  unfold can_access_block, storebytes in *;
    intros b' cp' H;
    destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (Datatypes.length bytes)) Cur Writable);
    destruct (can_access_block_dec m1 b cp);
    destruct Nat.eq_dec;
    inv STORE;
    assumption.
Qed.

Lemma storebytes_access: mem_access m2 = mem_access m1.
Proof.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  destruct (can_access_block_dec m1 b cp);
    destruct Nat.eq_dec;
  inv STORE.
  auto. auto. auto.
Qed.

Lemma storebytes_mem_contents:
   mem_contents m2 = PMap.set b (setN bytes ofs m1.(mem_contents)#b) m1.(mem_contents).
Proof.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  destruct (can_access_block_dec m1 b cp);
    destruct Nat.eq_dec;
  inv STORE;
  auto.
Qed.

Theorem perm_storebytes_1:
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Proof.
  intros. unfold perm in *. rewrite storebytes_access; auto.
Qed.

Theorem perm_storebytes_2:
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Proof.
  intros. unfold perm in *. rewrite storebytes_access in H; auto.
Qed.

Local Hint Resolve perm_storebytes_1 perm_storebytes_2: mem.

Theorem storebytes_valid_access_1:
  forall chunk' b' ofs' p cp',
  valid_access m1 chunk' b' ofs' p cp' -> valid_access m2 chunk' b' ofs' p cp'.
Proof.
  intros. inv H. destruct H1 as [H1 H2]. constructor; try red; auto with mem.
  split; auto.
  apply storebytes_can_access_block_inj_1; eassumption.
Qed.

Theorem storebytes_valid_access_2:
  forall chunk' b' ofs' p cp',
  valid_access m2 chunk' b' ofs' p cp' -> valid_access m1 chunk' b' ofs' p cp'.
Proof.
  intros. inv H. destruct H1 as [H1 H2]. constructor; try red; auto with mem.
  split; auto.
  apply storebytes_can_access_block_inj_2; eassumption.
Qed.

Local Hint Resolve storebytes_valid_access_1 storebytes_valid_access_2: mem.


Theorem storebytes_block_compartment:
  forall b',
  block_compartment m2 b' = block_compartment m1 b'.
Proof.
  unfold storebytes in STORE;
  destruct range_perm_dec; try easy;
  destruct can_access_block_dec; try easy;
    destruct Nat.eq_dec; try easy;
  injection STORE;
  now intros <- b'.
Qed.

Theorem nextblock_storebytes:
  nextblock m2 = nextblock m1.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  destruct (can_access_block_dec m1 b cp);
    destruct Nat.eq_dec;
  inv STORE;
  auto.
Qed.

Theorem storebytes_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_storebytes; auto.
Qed.

Theorem storebytes_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_storebytes in H; auto.
Qed.

Local Hint Resolve storebytes_valid_block_1 storebytes_valid_block_2: mem.

Theorem storebytes_range_perm:
  range_perm m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Theorem loadbytes_storebytes_same:
  loadbytes m2 b ofs (Z.of_nat (length bytes)) cp = Some bytes.
Proof.
  intros. assert (STORE2:=STORE). unfold storebytes in STORE2. unfold loadbytes.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  destruct (can_access_block_dec m1 b cp);
  try discriminate.
  setoid_rewrite (pred_dec_true (can_access_block_dec _ _ _)). simpl.
  setoid_rewrite pred_dec_true. simpl.
  decEq. inv STORE2; simpl. rewrite PMap.gss. rewrite Nat2Z.id.
  apply getN_setN_same.
  red; eauto with mem.
  apply storebytes_can_access_block_inj_1; eassumption.
  destruct Nat.eq_dec; try discriminate. simpl in *. rewrite e in *.
  setoid_rewrite pred_dec_true at 1 3. rewrite orb_true_r.
  inv STORE2; simpl. destruct bytes; try lia; auto. simpl in e. lia.
  red; eauto with mem. lia.
Qed.

Theorem loadbytes_change_comp:
  forall ofs' z cp' v',
    0 < z ->
    loadbytes m2 b ofs' z cp' = Some v' ->
    loadbytes m2 b ofs (Z.of_nat (length bytes)) cp' = Some bytes.
Proof.
  intros ofs' z cp' v' z0 H.
  pose proof loadbytes_storebytes_same as G.
  unfold loadbytes in *.
  destruct andb eqn:E1; try congruence. apply andb_prop in E1 as [E1 E1'].
  destruct andb eqn:E2; try congruence. apply andb_prop in E2 as [E2 E2'].
  destruct andb eqn:E3; try congruence. apply andb_false_iff in E3 as [E3 | E3]; try congruence.
  apply orb_true_iff in E1' as [? | ?];
    apply orb_true_iff in E2' as [? | ?];
    apply orb_false_iff in E3 as [? ?]; try congruence.
  destruct z; simpl in *; try now auto.
Qed.

Theorem loadbytes_storebytes_same_None:
  loadbytes m2 b ofs (Z.of_nat (length bytes)) top = Some bytes.
Proof.
  intros. assert (STORE2:=STORE). unfold storebytes in STORE2. unfold loadbytes.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  destruct (can_access_block_dec m1 b cp);
  try discriminate.
  setoid_rewrite (pred_dec_true (can_access_block_dec _ _ _)). simpl.
  setoid_rewrite pred_dec_true. simpl.
  decEq. inv STORE2; simpl. rewrite PMap.gss. rewrite Nat2Z.id.
  apply getN_setN_same.
  red; eauto with mem.
  simpl; auto with comps.
  destruct Nat.eq_dec; try discriminate.
  setoid_rewrite pred_dec_true at 1 3. rewrite orb_true_r. simpl.
  decEq. inv STORE2; simpl. rewrite PMap.gss. rewrite Nat2Z.id.
  apply getN_setN_same.
  red; eauto with mem. lia.
Qed.

Theorem loadbytes_storebytes_disjoint:
  forall b' ofs' len cp',
  len >= 0 ->
  b' <> b \/ Intv.disjoint (ofs', ofs' + len) (ofs, ofs + Z.of_nat (length bytes)) ->
  loadbytes m2 b' ofs' len cp' = loadbytes m1 b' ofs' len cp'.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs' (ofs' + len) Cur Readable);
  destruct (can_access_block_dec m1 b' cp');
  destruct (Z_le_dec len 0); simpl.
- setoid_rewrite pred_dec_true; simpl.
+ rewrite storebytes_mem_contents. decEq.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  apply getN_setN_disjoint. rewrite Z2Nat.id by lia. intuition congruence.
  auto.
+ red; auto with mem.
+ apply storebytes_can_access_block_inj_1; assumption.
- setoid_rewrite pred_dec_true; simpl.
+ rewrite storebytes_mem_contents. decEq.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  apply getN_setN_disjoint. rewrite Z2Nat.id by lia. intuition congruence.
  auto.
+ red; auto with mem.
+ apply storebytes_can_access_block_inj_1; assumption.
- setoid_rewrite orb_true_r; setoid_rewrite pred_dec_true; simpl.
+ rewrite storebytes_mem_contents. decEq.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  apply getN_setN_disjoint. rewrite Z2Nat.id by lia. intuition congruence.
  auto.
+ red; auto with mem.
- setoid_rewrite pred_dec_false at 2; simpl.
+ do 1 rewrite andb_false_r. reflexivity.
+ intro Hcontra. apply storebytes_can_access_block_inj_2 in Hcontra. contradiction.
- setoid_rewrite pred_dec_false at 1; simpl. reflexivity.
  red; intros; elim n. red; auto with mem.
- setoid_rewrite pred_dec_false at 1; simpl. reflexivity.
  red; intros; elim n. red; auto with mem.
- setoid_rewrite pred_dec_false at 1; simpl. reflexivity.
  red; intros; elim n. red; auto with mem.
- setoid_rewrite pred_dec_false at 1; simpl. reflexivity.
  red; intros; elim n. red; auto with mem.
Qed.

Theorem loadbytes_storebytes_other:
  forall b' ofs' len cp',
  len >= 0 ->
  b' <> b
  \/ ofs' + len <= ofs
  \/ ofs + Z.of_nat (length bytes) <= ofs' ->
  loadbytes m2 b' ofs' len cp' = loadbytes m1 b' ofs' len cp'.
Proof.
  intros. apply loadbytes_storebytes_disjoint; auto.
  destruct H0; auto. right. apply Intv.disjoint_range; auto.
Qed.

Theorem load_storebytes_other:
  forall chunk b' ofs' cp',
  b' <> b
  \/ ofs' + size_chunk chunk <= ofs
  \/ ofs + Z.of_nat (length bytes) <= ofs' ->
  load chunk m2 b' ofs' cp' = load chunk m1 b' ofs' cp'.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m1 chunk b' ofs' Readable cp').
  rewrite pred_dec_true.
  rewrite storebytes_mem_contents. decEq.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  rewrite getN_setN_outside. auto. rewrite <- size_chunk_conv. intuition congruence.
  auto.
  destruct v; split; auto. red; auto with mem.
  destruct H1 as [H1 H2]. split.
  apply storebytes_can_access_block_inj_1; assumption.
  assumption.
  apply pred_dec_false.
  red; intros; elim n. destruct H0. split; auto. red; auto with mem.
  destruct H1 as [H1 H2]. split.
  apply storebytes_can_access_block_inj_2; assumption.
  assumption.
Qed.

End STOREBYTES.

Lemma setN_concat:
  forall bytes1 bytes2 ofs c,
  setN (bytes1 ++ bytes2) ofs c = setN bytes2 (ofs + Z.of_nat (length bytes1)) (setN bytes1 ofs c).
Proof.
  induction bytes1; intros.
  simpl. decEq. lia.
  simpl length. rewrite Nat2Z.inj_succ. simpl. rewrite IHbytes1. decEq. lia.
Qed.

(* RB: NOTE: Different compartment variables could be used in each premise (and
   the conclusion), as those would effectively be equal. *)
Theorem storebytes_concat:
  forall m b ofs bytes1 cp m1 bytes2 m2,
  storebytes m b ofs bytes1 cp = Some m1 ->
  storebytes m1 b (ofs + Z.of_nat(length bytes1)) bytes2 cp = Some m2 ->
  storebytes m b ofs (bytes1 ++ bytes2) cp = Some m2.
Proof.
  intros. generalize H; intro ST1. generalize H0; intro ST2.
  unfold storebytes; unfold storebytes in ST1; unfold storebytes in ST2.
  destruct (range_perm_dec m b ofs (ofs + Z.of_nat(length bytes1)) Cur Writable);
  destruct (can_access_block_dec m b cp);
  simpl in *;
  try congruence.
  - destruct (range_perm_dec m1 b (ofs + Z.of_nat(length bytes1))
              (ofs + Z.of_nat(length bytes1) + Z.of_nat(length bytes2)) Cur Writable);
      simpl in *; try congruence.
    destruct (can_access_block_dec m1 b cp) eqn:rewr; simpl in *; try congruence.
    destruct (range_perm_dec m b ofs (ofs + Z.of_nat (length (bytes1 ++ bytes2))) Cur Writable); simpl in *.
    inv ST1; inv ST2; simpl in *; try congruence. decEq. apply mkmem_ext; auto.
    rewrite PMap.gss.  rewrite setN_concat. symmetry. apply PMap.set2.
    elim n.
    rewrite app_length. rewrite Nat2Z.inj_add. red; intros.
    destruct (zlt ofs0 (ofs + Z.of_nat(length bytes1))).
    apply r. lia.
    eapply perm_storebytes_2; eauto. apply r0. lia.
    destruct (Nat.eq_dec (Datatypes.length bytes2) 0); try discriminate.
    destruct (range_perm_dec m b ofs (ofs + Z.of_nat (length (bytes1 ++ bytes2))) Cur Writable); simpl in *.
    inv ST1; inv ST2; simpl in *; try congruence. decEq. apply mkmem_ext; auto.
    rewrite PMap.gss.  rewrite setN_concat. symmetry. apply PMap.set2.
    elim n0.
    rewrite app_length. rewrite Nat2Z.inj_add. red; intros.
    destruct (zlt ofs0 (ofs + Z.of_nat(length bytes1))).
    apply r. lia.
    eapply perm_storebytes_2; eauto. apply r0. lia.
  - destruct (Nat.eq_dec (Datatypes.length bytes1)); try discriminate. simpl in ST1.
    destruct (range_perm_dec m1 b (ofs + Z.of_nat(length bytes1))
              (ofs + Z.of_nat(length bytes1) + Z.of_nat(length bytes2)) Cur Writable);
      simpl in *; try congruence.
    destruct (can_access_block_dec m1 b cp) eqn:rewr; simpl in *; try congruence.
    + inv ST1. clear -c n.
      contradiction.
    + destruct (Nat.eq_dec (Datatypes.length bytes2) 0); try discriminate.
      setoid_rewrite pred_dec_true at 2.
      destruct (range_perm_dec m b ofs (ofs + Z.of_nat (length (bytes1 ++ bytes2))) Cur Writable); simpl in *.
      inv ST1; inv ST2; simpl in *; try congruence. decEq. apply mkmem_ext; auto.
      rewrite PMap.gss.  rewrite setN_concat. symmetry. apply PMap.set2.
      elim n1.
      rewrite app_length. rewrite Nat2Z.inj_add. red; intros.
      destruct (zlt ofs0 (ofs + Z.of_nat(length bytes1))).
      apply r. lia.
      eapply perm_storebytes_2; eauto. apply r0. lia.
      rewrite app_length; simpl.
      lia.
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
  red; intros. exploit storebytes_range_perm; eauto. rewrite app_length. lia.
  { unfold storebytes in H. destruct can_access_block_dec; try now auto.
    destruct Nat.eq_dec; try congruence. clear H. rewrite app_length in e. right. lia.
    simpl in *. rewrite andb_false_r in H. congruence. }
    destruct (range_perm_storebytes m1 b (ofs + Z.of_nat (length bytes1)) bytes2 cp) as [m2' ST2].
    red; intros. eapply perm_storebytes_1; eauto. exploit storebytes_range_perm.
    eexact H. instantiate (1 := ofs0). rewrite app_length. lia.
    auto.
  { unfold storebytes in H. destruct can_access_block_dec.
    simpl. erewrite <- storebytes_preserves_comp; eauto.
    destruct Nat.eq_dec; try congruence. clear H. rewrite app_length in e. right. lia.
    simpl in *. rewrite andb_false_r in H. congruence. }
    (* eapply storebytes_can_access_block_2; eauto. simpl; lia. *)
    assert (Some m2 = Some m2'). simpl in *.
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
Qed.

(* RB: NOTE: Maybe add these new lemmas to hint databases. *)
Lemma block_compartment_nextblock m:
  block_compartment m (nextblock m) = top.
Proof.
  destruct m. simpl in *.
  apply nextblock_compartments0. apply Plt_strict.
Qed.

(** ** Properties related to [alloc]. *)

Section ALLOC.

Variable m1: mem.
Variable c: compartment.
Variables lo hi: Z.
Variable m2: mem.
Variable b: block.
Hypothesis ALLOC: alloc m1 c lo hi = (m2, b).

Theorem nextblock_alloc:
  nextblock m2 = Pos.succ (nextblock m1).
Proof.
  injection ALLOC; intros. rewrite <- H0; auto.
Qed.

Theorem alloc_result:
  b = nextblock m1.
Proof.
  injection ALLOC; auto.
Qed.

Theorem valid_block_alloc:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_alloc.
  apply Plt_trans_succ; auto.
Qed.

Theorem fresh_block_alloc:
  ~(valid_block m1 b).
Proof.
  unfold valid_block. rewrite alloc_result. apply Plt_strict.
Qed.

Theorem valid_new_block:
  valid_block m2 b.
Proof.
  unfold valid_block. rewrite alloc_result. rewrite nextblock_alloc. apply Plt_succ.
Qed.

Theorem unowned_fresh_block:
  forall c', can_access_block m1 b c' -> c' = top.
Proof.
  unfold can_access_block. intros c'.
  injection ALLOC as _ <-.
  rewrite block_compartment_nextblock.
  intros ?. assert (c' ⊆ top) by now apply flowsto_top.
  exploit flowsto_antisym; eauto.
Qed.

Theorem owned_new_block:
  Mem.block_compartment m2 b = c.
Proof.
  unfold block_compartment.
  unfold alloc in ALLOC. destruct m1. inv ALLOC. simpl in *.
  rewrite PMap.gss; auto with comps.
Qed.

Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.

Theorem valid_block_alloc_inv:
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.
Proof.
  unfold valid_block; intros.
  rewrite nextblock_alloc in H. rewrite alloc_result.
  exploit Plt_succ_inv; eauto. tauto.
Qed.

Theorem valid_block_alloc_inv':
  forall b', valid_block m1 b' -> b' <> b.
Proof.
  intros b' Hvalid Heq; subst b'.
  apply fresh_block_alloc. assumption.
Qed.

Theorem perm_alloc_1:
  forall b' ofs k p, perm m1 b' ofs k p -> perm m2 b' ofs k p.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite PMap.gsspec. destruct (peq b' (nextblock m1)); auto.
  rewrite nextblock_noaccess in H. contradiction. subst b'. apply Plt_strict.
Qed.

Theorem perm_alloc_2:
  forall ofs k, lo <= ofs < hi -> perm m2 b ofs k Freeable.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite PMap.gss. unfold proj_sumbool. rewrite zle_true.
  rewrite zlt_true. simpl. auto with mem. lia. lia.
Qed.

Theorem perm_alloc_inv:
  forall b' ofs k p,
  perm m2 b' ofs k p ->
  if eq_block b' b then lo <= ofs < hi else perm m1 b' ofs k p.
Proof.
  intros until p; unfold perm. inv ALLOC. simpl.
  rewrite PMap.gsspec. unfold eq_block. destruct (peq b' (nextblock m1)); intros.
  destruct (zle lo ofs); try contradiction. destruct (zlt ofs hi); try contradiction.
  split; auto.
  auto.
Qed.

Theorem perm_alloc_3:
  forall ofs k p, perm m2 b ofs k p -> lo <= ofs < hi.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_true; auto.
Qed.

Theorem perm_alloc_4:
  forall b' ofs k p, perm m2 b' ofs k p -> b' <> b -> perm m1 b' ofs k p.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_false; auto.
Qed.

Local Hint Resolve perm_alloc_1 perm_alloc_2 perm_alloc_3 perm_alloc_4: mem.

Theorem alloc_block_compartment:
  forall b', block_compartment m2 b' =
  if eq_block b' b then c else block_compartment m1 b'.
Proof.
intros b'. injection ALLOC as <- <-. unfold block_compartment. simpl.
destruct eq_block as [->|neq].
- now rewrite PMap.gss; auto with comps.
- now rewrite PMap.gso.
Qed.

(* Lemma alloc_can_access_block_inj : *)
(*   forall b' c', can_access_block m1 b' c' -> b <> b'. *)
(* Proof. *)
(*   intros b' c' Hown Heq; subst b'. *)
(*   unfold can_access_block in Hown. *)
(*   now rewrite alloc_result, block_compartment_nextblock in Hown. *)
(* Qed. *)

Lemma alloc_lowers_comp:
  forall b', block_compartment m2 b' ⊆ block_compartment m1 b'.
Proof.
  intros b'.
  rewrite alloc_block_compartment.
  destruct eq_block as [->|neq]; auto with comps.
  rewrite alloc_result, block_compartment_nextblock; auto with comps.
Qed.

Lemma alloc_can_access_block_other_inj_1 :
  forall b' c', can_access_block m1 b' c' -> can_access_block m2 b' c'.
Proof.
  unfold can_access_block. intros b' c' Hown.
  rewrite alloc_block_compartment.
  destruct eq_block as [->|neq]; trivial.
  rewrite alloc_result, block_compartment_nextblock in Hown.
  eapply flowsto_trans. eapply flowsto_top. eauto.
Qed.

Lemma alloc_can_access_block_other_inj_2 :
  forall b' c', b' <> b -> can_access_block m2 b' c' -> can_access_block m1 b' c'.
Proof.
  unfold can_access_block. intros b' c' Hneq Hown.
  rewrite alloc_block_compartment in Hown.
  destruct eq_block; congruence.
Qed.

Theorem valid_access_alloc_other:
  forall chunk b' ofs p c',
  valid_access m1 chunk b' ofs p c' ->
  valid_access m2 chunk b' ofs p c'.
Proof.
  intros. inv H. destruct H1 as [H1 H2]. constructor; auto with mem.
  red; auto with mem.
  split.
  apply alloc_can_access_block_other_inj_1; assumption.
  auto.
Qed.

Theorem valid_access_alloc_same:
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable c.
Proof.
  intros. constructor; auto with mem.
  red; intros. apply perm_alloc_2. lia.
  split.
  simpl; rewrite owned_new_block; auto with comps.
  auto.
Qed.

Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

Theorem valid_access_alloc_inv:
  forall chunk b' ofs p c',
  valid_access m2 chunk b' ofs p c' ->
  if eq_block b' b
  then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p c'.
Proof.
  intros. inv H. destruct H1 as [H1 Hx].
  generalize (size_chunk_pos chunk); intro.
  destruct (eq_block b' b). subst b'.
  assert (perm m2 b ofs Cur p). apply H0. lia.
  assert (perm m2 b (ofs + size_chunk chunk - 1) Cur p). apply H0. lia.
  exploit perm_alloc_inv. eexact H2. rewrite dec_eq_true. intro.
  exploit perm_alloc_inv. eexact H3. rewrite dec_eq_true. intro.
  intuition lia.
  split; auto. red; intros.
  exploit perm_alloc_inv. apply H0. eauto. rewrite dec_eq_false; auto.
  split.
  apply alloc_can_access_block_other_inj_2; assumption.
  assumption.
Qed.

Theorem load_alloc_unchanged:
  forall chunk b' ofs c',
  valid_block m1 b' ->
  load chunk m2 b' ofs c' = load chunk m1 b' ofs c'.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b' ofs Readable).
  exploit valid_access_alloc_inv; eauto. destruct (eq_block b' b); intros.
  subst b'. elimtype False. eauto with mem.
  rewrite pred_dec_true; auto.
  injection ALLOC; intros. rewrite <- H2; simpl.
  rewrite PMap.gso. auto. rewrite H1. apply not_eq_sym; eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.

Theorem load_alloc_other:
  forall chunk b' ofs c' v,
  load chunk m1 b' ofs c' = Some v ->
  load chunk m2 b' ofs c' = Some v.
Proof.
  intros. rewrite <- H. apply load_alloc_unchanged. eauto with mem.
Qed.

Theorem load_alloc_same:
  forall chunk ofs c' v,
  load chunk m2 b ofs c' = Some v ->
  v = Vundef.
Proof.
  intros. exploit load_result; eauto. intro. rewrite H0.
  injection ALLOC; intros. rewrite <- H2; simpl. rewrite <- H1.
  rewrite PMap.gss. destruct (size_chunk_nat_pos chunk) as [n E]. rewrite E. simpl.
  rewrite ZMap.gi. apply decode_val_undef.
Qed.

(* RB: NOTE: In keeping with the style of the lemma, we add the missing
   assumption to it, however it is unclear whether this is the best choice.
   Clearly, c' can only be c, and block ownership can be established from
   known facts. *)
Theorem load_alloc_same':
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> can_access_block m2 b c -> (align_chunk chunk | ofs) ->
  load chunk m2 b ofs c = Some Vundef.
Proof.
  intros. assert (exists v, load chunk m2 b ofs c = Some v).
    apply valid_access_load. constructor; auto.
    red; intros. eapply perm_implies. apply perm_alloc_2. lia. auto with mem.
  destruct H3 as [v LOAD]. rewrite LOAD. decEq.
  eapply load_alloc_same; eauto.
Qed.

Theorem loadbytes_alloc_unchanged:
  forall b' ofs n c',
  valid_block m1 b' ->
  loadbytes m2 b' ofs n c' = loadbytes m1 b' ofs n c'.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs (ofs + n) Cur Readable).
- destruct (can_access_block_dec m1 b' c'); destruct (Z_le_dec n 0); simpl.
+ setoid_rewrite pred_dec_true. simpl.
  injection ALLOC; intros A B. rewrite <- B; simpl.
  rewrite PMap.gso. auto. rewrite A. eauto with mem.
  red; intros. eapply perm_alloc_1; eauto.
  apply alloc_can_access_block_other_inj_1; assumption.
+ setoid_rewrite pred_dec_true. simpl.
  injection ALLOC; intros A B. rewrite <- B; simpl.
  rewrite PMap.gso. auto. rewrite A. eauto with mem.
  red; intros. eapply perm_alloc_1; eauto.
  apply alloc_can_access_block_other_inj_1; assumption.
+ rewrite orb_true_r; simpl.
  setoid_rewrite pred_dec_true. simpl.
  injection ALLOC; intros A B. rewrite <- B; simpl.
  rewrite PMap.gso. auto. rewrite A. eauto with mem.
  red; intros. eapply perm_alloc_1; eauto.
+ setoid_rewrite pred_dec_false at 2; simpl.
* rewrite andb_comm; simpl. reflexivity.
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
  destruct (Z_le_dec n 0); simpl in *; try congruence.
  subst; simpl in *; inv H2. rewrite Z_to_nat_neg in H0; auto. inv H0.
Qed.

End ALLOC.

Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.
Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

(** ** Properties related to [free]. *)

Theorem range_perm_free:
  forall m1 b lo hi cp,
  range_perm m1 b lo hi Cur Freeable ->
  can_access_block m1 b cp \/ hi <= lo ->
  { m2: mem | free m1 b lo hi cp = Some m2 }.
Proof.
  intros; unfold free.
  destruct (Z_le_dec); eauto.
  econstructor.
  setoid_rewrite pred_dec_true; auto. simpl. eauto.
  destruct H0; eauto. lia.
Defined.

Section FREE.

Variable m1: mem.
Variable bf: block.
Variables lo hi: Z.
Variable cp: compartment.
Variable m2: mem.
Hypothesis FREE: free m1 bf lo hi cp = Some m2.

Theorem free_range_perm:
  range_perm m1 bf lo hi Cur Freeable.
Proof.
  unfold free in FREE. destruct (Z_le_dec hi lo); auto.
  intros ? ?; lia.
  destruct (range_perm_dec m1 bf lo hi Cur Freeable); auto.
  destruct (can_access_block_dec m1 bf cp); simpl in FREE;
  try congruence.
Qed.

Lemma free_result:
  m2 = unchecked_free m1 bf lo hi.
Proof.
  unfold free in FREE.
  destruct Z_le_dec; auto. inv FREE. unfold unchecked_free. destruct zle; auto. lia.
  destruct (range_perm_dec m1 bf lo hi Cur Freeable);
  destruct (can_access_block_dec m1 bf cp);
  simpl in FREE;
  auto;
  congruence.
Qed.

Theorem nextblock_free:
  nextblock m2 = nextblock m1.
Proof.
  rewrite free_result; unfold unchecked_free; destruct (zle hi lo); reflexivity.
Qed.

Theorem valid_block_free_1:
  forall b, valid_block m1 b -> valid_block m2 b.
Proof.
  intros. rewrite free_result. unfold unchecked_free; destruct (zle hi lo); assumption.
Qed.

Theorem valid_block_free_2:
  forall b, valid_block m2 b -> valid_block m1 b.
Proof.
  intros. rewrite free_result in H. unfold unchecked_free in *; destruct (zle hi lo); assumption.
Qed.

Local Hint Resolve valid_block_free_1 valid_block_free_2: mem.

Theorem perm_free_1:
  forall b ofs k p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs k p ->
  perm m2 b ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; destruct (zle hi lo); auto; simpl.
  rewrite PMap.gsspec. destruct (peq b bf). subst b.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl.
  elimtype False; intuition.
  auto. auto.
  auto.
Qed.

Theorem perm_free_2:
  forall ofs k p, lo <= ofs < hi -> ~ perm m2 bf ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; destruct (zle hi lo); auto; simpl; try lia.
  rewrite PMap.gss. unfold proj_sumbool. rewrite zle_true. rewrite zlt_true.
  simpl. tauto. lia. lia.
Qed.

Theorem perm_free_3:
  forall b ofs k p,
  perm m2 b ofs k p -> perm m1 b ofs k p.
Proof.
  intros until p. rewrite free_result. unfold perm, unchecked_free; destruct (zle hi lo); auto; simpl.
  rewrite PMap.gsspec. destruct (peq b bf). subst b.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl. tauto.
  auto. auto. auto.
Qed.

Theorem perm_free_inv:
  forall b ofs k p,
  perm m1 b ofs k p ->
  (b = bf /\ lo <= ofs < hi) \/ perm m2 b ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; destruct (zle hi lo); auto; simpl.
  rewrite PMap.gsspec. destruct (peq b bf); auto. subst b.
  destruct (zle lo ofs); simpl; auto.
  destruct (zlt ofs hi); simpl; auto.
Qed.

Lemma free_can_access_block_1 : can_access_block m1 bf cp \/ hi <= lo.
Proof.
  unfold free in FREE.
  destruct Z_le_dec; auto.
  destruct (range_perm_dec m1 bf lo hi Cur Freeable);
    destruct (can_access_block_dec m1 bf cp);
    simpl in FREE;
    try congruence.
  now left.
Qed.

Lemma free_can_access_block_2 : can_access_block m2 bf cp \/ hi <= lo.
Proof.
  unfold free in FREE.
  destruct Z_le_dec; auto.
  destruct (range_perm_dec m1 bf lo hi Cur Freeable);
    destruct (can_access_block_dec m1 bf cp);
    inv FREE.
  unfold unchecked_free; destruct (zle hi lo); left; assumption.
Qed.

Lemma free_preserves_comp:
  forall b, block_compartment m1 b = block_compartment m2 b.
Proof.
  intros b.
  unfold free in FREE.
  destruct Z_le_dec; auto. inv FREE; congruence.
  destruct (range_perm_dec m1 bf lo hi Cur Freeable); [| simpl in FREE; congruence].
  destruct (can_access_block_dec m1 bf cp); [| simpl in FREE; congruence].
  inv FREE.
  unfold unchecked_free; destruct (zle hi lo); auto.
Qed.

Lemma free_can_access_block_inj_1 :
  forall b cp', can_access_block m1 b cp' -> can_access_block m2 b cp'.
Proof.
  unfold can_access_block.
  intros b cp' Hown.
  unfold free in FREE.
  destruct Z_le_dec; auto. inv FREE; congruence.
  destruct (range_perm_dec m1 bf lo hi Cur Freeable); [| simpl in FREE; congruence].
  destruct (can_access_block_dec m1 bf cp); [| simpl in FREE; congruence].
  inv FREE. (* rewrite <- Hown. *)
  unfold unchecked_free; destruct (zle hi lo); auto.
Qed.

Lemma free_can_access_block_inj_2 :
  forall b cp', can_access_block m2 b cp' -> can_access_block m1 b cp'.
Proof.
  unfold can_access_block.
  intros b cp' Hown.
  unfold free in FREE.
  destruct Z_le_dec; auto. inv FREE; congruence.
  destruct (range_perm_dec m1 bf lo hi Cur Freeable); [| simpl in FREE; congruence].
  destruct (can_access_block_dec m1 bf cp); [| simpl in FREE; congruence].
  inv FREE. (* rewrite <- Hown. *)
  unfold unchecked_free in *; destruct (zle hi lo); auto.
Qed.

Theorem valid_access_free_1:
  forall chunk b ofs p cp',
  valid_access m1 chunk b ofs p cp' ->
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p cp'.
Proof.
  intros. inv H. destruct H2 as [H2 H3]. constructor; auto with mem.
  red; intros. eapply perm_free_1; eauto.
  destruct (zlt lo hi). intuition. right. lia.
  split; auto.
  apply free_can_access_block_inj_1; auto.
Qed.

Theorem valid_access_free_2:
  forall chunk ofs p cp',
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p cp').
Proof.
  intros; red; intros. inv H2.
  generalize (size_chunk_pos chunk); intros.
  destruct (zlt ofs lo).
  elim (perm_free_2 lo Cur p).
  lia. apply H3. lia.
  elim (perm_free_2 ofs Cur p).
  lia. apply H3. lia.
Qed.

Theorem valid_access_free_inv_1:
  forall chunk b ofs p cp',
  valid_access m2 chunk b ofs p cp' ->
  valid_access m1 chunk b ofs p cp'.
Proof.
  intros. destruct H. split; auto.
  red; intros. generalize (H ofs0 H1).
  rewrite free_result. unfold perm, unchecked_free; destruct (zle hi lo); auto; simpl.
  rewrite PMap.gsspec. destruct (peq b bf). subst b.
  destruct (zle lo ofs0); simpl.
  destruct (zlt ofs0 hi); simpl.
  tauto. auto. auto. auto.
  split.
  apply free_can_access_block_inj_2; easy.
  easy.
Qed.

Theorem valid_access_free_inv_2:
  forall chunk ofs p cp',
  valid_access m2 chunk bf ofs p cp' ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.
Proof.
  intros.
  destruct (zlt lo hi); auto.
  destruct (zle (ofs + size_chunk chunk) lo); auto.
  destruct (zle hi ofs); auto.
  elim (valid_access_free_2 chunk ofs p cp'); auto. lia.
Qed.

Theorem load_free:
  forall chunk b ofs cp',
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs cp' = load chunk m1 b ofs cp'.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b ofs Readable cp').
  rewrite pred_dec_true.
  rewrite free_result; auto.
  unfold unchecked_free; destruct (zle hi lo); auto.
  eapply valid_access_free_inv_1; eauto.
  rewrite pred_dec_false; auto.
  red; intro; elim n. eapply valid_access_free_1; eauto.
Qed.

Theorem load_free_2:
  forall chunk b ofs v cp',
  load chunk m2 b ofs cp' = Some v -> load chunk m1 b ofs cp' = Some v.
Proof.
  intros. unfold load. rewrite pred_dec_true.
  rewrite (load_result _ _ _ _ _ _ H). rewrite free_result; auto.
  unfold unchecked_free; destruct (zle hi lo); auto.
  apply valid_access_free_inv_1. eauto with mem.
Qed.

Theorem loadbytes_free:
  forall b ofs n cp',
  b <> bf \/ lo >= hi \/ ofs + n <= lo \/ hi <= ofs ->
  loadbytes m2 b ofs n cp' = loadbytes m1 b ofs n cp'.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable).
- destruct (can_access_block_dec m2 b cp'); destruct (Z_le_dec n 0).
+ simpl.
  setoid_rewrite pred_dec_true; simpl.
  rewrite free_result; auto.
  unfold unchecked_free; destruct (zle hi lo); auto.
  red; intros. eapply perm_free_3; eauto.
  apply free_can_access_block_inj_2; assumption.
+ simpl.
  setoid_rewrite pred_dec_true at 1 2; simpl.
  rewrite free_result; auto.
  unfold unchecked_free; destruct (zle hi lo); auto.
  red; intros. eapply perm_free_3; eauto.
  apply free_can_access_block_inj_2; assumption.
+ simpl.
  setoid_rewrite pred_dec_true at 1; simpl.
  rewrite orb_true_r; simpl.
  rewrite free_result; auto.
  unfold unchecked_free; destruct (zle hi lo); auto.
  red; intros. eapply perm_free_3; eauto.
+ simpl. setoid_rewrite pred_dec_false at 2.
  rewrite andb_comm. reflexivity.
  intro Hcontra. apply n0. apply free_can_access_block_inj_1; assumption.
- simpl. setoid_rewrite pred_dec_false at 1; auto.
  red; intros. elim n0; red; intros.
  eapply perm_free_1; eauto. destruct H; auto. right; lia.
Qed.

Theorem loadbytes_free_2:
  forall b ofs n cp' bytes,
  loadbytes m2 b ofs n cp' = Some bytes -> loadbytes m1 b ofs n cp' = Some bytes.
Proof.
  intros. unfold loadbytes in *.
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable);
  destruct (can_access_block_dec m2 b cp');
  inv H.
  setoid_rewrite pred_dec_true at 1 2. rewrite free_result; auto.
  unfold unchecked_free; destruct (zle hi lo); auto.
  red; intros. apply perm_free_3; auto.
  apply free_can_access_block_inj_2; assumption.
  destruct Z_le_dec; simpl in *; try congruence.
  setoid_rewrite pred_dec_true at 1. rewrite orb_true_r. rewrite free_result; auto.
  unfold unchecked_free; destruct (zle hi lo); auto.
  red; intros. apply perm_free_3; auto.
Qed.

End FREE.

Local Hint Resolve valid_block_free_1 valid_block_free_2
             perm_free_1 perm_free_2 perm_free_3
             valid_access_free_1 valid_access_free_inv_1: mem.

(** ** Properties related to [drop_perm] *)

Theorem range_perm_drop_1:
  forall m b lo hi p cp m', drop_perm m b lo hi p cp = Some m' -> range_perm m b lo hi Cur Freeable.
Proof.
  unfold drop_perm; intros.
  destruct (Z_le_dec hi lo); inv H.
  - intros ? ?; lia.
  - destruct (range_perm_dec m b lo hi Cur Freeable). auto. discriminate.
Qed.

Theorem range_perm_drop_2:
  forall m b lo hi cp p,
  range_perm m b lo hi Cur Freeable ->
  can_access_block m b cp ->
  {m' | drop_perm m b lo hi p cp = Some m' }.
Proof.
  unfold drop_perm; intros.
  destruct (Z_le_dec hi lo).
  econstructor. eauto.
  destruct (range_perm_dec m b lo hi Cur Freeable).
- destruct (can_access_block_dec m b cp).
+ econstructor. eauto.
+ contradiction.
- contradiction.
Defined.

Section DROP.

Variable m: mem.
Variable b: block.
Variable lo hi: Z.
Variable p: permission.
Variable cp: compartment.
Variable m': mem.
Hypothesis DROP: drop_perm m b lo hi p cp = Some m'.

Theorem nextblock_drop:
  nextblock m' = nextblock m.
Proof.
  unfold drop_perm in DROP.
  destruct Z_le_dec;
  destruct (range_perm_dec m b lo hi Cur Freeable);
  destruct (can_access_block_dec m b cp);
  inv DROP; auto.
Qed.

Theorem drop_perm_valid_block_1:
  forall b', valid_block m b' -> valid_block m' b'.
Proof.
  unfold valid_block; rewrite nextblock_drop; auto.
Qed.

Theorem drop_perm_valid_block_2:
  forall b', valid_block m' b' -> valid_block m b'.
Proof.
  unfold valid_block; rewrite nextblock_drop; auto.
Qed.

Theorem drop_block_compartment:
  forall b', block_compartment m' b' = block_compartment m b'.
Proof.
unfold drop_perm in *.
destruct Z_le_dec; try now inv DROP.
destruct range_perm_dec; try discriminate.
destruct can_access_block_dec; try discriminate.
injection DROP as <-. intros b'. reflexivity.
Qed.

Theorem perm_drop_1:
  forall ofs k, lo <= ofs < hi -> perm m' b ofs k p.
Proof.
  intros.
  unfold drop_perm in DROP.
  destruct Z_le_dec; try lia;
  destruct (range_perm_dec m b lo hi Cur Freeable);
  destruct (can_access_block_dec m b cp);
  inv DROP.
  unfold perm. simpl. rewrite PMap.gss. unfold proj_sumbool.
  rewrite zle_true. rewrite zlt_true. simpl. constructor.
  lia. lia.
Qed.

Theorem perm_drop_2:
  forall ofs k p', lo <= ofs < hi -> perm m' b ofs k p' -> perm_order p p'.
Proof.
  intros.
  unfold drop_perm in DROP.
  destruct Z_le_dec; try lia;
  destruct (range_perm_dec m b lo hi Cur Freeable);
  destruct (can_access_block_dec m b cp);
  inv DROP.
  revert H0. unfold perm; simpl. rewrite PMap.gss. unfold proj_sumbool.
  rewrite zle_true. rewrite zlt_true. simpl. auto.
  lia. lia.
Qed.

Theorem perm_drop_3:
  forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs k p' -> perm m' b' ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP.
  destruct Z_le_dec;
  destruct (range_perm_dec m b lo hi Cur Freeable);
  destruct (can_access_block_dec m b cp);
  inv DROP; auto.
  unfold perm; simpl. rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi).
  byContradiction. intuition lia.
  auto. auto. auto.
Qed.

Theorem perm_drop_4:
  forall b' ofs k p', perm m' b' ofs k p' -> perm m b' ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP.
  destruct Z_le_dec; try lia;
  destruct (range_perm_dec m b lo hi Cur Freeable);
  destruct (can_access_block_dec m b cp);
  inv DROP; auto.
  revert H. unfold perm; simpl. rewrite PMap.gsspec. destruct (peq b' b).
  subst b'. unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi).
  simpl. intros. apply perm_implies with p. apply perm_implies with Freeable. apply perm_cur.
  apply r. tauto. auto with mem. auto.
  auto. auto. auto.
Qed.

Lemma drop_preserves_comp:
  forall b', block_compartment m b' = block_compartment m' b'.
Proof.
  intros b'.
  unfold drop_perm in DROP.
  destruct Z_le_dec; try lia;
  destruct (range_perm_dec m b lo hi Cur Freeable); try (now inversion DROP).
  destruct (can_access_block_dec m b cp); [| now inversion DROP].
  inv DROP. reflexivity.
Qed.

Theorem can_access_block_drop_1:
  forall b' cp', can_access_block m b' cp' -> can_access_block m' b' cp'.
Proof.
  unfold can_access_block. intros b' cp' Hown.
  unfold drop_perm in DROP.
  destruct Z_le_dec; [now inv DROP|];
  destruct (range_perm_dec m b lo hi Cur Freeable); [| now inversion DROP];
  destruct (can_access_block_dec m b cp); [| now inversion DROP].
  inv DROP. assumption.
Qed.

Theorem can_access_block_drop_2:
  forall b' cp', can_access_block m' b' cp' -> can_access_block m b' cp'.
Proof.
  unfold can_access_block. intros b' cp' Hown.
  unfold drop_perm in DROP.
  destruct Z_le_dec; [now inv DROP|];
  destruct (range_perm_dec m b lo hi Cur Freeable); [| now inversion DROP].
  destruct (can_access_block_dec m b cp); [| now inversion DROP].
  inv DROP. assumption.
Qed.

Theorem can_access_block_drop_3:
  hi <= lo \/ can_access_block m b cp.
Proof.
  unfold drop_perm in DROP.
  destruct Z_le_dec; [left; now inv DROP|];
  destruct (range_perm_dec m b lo hi Cur Freeable); [| congruence].
  destruct (can_access_block_dec m b cp); [| congruence].
  right; assumption.
Qed.

Theorem can_access_block_drop_4:
  hi <= lo \/ can_access_block m' b cp.
  unfold drop_perm in DROP.
  destruct Z_le_dec; [left; now inv DROP|];
  destruct (range_perm_dec m b lo hi Cur Freeable); [| congruence].
  destruct (can_access_block_dec m b cp); [| congruence].
  inv DROP. destruct m. unfold can_access_block in *. simpl in *.
  right; assumption.
Qed.

(* RB: NOTE: Other lemmas in the style of perm_drop_*? *)

Lemma valid_access_drop_1:
  forall chunk b' ofs p' cp',
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p p' ->
  valid_access m chunk b' ofs p' cp' -> valid_access m' chunk b' ofs p' cp'.
Proof.
  intros. destruct H0. split; auto.
  red; intros.
  destruct (eq_block b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto.
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. lia.
  generalize (size_chunk_pos chunk); intros. intuition.
  eapply perm_drop_3; eauto.
  split. apply can_access_block_drop_1; easy. easy.
Qed.

Lemma valid_access_drop_2:
  forall chunk b' ofs p' cp',
  valid_access m' chunk b' ofs p' cp' -> valid_access m chunk b' ofs p' cp'.
Proof.
  intros. destruct H; split; auto.
  red; intros. eapply perm_drop_4; eauto.
  split. apply can_access_block_drop_2; easy. easy.
Qed.

Theorem load_drop:
  forall chunk b' ofs cp',
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs cp' = load chunk m b' ofs cp'.
Proof.
  intros.
  unfold load.
  destruct (valid_access_dec m chunk b' ofs Readable).
  rewrite pred_dec_true.
  unfold drop_perm in DROP.
  destruct (Z_le_dec);
  destruct (range_perm_dec m b lo hi Cur Freeable);
  destruct (can_access_block_dec m b cp);
  inv DROP; auto.
  eapply valid_access_drop_1; eauto.
  rewrite pred_dec_false. auto.
  red; intros; elim n. eapply valid_access_drop_2; eauto.
Qed.

Theorem loadbytes_drop:
  forall b' ofs n cp',
  b' <> b \/ ofs + n <= lo \/ hi <= ofs \/ perm_order p Readable ->
  loadbytes m' b' ofs n cp' = loadbytes m b' ofs n cp'.
Proof.
  intros.
  unfold loadbytes.
  destruct (range_perm_dec m b' ofs (ofs + n) Cur Readable).
- destruct (can_access_block_dec m b' cp').
+ setoid_rewrite pred_dec_true at 1 2; simpl.
* unfold drop_perm in DROP.
  destruct (Z_le_dec);
  destruct (range_perm_dec m b lo hi Cur Freeable);
  destruct (can_access_block_dec m b cp);
  inv DROP; auto.
* red; intros.
  destruct (eq_block b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto.
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. lia. intuition.
  eapply perm_drop_3; eauto.
* apply can_access_block_drop_1; assumption.
+ setoid_rewrite pred_dec_false at 2.
  destruct (Z_le_dec n 0); simpl in *; try rewrite orb_true_r; try congruence.
  setoid_rewrite pred_dec_true; simpl; auto.
* unfold drop_perm in DROP.
  destruct Z_le_dec;
  destruct (range_perm_dec m b lo hi Cur Freeable);
  destruct (can_access_block_dec m b cp);
  inv DROP; auto.
* red; intros.
  destruct (eq_block b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto.
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. lia. intuition.
  eapply perm_drop_3; eauto.
* rewrite andb_comm. reflexivity.
* intro Hcontra. apply n0. apply can_access_block_drop_2; assumption.
- setoid_rewrite pred_dec_false at 1; eauto.
  red; intros; elim n0; red; intros.
  eapply perm_drop_4; eauto.
Qed.

End DROP.


Section SET.

Variable m: mem.
Variable b: block.
Variable p: permission.
Variable cp: compartment.
Variable m': mem.
Hypothesis SET: set_perm m b p = Some m'.

Theorem nextblock_set:
  nextblock m' = nextblock m.
Proof.
  unfold set_perm in SET.
  destruct plt; try discriminate.
  inv SET; auto.
Qed.

Theorem set_perm_valid_block_1:
  forall b', valid_block m b' -> valid_block m' b'.
Proof.
  unfold valid_block; rewrite nextblock_set; auto.
Qed.

Theorem set_perm_valid_block_2:
  forall b', valid_block m' b' -> valid_block m b'.
Proof.
  unfold valid_block; rewrite nextblock_set; auto.
Qed.

Theorem set_block_compartment:
  forall b', block_compartment m' b' = block_compartment m b'.
Proof.
unfold set_perm in *. destruct plt; try discriminate.
inv SET. intros b'. reflexivity.
Qed.


Lemma set_preserves_comp:
  forall b', block_compartment m b' = block_compartment m' b'.
Proof.
  intros b'.
  unfold set_perm in SET. destruct plt; try discriminate.
  inv SET. reflexivity.
Qed.

Theorem can_access_block_set_1:
  forall b' cp', can_access_block m b' cp' -> can_access_block m' b' cp'.
Proof.
  unfold can_access_block. intros b' cp' Hown.
  unfold set_perm in SET. destruct plt; try discriminate.
  inv SET. assumption.
Qed.

Theorem can_access_block_set_2:
  forall b' cp', can_access_block m' b' cp' -> can_access_block m b' cp'.
Proof.
  unfold can_access_block. intros b' cp' Hown.
  unfold set_perm in SET. destruct plt; try discriminate.
  inv SET. assumption.
Qed.

Theorem perm_set_1:
  forall ofs k p', perm m b ofs k p' -> perm m' b ofs k p.
Proof.
  intros.
  unfold set_perm in SET.
  destruct plt; try discriminate.
  (* destruct Z_le_dec; try lia; *)
  (* destruct (range_perm_dec m b lo hi Cur Freeable); *)
  (* destruct (can_access_block_dec m b cp); *)
  inv SET.
  unfold perm. simpl. rewrite PMap.gss. unfold perm in *.
  destruct ((mem_access m) # b ofs k) eqn:?. constructor. simpl. inv H.
Qed.

(* Theorem perm_set_2: *)
(*   forall ofs k p', lo <= ofs < hi -> perm m' b ofs k p' -> perm_order p p'. *)
(* Proof. *)
(*   intros. *)
(*   unfold set_perm in SET. *)
(*   destruct Z_le_dec; try lia; *)
(*   destruct (range_perm_dec m b lo hi Cur Freeable); *)
(*   destruct (can_access_block_dec m b cp); *)
(*   inv SET. *)
(*   revert H0. unfold perm; simpl. rewrite PMap.gss. unfold proj_sumbool. *)
(*   rewrite zle_true. rewrite zlt_true. simpl. auto. *)
(*   lia. lia. *)
(* Qed. *)

Theorem perm_set_3:
  forall b' ofs k p', perm_order p p' -> perm m b' ofs k p' ->
                 perm m' b' ofs k p'.
Proof.
  intros.
  unfold set_perm in SET.
  destruct plt; try discriminate.
  (* destruct Z_le_dec; *)
  (* destruct (range_perm_dec m b lo hi Cur Freeable); *)
  (* destruct (can_access_block_dec m b cp); *)
  inv SET; auto.
  unfold perm in *; simpl in *. rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  destruct (((mem_access m) # b ofs k)); auto.
  auto.
Qed.

Theorem perm_set_2:
  forall b' ofs k p', b <> b' -> perm m b' ofs k p' ->
                 perm m' b' ofs k p'.
Proof.
  intros.
  unfold set_perm in SET.
  destruct plt; try discriminate.
  inv SET; auto.
  unfold perm in *; simpl in *. rewrite PMap.gsspec.
  destruct (peq b' b); auto.
  subst b'. contradiction.
Qed.

Theorem perm_set_2':
  forall b' ofs k p', b <> b' -> perm m' b' ofs k p' ->
                 perm m b' ofs k p'.
Proof.
  intros.
  unfold set_perm in SET.
  destruct plt; try discriminate.
  inv SET; auto.
  unfold perm in *; simpl in *. rewrite PMap.gsspec in *.
  destruct (peq b' b); auto.
  subst b'. contradiction.
Qed.

Theorem perm_set_4':
  forall b' ofs k p', b' <> b \/ not (perm m b ofs k Nonempty) -> perm m b' ofs k p' -> perm m' b' ofs k p'.
Proof.
  intros.
  unfold set_perm in SET. destruct plt; try discriminate.
  inv SET; auto.
  revert H H0. unfold perm; simpl. rewrite PMap.gsspec. destruct (peq b' b).
  subst b'. intros []; try now contradiction.
  destruct ((mem_access m) # b ofs k). intros G. exfalso. eapply H. constructor.
  intros G. inv G. eauto.
Qed.

Theorem perm_set_4:
  forall b' ofs k p', b' <> b \/ not (perm m b ofs Max Nonempty) -> perm m' b' ofs k p' -> perm m b' ofs k p'.
Proof.
  intros.
  unfold set_perm in SET. destruct plt; try discriminate.
  inv SET; auto.
  assert (G: b' <> b \/ ~ perm m b ofs k Nonempty).
  { destruct H; try now left.
    right. intros ?. eapply H. eapply perm_max. eauto. } clear H.
  revert G H0. unfold perm; simpl. rewrite PMap.gsspec. destruct (peq b' b).
  subst b'. intros []; try now contradiction.
  destruct ((mem_access m) # b ofs k). intros G. exfalso. eapply H. constructor.
  intros G. inv G. eauto.
Qed.

Lemma set_perm_perm:
  forall b' ofs k p',
    perm m' b' ofs k p' -> exists p'', perm m b' ofs k p''.
Proof.
  intros b' ofs k p' H.
  destruct (peq b b').
  - subst. revert H.
    unfold set_perm in SET.
    destruct plt; try discriminate. inv SET. unfold perm. simpl.
    rewrite PMap.gsspec. rewrite peq_true.
    destruct ((mem_access m) # b' ofs k) eqn:EQ.
    simpl. eexists; eauto. constructor.
    eexists; eauto.
  - eexists; eapply perm_set_2'; eauto.
Qed.

Lemma set_perm_range_perm:
  forall b' lo hi k p',
    range_perm m' b' lo hi k p' -> exists p'', range_perm m b' lo hi k p''.
Proof.
  intros b' lo hi k p' H.
  destruct (peq b b').
  - subst. revert H.
    unfold set_perm in SET.
    destruct plt; try discriminate. inv SET. unfold range_perm. unfold perm. simpl.
    rewrite PMap.gsspec. rewrite peq_true.
    intros H. eexists.
    intros ofs ofs_range; specialize (H ofs ofs_range).
    destruct ((mem_access m) # b' ofs k) eqn:EQ.
    simpl. constructor. eauto.
  - eexists; intros ofs ofs_range; specialize (H ofs ofs_range); eapply perm_set_2'; eauto.
Qed.


Lemma valid_access_set_1:
  forall chunk b' ofs cp',
  perm_order p Readable ->
  valid_access m chunk b' ofs Readable cp' -> valid_access m' chunk b' ofs Readable cp'.
Proof.
  intros. destruct H0. split; auto.
  red; intros.
  destruct (eq_block b' b). subst b'.
  (* destruct (zlt ofs0 lo). *) eapply perm_set_3; eauto.
  (* destruct (zle hi ofs0). *) eapply perm_set_3; eauto.
  split. apply can_access_block_set_1; easy. easy.
Qed.

(* Lemma valid_access_set_2: *)
(*   forall chunk b' ofs p' cp', *)
(*   perm_order p Readable -> *)
(*   valid_access m' chunk b' ofs p' cp' -> valid_access m chunk b' ofs p' cp'. *)
(* Proof. *)
(*   intros. destruct H; split; auto. *)
(*   red; intros. eapply perm_set_4; eauto. *)
(*   split. apply can_access_block_set_2; easy. easy. *)
(* Qed. *)

Theorem load_set:
  forall chunk b' ofs cp' v,
  perm_order p Readable ->
  load chunk m b' ofs cp' = Some v ->
  load chunk m' b' ofs cp' = Some v.
Proof.
  intros. revert H0.
  unfold load.
  destruct (valid_access_dec m chunk b' ofs Readable).
  rewrite pred_dec_true.
  unfold set_perm in SET. destruct plt; try discriminate.
  inv SET; auto.
  eapply valid_access_set_1; eauto.
  discriminate.
Qed.

Theorem load_set':
  forall chunk b' ofs cp' v,
  perm_order p Readable ->
  Mem.range_perm m b' ofs (ofs + size_chunk chunk) Cur Readable ->
  load chunk m' b' ofs cp' = Some v ->
  load chunk m b' ofs cp' = Some v.
Proof.
  intros. revert H1.
  unfold load.
  destruct (valid_access_dec m chunk b' ofs Readable).
  rewrite pred_dec_true.
  unfold set_perm in SET. destruct plt; try discriminate.
  inv SET; auto.
  eapply valid_access_set_1; eauto.
  destruct (valid_access_dec m' chunk b' ofs Readable); try discriminate.
  elim n.
  destruct v0. split. eauto. split; try easy.
  simpl. unfold set_perm in SET. inv SET; auto. simpl in *.
 destruct plt; try discriminate. inv H4. easy.
Qed.

(* Theorem loadbytes_set: *)
(*   forall b' ofs n cp', *)
(*   b' <> b \/ ofs + n <= lo \/ hi <= ofs \/ perm_order p Readable -> *)
(*   loadbytes m' b' ofs n cp' = loadbytes m b' ofs n cp'. *)
(* Proof. *)
(*   intros. *)
(*   unfold loadbytes. *)
(*   destruct (range_perm_dec m b' ofs (ofs + n) Cur Readable). *)
(* - destruct (can_access_block_dec m b' cp'). *)
(* + setoid_rewrite pred_dec_true at 1 2; simpl. *)
(* * unfold set_perm in SET. *)
(*   destruct (Z_le_dec); *)
(*   destruct (range_perm_dec m b lo hi Cur Freeable); *)
(*   destruct (can_access_block_dec m b cp); *)
(*   inv SET; auto. *)
(* * red; intros. *)
(*   destruct (eq_block b' b). subst b'. *)
(*   destruct (zlt ofs0 lo). eapply perm_set_3; eauto. *)
(*   destruct (zle hi ofs0). eapply perm_set_3; eauto. *)
(*   apply perm_implies with p. eapply perm_set_1; eauto. lia. intuition. *)
(*   eapply perm_set_3; eauto. *)
(* * apply can_access_block_set_1; assumption. *)
(* + setoid_rewrite pred_dec_false at 2. *)
(*   destruct (Z_le_dec n 0); simpl in *; try rewrite orb_true_r; try congruence. *)
(*   setoid_rewrite pred_dec_true; simpl; auto. *)
(* * unfold set_perm in SET. *)
(*   destruct Z_le_dec; *)
(*   destruct (range_perm_dec m b lo hi Cur Freeable); *)
(*   destruct (can_access_block_dec m b cp); *)
(*   inv SET; auto. *)
(* * red; intros. *)
(*   destruct (eq_block b' b). subst b'. *)
(*   destruct (zlt ofs0 lo). eapply perm_set_3; eauto. *)
(*   destruct (zle hi ofs0). eapply perm_set_3; eauto. *)
(*   apply perm_implies with p. eapply perm_set_1; eauto. lia. intuition. *)
(*   eapply perm_set_3; eauto. *)
(* * rewrite andb_comm. reflexivity. *)
(* * intro Hcontra. apply n0. apply can_access_block_set_2; assumption. *)
(* - setoid_rewrite pred_dec_false at 1; eauto. *)
(*   red; intros; elim n0; red; intros. *)
(*   eapply perm_set_4; eauto. *)
(* Qed. *)

End SET.

(** * Generic injections *)

(** A memory state [m1] generically injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address.
*)

Record mem_inj (f: meminj) (m1 m2: mem) : Prop :=
  mk_mem_inj {
    mi_perm:
      forall b1 b2 delta ofs k p,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs k p ->
      perm m2 b2 (ofs + delta) k p;
      (* TODO: rename [mi_own] into [mi_access] *)
    mi_access:
      forall b1 b2 delta ofs p k,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs k p ->
      Mem.block_compartment m1 b1 = Mem.block_compartment m2 b2;
      (* can_access_block m1 b1 cp -> *)
      (* can_access_block m2 b2 cp; *)
    mi_align:
      forall b1 b2 delta chunk ofs p,
      f b1 = Some(b2, delta) ->
      range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p ->
      (align_chunk chunk | delta);
    mi_memval:
      forall b1 ofs b2 delta,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs Cur Readable ->
      memval_inject f (ZMap.get ofs m1.(mem_contents)#b1) (ZMap.get (ofs+delta) m2.(mem_contents)#b2)
  }.

Lemma mi_own (f: meminj) (m1 m2: mem):
  mem_inj f m1 m2 ->
  forall b1 b2 delta cp ofs p k,
    f b1 = Some(b2, delta) ->
    perm m1 b1 ofs k p ->
    can_access_block m1 b1 cp ->
    can_access_block m2 b2 cp.
Proof.
  intros until k.
  intros ? ?.
  unfold can_access_block.
  erewrite mi_access; eauto.
Qed.


(** Preservation of permissions *)

Lemma perm_inj:
  forall f m1 m2 b1 ofs k p b2 delta,
  mem_inj f m1 m2 ->
  perm m1 b1 ofs k p ->
  f b1 = Some(b2, delta) ->
  perm m2 b2 (ofs + delta) k p.
Proof.
  intros. eapply mi_perm; eauto.
Qed.

Lemma range_perm_inj:
  forall f m1 m2 b1 lo hi k p b2 delta,
  mem_inj f m1 m2 ->
  range_perm m1 b1 lo hi k p ->
  f b1 = Some(b2, delta) ->
  range_perm m2 b2 (lo + delta) (hi + delta) k p.
Proof.
  intros; red; intros.
  replace ofs with ((ofs - delta) + delta) by lia.
  eapply perm_inj; eauto. apply H0. lia.
Qed.

Lemma can_access_block_inj:
  forall f m1 m2 b1 cp b2 delta ofs p k,
  mem_inj f m1 m2 ->
  can_access_block m1 b1 cp ->
  f b1 = Some(b2, delta) ->
  perm m1 b1 ofs p k ->
  can_access_block m2 b2 cp.
Proof.
  intros; red.
  eapply mi_own; eauto.
Qed.

Lemma valid_access_inj:
  forall f m1 m2 b1 b2 delta chunk ofs p cp,
  mem_inj f m1 m2 ->
  f b1 = Some(b2, delta) ->
  valid_access m1 chunk b1 ofs p cp ->
  valid_access m2 chunk b2 (ofs + delta) p cp.
Proof.
  intros. destruct H1 as [A [B C]]. constructor.
  replace (ofs + delta + size_chunk chunk)
     with ((ofs + size_chunk chunk) + delta) by lia.
  eapply range_perm_inj; eauto.
  split. eapply mi_own; eauto. apply A with (ofs := ofs). destruct chunk; simpl; lia.
  apply Z.divide_add_r; auto. eapply mi_align; eauto with mem.
Qed.

(** Preservation of loads. *)

Lemma getN_inj:
  forall f m1 m2 b1 b2 delta,
  mem_inj f m1 m2 ->
  f b1 = Some(b2, delta) ->
  forall n ofs,
  range_perm m1 b1 ofs (ofs + Z.of_nat n) Cur Readable ->
  list_forall2 (memval_inject f)
               (getN n ofs (m1.(mem_contents)#b1))
               (getN n (ofs + delta) (m2.(mem_contents)#b2)).
Proof.
  induction n; intros; simpl.
  constructor.
  rewrite Nat2Z.inj_succ in H1.
  constructor.
  eapply mi_memval; eauto.
  apply H1. lia.
  replace (ofs + delta + 1) with ((ofs + 1) + delta) by lia.
  apply IHn. red; intros; apply H1; lia.
Qed.

Lemma load_inj:
  forall f m1 m2 chunk b1 ofs cp b2 delta v1,
  mem_inj f m1 m2 ->
  load chunk m1 b1 ofs cp = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) cp = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros.
  exists (decode_val chunk (getN (size_chunk_nat chunk) (ofs + delta) (m2.(mem_contents)#b2))).
  split. unfold load. apply pred_dec_true.
  eapply valid_access_inj; eauto with mem.
  exploit load_result; eauto. intro. rewrite H2.
  apply decode_val_inject. apply getN_inj; auto.
  rewrite <- size_chunk_conv. exploit load_valid_access; eauto. intros [A B]. auto.
Qed.

Lemma loadbytes_inj:
  forall f m1 m2 len b1 ofs cp b2 delta bytes1,
  mem_inj f m1 m2 ->
  loadbytes m1 b1 ofs len cp = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len cp = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2.
Proof.
  intros. unfold loadbytes in *.
  destruct (range_perm_dec m1 b1 ofs (ofs + len) Cur Readable);
  destruct (can_access_block_dec m1 b1 cp);
  destruct (Z_le_dec len 0);
  inv H0.
  - exists (getN (Z.to_nat len) (ofs + delta) (m2.(mem_contents)#b2)).
    split. setoid_rewrite pred_dec_true at 1. rewrite orb_true_r. reflexivity.
    replace (ofs + delta + len) with ((ofs + len) + delta) by lia.
    eapply range_perm_inj; eauto with mem.
    (* eapply mi_own; eauto. eapply r with (ofs := ofs). destruct len; try lia. *)
    apply getN_inj; auto.
    (* destruct (zle 0 len). *)
    (* rewrite Z2Nat.id by lia. auto. *)
    rewrite Z_to_nat_neg by extlia. simpl. red; intros; extlia.
  - exists (getN (Z.to_nat len) (ofs + delta) (m2.(mem_contents)#b2)).
    split. setoid_rewrite pred_dec_true at 1 2. reflexivity.
    replace (ofs + delta + len) with ((ofs + len) + delta) by lia.
    eapply range_perm_inj; eauto with mem.
    eapply mi_own; eauto. eapply r with (ofs := ofs). destruct len; try lia.
    apply getN_inj; auto.
    destruct (zle 0 len).
    rewrite Z2Nat.id by lia. auto.
    rewrite Z_to_nat_neg by extlia. simpl. red; intros; extlia.
  - exists (getN (Z.to_nat len) (ofs + delta) (m2.(mem_contents)#b2)).
    split. setoid_rewrite pred_dec_true at 1. rewrite orb_true_r. reflexivity.
    replace (ofs + delta + len) with ((ofs + len) + delta) by lia.
    eapply range_perm_inj; eauto with mem.
    (* eapply mi_own; eauto. eapply r with (ofs := ofs). destruct len; try lia. *)
    apply getN_inj; auto.
    (* destruct (zle 0 len). *)
    (* rewrite Z2Nat.id by lia. auto. *)
    rewrite Z_to_nat_neg by extlia. simpl. red; intros; extlia.
Qed.

(** Preservation of stores. *)

Lemma setN_inj:
  forall (access: Z -> Prop) delta f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  forall p c1 c2,
  (forall q, access q -> memval_inject f (ZMap.get q c1) (ZMap.get (q + delta) c2)) ->
  (forall q, access q -> memval_inject f (ZMap.get q (setN vl1 p c1))
                                         (ZMap.get (q + delta) (setN vl2 (p + delta) c2))).
Proof.
  induction 1; intros; simpl.
  auto.
  replace (p + delta + 1) with ((p + 1) + delta) by lia.
  apply IHlist_forall2; auto.
  intros. rewrite ZMap.gsspec at 1. destruct (ZIndexed.eq q0 p). subst q0.
  rewrite ZMap.gss. auto.
  rewrite ZMap.gso. auto. unfold ZIndexed.t in *. lia.
Qed.

Definition meminj_no_overlap (f: meminj) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m b1 ofs1 Max Nonempty ->
  perm m b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

Lemma store_mapped_inj:
  forall f chunk m1 b1 ofs v1 cp n1 m2 b2 delta v2,
  mem_inj f m1 m2 ->
  store chunk m1 b1 ofs v1 cp = Some n1 ->
  meminj_no_overlap f m1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 cp = Some n2
    /\ mem_inj f n1 n2.
Proof.
  intros.
  assert (valid_access m2 chunk b2 (ofs + delta) Writable cp).
    eapply valid_access_inj; eauto with mem.
  destruct (valid_access_store _ _ _ _ _ v2 H4) as [n2 STORE].
  exists n2; split. auto.
  constructor.
(* perm *)
  intros. eapply perm_store_1; [eexact STORE|].
  eapply mi_perm; eauto.
  eapply perm_store_2; eauto.
(* own *)
  intros.
  simpl.
  rewrite <- (store_preserves_comp _ _ _ _ _ _ _ STORE); eauto.
  simpl. rewrite <- (store_preserves_comp _ _ _ _ _ _ _ H0); eauto.
  eapply mi_access; try eassumption.
  eapply perm_store_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros; eauto with mem.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ _ H0).
  rewrite (store_mem_contents _ _ _ _ _ _ _ STORE).
  rewrite ! PMap.gsspec.
  destruct (peq b0 b1). subst b0.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite peq_true.
  apply setN_inj with (access := fun ofs => perm m1 b1 ofs Cur Readable).
  apply encode_val_inject; auto. intros. eapply mi_memval; eauto. eauto with mem.
  destruct (peq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  rewrite setN_other. eapply mi_memval; eauto. eauto with mem.
  rewrite encode_val_length. rewrite <- size_chunk_conv. intros.
  assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
    eapply H1; eauto. eauto 6 with mem.
    exploit store_valid_access_3. eexact H0. intros [A B].
    eapply perm_implies. apply perm_cur_max. apply A. lia. auto with mem.
  destruct H8. congruence. lia.
  (* block <> b1, block <> b2 *)
  eapply mi_memval; eauto. eauto with mem.
Qed.

Lemma store_unmapped_inj:
  forall f chunk m1 b1 ofs v1 cp n1 m2,
  mem_inj f m1 m2 ->
  store chunk m1 b1 ofs v1 cp = Some n1 ->
  f b1 = None ->
  mem_inj f n1 m2.
Proof.
  intros. constructor.
(* perm *)
  intros. eapply mi_perm; eauto with mem.
(* own *)
  intros.
  (* RB: NOTE: Should be solvable by properly extended hint databases. *)
  simpl. erewrite <- store_preserves_comp; eauto.
  eapply mi_access; eauto.
  eapply perm_store_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros; eauto with mem.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ _ H0).
  rewrite PMap.gso. eapply mi_memval; eauto with mem.
  congruence.
Qed.

Lemma store_outside_inj:
  forall f m1 m2 chunk b ofs v cp m2',
  mem_inj f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v cp = Some m2' ->
  mem_inj f m1 m2'.
Proof.
  intros. inv H. constructor.
(* perm *)
  eauto with mem.
(* own *)
  intros.
  (* RB: NOTE: Ditto re: hint databases. *)
  simpl; rewrite <- (store_preserves_comp _ _ _ _ _ _ _ H1); eauto.
(* access *)
  intros; eapply mi_align0; eauto.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ _ H1).
  rewrite PMap.gsspec. destruct (peq b2 b). subst b2.
  rewrite setN_outside. auto.
  rewrite encode_val_length. rewrite <- size_chunk_conv.
  destruct (zlt (ofs0 + delta) ofs); auto.
  destruct (zle (ofs + size_chunk chunk) (ofs0 + delta)). lia.
  byContradiction. eapply H0; eauto. lia.
  eauto with mem.
Qed.

Lemma storebytes_mapped_inj:
  forall f m1 b1 ofs bytes1 cp n1 m2 b2 delta bytes2,
  mem_inj f m1 m2 ->
  storebytes m1 b1 ofs bytes1 cp = Some n1 ->
  meminj_no_overlap f m1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 cp = Some n2
    /\ mem_inj f n1 n2.
Proof.
  intros. inversion H.
  assert (range_perm m2 b2 (ofs + delta) (ofs + delta + Z.of_nat (length bytes2)) Cur Writable).
    replace (ofs + delta + Z.of_nat (length bytes2))
       with ((ofs + Z.of_nat (length bytes1)) + delta).
    eapply range_perm_inj; eauto with mem.
    eapply storebytes_range_perm; eauto.
    rewrite (list_forall2_length H3). lia.
  destruct (range_perm_storebytes _ _ _ _ cp H4) as [n2 STORE].
  { unfold storebytes in H0.
    destruct (range_perm_dec m1 b1 ofs (ofs + Z.of_nat (Datatypes.length bytes1)) Cur Writable); try discriminate.
    simpl in *.
    destruct (Nat.eq_dec (Datatypes.length bytes1) 0). erewrite <- list_forall2_length; eauto.
    destruct can_access_block_dec; try now auto.
    left; erewrite <- mi_access0; eauto.
    eapply r with (ofs := ofs). lia. }
  exists n2; split. eauto.
  constructor.
(* perm *)
  intros.
  eapply perm_storebytes_1; [apply STORE |].
  eapply mi_perm0; eauto.
  eapply perm_storebytes_2; eauto.
(* own *)
  intros.
  erewrite <- (storebytes_preserves_comp _ _ _ _ _ _ STORE).
  erewrite <- (storebytes_preserves_comp); eauto.
  eapply mi_access0; eauto.
  eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  assert (perm m1 b0 ofs0 Cur Readable). eapply perm_storebytes_2; eauto.
  rewrite (storebytes_mem_contents _ _ _ _ _ _ H0).
  rewrite (storebytes_mem_contents _ _ _ _ _ _ STORE).
  rewrite ! PMap.gsspec. destruct (peq b0 b1). subst b0.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite peq_true.
  apply setN_inj with (access := fun ofs => perm m1 b1 ofs Cur Readable); auto.
  destruct (peq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  rewrite setN_other. auto.
  intros.
  assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
    eapply H1; eauto 6 with mem.
    exploit storebytes_range_perm. eexact H0.
    instantiate (1 := r - delta).
    rewrite (list_forall2_length H3). lia.
    eauto 6 with mem.
  destruct H9. congruence. lia.
  eauto.
Qed.

Lemma storebytes_unmapped_inj:
  forall f m1 b1 ofs bytes1 cp n1 m2,
  mem_inj f m1 m2 ->
  storebytes m1 b1 ofs bytes1 cp = Some n1 ->
  f b1 = None ->
  mem_inj f n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* perm *)
  intros. eapply mi_perm0; eauto. eapply perm_storebytes_2; eauto.
(* own *)
  intros.
  erewrite <- mi_access0; try eassumption.
  erewrite <- storebytes_preserves_comp; eauto.
  eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  rewrite (storebytes_mem_contents _ _ _ _ _ _ H0).
  rewrite PMap.gso. eapply mi_memval0; eauto. eapply perm_storebytes_2; eauto.
  congruence.
Qed.

Lemma storebytes_outside_inj:
  forall f m1 m2 b ofs bytes2 cp m2',
  mem_inj f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z.of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 cp = Some m2' ->
  mem_inj f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros. eapply perm_storebytes_1; eauto with mem.
(* own *)
  intros.
  erewrite <- (storebytes_preserves_comp _ _ _ _ _ _ H1); eauto.
(* align *)
  eauto.
(* mem_contents *)
  intros.
  rewrite (storebytes_mem_contents _ _ _ _ _ _ H1).
  rewrite PMap.gsspec. destruct (peq b2 b). subst b2.
  rewrite setN_outside. auto.
  destruct (zlt (ofs0 + delta) ofs); auto.
  destruct (zle (ofs + Z.of_nat (length bytes2)) (ofs0 + delta)). lia.
  byContradiction. eapply H0; eauto. lia.
  eauto with mem.
Qed.

Lemma storebytes_empty_inj:
  forall f m1 b1 ofs1 cp1 m1' m2 b2 ofs2 cp2 m2',
  mem_inj f m1 m2 ->
  storebytes m1 b1 ofs1 nil cp1 = Some m1' ->
  storebytes m2 b2 ofs2 nil cp2 = Some m2' ->
  mem_inj f m1' m2'.
Proof.
  intros. destruct H. constructor.
(* perm *)
  intros.
  eapply perm_storebytes_1; eauto.
  eapply mi_perm0; eauto.
  eapply perm_storebytes_2; eauto.
(* own *)
  intros.
  erewrite <- storebytes_preserves_comp; eauto.
  erewrite mi_access0; eauto.
  erewrite storebytes_preserves_comp; eauto.
  eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  assert (perm m1 b0 ofs Cur Readable). eapply perm_storebytes_2; eauto.
  rewrite (storebytes_mem_contents _ _ _ _ _ _ H0).
  rewrite (storebytes_mem_contents _ _ _ _ _ _ H1).
  simpl. rewrite ! PMap.gsspec.
  destruct (peq b0 b1); destruct (peq b3 b2); subst; eapply mi_memval0; eauto.
Qed.

(** Preservation of allocations *)

Lemma alloc_right_inj:
  forall f m1 m2 c lo hi b2 m2',
  mem_inj f m1 m2 ->
  alloc m2 c lo hi = (m2', b2) ->
  mem_inj f m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* perm *)
  intros. eapply perm_alloc_1; eauto.
(* own *)
  intros.
  symmetry. erewrite alloc_block_compartment; eauto.
  destruct eq_block; [subst | erewrite mi_access0; eauto].
  eapply mi_perm0 in H2; eauto. eapply perm_valid_block in H2.
  unfold valid_block in H2. now exploit Plt_strict; eauto.
(* align *)
  eauto.
(* mem_contents *)
  intros.
  assert (perm m2 b0 (ofs + delta) Cur Readable).
    eapply mi_perm0; eauto.
  assert (valid_block m2 b0) by eauto with mem.
  rewrite <- MEM; simpl. rewrite PMap.gso. eauto with mem.
  rewrite NEXT. eauto with mem.
Qed.

Lemma alloc_left_unmapped_inj:
  forall f m1 m2 c lo hi m1' b1,
  mem_inj f m1 m2 ->
  alloc m1 c lo hi = (m1', b1) ->
  f b1 = None ->
  mem_inj f m1' m2.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros. exploit perm_alloc_inv; eauto. intros.
  destruct (eq_block b0 b1). congruence. eauto.
(* own *)
  intros.
  erewrite <- mi_access0; eauto.
  erewrite alloc_block_compartment; eauto.
  destruct (eq_block b0 b1); subst; auto. congruence.
  exploit perm_alloc_inv; eauto.
  destruct (eq_block b0 b1). congruence. eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. exploit perm_alloc_inv; eauto.
  destruct (eq_block b0 b1); auto. congruence.
(* mem_contents *)
  injection H0; intros NEXT MEM. intros.
  rewrite <- MEM; simpl. rewrite NEXT.
  exploit perm_alloc_inv; eauto. intros.
  rewrite PMap.gsspec. unfold eq_block in H4. destruct (peq b0 b1).
  rewrite ZMap.gi. constructor. eauto.
Qed.

Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

(* RB: NOTE: Keep track of added assumptions and their effect on proofs. *)
Lemma alloc_left_mapped_inj:
  forall f m1 m2 c lo hi m1' b1 b2 delta,
  mem_inj f m1 m2 ->
  alloc m1 c lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  inj_offset_aligned delta (hi-lo) ->
  (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
  f b1 = Some(b2, delta) ->
  forall ACCESS : Mem.block_compartment m2 b2 = c,
  mem_inj f m1' m2.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros.
  exploit perm_alloc_inv; eauto. intros. destruct (eq_block b0 b1). subst b0.
  rewrite H4 in H5; inv H5. eauto. eauto.
(* own *)
  intros. destruct (eq_block b0 b1).
  { subst b0. rewrite H4 in H5. inv H5.
    erewrite owned_new_block; eauto. }
  { erewrite <- mi_access0; eauto.
    erewrite alloc_block_compartment; eauto.
    destruct (eq_block b0 b1). congruence. eauto.
    exploit perm_alloc_inv; eauto. intros.
    destruct (eq_block b0 b1). congruence. eauto. }
(* align *)
  intros. destruct (eq_block b0 b1).
  subst b0. assert (delta0 = delta) by congruence. subst delta0.
  assert (lo <= ofs < hi).
  { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); lia. }
  assert (lo <= ofs + size_chunk chunk - 1 < hi).
  { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); lia. }
  apply H2. lia.
  eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. eapply perm_alloc_4; eauto.
(* mem_contents *)
  injection H0; intros NEXT MEM.
  intros. rewrite <- MEM; simpl. rewrite NEXT.
  exploit perm_alloc_inv; eauto. intros.
  rewrite PMap.gsspec. unfold eq_block in H7.
  destruct (peq b0 b1). rewrite ZMap.gi. constructor. eauto.
Qed.

Lemma free_left_inj:
  forall f m1 m2 b lo hi cp m1',
  mem_inj f m1 m2 ->
  free m1 b lo hi cp = Some m1' ->
  mem_inj f m1' m2.
Proof.
  intros. exploit free_result; eauto. intro FREE.
  destruct (zle hi lo) eqn:R; [unfold unchecked_free in *; rewrite R in *; subst|]; auto.
  inversion H. constructor.
(* perm *)
  intros. eauto with mem.
(* own *)
  intros. erewrite <- mi_access0; eauto.
  erewrite <- free_preserves_comp; eauto.
  eauto with mem.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros; eapply perm_free_3; eauto.
(* mem_contents *)
  intros. rewrite FREE; simpl.
  unfold unchecked_free; rewrite R in *; simpl. eauto with mem.
Qed.

Lemma free_right_inj:
  forall f m1 m2 b lo hi cp m2',
  mem_inj f m1 m2 ->
  free m2 b lo hi cp = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  mem_inj f m1 m2'.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H.
  assert (PERM:
    forall b1 b2 delta ofs k p,
    f b1 = Some (b2, delta) ->
    perm m1 b1 ofs k p -> perm m2' b2 (ofs + delta) k p).
  intros.
  intros. eapply perm_free_1; eauto.
  destruct (eq_block b2 b); auto. subst b. right.
  assert (~ (lo <= ofs + delta < hi)). red; intros; eapply H1; eauto.
  lia.
  constructor.
(* perm *)
  auto.
(* own *)
  intros.
  erewrite <- (free_preserves_comp _ _ _ _ _ _ H0); eauto.
(* align *)
  eapply mi_align0; eauto.
(* mem_contents *)
  intros. rewrite FREE; simpl.
  unfold unchecked_free; destruct (zle hi lo); eauto.
Qed.

(** Preservation of [drop_perm] operations. *)

Lemma drop_unmapped_inj:
  forall f m1 m2 b lo hi p cp m1',
  mem_inj f m1 m2 ->
  drop_perm m1 b lo hi p cp = Some m1' ->
  f b = None ->
  mem_inj f m1' m2.
Proof.
  intros. inv H. constructor.
(* perm *)
  intros. eapply mi_perm0; eauto. eapply perm_drop_4; eauto.
(* own *)
  intros. erewrite <- mi_access0; eauto.
  erewrite <- drop_preserves_comp; eauto.
  eapply perm_drop_4; eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p0); eauto.
  red; intros; eapply perm_drop_4; eauto.
(* contents *)
  intros.
  replace (ZMap.get ofs m1'.(mem_contents)#b1) with (ZMap.get ofs m1.(mem_contents)#b1).
  apply mi_memval0; auto. eapply perm_drop_4; eauto.
  unfold drop_perm in H0;
  destruct Z_le_dec;
  destruct (range_perm_dec m1 b lo hi Cur Freeable);
  destruct (can_access_block_dec m1 b cp);
  inv H0; auto.
Qed.

(* Definition meminj_no_dispute (f: meminj) (m: mem) : Prop := *)
(*   forall b1 b1' delta1 cp1 b2 b2' delta2 cp2, *)
(*   b1 <> b2 -> *)
(*   f b1 = Some (b1', delta1) -> *)
(*   f b2 = Some (b2', delta2) -> *)
(*   can_access_block m b1 cp1 -> *)
(*   can_access_block m b2 cp2 -> *)
(*   b1' <> b2' \/ cp1 <> cp2. *)

Lemma drop_mapped_inj:
  forall f m1 m2 b1 b2 delta lo hi p cp m1',
  mem_inj f m1 m2 ->
  drop_perm m1 b1 lo hi p cp = Some m1' ->
  meminj_no_overlap f m1 ->
  (* forall DISP : meminj_no_dispute f m1, *)
  f b1 = Some(b2, delta) ->
  exists m2',
      drop_perm m2 b2 (lo + delta) (hi + delta) p cp = Some m2'
   /\ mem_inj f m1' m2'.
Proof.
  intros.
  assert ({ m2' | drop_perm m2 b2 (lo + delta) (hi + delta) p cp = Some m2' }).
  { destruct (Z_le_dec hi lo) eqn:EQ.
    - unfold drop_perm in *; rewrite EQ in *.
      destruct (Z_le_dec (hi + delta) (lo + delta)). econstructor; eauto.
      lia.
    - apply range_perm_drop_2. red; intros.
      replace ofs with ((ofs - delta) + delta) by lia.
      eapply perm_inj; eauto. eapply range_perm_drop_1; eauto. lia.
      exploit can_access_block_drop_3; eauto. intros [? | ?]; try lia.
      eapply mi_own; eauto. eapply range_perm_drop_1 with (ofs := lo); eauto. lia. }
  destruct X as [m2' DROP]. exists m2'; split; auto.
  inv H.
  constructor.
(* perm *)
  intros.
  assert (perm m2 b3 (ofs + delta0) k p0).
    eapply mi_perm0; eauto. eapply perm_drop_4; eauto.
  destruct (eq_block b1 b0).
  (* b1 = b0 *)
  subst b0. rewrite H2 in H; inv H.
  destruct (zlt (ofs + delta0) (lo + delta0)). eapply perm_drop_3; eauto.
  destruct (zle (hi + delta0) (ofs + delta0)). eapply perm_drop_3; eauto.
  assert (perm_order p p0).
    eapply perm_drop_2.  eexact H0. instantiate (1 := ofs). lia. eauto.
  apply perm_implies with p; auto.
  eapply perm_drop_1. eauto. lia.
  (* b1 <> b0 *)
  eapply perm_drop_3; eauto.
  destruct (eq_block b3 b2); auto.
  destruct (zlt (ofs + delta0) (lo + delta)); auto.
  destruct (zle (hi + delta) (ofs + delta0)); auto.
  exploit H1; eauto.
  instantiate (1 := ofs + delta0 - delta).
  apply perm_cur_max. apply perm_implies with Freeable.
  eapply range_perm_drop_1; eauto. lia. auto with mem.
  eapply perm_drop_4; eauto. eapply perm_max. apply perm_implies with p0. eauto.
  eauto with mem.
  intuition.
(* own *)
  intros.
  pose proof (drop_preserves_comp _ _ _ _ _ _ _ H0) as Hown1.
  rewrite <- (Hown1 b0).
  pose proof (drop_preserves_comp _ _ _ _ _ _ _ DROP) as Hown2.
  rewrite <- (Hown2 b3).
  erewrite <- mi_access0; eauto.
  { assert (perm m2 b3 (ofs + delta0) k p0).
    { eapply mi_perm0; eauto. eapply perm_drop_4; eauto. }
    destruct (eq_block b1 b0).
    - (* b1 = b0 *)
      subst b0. rewrite H2 in H; inv H.
      destruct (zlt (ofs + delta0) (lo + delta0)). eapply perm_drop_4; eauto.
      destruct (zle (hi + delta0) (ofs + delta0)). eapply perm_drop_4; eauto.
      assert (perm_order p p0).
      eapply perm_drop_2. eexact H0. instantiate (1 := ofs). lia. eauto.
      eapply perm_drop_4. eauto.
      apply perm_implies with p0; auto. constructor.
    - (* b1 <> b0 *)
      eapply perm_drop_4; eauto. }
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p0); eauto.
  red; intros; eapply perm_drop_4; eauto.
(* memval *)
  intros.
  replace (m1'.(mem_contents)#b0) with (m1.(mem_contents)#b0).
  replace (m2'.(mem_contents)#b3) with (m2.(mem_contents)#b3).
  apply mi_memval0; auto. eapply perm_drop_4; eauto.
  unfold drop_perm in DROP;
    destruct (Z_le_dec);
  destruct (range_perm_dec m2 b2 (lo + delta) (hi + delta) Cur Freeable);
  destruct (can_access_block_dec m2 b2 cp);
  inv DROP; auto.
  unfold drop_perm in H0;
    destruct (Z_le_dec);
  destruct (range_perm_dec m1 b1 lo hi Cur Freeable);
  destruct (can_access_block_dec m1 b1 cp);
  inv H0; auto.
Qed.

Lemma drop_outside_inj: forall f m1 m2 b lo hi p cp m2',
  mem_inj f m1 m2 ->
  drop_perm m2 b lo hi p cp = Some m2' ->
  (forall b' delta ofs' k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs' k p ->
    lo <= ofs' + delta < hi -> False) ->
  mem_inj f m1 m2'.
Proof.
  intros. inv H. constructor.
  (* perm *)
  intros. eapply perm_drop_3; eauto.
  destruct (eq_block b2 b); auto. subst b2. right.
  destruct (zlt (ofs + delta) lo); auto.
  destruct (zle hi (ofs + delta)); auto.
  byContradiction. exploit H1; eauto. lia.
  (* own *)
  intros.
  erewrite <- (drop_preserves_comp _ _ _ _ _ _ _ H0); eauto.
  (* align *)
  eapply mi_align0; eauto.
  (* contents *)
  intros.
  replace (m2'.(mem_contents)#b2) with (m2.(mem_contents)#b2).
  apply mi_memval0; auto.
  unfold drop_perm in H0;
    destruct Z_le_dec;
  destruct (range_perm_dec m2 b lo hi Cur Freeable);
  destruct (can_access_block_dec m2 b cp);
  inv H0; auto.
Qed.


(** Preservation of [set_perm] operations. *)

Lemma set_unmapped_inj:
  forall f m1 m2 b p m1',
  mem_inj f m1 m2 ->
  set_perm m1 b p = Some m1' ->
  f b = None ->
  mem_inj f m1' m2.
Proof.
  intros. unfold set_perm in *; destruct plt; try discriminate.
  inv H0.
  inv H. constructor.
(* perm *)
  intros. eapply mi_perm0; eauto. unfold perm in *.
  destruct (peq b1 b); try congruence. simpl in H0. rewrite PMap.gso in H0; auto.
(* own *)
  intros. erewrite <- mi_access0; eauto.
  unfold block_compartment in *; eauto.
  unfold perm in *.
  destruct (peq b1 b); try congruence. simpl in H0.
  rewrite PMap.gso in H0; eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p1); eauto.
  red; intros. specialize (H0 ofs0 H2).
  unfold perm in *.
  destruct (peq b1 b); try congruence. simpl in H0. rewrite PMap.gso in H0; eauto.
(* contents *)
  intros.
  apply mi_memval0; auto.
  unfold perm in *.
  destruct (peq b1 b); try congruence. simpl in H0. rewrite PMap.gso in H0; eauto.
Qed.

Lemma set_mapped_inj:
  forall f m1 m2 b1 b2 delta p m1',
  mem_inj f m1 m2 ->
  set_perm m1 b1 p = Some m1' ->
  forall (MAPPED_BLOCKS: forall b b' delta, f b = Some(b', delta) -> valid_block m2 b'),
  meminj_no_overlap f m1 ->
  forall (NO_OVERLAP_STRONG: forall b1 b2 b1' b2' delta1 delta2,
        b1 <> b2 ->
        f b1 = Some (b1', delta1) ->
        f b2 = Some (b2', delta2) ->
        b1' <> b2'),
  f b1 = Some(b2, delta) ->
  exists m2',
      set_perm m2 b2 p = Some m2'
   /\ mem_inj f m1' m2'.
Proof.
  intros f m1 m2 b1 b2 delta p m1' m1_m2 set1 mapped_blocks no_overlap no_overlap_strong f_b1.
  assert (X: { m2' | set_perm m2 b2 p = Some m2' }).
  { unfold set_perm in *.
    destruct (plt b1 (nextblock m1)); try discriminate.
    destruct (plt b2 (nextblock m2)); try now econstructor.
    exfalso. apply n. eapply mapped_blocks; eauto. }
  destruct X as [m2' set2]. exists m2'; split; auto.
  constructor.
  (* perm *)
  - intros b0 b3 delta0 ofs k p0 f_b0 PERM1'.
    destruct (eq_block b1 b0).
    + subst b0. rewrite f_b0 in f_b1; inv f_b1. rename f_b0 into f_b1.
      unfold set_perm in set2, set1. destruct (plt b1 (nextblock m1)), (plt b2 (nextblock m2)); inv set1; inv set2.
      unfold perm in *; simpl in *.
      rewrite PMap.gsspec in *. rewrite peq_true in *.
      destruct ((mem_access m1) # b1 ofs k) eqn:EQ1; try contradiction.
      assert (perm m1 b1 ofs k p3). { unfold perm; rewrite EQ1. constructor. }
      assert (perm m2 b2 (ofs + delta) k p3). { eapply mi_perm; eauto. }
      unfold perm in H0.
      destruct ((mem_access m2) # b2 (ofs + delta) k); auto.
    + eapply perm_set_2' in PERM1' as PERM1; eauto.
      eapply perm_set_2; eauto. eapply mi_perm; eauto.
  (* own *)
  - intros.
    pose proof (set_preserves_comp _ _ _ _ set1) as Haccess1.
    rewrite <- (Haccess1 b0).
    pose proof (set_preserves_comp _ _ _ _ set2) as Haccess2.
    rewrite <- (Haccess2 b3).
    eapply set_perm_perm in set1 as [p1 G]; eauto.
    erewrite mi_access with (ofs := ofs) (k := k); eauto.
  (* align *)
  - intros.
    eapply set_perm_range_perm in set1 as [p1 G]; eauto.
    eapply mi_align with (ofs := ofs); eauto.
  (* memval *)
  - intros.
    replace (m1'.(mem_contents)#b0) with (m1.(mem_contents)#b0).
    replace (m2'.(mem_contents)#b3) with (m2.(mem_contents)#b3).
    destruct (peq b0 b1); eauto. subst.
    { admit. }
    eapply mi_memval; eauto.
    eapply perm_set_2'; eauto.
    unfold set_perm in set2;
      destruct (plt b2 (nextblock m2)); inv set2; auto.
    unfold set_perm in set1;
      destruct (plt b1 (nextblock m1)); inv set1; auto.
Admitted.

Lemma set_outside_inj: forall f m1 m1' m2 b p,
  mem_inj f m1 m2 ->
  set_perm m1 b p = Some m1' ->
  f b = None ->
  mem_inj f m1' m2.
Proof.
  intros. inv H. constructor.
  (* perm *)
  - intros. eapply mi_perm0; eauto.
    assert (b1 <> b) by congruence.
    eapply perm_set_2'; eauto.
  (* own *)
  - intros.
    assert (b1 <> b) by congruence.
    erewrite <- mi_access0; eauto.
    erewrite <- set_preserves_comp; eauto.
    eapply perm_set_2'; eauto.
  (* align *)
  - intros. eapply mi_align0; eauto.
    assert (b1 <> b) by congruence.
    intros ??.
    eapply perm_set_2'; eauto.
  (* contents *)
  - intros.
    replace (m1'.(mem_contents)#b1) with (m1.(mem_contents)#b1).
    apply mi_memval0; auto.
    assert (b1 <> b) by congruence.
    eapply perm_set_2'; eauto.
    unfold set_perm in H0;
      destruct plt;
      inv H0; auto.
Qed.

Lemma set_outside_inj':
  forall f m1 m2 b p m2',
  mem_inj f m1 m2 ->
  set_perm m2 b p = Some m2' ->
  (forall b0 delta, not (f b0 = Some (b, delta))) ->
  mem_inj f m1 m2'.
Proof.
  intros. inv H. constructor.
  (* perm *)
  - intros. exploit mi_perm0; eauto.
    intros.
    eapply perm_set_2; eauto.
    intros ?. subst. exploit H1; eauto.
  (* own *)
  - intros.
    erewrite mi_access0; eauto.
    erewrite set_preserves_comp; eauto.
  (* align *)
  - intros. eapply mi_align0; eauto.
  (* contents *)
  - intros.
    replace (m2'.(mem_contents)#b2) with (m2.(mem_contents)#b2).
    apply mi_memval0; auto.
    (* eapply perm_set_2; eauto. *)
    unfold set_perm in H0;
      destruct plt;
      inv H0; auto.
Qed.


(** * Memory extensions *)

(**  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by increasing the sizes of the memory blocks of [m1] (decreasing
  the low bounds, increasing the high bounds), and replacing some of
  the [Vundef] values stored in [m1] by more defined values stored
  in [m2] at the same locations. *)

Record extends' (m1 m2: mem) : Prop :=
  mk_extends {
    mext_next: nextblock m1 = nextblock m2;
    mext_inj:  mem_inj inject_id m1 m2;
    mext_perm_inv: forall b ofs k p,
      perm m2 b ofs k p ->
      perm m1 b ofs k p \/ ~perm m1 b ofs Max Nonempty
  }.

Definition extends := extends'.

Theorem extends_refl:
  forall m, extends m m.
Proof.
  intros. constructor. auto. auto. constructor.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by lia. auto.
  intros. unfold inject_id in H; inv H. reflexivity.
  intros. unfold inject_id in H; inv H. apply Z.divide_0_r.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by lia.
  apply memval_lessdef_refl.
  tauto.
Qed.

Theorem load_extends:
  forall chunk m1 m2 b ofs cp v1,
  extends m1 m2 ->
  load chunk m1 b ofs cp = Some v1 ->
  exists v2, load chunk m2 b ofs cp = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. inv H. exploit load_inj; eauto. unfold inject_id; reflexivity.
  intros [v2 [A B]]. exists v2; split.
  replace (ofs + 0) with ofs in A by lia. auto.
  rewrite val_inject_id in B. auto.
Qed.

Theorem loadv_extends:
  forall chunk m1 m2 addr1 cp addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 cp = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 cp = Some v2 /\ Val.lessdef v1 v2.
Proof.
  unfold loadv; intros. inv H1.
  destruct addr2; try congruence. eapply load_extends; eauto.
  congruence.
Qed.

Theorem loadbytes_extends:
  forall m1 m2 b ofs len cp bytes1,
  extends m1 m2 ->
  loadbytes m1 b ofs len cp = Some bytes1 ->
  exists bytes2, loadbytes m2 b ofs len cp = Some bytes2
              /\ list_forall2 memval_lessdef bytes1 bytes2.
Proof.
  intros. inv H.
  replace ofs with (ofs + 0) by lia. eapply loadbytes_inj; eauto.
Qed.

Theorem store_within_extends:
  forall chunk m1 m2 b ofs v1 cp m1' v2,
  extends m1 m2 ->
  store chunk m1 b ofs v1 cp = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 b ofs v2 cp = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto.
    unfold inject_id; red; intros. inv H3; inv H4. auto.
    unfold inject_id; reflexivity.
    rewrite val_inject_id. eauto.
  intros [m2' [A B]].
  exists m2'; split.
  replace (ofs + 0) with ofs in A by lia. auto.
  constructor; auto.
  rewrite (nextblock_store _ _ _ _ _ _ _ H0).
  rewrite (nextblock_store _ _ _ _ _ _ _ A).
  auto.
  intros. exploit mext_perm_inv0; intuition eauto using perm_store_1, perm_store_2.
Qed.

Theorem store_outside_extends:
  forall chunk m1 m2 b ofs v cp m2',
  extends m1 m2 ->
  store chunk m2 b ofs v cp = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + size_chunk chunk -> False) ->
  extends m1 m2'.
Proof.
  intros. inversion H. constructor.
  rewrite (nextblock_store _ _ _ _ _ _ _ H0). auto.
  eapply store_outside_inj; eauto.
  unfold inject_id; intros. inv H2. eapply H1; eauto. lia.
  intros. eauto using perm_store_2.
Qed.

Theorem storev_extends:
  forall chunk m1 m2 addr1 v1 cp m1' addr2 v2,
  extends m1 m2 ->
  storev chunk m1 addr1 v1 cp = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 cp = Some m2'
  /\ extends m1' m2'.
Proof.
  unfold storev; intros. inv H1.
  destruct addr2; try congruence. eapply store_within_extends; eauto.
  congruence.
Qed.

Theorem storebytes_within_extends:
  forall m1 m2 b ofs bytes1 cp m1' bytes2,
  extends m1 m2 ->
  storebytes m1 b ofs bytes1 cp = Some m1' ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2',
     storebytes m2 b ofs bytes2 cp = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  exploit storebytes_mapped_inj; eauto.
    unfold inject_id; red; intros. inv H3; inv H4. auto.
    unfold inject_id; reflexivity.
  intros [m2' [A B]].
  exists m2'; split.
  replace (ofs + 0) with ofs in A by lia. auto.
  constructor; auto.
  rewrite (nextblock_storebytes _ _ _ _ _ _ H0).
  rewrite (nextblock_storebytes _ _ _ _ _ _ A).
  auto.
  intros. exploit mext_perm_inv0; intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

Theorem storebytes_outside_extends:
  forall m1 m2 b ofs bytes2 cp m2',
  extends m1 m2 ->
  storebytes m2 b ofs bytes2 cp = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + Z.of_nat (length bytes2) -> False) ->
  extends m1 m2'.
Proof.
  intros. inversion H. constructor.
  rewrite (nextblock_storebytes _ _ _ _ _ _ H0). auto.
  eapply storebytes_outside_inj; eauto.
  unfold inject_id; intros. inv H2. eapply H1; eauto. lia.
  intros. eauto using perm_storebytes_2.
Qed.

Theorem alloc_extends:
  forall m1 m2 c lo1 hi1 b m1' lo2 hi2,
  extends m1 m2 ->
  alloc m1 c lo1 hi1 = (m1', b) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 c lo2 hi2 = (m2', b)
  /\ extends m1' m2'.
Proof.
  intros. inv H.
  case_eq (alloc m2 c lo2 hi2); intros m2' b' ALLOC.
  assert (b' = b).
    rewrite (alloc_result _ _ _ _ _ _ H0).
    rewrite (alloc_result _ _ _ _ _ _ ALLOC).
    auto.
  subst b'.
  exists m2'; split; auto.
  constructor.
  rewrite (nextblock_alloc _ _ _ _ _ _ H0).
  rewrite (nextblock_alloc _ _ _ _ _ _ ALLOC).
  congruence.
  eapply alloc_left_mapped_inj with (m1 := m1) (m2 := m2') (b2 := b) (delta := 0); eauto.
  eapply alloc_right_inj; eauto.
  eauto with mem.
  red. intros. apply Z.divide_0_r.
  intros.
  eapply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto.
  lia.
  simpl. apply owned_new_block in ALLOC; subst; auto with comps.
  intros. eapply perm_alloc_inv in H; eauto.
  generalize (perm_alloc_inv _ _ _ _ _ _ H0 b0 ofs Max Nonempty); intros PERM.
  destruct (eq_block b0 b).
  subst b0.
  assert (EITHER: lo1 <= ofs < hi1 \/ ~(lo1 <= ofs < hi1)) by lia.
  destruct EITHER.
  left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto.
  right; tauto.
  exploit mext_perm_inv0; intuition eauto using perm_alloc_1, perm_alloc_4.
Qed.

Theorem free_left_extends:
  forall m1 m2 b lo hi cp m1',
  extends m1 m2 ->
  free m1 b lo hi cp = Some m1' ->
  extends m1' m2.
Proof.
  intros. inv H. constructor.
  rewrite (nextblock_free _ _ _ _ _ _ H0). auto.
  eapply free_left_inj; eauto.
  intros. exploit mext_perm_inv0; eauto. intros [A|A].
  eapply perm_free_inv in A; eauto. destruct A as [[A B]|A]; auto.
  subst b0. right; eapply perm_free_2; eauto.
  intuition eauto using perm_free_3.
Qed.

Theorem free_right_extends:
  forall m1 m2 b lo hi cp m2',
  extends m1 m2 ->
  free m2 b lo hi cp = Some m2' ->
  (forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  extends m1 m2'.
Proof.
  intros. inv H. constructor.
  rewrite (nextblock_free _ _ _ _ _ _ H0). auto.
  eapply free_right_inj; eauto.
  unfold inject_id; intros. inv H. eapply H1; eauto. lia.
  intros. eauto using perm_free_3.
Qed.

Theorem free_parallel_extends:
  forall m1 m2 b lo hi cp m1',
  extends m1 m2 ->
  free m1 b lo hi cp = Some m1' ->
  exists m2',
     free m2 b lo hi cp = Some m2'
  /\ extends m1' m2'.
Proof.
  intros.
  assert ({ m2': mem | free m2 b lo hi cp = Some m2' }).
    apply range_perm_free. red; intros.
    replace ofs with (ofs + 0) by lia.
    eapply perm_inj with (b1 := b); inv H; eauto.
    eapply free_range_perm; eauto.
    (* own *)
    { apply free_range_perm in H0 as G.
      unfold free in *. destruct (Z_le_dec); try auto.
      left.
      destruct can_access_block_dec; eauto.
    (* unfold inject_id in mext_inj0; inv mext_inj0. *)
    eapply mi_own; inv H; eauto. reflexivity.
    eapply G with (ofs := lo). lia.
      rewrite andb_comm in *; simpl in *; congruence. }
  destruct X as [m2' FREE]. exists m2'; split; auto.
  constructor.
  rewrite (nextblock_free _ _ _ _ _ _ H0).
  rewrite (nextblock_free _ _ _ _ _ _ FREE).
  inv H; auto.
  eapply free_right_inj with (m1 := m1'); eauto.
  eapply free_left_inj; eauto.
  inv H; auto.
  unfold inject_id; intros. inv H1.
  eapply perm_free_2. eexact H0. instantiate (1 := ofs); lia. eauto.
  intros. exploit mext_perm_inv; eauto using perm_free_3. intros [A|A].
  eapply perm_free_inv in A; eauto. destruct A as [[A B]|A]; auto.
  subst b0. right; eapply perm_free_2; eauto.
  right; intuition eauto using perm_free_3.
Qed.

Theorem valid_block_extends:
  forall m1 m2 b,
  extends m1 m2 ->
  (valid_block m1 b <-> valid_block m2 b).
Proof.
  intros. inv H. unfold valid_block. rewrite mext_next0. tauto.
Qed.

Theorem perm_extends:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m1 b ofs k p -> perm m2 b ofs k p.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by lia.
  eapply perm_inj; eauto.
Qed.

Theorem perm_extends_inv:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m2 b ofs k p -> perm m1 b ofs k p \/ ~perm m1 b ofs Max Nonempty.
Proof.
  intros. inv H; eauto.
Qed.

Theorem valid_access_extends:
  forall m1 m2 chunk b ofs p cp,
  extends m1 m2 -> valid_access m1 chunk b ofs p cp -> valid_access m2 chunk b ofs p cp.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by lia.
  eapply valid_access_inj; eauto. auto.
Qed.

Theorem valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 -> valid_pointer m1 b ofs = true -> valid_pointer m2 b ofs = true.
Proof.
  intros m1 m2 b ofs Hextend Hvalid.
  eapply valid_pointer_valid_access in Hvalid; eauto.
  destruct (valid_access_extends _ _ _ _ _ _ _ Hextend Hvalid) as [Hperm [Hown2 Halign]].
  rewrite valid_pointer_valid_access; eauto .
  repeat (split; simpl); eauto with comps. eapply flowsto_refl.
Qed.

Theorem weak_valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 ->
  weak_valid_pointer m1 b ofs = true -> weak_valid_pointer m2 b ofs = true.
Proof.
  intros until 1. unfold weak_valid_pointer. rewrite !orb_true_iff.
  intros []; eauto using valid_pointer_extends.
Qed.

(** * Memory injections *)

(** A memory state [m1] injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address;
- unallocated blocks in [m1] must be mapped to [top] by [f];
- if [f b = Some(b', delta)], [b'] must be valid in [m2];
- distinct blocks in [m1] are mapped to non-overlapping sub-blocks in [m2];
- the sizes of [m2]'s blocks are representable with unsigned machine integers;
- pointers that could be represented using unsigned machine integers remain
  representable after the injection.
*)

Record inject' (f: meminj) (m1 m2: mem) : Prop :=
  mk_inject {
    mi_inj:
      mem_inj f m1 m2;
    mi_freeblocks:
      forall b, ~(valid_block m1 b) -> f b = None;
    mi_mappedblocks:
      forall b b' delta, f b = Some(b', delta) -> valid_block m2 b';
    mi_no_overlap:
      meminj_no_overlap f m1;
    mi_representable:
      forall b b' delta ofs,
      f b = Some(b', delta) ->
      perm m1 b (Ptrofs.unsigned ofs) Max Nonempty \/ perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty ->
      delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned;
    mi_perm_inv:
      forall b1 ofs b2 delta k p,
      f b1 = Some(b2, delta) ->
      perm m2 b2 (ofs + delta) k p ->
      perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty
  }.
Definition inject := inject'.

Local Hint Resolve mi_mappedblocks: mem.

(** Preservation of access validity and pointer validity *)

Theorem valid_block_inject_1:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m1 b1.
Proof.
  intros. inv H. destruct (plt b1 (nextblock m1)). auto.
  assert (f b1 = None). eapply mi_freeblocks; eauto. congruence.
Qed.

Theorem valid_block_inject_2:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m2 b2.
Proof.
  intros. eapply mi_mappedblocks; eauto.
Qed.

Local Hint Resolve valid_block_inject_1 valid_block_inject_2: mem.

Theorem perm_inject:
  forall f m1 m2 b1 b2 delta ofs k p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  perm m1 b1 ofs k p -> perm m2 b2 (ofs + delta) k p.
Proof.
  intros. inv H0. eapply perm_inj; eauto.
Qed.

Theorem perm_inject_inv:
  forall f m1 m2 b1 ofs b2 delta k p,
  inject f m1 m2 ->
  f b1 = Some(b2, delta) ->
  perm m2 b2 (ofs + delta) k p ->
  perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty.
Proof.
  intros. eapply mi_perm_inv; eauto.
Qed.

Theorem range_perm_inject:
  forall f m1 m2 b1 b2 delta lo hi k p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  range_perm m1 b1 lo hi k p -> range_perm m2 b2 (lo + delta) (hi + delta) k p.
Proof.
  intros. inv H0. eapply range_perm_inj; eauto.
Qed.

Theorem valid_access_inject:
  forall f m1 m2 chunk b1 ofs b2 delta p cp,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_access m1 chunk b1 ofs p cp ->
  valid_access m2 chunk b2 (ofs + delta) p cp.
Proof.
  intros. eapply valid_access_inj; eauto. apply mi_inj; auto.
Qed.

Theorem valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros.
  eapply valid_pointer_valid_access in H1; eauto using flowsto_refl.
  apply proj1 in H1 as G.
  eapply valid_access_inject in H1; eauto.
  eapply valid_pointer_valid_access in H1; eauto.
  inv H0. inv mi_inj0. erewrite mi_access0; eauto.
  now apply flowsto_refl.
  eapply G with (ofs := ofs). simpl. lia.
Qed.

Theorem weak_valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  weak_valid_pointer m1 b1 ofs = true ->
  weak_valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros until 2. unfold weak_valid_pointer. rewrite !orb_true_iff.
  replace (ofs + delta - 1) with ((ofs - 1) + delta) by lia.
  intros []; eauto using valid_pointer_inject.
Qed.

(** The following lemmas establish the absence of machine integer overflow
  during address computations. *)

Lemma address_inject:
  forall f m1 m2 b1 ofs1 b2 delta p,
  inject f m1 m2 ->
  perm m1 b1 (Ptrofs.unsigned ofs1) Cur p ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
Proof.
  intros.
  assert (perm m1 b1 (Ptrofs.unsigned ofs1) Max Nonempty) by eauto with mem.
  exploit mi_representable; eauto. intros [A B].
  assert (0 <= delta <= Ptrofs.max_unsigned).
    generalize (Ptrofs.unsigned_range ofs1). lia.
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; lia.
Qed.

Lemma address_inject':
  forall f m1 m2 chunk b1 ofs1 cp b2 delta,
  inject f m1 m2 ->
  valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Nonempty cp ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
Proof.
  intros. destruct H0. eapply address_inject; eauto.
  apply H0. generalize (size_chunk_pos chunk). lia.
Qed.

Theorem weak_valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' delta,
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  intros. rewrite weak_valid_pointer_spec in H0.
  rewrite ! valid_pointer_nonempty_perm in H0.
  exploit mi_representable; eauto. destruct H0; eauto with mem.
  intros [A B].
  pose proof (Ptrofs.unsigned_range ofs).
  rewrite Ptrofs.unsigned_repr; lia.
Qed.

Theorem valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' delta,
  inject f m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  eauto using weak_valid_pointer_inject_no_overflow, valid_pointer_implies.
Qed.

Theorem valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
Proof.
  intros. inv H1.
  (* pose proof valid_pointer_can_access_block _ _ _ H0 as [cp Hown]. *)
  erewrite address_inject'; eauto.
  eapply valid_pointer_inject; eauto.
  rewrite valid_pointer_valid_access in H0. eauto.
  now eapply flowsto_refl.
Qed.

Theorem weak_valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
Proof.
  intros. inv H1.
  exploit weak_valid_pointer_inject; eauto. intros W.
  rewrite weak_valid_pointer_spec in H0.
  rewrite ! valid_pointer_nonempty_perm in H0.
  exploit mi_representable; eauto. destruct H0; eauto with mem.
  intros [A B].
  pose proof (Ptrofs.unsigned_range ofs).
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; auto; lia.
Qed.

Theorem inject_no_overlap:
  forall f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject f m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Max Nonempty ->
  perm m1 b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.
Proof.
  intros. inv H. eapply mi_no_overlap0; eauto.
Qed.

Theorem different_pointers_inject:
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
Proof.
  intros.
  (* destruct (valid_pointer_can_access_block _ _ _ H1) as [cp1 Hown1]. *)
  (* destruct (valid_pointer_can_access_block _ _ _ H2) as [cp2 Hown2]. *)
  rewrite valid_pointer_valid_access in H1; eauto using flowsto_refl.
  rewrite valid_pointer_valid_access in H2; eauto using flowsto_refl.
  rewrite (address_inject' _ _ _ _ _ _ _ _ _ H H1 H3).
  rewrite (address_inject' _ _ _ _ _ _ _ _ _ H H2 H4).
  inv H1. simpl in H5. inv H2. simpl in H1.
  eapply mi_no_overlap; eauto.
  apply perm_cur_max. apply (H5 (Ptrofs.unsigned ofs1)). lia.
  apply perm_cur_max. apply (H1 (Ptrofs.unsigned ofs2)). lia.
Qed.

Theorem disjoint_or_equal_inject:
  forall f m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
  inject f m m' ->
  f b1 = Some(b1', delta1) ->
  f b2 = Some(b2', delta2) ->
  range_perm m b1 ofs1 (ofs1 + sz) Max Nonempty ->
  range_perm m b2 ofs2 (ofs2 + sz) Max Nonempty ->
  sz > 0 ->
  b1 <> b2 \/ ofs1 = ofs2 \/ ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1 ->
  b1' <> b2' \/ ofs1 + delta1 = ofs2 + delta2
             \/ ofs1 + delta1 + sz <= ofs2 + delta2
             \/ ofs2 + delta2 + sz <= ofs1 + delta1.
Proof.
  intros.
  destruct (eq_block b1 b2).
  assert (b1' = b2') by congruence. assert (delta1 = delta2) by congruence. subst.
  destruct H5. congruence. right. destruct H5. left; congruence. right. lia.
  destruct (eq_block b1' b2'); auto. subst. right. right.
  set (i1 := (ofs1 + delta1, ofs1 + delta1 + sz)).
  set (i2 := (ofs2 + delta2, ofs2 + delta2 + sz)).
  change (snd i1 <= fst i2 \/ snd i2 <= fst i1).
  apply Intv.range_disjoint'; simpl; try lia.
  unfold Intv.disjoint, Intv.In; simpl; intros. red; intros.
  exploit mi_no_overlap; eauto.
  instantiate (1 := x - delta1). apply H2. lia.
  instantiate (1 := x - delta2). apply H3. lia.
  intuition.
Qed.

Theorem aligned_area_inject:
  forall f m m' b ofs al sz b' delta cp,
  inject f m m' ->
  al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz > 0 ->
  (al | sz) ->
  range_perm m b ofs (ofs + sz) Cur Nonempty ->
  (al | ofs) ->
  f b = Some(b', delta) ->
  forall OWN : can_access_block m b cp,
  (al | ofs + delta).
Proof.
  intros.
  assert (P: al > 0) by lia.
  assert (Q: Z.abs al <= Z.abs sz). apply Zdivide_bounds; auto. lia.
  rewrite Z.abs_eq in Q; try lia. rewrite Z.abs_eq in Q; try lia.
  assert (R: exists chunk, al = align_chunk chunk /\ al = size_chunk chunk).
    destruct H0. subst; exists Mint8unsigned; auto.
    destruct H0. subst; exists Mint16unsigned; auto.
    destruct H0. subst; exists Mint32; auto.
    subst; exists Mint64; auto.
  destruct R as [chunk [A B]].
  assert (valid_access m chunk b ofs Nonempty cp).
    split. red; intros; apply H3. lia.
    split. assumption. congruence.
  exploit valid_access_inject; eauto. intros [C [D E]].
  congruence.
Qed.

(** Preservation of loads *)

Theorem load_inject:
  forall f m1 m2 chunk b1 ofs cp b2 delta v1,
  inject f m1 m2 ->
  load chunk m1 b1 ofs cp = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) cp = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H. eapply load_inj; eauto.
Qed.

Theorem loadv_inject:
  forall f m1 m2 chunk a1 cp a2 v1,
  inject f m1 m2 ->
  loadv chunk m1 a1 cp = Some v1 ->
  Val.inject f a1 a2 ->
  exists v2, loadv chunk m2 a2 cp = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  exploit load_inject; eauto. intros [v2 [LOAD INJ]].
  exists v2; split; auto. unfold loadv.
  replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))
     with (Ptrofs.unsigned ofs1 + delta).
  auto. symmetry. eapply address_inject'; eauto with mem.
Qed.

Theorem loadbytes_inject:
  forall f m1 m2 b1 ofs len cp b2 delta bytes1,
  inject f m1 m2 ->
  loadbytes m1 b1 ofs len cp = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len cp = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2.
Proof.
  intros. inv H. eapply loadbytes_inj; eauto.
Qed.

(** Preservation of stores *)

Theorem store_mapped_inject:
  forall f chunk m1 b1 ofs v1 cp n1 m2 b2 delta v2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 cp = Some n1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 cp = Some n2
    /\ inject f n1 n2.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto. intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor.
(* inj *)
  auto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. eapply mi_representable; try eassumption.
  destruct H4; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_store_2.
  intuition eauto using perm_store_1, perm_store_2.
Qed.

Theorem store_unmapped_inject:
  forall f chunk m1 b1 ofs v1 cp n1 m2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 cp = Some n1 ->
  f b1 = None ->
  inject f n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* inj *)
  eapply store_unmapped_inj; eauto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. eapply mi_representable; try eassumption.
  destruct H3; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_store_2.
  intuition eauto using perm_store_1, perm_store_2.
Qed.

Theorem store_outside_inject:
  forall f m1 m2 chunk b ofs v cp m2',
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v cp = Some m2' ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply store_outside_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  eauto with mem.
(* perm inv *)
  intros. eauto using perm_store_2.
Qed.

Theorem storev_mapped_inject:
  forall f chunk m1 a1 v1 cp n1 m2 a2 v2,
  inject f m1 m2 ->
  storev chunk m1 a1 v1 cp = Some n1 ->
  Val.inject f a1 a2 ->
  Val.inject f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 cp = Some n2 /\ inject f n1 n2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  unfold storev.
  replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))
    with (Ptrofs.unsigned ofs1 + delta).
  eapply store_mapped_inject; eauto.
  symmetry. eapply address_inject'; eauto with mem.
Qed.

Theorem storebytes_mapped_inject:
  forall f m1 b1 ofs bytes1 cp n1 m2 b2 delta bytes2,
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 cp = Some n1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 cp = Some n2
    /\ inject f n1 n2.
Proof.
  intros. inversion H.
  exploit storebytes_mapped_inj; eauto. intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor.
(* inj *)
  auto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H3; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. eapply mi_representable0; eauto.
  destruct H4; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_storebytes_2.
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

Theorem storebytes_unmapped_inject:
  forall f m1 b1 ofs bytes1 cp n1 m2,
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 cp = Some n1 ->
  f b1 = None ->
  inject f n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* inj *)
  eapply storebytes_unmapped_inj; eauto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H2; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. eapply mi_representable0; eauto.
  destruct H3; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto.
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

Theorem storebytes_outside_inject:
  forall f m1 m2 b ofs bytes2 cp m2',
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z.of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 cp = Some m2' ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply storebytes_outside_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eapply mi_perm_inv0; eauto using perm_storebytes_2.
Qed.

Theorem storebytes_empty_inject:
  forall f m1 b1 ofs1 cp1 m1' m2 b2 ofs2 cp2 m2',
  inject f m1 m2 ->
  storebytes m1 b1 ofs1 nil cp1 = Some m1' ->
  storebytes m2 b2 ofs2 nil cp2 = Some m2' ->
  inject f m1' m2'.
Proof.
  intros. inversion H. constructor; intros.
(* inj *)
  eapply storebytes_empty_inj; eauto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H2; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. eapply mi_representable0; eauto.
  destruct H3; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_storebytes_2.
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

(* Preservation of allocations *)

Theorem alloc_right_inject:
  forall f m1 m2 c lo hi b2 m2',
  inject f m1 m2 ->
  alloc m2 c lo hi = (m2', b2) ->
  inject f m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* inj *)
  eapply alloc_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eapply perm_alloc_inv in H2; eauto. destruct (eq_block b0 b2).
  subst b0. eelim fresh_block_alloc; eauto.
  eapply mi_perm_inv0; eauto.
Qed.

Theorem alloc_left_unmapped_inject:
  forall f m1 m2 c lo hi m1' b1,
  inject f m1 m2 ->
  alloc m1 c lo hi = (m1', b1) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros. inversion H.
  set (f' := fun b => if eq_block b b1 then None else f b).
  assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  assert (mem_inj f' m1 m2).
    inversion mi_inj0; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence.
    unfold f'; intros. destruct (eq_block b0 b1). congruence.
    eapply mi_align0; eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence.
    apply memval_inject_incr with f; auto.
  exists f'; split. constructor.
(* inj *)
  eapply alloc_left_unmapped_inj; eauto. unfold f'; apply dec_eq_true.
(* freeblocks *)
  intros. unfold f'. destruct (eq_block b b1). auto.
  apply mi_freeblocks0. red; intro; elim H3. eauto with mem.
(* mappedblocks *)
  unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
(* no overlap *)
  unfold f'; red; intros.
  destruct (eq_block b0 b1); destruct (eq_block b2 b1); try congruence.
  eapply mi_no_overlap0. eexact H3. eauto. eauto.
  exploit perm_alloc_inv. eauto. eexact H6. rewrite dec_eq_false; auto.
  exploit perm_alloc_inv. eauto. eexact H7. rewrite dec_eq_false; auto.
(* representable *)
  unfold f'; intros.
  destruct (eq_block b b1); try discriminate.
  eapply mi_representable0; try eassumption.
  destruct H4; eauto using perm_alloc_4.
(* perm inv *)
  intros. unfold f' in H3; destruct (eq_block b0 b1); try discriminate.
  exploit mi_perm_inv0; eauto.
  intuition eauto using perm_alloc_1, perm_alloc_4.
(* incr *)
  split. auto.
(* image *)
  split. unfold f'; apply dec_eq_true.
(* incr *)
  intros; unfold f'; apply dec_eq_false; auto.
Qed.

Theorem alloc_left_mapped_inject:
  forall f m1 m2 c lo hi m1' b1 b2 delta,
  inject f m1 m2 ->
  alloc m1 c lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  forall OWN : block_compartment m2 b2 = c,
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
Proof.
  intros. inversion H.
  set (f' := fun b => if eq_block b b1 then Some(b2, delta) else f b).
  assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  assert (mem_inj f' m1 m2).
    inversion mi_inj0; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ _ H0). eauto with mem.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inv H8.
      eapply perm_valid_block in H9.
      erewrite alloc_result in H9; eauto.
      unfold valid_block in H9; simpl in H9; now exploit Plt_strict; eauto.
      erewrite mi_access0; eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ _ H0).
      eapply perm_valid_block with (ofs := ofs). apply H9. generalize (size_chunk_pos chunk); lia.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ _ H0). eauto with mem.
      apply memval_inject_incr with f; auto.
  exists f'. split. constructor.
(* inj *)
  eapply alloc_left_mapped_inj; eauto. unfold f'; apply dec_eq_true.
(* freeblocks *)
  unfold f'; intros. destruct (eq_block b b1). subst b.
  elim H9. eauto with mem.
  eauto with mem.
(* mappedblocks *)
  unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
(* overlap *)
  unfold f'; red; intros.
  exploit perm_alloc_inv. eauto. eexact H12. intros P1.
  exploit perm_alloc_inv. eauto. eexact H13. intros P2.
  destruct (eq_block b0 b1); destruct (eq_block b3 b1).
  congruence.
  inversion H10; subst b0 b1' delta1.
    destruct (eq_block b2 b2'); auto. subst b2'. right; red; intros.
    eapply H6; eauto. lia.
  inversion H11; subst b3 b2' delta2.
    destruct (eq_block b1' b2); auto. subst b1'. right; red; intros.
    eapply H6; eauto. lia.
  eauto.
(* representable *)
  unfold f'; intros.
  destruct (eq_block b b1).
   subst. injection H9; intros; subst b' delta0. destruct H10.
    exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
    exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
    generalize (Ptrofs.unsigned_range_2 ofs). lia.
   exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
   exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
   generalize (Ptrofs.unsigned_range_2 ofs). lia.
  eapply mi_representable0; try eassumption.
  destruct H10; eauto using perm_alloc_4.
(* perm inv *)
  intros. unfold f' in H9; destruct (eq_block b0 b1).
  inversion H9; clear H9; subst b0 b3 delta0.
  assert (EITHER: lo <= ofs < hi \/ ~(lo <= ofs < hi)) by lia.
  destruct EITHER.
  left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto.
  right; intros A. eapply perm_alloc_inv in A; eauto. rewrite dec_eq_true in A. tauto.
  exploit mi_perm_inv0; eauto. intuition eauto using perm_alloc_1, perm_alloc_4.
(* incr *)
  split. auto.
(* image of b1 *)
  split. unfold f'; apply dec_eq_true.
(* image of others *)
  intros. unfold f'; apply dec_eq_false; auto.
Qed.

Theorem alloc_parallel_inject:
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
Proof.
  intros.
  case_eq (alloc m2 c lo2 hi2). intros m2' b2 ALLOC.
  exploit alloc_left_mapped_inject.
  eapply alloc_right_inject; eauto.
  eauto.
  instantiate (1 := b2). eauto with mem.
  eapply owned_new_block in ALLOC; subst; eauto with comps.
  instantiate (1 := 0). unfold Ptrofs.max_unsigned. generalize Ptrofs.modulus_pos; lia.
  auto.
  intros. apply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto. lia.
  red; intros. apply Z.divide_0_r.
  intros. apply (valid_not_valid_diff m2 b2 b2); eauto with mem.
  intros [f' [A [B [C D]]]].
  exists f'; exists m2'; exists b2; auto.
Qed.

(** Preservation of [free] operations *)

Lemma free_left_inject:
  forall f m1 m2 b lo hi cp m1',
  inject f m1 m2 ->
  free m1 b lo hi cp = Some m1' ->
  inject f m1' m2.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply free_left_inj; eauto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  auto.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. eapply mi_representable0; try eassumption.
  destruct H2; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto. intuition eauto using perm_free_3.
  eapply perm_free_inv in H4; eauto. destruct H4 as [[A B] | A]; auto.
  subst b1. right; eapply perm_free_2; eauto.
Qed.

Lemma free_list_left_inject:
  forall f m2 l cp m1 m1',
  inject f m1 m2 ->
  free_list m1 l cp = Some m1' ->
  inject f m1' m2.
Proof.
  induction l; simpl; intros.
  inv H0. auto.
  destruct a as [[b lo] hi].
  destruct (free m1 b lo hi) as [m11|] eqn:E; try discriminate.
  apply IHl with cp m11; auto. eapply free_left_inject; eauto.
Qed.

Lemma free_right_inject:
  forall f m1 m2 b lo hi cp m2',
  inject f m1 m2 ->
  free m2 b lo hi cp = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p ->
    lo <= ofs + delta < hi -> False) ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply free_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eauto using perm_free_3.
Qed.

Lemma perm_free_list:
  forall l m cp m' b ofs k p,
  free_list m l cp = Some m' ->
  perm m' b ofs k p ->
  perm m b ofs k p /\
  (forall lo hi, In (b, lo, hi) l -> lo <= ofs < hi -> False).
Proof.
  induction l; simpl; intros.
  inv H. auto.
  destruct a as [[b1 lo1] hi1].
  destruct (free m b1 lo1 hi1) as [m1|] eqn:E; try discriminate.
  exploit IHl; eauto. intros [A B].
  split. eauto with mem.
  intros. destruct H1. inv H1.
  elim (perm_free_2 _ _ _ _ _ _ E ofs k p). auto. auto.
  eauto.
Qed.

Theorem free_inject:
  forall f m1 l cp1 m1' m2 b lo hi cp2 m2',
  inject f m1 m2 ->
  free_list m1 l cp1 = Some m1' ->
  free m2 b lo hi cp2 = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) ->
    perm m1 b1 ofs k p -> lo <= ofs + delta < hi ->
    exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
  inject f m1' m2'.
Proof.
  intros.
  eapply free_right_inject; eauto.
  eapply free_list_left_inject; eauto.
  intros. exploit perm_free_list; eauto. intros [A B].
  exploit H2; eauto. intros [lo1 [hi1 [C D]]]. eauto.
Qed.

Theorem free_parallel_inject:
  forall f m1 m2 b lo hi cp m1' b' delta,
  inject f m1 m2 ->
  free m1 b lo hi cp = Some m1' ->
  f b = Some(b', delta) ->
  exists m2',
     free m2 b' (lo + delta) (hi + delta) cp = Some m2'
  /\ inject f m1' m2'.
Proof.
  intros.
  destruct (range_perm_free m2 b' (lo + delta) (hi + delta) cp) as [m2' FREE].
  eapply range_perm_inject; eauto. eapply free_range_perm; eauto.
  { destruct (Z_le_dec hi lo) eqn:EQ.
    - unfold free in *; rewrite EQ in *. right. lia.
    - left.
      exploit free_can_access_block_1; eauto. intros [? | ?]; try lia.
      unfold free in H0. rewrite EQ in *.
      destruct range_perm_dec; simpl in *; try congruence.
      inv H; eapply mi_own; eauto.
      eapply r with (ofs := lo). lia. }
  exists m2'; split; auto.
  eapply free_inject with (m1 := m1) (l := (b,lo,hi)::nil); eauto.
  simpl; rewrite H0; auto.
  intros. destruct (eq_block b1 b).
  subst b1. rewrite H1 in H2; inv H2.
  exists lo, hi; split; auto with coqlib. lia.
  exploit mi_no_overlap. eexact H. eexact n. eauto. eauto.
  eapply perm_max. eapply perm_implies. eauto. auto with mem.
  instantiate (1 := ofs + delta0 - delta).
  apply perm_cur_max. apply perm_implies with Freeable; auto with mem.
  eapply free_range_perm; eauto. lia.
  intros [A|A]. congruence. lia.
Qed.

Lemma drop_outside_inject: forall f m1 m2 b lo hi p cp m2',
  inject f m1 m2 ->
  drop_perm m2 b lo hi p cp = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  inject f m1 m2'.
Proof.
  intros. destruct H. constructor; eauto.
  eapply drop_outside_inj; eauto.
  intros. unfold valid_block in *. erewrite nextblock_drop; eauto.
  intros. eapply mi_perm_inv0; eauto using perm_drop_4.
Qed.

Theorem set_parallel_inject:
  forall f m1 m2 b p m1' b' delta,
  inject f m1 m2 ->
  set_perm m1 b p = Some m1' ->
  (forall (b1 b2 b1' b2' : block) (delta1 delta2 : Z),
      b1 <> b2 -> f b1 = Some (b1', delta1) -> f b2 = Some (b2', delta2) -> b1' <> b2') ->
  f b = Some(b', delta) ->
  exists m2',
     set_perm m2 b' p = Some m2'
  /\ inject f m1' m2'.
Proof.
  intros. destruct H.
  exploit set_mapped_inj; eauto.
  intros [m2' [? ?]].
  eexists; split; eauto.
  constructor; eauto.
  - intros. eapply mi_freeblocks0. intros ?. eapply H4. eapply set_perm_valid_block_1; eauto.
  - intros. exploit set_perm_valid_block_1; eauto.
  - intros ?????????????. eapply mi_no_overlap0; eauto.
    eapply set_perm_perm in H7 as [? ?]; eauto. eapply Mem.perm_implies; eauto; constructor.
    eapply set_perm_perm in H8 as [? ?]; eauto. eapply Mem.perm_implies; eauto; constructor.
  - intros. eapply mi_representable0; eauto.
    destruct H5.
    + left. eapply set_perm_perm in H5 as [? ?]; eauto. eapply Mem.perm_implies; eauto; constructor.
    + right. eapply set_perm_perm in H5 as [? ?]; eauto. eapply Mem.perm_implies; eauto; constructor.
  - intros.
    destruct (peq b1 b).
    + admit.
    + exploit mi_perm_inv0; eauto.
      eapply perm_set_2'; eauto. intros [].
      * left; eapply perm_set_2; eauto.
      * right; intros ?. eapply H6. eapply perm_set_2'; eauto.
Admitted.

Theorem set_outside_inject:
  forall f m1 m2 b p m1',
  inject f m1 m2 ->
  set_perm m1 b p = Some m1' ->
  f b = None ->
  inject f m1' m2.
Proof.
  intros. destruct H. constructor; eauto.
  - eapply set_outside_inj; eauto.
  - intros. eapply mi_freeblocks0. intros ?. exploit set_perm_valid_block_1; eauto.
  - intros ?????????????. eapply mi_no_overlap0; eauto.
    eapply set_perm_perm in H4 as [? ?]; eauto. eapply Mem.perm_implies; eauto; constructor.
    eapply set_perm_perm in H5 as [? ?]; eauto. eapply Mem.perm_implies; eauto; constructor.
  - intros. eapply mi_representable0; eauto.
    destruct H2.
    + left. eapply set_perm_perm in H2 as [? ?]; eauto. eapply Mem.perm_implies; eauto; constructor.
    + right. eapply set_perm_perm in H2 as [? ?]; eauto. eapply Mem.perm_implies; eauto; constructor.
  - intros. exploit mi_perm_inv0; eauto. intros [].
    + left. assert (b <> b1) by congruence.
      eapply perm_set_2; eauto.
    + right. assert (b <> b1) by congruence.
      intros ?. eapply H3. eapply perm_set_2'; eauto.
Qed.


Lemma set_outside_inject_parallel:
  forall f m1 m2 m3 b1 b3 delta b2 m1' m2' m3' P f',
    f b1 = Some (b3, delta) ->
    perm_order P Readable ->
    Mem.set_perm m1 b1 P = Some m1' ->
    Mem.inject f m1 m3 ->
    Mem.set_perm m2 b2 P = Some m2' ->
    Mem.inject f' m2 m3 ->
    Mem.set_perm m3 b3 P = Some m3' ->
    Mem.inject f' m2' m3'.
Proof.
Admitted.

Theorem set_outside_inject':
  forall f m1 m2 b p m2',
  inject f m1 m2 ->
  set_perm m2 b p = Some m2' ->
  (forall b0 delta, not (f b0 = Some (b, delta))) ->
  inject f m1 m2'.
Proof.
  intros. destruct H. constructor; eauto.
  - eapply set_outside_inj'; eauto.
  - intros.
    exploit set_perm_valid_block_1; eauto.
  - intros.
    destruct (Pos.eqb_spec b2 b).
    + subst.
      exploit mi_perm_inv0; eauto. eapply H1 in H. contradiction.
    + exploit mi_perm_inv0; eauto.
      eapply perm_set_2'; eauto.
Qed.

(* Lemma set_outside_inject': forall f m1 m2 b p m2', *)
(*   inject f m1 m2 -> *)
(*   set_perm m2 b p = Some m2' -> *)
(*   (forall b' delta ofs' k p, *)
(*     f b' = Some(b, delta) -> *)
(*     perm m1 b' ofs' k p -> *)
(*     False) -> *)
(*   inject f m1 m2'. *)
(* Proof. *)
(*   intros. destruct H. constructor; eauto. *)
(*   eapply set_outside_inj; eauto. *)
(*   intros. unfold valid_block in *. erewrite nextblock_set; eauto. *)
(*   intros. eapply mi_perm_inv0; eauto using perm_set_2'. *)
(*   admit. *)
(* Admitted. *)

(** Composing two memory injections. *)

Lemma mem_inj_compose:
  forall f f' m1 m2 m3,
  mem_inj f m1 m2 -> mem_inj f' m2 m3 -> mem_inj (compose_meminj f f') m1 m3.
Proof.
  intros. unfold compose_meminj. (* inv H; inv H0;  *)
  constructor; intros.
  (* perm *)
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H1.
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') by lia.
  inv H; inv H0; eauto.
  (* own *)
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H1.
  erewrite (mi_access _ _ _ H); eauto.
  erewrite (mi_access _ _ _ H0); eauto.
  eapply mi_perm; eauto.
  (* align *)
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H1.
  apply Z.divide_add_r.
  eapply (mi_align _ _ _ H); eauto.
  eapply mi_align with (ofs := ofs + delta') (p := p); eauto.
  red; intros. replace ofs0 with ((ofs0 - delta') + delta') by lia.
  eapply mi_perm; eauto. apply H2. lia.
  (* memval *)
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H1.
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') by lia.
  inv H; eauto. inv H0; eauto.
  eapply memval_inject_compose; eauto.
Qed.

Theorem inject_compose:
  forall f f' m1 m2 m3,
  inject f m1 m2 -> inject f' m2 m3 ->
  inject (compose_meminj f f') m1 m3.
Proof.
  unfold compose_meminj; intros.
  inv H; inv H0. constructor.
(* inj *)
  eapply mem_inj_compose; eauto.
(* unmapped *)
  intros. erewrite mi_freeblocks0; eauto.
(* mapped *)
  intros.
  destruct (f b) as [[b1 delta1] |] eqn:?; try discriminate.
  destruct (f' b1) as [[b2 delta2] |] eqn:?; inv H.
  eauto.
(* no overlap *)
  red; intros.
  destruct (f b1) as [[b1x delta1x] |] eqn:?; try discriminate.
  destruct (f' b1x) as [[b1y delta1y] |] eqn:?; inv H0.
  destruct (f b2) as [[b2x delta2x] |] eqn:?; try discriminate.
  destruct (f' b2x) as [[b2y delta2y] |] eqn:?; inv H1.
  exploit mi_no_overlap0; eauto. intros A.
  destruct (eq_block b1x b2x).
  subst b1x. destruct A. congruence.
  assert (delta1y = delta2y) by congruence. right; lia.
  exploit mi_no_overlap1. eauto. eauto. eauto.
    eapply perm_inj. eauto. eexact H2. eauto.
    eapply perm_inj. eauto. eexact H3. eauto.
  intuition lia.
(* representable *)
  intros.
  destruct (f b) as [[b1 delta1] |] eqn:?; try discriminate.
  destruct (f' b1) as [[b2 delta2] |] eqn:?; inv H.
  exploit mi_representable0; eauto. intros [A B].
  set (ofs' := Ptrofs.repr (Ptrofs.unsigned ofs + delta1)).
  assert (Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs + delta1).
    unfold ofs'; apply Ptrofs.unsigned_repr. auto.
  exploit mi_representable1. eauto. instantiate (1 := ofs').
  rewrite H.
  replace (Ptrofs.unsigned ofs + delta1 - 1) with
    ((Ptrofs.unsigned ofs - 1) + delta1) by lia.
  destruct H0; eauto using perm_inj.
  rewrite H. lia.
(* perm inv *)
  intros.
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; try discriminate.
  inversion H; clear H; subst b'' delta.
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') in H0 by lia.
  exploit mi_perm_inv1; eauto. intros [A|A].
  eapply mi_perm_inv0; eauto.
  right; red; intros. elim A. eapply perm_inj; eauto.
Qed.

Lemma val_lessdef_inject_compose:
  forall f v1 v2 v3,
  Val.lessdef v1 v2 -> Val.inject f v2 v3 -> Val.inject f v1 v3.
Proof.
  intros. inv H. auto. auto.
Qed.

Lemma val_inject_lessdef_compose:
  forall f v1 v2 v3,
  Val.inject f v1 v2 -> Val.lessdef v2 v3 -> Val.inject f v1 v3.
Proof.
  intros. inv H0. auto. inv H. auto.
Qed.

Lemma extends_inject_compose:
  forall f m1 m2 m3,
  extends m1 m2 -> inject f m2 m3 -> inject f m1 m3.
Proof.
  intros. inversion H; inv H0. constructor; intros.
(* inj *)
  replace f with (compose_meminj inject_id f). eapply mem_inj_compose; eauto.
  apply extensionality; intros. unfold compose_meminj, inject_id.
  destruct (f x) as [[y delta] | ]; auto.
(* unmapped *)
  eapply mi_freeblocks0. erewrite <- valid_block_extends; eauto.
(* mapped *)
  eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_extends; eauto.
(* representable *)
  eapply mi_representable0; eauto.
  destruct H1; eauto using perm_extends.
(* perm inv *)
  exploit mi_perm_inv0; eauto. intros [A|A].
  eapply mext_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_extends; eauto.
Qed.

Lemma inject_extends_compose:
  forall f m1 m2 m3,
  inject f m1 m2 -> extends m2 m3 -> inject f m1 m3.
Proof.
  intros. inv H; inversion H0. constructor; intros.
(* inj *)
  replace f with (compose_meminj f inject_id). eapply mem_inj_compose; eauto.
  apply extensionality; intros. unfold compose_meminj, inject_id.
  destruct (f x) as [[y delta] | ]; auto. decEq. decEq. lia.
(* unmapped *)
  eauto.
(* mapped *)
  erewrite <- valid_block_extends; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto.
(* representable *)
  eapply mi_representable0; eauto.
(* perm inv *)
  exploit mext_perm_inv0; eauto. intros [A|A].
  eapply mi_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_inj; eauto.
Qed.

Lemma extends_extends_compose:
  forall m1 m2 m3,
  extends m1 m2 -> extends m2 m3 -> extends m1 m3.
Proof.
  intros. inversion H; subst; inv H0; constructor; intros.
  (* nextblock *)
  congruence.
  (* meminj *)
  replace inject_id with (compose_meminj inject_id inject_id).
  eapply mem_inj_compose; eauto.
  apply extensionality; intros. unfold compose_meminj, inject_id. auto.
  (* perm inv *)
  exploit mext_perm_inv1; eauto. intros [A|A].
  eapply mext_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_extends; eauto.
Qed.

(** Injecting a memory into itself. *)

Definition flat_inj (thr: block) : meminj :=
  fun (b: block) => if plt b thr then Some(b, 0) else None.

Definition inject_neutral (thr: block) (m: mem) :=
  mem_inj (flat_inj thr) m m.

Remark flat_inj_no_overlap:
  forall thr m, meminj_no_overlap (flat_inj thr) m.
Proof.
  unfold flat_inj; intros; red; intros.
  destruct (plt b1 thr); inversion H0; subst.
  destruct (plt b2 thr); inversion H1; subst.
  auto.
Qed.

Theorem neutral_inject:
  forall m, inject_neutral (nextblock m) m -> inject (flat_inj (nextblock m)) m m.
Proof.
  intros. constructor.
(* meminj *)
  auto.
(* freeblocks *)
  unfold flat_inj, valid_block; intros.
  apply pred_dec_false. auto.
(* mappedblocks *)
  unfold flat_inj, valid_block; intros.
  destruct (plt b (nextblock m)); inversion H0; subst. auto.
(* no overlap *)
  apply flat_inj_no_overlap.
(* range *)
  unfold flat_inj; intros.
  destruct (plt b (nextblock m)); inv H0. generalize (Ptrofs.unsigned_range_2 ofs); lia.
(* perm inv *)
  unfold flat_inj; intros.
  destruct (plt b1 (nextblock m)); inv H0.
  rewrite Z.add_0_r in H1; auto.
Qed.

Theorem empty_inject_neutral:
  forall thr, inject_neutral thr empty.
Proof.
  intros; red; constructor.
(* perm *)
  unfold flat_inj; intros. destruct (plt b1 thr); inv H.
  replace (ofs + 0) with ofs by lia; auto.
(* own *)
  intros.
  unfold block_compartment, empty; simpl.
  now rewrite !PMap.gi.
(* align *)
  unfold flat_inj; intros. destruct (plt b1 thr); inv H. apply Z.divide_0_r.
(* mem_contents *)
  intros; simpl. rewrite ! PMap.gi. rewrite ! ZMap.gi. constructor.
Qed.

Theorem alloc_inject_neutral:
  forall thr m c lo hi b m',
  alloc m c lo hi = (m', b) ->
  inject_neutral thr m ->
  Plt (nextblock m) thr ->
  inject_neutral thr m'.
Proof.
  intros; red.
  eapply alloc_left_mapped_inj with (m1 := m) (b2 := b) (delta := 0).
  eapply alloc_right_inj; eauto. eauto. eauto with mem.
  red. intros. apply Z.divide_0_r.
  intros.
  apply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto. lia.
  unfold flat_inj. apply pred_dec_true.
  rewrite (alloc_result _ _ _ _ _ _ H). auto.
  eapply owned_new_block in H; subst; eauto with comps.
Qed.

Theorem store_inject_neutral:
  forall chunk m b ofs v cp m' thr,
  store chunk m b ofs v cp = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  Val.inject (flat_inj thr) v v ->
  inject_neutral thr m'.
Proof.
  intros; red.
  exploit store_mapped_inj. eauto. eauto. apply flat_inj_no_overlap.
  unfold flat_inj. apply pred_dec_true; auto. eauto.
  replace (ofs + 0) with ofs by lia.
  intros [m'' [A B]]. congruence.
Qed.

Theorem drop_inject_neutral:
  forall m b lo hi p cp m' thr,
  drop_perm m b lo hi p cp = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  inject_neutral thr m'.
Proof.
  unfold inject_neutral; intros.
  exploit drop_mapped_inj; eauto. apply flat_inj_no_overlap.
  unfold flat_inj. apply pred_dec_true; eauto.
  repeat rewrite Z.add_0_r. intros [m'' [A B]]. congruence.
Qed.

(** * Invariance properties between two memory states *)

Section UNCHANGED_ON.

Variable P: block -> Z -> Prop.

Record unchanged_on (m_before m_after: mem) : Prop := mk_unchanged_on {
  unchanged_on_nextblock:
    Ple (nextblock m_before) (nextblock m_after);
  unchanged_on_perm:
    forall b ofs k p,
    P b ofs -> valid_block m_before b ->
    (perm m_before b ofs k p <-> perm m_after b ofs k p);
  unchanged_on_contents:
    forall b ofs,
    P b ofs -> perm m_before b ofs Cur Readable ->
    ZMap.get ofs (PMap.get b m_after.(mem_contents)) =
    ZMap.get ofs (PMap.get b m_before.(mem_contents));
  unchanged_on_own:
    forall b,
    valid_block m_before b -> (* Adjust preconditions as needed. *)
      block_compartment m_after b = block_compartment m_before b
    (* valid_block m_before b -> (* Adjust preconditions as needed. *) *)
    (* (can_access_block m_before b cp -> can_access_block m_after b cp) *)
}.

Lemma unchanged_on_refl:
  forall m, unchanged_on m m.
Proof.
  intros; constructor. apply Ple_refl. tauto. tauto. auto with comps.
Qed.

Lemma valid_block_unchanged_on:
  forall m m' b,
  unchanged_on m m' -> valid_block m b -> valid_block m' b.
Proof.
  unfold valid_block; intros. apply unchanged_on_nextblock in H. extlia.
Qed.

Lemma perm_unchanged_on:
  forall m m' b ofs k p,
  unchanged_on m m' -> P b ofs ->
  perm m b ofs k p -> perm m' b ofs k p.
Proof.
  intros. destruct H. apply unchanged_on_perm0; auto. eapply perm_valid_block; eauto.
Qed.

Lemma perm_unchanged_on_2:
  forall m m' b ofs k p,
  unchanged_on m m' -> P b ofs -> valid_block m b ->
  perm m' b ofs k p -> perm m b ofs k p.
Proof.
  intros. destruct H. apply unchanged_on_perm0; auto.
Qed.

Lemma unchanged_on_trans:
  forall m1 m2 m3, unchanged_on m1 m2 -> unchanged_on m2 m3 -> unchanged_on m1 m3.
Proof.
  intros; constructor.
- apply Ple_trans with (nextblock m2); apply unchanged_on_nextblock; auto.
- intros. transitivity (perm m2 b ofs k p); apply unchanged_on_perm; auto.
  eapply valid_block_unchanged_on; eauto.
- intros. transitivity (ZMap.get ofs (mem_contents m2)#b); apply unchanged_on_contents; auto.
  eapply perm_unchanged_on; eauto.
- intros. transitivity (block_compartment m2 b).
  (* eapply flowsto_trans; eauto. *)
  eapply unchanged_on_own; eauto using valid_block_unchanged_on.
  eapply unchanged_on_own; eauto using valid_block_unchanged_on.
Qed.

Lemma loadbytes_unchanged_on_1:
  forall m m' b ofs n cp,
  unchanged_on m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  (* forall OWN : can_access_block m b cp, *)
  loadbytes m' b ofs n cp = loadbytes m b ofs n cp.
Proof.
  intros.
  destruct (zle n 0).
- (* destruct (plt b (nextblock m)) as [e0 | n0]. *)
  destruct (can_access_block_dec m b cp).
  + erewrite ! loadbytes_empty; try easy.
  + unfold loadbytes.
    destruct (Z_le_dec n 0).
    * simpl. rewrite 2!orb_true_r.
      destruct range_perm_dec.
      destruct range_perm_dec. simpl.
      f_equal.
      apply getN_exten. intros. lia.
      exfalso. apply n1. intros ? ?. lia.
      exfalso. apply n1. intros ? ?. lia.
    * rewrite 2!andb_false_intro2; auto.
      destruct can_access_block_dec; now auto.
      destruct can_access_block_dec; auto.
      simpl in *.
      erewrite unchanged_on_own in c; eauto. contradiction.
- unfold loadbytes. destruct H.
  setoid_rewrite pred_dec_false at 3 6; [| lia | lia].
  destruct (range_perm_dec m b ofs (ofs + n) Cur Readable).
+ destruct (can_access_block_dec m b cp).
* setoid_rewrite pred_dec_true. simpl. f_equal.
  apply getN_exten. intros. rewrite Z2Nat.id in H by lia.
  apply unchanged_on_contents0; auto.
  red; intros. apply unchanged_on_perm0; auto.
  simpl. eapply flowsto_trans; eauto.
  erewrite unchanged_on_own0; auto with comps.
* simpl.
  rewrite andb_false_intro2; auto.
    destruct can_access_block_dec; auto.
    simpl in *.
    erewrite unchanged_on_own0 in c; eauto. contradiction.
+ setoid_rewrite pred_dec_false at 1. auto.
  red; intros; elim n0; red; intros. apply <- unchanged_on_perm0; auto.
Qed.

(* RB: TODO: Relocate. *)
Lemma loadbytes_can_access_block_inj:
  forall m b ofs n cp bytes,
  loadbytes m b ofs n cp = Some bytes ->
  can_access_block m b cp \/ n <= 0.
Proof.
  unfold loadbytes. intros.
  destruct (range_perm_dec m b ofs (ofs + n) Cur Readable); [| inversion H].
  destruct (can_access_block_dec m b cp), Z_le_dec; inv H.
  left; assumption.
  left; assumption.
  right; assumption.
Qed.

Lemma loadbytes_unchanged_on:
  forall m m' b ofs n cp bytes,
  unchanged_on m m' ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m b ofs n cp = Some bytes ->
  loadbytes m' b ofs n cp = Some bytes.
Proof.
  intros.
  pose proof loadbytes_can_access_block_inj _ _ _ _ _ _ H1 as Hown.
  destruct (zle n 0).
+ destruct (plt b (nextblock m)).
  - rewrite <- H1. apply loadbytes_unchanged_on_1; auto.
  -
    (* unfold loadbytes in *. *)
    (* destruct (Z_le_dec); try lia. *)
    (* destruct (range_perm_dec); try discriminate. *)
    (* rewrite orb_true_r in *. simpl in *. *)
    (* destruct (range_perm_dec); simpl; auto. *)
    (* assert (cp = top). *)
    (* { exploit block_compartment_valid_block; eauto. simpl in Hown. *)
    (*   intros R; rewrite R in Hown. *)
    (*   inv Hown; auto. } *)
    (* subst cp. *)
    erewrite loadbytes_empty in *; try assumption.
+ rewrite <- H1. apply loadbytes_unchanged_on_1; auto.
  exploit loadbytes_range_perm; eauto. instantiate (1 := ofs). lia.
  intros. eauto with mem.
Qed.

Lemma load_unchanged_on_1:
  forall m m' chunk b cp ofs,
  unchanged_on m m' ->
  valid_block m b ->
  forall (OWN: can_access_block m b cp),
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m' b ofs cp = load chunk m b ofs cp.
Proof.
  intros. unfold load. destruct (valid_access_dec m chunk b ofs Readable cp).
- destruct v as [H2 [H' H3]]. rewrite pred_dec_true. f_equal. f_equal. apply getN_exten. intros.
  rewrite <- size_chunk_conv in H4. eapply unchanged_on_contents; eauto.
  split; auto. red; intros. eapply perm_unchanged_on; eauto.
  split; auto.
  simpl; eapply flowsto_trans; eauto using unchanged_on_own.
  erewrite unchanged_on_own; eauto with comps.
- rewrite pred_dec_false. auto.
  red; intros [A [B C]]; elim n; split; auto. red; intros; eapply perm_unchanged_on_2; eauto.
Qed.

Lemma load_unchanged_on:
  forall m m' chunk b ofs cp v,
  unchanged_on m m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m b ofs cp = Some v ->
  load chunk m' b ofs cp = Some v.
Proof.
  intros. rewrite <- H1. eapply load_unchanged_on_1; eauto with mem.
  unfold load in H1. destruct (valid_access_dec m chunk b ofs Readable cp) as [v0 | ?]; try congruence.
  destruct v0 as [? [? ?]]; auto.
Qed.

Lemma store_unchanged_on:
  forall chunk m b ofs v cp m',
  store chunk m b ofs v cp = Some m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_store _ _ _ _ _ _ _ H). apply Ple_refl.
- split; intros; eauto with mem.
- erewrite store_mem_contents; eauto. rewrite PMap.gsspec.
  destruct (peq b0 b); auto. subst b0. apply setN_outside.
  rewrite encode_val_length. rewrite <- size_chunk_conv.
  destruct (zlt ofs0 ofs); auto.
  destruct (zlt ofs0 (ofs + size_chunk chunk)); auto.
  elim (H0 ofs0). lia. auto.
- erewrite <- store_preserves_comp; eauto with comps.
Qed.

Lemma storebytes_unchanged_on:
  forall m b ofs bytes cp m',
  storebytes m b ofs bytes cp = Some m' ->
  (forall i, ofs <= i < ofs + Z.of_nat (length bytes) -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_storebytes _ _ _ _ _ _ H). apply Ple_refl.
- split; intros. eapply perm_storebytes_1; eauto. eapply perm_storebytes_2; eauto.
- erewrite storebytes_mem_contents; eauto. rewrite PMap.gsspec.
  destruct (peq b0 b); auto. subst b0. apply setN_outside.
  destruct (zlt ofs0 ofs); auto.
  destruct (zlt ofs0 (ofs + Z.of_nat (length bytes))); auto.
  elim (H0 ofs0). lia. auto.
- erewrite <- storebytes_preserves_comp; eauto with comps.
Qed.

Lemma alloc_unchanged_on:
  forall m c lo hi m' b,
  alloc m c lo hi = (m', b) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_alloc _ _ _ _ _ _ H). apply Ple_succ.
- split; intros.
  eapply perm_alloc_1; eauto.
  eapply perm_alloc_4; eauto.
  eapply valid_not_valid_diff; eauto with mem.
- injection H; intros A B. rewrite <- B; simpl.
  rewrite PMap.gso; auto. rewrite A.  eapply valid_not_valid_diff; eauto with mem.
- destruct (peq b0 b).
+ subst b0.
  apply fresh_block_alloc in H; contradiction.
+ unfold alloc in H. inv H; subst. unfold block_compartment. simpl.
  rewrite PMap.gso; auto.
Qed.

Lemma free_unchanged_on:
  forall m b lo hi cp m',
  free m b lo hi cp = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_free _ _ _ _ _ _ H). apply Ple_refl.
- split; intros.
  eapply perm_free_1; eauto.
  destruct (eq_block b0 b); auto. destruct (zlt ofs lo); auto. destruct (zle hi ofs); auto.
  subst b0. elim (H0 ofs). lia. auto.
  eapply perm_free_3; eauto.
- unfold free in H.
  destruct (Z_le_dec hi lo); [now inv H |];
  destruct (range_perm_dec m b lo hi Cur Freeable);
  destruct (can_access_block_dec m b cp);
  inv H. unfold unchecked_free; destruct (zle hi lo); simpl; auto.
- erewrite <- free_preserves_comp; eauto with comps.
Qed.

Lemma drop_perm_unchanged_on:
  forall m b lo hi p cp m',
  drop_perm m b lo hi p cp = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_drop _ _ _ _ _ _ _ H). apply Ple_refl.
- split; intros. eapply perm_drop_3; eauto.
  destruct (eq_block b0 b); auto.
  subst b0.
  assert (~ (lo <= ofs < hi)). { red; intros; eelim H0; eauto. }
  right; lia.
  eapply perm_drop_4; eauto.
- unfold drop_perm in H.
  destruct (Z_le_dec hi lo); [now inv H |];
  destruct (range_perm_dec m b lo hi Cur Freeable);
  destruct (can_access_block_dec m b cp);
  inv H; simpl. auto.
- erewrite <- drop_preserves_comp; eauto with comps.
Qed.

End UNCHANGED_ON.

Lemma unchanged_on_implies:
  forall (P Q: block -> Z -> Prop) m m',
  unchanged_on P m m' ->
  (forall b ofs, Q b ofs -> valid_block m b -> P b ofs) ->
  unchanged_on Q m m'.
Proof.
  intros. destruct H. constructor; intros.
- auto.
- apply unchanged_on_perm0; auto.
- apply unchanged_on_contents0; auto.
  apply H0; auto. eapply perm_valid_block; eauto.
- apply unchanged_on_own0; auto.
Qed.

Section SECURITY.

#[export] Instance has_side_block: has_side block :=
  { in_side '(s, m) := fun b δ => s (Mem.block_compartment m b) = δ }.

#[export] Instance has_side_value: has_side val :=
  {| in_side := fun '(s, m) v δ => match v with
                                | Vptr b _=> (s, m) |= b ∈ δ
                                | _ => False
                                end |}.

Definition same_domain (s: split) (j: meminj) (δ: side) (m: mem): Prop :=
  forall b, (j b <> None <-> (s, m) |= b ∈ δ).

Definition delta_zero (j: meminj): Prop :=
  forall loc loc' delta, j loc = Some (loc', delta) -> delta = 0.

Definition meminj_injective (j: meminj): Prop :=
  forall b1 b2 b1' b2' ofs1 ofs2,
      b1 <> b2 ->
      j b1 = Some (b1', ofs1) ->
      j b2 = Some (b2', ofs2) ->
      b1' <> b2' \/ ofs1 <> ofs2.
End SECURITY.

End Mem.

#[export] Existing Instance Mem.has_side_block.
#[export] Existing Instance Mem.has_side_value.

Notation mem := Mem.mem.

Global Opaque Mem.alloc Mem.free Mem.store Mem.load Mem.storebytes Mem.loadbytes.

Global Hint Resolve
  Mem.valid_not_valid_diff
  Mem.perm_implies
  Mem.perm_cur
  Mem.perm_max
  Mem.perm_valid_block
  Mem.range_perm_implies
  Mem.range_perm_cur
  Mem.range_perm_max
  Mem.valid_access_implies
  Mem.valid_access_valid_block
  Mem.valid_access_perm
  Mem.valid_access_load
  Mem.load_valid_access
  Mem.loadbytes_range_perm
  Mem.valid_access_store
  Mem.perm_store_1
  Mem.perm_store_2
  Mem.nextblock_store
  Mem.store_valid_block_1
  Mem.store_valid_block_2
  Mem.store_valid_access_1
  Mem.store_valid_access_2
  Mem.store_valid_access_3
  Mem.storebytes_range_perm
  Mem.perm_storebytes_1
  Mem.perm_storebytes_2
  Mem.storebytes_valid_access_1
  Mem.storebytes_valid_access_2
  Mem.nextblock_storebytes
  Mem.storebytes_valid_block_1
  Mem.storebytes_valid_block_2
  Mem.nextblock_alloc
  Mem.alloc_result
  Mem.valid_block_alloc
  Mem.fresh_block_alloc
  Mem.valid_new_block
  Mem.perm_alloc_1
  Mem.perm_alloc_2
  Mem.perm_alloc_3
  Mem.perm_alloc_4
  Mem.perm_alloc_inv
  Mem.valid_access_alloc_other
  Mem.valid_access_alloc_same
  Mem.valid_access_alloc_inv
  Mem.range_perm_free
  Mem.free_range_perm
  Mem.nextblock_free
  Mem.valid_block_free_1
  Mem.valid_block_free_2
  Mem.perm_free_1
  Mem.perm_free_2
  Mem.perm_free_3
  Mem.valid_access_free_1
  Mem.valid_access_free_2
  Mem.valid_access_free_inv_1
  Mem.valid_access_free_inv_2
  Mem.unchanged_on_refl
: mem.
