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

(** Global environments are a component of the dynamic semantics of
  all languages involved in the compiler.  A global environment
  maps symbol names (names of functions and of global variables)
  to the corresponding memory addresses.  It also maps memory addresses
  of functions to the corresponding function descriptions.

  Global environments, along with the initial memory state at the beginning
  of program execution, are built from the program of interest, as follows:
- A distinct memory address is assigned to each function of the program.
  These function addresses use negative numbers to distinguish them from
  addresses of memory blocks.  The associations of function name to function
  address and function address to function description are recorded in
  the global environment.
- For each global variable, a memory block is allocated and associated to
  the name of the variable.

  These operations reflect (at a high level of abstraction) what takes
  place during program linking and program loading in a real operating
  system. *)

(** This file consists of the altered definition of globalenvs for the
capability machine backend, where symbols are now matched to capabilities *)

Require Import Recdef.
Require Import Zwf.
Require Import Axioms Coqlib Errors Maps CapAST Linking.
Require Import Integers Floats OCapValues CapMemory.

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.

Local Open Scope pair_scope.
Local Open Scope error_monad_scope.

Set Implicit Arguments.

Arguments Some [A] _.
Arguments None [A].

(** standard maybe monad for option types *)
Definition ret {A : Type} (x : A) := Some x.
Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
    | Some x => f x
    | None => None
  end.

Notation "A >>= F" := (bind A F) (at level 42, left associativity).
Notation "'do' X <- A ; B" := (bind A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200).

Lemma mon_left_id : forall (A B : Type) (a : A) (f : A -> option B),
  ret a >>= f = f a.
intros.
reflexivity.
Qed.
 
Lemma mon_right_id : forall (A : Type) (a : option A),
  a >>= ret = a.
intros.
induction a; repeat reflexivity.
Qed.
 
Lemma mon_assoc :
  forall (A B C : Type) (a : option A) (f : A -> option B) (g : B -> option C),
    (a >>= f) >>= g = a >>= (fun x => f x >>= g).
intros.
induction a; repeat reflexivity.
Qed.

(** Lifting a unary relation to an option type. *)

Inductive option_urel (A: Type) (R: A -> Prop) : option A -> Prop :=
  | option_urel_none: option_urel R None
  | option_urel_some: forall x, R x -> option_urel R (Some x).

(** Auxiliary function for initialization of global variables. *)

(** The following version assumes an init capability *)
Function store_zeros (m: mem) (ptr: occap) (n: Z) (cp: compartment) {wf (Zwf 0) n}: occap * mem + error_kind :=
  if zle n 0 then inl (ptr,m) else
    match Mem.store DIR CMint8unsigned m ptr 0 OCVzero cp, incr_addr_stk ptr 1 with
    | inl (_,m'),Some ptr' => store_zeros m' ptr' (n - 1) cp
    | inr err,_ => inr err
    | inl _, None => inr CapErr
    end.
Proof.
  intros. red. omega.
  apply Zwf_well_founded.
Qed.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

(** * Symbol environments *)

(** Symbol environments are a restricted view of global environments,
  focusing on symbol names and their associated blocks.  They do not
  contain mappings from blocks to function or variable definitions. *)

Module Senv.

Record t: Type := mksenv {
  (** Operations *)
  find_symbol: ident -> option occap;
  public_symbol: ident -> bool;
  invert_symbol: occap -> option ident;
  block_is_volatile: occap -> bool;
  snext: ptrofs;
  sstart: ptrofs;
  send: ptrofs;
  (** Properties *)
  find_symbol_injective:
    forall id1 id2 b, find_symbol id1 = Some b -> find_symbol id2 = Some b -> id1 = id2;
  invert_find_symbol:
    forall id b, invert_symbol b = Some id -> find_symbol id = Some b;
  find_invert_symbol:
    forall id b, find_symbol id = Some b -> invert_symbol b = Some id;
  public_symbol_exists:
    forall id, public_symbol id = true -> exists b, find_symbol id = Some b;
}.

Definition symbol_address (ge: t) (id: ident) (ofs: ptrofs) : ocval :=
  match find_symbol ge id with
  | Some c =>
      if Ptrofs.unsigned ofs =? 0 then
        OCVcap c
      else 
        match Val.offset_cap c ofs with
        | None => OCVundef
        | Some c' => OCVcap c'
        end
  | None => OCVundef
  end.

(* Theorem shift_symbol_address: *)
(*   forall ge id ofs delta, *)
(*   symbol_address ge id (Ptrofs.add ofs delta) = Val.offset_ptr (symbol_address ge id ofs) delta. *)
(* Proof. *)
(*   intros. unfold symbol_address, Val.offset_ptr. destruct (find_symbol ge id); auto. *)
(* Qed. *)

(* Theorem shift_symbol_address_32: *)
(*   forall ge id ofs n, *)
(*   Archi.ptr64 = false -> *)
(*   symbol_address ge id (Ptrofs.add ofs (Ptrofs.of_int n)) = Val.add (symbol_address ge id ofs) (Vint n). *)
(* Proof. *)
(*   intros. unfold symbol_address. destruct (find_symbol ge id). *)
(* - unfold Val.add. rewrite H. auto. *)
(* - auto. *)
(* Qed. *)

(* Theorem shift_symbol_address_64: *)
(*   forall ge id ofs n, *)
(*   Archi.ptr64 = true -> *)
(*   symbol_address ge id (Ptrofs.add ofs (Ptrofs.of_int64 n)) = Val.addl (symbol_address ge id ofs) (Vlong n). *)
(* Proof. *)
(*   intros. unfold symbol_address. destruct (find_symbol ge id). *)
(* - unfold Val.addl. rewrite H. auto. *)
(* - auto. *)
(* Qed. *)

Definition equiv (se1 se2: t) : Prop :=
     (forall id, find_symbol se2 id = find_symbol se1 id)
  /\ (forall id, public_symbol se2 id = public_symbol se1 id)
  /\ (forall b, block_is_volatile se2 b = block_is_volatile se1 b).

End Senv.

Module Genv.

(** * Global environments *)

Section GENV.

Variable F: Type.  (**r The type of function descriptions *)
Variable V: Type.  (**r The type of information attached to variables *) 

(** function that calculates the region size of a global def *)
(* AINA: might need to change the size of a function to be the number
  of instructions + wrapper size. No need to actually store
  instructions in memory, but since size is observation, the compiler
  will only be FA if the function pointer points to a region of the
  appropriate size *)
Definition globdef_size: (globdef F V) -> Z :=
  fun g => match g with
        | Gfun _ => 1
        | Gvar g => Z.max 1 (cap_init_data_list_size (gvar_init g)) (* want to avoid empty region *)
        end.

(** function that derives a capability of the correct size given a
  starting address and a global def *)
Variable build_capability: ptrofs -> (globdef F V) -> occap.

(** function that derives the stack capability given a start and a
  size *)
Variable stack_size: Z.
Variable build_stack_capability: ptrofs -> occap.

(** function that derives the heap capability of a given a starting
  address. Each heap has a fixed predetermined size *)
Variable heap_size: Z.
Variable build_heap_capability: ptrofs -> occap.

Definition isFunctionCap (c: occap): bool :=
  match c with
  | OCsealable (OCVmem RX Global _ _ _) => true
  | _ => false
  end.

Definition isVarCap (c: occap): bool :=
  match c with
  | OCsealable (OCVmem RW Global _ _ _) => true
  | _ => false
  end.

Definition isEntryCap (c: occap): bool :=
  match c with
  | OCsealed _ (OCVmem RX Global _ _ _) => true
  | _ => false
  end.

Definition isStackCap (c: occap): bool :=
  match c with
  | OCsealable (OCVmem URWL Directed _ _ _) => true
  | _ => false
  end.

Definition globdef_capability_spec : ptrofs -> globdef F V -> occap -> Prop :=
  fun base glob c =>
    Ptrofs.eq (get_lo c) base = true
    /\ Ptrofs.eq (get_lo c) (get_addr c) = true
    /\ get_region_size c = globdef_size glob
    /\ is_mem_cap c
    /\ match glob with
      | Gfun _ => isEntryCap c = true
      | Gvar g => isVarCap c = true
      end.

Definition stack_capability_spec : ptrofs -> occap -> Prop :=
  fun base c =>
    Ptrofs.eq (get_lo c) base = true
    /\ Ptrofs.unsigned (get_lo c) <= Ptrofs.unsigned (get_hi c)
    /\ get_region_size c = stack_size mod Ptrofs.modulus
    /\ isStackCap c = true.

Definition heap_capability_spec : ptrofs -> occap -> Prop :=
  fun base c =>
    Ptrofs.eq (get_lo c) base = true
    /\ Ptrofs.unsigned (get_lo c) <= Ptrofs.unsigned (get_hi c)
    /\ get_region_size c = heap_size mod Ptrofs.modulus
    /\ isVarCap c = true.

Variable build_capability_inv:
  forall base glob, globdef_capability_spec base glob (build_capability base glob).

Variable build_stack_capability_inv:
  forall base, stack_capability_spec base (build_stack_capability base).

Variable build_heap_capability_inv:
  forall base, heap_capability_spec base (build_heap_capability base).

Lemma globdef_size_pos:
  forall glob, (globdef_size glob > 0).
Proof.
  intros. destruct glob;simpl;try omega.
  rewrite Zmax_spec.
  destruct zlt;omega.
Qed.

Context {CF: has_comp F}.

(** The type of global environments. *)

Definition cap_to_Z_lo (ptr: occap) : Z :=
  (Ptrofs.unsigned (get_lo ptr)).

Record t: Type := mkgenv {
  genv_public: list ident;              (**r which symbol names are public *)
  genv_symb: PTree.t occap;             (**r mapping symbol -> capability *)
  genv_defs: PTree.t (globdef F V);     (**r mapping the lower bound of cap -> definition *)
  genv_heaps: PTree.t occap;            (**r mapping from compartments to heap capabilities *)
  genv_stack: option occap;             (**r stack capability *)
  genv_next: ptrofs;                    (**r next symbol pointer *)
  genv_start: ptrofs;                   (**r the bottom range of the globals environment *)
  genv_end: ptrofs;                     (**r the top limit of the globals environment *)
  genv_policy: Policy.t;                (**r policy *)
  genv_symb_range: forall id c, PTree.get id genv_symb = Some c -> Ptrofs.unsigned (get_lo c) < Ptrofs.unsigned genv_next;
  genv_defs_range: forall ptr g, ZTree.get (cap_to_Z_lo ptr) genv_defs = Some g -> Ptrofs.unsigned (get_lo ptr) < Ptrofs.unsigned genv_next;
  genv_vars_inj: forall id1 id2 b,
   PTree.get id1 genv_symb = Some b -> PTree.get id2 genv_symb = Some b -> id1 = id2;
  genv_next_in_bounds: Ptrofs.unsigned genv_start <= Ptrofs.unsigned genv_next < Ptrofs.unsigned genv_end                  
}.

(** ** Lookup functions *)

(** [find_symbol ge id] returns the block associated with the given name, if any *)

Definition find_symbol (ge: t) (id: ident) : option occap :=
  PTree.get id ge.(genv_symb).

(** [symbol_address ge id ofs] returns a pointer into the block associated
  with [id], at byte offset [ofs].  [Vundef] is returned if no block is associated
  to [id], or if there is an attempt at altering a sealed capability *)

Definition symbol_address (ge: t) (id: ident) (ofs: ptrofs) : ocval :=
  match find_symbol ge id with
  | Some c =>
      if Ptrofs.unsigned ofs =? 0 then
        OCVcap c
      else 
        match Val.offset_cap c ofs with
        | None => OCVundef
        | Some c' => OCVcap c'
        end
  | None => OCVundef
  end.

(** [public_symbol ge id] says whether the name [id] is public and defined. *)

Definition public_symbol (ge: t) (id: ident) : bool :=
  match find_symbol ge id with
  | None => false
  | Some _ => In_dec ident_eq id ge.(genv_public)
  end.

(** [find_def ge b] returns the global definition associated with the given capability. *)

Definition find_def (ge: t) (ptr: occap) : option (globdef F V) :=
  ZTree.get (cap_to_Z_lo ptr) ge.(genv_defs).

(** [find_funct_ptr ge b] returns the function description associated with
    the given address. *)

Definition find_funct_ptr (ge: t) (ptr: occap) : option F :=
  match find_def ge ptr with Some (Gfun f) => Some f | _ => None end.

Definition find_funct_size (ge: t) (lo: positive) : Z :=
  match  PTree.get lo ge.(genv_defs) with Some f => globdef_size f | None => 0 end.
  
(** [find_funct] is similar to [find_funct_ptr], but the function
    address is given as a value, which must be a memory capability
    with address pointing to the base. *)

Definition find_funct (ge: t) (v: ocval) : option F :=
  match v with
  | OCVcap c =>
      if Ptrofs.eq_dec (get_lo c) (get_addr c) && is_mem_cap_b c
      then find_funct_ptr ge c
      else None
  | _ => None
  end.

(** [find_comp ge v] finds the compartment associated with the pointer [v] as it
    is recorded in [ge]. *)

Definition find_comp (ge: t) (v: ocval) : compartment :=
  match v with
  | OCVcap c =>
    match find_funct_ptr ge c with
    | Some f => (comp_of f)
    | None   => default_compartment
    end
  | _ => default_compartment
  end.

Lemma find_comp_null:
  forall ge, find_comp ge Vnullptr = default_compartment.
Proof.
  unfold find_comp, Vnullptr.
  now destruct Archi.ptr64.
Qed.

(** [invert_symbol ge b] returns the name associated with the given block, if any *)

Definition invert_symbol (ge: t) (c: occap) : option ident :=
  PTree.fold
    (fun res id c' => if occap_dec c c' then Some id else res)
    ge.(genv_symb) None.

(** [find_var_info ge b] returns the information attached to the variable
   at address [b]. *)

Definition find_var_info (ge: t) (c: occap) : option (globvar V) :=
  match find_def ge c with Some (Gvar v) => Some v | _ => None end.

(** [block_is_volatile ge b] returns [true] if [b] points to a global variable
  of volatile type, [false] otherwise. *)

Definition block_is_volatile (ge: t) (c: occap) : bool :=
  match find_var_info ge c with
  | None => false
  | Some gv => gv.(gvar_volatile)
  end.

(** ** Constructing the global environment *)

Lemma build_capability_inv_lt:
  forall base genv c, c = build_capability base genv ->
                 Ptrofs.unsigned (get_lo c) <= Ptrofs.unsigned (get_hi c).
Proof.
  intros until c. intros Heqc.
  pose proof (build_capability_inv base genv) as [S [B [Size [C G]]]].
  rewrite <- Heqc in *.
  destruct c,o;[|easy..].
  apply Ptrofs.same_if_eq in S.
  apply Ptrofs.same_if_eq in B. subst.
  unfold get_region_size_nat,get_region_size in Size. simpl in *.
  pose proof (Ptrofs.unsigned_range i) as [? _].
  pose proof (Ptrofs.unsigned_range i0) as [? _].
  (* rewrite Z2Nat.inj_sub in Size;auto. *)
  pose proof (globdef_size_pos genv).
  omega.
Qed.  
  
Program Definition add_global (idg: ident * globdef F V) (ge: t): option t :=
  let cap := build_capability ge.(genv_next) idg#2 in
  if zlt (Ptrofs.unsigned (get_hi cap)) (Ptrofs.unsigned ge.(genv_end)) then
    Some (@mkgenv
      ge.(genv_public)
      (PTree.set idg#1 cap ge.(genv_symb))
      (ZTree.set (cap_to_Z_lo cap) idg#2 ge.(genv_defs))
      ge.(genv_heaps)
      ge.(genv_stack)
      (get_hi cap)
      ge.(genv_start)
      ge.(genv_end)
      (genv_policy ge)
      _ _ _ _)
  else None.
Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gsspec in H0.
  inv H0. pose proof (build_capability_inv genv_next0 g).
  destruct H0 as [B [S [Size [C G]]]].
  remember (build_capability genv_next0 g) as cap.
  destruct cap,o;[|easy..].
  pose proof (build_capability_inv_lt Heqcap) as LT. simpl in *.
  destruct (peq id i).
  - unfold get_region_size_nat,get_region_size in Size.
    pose proof (Ptrofs.unsigned_range i0) as [? _].
    pose proof (globdef_size_pos g).
    subst. inv H2. simpl in *. omega.
  - apply genv_symb_range0 in H2.
    apply Ptrofs.same_if_eq in B. subst.  
    omega.
Qed.
Next Obligation.
  destruct ge; simpl in *.
  pose proof (build_capability_inv genv_next0 g0) as [B [S [Size [C G]]]].
  rewrite ZTree.gsspec in H0.
  remember (build_capability genv_next0 g0) as c.
  apply build_capability_inv_lt in Heqc as LT.
  destruct c,o;[|easy..]. simpl in *.
  destruct ZTree.elt_eq;inv H0.
  - unfold cap_to_Z_lo in e.
    unfold get_region_size_nat,get_region_size in Size.
    simpl in *. rewrite e.
    pose proof (globdef_size_pos g).
    omega.
  - apply genv_defs_range0 in H2.
    apply Ptrofs.same_if_eq in B.
    apply Ptrofs.same_if_eq in S;subst.
    omega.
Qed.
Next Obligation.
  destruct ge; simpl in *.
  rewrite PTree.gsspec in H0. rewrite PTree.gsspec in H1.
  pose proof (build_capability_inv genv_next0 g) as [B [S [Size [C G]]]].
  remember (build_capability genv_next0 g) as c.
  apply build_capability_inv_lt in Heqc as LT.
  apply Ptrofs.same_if_eq in S.
  apply Ptrofs.same_if_eq in B.
  destruct (peq id1 i); destruct (peq id2 i).
  - congruence.
  - inversion H0. subst c. apply genv_symb_range0 in H1 as ?.
    rewrite S in *. rewrite B in *. rewrite H3 in *.
    rewrite S in H2. omega.
  - inversion H1. subst c. apply genv_symb_range0 in H0 as ?.
    rewrite <- B, H3 in H2. omega.
  - eauto.
Qed.
Next Obligation.
  destruct ge;simpl in *.
  pose proof (build_capability_inv genv_next0 g) as [B [S [Size [C G]]]].
  remember (build_capability genv_next0 g) as c.
  apply build_capability_inv_lt in Heqc as LT.
  destruct c,o;[|easy..]. simpl in *.
  apply Ptrofs.same_if_eq in B.
  apply Ptrofs.same_if_eq in S;subst.
  omega.
Qed.

Definition add_globals (ge: option t) (gl: list (ident * globdef F V)) : option t :=
  List.fold_left (fun ge gl => (ge >>= add_global gl)) gl ge.

Lemma add_globals_app:
  forall gl2 gl1 ge,
    add_globals ge (gl1 ++ gl2) = do X <- (add_globals ge gl1); add_globals (Some X) gl2.
Proof.
  intros. unfold add_globals.
  generalize dependent ge.
  induction gl1;intros.
  - destruct ge;simpl;auto.
    induction gl2;auto.
  - simpl. apply IHgl1.
Qed.

Lemma add_globals_nil:
  forall go, add_globals go nil = go.
Proof.
  unfold add_globals. simpl. auto.
Qed.

Lemma add_globals_none:
  forall gls, add_globals None gls = None.
Proof.
  induction 0;auto.
Qed.

Program Definition add_stack (ge: t): option t :=
  let cap := build_stack_capability ge.(genv_next) in
  if zlt (Ptrofs.unsigned (get_hi cap)) (Ptrofs.unsigned ge.(genv_end)) then
    Some (@mkgenv
      ge.(genv_public)
      ge.(genv_symb)
      ge.(genv_defs)
      ge.(genv_heaps)
      (Some cap)
      (get_hi cap)
      ge.(genv_start)
      ge.(genv_end)
      ge.(genv_policy)
      _ _ _ _)
  else None.
Next Obligation.
  remember (build_stack_capability (genv_next ge)) as cap.
  pose proof (build_stack_capability_inv (genv_next ge)) as [B [LE [Size S]]].
  rewrite <- Heqcap in *.
  destruct cap,o;[clear S|easy..].
  unfold get_region_size in Size. simpl in *.
  apply (ge.(genv_symb_range)) in H0.
  apply Ptrofs.same_if_eq in B. subst.
  omega.
Defined.
Next Obligation.
  remember (build_stack_capability (genv_next ge)) as cap.
  pose proof (build_stack_capability_inv (genv_next ge)) as [B [LE [Size S]]].
  rewrite <- Heqcap in *.
  destruct cap,o;[clear S|easy..].
  unfold get_region_size in Size. simpl in *.
  apply (ge.(genv_defs_range)) in H0.
  apply Ptrofs.same_if_eq in B. subst.
  omega.
Defined.
Next Obligation.
  remember (build_stack_capability (genv_next ge)) as cap.
  pose proof (build_stack_capability_inv (genv_next ge)) as [B [LE [Size S]]].
  rewrite <- Heqcap in *.
  destruct cap,o;[clear S|easy..].
  unfold get_region_size in Size. simpl in *.
  eapply (ge.(genv_vars_inj)) in H0;[|apply H1].
  auto.
Defined.
Next Obligation.
  split;auto.
  remember (build_stack_capability (genv_next ge)) as cap.
  pose proof (build_stack_capability_inv (genv_next ge)) as [B [LE [Size S]]].
  rewrite <- Heqcap in *.
  destruct cap,o;[clear S|easy..].
  unfold get_region_size in Size. simpl in *.
  pose proof (ge.(genv_next_in_bounds)) as LE'. 
  apply Ptrofs.same_if_eq in B. subst. omega.
Defined.

Program Definition add_heap (c: compartment) (ge: t): option t :=
  let cap := build_heap_capability ge.(genv_next) in
  if zlt (Ptrofs.unsigned (get_hi cap)) (Ptrofs.unsigned ge.(genv_end)) then
    Some (@mkgenv
      ge.(genv_public)
      ge.(genv_symb)
      ge.(genv_defs)
      (PTree.set c cap ge.(genv_heaps))
      ge.(genv_stack)
      (get_hi cap)
      ge.(genv_start)
      ge.(genv_end)
      ge.(genv_policy)
      _ _ _ _)
  else None.
Next Obligation.
  remember (build_heap_capability (genv_next ge)) as cap.
  pose proof (build_heap_capability_inv (genv_next ge)) as [B [LE [Size S]]].
  rewrite <- Heqcap in *.
  destruct cap,o;[clear S|easy..].
  unfold get_region_size in Size. simpl in *.
  apply (ge.(genv_symb_range)) in H0.
  apply Ptrofs.same_if_eq in B. subst.
  omega.
Defined.
Next Obligation.
  remember (build_heap_capability (genv_next ge)) as cap.
  pose proof (build_heap_capability_inv (genv_next ge)) as [B [LE [Size S]]].
  rewrite <- Heqcap in *.
  destruct cap,o;[clear S|easy..].
  unfold get_region_size in Size. simpl in *.
  apply (ge.(genv_defs_range)) in H0.
  apply Ptrofs.same_if_eq in B. subst.
  omega.
Defined.
Next Obligation.
  remember (build_heap_capability (genv_next ge)) as cap.
  pose proof (build_heap_capability_inv (genv_next ge)) as [B [LE [Size S]]].
  rewrite <- Heqcap in *.
  destruct cap,o;[clear S|easy..].
  unfold get_region_size in Size. simpl in *.
  eapply (ge.(genv_vars_inj)) in H0;[|apply H1].
  auto.
Defined.
Next Obligation.
  split;auto.
  remember (build_heap_capability (genv_next ge)) as cap.
  pose proof (build_heap_capability_inv (genv_next ge)) as [B [LE [Size S]]].
  rewrite <- Heqcap in *.
  destruct cap,o;[clear S|easy..].
  unfold get_region_size in Size. simpl in *.
  pose proof (ge.(genv_next_in_bounds)) as LE'. 
  apply Ptrofs.same_if_eq in B. subst. omega.
Defined.

Definition comp_has_heap (ge: t) (c: compartment) : Prop :=
  match PTree.get c ge.(genv_heaps) with
  | Some h => True
  | None => False
  end.
Lemma comp_has_heap_dec: forall ge c, {comp_has_heap ge c} + {~ comp_has_heap ge c}.
Proof.
  intros. unfold comp_has_heap.
  destruct (PTree.get c ge.(genv_heaps));auto.
Defined.

Definition comp_of_gl (gl: globdef F V) : compartment :=
  match gl with
  | Gfun f => comp_of f
  | Gvar g => gvar_comp g
  end.

Fixpoint add_heaps (ge: option t) (gl: list (ident * globdef F V)) : option t :=
  List.fold_left (fun ge gl => (do X <- ge; if comp_has_heap_dec X (comp_of gl#2) then Some X else add_heap (comp_of gl#2) X)) gl ge.

Program Definition empty_genv (pub: list ident) (pol: Policy.t) (gstart gend: ptrofs) {region_wf: Ptrofs.unsigned gstart < Ptrofs.unsigned gend}: t :=
  @mkgenv pub
          (PTree.empty _)
          (PTree.empty _)
          (PTree.empty _)
          None
          gstart
          gstart
          gend
          pol
          _ _ _ _.
Next Obligation.
  rewrite PTree.gempty in H. discriminate.
Qed.
Next Obligation.
  rewrite ZTree.gempty in H. discriminate.
Qed.
Next Obligation.
  rewrite PTree.gempty in H. discriminate.
Qed.
Next Obligation.
  omega.
Qed.

Program Definition globalenv (p: program F V) (gstart gend: ptrofs) :=
  if zlt (Ptrofs.unsigned gstart) (Ptrofs.unsigned gend) then 
    add_globals (Some (@empty_genv p.(prog_public) p.(prog_pol) gstart gend _)) p.(prog_defs)
  else None.

(** Proof principles *)

Section GLOBALENV_PRINCIPLES.

Variable P: t -> Prop.

Lemma add_globals_preserves:
  forall gl ge,
  (forall ge id g, P ge -> In (id, g) gl -> option_urel P (add_global (id, g) ge)) ->
  option_urel P ge -> option_urel P (add_globals ge gl).
Proof.
  generalize dependent ge.
  induction gl; simpl; intros;auto.
  destruct a. inv H0.
  - simpl. rewrite add_globals_none.
    constructor.
  - simpl.
    assert (option_urel P (add_global (i, g) x)) as P';auto.
Qed.

Lemma add_globals_ensures:
  forall id g gl ge,
  (forall ge id g, P ge -> In (id, g) gl -> option_urel P (add_global (id, g) ge)) ->
  (forall ge, option_urel P (add_global (id, g) ge)) ->
  In (id, g) gl -> option_urel P (add_globals ge gl).
Proof.
  induction gl; simpl; intros.
  contradiction.
  destruct H1.
  - subst a. apply add_globals_preserves; auto.
    destruct ge;simpl;[|constructor].
    auto.
  - apply IHgl; auto.
Qed.

Lemma add_globals_unique_preserves:
  forall id gl ge,
  (forall ge id1 g, P ge -> In (id1, g) gl -> id1 <> id -> option_urel P (add_global (id1, g) ge)) ->
  ~In id (map fst gl) -> option_urel P ge -> option_urel P (add_globals ge gl).
Proof.
  induction gl; simpl; intros.
  auto.
  destruct a. apply IHgl; auto.
  inv H1;simpl;auto. constructor.
Qed.

Lemma add_globals_unique_ensures:
  forall gl1 id g gl2 ge,
  (forall ge id1 g1, P ge -> In (id1, g1) gl2 -> id1 <> id -> option_urel P (add_global (id1, g1) ge)) ->
  (forall ge, option_urel P (add_global (id, g) ge)) ->
  ~In id (map fst gl2) -> option_urel P (add_globals ge (gl1 ++ (id, g) :: gl2)).
Proof.
  intros. rewrite add_globals_app.
  simpl. remember (add_globals ge gl1) as x1.
  destruct x1;simpl;[|constructor].
  specialize H0 with t0.
  inv H0.
  - rewrite add_globals_none. constructor.
  - apply add_globals_preserves;auto.
    + intros. apply H;auto.
      intros Hcontr. subst.
      apply H1. apply in_map_iff. exists (id,g0);auto.
    + constructor;auto.
Qed.

Remark in_norepet_unique:
  forall id g (gl: list (ident * globdef F V)),
  In (id, g) gl -> list_norepet (map fst gl) ->
  exists gl1 gl2, gl = gl1 ++ (id, g) :: gl2 /\ ~In id (map fst gl2).
Proof.
  induction gl as [|[id1 g1] gl]; simpl; intros.
  contradiction.
  inv H0. destruct H.
  inv H. exists nil, gl. auto.
  exploit IHgl; eauto. intros (gl1 & gl2 & X & Y).
  exists ((id1, g1) :: gl1), gl2; split; auto. rewrite X; auto.
Qed.

Lemma add_globals_norepet_ensures:
  forall id g gl ge,
  (forall ge id1 g1, P ge -> In (id1, g1) gl -> id1 <> id -> option_urel P (add_global (id1, g1) ge)) ->
  (forall ge, option_urel P (add_global (id, g) ge)) ->
  In (id, g) gl -> list_norepet (map fst gl) -> option_urel P (add_globals ge gl).
Proof.
  intros. exploit in_norepet_unique; eauto. intros (gl1 & gl2 & X & Y).
  subst gl. apply add_globals_unique_ensures; auto. intros. eapply H; eauto.
  apply in_or_app; simpl; auto.
Qed.

End GLOBALENV_PRINCIPLES.

(** ** Properties of the operations over global environments *)

Theorem public_symbol_exists:
  forall ge id, public_symbol ge id = true -> exists b, find_symbol ge id = Some b.
Proof.
  unfold public_symbol; intros. destruct (find_symbol ge id) as [b|].
  exists b; auto.
  discriminate.
Qed.

(* ALG: do the following still hold? Not sure, address manipulation on capabilities is partial *)
(* Theorem shift_symbol_address: *)
(*   forall ge id ofs delta, *)
(*   symbol_address ge id (Ptrofs.add ofs delta) = Val.offset_ptr (symbol_address ge id ofs) delta. *)
(* Proof. *)
(*   intros. unfold symbol_address, Val.offset_ptr. destruct (find_symbol ge id); auto. *)
(* Qed. *)

(* Theorem shift_symbol_address_32: *)
(*   forall ge id ofs n, *)
(*   Archi.ptr64 = false -> *)
(*   symbol_address ge id (Ptrofs.add ofs (Ptrofs.of_int n)) = Val.add (symbol_address ge id ofs) (Vint n). *)
(* Proof. *)
(*   intros. unfold symbol_address. destruct (find_symbol ge id). *)
(* - unfold Val.add. rewrite H. auto. *)
(* - auto. *)
(* Qed. *)

(* Theorem shift_symbol_address_64: *)
(*   forall ge id ofs n, *)
(*   Archi.ptr64 = true -> *)
(*   symbol_address ge id (Ptrofs.add ofs (Ptrofs.of_int64 n)) = Val.addl (symbol_address ge id ofs) (Vlong n). *)
(* Proof. *)
(*   intros. unfold symbol_address. destruct (find_symbol ge id). *)
(* - unfold Val.addl. rewrite H. auto. *)
(* - auto. *)
(* Qed. *)

Theorem find_funct_inv:
  forall ge v f,
  find_funct ge v = Some f -> exists p l b e a, v = OCVcap (OCsealable (OCVmem p l b e a)).
Proof.
  intros until f; unfold find_funct.
  destruct v; try congruence.
  destruct Ptrofs.eq_dec,is_mem_cap_b eqn:Hb;simpl;try congruence.
  destruct o,o;try easy.
  intros. exists p, l, i, i0, i1. auto.
Qed.

Theorem find_funct_find_funct_ptr:
  forall ge p l b e,
  find_funct ge (OCVcap (OCsealable (OCVmem p l b e b))) = find_funct_ptr ge (OCsealable (OCVmem p l b e b)).
Proof.
  intros; simpl.
  rewrite andb_true_r. simpl.
  unfold proj_sumbool.
  rewrite pred_dec_true;auto.
Qed.

Theorem find_funct_ptr_iff:
  forall ge b f,
  find_funct_ptr ge b = Some f <->
  find_def ge b = Some (Gfun f).
Proof.
  intros. unfold find_funct_ptr.
  destruct (find_def ge b) as [[f1|v1]|]; intuition congruence.
Qed.

Theorem find_var_info_iff:
  forall ge b v,
  find_var_info ge b = Some v <->
  find_def ge b = Some (Gvar v).
Proof.
  intros. unfold find_var_info.
  destruct (find_def ge b) as [[f1|v1]|]; intuition congruence.
Qed.

Theorem find_def_symbol:
  forall p gstart gend id g,
    (prog_defmap p)!id = Some g <-> exists b, option_urel (fun x => find_symbol x id = Some b) (globalenv p gstart gend) /\
                                       option_urel (fun x => find_def x b = Some g) (globalenv p gstart gend).
Proof.
  (* intros. *)
(*   set (P := fun m ge => m!id = Some g <-> exists b, find_symbol ge id = Some b /\ find_def ge b = Some g). *)
(*   assert (REC: forall l m ge, *)
(*             P m ge -> *)
(*             P (fold_left (fun m idg => PTree.set idg#1 idg#2 m) l m) *)
(*               (add_globals ge l)). *)
(*   { induction l as [ | [id1 g1] l]; intros; simpl. *)
(*   - auto. *)
(*   - apply IHl. unfold P, add_global, find_symbol, find_def; simpl. *)
(*     rewrite ! PTree.gsspec. destruct (peq id id1). *)
(*     + subst id1. split; intros. *)
(*       inv H0. exists (genv_next ge); split; auto. apply PTree.gss. *)
(*       destruct H0 as (b & A & B). inv A. rewrite PTree.gss in B. auto. *)
(*     + red in H; rewrite H. split. *)
(*       intros (b & A & B). exists b; split; auto. rewrite PTree.gso; auto. *)
(*       apply Plt_ne. eapply genv_symb_range; eauto. *)
(*       intros (b & A & B). rewrite PTree.gso in B. exists b; auto. *)
(*       apply Plt_ne. eapply genv_symb_range; eauto. *)
(*   } *)
(*   apply REC. unfold P, find_symbol, find_def; simpl. *)
(*   rewrite ! PTree.gempty. split. *)
(*   congruence. *)
(*   intros (b & A & B); congruence. *)
  (* Qed. *)
Admitted.

Theorem find_symbol_add_global_ne:
  forall ge id b i c, find_symbol ge id = Some b ->
                 i <> id ->
                option_urel (fun x => find_symbol x id = Some b) (add_global (i,c) ge).
Proof.
  intros until c.
  intros S n.
  destruct (add_global (i,c) ge) eqn:Hg;[|constructor].
  constructor. unfold find_symbol in *.
  unfold add_global in Hg.
  destruct zlt;inv Hg.
  simpl in *.
  rewrite PTree.gso;auto.
Qed.

Theorem find_symbol_add_globals_ne:
  forall ge id b gls, find_symbol ge id = Some b ->
                 ~ In id (map fst gls) ->
                 option_urel (fun x => find_symbol x id = Some b) (add_globals (Some ge) gls).
Proof.
  intros until gls.
  intros S n.
  generalize dependent ge.
  generalize dependent b.
  induction gls;simpl;intros.
  - constructor. auto.
  - destruct a. apply not_in_cons in n as [ne n].
    apply find_symbol_add_global_ne with (i:=i) (c:=g) in S;auto.
    inv S.
    + rewrite add_globals_none. constructor.
    + eapply IHgls in n;eauto.
Qed.

Theorem find_symbol_add_global:
  forall ge i c, option_urel (fun x => find_symbol x i = Some (build_capability (genv_next ge) c)) (add_global (i,c) ge).
Proof.
  intros until c.
  destruct (add_global (i,c) ge) eqn:Hg;[|constructor].
  constructor. unfold find_symbol in *.
  unfold add_global in Hg.
  destruct zlt;inv Hg.
  simpl in *.
  rewrite PTree.gss;auto.
Qed.


Theorem find_symbol_exists:
  forall p id g gend gstart,
  In (id, g) (prog_defs p) ->
  exists b, option_urel (fun x => find_symbol x id = Some b) (globalenv p gstart gend).
Proof.
  intros. unfold globalenv.
  destruct zlt;[|exists OCVnullmemcap;constructor].
  remember (add_globals (Some (empty_genv (prog_public p) (prog_pol p) gstart gend)) (prog_defs p)).
  destruct o;[|exists OCVnullmemcap;constructor].
  destruct p;simpl in *.
  generalize dependent t0.
  induction prog_defs using rev_ind;try easy;simpl in *;intros.
  apply in_app_or in H.
  destruct H as [Hin | [Heq | HH]];[..|inv HH].
  - destruct (add_globals (Some (empty_genv prog_public prog_pol gstart gend)) prog_defs) eqn:Heq.
    + rewrite add_globals_app in Heqo. rewrite Heq in Heqo.
      simpl in Heqo. 
      eapply IHprog_defs with t1 in Hin as [b Hb];eauto.
      exists b. constructor. admit.
    + rewrite add_globals_app in Heqo. rewrite Heq in Heqo.
      simpl in Heqo. congruence.
  - admit.
Admitted.

Theorem find_symbol_inversion : forall p gstart gend x b t0,
    globalenv p gstart gend = Some t0 ->
    find_symbol t0 x = Some b ->
    In x (prog_defs_names p).
Proof.
  intros until t0; unfold globalenv. intros Heq.
  destruct zlt;[|easy].
(*   eapply add_globals_preserves. *)
(* (* preserves *) *)
(*   unfold find_symbol; simpl; intros. rewrite PTree.gsspec in H1. *)
(*   destruct (peq x id). subst x. change id with (fst (id, g)). apply List.in_map; auto. *)
(*   auto. *)
(* (* base *) *)
(*   unfold find_symbol; simpl; intros. rewrite PTree.gempty in H. discriminate. *)
  (* Qed. *)
Admitted.

Theorem find_symbol_find_def_inversion : forall p gstart gend x b t0,
    globalenv p gstart gend = Some t0 ->
    find_symbol t0 x = Some b ->
    exists g, find_def t0 b = Some g.
Proof.
  intros until b. unfold globalenv. (* eapply add_globals_preserves. *)
(*   - unfold find_symbol, find_def, add_global. simpl. *)
(*     intros ge id g IH IN SYMBOL. *)
(*     destruct (Pos.eq_dec id x) as [->|neq]. *)
(*     + rewrite PTree.gss in SYMBOL. injection SYMBOL as <-. *)
(*       rewrite PTree.gss. eauto. *)
(*     + rewrite PTree.gso in SYMBOL; eauto. *)
(*       destruct IH as [g' IH]; eauto. *)
(*       pose proof (genv_defs_range _ _ IH) as FRESH. *)
(*       rewrite PTree.gso; eauto. *)
(*       now apply Plt_ne. *)
(*   - unfold find_symbol. simpl. now rewrite PTree.gempty. *)
  (* Qed. *)
Admitted.

(* TODO: state following missing theorems *)
(*
Theorem find_def_inversion:
  forall p b g,
  find_def (globalenv p) b = Some g ->
  exists id, In (id, g) (prog_defs p).
Proof.
  intros until g. unfold globalenv. apply add_globals_preserves.
(* preserves *)
  unfold find_def; simpl; intros.
  rewrite PTree.gsspec in H1. destruct (peq b (genv_next ge)).
  inv H1. exists id; auto.
  auto.
(* base *)
  unfold find_def; simpl; intros. rewrite PTree.gempty in H. discriminate.
Qed.

Corollary find_funct_ptr_inversion:
  forall p b f,
  find_funct_ptr (globalenv p) b = Some f ->
  exists id, In (id, Gfun f) (prog_defs p).
Proof.
  intros. apply find_def_inversion with b. apply find_funct_ptr_iff; auto.
Qed.

Corollary find_funct_inversion:
  forall p v f,
  find_funct (globalenv p) v = Some f ->
  exists id, In (id, Gfun f) (prog_defs p).
Proof.
  intros. exploit find_funct_inv; eauto. intros [b EQ]. subst v.
  rewrite find_funct_find_funct_ptr in H.
  eapply find_funct_ptr_inversion; eauto.
Qed.

Theorem find_funct_ptr_prop:
  forall (P: F -> Prop) p b f,
  (forall id f, In (id, Gfun f) (prog_defs p) -> P f) ->
  find_funct_ptr (globalenv p) b = Some f ->
  P f.
Proof.
  intros. exploit find_funct_ptr_inversion; eauto. intros [id IN]. eauto.
Qed.

Theorem find_funct_prop:
  forall (P: F -> Prop) p v f,
  (forall id f, In (id, Gfun f) (prog_defs p) -> P f) ->
  find_funct (globalenv p) v = Some f ->
  P f.
Proof.
  intros. exploit find_funct_inversion; eauto. intros [id IN]. eauto.
Qed.

Theorem global_addresses_distinct:
  forall ge id1 id2 b1 b2,
  id1 <> id2 ->
  find_symbol ge id1 = Some b1 ->
  find_symbol ge id2 = Some b2 ->
  b1 <> b2.
Proof.
  intros. red; intros; subst. elim H. destruct ge. eauto.
Qed.
*)

Theorem invert_find_symbol:
  forall ge id b,
  invert_symbol ge b = Some id -> find_symbol ge id = Some b.
Proof.
  intros until b; unfold find_symbol, invert_symbol.
  apply PTree_Properties.fold_rec.
  intros. rewrite H in H0; auto.
  congruence.
  intros. destruct occap_dec.
  - inv H2. apply PTree.gss.
  - subst. assert (m!id = Some b);auto.
    rewrite PTree.gso;[|intros;subst;congruence].
    auto.
Qed.

Theorem find_invert_symbol:
  forall ge id b,
  find_symbol ge id = Some b -> invert_symbol ge b = Some id.
Proof.
  intros until b.
  assert (find_symbol ge id = Some b -> exists id', invert_symbol ge b = Some id').
  unfold find_symbol, invert_symbol.
  apply PTree_Properties.fold_rec.
  intros. rewrite H in H0; auto.
  rewrite PTree.gempty; congruence.
  intros. destruct (occap_dec b v). exists k; auto.
  rewrite PTree.gsspec in H2. destruct (peq id k).
  inv H2. congruence. auto.

  intros; exploit H; eauto. intros [id' A].
  assert (id = id'). eapply genv_vars_inj; eauto. apply invert_find_symbol; auto.
  congruence.
Qed.

(*
Definition advance_next (gl: list (ident * globdef F V)) (x: positive) :=
  List.fold_left (fun n g => Pos.succ n) gl x.

Remark genv_next_add_globals:
  forall gl ge,
  genv_next (add_globals ge gl) = advance_next gl (genv_next ge).
Proof.
  induction gl; simpl; intros.
  auto.
  rewrite IHgl. auto.
Qed.

Remark genv_public_add_globals:
  forall gl ge,
  genv_public (add_globals ge gl) = genv_public ge.
Proof.
  induction gl; simpl; intros.
  auto.
  rewrite IHgl; auto.
Qed.

Remark genv_pol_add_globals:
  forall gl ge,
  genv_policy (add_globals ge gl) = genv_policy ge.
Proof.
  induction gl; simpl; intros.
  auto.
  rewrite IHgl; auto.
Qed.

Theorem globalenv_public:
  forall p, genv_public (globalenv p) = prog_public p.
Proof.
  unfold globalenv; intros. rewrite genv_public_add_globals. auto.
Qed.

Theorem block_is_volatile_below:
  forall ge b, block_is_volatile ge b = true ->  Plt b ge.(genv_next).
Proof.
  unfold block_is_volatile; intros. destruct (find_var_info ge b) as [[c gv]|] eqn:FV.
  rewrite find_var_info_iff in FV. eapply genv_defs_range; eauto.
  discriminate.
Qed.
*)
(** ** Coercing a global environment into a symbol environment *)

Program Definition to_senv (ge: t) : Senv.t :=
 @Senv.mksenv
    (find_symbol ge)
    (public_symbol ge)
    (invert_symbol ge)
    (block_is_volatile ge)
    ge.(genv_next)
    ge.(genv_start)
    ge.(genv_end)
    ge.(genv_vars_inj)
    (invert_find_symbol ge)
    (find_invert_symbol ge)
    (public_symbol_exists ge).

(** * Construction of the initial memory state *)

Section INITMEM.

Variable ge: t.

(** * Construction of the globals *)

Definition store_init_data (m: mem) (c: occap) (p: Z) (id: init_data) (cp: compartment) : occap * mem + error_kind :=
  match id with
  | Init_int8 n => Mem.store DEFAULT CMint8unsigned m c p (OCVint n) cp
  | Init_int16 n => Mem.store DEFAULT CMint16unsigned m c p (OCVint n) cp
  | Init_int32 n => Mem.store DEFAULT CMint32 m c p (OCVint n) cp
  | Init_int64 n => Mem.store DEFAULT CMint64 m c p (OCVlong n) cp
  | Init_float32 n => Mem.store DEFAULT CMfloat32 m c p (OCVsingle n) cp
  | Init_float64 n => Mem.store DEFAULT CMfloat64 m c p (OCVfloat n) cp
  | Init_addrof symb ofs =>
      match find_symbol ge symb with
      | None => inr PtrErr
      | Some c' => if Ptrofs.unsigned ofs =? 0 then
                    Mem.store DEFAULT CMcap m c p (OCVcap c') cp
                  else
                    match Val.offset_cap c' ofs with
                    | None => inr CapErr (* the capability is sealed and cannot have altered address *)
                    | Some c'' => Mem.store DEFAULT CMcap m c p (OCVcap c'') cp
                    end
      end
  | Init_space n => inl (c,m)
  end.

Fixpoint store_init_data_list (m: mem) (c: occap) (p: Z) (idl: list init_data)
                              (cp : compartment)
                              {struct idl}: mem + error_kind :=
  match idl with
  | nil => inl m
  | id :: idl' =>
      match store_init_data m c p id cp with
      | inr err => inr err
      | inl (_,m') => store_init_data_list m' c (p + cap_init_data_size id) idl' cp
      end
  end.

Definition perm_globvar (gv: globvar V) : permission :=
  if gv.(gvar_volatile) then Nonempty
  else if gv.(gvar_readonly) then Readable
  else Writable.

Definition alloc_global (m: mem) (idg: ident * globdef F V): option mem :=
  match idg with
  | (id, Gfun f) =>
      match find_symbol ge id with
      | None => None
      | Some cap =>
          let m1 := Mem.init m (comp_of f) cap in
          match Mem.drop_perm m1 cap Nonempty (comp_of f) with
          | inl m2 => Some m2
          | inr _ => None
          end
      end
  | (id, Gvar v) =>
      let init := v.(gvar_init) in
      let comp := v.(gvar_comp) in
      (* let cap  := lib.(genv_symb) ! id in *)
      match find_symbol ge id with
      | None => None
      | Some cap =>
          let m1 := Mem.init m comp cap in
          match store_zeros m1 cap 0 comp with
          | inr err => None
          | inl (_,m2) =>
              match store_init_data_list m2 cap 0 init comp with
              | inr err => None
              | inl m3 => match Mem.drop_perm m3 cap (perm_globvar v) comp with
                         | inr _ => None
                         | inl m2 => Some m2
                         end
              end
          end
      end
  end.

Fixpoint alloc_globals (m: mem) (gl: list (ident * globdef F V))
                       {struct gl} : option mem :=
  match gl with
  | nil => Some m
  | g :: gl' =>
      match alloc_global m g with
      | None => None
      | Some m' => alloc_globals m' gl'
      end
  end.

Lemma alloc_globals_app : forall gl1 gl2 m m1,
  alloc_globals m gl1 = Some m1 ->
  alloc_globals m1 gl2 = alloc_globals m (gl1 ++ gl2).
Proof.
  induction gl1.
  simpl. intros.  inversion H; subst. auto.
  simpl. intros. destruct (alloc_global m a); eauto. inversion H.
Qed.

(** Next-block properties *)

(* ALG: TODO *)
(*Remark store_zeros_nextblock:
  forall m b p n cp m', store_zeros m b p n cp = Some m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  intros until cp. functional induction (store_zeros m b p n cp); intros.
  inv H; auto.
  rewrite IHo; eauto with mem.
  congruence.
Qed.

Remark store_init_data_list_nextblock:
  forall idl b m p cp m',
  store_init_data_list m b p idl cp = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction idl; simpl; intros until m'.
  intros. congruence.
  caseEq (store_init_data m b p a cp); try congruence. intros.
  transitivity (Mem.nextblock m0). eauto.
  destruct a; simpl in H; try (eapply Mem.nextblock_store; eauto; fail).
  congruence.
  destruct (find_symbol ge i); try congruence. eapply Mem.nextblock_store; eauto.
Qed.

Remark alloc_global_nextblock:
  forall g m m',
  alloc_global m g = Some m' ->
  Mem.nextblock m' = Pos.succ(Mem.nextblock m).
Proof.
  unfold alloc_global. intros.
  destruct g as [id [f|v]].
- (* function *)
  destruct (Mem.alloc m _ 0 1) as [m1 b] eqn:?.
  erewrite Mem.nextblock_drop; eauto.
  now erewrite Mem.nextblock_alloc; eauto.
- (* variable *)
  set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m _ 0 sz) as [m1 b] eqn:?.
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list m2 b 0 init) as [m3|] eqn:?; try discriminate.
  erewrite Mem.nextblock_drop; eauto.
  erewrite store_init_data_list_nextblock; eauto.
  erewrite store_zeros_nextblock; eauto.
  erewrite Mem.nextblock_alloc; eauto.
Qed.

Remark alloc_globals_nextblock:
  forall gl m m',
  alloc_globals m gl = Some m' ->
  Mem.nextblock m' = advance_next gl (Mem.nextblock m).
Proof.
  induction gl; simpl; intros.
  congruence.
  destruct (alloc_global m a) as [m1|] eqn:?; try discriminate.
  erewrite IHgl; eauto. erewrite alloc_global_nextblock; eauto.
Qed.*)

(** Block compartments *)

(* ALG: TODO *)
(*Remark store_zeros_block_compartment:
  forall m b p n cp m', store_zeros m b p n cp = Some m' ->
  forall b', Mem.block_compartment m' b' = Mem.block_compartment m b'.
Proof.
  intros m b p n cp.
  functional induction (store_zeros m b p n cp)
    as [|m b p n cp ? ? m' STORE IH|]; try congruence.
  intros m'' STOREZEROS b'.
  rewrite (IH _ STOREZEROS).
  erewrite Mem.store_block_compartment; eauto.
Qed.

Remark store_init_data_block_compartment:
  forall m b p id cp m',
  store_init_data m b p id cp = Some m' ->
  forall b', Mem.block_compartment m' b' = Mem.block_compartment m b'.
Proof.
  intros m b p id cp m'.
  destruct id as [?|?|?|?|?|?|?|id off]; simpl;
  try apply Mem.store_block_compartment.
  - congruence.
  - destruct find_symbol; try congruence.
    apply Mem.store_block_compartment.
Qed.

Remark store_init_data_list_block_compartment:
  forall m b p idl cp m',
  store_init_data_list m b p idl cp = Some m' ->
  forall b', Mem.block_compartment m' b' = Mem.block_compartment m b'.
Proof.
  intros m b p idl cp. revert m p.
  induction idl as [|id idl IH]; intros m p; simpl.
  - congruence.
  - intros m'.
    destruct store_init_data as [m''|] eqn:INITDATA; try congruence.
    intros INITDATALIST b'. rewrite (IH _ _ _ INITDATALIST).
    eapply store_init_data_block_compartment; eauto.
Qed.

Remark alloc_global_block_compartment:
  forall m idg m' b,
  alloc_global m idg = Some m' ->
  Mem.block_compartment m' b =
  if eq_block b (Mem.nextblock m) then Some (comp_of idg#2)
  else Mem.block_compartment m b.
Proof.
intros m [id [v|f]] m' b ALLOCGLOB; simpl in *.
- destruct (Mem.alloc _ _ _ _) as [m'' b'] eqn:ALLOC.
  erewrite Mem.drop_block_compartment; eauto.
  erewrite Mem.alloc_block_compartment; eauto.
  erewrite <- Mem.alloc_result; eauto.
- destruct (Mem.alloc _ _ _ _) as [m0 b0] eqn:ALLOC.
  destruct store_zeros as [m1|] eqn:STOREZEROS; try congruence.
  destruct store_init_data_list as [m2|] eqn:INITDATALIST; try congruence.
  erewrite Mem.drop_block_compartment; eauto.
  erewrite store_init_data_list_block_compartment; eauto.
  erewrite store_zeros_block_compartment; eauto.
  erewrite Mem.alloc_block_compartment; eauto.
  erewrite <- Mem.alloc_result; eauto.
Qed.

Fixpoint alloc_globals_block_compartment_spec
         dflt b0 (gl : list (ident * globdef F V)) b : option block :=
  match gl with
  | nil => dflt
  | g :: gl =>
    let dflt' := if eq_block b b0 then Some (comp_of g#2)
                 else dflt in
    alloc_globals_block_compartment_spec dflt' (Pos.succ b0) gl b
  end.

Remark alloc_globals_block_compartment:
  forall m gl m',
  alloc_globals m gl = Some m' ->
  forall b, Mem.block_compartment m' b =
  alloc_globals_block_compartment_spec
    (Mem.block_compartment m b) (Mem.nextblock m) gl b.
Proof.
intros m gl m' ALLOC b. revert m m' ALLOC.
induction gl as [|g gl IH]; simpl; try congruence.
intros m1 m3 ALLOCGLOBALS.
destruct alloc_global as [m2|] eqn:ALLOC; try congruence.
rewrite (IH _ _ ALLOCGLOBALS), (alloc_global_block_compartment _ _ _ ALLOC).
erewrite <- alloc_global_nextblock; eauto.
Qed.*)

(** Permissions *)

(* ALG: TODO *)
(*Remark store_zeros_perm:
  forall k prm b' q m b p n cp m',
  store_zeros m b p n cp = Some m' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  intros until cp. functional induction (store_zeros m b p n cp); intros.
  inv H; tauto.
  destruct (IHo _ H); intros. split; eauto with mem.
  congruence.
Qed.

Remark store_init_data_perm:
  forall k prm b' q i cp b m p m',
  store_init_data m b p i cp = Some m' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  intros.
  assert (forall chunk v,
          Mem.store chunk m b p v cp = Some m' ->
          (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm)).
    intros; split; eauto with mem.
  destruct i; simpl in H; eauto.
  inv H; tauto.
  destruct (find_symbol ge i); try discriminate. eauto.
Qed.

Remark store_init_data_list_perm:
  forall k prm b' q idl cp b m p m',
  store_init_data_list m b p idl cp = Some m' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  induction idl as [ | i1 idl]; simpl; intros.
- inv H; tauto.
- destruct (store_init_data m b p i1) as [m1|] eqn:S1; try discriminate.
  transitivity (Mem.perm m1 b' q k prm).
  eapply store_init_data_perm; eauto.
  eapply IHidl; eauto.
Qed.

Remark alloc_global_perm:
  forall k prm b' q idg m m',
  alloc_global m idg = Some m' ->
  Mem.valid_block m b' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  intros. destruct idg as [id [f|v]]; simpl in H.
- (* function *)
  destruct (Mem.alloc m _ 0 1) as [m1 b] eqn:?.
  assert (b' <> b). apply Mem.valid_not_valid_diff with m; eauto with mem.
  split; intros.
  eapply Mem.perm_drop_3; eauto. eapply Mem.perm_alloc_1; eauto.
  eapply Mem.perm_alloc_4; eauto. eapply Mem.perm_drop_4; eauto.
- (* variable *)
  set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m _ 0 sz) as [m1 b] eqn:?.
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list m2 b 0 init) as [m3|] eqn:?; try discriminate.
  assert (b' <> b). apply Mem.valid_not_valid_diff with m; eauto with mem.
  split; intros.
  eapply Mem.perm_drop_3; eauto.
  erewrite <- store_init_data_list_perm; [idtac|eauto].
  erewrite <- store_zeros_perm; [idtac|eauto].
  eapply Mem.perm_alloc_1; eauto.
  eapply Mem.perm_alloc_4; eauto.
  erewrite store_zeros_perm; [idtac|eauto].
  erewrite store_init_data_list_perm; [idtac|eauto].
  eapply Mem.perm_drop_4; eauto.
Qed.

Remark alloc_globals_perm:
  forall k prm b' q gl m m',
  alloc_globals m gl = Some m' ->
  Mem.valid_block m b' ->
  (Mem.perm m b' q k prm <-> Mem.perm m' b' q k prm).
Proof.
  induction gl.
  simpl; intros. inv H. tauto.
  simpl; intros. destruct (alloc_global m a) as [m1|] eqn:?; try discriminate.
  erewrite alloc_global_perm; eauto. eapply IHgl; eauto.
  unfold Mem.valid_block in *. erewrite alloc_global_nextblock; eauto.
  apply Plt_trans_succ; auto.
Qed. *)

(** Data preservation properties *)

(* ALG: TODO *)
(*Remark store_zeros_unchanged:
  forall (P: block -> Z -> Prop) m b p n cp m',
  store_zeros m b p n cp = Some m' ->
  (forall i, p <= i < p + n -> ~ P b i) ->
  Mem.unchanged_on P m m'.
Proof.
  intros until cp. functional induction (store_zeros m b p n cp); intros.
- inv H; apply Mem.unchanged_on_refl.
- apply Mem.unchanged_on_trans with m'.
+ eapply Mem.store_unchanged_on; eauto. simpl. intros. apply H0. omega.
+ apply IHo; auto. intros; apply H0; omega.
- discriminate.
Qed.

Remark store_init_data_unchanged:
  forall (P: block -> Z -> Prop) b i cp m p m',
  store_init_data m b p i cp = Some m' ->
  (forall ofs, p <= ofs < p + init_data_size i -> ~ P b ofs) ->
  Mem.unchanged_on P m m'.
Proof.
  intros. destruct i; simpl in *;
  try (eapply Mem.store_unchanged_on; eauto; fail).
  inv H; apply Mem.unchanged_on_refl.
  destruct (find_symbol ge i); try congruence.
  eapply Mem.store_unchanged_on; eauto;
  unfold Mptr; destruct Archi.ptr64; eauto.
Qed.

Remark store_init_data_list_unchanged:
  forall (P: block -> Z -> Prop) b il cp m p m',
  store_init_data_list m b p il cp = Some m' ->
  (forall ofs, p <= ofs -> ~ P b ofs) ->
  Mem.unchanged_on P m m'.
Proof.
  induction il; simpl; intros.
- inv H. apply Mem.unchanged_on_refl.
- destruct (store_init_data m b p a) as [m1|] eqn:?; try congruence.
  apply Mem.unchanged_on_trans with m1.
  eapply store_init_data_unchanged; eauto. intros; apply H0; tauto.
  eapply IHil; eauto. intros; apply H0. generalize (init_data_size_pos a); omega.
Qed.*)

(** Properties related to [loadbytes] *)

Definition readbytes_as_zero (m: mem) (cap: occap) (ofs len: Z) (cp: option compartment) : Prop :=
  forall p n,
  ofs <= p -> p + Z.of_nat n <= ofs + len ->
  Mem.loadbytes DEFAULT m cap p (Z.of_nat n) cp = inl (list_repeat n (Byte Byte.zero)).

(* ALG: TODO *)
(* Lemma store_zeros_loadbytes:
  forall m b p n cp m',
    Mem.can_access_block m b (Some cp) ->
  store_zeros m b p n cp = Some m' ->
  readbytes_as_zero m' b p n (Some cp) /\ Mem.can_access_block m' b (Some cp).
Proof.
  intros until cp.
  functional induction (store_zeros m b p n cp).
- split; [red|]; intros.
  destruct n0. simpl. apply Mem.loadbytes_empty. omega.
  inv H0; eauto.
  rewrite Nat2Z.inj_succ in H2. omegaContradiction.
  inv H0; eauto.
- split; [red|]; intros.
  destruct (zeq p0 p).
  + subst p0. destruct n0. simpl. apply Mem.loadbytes_empty. omega.
    eapply IHo in H0 as [? ?]; eauto.
    eapply Mem.store_can_access_block_2; eauto.
    rewrite Nat2Z.inj_succ in H2. rewrite Nat2Z.inj_succ.
    replace (Z.succ (Z.of_nat n0)) with (1 + Z.of_nat n0) by omega.
    change (list_repeat (S n0) (Byte Byte.zero))
      with ((Byte Byte.zero :: nil) ++ list_repeat n0 (Byte Byte.zero)).
    apply Mem.loadbytes_concat.
    eapply Mem.loadbytes_unchanged_on with (P := fun b1 ofs1 => ofs1 = p).
    eapply store_zeros_unchanged; eauto. intros; omega.
    intros; omega.
    replace (Byte Byte.zero :: nil) with (encode_val Mint8unsigned Vzero).
    change 1 with (size_chunk Mint8unsigned).
    eapply Mem.loadbytes_store_same; eauto.
    unfold encode_val; unfold encode_int; unfold rev_if_be; destruct Archi.big_endian; reflexivity.
    eapply IHo; eauto.
    eapply Mem.store_can_access_block_2; eauto.
    omega. omega. omega. omega.
  + eapply IHo; eauto.
    eapply Mem.store_can_access_block_2; eauto.
    omega. omega.
  + eapply IHo; eauto.
    eapply Mem.store_can_access_block_2; eauto.
- discriminate.
Qed. *)

Definition bytes_of_init_data (i: init_data): list memval :=
  match i with
  | Init_int8 n => inj_bytes (encode_int 1%nat (Int.unsigned n))
  | Init_int16 n => inj_bytes (encode_int 2%nat (Int.unsigned n))
  | Init_int32 n => inj_bytes (encode_int 4%nat (Int.unsigned n))
  | Init_int64 n => inj_bytes (encode_int 8%nat (Int64.unsigned n))
  | Init_float32 n => inj_bytes (encode_int 4%nat (Int.unsigned (Float32.to_bits n)))
  | Init_float64 n => inj_bytes (encode_int 8%nat (Int64.unsigned (Float.to_bits n)))
  | Init_space n => list_repeat (Z.to_nat n) (Byte Byte.zero)
  | Init_addrof id ofs =>
      match find_symbol ge id with
      | Some c => inj_value (if Archi.ptr64 then Q128 else Q64) (OCVcap c)
      | None   => list_repeat (if Archi.ptr64 then 16%nat else 8%nat) Undef
      end
  end.

Remark cap_init_data_size_addrof:
  forall id ofs, cap_init_data_size (Init_addrof id ofs) = size_chunk CMcap.
Proof.
  intros. unfold CMcap. simpl. destruct Archi.ptr64; auto.
Qed.

(* ALG: TODO *)
(*Lemma store_init_data_loadbytes:
  forall m b p i cp m',
  store_init_data m b p i cp = Some m' ->
  readbytes_as_zero m b p (init_data_size i) (Some cp) ->
  Mem.loadbytes m' b p (init_data_size i) (Some cp) = Some (bytes_of_init_data i).
Proof.
  intros; destruct i; simpl in H; try apply (Mem.loadbytes_store_same _ _ _ _ _ _ _ H).
- inv H. simpl.
  assert (EQ: Z.of_nat (Z.to_nat z) = Z.max z 0).
  { destruct (zle 0 z). rewrite Z2Nat.id; xomega. destruct z; try discriminate. simpl. xomega. }
  rewrite <- EQ. apply H0. omega. simpl. omega.
- rewrite init_data_size_addrof. simpl.
  destruct (find_symbol ge i) as [b'|]; try discriminate.
  rewrite (Mem.loadbytes_store_same _ _ _ _ _ _ _ H).
  unfold encode_val, Mptr; destruct Archi.ptr64; reflexivity.
Qed.*)

Fixpoint bytes_of_init_data_list (il: list init_data): list memval :=
  match il with
  | nil => nil
  | i :: il => bytes_of_init_data i ++ bytes_of_init_data_list il
  end.

(* ALG: TODO *)
(* Lemma store_init_data_list_loadbytes:
  forall b il m p cp m',
    Mem.can_access_block m b (Some cp) ->
  store_init_data_list m b p il cp = Some m' ->
  readbytes_as_zero m b p (init_data_list_size il) (Some cp) ->
  Mem.loadbytes m' b p (init_data_list_size il) (Some cp) = Some (bytes_of_init_data_list il).
Proof.
  induction il as [ | i1 il]; simpl; intros.
- apply Mem.loadbytes_empty. omega. inv H0; eauto.
- generalize (init_data_size_pos i1) (init_data_list_size_pos il); intros P1 PL.
  destruct (store_init_data m b p i1) as [m1|] eqn:S; try discriminate.
  apply Mem.loadbytes_concat.
  eapply Mem.loadbytes_unchanged_on with (P := fun b1 ofs1 => ofs1 < p + init_data_size i1).
  eapply store_init_data_list_unchanged; eauto.
  intros; omega.
  intros; omega.
  eapply store_init_data_loadbytes; eauto.
  red; intros; apply H1. omega. omega.
  apply IHil with m1; auto.
  unfold store_init_data in S; destruct i1; try now eapply Mem.store_can_access_block_2; eauto.
  inv S; eauto. destruct (find_symbol ge i); try discriminate.
  now eapply Mem.store_can_access_block_2; eauto.
  red; intros.
  eapply Mem.loadbytes_unchanged_on with (P := fun b1 ofs1 => p + init_data_size i1 <= ofs1).
  eapply store_init_data_unchanged; eauto.
  intros; omega.
  intros; omega.
  apply H1. omega. omega.
  auto. auto.
Qed. *)

(** Properties related to [load] *)

Definition read_as_zero (m: mem) (c: occap) (ofs len: Z) (cp: option compartment) : Prop :=
  forall chunk p,
  ofs <= p -> p + size_chunk chunk <= ofs + len ->
  (align_chunk chunk | p) ->
  Mem.load DEFAULT chunk m c p cp =
  inl (match chunk with
        | CMint8unsigned | CMint8signed | CMint16unsigned | CMint16signed | CMint32 => OCVint Int.zero
        | CMint64 => OCVlong Int64.zero
        | CMfloat32 => OCVsingle Float32.zero
        | CMfloat64 => OCVfloat Float.zero
        | CMany32 | CMany64 | CMany128 | CMcap64 | CMcap128 => OCVundef
        end).

(* ALG: TODO *)
(* Remark read_as_zero_unchanged:
  forall (P: block -> Z -> Prop) m b ofs len cp m',
  read_as_zero m b ofs len cp ->
  Mem.unchanged_on P m m' ->
  (forall i, ofs <= i < ofs + len -> P b i) ->
  read_as_zero m' b ofs len cp.
Proof.
  intros; red; intros. eapply Mem.load_unchanged_on; eauto.
  intros; apply H1. omega.
Qed.

Lemma store_zeros_read_as_zero:
  forall m b p n cp m',
    Mem.can_access_block m b (Some cp) ->
  store_zeros m b p n cp = Some m' ->
  read_as_zero m' b p n (Some cp).
Proof.
  intros; red; intros.
  transitivity (Some(decode_val chunk (list_repeat (size_chunk_nat chunk) (Byte Byte.zero)))).
  apply Mem.loadbytes_load; auto. rewrite size_chunk_conv.
  eapply store_zeros_loadbytes; eauto. rewrite <- size_chunk_conv; auto.
  f_equal. destruct chunk; unfold decode_val; unfold decode_int; unfold rev_if_be; destruct Archi.big_endian; reflexivity.
Qed. *)

Fixpoint load_store_init_data (m: mem) (c: occap) (p: Z) (il: list init_data) (cp: option compartment) {struct il} : Prop :=
  match il with
  | nil => True
  | Init_int8 n :: il' =>
      Mem.load DEFAULT CMint8unsigned m c p cp = inl (OCVint(Int.zero_ext 8 n))
      /\ load_store_init_data m c (p + 1) il' cp
  | Init_int16 n :: il' =>
      Mem.load DEFAULT CMint16unsigned m c p cp = inl(OCVint(Int.zero_ext 16 n))
      /\ load_store_init_data m c (p + 2) il' cp
  | Init_int32 n :: il' =>
      Mem.load DEFAULT CMint32 m c p cp = inl(OCVint n)
      /\ load_store_init_data m c (p + 4) il' cp
  | Init_int64 n :: il' =>
      Mem.load DEFAULT CMint64 m c p cp = inl(OCVlong n)
      /\ load_store_init_data m c (p + 8) il' cp
  | Init_float32 n :: il' =>
      Mem.load DEFAULT CMfloat32 m c p cp = inl(OCVsingle n)
      /\ load_store_init_data m c (p + 4) il' cp
  | Init_float64 n :: il' =>
      Mem.load DEFAULT CMfloat64 m c p cp = inl(OCVfloat n)
      /\ load_store_init_data m c (p + 8) il' cp
  | Init_addrof symb ofs :: il' =>
      (exists b', find_symbol ge symb = Some b' /\ Mem.load DEFAULT CMptr m c p cp = inl(OCVcap b'))
      /\ load_store_init_data m c (p + size_chunk CMcap) il' cp
  | Init_space n :: il' =>
      read_as_zero m c p n cp
      /\ load_store_init_data m c (p + Z.max n 0) il' cp
  end.

(* ALG: TODO *)
(* Lemma store_init_data_list_charact:
  forall b il m p cp m',
  store_init_data_list m b p il cp = Some m' ->
  read_as_zero m b p (init_data_list_size il) (Some cp) ->
  load_store_init_data m' b p il (Some cp).
Proof.
  assert (A: forall chunk v m b p m1 il cp m',
    Mem.store chunk m b p v cp = Some m1 ->
    store_init_data_list m1 b (p + size_chunk chunk) il cp = Some m' ->
    Mem.load chunk m' b p (Some cp) = Some(Val.load_result chunk v)).
  {
    intros.
    eapply Mem.load_unchanged_on with (P := fun b' ofs' => ofs' < p + size_chunk chunk).
    eapply store_init_data_list_unchanged; eauto. intros; omega.
    intros; tauto.
    eapply Mem.load_store_same; eauto.
  }
  induction il; simpl.
- auto.
- intros. destruct (store_init_data m b p a) as [m1|] eqn:?; try congruence.
  exploit IHil; eauto.
  set (P := fun (b': block) ofs' => p + init_data_size a <= ofs').
  apply read_as_zero_unchanged with (m := m) (P := P).
  red; intros; apply H0; auto. generalize (init_data_size_pos a); omega. omega.
  eapply store_init_data_unchanged with (P := P); eauto.
  intros; unfold P. omega.
  intros; unfold P. omega.
  intro D.
  destruct a; simpl in Heqo.
+ split; auto. eapply (A Mint8unsigned (Vint i)); eauto.
+ split; auto. eapply (A Mint16unsigned (Vint i)); eauto.
+ split; auto. eapply (A Mint32 (Vint i)); eauto.
+ split; auto. eapply (A Mint64 (Vlong i)); eauto.
+ split; auto. eapply (A Mfloat32 (Vsingle f)); eauto.
+ split; auto. eapply (A Mfloat64 (Vfloat f)); eauto.
+ split; auto.
  set (P := fun (b': block) ofs' => ofs' < p + init_data_size (Init_space z)).
  inv Heqo. apply read_as_zero_unchanged with (m := m1) (P := P).
  red; intros. apply H0; auto. simpl. generalize (init_data_list_size_pos il); xomega.
  eapply store_init_data_list_unchanged; eauto.
  intros; unfold P. omega.
  intros; unfold P. simpl; xomega.
+ rewrite init_data_size_addrof in *.
  split; auto.
  destruct (find_symbol ge i); try congruence.
  exists b0; split; auto.
  transitivity (Some (Val.load_result Mptr (Vptr b0 i0))).
  eapply (A Mptr (Vptr b0 i0)); eauto.
  unfold Val.load_result, Mptr; destruct Archi.ptr64; auto.
Qed.

Remark alloc_global_unchanged:
  forall (P: block -> Z -> Prop) m id g m',
  alloc_global m (id, g) = Some m' ->
  Mem.unchanged_on P m m'.
Proof.
  intros. destruct g as [f|v]; simpl in H.
- (* function *)
  destruct (Mem.alloc m _ 0 1) as [m1 b] eqn:?.
  set (Q := fun b' (ofs: Z) => b' <> b).
  apply Mem.unchanged_on_implies with Q.
  apply Mem.unchanged_on_trans with m1.
  eapply Mem.alloc_unchanged_on; eauto.
  eapply Mem.drop_perm_unchanged_on; eauto.
  intros; red. apply Mem.valid_not_valid_diff with m; eauto with mem.
- (* variable *)
  set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m _ 0 sz) as [m1 b] eqn:?.
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list m2 b 0 init) as [m3|] eqn:?; try discriminate.
  set (Q := fun b' (ofs: Z) => b' <> b).
  apply Mem.unchanged_on_implies with Q.
  apply Mem.unchanged_on_trans with m1.
  eapply Mem.alloc_unchanged_on; eauto.
  apply Mem.unchanged_on_trans with m2.
  eapply store_zeros_unchanged; eauto.
  apply Mem.unchanged_on_trans with m3.
  eapply store_init_data_list_unchanged; eauto.
  eapply Mem.drop_perm_unchanged_on; eauto.
  intros; red. apply Mem.valid_not_valid_diff with m; eauto with mem.
Qed.

Remark alloc_globals_unchanged:
  forall (P: block -> Z -> Prop) gl m m',
  alloc_globals m gl = Some m' ->
  Mem.unchanged_on P m m'.
Proof.
  induction gl; simpl; intros.
- inv H. apply Mem.unchanged_on_refl.
- destruct (alloc_global m a) as [m''|] eqn:?; try discriminate.
  destruct a as [id g].
  apply Mem.unchanged_on_trans with m''.
  eapply alloc_global_unchanged; eauto.
  apply IHgl; auto.
Qed.

Remark load_store_init_data_invariant:
  forall m m' b,
  (forall chunk ofs cp, Mem.load chunk m' b ofs cp = Mem.load chunk m b ofs cp) ->
  forall il p cp,
  load_store_init_data m b p il cp -> load_store_init_data m' b p il cp.
Proof.
  induction il; intro p; simpl.
  auto.
  intros. rewrite ! H. destruct a; intuition. red; intros; rewrite H; auto.
Qed. *)

(* ALD: TODO: add something about the permission/sealed status/other tags of the capability? *)
Definition globals_initialized (g: t) (m: mem) :=
  forall b gd,
  find_def g b = Some gd ->
  match gd with
  | Gfun f =>
    Mem.perm m (Mem.derive_offset DEFAULT b 0) Cur Nonempty
      /\ (forall ofs k p, Mem.perm m (Mem.derive_offset DEFAULT b ofs) k p -> ofs = 0 /\ p = Nonempty)
  | Gvar v =>
         Mem.range_perm m (Mem.derive_offset DEFAULT b 0) (Mem.derive_offset DEFAULT b (init_data_list_size v.(gvar_init))) Cur (perm_globvar v)
      /\ (forall ofs k p, Mem.perm m (Mem.derive_offset DEFAULT b ofs) k p ->
            0 <= ofs < init_data_list_size v.(gvar_init) /\ perm_order (perm_globvar v) p)
      /\ (v.(gvar_volatile) = false -> load_store_init_data m b 0 v.(gvar_init) (Some v.(gvar_comp)))
      /\ (v.(gvar_volatile) = false -> Mem.loadbytes DEFAULT m b 0 (init_data_list_size v.(gvar_init)) (Some v.(gvar_comp)) = inl (bytes_of_init_data_list v.(gvar_init)))
  end.

(* ALG: TODO *)
(* Lemma alloc_global_initialized:
  forall g m id gd m',
  genv_next g = Mem.nextblock m ->
  alloc_global m (id, gd) = Some m' ->
  globals_initialized g m ->
     globals_initialized (add_global g (id, gd)) m'
  /\ genv_next (add_global g (id, gd)) = Mem.nextblock m'.
Proof.
  intros.
  exploit alloc_global_nextblock; eauto. intros NB. split.
- (* globals-initialized *)
  red; intros. unfold find_def in H2; simpl in H2.
  rewrite PTree.gsspec in H2. destruct (peq b (genv_next g)).
+ inv H2. destruct gd0 as [f|v]; simpl in H0.
* destruct (Mem.alloc m _ 0 1) as [m1 b] eqn:ALLOC.
  exploit Mem.alloc_result; eauto. intros RES.
  rewrite H, <- RES. split.
  eapply Mem.perm_drop_1; eauto. omega.
  intros.
  assert (0 <= ofs < 1). { eapply Mem.perm_alloc_3; eauto. eapply Mem.perm_drop_4; eauto. }
  exploit Mem.perm_drop_2; eauto. intros ORD.
  split. omega. inv ORD; auto.
* set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m _ 0 sz) as [m1 b] eqn:?.
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list m2 b 0 init) as [m3|] eqn:?; try discriminate.
  exploit Mem.alloc_result; eauto. intro RES.
  replace (genv_next g) with b by congruence.
  split. red; intros. eapply Mem.perm_drop_1; eauto.
  split. intros.
  assert (0 <= ofs < sz).
  { eapply Mem.perm_alloc_3; eauto.
    erewrite store_zeros_perm by eauto.
    erewrite store_init_data_list_perm by eauto.
    eapply Mem.perm_drop_4; eauto. }
  split; auto.
  eapply Mem.perm_drop_2; eauto.
  split. intros NOTVOL. apply load_store_init_data_invariant with m3.
  intros. eapply Mem.load_drop; eauto. right; right; right.
  unfold perm_globvar. rewrite NOTVOL. destruct (gvar_readonly v); auto with mem.
  eapply store_init_data_list_charact; eauto.
  eapply store_zeros_read_as_zero; eauto. eapply Mem.owned_new_block; eauto.
  intros NOTVOL.
  transitivity (Mem.loadbytes m3 b 0 sz (Some v.(gvar_comp))).
  eapply Mem.loadbytes_drop; eauto. right; right; right.
  unfold perm_globvar. rewrite NOTVOL. destruct (gvar_readonly v); auto with mem.
  eapply store_init_data_list_loadbytes; eauto.
  eapply store_zeros_loadbytes; eauto. eapply Mem.owned_new_block; eauto.
  eapply store_zeros_loadbytes; eauto. eapply Mem.owned_new_block; eauto.
+ assert (U: Mem.unchanged_on (fun _ _ => True) m m') by (eapply alloc_global_unchanged; eauto).
  assert (VALID: Mem.valid_block m b).
  { red. rewrite <- H. eapply genv_defs_range; eauto. }
  exploit H1; eauto.
  destruct gd0 as [f|v].
* intros [A B]; split; intros.
  eapply Mem.perm_unchanged_on; eauto. exact I.
  eapply B. eapply Mem.perm_unchanged_on_2; eauto. exact I.
* intros (A & B & C & D). split; [| split; [| split]].
  red; intros. eapply Mem.perm_unchanged_on; eauto. exact I.
  intros. eapply B. eapply Mem.perm_unchanged_on_2; eauto. exact I.
  intros. apply load_store_init_data_invariant with m; auto.
  intros. eapply Mem.load_unchanged_on_1; eauto. intros; exact I.
  intros. eapply Mem.loadbytes_unchanged_on; eauto. intros; exact I.
- simpl. congruence.
Qed.

Lemma alloc_globals_initialized:
  forall gl ge m m',
  alloc_globals m gl = Some m' ->
  genv_next ge = Mem.nextblock m ->
  globals_initialized ge m ->
  globals_initialized (add_globals ge gl) m'.
Proof.
  induction gl; simpl; intros.
- inv H; auto.
- destruct a as [id g]. destruct (alloc_global m (id, g)) as [m1|] eqn:?; try discriminate.
  exploit alloc_global_initialized; eauto. intros [P Q].
  eapply IHgl; eauto.
Qed. *)

(** * Construction of the stack *)

(** A stack region is initialized to NonEmpty *)
(** Note that since it starts out uninitialized, it does not need to
  be 0'd out *)

Definition alloc_stack (m: mem): option mem :=
  match ge.(genv_stack) with
  | Some cap => Some (Mem.init_stack m cap)
  | None => None
end.

(** * Construction of the per component heaps *)

Definition alloc_heap (m: mem) (idg: ident * globdef F V) : option mem :=
  let (id, g) := idg in
  let comp := comp_of_gl g in
  match PTree.get comp (genv_heaps ge) with
  | Some cap =>
      let m1 := Mem.init_heap m comp cap in
      Some m1
  | None => None
  end.

Fixpoint alloc_heaps (m: mem) (gl: list (ident * globdef F V)) {struct gl} : option mem :=
  match gl with
  | nil => Some m
  | g :: gl' =>
      match alloc_heap m g with
      | Some m' => alloc_heaps m' gl'
      | None => None
      end
  end.

End INITMEM.

Definition init_mem (ge: t) (p: program F V) (gstart gend: ptrofs) :=
  do GL <- (globalenv p gstart gend);
  do M1 <- alloc_globals GL Mem.empty p.(prog_defs);
  do M2 <- alloc_stack GL M1;
  alloc_heaps GL M2 p.(prog_defs).

Lemma init_mem_find_def:
  forall p m b g,
  init_mem p = Some m ->
  find_def (globalenv p) b = Some g ->
  Mem.block_compartment m b = Some (comp_of g).
Proof.
  intros p m b g.
  unfold init_mem, find_def.
  intros ALLOC.
  rewrite (alloc_globals_block_compartment _ _ _ ALLOC). clear ALLOC.
  unfold globalenv.
  assert (Mem.block_compartment Mem.empty b = None) as ->.
  { rewrite <- Mem.block_compartment_valid_block.
    unfold Mem.valid_block. rewrite Mem.nextblock_empty.
    now destruct b. }
  simpl.
  set (ge := empty_genv _ _).
  change 1%positive with (genv_next ge).
  assert (forall g', (genv_defs ge) ! b = Some g' ->
                     None = Some (comp_of g')) as INV.
  { intros g'. unfold ge. simpl. now rewrite PTree.gempty. }
  generalize ge (@None compartment) INV. clear ge INV.
  generalize (prog_defs p). clear p. intros idgl.
  induction idgl as [|idg idgl IH]; simpl.
  - eauto.
  - intros ge o INV. apply IH. clear IH g.
    intros g. simpl. destruct eq_block as [->|neq].
    + rewrite PTree.gss. intros H. now injection H as <-.
    + rewrite PTree.gso; trivial. apply INV.
Qed.

Lemma init_mem_genv_next: forall p m,
  init_mem p = Some m ->
  genv_next (globalenv p) = Mem.nextblock m.
Proof.
  unfold init_mem; intros.
  exploit alloc_globals_nextblock; eauto. rewrite Mem.nextblock_empty. intro.
  generalize (genv_next_add_globals (prog_defs p) (empty_genv (prog_public p) (prog_pol p))).
  fold (globalenv p). simpl genv_next. intros. congruence.
Qed.

Theorem find_symbol_not_fresh:
  forall p id b m,
  init_mem p = Some m ->
  find_symbol (globalenv p) id = Some b -> Mem.valid_block m b.
Proof.
  intros. red. erewrite <- init_mem_genv_next; eauto.
  eapply genv_symb_range; eauto.
Qed.

Theorem find_def_not_fresh:
  forall p b g m,
  init_mem p = Some m ->
  find_def (globalenv p) b = Some g -> Mem.valid_block m b.
Proof.
  intros. red. erewrite <- init_mem_genv_next; eauto.
  eapply genv_defs_range; eauto.
Qed.

Theorem find_funct_ptr_not_fresh:
  forall p b f m,
  init_mem p = Some m ->
  find_funct_ptr (globalenv p) b = Some f -> Mem.valid_block m b.
Proof.
  intros. rewrite find_funct_ptr_iff in H0. eapply find_def_not_fresh; eauto.
Qed.

Theorem find_var_info_not_fresh:
  forall p b gv m,
  init_mem p = Some m ->
  find_var_info (globalenv p) b = Some gv -> Mem.valid_block m b.
Proof.
  intros. rewrite find_var_info_iff in H0. eapply find_def_not_fresh; eauto.
Qed.

Lemma init_mem_characterization_gen:
  forall p m,
  init_mem p = Some m ->
  globals_initialized (globalenv p) (globalenv p) m.
Proof.
  intros. apply alloc_globals_initialized with Mem.empty.
  auto.
  rewrite Mem.nextblock_empty. auto.
  red; intros. unfold find_def in H0; simpl in H0; rewrite PTree.gempty in H0; discriminate.
Qed.

Theorem init_mem_characterization:
  forall p b gv m,
  find_var_info (globalenv p) b = Some gv ->
  init_mem p = Some m ->
  Mem.range_perm m b 0 (init_data_list_size gv.(gvar_init)) Cur (perm_globvar gv)
  /\ (forall ofs k p, Mem.perm m b ofs k p ->
        0 <= ofs < init_data_list_size gv.(gvar_init) /\ perm_order (perm_globvar gv) p)
  /\ (gv.(gvar_volatile) = false ->
      load_store_init_data (globalenv p) m b 0 gv.(gvar_init) (Some gv.(gvar_comp)))
  /\ (gv.(gvar_volatile) = false ->
      Mem.loadbytes m b 0 (init_data_list_size gv.(gvar_init)) (Some gv.(gvar_comp)) = Some (bytes_of_init_data_list (globalenv p) gv.(gvar_init))).
Proof.
  intros. rewrite find_var_info_iff in H.
  exploit init_mem_characterization_gen; eauto.
Qed.

Theorem init_mem_characterization_2:
  forall p b fd m,
  find_funct_ptr (globalenv p) b = Some fd ->
  init_mem p = Some m ->
  Mem.perm m b 0 Cur Nonempty
  /\ (forall ofs k p, Mem.perm m b ofs k p -> ofs = 0 /\ p = Nonempty).
Proof.
  intros. rewrite find_funct_ptr_iff in H.
  exploit init_mem_characterization_gen; eauto.
Qed.

(** ** Compatibility with memory injections *)

Section INITMEM_INJ.

Variable ge: t.
Variable thr: block.
Hypothesis symb_inject: forall id b, find_symbol ge id = Some b -> Plt b thr.

Lemma store_zeros_neutral:
  forall m b p n cp m',
  Mem.inject_neutral thr m ->
  Plt b thr ->
  store_zeros m b p n cp = Some m' ->
  Mem.inject_neutral thr m'.
Proof.
  intros until cp. functional induction (store_zeros m b p n cp); intros.
  inv H1; auto.
  apply IHo; auto. eapply Mem.store_inject_neutral; eauto. constructor.
  inv H1.
Qed.

Lemma store_init_data_neutral:
  forall m b p id cp m',
  Mem.inject_neutral thr m ->
  Plt b thr ->
  store_init_data ge m b p id cp = Some m' ->
  Mem.inject_neutral thr m'.
Proof.
  intros.
  destruct id; simpl in H1; try (eapply Mem.store_inject_neutral; eauto; fail).
  congruence.
  destruct (find_symbol ge i) as [b'|] eqn:E; try discriminate.
  eapply Mem.store_inject_neutral; eauto.
  econstructor. unfold Mem.flat_inj. apply pred_dec_true; auto. eauto.
  rewrite Ptrofs.add_zero. auto.
Qed.

Lemma store_init_data_list_neutral:
  forall b idl m p cp m',
  Mem.inject_neutral thr m ->
  Plt b thr ->
  store_init_data_list ge m b p idl cp = Some m' ->
  Mem.inject_neutral thr m'.
Proof.
  induction idl; simpl; intros.
  congruence.
  destruct (store_init_data ge m b p a) as [m1|] eqn:E; try discriminate.
  eapply IHidl. eapply store_init_data_neutral; eauto. auto. eauto.
Qed.

Lemma alloc_global_neutral:
  forall idg m m',
  alloc_global ge m idg = Some m' ->
  Mem.inject_neutral thr m ->
  Plt (Mem.nextblock m) thr ->
  Mem.inject_neutral thr m'.
Proof.
  intros. destruct idg as [id [f|v]]; simpl in H.
- (* function *)
  destruct (Mem.alloc m _ 0 1) as [m1 b] eqn:?.
  assert (Plt b thr). rewrite (Mem.alloc_result _ _ _ _ _ _ Heqp). auto.
  eapply Mem.drop_inject_neutral; eauto.
  eapply Mem.alloc_inject_neutral; eauto.
- (* variable *)
  set (init := gvar_init v) in *.
  set (sz := init_data_list_size init) in *.
  destruct (Mem.alloc m _ 0 sz) as [m1 b] eqn:?.
  destruct (store_zeros m1 b 0 sz) as [m2|] eqn:?; try discriminate.
  destruct (store_init_data_list ge m2 b 0 init) as [m3|] eqn:?; try discriminate.
  assert (Plt b thr). rewrite (Mem.alloc_result _ _ _ _ _ _ Heqp). auto.
  eapply Mem.drop_inject_neutral; eauto.
  eapply store_init_data_list_neutral with (m := m2) (b := b); eauto.
  eapply store_zeros_neutral with (m := m1); eauto.
  eapply Mem.alloc_inject_neutral; eauto.
Qed.

Remark advance_next_le: forall gl x, Ple x (advance_next gl x).
Proof.
  induction gl; simpl; intros.
  apply Ple_refl.
  apply Ple_trans with (Pos.succ x). apply Ple_succ. eauto.
Qed.

Lemma alloc_globals_neutral:
  forall gl m m',
  alloc_globals ge m gl = Some m' ->
  Mem.inject_neutral thr m ->
  Ple (Mem.nextblock m') thr ->
  Mem.inject_neutral thr m'.
Proof.
  induction gl; intros.
  simpl in *. congruence.
  exploit alloc_globals_nextblock; eauto. intros EQ.
  simpl in *. destruct (alloc_global ge m a) as [m1|] eqn:E; try discriminate.
  exploit alloc_global_neutral; eauto.
  assert (Ple (Pos.succ (Mem.nextblock m)) (Mem.nextblock m')).
  { rewrite EQ. apply advance_next_le. }
  unfold Plt, Ple in *; zify; omega.
Qed.

End INITMEM_INJ.

Theorem initmem_inject:
  forall p m,
  init_mem p = Some m ->
  Mem.inject (Mem.flat_inj (Mem.nextblock m)) m m.
Proof.
  unfold init_mem; intros.
  apply Mem.neutral_inject.
  eapply alloc_globals_neutral; eauto.
  intros. exploit find_symbol_not_fresh; eauto.
  apply Mem.empty_inject_neutral.
  apply Ple_refl.
Qed.

(** ** Sufficient and necessary conditions for the initial memory to exist. *)

(** Alignment properties *)

Definition init_data_alignment (i: init_data) : Z :=
  match i with
  | Init_int8 n => 1
  | Init_int16 n => 2
  | Init_int32 n => 4
  | Init_int64 n => 8
  | Init_float32 n => 4
  | Init_float64 n => 4
  | Init_addrof symb ofs => if Archi.ptr64 then 8 else 4
  | Init_space n => 1
  end.

Fixpoint init_data_list_aligned (p: Z) (il: list init_data) {struct il} : Prop :=
  match il with
  | nil => True
  | i1 :: il => (init_data_alignment i1 | p) /\ init_data_list_aligned (p + init_data_size i1) il
  end.

Section INITMEM_INVERSION.

Variable ge: t.

Lemma store_init_data_aligned:
  forall m b p i cp m',
  store_init_data ge m b p i cp = Some m' ->
  (init_data_alignment i | p).
Proof.
  intros.
  assert (DFL: forall chunk v,
    Mem.store chunk m b p v cp = Some m' ->
    align_chunk chunk = init_data_alignment i ->
    (init_data_alignment i | p)).
  { intros. apply Mem.store_valid_access_3 in H0. destruct H0 as [? [? ?]]. congruence. }
  destruct i; simpl in H; eauto.
  simpl. apply Z.divide_1_l.
  destruct (find_symbol ge i); try discriminate. eapply DFL. eassumption.
  unfold Mptr, init_data_alignment; destruct Archi.ptr64; auto.
Qed.

Lemma store_init_data_list_aligned:
  forall b il m p cp m',
  store_init_data_list ge m b p il cp = Some m' ->
  init_data_list_aligned p il.
Proof.
  induction il as [ | i1 il]; simpl; intros.
- auto.
- destruct (store_init_data ge m b p i1) as [m1|] eqn:S1; try discriminate.
  split; eauto. eapply store_init_data_aligned; eauto.
Qed.

Lemma store_init_data_list_free_idents:
  forall b i o il m p cp m',
  store_init_data_list ge m b p il cp = Some m' ->
  In (Init_addrof i o) il ->
  exists b', find_symbol ge i = Some b'.
Proof.
  induction il as [ | i1 il]; simpl; intros.
- contradiction.
- destruct (store_init_data ge m b p i1) as [m1|] eqn:S1; try discriminate.
  destruct H0.
+ subst i1. simpl in S1. destruct (find_symbol ge i) as [b'|]. exists b'; auto. discriminate.
+ eapply IHil; eauto.
Qed.

End INITMEM_INVERSION.

Theorem init_mem_inversion:
  forall p m id v,
  init_mem p = Some m ->
  In (id, Gvar v) p.(prog_defs) ->
  init_data_list_aligned 0 v.(gvar_init)
  /\ forall i o, In (Init_addrof i o) v.(gvar_init) -> exists b, find_symbol (globalenv p) i = Some b.
Proof.
  intros until v. unfold init_mem. set (ge := globalenv p).
  revert m. generalize Mem.empty. generalize (prog_defs p).
  induction l as [ | idg1 defs ]; simpl; intros m m'; intros.
- contradiction.
- destruct (alloc_global ge m idg1) as [m''|] eqn:A; try discriminate.
  destruct H0.
+ subst idg1; simpl in A.
  set (il := gvar_init v) in *. set (sz := init_data_list_size il) in *.
  destruct (Mem.alloc m _ 0 sz) as [m1 b].
  destruct (store_zeros m1 b 0 sz) as [m2|]; try discriminate.
  destruct (store_init_data_list ge m2 b 0 il) as [m3|] eqn:B; try discriminate.
  split. eapply store_init_data_list_aligned; eauto. intros; eapply store_init_data_list_free_idents; eauto.
+ eapply IHdefs; eauto.
Qed.

Section INITMEM_EXISTS.

Variable ge: t.

Lemma store_zeros_exists:
  forall m b p n cp,
    Mem.range_perm m b p (p + n) Cur Writable ->
    Mem.can_access_block m b (Some cp) ->
  exists m', store_zeros m b p n cp = Some m'.
Proof.
  intros until cp. functional induction (store_zeros m b p n cp); intros PERM ACC.
- exists m; auto.
- intros. apply IHo. red; intros. eapply Mem.perm_store_1; eauto. apply PERM. omega.
  eapply (Mem.store_can_access_block_inj _ _ _ _ _ _ _ e0). eauto.
- destruct (Mem.valid_access_store m Mint8unsigned b p cp Vzero) as (m' & STORE).
  split. red; intros. apply Mem.perm_cur. apply PERM. simpl in H. omega.
  split. auto.
  simpl. apply Z.divide_1_l.
  congruence.
Qed.

Lemma store_init_data_exists:
  forall m b p i cp,
  Mem.range_perm m b p (p + init_data_size i) Cur Writable ->
  forall OWN : Mem.can_access_block m b (Some cp),
  (init_data_alignment i | p) ->
  (forall id ofs, i = Init_addrof id ofs -> exists b, find_symbol ge id = Some b) ->
  exists m', store_init_data ge m b p i cp = Some m'.
Proof.
  intros.
  assert (DFL: forall chunk v,
          init_data_size i = size_chunk chunk ->
          init_data_alignment i = align_chunk chunk ->
          exists m', Mem.store chunk m b p v cp = Some m').
  { intros. destruct (Mem.valid_access_store m chunk b p cp v) as (m' & STORE).
    split. rewrite <- H2; auto. rewrite <- H3; auto.
    exists m'; auto. }
  destruct i; eauto.
  simpl. exists m; auto.
  simpl. exploit H1; eauto. intros (b1 & FS). rewrite FS. eapply DFL.
  unfold init_data_size, Mptr. destruct Archi.ptr64; auto.
  unfold init_data_alignment, Mptr. destruct Archi.ptr64; auto.
Qed.

Lemma store_init_data_list_exists:
  forall b il m p cp,
  Mem.range_perm m b p (p + init_data_list_size il) Cur Writable ->
  forall OWN : Mem.can_access_block m b (Some cp),
  init_data_list_aligned p il ->
  (forall id ofs, In (Init_addrof id ofs) il -> exists b, find_symbol ge id = Some b) ->
  exists m', store_init_data_list ge m b p il cp = Some m'.
Proof.
  induction il as [ | i1 il ]; simpl; intros.
- exists m; auto.
- destruct H0.
  destruct (@store_init_data_exists m b p i1 cp) as (m1 & S1); eauto.
  red; intros. apply H. generalize (init_data_list_size_pos il); omega.
  rewrite S1.
  apply IHil; eauto.
  red; intros. erewrite <- store_init_data_perm by eauto. apply H. generalize (init_data_size_pos i1); omega.

  destruct i1; inv S1;
    try eapply (Mem.store_can_access_block_inj _ _ _ _ _ _ _ H4); eauto.
  destruct (find_symbol ge i); try discriminate.
  eapply (Mem.store_can_access_block_inj _ _ _ _ _ _ _ H4). eauto.
Qed.


Lemma alloc_global_exists:
  forall m idg,
  match idg with
  | (id, Gfun f) => True
  | (id, Gvar v) =>
        init_data_list_aligned 0 v.(gvar_init)
     /\ forall i o, In (Init_addrof i o) v.(gvar_init) -> exists b, find_symbol ge i = Some b
  end ->
  exists m', alloc_global ge m idg = Some m'.
Proof.
  intros m [id [f|v]]; intros; simpl.
- destruct (Mem.alloc m _ 0 1) as [m1 b] eqn:ALLOC.
  destruct (Mem.range_perm_drop_2 m1 b 0 1 (comp_of f) Nonempty) as [m2 DROP].
  red; intros; eapply Mem.perm_alloc_2; eauto.
  eapply Mem.owned_new_block; eauto.
  exists m2; auto.
- destruct H as [P Q].
  set (sz := init_data_list_size (gvar_init v)).
  destruct (Mem.alloc m _ 0 sz) as [m1 b] eqn:ALLOC.
  assert (P1: Mem.range_perm m1 b 0 sz Cur Freeable) by (red; intros; eapply Mem.perm_alloc_2; eauto).
  destruct (@store_zeros_exists m1 b 0 sz (gvar_comp v)) as [m2 ZEROS].
  red; intros. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.owned_new_block; eauto.
  rewrite ZEROS.
  assert (P2: Mem.range_perm m2 b 0 sz Cur Freeable).
  { red; intros. erewrite <- store_zeros_perm by eauto. eauto. }
  destruct (@store_init_data_list_exists b (gvar_init v) m2 0 (gvar_comp v)) as [m3 STORE]; auto.
  red; intros. apply Mem.perm_implies with Freeable; auto with mem.
  eapply store_zeros_block_compartment with (b' := b) in ZEROS.
  unfold Mem.can_access_block.  rewrite ZEROS. eapply Mem.owned_new_block. eauto.
  rewrite STORE.
  assert (P3: Mem.range_perm m3 b 0 sz Cur Freeable).
  { red; intros. erewrite <- store_init_data_list_perm by eauto. eauto. }
  destruct (Mem.range_perm_drop_2 m3 b 0 sz (gvar_comp v) (perm_globvar v)) as [m4 DROP]; auto.
  eapply store_init_data_list_block_compartment with (b' := b) in STORE.
  eapply store_zeros_block_compartment with (b' := b) in ZEROS.
  unfold Mem.can_access_block.  rewrite STORE, ZEROS. eapply Mem.owned_new_block. eauto.
  exists m4; auto.
Qed.

End INITMEM_EXISTS.

Theorem init_mem_exists:
  forall p,
  (forall id v, In (id, Gvar v) (prog_defs p) ->
        init_data_list_aligned 0 v.(gvar_init)
     /\ forall i o, In (Init_addrof i o) v.(gvar_init) -> exists b, find_symbol (globalenv p) i = Some b) ->
  exists m, init_mem p = Some m.
Proof.
  intros. set (ge := globalenv p) in *.
  unfold init_mem. revert H. generalize (prog_defs p) Mem.empty.
  induction l as [ | idg l]; simpl; intros.
- exists m; auto.
- destruct (@alloc_global_exists ge m idg) as [m1 A1].
  destruct idg as [id [f|v]]; eauto.
  fold ge. rewrite A1. eapply IHl; eauto.
Qed.

(* Allowed cross-compartment calls *)
Definition allowed_cross_call (ge: t) (cp: compartment) (vf: val) :=
  match vf with
  | Vptr b _ =>
    exists i cp',
    invert_symbol ge b = Some i /\
    find_comp ge vf = cp' /\
    match (Policy.policy_import ge.(genv_policy)) ! cp with
    | Some l => In (cp', i) l
    | None => False
    end /\
    match (Policy.policy_export ge.(genv_policy)) ! cp' with
    | Some l => In i l
    | None => False
    end
  | _ => False
  end.

Variant call_type :=
  | InternalCall
  | CrossCompartmentCall
  | DefaultCompartmentCall
.

Definition type_of_call (ge: t) (cp: compartment) (cp': compartment): call_type :=
  if Pos.eqb cp cp' then InternalCall
  else if Pos.eqb cp' default_compartment then DefaultCompartmentCall
       else CrossCompartmentCall.

(* Definition type_of_call (ge: t) (cp: compartment) (vf: val): call_type := *)
(*   match find_comp ge vf with *)
(*   | None => InternalCall (* a failed call is internal, by definition *) *)
(*   | Some cp' => type_of_call ge cp cp' *)
(*       (* if Pos.eqb cp cp' then InternalCall *) *)
(*       (* else if Pos.eqb cp' default_compartment then DefaultCompartmentCall *) *)
(*       (*      else CrossCompartmentCall *) *)
(*   end. *)

(* (* A call is cross-compartment if the following definition holds: *) *)
(* Definition cross_call (ge: t) (cp: compartment) (vf: val) := *)
(*   match find_comp ge vf with *)
(*   | Some cp' => cp <> cp' /\ *)
(*                  cp' <> default_compartment (* the default compartment is really privileged, *)
(*                                             as this is where all the builtin functions live *) *)
(*   | None => False *)
(*   end. *)

(* Definition cross_call_b (ge: t) (cp: compartment) (vf: val): bool := *)
(*   match find_comp ge vf with *)
(*   | Some cp' => negb (Pos.eqb cp cp') && negb (Pos.eqb cp' default_compartment) *)
(*   | None => false *)
(*   end. *)

(* Lemma cross_call_reflect: forall ge cp vf, *)
(*     cross_call ge cp vf <-> cross_call_b ge cp vf = true. *)
(* Proof. *)
(*   intros. *)
(*   unfold cross_call, cross_call_b. *)
(*   destruct (find_comp ge vf) eqn:COMP. *)
(*   - split. *)
(*     + intros [cp_neq cp_neq']. *)
(*       apply Pos.eqb_neq in cp_neq. apply Pos.eqb_neq in cp_neq'. *)
(*       rewrite cp_neq, cp_neq'. reflexivity. *)
(*     + intros cp_neq. apply andb_true_iff in cp_neq as [cp_neq cp_neq']. *)
(*       apply negb_true_iff in cp_neq. apply negb_true_iff in cp_neq'. *)
(*       split; apply Pos.eqb_neq; assumption. *)
(*   - split; [auto | discriminate]. *)
(* Qed. *)

(* A call is allowed if any of these 3 cases holds:
(1) the procedure being called belongs to the default compartment
(2) the procedure being called belongs to the same compartment as the caller
(3) the call is an inter-compartment call and is allowed by the policy
*)
Definition allowed_call (ge: t) (cp: compartment) (vf: val) :=
  default_compartment = find_comp ge vf \/ (* TODO: does this mean we allow all compartment to perform IO calls? *)
  cp = find_comp ge vf \/
  allowed_cross_call ge cp vf.

Lemma comp_ident_eq_dec: forall (x y: compartment * ident),
    {x = y} + {x <> y}.
Proof.
  intros x y.
  decide equality.
  eapply Pos.eq_dec.
  eapply Pos.eq_dec.
Qed.

Definition allowed_call_b (ge: t) (cp: compartment) (vf: val): bool :=
  match find_comp ge vf with
  | c => Pos.eqb c default_compartment
             || Pos.eqb c cp
             || match vf with
               | Vptr b _ => match invert_symbol ge b with
                            | Some i =>
                              match (Policy.policy_import ge.(genv_policy)) ! cp with
                              | Some imps =>
                                match (Policy.policy_export ge.(genv_policy)) ! c with
                                | Some exps =>
                                  in_dec comp_ident_eq_dec (c, i) imps &&
                                  in_dec Pos.eq_dec i exps
                                | None => false
                                end
                              | None => false
                              end
                            | None => false
                            end
               | _ => false
               end
  end.

Lemma allowed_call_reflect: forall ge cp vf,
    allowed_call ge cp vf <-> allowed_call_b ge cp vf = true.
Proof.
  intros ge cp vf.
  unfold allowed_call, allowed_call_b, allowed_cross_call.
  destruct vf eqn:VF; try (firstorder; discriminate).
  (* destruct (find_comp ge (Vptr b i)) eqn:COMP; try (firstorder; discriminate). *)
  remember (find_comp ge (Vptr b i)) as c.
  destruct (Pos.eq_dec default_compartment c); subst.
  - rewrite <- e. split; auto.
  - destruct (Pos.eq_dec (find_comp ge (Vptr b i)) cp); subst.
    (* destruct (Pos.eq_dec c cp); subst. *)
    + rewrite Pos.eqb_refl. rewrite orb_true_r. simpl. split; auto.
    + split; auto.
      * intros H. destruct H as [? | [? | ?]]; try congruence.
        destruct H as [i' [cp' [H1 [H2 [H3 H4]]]]].
        rewrite H1. inv H2.
        destruct ((Policy.policy_import (genv_policy ge)) ! cp) as [imps |]; auto.
        destruct ((Policy.policy_export (genv_policy ge)) ! (find_comp ge (Vptr b i))) as [exps |]; auto.
        destruct (in_dec comp_ident_eq_dec ((find_comp ge (Vptr b i)), i') imps);
          destruct (in_dec Pos.eq_dec i' exps); simpl; auto.
        now rewrite orb_true_r.
      * intros H.
        right; right.
        destruct (find_comp ge (Vptr b i)); try (now unfold default_compartment in n).
        -- simpl in H. apply Pos.eqb_neq in n0. rewrite n0 in H. simpl in H.
           destruct (invert_symbol ge b); try discriminate.
           exists i0. exists (c~1)%positive. split; auto. split; auto. simpl.
           destruct ((Policy.policy_import (genv_policy ge)) ! cp) as [imps |]; try discriminate.
           destruct (Policy.policy_export (genv_policy ge)); try discriminate.
           destruct (t0_2 ! c); try discriminate.
           apply andb_prop in H.
           destruct H as [H1 H2].
           apply proj_sumbool_true in H1.
           apply proj_sumbool_true in H2.
           auto.
        -- simpl in H. apply Pos.eqb_neq in n0. rewrite n0 in H. simpl in H.
           destruct (invert_symbol ge b); try discriminate.
           exists i0. exists (c~0)%positive. split; auto. split; auto. simpl.
           destruct ((Policy.policy_import (genv_policy ge)) ! cp) as [imps |]; try discriminate.
           destruct (Policy.policy_export (genv_policy ge)); try discriminate.
           destruct (t0_1 ! c); try discriminate.
           apply andb_prop in H.
           destruct H as [H1 H2].
           apply proj_sumbool_true in H1.
           apply proj_sumbool_true in H2.
           auto.
Qed.

End GENV.

(** * Commutation with program transformations *)

Section MATCH_GENVS.

Context {A B V W: Type} (R: globdef A V -> globdef B W -> Prop).

Record match_genvs (ge1: t A V) (ge2: t B W): Prop := {
  mge_next:
    genv_next ge2 = genv_next ge1;
  mge_symb:
    forall id, PTree.get id (genv_symb ge2) = PTree.get id (genv_symb ge1);
  mge_defs:
    forall b, option_rel R (PTree.get b (genv_defs ge1)) (PTree.get b (genv_defs ge2))
}.

Lemma add_global_match:
  forall ge1 ge2 id g1 g2,
  match_genvs ge1 ge2 ->
  R g1 g2 ->
  match_genvs (add_global ge1 (id, g1)) (add_global ge2 (id, g2)).
Proof.
  intros. destruct H. constructor; simpl; intros.
- congruence.
- rewrite mge_next0, ! PTree.gsspec. destruct (peq id0 id); auto.
- rewrite mge_next0, ! PTree.gsspec. destruct (peq b (genv_next ge1)).
  constructor; auto.
  auto.
Qed.

Lemma add_globals_match:
  forall gl1 gl2,
  list_forall2 (fun idg1 idg2 => fst idg1 = fst idg2 /\ R (snd idg1) (snd idg2)) gl1 gl2 ->
  forall ge1 ge2, match_genvs ge1 ge2 ->
  match_genvs (add_globals ge1 gl1) (add_globals ge2 gl2).
Proof.
  induction 1; intros; simpl.
  auto.
  destruct a1 as [id1 g1]; destruct b1 as [id2 g2]; simpl in *; destruct H; subst id2.
  apply IHlist_forall2. apply add_global_match; auto.
Qed.

End MATCH_GENVS.

Section MATCH_PROGRAMS.

Context {C F1 V1 F2 V2: Type} {LC: Linker C} {LF: Linker F1} {LV: Linker V1}.
Context {CF1: has_comp F1} {CF2: has_comp F2}.
Variable match_fundef: C -> F1 -> F2 -> Prop.
Variable match_varinfo: V1 -> V2 -> Prop.
Variable ctx: C.
Variable p: program F1 V1.
Variable tp: program F2 V2.
Context {match_fundef_comp: has_comp_match match_fundef}.
Hypothesis progmatch: match_program_gen match_fundef match_varinfo ctx p tp.

Lemma globalenvs_match:
  match_genvs (match_globdef match_fundef match_varinfo ctx) (globalenv p) (globalenv tp).
Proof.
  intros. apply add_globals_match. apply progmatch.
  constructor; simpl; intros; auto. rewrite ! PTree.gempty. constructor.
Qed.

Theorem find_def_match_2:
  forall b, option_rel (match_globdef match_fundef match_varinfo ctx)
                       (find_def (globalenv p) b) (find_def (globalenv tp) b).
Proof (mge_defs globalenvs_match).

Theorem find_def_match:
  forall b g,
  find_def (globalenv p) b = Some g ->
  exists tg,
  find_def (globalenv tp) b = Some tg /\ match_globdef match_fundef match_varinfo ctx g tg.
Proof.
  intros. generalize (find_def_match_2 b). rewrite H; intros R; inv R.
  exists y; auto.
Qed.

Theorem find_def_match_conv:
  forall b tg,
  find_def (globalenv tp) b = Some tg ->
  exists g,
  find_def (globalenv p) b = Some g /\ match_globdef match_fundef match_varinfo ctx g tg.
Proof.
  intros. generalize (find_def_match_2 b). rewrite H; intros R; inv R.
  exists x; auto.
Qed.

Theorem find_funct_ptr_match:
  forall b f,
  find_funct_ptr (globalenv p) b = Some f ->
  exists cunit tf,
  find_funct_ptr (globalenv tp) b = Some tf /\ match_fundef cunit f tf /\ linkorder cunit ctx.
Proof.
  intros. rewrite find_funct_ptr_iff in *. apply find_def_match in H.
  destruct H as (tg & P & Q). inv Q.
  exists ctx', f2; intuition auto. apply find_funct_ptr_iff; auto.
Qed.

Theorem find_funct_ptr_match_conv:
  forall b tf,
  find_funct_ptr (globalenv tp) b = Some tf ->
  exists cunit f,
  find_funct_ptr (globalenv p) b = Some f /\ match_fundef cunit f tf /\ linkorder cunit ctx.
Proof.
  intros. rewrite find_funct_ptr_iff in *. apply find_def_match_conv in H.
  destruct H as (tg & P & Q). inv Q.
  exists ctx', f1; intuition auto. apply find_funct_ptr_iff; auto.
Qed.

Theorem find_funct_match:
  forall v f,
  find_funct (globalenv p) v = Some f ->
  exists cunit tf,
  find_funct (globalenv tp) v = Some tf /\ match_fundef cunit f tf /\ linkorder cunit ctx.
Proof.
  intros. exploit find_funct_inv; eauto. intros [b EQ]. subst v.
  rewrite find_funct_find_funct_ptr in H.
  rewrite find_funct_find_funct_ptr.
  apply find_funct_ptr_match. auto.
Qed.

Theorem find_var_info_match:
  forall b v,
  find_var_info (globalenv p) b = Some v ->
  exists tv,
  find_var_info (globalenv tp) b = Some tv /\ match_globvar match_varinfo v tv.
Proof.
  intros. rewrite find_var_info_iff in *. apply find_def_match in H.
  destruct H as (tg & P & Q). inv Q.
  exists v2; split; auto. apply find_var_info_iff; auto.
Qed.

Theorem find_symbol_match:
  forall (s : ident),
  find_symbol (globalenv tp) s = find_symbol (globalenv p) s.
Proof.
  intros. destruct globalenvs_match. apply mge_symb0.
Qed.

Theorem senv_match:
  Senv.equiv (to_senv (globalenv p)) (to_senv (globalenv tp)).
Proof.
  red; simpl. repeat split.
- apply find_symbol_match.
- intros. unfold public_symbol. rewrite find_symbol_match.
  rewrite ! globalenv_public.
  destruct progmatch as (P & Q & R & S). rewrite R. auto.
- intros. unfold block_is_volatile.
  destruct globalenvs_match as [P Q R]. specialize (R b).
  unfold find_var_info, find_def.
  inv R; auto.
  inv H1; auto.
  inv H2; auto.
Qed.

Lemma store_init_data_list_match:
  forall idl m b ofs cp m',
  store_init_data_list (globalenv p) m b ofs idl cp = Some m' ->
  store_init_data_list (globalenv tp) m b ofs idl cp = Some m'.
Proof.
  induction idl; simpl; intros.
- auto.
- destruct (store_init_data (globalenv p) m b ofs a) as [m1|] eqn:S; try discriminate.
  assert (X: store_init_data (globalenv tp) m b ofs a cp = Some m1).
  { destruct a; auto. simpl; rewrite find_symbol_match; auto. }
  rewrite X. auto.
Qed.

Lemma alloc_globals_match:
  forall gl1 gl2, list_forall2 (match_ident_globdef match_fundef match_varinfo ctx) gl1 gl2 ->
  forall m m',
  alloc_globals (globalenv p) m gl1 = Some m' ->
  alloc_globals (globalenv tp) m gl2 = Some m'.
Proof.
  induction 1; simpl; intros.
- auto.
- destruct (alloc_global (globalenv p) m a1) as [m1|] eqn:?; try discriminate.
  assert (X: alloc_global (globalenv tp) m b1 = Some m1).
  { destruct a1 as [id1 g1]; destruct b1 as [id2 g2]; destruct H; simpl in *.
    subst id2. inv H2.
  - erewrite <- match_fundef_comp; eauto.
    erewrite <- match_fundef_comp; eauto.
  - inv H; simpl in *. simpl in Heqo.
    set (sz := init_data_list_size init) in *.
    destruct (Mem.alloc m _ 0 sz) as [m2 b] eqn:?.
    destruct (store_zeros m2 b 0 sz) as [m3|] eqn:?; try discriminate.
    destruct (store_init_data_list (globalenv p) m3 b 0 init) as [m4|] eqn:?; try discriminate.
    erewrite store_init_data_list_match; eauto.
  }
  rewrite X; eauto.
Qed.

Theorem init_mem_match:
  forall m, init_mem p = Some m -> init_mem tp = Some m.
Proof.
  unfold init_mem; intros.
  eapply alloc_globals_match; eauto. apply progmatch.
Qed.

Lemma match_genvs_find_comp:
  forall vf,
    find_comp (globalenv p) vf = find_comp (globalenv tp) vf.
Proof.
  intros vf.
  unfold find_comp.
  destruct vf; auto.
  destruct (find_funct_ptr (globalenv p) b) eqn:EQ.
  - apply find_funct_ptr_match in EQ as [? [? [H [? ?]]]]. rewrite H.
    rewrite match_fundef_comp; eauto.
  - destruct (find_funct_ptr (globalenv tp) b) eqn:EQ'.
    + apply find_funct_ptr_match_conv in EQ' as [? [? [H [? ?]]]]. congruence.
    + reflexivity.
Qed.

Lemma match_genvs_allowed_calls:
  forall cp vf,
    allowed_call (globalenv p) cp vf ->
    allowed_call (globalenv tp) cp vf.
Proof.
  intros cp vf.
  unfold allowed_call.
  intros [H1 | [H1 | H1]].
  - left. rewrite H1.
    unfold find_comp in *. destruct vf; auto.
    destruct (find_funct_ptr (globalenv p) b) eqn:EQ; auto.
    apply find_funct_ptr_match in EQ as [? [? [? [? ?]]]].
    rewrite H.
    erewrite match_fundef_comp; eauto.
    destruct (find_funct_ptr (globalenv tp) b) eqn:EQ'; auto.
    apply find_funct_ptr_match_conv in EQ' as [? [? [? [? ?]]]].
    congruence.
  - right; left. rewrite H1.
    unfold find_comp. destruct vf; auto.
    destruct (find_funct_ptr (globalenv p) b) eqn:EQ; auto.
    apply find_funct_ptr_match in EQ as [? [? [? [? ?]]]].
    rewrite H.
    erewrite match_fundef_comp; eauto.
    destruct (find_funct_ptr (globalenv tp) b) eqn:EQ'; auto.
    apply find_funct_ptr_match_conv in EQ' as [? [? [? [? ?]]]].
    congruence.
  - right; right.
    unfold allowed_cross_call in *. destruct vf; eauto.
    destruct H1 as [i0 [cp' [? [? [? ?]]]]].
    exists i0; exists cp'; split; [| split; [| split]].
    + apply find_invert_symbol. apply invert_find_symbol in H.
      rewrite find_symbol_match; eauto.
    + unfold find_comp in H0. unfold find_comp.
      destruct (find_funct_ptr (globalenv p) b) eqn:EQ; auto.
      apply find_funct_ptr_match in EQ as [? [? [? [? ?]]]].
      rewrite H3.
      inversion H0; subst.
      rewrite match_fundef_comp. eauto. eauto.
      destruct (find_funct_ptr (globalenv tp) b) eqn:EQ'; auto.
      apply find_funct_ptr_match_conv in EQ' as [? [? [? [? ?]]]].
      congruence.
    + destruct progmatch as [? [? [? EQPOL]]].
      destruct p, tp; simpl in *; subst.
      unfold globalenv. unfold globalenv in H1.
      simpl.
      simpl in H1. clear -H1 EQPOL.

      rewrite genv_pol_add_globals.
      rewrite genv_pol_add_globals in H1.
      unfold Policy.eqb in EQPOL. apply andb_prop in EQPOL.
      destruct EQPOL as [EQPOL1 EQPOL2].
      simpl in *.
      rewrite PTree.beq_correct in EQPOL2. specialize (EQPOL2 cp).
      destruct ((Policy.policy_import prog_pol0) ! cp);
        destruct ((Policy.policy_import prog_pol) ! cp); auto.
      destruct (Policy.list_cpt_id_eq l l0); subst; simpl in *; auto; try discriminate. contradiction.
    + destruct progmatch as [? [? [? EQPOL]]].
      destruct p, tp; simpl in *; subst.
      unfold globalenv. unfold globalenv in H2.
      simpl.
      simpl in H2. clear -H2 EQPOL.

      rewrite genv_pol_add_globals.
      rewrite genv_pol_add_globals in H2.
      unfold Policy.eqb in EQPOL. apply andb_prop in EQPOL.
      destruct EQPOL as [EQPOL1 EQPOL2].
      simpl in *.
      rewrite PTree.beq_correct in EQPOL1.
      remember (match find_funct_ptr (add_globals (empty_genv F1 V1 prog_public prog_pol) prog_defs) b with
      | Some f => comp_of f
      | None => default_compartment
      end) as cp'.
      (* destruct (find_funct_ptr (add_globals (empty_genv F1 V1 prog_public prog_pol) prog_defs) b) *)
      specialize (EQPOL1 cp').
      destruct ((Policy.policy_export prog_pol0) ! cp');
        destruct ((Policy.policy_export prog_pol) ! cp'); subst cp'; auto; try contradiction.
      destruct (Policy.list_id_eq l l0); subst; simpl in *; auto; try discriminate.
Qed.

Lemma match_genvs_type_of_call:
  forall cp cp',
    type_of_call (globalenv p) cp cp' (* (find_comp (globalenv p) vf) *) =
      type_of_call (globalenv tp) cp cp' (* (find_comp (globalenv tp) vf) *).
Proof.
  intros. reflexivity.
Qed.

End MATCH_PROGRAMS.

(** Special case for partial transformations that do not depend on the compilation unit *)

Section TRANSFORM_PARTIAL.

Context {A B V: Type} {LA: Linker A} {LV: Linker V}.
Context {CA: has_comp A} {CB: has_comp B}.
Context {transf: A -> res B} {p: program A V} {tp: program B V}.
Context {CAB: has_comp_transl_partial transf}.
Hypothesis progmatch: match_program (fun cu f tf => transf f = OK tf) eq p tp.

Theorem find_funct_ptr_transf_partial:
  forall b f,
  find_funct_ptr (globalenv p) b = Some f ->
  exists tf,
  find_funct_ptr (globalenv tp) b = Some tf /\ transf f = OK tf.
Proof.
  intros. exploit (find_funct_ptr_match progmatch); eauto.
  intros (cu & tf & P & Q & R); exists tf; auto.
Qed.

Theorem find_funct_ptr_transf_partial_conv:
  forall b tf,
  find_funct_ptr (globalenv tp) b = Some tf ->
  exists f,
  find_funct_ptr (globalenv p) b = Some f /\ transf f = OK tf.
Proof.
  intros. exploit (find_funct_ptr_match_conv progmatch); eauto.
  intros (cu & f & P & Q & R); exists f; auto.
Qed.

Lemma find_comp_transf_partial:
  forall v,
  find_comp (globalenv p) v = find_comp (globalenv tp) v.
Proof.
  unfold find_comp. intros v.
  destruct v as [| | | | |b ofs]; trivial.
  destruct (find_funct_ptr (globalenv p) b) as [f|] eqn:Ef; try easy.
  (* intros Ecp. *)
  destruct (find_funct_ptr_transf_partial _ Ef) as (tf & H1 & H2).
  now rewrite H1, <- (comp_transl_partial _ H2).
  destruct (find_funct_ptr (globalenv tp) b) eqn:Etf; auto.
  destruct (find_funct_ptr_transf_partial_conv _ Etf) as (f & H1 & H2).
  congruence.
Qed.

Theorem find_funct_transf_partial:
  forall v f,
  find_funct (globalenv p) v = Some f ->
  exists tf,
  find_funct (globalenv tp) v = Some tf /\ transf f = OK tf.
Proof.
  intros. exploit (find_funct_match progmatch); eauto.
  intros (cu & tf & P & Q & R); exists tf; auto.
Qed.

Theorem find_symbol_transf_partial:
  forall (s : ident),
  find_symbol (globalenv tp) s = find_symbol (globalenv p) s.
Proof.
  intros. eapply (find_symbol_match progmatch).
Qed.

Theorem senv_transf_partial:
  Senv.equiv (to_senv (globalenv p)) (to_senv (globalenv tp)).
Proof.
  intros. eapply (senv_match progmatch).
Qed.

Theorem init_mem_transf_partial:
  forall m, init_mem p = Some m -> init_mem tp = Some m.
Proof.
  eapply (init_mem_match progmatch).
Qed.

Theorem allowed_call_transf_partial:
  forall cp vf,
    allowed_call (globalenv p) cp vf -> allowed_call (globalenv tp) cp vf.
Proof.
  eapply (match_genvs_allowed_calls progmatch).
Qed.

Theorem type_of_call_transf_partial:
  forall cp cp',
    type_of_call (globalenv p) cp cp' =
      type_of_call (globalenv tp) cp cp'.
Proof.
  eapply (match_genvs_type_of_call).
Qed.

End TRANSFORM_PARTIAL.

(** Special case for total transformations that do not depend on the compilation unit *)

Section TRANSFORM_TOTAL.

Context {A B V: Type} {LA: Linker A} {LV: Linker V}.
Context {CA: has_comp A} {CB: has_comp B}.
Context {transf: A -> B} {p: program A V} {tp: program B V}.
Context {CAB: has_comp_transl transf}.
Hypothesis progmatch: match_program (fun cu f tf => tf = transf f) eq p tp.

Theorem find_funct_ptr_transf:
  forall b f,
  find_funct_ptr (globalenv p) b = Some f ->
  find_funct_ptr (globalenv tp) b = Some (transf f).
Proof.
  intros. exploit (find_funct_ptr_match progmatch); eauto.
  intros (cu & tf & P & Q & R). congruence.
Qed.

Theorem find_funct_transf:
  forall v f,
  find_funct (globalenv p) v = Some f ->
  find_funct (globalenv tp) v = Some (transf f).
Proof.
  intros. exploit (find_funct_match progmatch); eauto.
  intros (cu & tf & P & Q & R). congruence.
Qed.

Theorem find_symbol_transf:
  forall (s : ident),
  find_symbol (globalenv tp) s = find_symbol (globalenv p) s.
Proof.
  intros. eapply (find_symbol_match progmatch).
Qed.

Theorem senv_transf:
  Senv.equiv (to_senv (globalenv p)) (to_senv (globalenv tp)).
Proof.
  intros. eapply (senv_match progmatch).
Qed.

Theorem init_mem_transf:
  forall m, init_mem p = Some m -> init_mem tp = Some m.
Proof.
  eapply (init_mem_match progmatch).
Qed.

Theorem allowed_call_transf:
  forall cp vf,
    allowed_call (globalenv p) cp vf -> allowed_call (globalenv tp) cp vf.
Proof.
  eapply (match_genvs_allowed_calls progmatch).
Qed.

Lemma find_comp_transf:
  forall v,
  find_comp (globalenv p) v = find_comp (globalenv tp) v.
Proof.
  unfold find_comp. intros v.
  destruct v as [| | | | |b ofs]; trivial.
  destruct (find_funct_ptr (globalenv p) b) as [f|] eqn:Ef; try easy.
  (* intros Ecp. *)
  rewrite (find_funct_ptr_transf _ Ef).
  now rewrite comp_transl.
  destruct (find_funct_ptr (globalenv tp) b) eqn:Etf; auto.
  eapply (find_funct_ptr_match_conv progmatch) in Etf as [? [? [? [? ?]]]].
  congruence.
Qed.

Theorem type_of_call_transf:
  forall cp cp',
    type_of_call (globalenv p) cp cp' =
      type_of_call (globalenv tp) cp cp'.
Proof.
  eapply (match_genvs_type_of_call).
Qed.

End TRANSFORM_TOTAL.

End Genv.

Coercion Genv.to_senv: Genv.t >-> Senv.t.
