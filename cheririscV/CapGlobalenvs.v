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
Require Import Axioms Coqlib Errors Maps Linking.
Require Import CapAST.
Require Import Integers Floats OCapValues CapMemory.

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.

Fixpoint find_index_rec {A: Type} (f: A -> bool) (l:list A) (i: nat) : option nat :=
  match l with
  | nil => None
  | x :: tl => if f x then Some i else find_index_rec f tl (S i)
  end.
Definition find_index {A: Type} (f: A -> bool) (l:list A) : option nat := find_index_rec f l 0.

Local Open Scope pair_scope.
Local Open Scope monad_scope.

Set Implicit Arguments.

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
  intros. red. lia.
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
  intros. destruct glob;simpl;try lia.
Qed.

Context {CF: has_comp F}.

(** The type of global environments. *)

Definition cap_to_Z_lo (ptr: occap) : Z :=
  (Ptrofs.unsigned (get_lo ptr)).

Record t: Type := mkgenv {
  genv_public: list ident;              (**r which symbol names are public *)
  genv_symb: PTree.t occap;             (**r mapping symbol -> capability *)
  genv_defs: PTree.t (globdef F V);     (**r mapping the lower bound of cap -> definition *)
  genv_heaps: CompTree.t occap;            (**r mapping from compartments to heap capabilities *)
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
    | None   => AST.COMP.bottom
    end
  | _ => AST.COMP.bottom
  end.

Lemma find_comp_null:
  forall ge, find_comp ge Vnullptr = AST.COMP.bottom.
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
  lia.
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
    subst. inv H2. simpl in *. lia.
  - apply genv_symb_range0 in H2.
    apply Ptrofs.same_if_eq in B. subst.  
    lia.
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
    lia.
  - apply genv_defs_range0 in H2.
    apply Ptrofs.same_if_eq in B.
    apply Ptrofs.same_if_eq in S;subst.
    lia.
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
    rewrite S in H2. lia.
  - inversion H1. subst c. apply genv_symb_range0 in H0 as ?.
    rewrite <- B, H3 in H2. lia.
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
  lia.
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
  lia.
Defined.
Next Obligation.
  remember (build_stack_capability (genv_next ge)) as cap.
  pose proof (build_stack_capability_inv (genv_next ge)) as [B [LE [Size S]]].
  rewrite <- Heqcap in *.
  destruct cap,o;[clear S|easy..].
  unfold get_region_size in Size. simpl in *.
  apply (ge.(genv_defs_range)) in H0.
  apply Ptrofs.same_if_eq in B. subst.
  lia.
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
  apply Ptrofs.same_if_eq in B. subst. lia.
Defined.

Program Definition add_heap (c: compartment) (ge: t): option t :=
  let cap := build_heap_capability ge.(genv_next) in
  if zlt (Ptrofs.unsigned (get_hi cap)) (Ptrofs.unsigned ge.(genv_end)) then
    Some (@mkgenv
      ge.(genv_public)
      ge.(genv_symb)
      ge.(genv_defs)
      (CompTree.set c cap ge.(genv_heaps))
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
  lia.
Defined.
Next Obligation.
  remember (build_heap_capability (genv_next ge)) as cap.
  pose proof (build_heap_capability_inv (genv_next ge)) as [B [LE [Size S]]].
  rewrite <- Heqcap in *.
  destruct cap,o;[clear S|easy..].
  unfold get_region_size in Size. simpl in *.
  apply (ge.(genv_defs_range)) in H0.
  apply Ptrofs.same_if_eq in B. subst.
  lia.
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
  apply Ptrofs.same_if_eq in B. subst. lia.
Defined.

Definition comp_has_heap (ge: t) (c: compartment) : Prop :=
  match CompTree.get c ge.(genv_heaps) with
  | Some h => True
  | None => False
  end.
Lemma comp_has_heap_dec: forall ge c, {comp_has_heap ge c} + {~ comp_has_heap ge c}.
Proof.
  intros. unfold comp_has_heap.
  destruct (CompTree.get c ge.(genv_heaps));auto.
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
  lia.
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

Definition bytes_of_init_data (i: init_data): list memval :=
  match i with
  | Init_int8 n => inj_bytes (encode_int 1%nat (Int.unsigned n))
  | Init_int16 n => inj_bytes (encode_int 2%nat (Int.unsigned n))
  | Init_int32 n => inj_bytes (encode_int 4%nat (Int.unsigned n))
  | Init_int64 n => inj_bytes (encode_int 8%nat (Int64.unsigned n))
  | Init_float32 n => inj_bytes (encode_int 4%nat (Int.unsigned (Float32.to_bits n)))
  | Init_float64 n => inj_bytes (encode_int 8%nat (Int64.unsigned (Float.to_bits n)))
  | Init_space n => List.repeat (Byte Byte.zero) (Z.to_nat n)
  | Init_addrof id ofs =>
      match find_symbol ge id with
      | Some c => inj_value (if Archi.ptr64 then Q128 else Q64) (OCVcap c)
      | None   => List.repeat Undef (if Archi.ptr64 then 16%nat else 8%nat)
      end
  end.

Remark cap_init_data_size_addrof:
  forall id ofs, cap_init_data_size (Init_addrof id ofs) = size_chunk CMcap.
Proof.
  intros. unfold CMcap. simpl. destruct Archi.ptr64; auto.
Qed.

Fixpoint bytes_of_init_data_list (il: list init_data): list memval :=
  match il with
  | nil => nil
  | i :: il => bytes_of_init_data i ++ bytes_of_init_data_list il
  end.

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
  match CompTree.get comp (genv_heaps ge) with
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

Definition init_mem (p: program F V) (gstart gend: ptrofs) :=
  do GL <- (globalenv p gstart gend);
  do M1 <- alloc_globals GL Mem.empty p.(prog_defs);
  do M2 <- alloc_stack GL M1;
  alloc_heaps GL M2 p.(prog_defs).


(* Allowed cross-compartment calls *)
Definition allowed_cross_call (ge: t) (cp: compartment) (vf: ocval) :=
  match vf with
  | OCVcap c =>
    exists i cp',
    invert_symbol ge c = Some i /\
    find_comp ge vf = cp' /\
    match CompTree.get cp (Policy.policy_import ge.(genv_policy)) with
    | Some l => In (cp', i) l
    | None => False
    end /\
    match CompTree.get cp' (Policy.policy_export ge.(genv_policy)) with
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
  if COMP.comp_eqb cp cp' then InternalCall
  else if COMP.comp_eqb cp' AST.COMP.bottom then DefaultCompartmentCall
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
Definition allowed_call (ge: t) (cp: compartment) (vf: ocval) :=
  AST.COMP.bottom = find_comp ge vf \/ (* TODO: does this mean we allow all compartment to perform IO calls? *)
  cp = find_comp ge vf \/
  allowed_cross_call ge cp vf.

Lemma comp_ident_eq_dec: forall (x y: compartment * ident),
    {x = y} + {x <> y}.
Proof.
  intros x y.
  decide equality.
  eapply Pos.eq_dec.
  eapply COMP.cp_eq_dec.
Qed.

Definition allowed_call_b (ge: t) (cp: compartment) (vf: ocval): bool :=
  match find_comp ge vf with
  | c => COMP.comp_eqb c AST.COMP.bottom
             || COMP.comp_eqb c cp
             || match vf with
               | OCVcap ca => match invert_symbol ge ca with
                            | Some i =>
                              match CompTree.get cp (Policy.policy_import ge.(genv_policy)) with
                              | Some imps =>
                                match CompTree.get cp (Policy.policy_export ge.(genv_policy)) with
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
  remember (find_comp ge (OCVcap o)) as c.
  destruct (COMP.cp_eq_dec AST.COMP.bottom c); subst.
  - rewrite <- e. split; auto.
  - destruct (COMP.cp_eq_dec (find_comp ge (OCVcap o)) cp); subst.
    (* destruct (Pos.eq_dec c cp); subst. *)
    + rewrite COMP.comp_eqb_refl. rewrite orb_true_r. simpl. split; auto.
    + split; auto.
      * intros H. destruct H as [? | [? | ?]]; try congruence.
        destruct H as [i' [cp' [H1 [H2 [H3 H4]]]]].
        rewrite H1. inv H2.
        destruct (CompTree.get cp (Policy.policy_import (genv_policy ge))) as [imps |]; auto.
        destruct (CompTree.get (find_comp ge (OCVcap o)) (Policy.policy_export (genv_policy ge))) as [exps |]; auto.
        destruct (in_dec comp_ident_eq_dec ((find_comp ge (OCVcap o)), i') imps);
          destruct (in_dec Pos.eq_dec i' exps); simpl; auto.
        (* CHECK ME: how can we complete this proof? *)
        (* now rewrite orb_true_r. *)
        admit.
      * intros H.
        right; right.
        destruct (find_comp ge (OCVcap o)); try (now unfold default_compartment in n).
        -- simpl in H. apply COMP.comp_eqb_neq in n0.
           (* CHECK ME: how can we complete this proof? *)
           (* rewrite n0 in H. simpl in H.
           destruct (invert_symbol ge o); try discriminate.
           exists i. exists (c~1)%positive. split; auto. split; auto. simpl.
           destruct (CompTree.get cp (Policy.policy_import (genv_policy ge))) as [imps |]; try discriminate.
           destruct (Policy.policy_export (genv_policy ge)); try discriminate.
           destruct ((PTree.Nodes t0) ! (c~1)); try discriminate.
           apply andb_prop in H.
           destruct H as [H1 H2].
           apply proj_sumbool_true in H1.
           apply proj_sumbool_true in H2.
           auto. *)
           admit.
        -- simpl in H. apply COMP.comp_eqb_neq in n0. rewrite n0 in H. simpl in H.
           destruct (invert_symbol ge o); try discriminate.
           exists i.
           (* CHECK ME: how can we complete this proof? *)
           (* exists (c~0)%positive. split; auto. split; auto. simpl.
           destruct (CompTree.get cp (Policy.policy_import (genv_policy ge))) as [imps |]; try discriminate.
           destruct (Policy.policy_export (genv_policy ge)); try discriminate.
           destruct ((PTree.Nodes t0) ! (c~0)); try discriminate.
           apply andb_prop in H.
           destruct H as [H1 H2].
           apply proj_sumbool_true in H1.
           apply proj_sumbool_true in H2.
           auto. *)
           admit.
Admitted.

End GENV.

End Genv.

Coercion Genv.to_senv: Genv.t >-> Senv.t.
