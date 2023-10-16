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

(** This file defines a number of data types and operations used in
  the abstract syntax trees of many of the intermediate languages. *)

Require Import String.
Require Import Coqlib Maps Errors Integers Floats.
Require Archi.

Set Implicit Arguments.

(** * Syntactic elements *)

(** Identifiers (names of local variables, of global symbols and functions,
  etc) are represented by the type [positive] of positive integers. *)

Definition ident := positive.

Definition ident_eq := peq.

(** Programs entities can be grouped into compartments, which remain isolated
  from each other during execution. *)

Definition compartment : Type := positive.
Definition privileged_compartment : compartment := 1%positive.
Notation default_compartment := privileged_compartment. (* TODO: fix this *)
Definition eq_compartment (c1 c2: compartment) :=
  peq c1 c2.

(** Calls into certain compartments cannot be inlined or transformed into tail
  calls because they need to know who the calling compartment is.  These
  compartments are recorded in the following map. *)

Definition needs_calling_comp_map : PMap.t bool :=
  let comps := privileged_compartment :: nil in
  fold_left (fun m cp => PMap.set cp true m) comps (PMap.init false).

Definition needs_calling_comp (cp: compartment) : bool :=
  PMap.get cp needs_calling_comp_map.

Set Typeclasses Strict Resolution.
(** An instance of [has_comp] represents a syntactic entity that belongs to a
  compartment. We turn on strict resolution to prevent typeclass inference from
  triggering when the type parameter is still unknown.  *)
Class has_comp (T: Type) := comp_of: T -> compartment.
Unset Typeclasses Strict Resolution.

Class has_comp_transl {T S: Type}
                      {CT: has_comp T} {CS: has_comp S}
                      (f : T -> S) :=
  comp_transl:
    forall x, comp_of (f x) = comp_of x.

Class has_comp_transl_partial {T S: Type}
                              {CT: has_comp T} {CS: has_comp S}
                              (f : T -> res S) :=
  comp_transl_partial:
    forall x y, f x = OK y -> comp_of x = comp_of y.

Class has_comp_match {C T S: Type} {CT: has_comp T} {CS: has_comp S}
                     (R : C -> T -> S -> Prop) :=
  comp_match:
    forall c x y, R c x y -> comp_of x = comp_of y.

Instance has_comp_transl_match:
  forall {C T S: Type}
         {CT: has_comp T} {CS: has_comp S}
         (f: T -> S) {Cf: has_comp_transl f},
  has_comp_match (fun (c : C) x y => y = f x).
Proof. now intros C T S ???? c x y ->; rewrite comp_transl. Qed.

Instance has_comp_transl_partial_match:
  forall {C T S: Type}
         {CT: has_comp T} {CS: has_comp S}
         (f: T -> res S) {Cf: has_comp_transl_partial f},
  has_comp_match (fun (c : C) x y => f x = OK y).
Proof.
  intros C T S ???? c. exact comp_transl_partial.
Qed.

Instance has_comp_transl_match_contextual:
  forall {C D T S: Type}
         {CT: has_comp T} {CS: has_comp S}
         (f: D -> T -> S) {Cf: forall d, has_comp_transl (f d)}
         (g: C -> D),
  has_comp_match (fun (c : C) x y => y = f (g c) x).
Proof.
now intros C D T S CT CS f Cf g ??? ->; rewrite comp_transl.
Qed.

Instance has_comp_transl_partial_match_contextual:
  forall {C D T S: Type}
         {CT: has_comp T} {CS: has_comp S}
         (f: D -> T -> res S) {Cf: forall d, has_comp_transl_partial (f d)}
         (g: C -> D),
  has_comp_match (fun (c : C) x y => f (g c) x = OK y).
Proof.
intros C D T S CT CS f Cf g c. exact comp_transl_partial.
Qed.

(** The intermediate languages are weakly typed, using the following types: *)

Inductive typ : Type :=
  | Tint                (**r 32-bit integers or pointers *)
  | Tfloat              (**r 64-bit double-precision floats *)
  | Tlong               (**r 64-bit integers *)
  | Tsingle             (**r 32-bit single-precision floats *)
  | Tany32              (**r any 32-bit value *)
  | Tany64.             (**r any 64-bit value, i.e. any value *)

Lemma typ_eq: forall (t1 t2: typ), {t1=t2} + {t1<>t2}.
Proof. decide equality. Defined.
Global Opaque typ_eq.

Definition list_typ_eq: forall (l1 l2: list typ), {l1=l2} + {l1<>l2}
                     := list_eq_dec typ_eq.

Definition Tptr : typ := if Archi.ptr64 then Tlong else Tint.

Definition typesize (ty: typ) : Z :=
  match ty with
  | Tint => 4
  | Tfloat => 8
  | Tlong => 8
  | Tsingle => 4
  | Tany32 => 4
  | Tany64 => 8
  end.

Lemma typesize_pos: forall ty, typesize ty > 0.
Proof. destruct ty; simpl; lia. Qed.

Lemma typesize_Tptr: typesize Tptr = if Archi.ptr64 then 8 else 4.
Proof. unfold Tptr; destruct Archi.ptr64; auto. Qed.

(** All values of size 32 bits are also of type [Tany32].  All values
  are of type [Tany64].  This corresponds to the following subtyping
  relation over types. *)

Definition subtype (ty1 ty2: typ) : bool :=
  match ty1, ty2 with
  | Tint, Tint => true
  | Tlong, Tlong => true
  | Tfloat, Tfloat => true
  | Tsingle, Tsingle => true
  | (Tint | Tsingle | Tany32), Tany32 => true
  | _, Tany64 => true
  | _, _ => false
  end.

Fixpoint subtype_list (tyl1 tyl2: list typ) : bool :=
  match tyl1, tyl2 with
  | nil, nil => true
  | ty1::tys1, ty2::tys2 => subtype ty1 ty2 && subtype_list tys1 tys2
  | _, _ => false
  end.

(** To describe the values returned by functions, we use the more precise
    types below. *)

Inductive rettype : Type :=
  | Tret (t: typ)                       (**r like type [t] *)
  | Tint8signed                         (**r 8-bit signed integer *)
  | Tint8unsigned                       (**r 8-bit unsigned integer *)
  | Tint16signed                        (**r 16-bit signed integer *)
  | Tint16unsigned                      (**r 16-bit unsigned integer *)
  | Tvoid.                              (**r no value returned *)

Coercion Tret: typ >-> rettype.

Lemma rettype_eq: forall (t1 t2: rettype), {t1=t2} + {t1<>t2}.
Proof. generalize typ_eq; decide equality. Defined.
Global Opaque rettype_eq.

Definition proj_rettype (r: rettype) : typ :=
  match r with
  | Tret t => t
  | Tint8signed | Tint8unsigned | Tint16signed | Tint16unsigned => Tint
  | Tvoid => Tint
  end.

(** Additionally, function definitions and function calls are annotated
  by function signatures indicating:
- the number and types of arguments;
- the type of the returned value;
- additional information on which calling convention to use.

These signatures are used in particular to determine appropriate
calling conventions for the function. *)

Record calling_convention : Type := mkcallconv {
  cc_vararg: option Z;  (**r variable-arity function (+ number of fixed args) *)
  cc_unproto: bool;     (**r old-style unprototyped function *)
  cc_structret: bool    (**r function returning a struct  *)
}.

Definition cc_default :=
  {| cc_vararg := None; cc_unproto := false; cc_structret := false |}.

Definition calling_convention_eq (x y: calling_convention) : {x=y} + {x<>y}.
Proof.
  decide equality; try (apply bool_dec). decide equality; apply Z.eq_dec.
Defined.
Global Opaque calling_convention_eq.

Record signature : Type := mksignature {
  sig_args: list typ;
  sig_res: rettype;
  sig_cc: calling_convention
}.

Definition proj_sig_res (s: signature) : typ := proj_rettype s.(sig_res).

Definition signature_eq: forall (s1 s2: signature), {s1=s2} + {s1<>s2}.
Proof.
  generalize rettype_eq, list_typ_eq, calling_convention_eq; decide equality.
Defined.
Global Opaque signature_eq.

Definition signature_main :=
  {| sig_args := nil; sig_res := Tint; sig_cc := cc_default |}.

(** Memory accesses (load and store instructions) are annotated by
  a ``memory chunk'' indicating the type, size and signedness of the
  chunk of memory being accessed. *)

Inductive memory_chunk : Type :=
  | Mint8signed     (**r 8-bit signed integer *)
  | Mint8unsigned   (**r 8-bit unsigned integer *)
  | Mint16signed    (**r 16-bit signed integer *)
  | Mint16unsigned  (**r 16-bit unsigned integer *)
  | Mint32          (**r 32-bit integer, or pointer *)
  | Mint64          (**r 64-bit integer *)
  | Mfloat32        (**r 32-bit single-precision float *)
  | Mfloat64        (**r 64-bit double-precision float *)
  | Many32          (**r any value that fits in 32 bits *)
  | Many64.         (**r any value *)

Definition chunk_eq: forall (c1 c2: memory_chunk), {c1=c2} + {c1<>c2}.
Proof. decide equality. Defined.
Global Opaque chunk_eq.

Definition Mptr : memory_chunk := if Archi.ptr64 then Mint64 else Mint32.

(** The type (integer/pointer or float) of a chunk. *)

Definition type_of_chunk (c: memory_chunk) : typ :=
  match c with
  | Mint8signed => Tint
  | Mint8unsigned => Tint
  | Mint16signed => Tint
  | Mint16unsigned => Tint
  | Mint32 => Tint
  | Mint64 => Tlong
  | Mfloat32 => Tsingle
  | Mfloat64 => Tfloat
  | Many32 => Tany32
  | Many64 => Tany64
  end.

Lemma type_of_Mptr: type_of_chunk Mptr = Tptr.
Proof. unfold Mptr, Tptr; destruct Archi.ptr64; auto. Qed.

(** Same, as a return type. *)

Definition rettype_of_chunk (c: memory_chunk) : rettype :=
  match c with
  | Mint8signed => Tint8signed
  | Mint8unsigned => Tint8unsigned
  | Mint16signed => Tint16signed
  | Mint16unsigned => Tint16unsigned
  | Mint32 => Tint
  | Mint64 => Tlong
  | Mfloat32 => Tsingle
  | Mfloat64 => Tfloat
  | Many32 => Tany32
  | Many64 => Tany64
  end.

Lemma proj_rettype_of_chunk:
  forall chunk, proj_rettype (rettype_of_chunk chunk) = type_of_chunk chunk.
Proof.
  destruct chunk; auto.
Qed.

(** The chunk that is appropriate to store and reload a value of
  the given type, without losing information. *)

Definition chunk_of_type (ty: typ) :=
  match ty with
  | Tint => Mint32
  | Tfloat => Mfloat64
  | Tlong => Mint64
  | Tsingle => Mfloat32
  | Tany32 => Many32
  | Tany64 => Many64
  end.

Lemma chunk_of_Tptr: chunk_of_type Tptr = Mptr.
Proof. unfold Mptr, Tptr; destruct Archi.ptr64; auto. Qed.

(** Initialization data for global variables. *)

Inductive init_data: Type :=
  | Init_int8: int -> init_data
  | Init_int16: int -> init_data
  | Init_int32: int -> init_data
  | Init_int64: int64 -> init_data
  | Init_float32: float32 -> init_data
  | Init_float64: float -> init_data
  | Init_space: Z -> init_data
  | Init_addrof: ident -> ptrofs -> init_data.  (**r address of symbol + offset *)

Definition init_data_size (i: init_data) : Z :=
  match i with
  | Init_int8 _ => 1
  | Init_int16 _ => 2
  | Init_int32 _ => 4
  | Init_int64 _ => 8
  | Init_float32 _ => 4
  | Init_float64 _ => 8
  | Init_addrof _ _ => if Archi.ptr64 then 8 else 4
  | Init_space n => Z.max n 0
  end.

Fixpoint init_data_list_size (il: list init_data) {struct il} : Z :=
  match il with
  | nil => 0
  | i :: il' => init_data_size i + init_data_list_size il'
  end.

Lemma init_data_size_pos:
  forall i, init_data_size i >= 0.
Proof.
  destruct i; simpl; try extlia. destruct Archi.ptr64; lia.
Qed.

Lemma init_data_list_size_pos:
  forall il, init_data_list_size il >= 0.
Proof.
  induction il; simpl. lia. generalize (init_data_size_pos a); lia.
Qed.

(** Information attached to global variables. *)

Record globvar (V: Type) : Type := mkglobvar {
  gvar_info: V;                    (**r language-dependent info, e.g. a type *)
  gvar_comp: compartment;          (**r the compartment where the variable resides *)
  gvar_init: list init_data;       (**r initialization data *)
  gvar_readonly: bool;             (**r read-only variable? (const) *)
  gvar_volatile: bool              (**r volatile variable? *)
}.

Instance has_comp_globvar V : has_comp (globvar V) := @gvar_comp _.

(** Policies are used to decide whether a given call is allowed or not.

    For each compartment, a policy defines a list of exported procedures
    and a list of procedures imported from other compartments. Procedures are
    refered to by their public identifier.

    This module doesn't define what it means for a call to be allowed or rejected;
    instead, this is defined in common/Globalenv.v
 *)
Module Policy.

  Record t: Type := mkpolicy {
    policy_export: PTree.t (list ident);
    policy_import: PTree.t (list (compartment * ident))
  }.

  Definition in_pub_exports (pol: t) (pubs: list ident) : Prop :=
    forall cp exps, (policy_export pol) ! cp = Some exps ->
    forall id, In id exps -> In id pubs.

  Definition in_pub_imports (pol: t) (pubs: list ident) : Prop :=
    forall cp imps, (policy_import pol) ! cp = Some imps ->
    forall cp' id, In (cp', id) imps -> In id pubs.

  Definition in_pub (pol: t) (pubs: list ident) : Prop :=
    in_pub_exports pol pubs /\ in_pub_imports pol pubs.

  (* FIXME: If we run this code every time that we have trouble checking that a
     policy is well-formed, we might be running spurious filters, which could
     have performance impacts in compilation.  *)
  Definition enforce_in_pub (pol: t) (pubs: list ident) :=
    {| policy_export :=
        PTree.map1
          (filter (fun id : ident => in_dec ident_eq id pubs))
          pol.(policy_export);
       policy_import :=
        PTree.map1
          (filter (fun p : compartment * ident => in_dec ident_eq (snd p) pubs))
          pol.(policy_import);
    |}.

  Lemma enforce_in_pub_correct :
    forall (pol: t) (pubs: list ident),
      in_pub (enforce_in_pub pol pubs) pubs.
  Proof.
    split.
    - intros cp imps. simpl. rewrite PTree.gmap1.
      destruct PTree.get as [exps|] eqn:pol_cp; simpl; try congruence.
      intros e. injection e as e. rewrite <- e. clear e.
      intros id. rewrite filter_In. intros [_ Hin]. now destruct in_dec.
    - intros cp exps. simpl. rewrite PTree.gmap1.
      destruct PTree.get as [imps|] eqn:pol_cp; simpl; try congruence.
      intros e. injection e as e. rewrite <- e. clear e.
      intros cp' id. rewrite filter_In. simpl. intros [_ Hin].
      now destruct in_dec.
  Qed.

  (* The empty policy is the policy where there is no imported procedure and no exported procedure for all compartments *)
  Definition empty_pol: t := mkpolicy (PTree.empty (list ident)) (PTree.empty (list (compartment * ident))).

  (* Decidable equality for the elements contained in the policies *)
  Definition list_id_eq: forall (x y: list ident),
      {x = y} + {x <> y}.
  Proof.
    intros x y.
    decide equality.
    apply Pos.eq_dec.
  Qed.

  Definition list_cpt_id_eq: forall (x y: list (compartment * ident)),
      {x = y} + {x <> y}.
  Proof.
    intros x y.
    decide equality.
    decide equality.
    apply Pos.eq_dec.
    apply Pos.eq_dec.
  Qed.

  (* Defines an equivalence between two policies: two policies are equivalent iff for each compartment,
     they define the same exported and imported procedures *)
  Definition eqb (t1 t2: t): bool :=
    PTree.beq list_id_eq t1.(policy_export) t2.(policy_export) &&
    PTree.beq list_cpt_id_eq t1.(policy_import) t2.(policy_import).

  (* Properties of an equivalence relation: reflexivity, commutativity, transitivity *)
  Lemma eqb_refl: forall pol, eqb pol pol = true.
  Proof.
    intros pol.
    unfold eqb.
    assert (PTree.beq (fun x y : list ident => list_id_eq x y) (policy_export pol) (policy_export pol) = true).
    rewrite PTree.beq_correct.
    intros x. destruct ((policy_export pol) ! x); auto.
    destruct (list_id_eq l l); auto.
    rewrite H. simpl.
    rewrite PTree.beq_correct.
    intros x. destruct ((policy_import pol) ! x); auto.
    destruct (list_cpt_id_eq l l); auto.
  Qed.

  Lemma eqb_comm: forall pol pol', eqb pol pol' = true -> eqb pol' pol = true.
  Proof.
    intros pol pol' H.
    unfold eqb in *.
    apply andb_prop in H as [H1 H2].
    assert (H1': PTree.beq (fun x y : list ident => list_id_eq x y) (policy_export pol') (policy_export pol) = true).
    rewrite PTree.beq_correct. rewrite PTree.beq_correct in H1.
    intros x. specialize (H1 x). destruct ((policy_export pol') ! x); auto.
    destruct ((policy_export pol) ! x); auto.
    destruct (list_id_eq l0 l); subst.
    destruct (list_id_eq l l); auto.
    destruct (list_id_eq l l0); auto.
    assert (H2': PTree.beq (fun x y => list_cpt_id_eq x y) (policy_import pol') (policy_import pol) = true).
    rewrite PTree.beq_correct. rewrite PTree.beq_correct in H2.
    intros x. specialize (H2 x). destruct ((policy_import pol') ! x); auto.
    destruct ((policy_import pol) ! x); auto.
    destruct (list_cpt_id_eq l0 l); subst.
    destruct (list_cpt_id_eq l l); auto.
    destruct (list_cpt_id_eq l l0); auto.
    rewrite H1', H2'. auto.
  Qed.

  Lemma eqb_trans: forall pol pol' pol'', eqb pol pol' = true -> eqb pol' pol'' = true -> eqb pol pol'' = true.
  Proof.
    intros pol pol' pol'' H1 H2.
    unfold eqb in *.
    apply andb_prop in H1 as [H1 H1'].
    apply andb_prop in H2 as [H2 H2'].
    assert (H3: PTree.beq (fun x y : list ident => list_id_eq x y) (policy_export pol) (policy_export pol'') = true).
    { clear -H1 H2.
      rewrite PTree.beq_correct in H1, H2.
      rewrite PTree.beq_correct.
      intros x. specialize (H1 x); specialize (H2 x).
      destruct ((policy_export pol) ! x);
        destruct ((policy_export pol') ! x);
        destruct ((policy_export pol'') ! x); auto.
      destruct (list_id_eq l l0);
        destruct (list_id_eq l0 l1);
        destruct (list_id_eq l l1); auto.
      now subst.
    }
    assert (H3': PTree.beq (fun x y => list_cpt_id_eq x y) (policy_import pol) (policy_import pol'') = true).
    { clear -H1' H2'.
      rewrite PTree.beq_correct in H1', H2'.
      rewrite PTree.beq_correct.
      intros x. specialize (H1' x); specialize (H2' x).
      destruct ((policy_import pol) ! x);
        destruct ((policy_import pol') ! x);
        destruct ((policy_import pol'') ! x); auto.
      destruct (list_cpt_id_eq l l0);
        destruct (list_cpt_id_eq l0 l1);
        destruct (list_cpt_id_eq l l1); auto.
      now subst.
    }
    rewrite H3, H3'. auto.
  Qed.

End Policy.


(** Whole programs consist of:
- a collection of global definitions (name and description);
- a set of public names (the names that are visible outside
  this compilation unit);
- the name of the ``main'' function that serves as entry point in the program.
- a policy that governs which calls are allowed

A global definition is either a global function or a global variable.
The type of function descriptions and that of additional information
for variables vary among the various intermediate languages and are
taken as parameters to the [program] type.  The other parts of whole
programs are common to all languages. *)

Inductive globdef (F V: Type) : Type :=
  | Gfun (f: F)
  | Gvar (v: globvar V).

Arguments Gfun [F V].
Arguments Gvar [F V].

Instance has_comp_globdef F V {CF: has_comp F} : has_comp (globdef F V) :=
  fun gd =>
    match gd with
    | Gfun f => comp_of f
    | Gvar v => comp_of v
    end.

Record program (F V: Type) : Type := mkprogram {
  prog_defs: list (ident * globdef F V);
  prog_public: list ident;
  prog_main: ident;
  prog_pol: Policy.t;
  prog_pol_pub: Policy.in_pub prog_pol prog_public;
}.

Arguments mkprogram {F V} _ _ _ _ _.

Definition prog_defs_names (F V: Type) (p: program F V) : list ident :=
  List.map fst p.(prog_defs).

(** The "definition map" of a program maps names of globals to their definitions.
  If several definitions have the same name, the one appearing last in [p.(prog_defs)] wins. *)

Definition prog_defmap (F V: Type) (p: program F V) : PTree.t (globdef F V) :=
  PTree_Properties.of_list p.(prog_defs).

Definition list_comp (F V: Type) (p: program F V) {CF: has_comp F}: list compartment :=
  List.map (fun x => comp_of (snd x)) p.(prog_defs). (* TODO: filter out duplicate compartments from this list *)

Section DEFMAP.

Variables F V: Type.
Variable p: program F V.

Lemma in_prog_defmap:
  forall id g, (prog_defmap p)!id = Some g -> In (id, g) (prog_defs p).
Proof.
  apply PTree_Properties.in_of_list.
Qed.

Lemma prog_defmap_dom:
  forall id, In id (prog_defs_names p) -> exists g, (prog_defmap p)!id = Some g.
Proof.
  apply PTree_Properties.of_list_dom.
Qed.

Lemma prog_defmap_unique:
  forall defs1 id g defs2,
  prog_defs p = defs1 ++ (id, g) :: defs2 ->
  ~In id (map fst defs2) ->
  (prog_defmap p)!id = Some g.
Proof.
  unfold prog_defmap; intros. rewrite H. apply PTree_Properties.of_list_unique; auto.
Qed.

Lemma prog_defmap_norepet:
  forall id g,
  list_norepet (prog_defs_names p) ->
  In (id, g) (prog_defs p) ->
  (prog_defmap p)!id = Some g.
Proof.
  apply PTree_Properties.of_list_norepet.
Qed.

End DEFMAP.

(** * Generic transformations over programs *)

(** We now define a general iterator over programs that applies a given
  code transformation function to all function descriptions and leaves
  the other parts of the program unchanged. *)

Section TRANSF_PROGRAM.

Variable A B V: Type.
Variable transf: A -> B.

Definition transform_program_globdef (idg: ident * globdef A V) : ident * globdef B V :=
  match idg with
  | (id, Gfun f) => (id, Gfun (transf f))
  | (id, Gvar v) => (id, Gvar v)
  end.

Definition transform_program (p: program A V) : program B V :=
  mkprogram
    (List.map transform_program_globdef p.(prog_defs))
    p.(prog_public)
    p.(prog_main)
    p.(prog_pol)
    p.(prog_pol_pub).

End TRANSF_PROGRAM.

(** The following is a more general presentation of [transform_program]:
- Global variable information can be transformed, in addition to function
  definitions.
- The transformation functions can fail and return an error message.
- The transformation for function definitions receives a global context
  (derived from the compilation unit being transformed) as additiona
  argument.
- The transformation functions receive the name of the global as
  additional argument. *)

Local Open Scope error_monad_scope.

Section TRANSF_PROGRAM_GEN.

Variables A B V W: Type.
Variable transf_fun: ident -> A -> res B.
Variable transf_var: ident -> V -> res W.

Definition transf_globvar (i: ident) (g: globvar V) : res (globvar W) :=
  do info' <- transf_var i g.(gvar_info);
  OK (mkglobvar info' g.(gvar_comp) g.(gvar_init) g.(gvar_readonly) g.(gvar_volatile)).

Fixpoint transf_globdefs (l: list (ident * globdef A V)) : res (list (ident * globdef B W)) :=
  match l with
  | nil => OK nil
  | (id, Gfun f) :: l' =>
    match transf_fun id f with
      | Error msg => Error (MSG "In function " :: CTX id :: MSG ": " :: msg)
      | OK tf =>
        do tl' <- transf_globdefs l'; OK ((id, Gfun tf) :: tl')
    end
  | (id, Gvar v) :: l' =>
    match transf_globvar id v with
      | Error msg => Error (MSG "In variable " :: CTX id :: MSG ": " :: msg)
      | OK tv =>
        do tl' <- transf_globdefs l'; OK ((id, Gvar tv) :: tl')
    end
  end.

Definition transform_partial_program2 (p: program A V) : res (program B W) :=
  do gl' <- transf_globdefs p.(prog_defs);
  OK (mkprogram gl' p.(prog_public) p.(prog_main) p.(prog_pol) p.(prog_pol_pub)).

End TRANSF_PROGRAM_GEN.

(** The following is a special case of [transform_partial_program2], where only
  function definitions are transformed (but not variable definitions), and
  compartments are not taken into account. *)

Section TRANSF_PARTIAL_PROGRAM.

Variable A B V: Type.
Variable transf_fun: A -> res B.

Definition transform_partial_program (p: program A V) : res (program B V) :=
  transform_partial_program2 (fun i f => transf_fun f) (fun i v => OK v) p.

End TRANSF_PARTIAL_PROGRAM.

Lemma transform_program_partial_program:
  forall (A B V: Type) (transf_fun: A -> B) (p: program A V),
  transform_partial_program (fun f => OK (transf_fun f)) p = OK (transform_program transf_fun p).
Proof.
  intros. unfold transform_partial_program, transform_partial_program2.
  assert (EQ: forall l,
              transf_globdefs (fun i f => OK (transf_fun f)) (fun i (v: V) => OK v) l =
              OK (List.map (transform_program_globdef transf_fun) l)).
  { induction l as [ | [id g] l]; simpl.
  - auto.
  - destruct g; simpl; rewrite IHl; simpl. auto. destruct v; auto.
  }
  rewrite EQ; simpl. auto.
Qed.

(** * External functions *)

(** For most languages, the functions composing the program are either
  internal functions, defined within the language, or external functions,
  defined outside.  External functions include system calls but also
  compiler built-in functions.  We define a type for external functions
  and associated operations. *)

Inductive external_function : Type :=
  | EF_external (cp: compartment) (name: string) (sg: signature)
     (** A system call or library function.  Produces an event
         in the trace. *)
  | EF_builtin (cp: compartment) (name: string) (sg: signature)
     (** A compiler built-in function.  Behaves like an external, but
         can be inlined by the compiler. *)
  | EF_runtime (cp: compartment) (name: string) (sg: signature)
     (** A function from the run-time library.  Behaves like an
         external, but must not be redefined. *)
  | EF_vload (cp: compartment) (chunk: memory_chunk)
     (** A volatile read operation.  If the address given as first argument
         points within a volatile global variable, generate an
         event and return the value found in this event.  Otherwise,
         produce no event and behave like a regular memory load. *)
  | EF_vstore (cp: compartment) (chunk: memory_chunk)
     (** A volatile store operation.   If the address given as first argument
         points within a volatile global variable, generate an event.
         Otherwise, produce no event and behave like a regular memory store. *)
  | EF_malloc (cp: compartment)
     (** Dynamic memory allocation.  Takes the requested size in bytes
         as argument; returns a pointer to a fresh block of the given size.
         Produces no observable event. *)
  | EF_free (cp: compartment)
     (** Dynamic memory deallocation.  Takes a pointer to a block
         allocated by an [EF_malloc] external call and frees the
         corresponding block.
         Produces no observable event. *)
  | EF_memcpy (cp: compartment) (sz: Z) (al: Z)
     (** Block copy, of [sz] bytes, between addresses that are [al]-aligned. *)
  | EF_annot (cp: compartment) (kind: positive) (text: string) (targs: list typ)
     (** A programmer-supplied annotation.  Takes zero, one or several arguments,
         produces an event carrying the text and the values of these arguments,
         and returns no value. *)
  | EF_annot_val (cp: compartment) (kind: positive) (text: string) (targ: typ)
     (** Another form of annotation that takes one argument, produces
         an event carrying the text and the value of this argument,
         and returns the value of the argument. *)
  | EF_inline_asm (cp: compartment) (text: string) (sg: signature) (clobbers: list string)
     (** Inline [asm] statements.  Semantically, treated like an
         annotation with no parameters ([EF_annot text nil]).  To be
         used with caution, as it can invalidate the semantic
         preservation theorem.  Generated only if [-finline-asm] is
         given. *)
  | EF_debug (cp: compartment) (kind: positive) (text: ident) (targs: list typ).
     (** Transport debugging information from the front-end to the generated
         assembly.  Takes zero, one or several arguments like [EF_annot].
         Unlike [EF_annot], produces no observable event. *)


Instance has_comp_external_function : has_comp (external_function) :=
  fun ef =>
    match ef with
    | EF_external cp _ _ | EF_builtin cp _ _ | EF_runtime cp _ _
    | EF_malloc cp| EF_free cp | EF_vload cp _ | EF_vstore cp _ | EF_memcpy cp _ _
    | EF_annot cp _ _ _ | EF_annot_val cp _ _ _ | EF_inline_asm cp _ _ _
    | EF_debug cp _ _ _ => cp
    end.

(** The type signature of an external function. *)

Definition ef_sig (ef: external_function): signature :=
  match ef with
  | EF_external _ name sg => sg
  | EF_builtin _ name sg => sg
  | EF_runtime _ name sg => sg
  | EF_vload _ chunk => mksignature (Tptr :: nil) (rettype_of_chunk chunk) cc_default
  | EF_vstore _ chunk => mksignature (Tptr :: type_of_chunk chunk :: nil) Tvoid cc_default
  | EF_malloc _ => mksignature (Tptr :: nil) Tptr cc_default
  | EF_free _ => mksignature (Tptr :: nil) Tvoid cc_default
  | EF_memcpy _ sz al => mksignature (Tptr :: Tptr :: nil) Tvoid cc_default
  | EF_annot _ kind text targs => mksignature targs Tvoid cc_default
  | EF_annot_val _ kind text targ => mksignature (targ :: nil) targ cc_default
  | EF_inline_asm _ text sg clob => sg
  | EF_debug _ kind text targs => mksignature targs Tvoid cc_default
  end.


(** Whether an external function should be inlined by the compiler. *)

Definition ef_inline (ef: external_function) : bool :=
  match ef with
  | EF_external _ name sg => false
  | EF_builtin _ name sg => true
  | EF_runtime _ name sg => false
  | EF_vload _ chunk => true
  | EF_vstore _ chunk => true
  | EF_malloc _ => false
  | EF_free _ => false
  | EF_memcpy _ sz al => true
  | EF_annot _ kind text targs => true
  | EF_annot_val _ kind Text rg => true
  | EF_inline_asm _ text sg clob => true
  | EF_debug _ kind text targs => true
  end.

(** Whether an external function must reload its arguments. *)

Definition ef_reloads(ef: external_function) : bool :=
  match ef with
  | EF_annot _ kind text targs => false
  | EF_debug _ kind text targs => false
  | _ => true
  end.

(** Equality between external functions.  Used in module [Allocation]. *)

Definition external_function_eq: forall (ef1 ef2: external_function), {ef1=ef2} + {ef1<>ef2}.
Proof.
  generalize ident_eq string_dec signature_eq chunk_eq typ_eq list_eq_dec zeq Int.eq_dec; intros.
  decide equality.
Defined.
Global Opaque external_function_eq.

(** Function definitions are the union of internal and external functions. *)

Inductive fundef (F: Type): Type :=
  | Internal: F -> fundef F
  | External: external_function -> fundef F.

Arguments External [F].

Instance has_comp_fundef F {CF: has_comp F} : has_comp (fundef F) :=
  fun fd =>
    match fd with
    | Internal f => comp_of f
    | External ef => comp_of ef
    end.

Section TRANSF_FUNDEF.

Variable A B: Type.
Variable transf: A -> B.

Definition transf_fundef (fd: fundef A): fundef B :=
  match fd with
  | Internal f => Internal (transf f)
  | External ef => External ef
  end.

Global Instance comp_transf_fundef:
  forall {CA: has_comp A} {CB: has_comp B}
         {CAB: has_comp_transl transf},
  has_comp_transl transf_fundef.
Proof.
  intros CA CB CAB [f|ef]; simpl; eauto using comp_transl.
Qed.

End TRANSF_FUNDEF.

Section TRANSF_PARTIAL_FUNDEF.

Variable A B: Type.
Variable transf_partial: A -> res B.

Definition transf_partial_fundef (fd: fundef A): res (fundef B) :=
  match fd with
  | Internal f => do f' <- transf_partial f; OK (Internal f')
  | External ef => OK (External ef)
  end.

Global Instance comp_transf_partial_fundef:
  forall {CA: has_comp A} {CB: has_comp B}
         {CAB: has_comp_transl_partial transf_partial},
  has_comp_transl_partial transf_partial_fundef.
Proof.
  intros CA CB CAB [f|ef] tf H; simpl in *; monadInv H; trivial.
  eauto using comp_transl_partial.
Qed.

End TRANSF_PARTIAL_FUNDEF.

(** * Register pairs *)

Set Contextual Implicit.

(** In some intermediate languages (LTL, Mach), 64-bit integers can be
  split into two 32-bit halves and held in a pair of registers.
  Syntactically, this is captured by the type [rpair] below. *)

Inductive rpair (A: Type) : Type :=
  | One (r: A)
  | Twolong (rhi rlo: A).

Definition typ_rpair (A: Type) (typ_of: A -> typ) (p: rpair A): typ :=
  match p with
  | One r => typ_of r
  | Twolong rhi rlo => Tlong
  end.

Definition map_rpair (A B: Type) (f: A -> B) (p: rpair A): rpair B :=
  match p with
  | One r => One (f r)
  | Twolong rhi rlo => Twolong (f rhi) (f rlo)
  end.

Definition regs_of_rpair (A: Type) (p: rpair A): list A :=
  match p with
  | One r => r :: nil
  | Twolong rhi rlo => rhi :: rlo :: nil
  end.

Fixpoint regs_of_rpairs (A: Type) (l: list (rpair A)): list A :=
  match l with
  | nil => nil
  | p :: l => regs_of_rpair p ++ regs_of_rpairs l
  end.

Lemma in_regs_of_rpairs:
  forall (A: Type) (x: A) p, In x (regs_of_rpair p) -> forall l, In p l -> In x (regs_of_rpairs l).
Proof.
  induction l; simpl; intros. auto. apply in_app. destruct H0; auto. subst a. auto.
Qed.

Lemma in_regs_of_rpairs_inv:
  forall (A: Type) (x: A) l, In x (regs_of_rpairs l) -> exists p, In p l /\ In x (regs_of_rpair p).
Proof.
  induction l; simpl; intros. contradiction.
  rewrite in_app_iff in H; destruct H.
  exists a; auto.
  apply IHl in H. firstorder auto.
Qed.

Definition forall_rpair (A: Type) (P: A -> Prop) (p: rpair A): Prop :=
  match p with
  | One r => P r
  | Twolong rhi rlo => P rhi /\ P rlo
  end.

(** * Arguments and results to builtin functions *)

Inductive builtin_arg (A: Type) : Type :=
  | BA (x: A)
  | BA_int (n: int)
  | BA_long (n: int64)
  | BA_float (f: float)
  | BA_single (f: float32)
  | BA_loadstack (chunk: memory_chunk) (ofs: ptrofs)
  | BA_addrstack (ofs: ptrofs)
  | BA_loadglobal (chunk: memory_chunk) (id: ident) (ofs: ptrofs)
  | BA_addrglobal (id: ident) (ofs: ptrofs)
  | BA_splitlong (hi lo: builtin_arg A)
  | BA_addptr (a1 a2: builtin_arg A).

Inductive builtin_res (A: Type) : Type :=
  | BR (x: A)
  | BR_none
  | BR_splitlong (hi lo: builtin_res A).

Fixpoint globals_of_builtin_arg (A: Type) (a: builtin_arg A) : list ident :=
  match a with
  | BA_loadglobal chunk id ofs => id :: nil
  | BA_addrglobal id ofs => id :: nil
  | BA_splitlong hi lo => globals_of_builtin_arg hi ++ globals_of_builtin_arg lo
  | BA_addptr a1 a2 => globals_of_builtin_arg a1 ++ globals_of_builtin_arg a2
  | _ => nil
  end.

Definition globals_of_builtin_args (A: Type) (al: list (builtin_arg A)) : list ident :=
  List.fold_right (fun a l => globals_of_builtin_arg a ++ l) nil al.

Fixpoint params_of_builtin_arg (A: Type) (a: builtin_arg A) : list A :=
  match a with
  | BA x => x :: nil
  | BA_splitlong hi lo => params_of_builtin_arg hi ++ params_of_builtin_arg lo
  | BA_addptr a1 a2 => params_of_builtin_arg a1 ++ params_of_builtin_arg a2
  | _ => nil
  end.

Definition params_of_builtin_args (A: Type) (al: list (builtin_arg A)) : list A :=
  List.fold_right (fun a l => params_of_builtin_arg a ++ l) nil al.

Fixpoint params_of_builtin_res (A: Type) (a: builtin_res A) : list A :=
  match a with
  | BR x => x :: nil
  | BR_none => nil
  | BR_splitlong hi lo => params_of_builtin_res hi ++ params_of_builtin_res lo
  end.

Fixpoint map_builtin_arg (A B: Type) (f: A -> B) (a: builtin_arg A) : builtin_arg B :=
  match a with
  | BA x => BA (f x)
  | BA_int n => BA_int n
  | BA_long n => BA_long n
  | BA_float n => BA_float n
  | BA_single n => BA_single n
  | BA_loadstack chunk ofs => BA_loadstack chunk ofs
  | BA_addrstack ofs => BA_addrstack ofs
  | BA_loadglobal chunk id ofs => BA_loadglobal chunk id ofs
  | BA_addrglobal id ofs => BA_addrglobal id ofs
  | BA_splitlong hi lo =>
      BA_splitlong (map_builtin_arg f hi) (map_builtin_arg f lo)
  | BA_addptr a1 a2 =>
      BA_addptr (map_builtin_arg f a1) (map_builtin_arg f a2)
  end.

Fixpoint map_builtin_res (A B: Type) (f: A -> B) (a: builtin_res A) : builtin_res B :=
  match a with
  | BR x => BR (f x)
  | BR_none => BR_none
  | BR_splitlong hi lo =>
      BR_splitlong (map_builtin_res f hi) (map_builtin_res f lo)
  end.

(** Which kinds of builtin arguments are supported by which external function. *)

Inductive builtin_arg_constraint : Type :=
  | OK_default
  | OK_const
  | OK_addrstack
  | OK_addressing
  | OK_all.
