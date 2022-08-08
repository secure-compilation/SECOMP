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

(** This file defines a number of data types and operations used in
  the abstract syntax trees of a capability machine backend. It adds a
  capability type and chunk to the common AST *)

Require Import String.
Require Export AST.
Require Import Coqlib Maps Errors Integers Floats.
Require Archi.

Set Implicit Arguments.

(** The intermediate languages are weakly typed, using the following types: *)

Inductive captyp : Type :=
  | CTint                (**r 32-bit integers or capability offset *)
  | CTfloat              (**r 64-bit double-precision floats *)
  | CTlong               (**r 64-bit integers *)
  | CTsingle             (**r 32-bit single-precision floats *)
  | CTany32              (**r any 32-bit value *)
  | CTany64              (**r any 64-bit value, i.e. any value *)
  | CTany128             (**r any 128 bit value *)
  | CTcap64              (**r a 64-bit capability for 32 bit arch *)
  | CTcap128.            (**r a 128-bit capability for 64 bit arch *)

Lemma captyp_eq: forall (t1 t2: captyp), {t1=t2} + {t1<>t2}.
Proof. decide equality. Defined.
Global Opaque captyp_eq.

Definition list_captyp_eq: forall (l1 l2: list captyp), {l1=l2} + {l1<>l2}
                     := list_eq_dec captyp_eq.

Definition CTcap : captyp := if Archi.ptr64 then CTcap128 else CTcap64.
Definition CTanycap : captyp := if Archi.ptr64 then CTany128 else CTany64.
Definition CTptr : captyp := if Archi.ptr64 then CTlong else CTint.

Definition typesize (ty: captyp) : Z :=
  match ty with
  | CTint => 4
  | CTfloat => 8
  | CTlong => 8
  | CTsingle => 4
  | CTany32 => 4
  | CTany64 => 8
  | CTcap64 => 8
  | CTany128 => 16
  | CTcap128 => 16
  end.

Lemma typesize_pos: forall ty, typesize ty > 0.
Proof. destruct ty; simpl; omega. Qed.

Lemma typesize_CTcap: typesize CTcap = if Archi.ptr64 then 16 else 8.
Proof. unfold CTcap; destruct Archi.ptr64; auto. Qed.

Lemma typesize_CTptr: typesize CTptr = if Archi.ptr64 then 8 else 4.
Proof. unfold CTptr; destruct Archi.ptr64; auto. Qed.


(** All values of size 32 bits are also of type [Tany32].  All values
  are of type [Tany64].  This corresponds to the following subtyping
  relation over types. *)

Definition subtype (ty1 ty2: captyp) : bool :=
  match ty1, ty2 with
  | CTint, CTint => true
  | CTlong, CTlong => true
  | CTfloat, CTfloat => true
  | CTsingle, CTsingle => true
  | (CTint | CTsingle | CTany32), CTany32 => true
  | (CTint | CTlong | CTsingle | CTany32 | CTany64 | CTcap64), CTany64 => true
  | _, CTany128 => true
  | _, _ => false
  end.

Fixpoint subtype_list (tyl1 tyl2: list captyp) : bool :=
  match tyl1, tyl2 with
  | nil, nil => true
  | ty1::tys1, ty2::tys2 => subtype ty1 ty2 && subtype_list tys1 tys2
  | _, _ => false
  end.

(** To describe the values returned by functions, we use the more precise
    types below. *)

Inductive caprettype : Type :=
  | CTret (t: captyp)                    (**r like type [t] *)
  | CTint8signed                         (**r 8-bit signed integer *)
  | CTint8unsigned                       (**r 8-bit unsigned integer *)
  | CTint16signed                        (**r 16-bit signed integer *)
  | CTint16unsigned                      (**r 16-bit unsigned integer *)
  | CTvoid.                              (**r no value returned *)

Coercion CTret: captyp >-> caprettype.

Lemma rettype_eq: forall (t1 t2: caprettype), {t1=t2} + {t1<>t2}.
Proof. generalize captyp_eq; decide equality. Defined.
Global Opaque rettype_eq.

Fixpoint proj_rettype (r: caprettype) : captyp :=
  match r with
  | CTret t => t
  | CTint8signed | CTint8unsigned | CTint16signed | CTint16unsigned => CTint
  | CTvoid => CTint
  end.

Record capsignature : Type := mksignature {
  sig_args: list captyp;
  sig_res: caprettype;
  sig_cc: AST.calling_convention
}.

Definition proj_sig_res (s: capsignature) : captyp := proj_rettype s.(sig_res).

Definition signature_eq: forall (s1 s2: capsignature), {s1=s2} + {s1<>s2}.
Proof.
  generalize rettype_eq, list_captyp_eq, AST.calling_convention_eq; decide equality.
Defined.
Global Opaque signature_eq.

Definition capsignature_main :=
  {| sig_args := nil; sig_res := CTint; sig_cc := AST.cc_default |}.

(** Memory accesses (load and store instructions) are annotated by
  a ``memory chunk'' indicating the type, size and signedness of the
  chunk of memory being accessed. *)

Inductive cap_memory_chunk : Type :=
| CMint8signed     (**r 8-bit signed integer *)
| CMint8unsigned   (**r 8-bit unsigned integer *)
| CMint16signed    (**r 16-bit signed integer *)
| CMint16unsigned  (**r 16-bit unsigned integer *)
| CMint32          (**r 32-bit integer, or pointer *)
| CMint64          (**r 64-bit integer *)
| CMfloat32        (**r 32-bit single-precision float *)
| CMfloat64        (**r 64-bit double-precision float *)
| CMany32          (**r any value that fits in 32 bits *)
| CMany64          (**r any value that fits in 64 bits *)
| CMany128         (**r any value *)
| CMcap64          (**r 64-bit capability for 32 bit arch *)
| CMcap128.        (**r 128-bit capability for 64 bit arch *)

Definition chunk_eq: forall (c1 c2: cap_memory_chunk), {c1=c2} + {c1<>c2}.
Proof. decide equality. Defined.
Global Opaque chunk_eq.

Definition CMcap : cap_memory_chunk := if Archi.ptr64 then CMcap128 else CMcap64.
Definition CMptr : cap_memory_chunk := if Archi.ptr64 then CMint64 else CMint32.

(** The type (integer/pointer or float) of a chunk. *)

Definition type_of_chunk (c: cap_memory_chunk) : captyp :=
  match c with
  | CMint8signed => CTint
  | CMint8unsigned => CTint
  | CMint16signed => CTint
  | CMint16unsigned => CTint
  | CMint32 => CTint
  | CMint64 => CTlong
  | CMfloat32 => CTsingle
  | CMfloat64 => CTfloat
  | CMany32 => CTany32
  | CMany64 => CTany64
  | CMcap64 => CTcap64
  | CMcap128 => CTcap128
  | CMany128 => CTany128
  end.

Lemma type_of_CMcap: type_of_chunk CMcap = CTcap.
Proof. unfold CMcap, CTcap; destruct Archi.ptr64; auto. Qed.

Lemma type_of_CMptr: type_of_chunk CMptr = CTptr.
Proof. unfold CMptr, CTptr. destruct Archi.ptr64; auto. Qed.

(** Same, as a return type. *)

Definition rettype_of_chunk (c: cap_memory_chunk) : caprettype :=
  match c with
  | CMint8signed => CTint8signed
  | CMint8unsigned => CTint8unsigned
  | CMint16signed => CTint16signed
  | CMint16unsigned => CTint16unsigned
  | CMint32 => CTint
  | CMint64 => CTlong
  | CMfloat32 => CTsingle
  | CMfloat64 => CTfloat
  | CMany32 => CTany32
  | CMany64 => CTany64
  | CMcap64 => CTcap64
  | CMcap128 => CTcap128
  | CMany128 => CTany128
  end.

Lemma proj_rettype_of_chunk:
  forall chunk, proj_rettype (rettype_of_chunk chunk) = type_of_chunk chunk.
Proof.
  destruct chunk; auto.
Qed.

(** The chunk that is appropriate to store and reload a value of
  the given type, without losing information. *)

Definition chunk_of_type (ty: captyp) :=
  match ty with
  | CTint => CMint32
  | CTfloat => CMfloat64
  | CTlong => CMint64
  | CTsingle => CMfloat32
  | CTany32 => CMany32
  | CTany64 => CMany64
  | CTcap64 => CMcap64
  | CTcap128 => CMcap128
  | CTany128 => CMany128
  end.

Lemma chunk_of_CTcap: chunk_of_type CTcap = CMcap.
Proof. unfold CMcap, CTcap; destruct Archi.ptr64; auto. Qed.

Lemma chunk_of_CTptr: chunk_of_type CTptr = CMptr.
Proof. unfold CTptr, CMptr; destruct Archi.ptr64; auto. Qed.

(** * External functions *)

(** For most languages, the functions composing the program are either
  internal functions, defined within the language, or external functions,
  defined outside.  External functions include system calls but also
  compiler built-in functions.  We define a type for external functions
  and associated operations. *)

Inductive cap_external_function : Type :=
  | CEF_external (name: string) (cp: AST.compartment) (sg: capsignature)
     (** A system call or library function.  Produces an event
         in the trace. *)
  | CEF_builtin (name: string) (sg: capsignature)
     (** A compiler built-in function.  Behaves like an external, but
         can be inlined by the compiler. *)
  | CEF_runtime (name: string) (sg: capsignature)
     (** A function from the run-time library.  Behaves like an
         external, but must not be redefined. *)
  | CEF_vload (chunk: cap_memory_chunk)
     (** A volatile read operation.  If the address given as first argument
         points within a volatile global variable, generate an
         event and return the value found in this event.  Otherwise,
         produce no event and behave like a regular memory load. *)
  | CEF_vstore (chunk: cap_memory_chunk)
     (** A volatile store operation.   If the address given as first argument
         points within a volatile global variable, generate an event.
         Otherwise, produce no event and behave like a regular memory store. *)
  | CEF_malloc
     (** Dynamic memory allocation.  Takes the requested size in bytes
         as argument; returns a pointer to a fresh block of the given size.
         Produces no observable event. *)
  | CEF_free
     (** Dynamic memory deallocation.  Takes a pointer to a block
         allocated by an [EF_malloc] external call and frees the
         corresponding block.
         Produces no observable event. *)
  | CEF_memcpy (sz: Z) (al: Z)
     (** Block copy, of [sz] bytes, between addresses that are [al]-aligned. *)
  | CEF_annot (kind: positive) (text: string) (targs: list captyp)
     (** A programmer-supplied annotation.  Takes zero, one or several arguments,
         produces an event carrying the text and the values of these arguments,
         and returns no value. *)
  | CEF_annot_val (kind: positive) (text: string) (targ: captyp)
     (** Another form of annotation that takes one argument, produces
         an event carrying the text and the value of this argument,
         and returns the value of the argument. *)
  | CEF_inline_asm (text: string) (sg: capsignature) (clobbers: list string)
     (** Inline [asm] statements.  Semantically, treated like an
         annotation with no parameters ([EF_annot text nil]).  To be
         used with caution, as it can invalidate the semantic
         preservation theorem.  Generated only if [-finline-asm] is
         given. *)
  | CEF_debug (kind: positive) (text: AST.ident) (targs: list captyp).
     (** Transport debugging information from the front-end to the generated
         assembly.  Takes zero, one or several arguments like [EF_annot].
         Unlike [EF_annot], produces no observable event. *)

(** For now, we group most external functions together in the default
compartment.  Eventually this will probably be refined. *)

Instance has_comp_cap_external_function : AST.has_comp cap_external_function :=
  fun ef =>
    match ef with
    | CEF_external _ cp _ => cp
    | CEF_malloc | CEF_free | CEF_vload _ | CEF_vstore _ | CEF_memcpy _ _ => AST.privileged_compartment (* default_compartment *)
    | _ => AST.default_compartment
    end.

(** The type signature of an external function. *)

Definition ef_sig (ef: cap_external_function): capsignature :=
  match ef with
  | CEF_external name cp sg => sg
  | CEF_builtin name sg => sg
  | CEF_runtime name sg => sg
  | CEF_vload chunk => mksignature (CTptr :: nil) (rettype_of_chunk chunk) AST.cc_default
  | CEF_vstore chunk => mksignature (CTptr :: type_of_chunk chunk :: nil) CTvoid AST.cc_default
  | CEF_malloc => mksignature (CTptr :: nil) CTcap AST.cc_default
  | CEF_free => mksignature (CTptr :: nil) CTvoid AST.cc_default
  | CEF_memcpy sz al => mksignature (CTcap :: CTcap :: nil) CTvoid AST.cc_default
  | CEF_annot kind text targs => mksignature targs CTvoid AST.cc_default
  | CEF_annot_val kind text targ => mksignature (targ :: nil) targ AST.cc_default
  | CEF_inline_asm text sg clob => sg
  | CEF_debug kind text targs => mksignature targs CTvoid AST.cc_default
  end.

(** Whether an external function should be inlined by the compiler. *)

Definition ef_inline (ef: cap_external_function) : bool :=
  match ef with
  | CEF_external name cp sg => false
  | CEF_builtin name sg => true
  | CEF_runtime name sg => false
  | CEF_vload chunk => true
  | CEF_vstore chunk => true
  | CEF_malloc => false
  | CEF_free => false
  | CEF_memcpy sz al => true
  | CEF_annot kind text targs => true
  | CEF_annot_val kind Text rg => true
  | CEF_inline_asm text sg clob => true
  | CEF_debug kind text targs => true
  end.

(** Whether an external function must reload its arguments. *)

Definition ef_reloads (ef: cap_external_function) : bool :=
  match ef with
  | CEF_annot kind text targs => false
  | CEF_debug kind text targs => false
  | _ => true
  end.

(** Equality between external functions.  Used in module [Allocation]. *)

Definition external_function_eq: forall (ef1 ef2: cap_external_function), {ef1=ef2} + {ef1<>ef2}.
Proof.
  generalize AST.ident_eq string_dec signature_eq chunk_eq captyp_eq list_eq_dec zeq Int.eq_dec; intros.
  decide equality.
Defined.
Global Opaque external_function_eq.

(** Function definitions are the union of internal and external functions. *)

Inductive capfundef (F: Type): Type :=
  | CInternal: F -> capfundef F
  | CExternal: cap_external_function -> capfundef F.

Arguments CExternal [F].

Instance has_comp_fundef F {CF: AST.has_comp F} : AST.has_comp (capfundef F) :=
  fun fd =>
    match fd with
    | CInternal f => AST.comp_of f
    | CExternal ef => AST.comp_of ef
    end.

Section TRANSF_FUNDEF.

Variable A B: Type.
Variable transf: A -> B.

Definition transf_fundef (fd: capfundef A): capfundef B :=
  match fd with
  | CInternal f => CInternal (transf f)
  | CExternal ef => CExternal ef
  end.

Global Instance comp_transf_fundef:
  forall {CA: AST.has_comp A} {CB: AST.has_comp B}
         {CAB: AST.has_comp_transl transf},
  AST.has_comp_transl transf_fundef.
Proof.
  intros CA CB CAB [f|ef]; simpl; eauto using AST.comp_transl.
Qed.

End TRANSF_FUNDEF.

Section TRANSF_PARTIAL_FUNDEF.

Variable A B: Type.
Variable transf_partial: A -> res B.

Definition transf_partial_fundef (fd: capfundef A): res (capfundef B) :=
  match fd with
  | CInternal f => bind (transf_partial f) (fun f' => OK (CInternal f'))
  | CExternal ef => OK (CExternal ef)
  end.

Global Instance comp_transf_partial_fundef:
  forall {CA: AST.has_comp A} {CB: AST.has_comp B}
         {CAB: AST.has_comp_transl_partial transf_partial},
  AST.has_comp_transl_partial transf_partial_fundef.
Proof.
  intros CA CB CAB [f|ef] tf H; simpl in *; monadInv H; trivial.
  eauto using AST.comp_transl_partial.
Qed.

End TRANSF_PARTIAL_FUNDEF.

Set Contextual Implicit.
