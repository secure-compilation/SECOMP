(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*           Prashanth Mundkur, SRI International                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(*  The contributions by Prashanth Mundkur are reused and adapted      *)
(*  under the terms of a Contributor License Agreement between         *)
(*  SRI International and INRIA.                                       *)
(*                                                                     *)
(* *********************************************************************)

(** Instruction selection for operators *)

(** The instruction selection pass recognizes opportunities for using
  combined arithmetic and logical operations and addressing modes
  offered by the target processor.  For instance, the expression [x + 1]
  can take advantage of the "immediate add" instruction of the processor,
  and on the PowerPC, the expression [(x >> 6) & 0xFF] can be turned
  into a "rotate and mask" instruction.

  This file defines functions for building CminorSel expressions and
  statements, especially expressions consisting of operator
  applications.  These functions examine their arguments to choose
  cheaper forms of operators whenever possible.

  For instance, [add e1 e2] will return a CminorSel expression semantically
  equivalent to [Eop Oadd (e1 ::: e2 ::: Enil)], but will use a
  [Oaddimm] operator if one of the arguments is an integer constant,
  or suppress the addition altogether if one of the arguments is the
  null integer.  In passing, we perform operator reassociation
  ([(e + c1) * c2] becomes [(e * c2) + (c1 * c2)]) and a small amount
  of constant propagation.

  On top of the "smart constructor" functions defined below,
  module [Selection] implements the actual instruction selection pass.
*)

Require Archi.
Require Import Coqlib.
Require Import Compopts.
Require Import AST Integers Floats Builtins.
Require Import Op CminorSel.

Local Open Scope cminorsel_scope.

(** ** Constants **)

Definition addrsymbol (id: ident) (ofs: ptrofs) :=
  Eop (Oaddrsymbol id ofs) Enil.

Definition addrstack (ofs: ptrofs) :=
  Eop (Oaddrstack ofs) Enil.

(** ** Integer addition and pointer addition *)

(** Original definition:
<<
Nondetfunction addimm (n: int) (e: expr) :=
  if Int.eq n Int.zero then e else
  match e with
  | Eop (Ointconst m) Enil => Eop (Ointconst (Int.add n m)) Enil
  | Eop (Oaddrsymbol s m) Enil   => Eop (Oaddrsymbol s (Ptrofs.add (Ptrofs.of_int n) m)) Enil
  | Eop (Oaddrstack m) Enil      => Eop (Oaddrstack (Ptrofs.add (Ptrofs.of_int n) m)) Enil
  | Eop (Oaddimm m) (t ::: Enil) => Eop (Oaddimm(Int.add n m)) (t ::: Enil)
  | _ => Eop (Oaddimm n) (e ::: Enil)
  end.
>>
*)

Inductive addimm_cases: forall (e: expr), Type :=
  | addimm_case1: forall m, addimm_cases (Eop (Ointconst m) Enil)
  | addimm_case2: forall s m, addimm_cases (Eop (Oaddrsymbol s m) Enil)
  | addimm_case3: forall m, addimm_cases (Eop (Oaddrstack m) Enil)
  | addimm_case4: forall m t, addimm_cases (Eop (Oaddimm m) (t ::: Enil))
  | addimm_default: forall (e: expr), addimm_cases e.

Definition addimm_match (e: expr) :=
  match e as zz1 return addimm_cases zz1 with
  | Eop (Ointconst m) Enil => addimm_case1 m
  | Eop (Oaddrsymbol s m) Enil => addimm_case2 s m
  | Eop (Oaddrstack m) Enil => addimm_case3 m
  | Eop (Oaddimm m) (t ::: Enil) => addimm_case4 m t
  | e => addimm_default e
  end.

Definition addimm (n: int) (e: expr) :=
 if Int.eq n Int.zero then e else match addimm_match e with
  | addimm_case1 m => (* Eop (Ointconst m) Enil *) 
      Eop (Ointconst (Int.add n m)) Enil
  | addimm_case2 s m => (* Eop (Oaddrsymbol s m) Enil *) 
      Eop (Oaddrsymbol s (Ptrofs.add (Ptrofs.of_int n) m)) Enil
  | addimm_case3 m => (* Eop (Oaddrstack m) Enil *) 
      Eop (Oaddrstack (Ptrofs.add (Ptrofs.of_int n) m)) Enil
  | addimm_case4 m t => (* Eop (Oaddimm m) (t ::: Enil) *) 
      Eop (Oaddimm(Int.add n m)) (t ::: Enil)
  | addimm_default e =>
      Eop (Oaddimm n) (e ::: Enil)
  end.


(** Original definition:
<<
Nondetfunction add (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => addimm n1 t2
  | t1, Eop (Ointconst n2) Enil => addimm n2 t1
  | Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) =>
      addimm (Int.add n1 n2) (Eop Oadd (t1:::t2:::Enil))
  | Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddrstack n2) Enil =>
      Eop Oadd (Eop (Oaddrstack (Ptrofs.add (Ptrofs.of_int n1) n2)) Enil ::: t1 ::: Enil)
  | Eop (Oaddrstack n1) Enil, Eop (Oaddimm n2) (t2:::Enil) =>
      Eop Oadd (Eop (Oaddrstack (Ptrofs.add n1 (Ptrofs.of_int n2))) Enil ::: t2 ::: Enil)
  | Eop (Oaddimm n1) (t1:::Enil), t2 =>
      addimm n1 (Eop Oadd (t1:::t2:::Enil))
  | t1, Eop (Oaddimm n2) (t2:::Enil) =>
      addimm n2 (Eop Oadd (t1:::t2:::Enil))
  | _, _ => Eop Oadd (e1:::e2:::Enil)
  end.
>>
*)

Inductive add_cases: forall (e1: expr) (e2: expr), Type :=
  | add_case1: forall n1 t2, add_cases (Eop (Ointconst n1) Enil) (t2)
  | add_case2: forall t1 n2, add_cases (t1) (Eop (Ointconst n2) Enil)
  | add_case3: forall n1 t1 n2 t2, add_cases (Eop (Oaddimm n1) (t1:::Enil)) (Eop (Oaddimm n2) (t2:::Enil))
  | add_case4: forall n1 t1 n2, add_cases (Eop (Oaddimm n1) (t1:::Enil)) (Eop (Oaddrstack n2) Enil)
  | add_case5: forall n1 n2 t2, add_cases (Eop (Oaddrstack n1) Enil) (Eop (Oaddimm n2) (t2:::Enil))
  | add_case6: forall n1 t1 t2, add_cases (Eop (Oaddimm n1) (t1:::Enil)) (t2)
  | add_case7: forall t1 n2 t2, add_cases (t1) (Eop (Oaddimm n2) (t2:::Enil))
  | add_default: forall (e1: expr) (e2: expr), add_cases e1 e2.

Definition add_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return add_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => add_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => add_case2 t1 n2
  | Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) => add_case3 n1 t1 n2 t2
  | Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddrstack n2) Enil => add_case4 n1 t1 n2
  | Eop (Oaddrstack n1) Enil, Eop (Oaddimm n2) (t2:::Enil) => add_case5 n1 n2 t2
  | Eop (Oaddimm n1) (t1:::Enil), t2 => add_case6 n1 t1 t2
  | t1, Eop (Oaddimm n2) (t2:::Enil) => add_case7 t1 n2 t2
  | e1, e2 => add_default e1 e2
  end.

Definition add (e1: expr) (e2: expr) :=
  match add_match e1 e2 with
  | add_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      addimm n1 t2
  | add_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      addimm n2 t1
  | add_case3 n1 t1 n2 t2 => (* Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) *) 
      addimm (Int.add n1 n2) (Eop Oadd (t1:::t2:::Enil))
  | add_case4 n1 t1 n2 => (* Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddrstack n2) Enil *) 
      Eop Oadd (Eop (Oaddrstack (Ptrofs.add (Ptrofs.of_int n1) n2)) Enil ::: t1 ::: Enil)
  | add_case5 n1 n2 t2 => (* Eop (Oaddrstack n1) Enil, Eop (Oaddimm n2) (t2:::Enil) *) 
      Eop Oadd (Eop (Oaddrstack (Ptrofs.add n1 (Ptrofs.of_int n2))) Enil ::: t2 ::: Enil)
  | add_case6 n1 t1 t2 => (* Eop (Oaddimm n1) (t1:::Enil), t2 *) 
      addimm n1 (Eop Oadd (t1:::t2:::Enil))
  | add_case7 t1 n2 t2 => (* t1, Eop (Oaddimm n2) (t2:::Enil) *) 
      addimm n2 (Eop Oadd (t1:::t2:::Enil))
  | add_default e1 e2 =>
      Eop Oadd (e1:::e2:::Enil)
  end.


(** ** Integer and pointer subtraction *)

(** Original definition:
<<
Nondetfunction sub (e1: expr) (e2: expr) :=
  match e1, e2 with
  | t1, Eop (Ointconst n2) Enil =>
      addimm (Int.neg n2) t1
  | Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) =>
      addimm (Int.sub n1 n2) (Eop Osub (t1:::t2:::Enil))
  | Eop (Oaddimm n1) (t1:::Enil), t2 =>
      addimm n1 (Eop Osub (t1:::t2:::Enil))
  | t1, Eop (Oaddimm n2) (t2:::Enil) =>
      addimm (Int.neg n2) (Eop Osub (t1:::t2:::Enil))
  | _, _ => Eop Osub (e1:::e2:::Enil)
  end.
>>
*)

Inductive sub_cases: forall (e1: expr) (e2: expr), Type :=
  | sub_case1: forall t1 n2, sub_cases (t1) (Eop (Ointconst n2) Enil)
  | sub_case2: forall n1 t1 n2 t2, sub_cases (Eop (Oaddimm n1) (t1:::Enil)) (Eop (Oaddimm n2) (t2:::Enil))
  | sub_case3: forall n1 t1 t2, sub_cases (Eop (Oaddimm n1) (t1:::Enil)) (t2)
  | sub_case4: forall t1 n2 t2, sub_cases (t1) (Eop (Oaddimm n2) (t2:::Enil))
  | sub_default: forall (e1: expr) (e2: expr), sub_cases e1 e2.

Definition sub_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return sub_cases zz1 zz2 with
  | t1, Eop (Ointconst n2) Enil => sub_case1 t1 n2
  | Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) => sub_case2 n1 t1 n2 t2
  | Eop (Oaddimm n1) (t1:::Enil), t2 => sub_case3 n1 t1 t2
  | t1, Eop (Oaddimm n2) (t2:::Enil) => sub_case4 t1 n2 t2
  | e1, e2 => sub_default e1 e2
  end.

Definition sub (e1: expr) (e2: expr) :=
  match sub_match e1 e2 with
  | sub_case1 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      addimm (Int.neg n2) t1
  | sub_case2 n1 t1 n2 t2 => (* Eop (Oaddimm n1) (t1:::Enil), Eop (Oaddimm n2) (t2:::Enil) *) 
      addimm (Int.sub n1 n2) (Eop Osub (t1:::t2:::Enil))
  | sub_case3 n1 t1 t2 => (* Eop (Oaddimm n1) (t1:::Enil), t2 *) 
      addimm n1 (Eop Osub (t1:::t2:::Enil))
  | sub_case4 t1 n2 t2 => (* t1, Eop (Oaddimm n2) (t2:::Enil) *) 
      addimm (Int.neg n2) (Eop Osub (t1:::t2:::Enil))
  | sub_default e1 e2 =>
      Eop Osub (e1:::e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction negint (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil => Eop (Ointconst (Int.neg n)) Enil
  | _ => Eop Oneg (e ::: Enil)
  end.
>>
*)

Inductive negint_cases: forall (e: expr), Type :=
  | negint_case1: forall n, negint_cases (Eop (Ointconst n) Enil)
  | negint_default: forall (e: expr), negint_cases e.

Definition negint_match (e: expr) :=
  match e as zz1 return negint_cases zz1 with
  | Eop (Ointconst n) Enil => negint_case1 n
  | e => negint_default e
  end.

Definition negint (e: expr) :=
  match negint_match e with
  | negint_case1 n => (* Eop (Ointconst n) Enil *) 
      Eop (Ointconst (Int.neg n)) Enil
  | negint_default e =>
      Eop Oneg (e ::: Enil)
  end.


(** ** Immediate shifts *)

(** Original definition:
<<
Nondetfunction shlimm (e1: expr) (n: int) :=
  if Int.eq n Int.zero then
    e1
  else if negb (Int.ltu n Int.iwordsize) then
    Eop Oshl (e1 ::: Eop (Ointconst n) Enil ::: Enil)
  else match e1 with
    | Eop (Ointconst n1) Enil =>
        Eop (Ointconst (Int.shl n1 n)) Enil
    | Eop (Oshlimm n1) (t1:::Enil) =>
        if Int.ltu (Int.add n n1) Int.iwordsize
        then Eop (Oshlimm (Int.add n n1)) (t1:::Enil)
        else Eop (Oshlimm n) (e1:::Enil)
    | _ =>
        Eop (Oshlimm n) (e1:::Enil)
  end.
>>
*)

Inductive shlimm_cases: forall (e1: expr) , Type :=
  | shlimm_case1: forall n1, shlimm_cases (Eop (Ointconst n1) Enil)
  | shlimm_case2: forall n1 t1, shlimm_cases (Eop (Oshlimm n1) (t1:::Enil))
  | shlimm_default: forall (e1: expr) , shlimm_cases e1.

Definition shlimm_match (e1: expr)  :=
  match e1 as zz1 return shlimm_cases zz1 with
  | Eop (Ointconst n1) Enil => shlimm_case1 n1
  | Eop (Oshlimm n1) (t1:::Enil) => shlimm_case2 n1 t1
  | e1 => shlimm_default e1
  end.

Definition shlimm (e1: expr) (n: int) :=
 if Int.eq n Int.zero then e1 else if negb (Int.ltu n Int.iwordsize) then Eop Oshl (e1 ::: Eop (Ointconst n) Enil ::: Enil) else match shlimm_match e1 with
  | shlimm_case1 n1 => (* Eop (Ointconst n1) Enil *) 
      Eop (Ointconst (Int.shl n1 n)) Enil
  | shlimm_case2 n1 t1 => (* Eop (Oshlimm n1) (t1:::Enil) *) 
      if Int.ltu (Int.add n n1) Int.iwordsize then Eop (Oshlimm (Int.add n n1)) (t1:::Enil) else Eop (Oshlimm n) (e1:::Enil)
  | shlimm_default e1 =>
      Eop (Oshlimm n) (e1:::Enil)
  end.


(** Original definition:
<<
Nondetfunction shruimm (e1: expr) (n: int) :=
  if Int.eq n Int.zero then
    e1
  else if negb (Int.ltu n Int.iwordsize) then
    Eop Oshru (e1 ::: Eop (Ointconst n) Enil ::: Enil)
  else match e1 with
    | Eop (Ointconst n1) Enil =>
        Eop (Ointconst (Int.shru n1 n)) Enil
    | Eop (Oshruimm n1) (t1:::Enil) =>
        if Int.ltu (Int.add n n1) Int.iwordsize
        then Eop (Oshruimm (Int.add n n1)) (t1:::Enil)
        else Eop (Oshruimm n) (e1:::Enil)
    | _ =>
        Eop (Oshruimm n) (e1:::Enil)
    end.
>>
*)

Inductive shruimm_cases: forall (e1: expr) , Type :=
  | shruimm_case1: forall n1, shruimm_cases (Eop (Ointconst n1) Enil)
  | shruimm_case2: forall n1 t1, shruimm_cases (Eop (Oshruimm n1) (t1:::Enil))
  | shruimm_default: forall (e1: expr) , shruimm_cases e1.

Definition shruimm_match (e1: expr)  :=
  match e1 as zz1 return shruimm_cases zz1 with
  | Eop (Ointconst n1) Enil => shruimm_case1 n1
  | Eop (Oshruimm n1) (t1:::Enil) => shruimm_case2 n1 t1
  | e1 => shruimm_default e1
  end.

Definition shruimm (e1: expr) (n: int) :=
 if Int.eq n Int.zero then e1 else if negb (Int.ltu n Int.iwordsize) then Eop Oshru (e1 ::: Eop (Ointconst n) Enil ::: Enil) else match shruimm_match e1 with
  | shruimm_case1 n1 => (* Eop (Ointconst n1) Enil *) 
      Eop (Ointconst (Int.shru n1 n)) Enil
  | shruimm_case2 n1 t1 => (* Eop (Oshruimm n1) (t1:::Enil) *) 
      if Int.ltu (Int.add n n1) Int.iwordsize then Eop (Oshruimm (Int.add n n1)) (t1:::Enil) else Eop (Oshruimm n) (e1:::Enil)
  | shruimm_default e1 =>
      Eop (Oshruimm n) (e1:::Enil)
  end.


(** Original definition:
<<
Nondetfunction shrimm (e1: expr) (n: int) :=
  if Int.eq n Int.zero then
    e1
  else if negb (Int.ltu n Int.iwordsize) then
    Eop Oshr (e1 ::: Eop (Ointconst n) Enil ::: Enil)
  else match e1 with
    | Eop (Ointconst n1) Enil =>
        Eop (Ointconst (Int.shr n1 n)) Enil
    | Eop (Oshrimm n1) (t1:::Enil) =>
        if Int.ltu (Int.add n n1) Int.iwordsize
        then Eop (Oshrimm (Int.add n n1)) (t1:::Enil)
        else Eop (Oshrimm n) (e1:::Enil)
    | _ =>
        Eop (Oshrimm n) (e1:::Enil)
    end.
>>
*)

Inductive shrimm_cases: forall (e1: expr) , Type :=
  | shrimm_case1: forall n1, shrimm_cases (Eop (Ointconst n1) Enil)
  | shrimm_case2: forall n1 t1, shrimm_cases (Eop (Oshrimm n1) (t1:::Enil))
  | shrimm_default: forall (e1: expr) , shrimm_cases e1.

Definition shrimm_match (e1: expr)  :=
  match e1 as zz1 return shrimm_cases zz1 with
  | Eop (Ointconst n1) Enil => shrimm_case1 n1
  | Eop (Oshrimm n1) (t1:::Enil) => shrimm_case2 n1 t1
  | e1 => shrimm_default e1
  end.

Definition shrimm (e1: expr) (n: int) :=
 if Int.eq n Int.zero then e1 else if negb (Int.ltu n Int.iwordsize) then Eop Oshr (e1 ::: Eop (Ointconst n) Enil ::: Enil) else match shrimm_match e1 with
  | shrimm_case1 n1 => (* Eop (Ointconst n1) Enil *) 
      Eop (Ointconst (Int.shr n1 n)) Enil
  | shrimm_case2 n1 t1 => (* Eop (Oshrimm n1) (t1:::Enil) *) 
      if Int.ltu (Int.add n n1) Int.iwordsize then Eop (Oshrimm (Int.add n n1)) (t1:::Enil) else Eop (Oshrimm n) (e1:::Enil)
  | shrimm_default e1 =>
      Eop (Oshrimm n) (e1:::Enil)
  end.


(** ** Integer multiply *)

Definition mulimm_base (n1: int) (e2: expr) :=
  match Int.one_bits n1 with
  | i :: nil =>
      shlimm e2 i
  | i :: j :: nil =>
      Elet e2 (add (shlimm (Eletvar 0) i) (shlimm (Eletvar 0) j))
  | _ =>
      Eop Omul (Eop (Ointconst n1) Enil ::: e2 ::: Enil)
  end.

(** Original definition:
<<
Nondetfunction mulimm (n1: int) (e2: expr) :=
  if Int.eq n1 Int.zero then Eop (Ointconst Int.zero) Enil
  else if Int.eq n1 Int.one then e2
  else match e2 with
  | Eop (Ointconst n2) Enil => Eop (Ointconst (Int.mul n1 n2)) Enil
  | Eop (Oaddimm n2) (t2:::Enil) => addimm (Int.mul n1 n2) (mulimm_base n1 t2)
  | _ => mulimm_base n1 e2
  end.
>>
*)

Inductive mulimm_cases: forall (e2: expr), Type :=
  | mulimm_case1: forall n2, mulimm_cases (Eop (Ointconst n2) Enil)
  | mulimm_case2: forall n2 t2, mulimm_cases (Eop (Oaddimm n2) (t2:::Enil))
  | mulimm_default: forall (e2: expr), mulimm_cases e2.

Definition mulimm_match (e2: expr) :=
  match e2 as zz1 return mulimm_cases zz1 with
  | Eop (Ointconst n2) Enil => mulimm_case1 n2
  | Eop (Oaddimm n2) (t2:::Enil) => mulimm_case2 n2 t2
  | e2 => mulimm_default e2
  end.

Definition mulimm (n1: int) (e2: expr) :=
 if Int.eq n1 Int.zero then Eop (Ointconst Int.zero) Enil else if Int.eq n1 Int.one then e2 else match mulimm_match e2 with
  | mulimm_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      Eop (Ointconst (Int.mul n1 n2)) Enil
  | mulimm_case2 n2 t2 => (* Eop (Oaddimm n2) (t2:::Enil) *) 
      addimm (Int.mul n1 n2) (mulimm_base n1 t2)
  | mulimm_default e2 =>
      mulimm_base n1 e2
  end.


(** Original definition:
<<
Nondetfunction mul (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => mulimm n1 t2
  | t1, Eop (Ointconst n2) Enil => mulimm n2 t1
  | _, _ => Eop Omul (e1:::e2:::Enil)
  end.
>>
*)

Inductive mul_cases: forall (e1: expr) (e2: expr), Type :=
  | mul_case1: forall n1 t2, mul_cases (Eop (Ointconst n1) Enil) (t2)
  | mul_case2: forall t1 n2, mul_cases (t1) (Eop (Ointconst n2) Enil)
  | mul_default: forall (e1: expr) (e2: expr), mul_cases e1 e2.

Definition mul_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return mul_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => mul_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => mul_case2 t1 n2
  | e1, e2 => mul_default e1 e2
  end.

Definition mul (e1: expr) (e2: expr) :=
  match mul_match e1 e2 with
  | mul_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      mulimm n1 t2
  | mul_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      mulimm n2 t1
  | mul_default e1 e2 =>
      Eop Omul (e1:::e2:::Enil)
  end.


Definition mulhs (e1: expr) (e2: expr) :=
  if Archi.ptr64 then
    Eop Olowlong
      (Eop (Oshrlimm (Int.repr 32))
         (Eop Omull (Eop Ocast32signed (e1 ::: Enil) :::
                     Eop Ocast32signed (e2 ::: Enil) ::: Enil) ::: Enil)
          ::: Enil)
  else
    Eop Omulhs (e1 ::: e2 ::: Enil).

Definition mulhu (e1: expr) (e2: expr) :=
  if Archi.ptr64 then
    Eop Olowlong
      (Eop (Oshrluimm (Int.repr 32))
         (Eop Omull (Eop Ocast32unsigned (e1 ::: Enil) :::
                     Eop Ocast32unsigned (e2 ::: Enil) ::: Enil) ::: Enil)
          ::: Enil)
  else
    Eop Omulhu (e1 ::: e2 ::: Enil).

(** ** Bitwise and, or, xor *)

(** Original definition:
<<
Nondetfunction andimm (n1: int) (e2: expr) :=
  if Int.eq n1 Int.zero then Eop (Ointconst Int.zero) Enil
  else if Int.eq n1 Int.mone then e2
  else match e2 with
  | Eop (Ointconst n2) Enil => Eop (Ointconst (Int.and n1 n2)) Enil
  | Eop (Oandimm n2) (t2:::Enil) => Eop (Oandimm (Int.and n1 n2)) (t2:::Enil)
  | _ => Eop (Oandimm n1) (e2:::Enil)
  end.
>>
*)

Inductive andimm_cases: forall (e2: expr), Type :=
  | andimm_case1: forall n2, andimm_cases (Eop (Ointconst n2) Enil)
  | andimm_case2: forall n2 t2, andimm_cases (Eop (Oandimm n2) (t2:::Enil))
  | andimm_default: forall (e2: expr), andimm_cases e2.

Definition andimm_match (e2: expr) :=
  match e2 as zz1 return andimm_cases zz1 with
  | Eop (Ointconst n2) Enil => andimm_case1 n2
  | Eop (Oandimm n2) (t2:::Enil) => andimm_case2 n2 t2
  | e2 => andimm_default e2
  end.

Definition andimm (n1: int) (e2: expr) :=
 if Int.eq n1 Int.zero then Eop (Ointconst Int.zero) Enil else if Int.eq n1 Int.mone then e2 else match andimm_match e2 with
  | andimm_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      Eop (Ointconst (Int.and n1 n2)) Enil
  | andimm_case2 n2 t2 => (* Eop (Oandimm n2) (t2:::Enil) *) 
      Eop (Oandimm (Int.and n1 n2)) (t2:::Enil)
  | andimm_default e2 =>
      Eop (Oandimm n1) (e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction and (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => andimm n1 t2
  | t1, Eop (Ointconst n2) Enil => andimm n2 t1
  | _, _ => Eop Oand (e1:::e2:::Enil)
  end.
>>
*)

Inductive and_cases: forall (e1: expr) (e2: expr), Type :=
  | and_case1: forall n1 t2, and_cases (Eop (Ointconst n1) Enil) (t2)
  | and_case2: forall t1 n2, and_cases (t1) (Eop (Ointconst n2) Enil)
  | and_default: forall (e1: expr) (e2: expr), and_cases e1 e2.

Definition and_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return and_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => and_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => and_case2 t1 n2
  | e1, e2 => and_default e1 e2
  end.

Definition and (e1: expr) (e2: expr) :=
  match and_match e1 e2 with
  | and_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      andimm n1 t2
  | and_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      andimm n2 t1
  | and_default e1 e2 =>
      Eop Oand (e1:::e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction orimm (n1: int) (e2: expr) :=
  if Int.eq n1 Int.zero then e2
  else if Int.eq n1 Int.mone then Eop (Ointconst Int.mone) Enil
  else match e2 with
       | Eop (Ointconst n2) Enil => Eop (Ointconst (Int.or n1 n2)) Enil
       | Eop (Oorimm n2) (t2:::Enil) => Eop (Oorimm (Int.or n1 n2)) (t2:::Enil)
       | _ => Eop (Oorimm n1) (e2:::Enil)
  end.
>>
*)

Inductive orimm_cases: forall (e2: expr), Type :=
  | orimm_case1: forall n2, orimm_cases (Eop (Ointconst n2) Enil)
  | orimm_case2: forall n2 t2, orimm_cases (Eop (Oorimm n2) (t2:::Enil))
  | orimm_default: forall (e2: expr), orimm_cases e2.

Definition orimm_match (e2: expr) :=
  match e2 as zz1 return orimm_cases zz1 with
  | Eop (Ointconst n2) Enil => orimm_case1 n2
  | Eop (Oorimm n2) (t2:::Enil) => orimm_case2 n2 t2
  | e2 => orimm_default e2
  end.

Definition orimm (n1: int) (e2: expr) :=
 if Int.eq n1 Int.zero then e2 else if Int.eq n1 Int.mone then Eop (Ointconst Int.mone) Enil else match orimm_match e2 with
  | orimm_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      Eop (Ointconst (Int.or n1 n2)) Enil
  | orimm_case2 n2 t2 => (* Eop (Oorimm n2) (t2:::Enil) *) 
      Eop (Oorimm (Int.or n1 n2)) (t2:::Enil)
  | orimm_default e2 =>
      Eop (Oorimm n1) (e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction or (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => orimm n1 t2
  | t1, Eop (Ointconst n2) Enil => orimm n2 t1
  | _, _ => Eop Oor (e1:::e2:::Enil)
  end.
>>
*)

Inductive or_cases: forall (e1: expr) (e2: expr), Type :=
  | or_case1: forall n1 t2, or_cases (Eop (Ointconst n1) Enil) (t2)
  | or_case2: forall t1 n2, or_cases (t1) (Eop (Ointconst n2) Enil)
  | or_default: forall (e1: expr) (e2: expr), or_cases e1 e2.

Definition or_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return or_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => or_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => or_case2 t1 n2
  | e1, e2 => or_default e1 e2
  end.

Definition or (e1: expr) (e2: expr) :=
  match or_match e1 e2 with
  | or_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      orimm n1 t2
  | or_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      orimm n2 t1
  | or_default e1 e2 =>
      Eop Oor (e1:::e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction xorimm (n1: int) (e2: expr) :=
  if Int.eq n1 Int.zero then e2 else
  match e2 with
  | Eop (Ointconst n2) Enil => Eop (Ointconst (Int.xor n1 n2)) Enil
  | Eop (Oxorimm n2) (t2:::Enil) =>
      let n := Int.xor n1 n2 in
      if Int.eq n Int.zero then t2 else Eop (Oxorimm n) (t2:::Enil)
  | _ => Eop (Oxorimm n1) (e2:::Enil)
  end.
>>
*)

Inductive xorimm_cases: forall (e2: expr), Type :=
  | xorimm_case1: forall n2, xorimm_cases (Eop (Ointconst n2) Enil)
  | xorimm_case2: forall n2 t2, xorimm_cases (Eop (Oxorimm n2) (t2:::Enil))
  | xorimm_default: forall (e2: expr), xorimm_cases e2.

Definition xorimm_match (e2: expr) :=
  match e2 as zz1 return xorimm_cases zz1 with
  | Eop (Ointconst n2) Enil => xorimm_case1 n2
  | Eop (Oxorimm n2) (t2:::Enil) => xorimm_case2 n2 t2
  | e2 => xorimm_default e2
  end.

Definition xorimm (n1: int) (e2: expr) :=
 if Int.eq n1 Int.zero then e2 else match xorimm_match e2 with
  | xorimm_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      Eop (Ointconst (Int.xor n1 n2)) Enil
  | xorimm_case2 n2 t2 => (* Eop (Oxorimm n2) (t2:::Enil) *) 
      let n := Int.xor n1 n2 in if Int.eq n Int.zero then t2 else Eop (Oxorimm n) (t2:::Enil)
  | xorimm_default e2 =>
      Eop (Oxorimm n1) (e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction xor (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 => xorimm n1 t2
  | t1, Eop (Ointconst n2) Enil => xorimm n2 t1
  | _, _ => Eop Oxor (e1:::e2:::Enil)
  end.
>>
*)

Inductive xor_cases: forall (e1: expr) (e2: expr), Type :=
  | xor_case1: forall n1 t2, xor_cases (Eop (Ointconst n1) Enil) (t2)
  | xor_case2: forall t1 n2, xor_cases (t1) (Eop (Ointconst n2) Enil)
  | xor_default: forall (e1: expr) (e2: expr), xor_cases e1 e2.

Definition xor_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return xor_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => xor_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => xor_case2 t1 n2
  | e1, e2 => xor_default e1 e2
  end.

Definition xor (e1: expr) (e2: expr) :=
  match xor_match e1 e2 with
  | xor_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      xorimm n1 t2
  | xor_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      xorimm n2 t1
  | xor_default e1 e2 =>
      Eop Oxor (e1:::e2:::Enil)
  end.


(** ** Integer logical negation *)

Definition notint (e: expr) := xorimm Int.mone e.

(** ** Integer division and modulus *)

Definition divs_base (e1: expr) (e2: expr) := Eop Odiv (e1:::e2:::Enil).
Definition mods_base (e1: expr) (e2: expr) := Eop Omod (e1:::e2:::Enil).
Definition divu_base (e1: expr) (e2: expr) := Eop Odivu (e1:::e2:::Enil).
Definition modu_base (e1: expr) (e2: expr) := Eop Omodu (e1:::e2:::Enil).

Definition shrximm (e1: expr) (n2: int) :=
  if Int.eq n2 Int.zero then e1 else Eop (Oshrximm n2) (e1:::Enil).

(* Alternate definition, not convenient for strength reduction during constant propagation *)
(*
(* n2 will be less than 31. *)

Definition shrximm_inner (e1: expr) (n2: int) :=
  Eop (Oshruimm (Int.sub Int.iwordsize n2))
      ((Eop (Oshrimm (Int.repr (Int.zwordsize - 1)))
            (e1 ::: Enil))
         ::: Enil).

Definition shrximm (e1: expr) (n2: int) :=
  if Int.eq n2 Int.zero then e1
  else Eop (Oshrimm n2)
           ((Eop Oadd (e1 ::: shrximm_inner e1 n2 ::: Enil))
              ::: Enil).
*)

(** ** General shifts *)

(** Original definition:
<<
Nondetfunction shl (e1: expr) (e2: expr) :=
  match e2 with
  | Eop (Ointconst n2) Enil => shlimm e1 n2
  | _ => Eop Oshl (e1:::e2:::Enil)
  end.
>>
*)

Inductive shl_cases: forall (e2: expr), Type :=
  | shl_case1: forall n2, shl_cases (Eop (Ointconst n2) Enil)
  | shl_default: forall (e2: expr), shl_cases e2.

Definition shl_match (e2: expr) :=
  match e2 as zz1 return shl_cases zz1 with
  | Eop (Ointconst n2) Enil => shl_case1 n2
  | e2 => shl_default e2
  end.

Definition shl (e1: expr) (e2: expr) :=
  match shl_match e2 with
  | shl_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      shlimm e1 n2
  | shl_default e2 =>
      Eop Oshl (e1:::e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction shr (e1: expr) (e2: expr) :=
  match e2 with
  | Eop (Ointconst n2) Enil => shrimm e1 n2
  | _ => Eop Oshr (e1:::e2:::Enil)
  end.
>>
*)

Inductive shr_cases: forall (e2: expr), Type :=
  | shr_case1: forall n2, shr_cases (Eop (Ointconst n2) Enil)
  | shr_default: forall (e2: expr), shr_cases e2.

Definition shr_match (e2: expr) :=
  match e2 as zz1 return shr_cases zz1 with
  | Eop (Ointconst n2) Enil => shr_case1 n2
  | e2 => shr_default e2
  end.

Definition shr (e1: expr) (e2: expr) :=
  match shr_match e2 with
  | shr_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      shrimm e1 n2
  | shr_default e2 =>
      Eop Oshr (e1:::e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction shru (e1: expr) (e2: expr) :=
  match e2 with
  | Eop (Ointconst n2) Enil => shruimm e1 n2
  | _ => Eop Oshru (e1:::e2:::Enil)
  end.
>>
*)

Inductive shru_cases: forall (e2: expr), Type :=
  | shru_case1: forall n2, shru_cases (Eop (Ointconst n2) Enil)
  | shru_default: forall (e2: expr), shru_cases e2.

Definition shru_match (e2: expr) :=
  match e2 as zz1 return shru_cases zz1 with
  | Eop (Ointconst n2) Enil => shru_case1 n2
  | e2 => shru_default e2
  end.

Definition shru (e1: expr) (e2: expr) :=
  match shru_match e2 with
  | shru_case1 n2 => (* Eop (Ointconst n2) Enil *) 
      shruimm e1 n2
  | shru_default e2 =>
      Eop Oshru (e1:::e2:::Enil)
  end.


(** ** Floating-point arithmetic *)

Definition negf (e: expr) :=  Eop Onegf (e ::: Enil).
Definition absf (e: expr) :=  Eop Oabsf (e ::: Enil).
Definition addf (e1 e2: expr) :=  Eop Oaddf (e1 ::: e2 ::: Enil).
Definition subf (e1 e2: expr) :=  Eop Osubf (e1 ::: e2 ::: Enil).
Definition mulf (e1 e2: expr) :=  Eop Omulf (e1 ::: e2 ::: Enil).

Definition negfs (e: expr) :=  Eop Onegfs (e ::: Enil).
Definition absfs (e: expr) :=  Eop Oabsfs (e ::: Enil).
Definition addfs (e1 e2: expr) :=  Eop Oaddfs (e1 ::: e2 ::: Enil).
Definition subfs (e1 e2: expr) :=  Eop Osubfs (e1 ::: e2 ::: Enil).
Definition mulfs (e1 e2: expr) :=  Eop Omulfs (e1 ::: e2 ::: Enil).

(** ** Comparisons *)

(** Original definition:
<<
Nondetfunction compimm (default: comparison -> int -> condition)
                       (sem: comparison -> int -> int -> bool)
                       (c: comparison) (e1: expr) (n2: int) :=
  match c, e1 with
  | c, Eop (Ointconst n1) Enil =>
      Eop (Ointconst (if sem c n1 n2 then Int.one else Int.zero)) Enil
  | Ceq, Eop (Ocmp c) el =>
      if Int.eq_dec n2 Int.zero then
        Eop (Ocmp (negate_condition c)) el
      else if Int.eq_dec n2 Int.one then
        Eop (Ocmp c) el
      else
        Eop (Ointconst Int.zero) Enil
  | Cne, Eop (Ocmp c) el =>
      if Int.eq_dec n2 Int.zero then
        Eop (Ocmp c) el
      else if Int.eq_dec n2 Int.one then
        Eop (Ocmp (negate_condition c)) el
      else
        Eop (Ointconst Int.one) Enil
  | _, _ =>
       Eop (Ocmp (default c n2)) (e1 ::: Enil)
  end.
>>
*)

Inductive compimm_cases: forall (c: comparison) (e1: expr) , Type :=
  | compimm_case1: forall c n1, compimm_cases (c) (Eop (Ointconst n1) Enil)
  | compimm_case2: forall c el, compimm_cases (Ceq) (Eop (Ocmp c) el)
  | compimm_case3: forall c el, compimm_cases (Cne) (Eop (Ocmp c) el)
  | compimm_default: forall (c: comparison) (e1: expr) , compimm_cases c e1.

Definition compimm_match (c: comparison) (e1: expr)  :=
  match c as zz1, e1 as zz2 return compimm_cases zz1 zz2 with
  | c, Eop (Ointconst n1) Enil => compimm_case1 c n1
  | Ceq, Eop (Ocmp c) el => compimm_case2 c el
  | Cne, Eop (Ocmp c) el => compimm_case3 c el
  | c, e1 => compimm_default c e1
  end.

Definition compimm (default: comparison -> int -> condition) (sem: comparison -> int -> int -> bool) (c: comparison) (e1: expr) (n2: int) :=
  match compimm_match c e1 with
  | compimm_case1 c n1 => (* c, Eop (Ointconst n1) Enil *) 
      Eop (Ointconst (if sem c n1 n2 then Int.one else Int.zero)) Enil
  | compimm_case2 c el => (* Ceq, Eop (Ocmp c) el *) 
      if Int.eq_dec n2 Int.zero then Eop (Ocmp (negate_condition c)) el else if Int.eq_dec n2 Int.one then Eop (Ocmp c) el else Eop (Ointconst Int.zero) Enil
  | compimm_case3 c el => (* Cne, Eop (Ocmp c) el *) 
      if Int.eq_dec n2 Int.zero then Eop (Ocmp c) el else if Int.eq_dec n2 Int.one then Eop (Ocmp (negate_condition c)) el else Eop (Ointconst Int.one) Enil
  | compimm_default c e1 =>
      Eop (Ocmp (default c n2)) (e1 ::: Enil)
  end.


(** Original definition:
<<
Nondetfunction comp (c: comparison) (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 =>
      compimm Ccompimm Int.cmp (swap_comparison c) t2 n1
  | t1, Eop (Ointconst n2) Enil =>
      compimm Ccompimm Int.cmp c t1 n2
  | _, _ =>
      Eop (Ocmp (Ccomp c)) (e1 ::: e2 ::: Enil)
  end.
>>
*)

Inductive comp_cases: forall (e1: expr) (e2: expr), Type :=
  | comp_case1: forall n1 t2, comp_cases (Eop (Ointconst n1) Enil) (t2)
  | comp_case2: forall t1 n2, comp_cases (t1) (Eop (Ointconst n2) Enil)
  | comp_default: forall (e1: expr) (e2: expr), comp_cases e1 e2.

Definition comp_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return comp_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => comp_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => comp_case2 t1 n2
  | e1, e2 => comp_default e1 e2
  end.

Definition comp (c: comparison) (e1: expr) (e2: expr) :=
  match comp_match e1 e2 with
  | comp_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      compimm Ccompimm Int.cmp (swap_comparison c) t2 n1
  | comp_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      compimm Ccompimm Int.cmp c t1 n2
  | comp_default e1 e2 =>
      Eop (Ocmp (Ccomp c)) (e1 ::: e2 ::: Enil)
  end.


(** Original definition:
<<
Nondetfunction compu (c: comparison) (e1: expr) (e2: expr) :=
  match e1, e2 with
  | Eop (Ointconst n1) Enil, t2 =>
      compimm Ccompuimm Int.cmpu (swap_comparison c) t2 n1
  | t1, Eop (Ointconst n2) Enil =>
      compimm Ccompuimm Int.cmpu c t1 n2
  | _, _ =>
      Eop (Ocmp (Ccompu c)) (e1 ::: e2 ::: Enil)
  end.
>>
*)

Inductive compu_cases: forall (e1: expr) (e2: expr), Type :=
  | compu_case1: forall n1 t2, compu_cases (Eop (Ointconst n1) Enil) (t2)
  | compu_case2: forall t1 n2, compu_cases (t1) (Eop (Ointconst n2) Enil)
  | compu_default: forall (e1: expr) (e2: expr), compu_cases e1 e2.

Definition compu_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return compu_cases zz1 zz2 with
  | Eop (Ointconst n1) Enil, t2 => compu_case1 n1 t2
  | t1, Eop (Ointconst n2) Enil => compu_case2 t1 n2
  | e1, e2 => compu_default e1 e2
  end.

Definition compu (c: comparison) (e1: expr) (e2: expr) :=
  match compu_match e1 e2 with
  | compu_case1 n1 t2 => (* Eop (Ointconst n1) Enil, t2 *) 
      compimm Ccompuimm Int.cmpu (swap_comparison c) t2 n1
  | compu_case2 t1 n2 => (* t1, Eop (Ointconst n2) Enil *) 
      compimm Ccompuimm Int.cmpu c t1 n2
  | compu_default e1 e2 =>
      Eop (Ocmp (Ccompu c)) (e1 ::: e2 ::: Enil)
  end.


Definition compf (c: comparison) (e1: expr) (e2: expr) :=
  Eop (Ocmp (Ccompf c)) (e1 ::: e2 ::: Enil).

Definition compfs (c: comparison) (e1: expr) (e2: expr) :=
  Eop (Ocmp (Ccompfs c)) (e1 ::: e2 ::: Enil).

(** ** Integer conversions *)

Definition cast8unsigned (e: expr) := andimm (Int.repr 255) e.

(** Original definition:
<<
Nondetfunction cast8signed (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil => Eop (Ointconst (Int.sign_ext 8 n)) Enil
  | _ =>  Eop Ocast8signed (e ::: Enil)
  end.
>>
*)

Inductive cast8signed_cases: forall (e: expr), Type :=
  | cast8signed_case1: forall n, cast8signed_cases (Eop (Ointconst n) Enil)
  | cast8signed_default: forall (e: expr), cast8signed_cases e.

Definition cast8signed_match (e: expr) :=
  match e as zz1 return cast8signed_cases zz1 with
  | Eop (Ointconst n) Enil => cast8signed_case1 n
  | e => cast8signed_default e
  end.

Definition cast8signed (e: expr) :=
  match cast8signed_match e with
  | cast8signed_case1 n => (* Eop (Ointconst n) Enil *) 
      Eop (Ointconst (Int.sign_ext 8 n)) Enil
  | cast8signed_default e =>
      Eop Ocast8signed (e ::: Enil)
  end.


Definition cast16unsigned (e: expr) := andimm (Int.repr 65535) e.

(** Original definition:
<<
Nondetfunction cast16signed (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil => Eop (Ointconst (Int.sign_ext 16 n)) Enil
  | _ => Eop Ocast16signed (e ::: Enil)
  end.
>>
*)

Inductive cast16signed_cases: forall (e: expr), Type :=
  | cast16signed_case1: forall n, cast16signed_cases (Eop (Ointconst n) Enil)
  | cast16signed_default: forall (e: expr), cast16signed_cases e.

Definition cast16signed_match (e: expr) :=
  match e as zz1 return cast16signed_cases zz1 with
  | Eop (Ointconst n) Enil => cast16signed_case1 n
  | e => cast16signed_default e
  end.

Definition cast16signed (e: expr) :=
  match cast16signed_match e with
  | cast16signed_case1 n => (* Eop (Ointconst n) Enil *) 
      Eop (Ointconst (Int.sign_ext 16 n)) Enil
  | cast16signed_default e =>
      Eop Ocast16signed (e ::: Enil)
  end.


(** ** Floating-point conversions *)

Definition intoffloat  (e: expr) := Eop Ointoffloat (e ::: Enil).
Definition intuoffloat (e: expr) := Eop Ointuoffloat (e ::: Enil).

(** Original definition:
<<
Nondetfunction floatofintu (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil => Eop (Ofloatconst (Float.of_intu n)) Enil
  | _ => Eop Ofloatofintu (e ::: Enil)
  end.
>>
*)

Inductive floatofintu_cases: forall (e: expr), Type :=
  | floatofintu_case1: forall n, floatofintu_cases (Eop (Ointconst n) Enil)
  | floatofintu_default: forall (e: expr), floatofintu_cases e.

Definition floatofintu_match (e: expr) :=
  match e as zz1 return floatofintu_cases zz1 with
  | Eop (Ointconst n) Enil => floatofintu_case1 n
  | e => floatofintu_default e
  end.

Definition floatofintu (e: expr) :=
  match floatofintu_match e with
  | floatofintu_case1 n => (* Eop (Ointconst n) Enil *) 
      Eop (Ofloatconst (Float.of_intu n)) Enil
  | floatofintu_default e =>
      Eop Ofloatofintu (e ::: Enil)
  end.


(** Original definition:
<<
Nondetfunction floatofint (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil => Eop (Ofloatconst (Float.of_int n)) Enil
  | _ => Eop Ofloatofint (e ::: Enil)
  end.
>>
*)

Inductive floatofint_cases: forall (e: expr), Type :=
  | floatofint_case1: forall n, floatofint_cases (Eop (Ointconst n) Enil)
  | floatofint_default: forall (e: expr), floatofint_cases e.

Definition floatofint_match (e: expr) :=
  match e as zz1 return floatofint_cases zz1 with
  | Eop (Ointconst n) Enil => floatofint_case1 n
  | e => floatofint_default e
  end.

Definition floatofint (e: expr) :=
  match floatofint_match e with
  | floatofint_case1 n => (* Eop (Ointconst n) Enil *) 
      Eop (Ofloatconst (Float.of_int n)) Enil
  | floatofint_default e =>
      Eop Ofloatofint (e ::: Enil)
  end.


Definition intofsingle (e: expr) := Eop Ointofsingle (e ::: Enil).
Definition singleofint (e: expr) := Eop Osingleofint (e ::: Enil).

Definition intuofsingle (e: expr) := Eop Ointuofsingle (e ::: Enil).
Definition singleofintu (e: expr) := Eop Osingleofintu (e ::: Enil).

Definition singleoffloat (e: expr) := Eop Osingleoffloat (e ::: Enil).
Definition floatofsingle (e: expr) := Eop Ofloatofsingle (e ::: Enil).

(** ** Selection *)

Definition select (ty: typ) (cond: condition) (args: exprlist) (e1 e2: expr)
   : option expr
   := None.
 
(** ** Recognition of addressing modes for load and store operations *)

(** Original definition:
<<
Nondetfunction addressing (chunk: memory_chunk) (e: expr) :=
  match e with
  | Eop (Oaddrstack n) Enil => (Ainstack n, Enil)
  | Eop (Oaddrsymbol id ofs) Enil => if Archi.pic_code tt then (Aindexed Ptrofs.zero, e:::Enil) else (Aglobal id ofs, Enil)
  | Eop (Oaddimm n) (e1:::Enil) => (Aindexed (Ptrofs.of_int n), e1:::Enil)
  | Eop (Oaddlimm n) (e1:::Enil) => (Aindexed (Ptrofs.of_int64 n), e1:::Enil)
  | _ => (Aindexed Ptrofs.zero, e:::Enil)
  end.
>>
*)

Inductive addressing_cases: forall (e: expr), Type :=
  | addressing_case1: forall n, addressing_cases (Eop (Oaddrstack n) Enil)
  | addressing_case2: forall id ofs, addressing_cases (Eop (Oaddrsymbol id ofs) Enil)
  | addressing_case3: forall n e1, addressing_cases (Eop (Oaddimm n) (e1:::Enil))
  | addressing_case4: forall n e1, addressing_cases (Eop (Oaddlimm n) (e1:::Enil))
  | addressing_default: forall (e: expr), addressing_cases e.

Definition addressing_match (e: expr) :=
  match e as zz1 return addressing_cases zz1 with
  | Eop (Oaddrstack n) Enil => addressing_case1 n
  | Eop (Oaddrsymbol id ofs) Enil => addressing_case2 id ofs
  | Eop (Oaddimm n) (e1:::Enil) => addressing_case3 n e1
  | Eop (Oaddlimm n) (e1:::Enil) => addressing_case4 n e1
  | e => addressing_default e
  end.

Definition addressing (chunk: memory_chunk) (e: expr) :=
  match addressing_match e with
  | addressing_case1 n => (* Eop (Oaddrstack n) Enil *) 
      (Ainstack n, Enil)
  | addressing_case2 id ofs => (* Eop (Oaddrsymbol id ofs) Enil *) 
      if Archi.pic_code tt then (Aindexed Ptrofs.zero, e:::Enil) else (Aglobal id ofs, Enil)
  | addressing_case3 n e1 => (* Eop (Oaddimm n) (e1:::Enil) *) 
      (Aindexed (Ptrofs.of_int n), e1:::Enil)
  | addressing_case4 n e1 => (* Eop (Oaddlimm n) (e1:::Enil) *) 
      (Aindexed (Ptrofs.of_int64 n), e1:::Enil)
  | addressing_default e =>
      (Aindexed Ptrofs.zero, e:::Enil)
  end.


(** ** Arguments of builtins *)

(** Original definition:
<<
Nondetfunction builtin_arg (e: expr) :=
  match e with
  | Eop (Ointconst n) Enil => BA_int n
  | Eop (Oaddrsymbol id ofs) Enil => BA_addrglobal id ofs
  | Eop (Oaddrstack ofs) Enil => BA_addrstack ofs
  | Eop Omakelong (Eop (Ointconst h) Enil ::: Eop (Ointconst l) Enil ::: Enil) =>
        BA_long (Int64.ofwords h l)
  | Eop Omakelong (h ::: l ::: Enil) => BA_splitlong (BA h) (BA l)
  | Eload chunk (Ainstack ofs) Enil => BA_loadstack chunk ofs
  | Eop (Oaddimm n) (e1:::Enil) =>
      if Archi.ptr64 then BA e else BA_addptr (BA e1) (BA_int n)
  | Eop (Oaddlimm n) (e1:::Enil) =>
      if Archi.ptr64 then BA_addptr (BA e1) (BA_long n) else BA e
  | _ => BA e
  end.
>>
*)

Inductive builtin_arg_cases: forall (e: expr), Type :=
  | builtin_arg_case1: forall n, builtin_arg_cases (Eop (Ointconst n) Enil)
  | builtin_arg_case2: forall id ofs, builtin_arg_cases (Eop (Oaddrsymbol id ofs) Enil)
  | builtin_arg_case3: forall ofs, builtin_arg_cases (Eop (Oaddrstack ofs) Enil)
  | builtin_arg_case4: forall h l, builtin_arg_cases (Eop Omakelong (Eop (Ointconst h) Enil ::: Eop (Ointconst l) Enil ::: Enil))
  | builtin_arg_case5: forall h l, builtin_arg_cases (Eop Omakelong (h ::: l ::: Enil))
  | builtin_arg_case6: forall chunk ofs, builtin_arg_cases (Eload chunk (Ainstack ofs) Enil)
  | builtin_arg_case7: forall n e1, builtin_arg_cases (Eop (Oaddimm n) (e1:::Enil))
  | builtin_arg_case8: forall n e1, builtin_arg_cases (Eop (Oaddlimm n) (e1:::Enil))
  | builtin_arg_default: forall (e: expr), builtin_arg_cases e.

Definition builtin_arg_match (e: expr) :=
  match e as zz1 return builtin_arg_cases zz1 with
  | Eop (Ointconst n) Enil => builtin_arg_case1 n
  | Eop (Oaddrsymbol id ofs) Enil => builtin_arg_case2 id ofs
  | Eop (Oaddrstack ofs) Enil => builtin_arg_case3 ofs
  | Eop Omakelong (Eop (Ointconst h) Enil ::: Eop (Ointconst l) Enil ::: Enil) => builtin_arg_case4 h l
  | Eop Omakelong (h ::: l ::: Enil) => builtin_arg_case5 h l
  | Eload chunk (Ainstack ofs) Enil => builtin_arg_case6 chunk ofs
  | Eop (Oaddimm n) (e1:::Enil) => builtin_arg_case7 n e1
  | Eop (Oaddlimm n) (e1:::Enil) => builtin_arg_case8 n e1
  | e => builtin_arg_default e
  end.

Definition builtin_arg (e: expr) :=
  match builtin_arg_match e with
  | builtin_arg_case1 n => (* Eop (Ointconst n) Enil *) 
      BA_int n
  | builtin_arg_case2 id ofs => (* Eop (Oaddrsymbol id ofs) Enil *) 
      BA_addrglobal id ofs
  | builtin_arg_case3 ofs => (* Eop (Oaddrstack ofs) Enil *) 
      BA_addrstack ofs
  | builtin_arg_case4 h l => (* Eop Omakelong (Eop (Ointconst h) Enil ::: Eop (Ointconst l) Enil ::: Enil) *) 
      BA_long (Int64.ofwords h l)
  | builtin_arg_case5 h l => (* Eop Omakelong (h ::: l ::: Enil) *) 
      BA_splitlong (BA h) (BA l)
  | builtin_arg_case6 chunk ofs => (* Eload chunk (Ainstack ofs) Enil *) 
      BA_loadstack chunk ofs
  | builtin_arg_case7 n e1 => (* Eop (Oaddimm n) (e1:::Enil) *) 
      if Archi.ptr64 then BA e else BA_addptr (BA e1) (BA_int n)
  | builtin_arg_case8 n e1 => (* Eop (Oaddlimm n) (e1:::Enil) *) 
      if Archi.ptr64 then BA_addptr (BA e1) (BA_long n) else BA e
  | builtin_arg_default e =>
      BA e
  end.


(** Platform-specific known builtins *)

Definition platform_builtin (b: platform_builtin) (args: exprlist) : option expr :=
  None.
