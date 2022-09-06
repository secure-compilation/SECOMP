(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                 Xavier Leroy, INRIA Paris                           *)
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

(** Instruction selection for 64-bit integer operations *)

Require Import Coqlib.
Require Import Compopts.
Require Import AST Integers Floats.
Require Import Op CminorSel.
Require Import SelectOp SplitLong.

Local Open Scope cminorsel_scope.
Local Open Scope string_scope.

Section SELECT.

Context {hf: helper_functions}.

Definition longconst (n: int64) : expr :=
  if Archi.splitlong then SplitLong.longconst n else Eop (Olongconst n) Enil.

Definition is_longconst (e: expr) :=
  if Archi.splitlong then SplitLong.is_longconst e else
  match e with
  | Eop (Olongconst n) Enil => Some n
  | _ => None
  end.

Definition intoflong (e: expr) :=
  if Archi.splitlong then SplitLong.intoflong e else
  match is_longconst e with
  | Some n => Eop (Ointconst (Int.repr (Int64.unsigned n))) Enil
  | None =>  Eop Olowlong (e ::: Enil)
  end.

Definition longofint (e: expr) :=
  if Archi.splitlong then SplitLong.longofint e else
  match is_intconst e with
  | Some n => longconst (Int64.repr (Int.signed n))
  | None =>  Eop Ocast32signed (e ::: Enil)
  end.

Definition longofintu (e: expr) :=
  if Archi.splitlong then SplitLong.longofintu e else
  match is_intconst e with
  | Some n => longconst (Int64.repr (Int.unsigned n))
  | None =>  Eop Ocast32unsigned (e ::: Enil)
  end.

(** ** Integer addition and pointer addition *)

(** Original definition:
<<
Nondetfunction addlimm (n: int64) (e: expr) :=
  if Int64.eq n Int64.zero then e else
  match e with
  | Eop (Olongconst m) Enil => longconst (Int64.add n m)
  | Eop (Oaddrsymbol s m) Enil   => Eop (Oaddrsymbol s (Ptrofs.add (Ptrofs.of_int64 n) m)) Enil
  | Eop (Oaddrstack m) Enil      => Eop (Oaddrstack (Ptrofs.add (Ptrofs.of_int64 n) m)) Enil
  | Eop (Oaddlimm m) (t ::: Enil) => Eop (Oaddlimm(Int64.add n m)) (t ::: Enil)
  | _ => Eop (Oaddlimm n) (e ::: Enil)
  end.
>>
*)

Inductive addlimm_cases: forall (e: expr), Type :=
  | addlimm_case1: forall m, addlimm_cases (Eop (Olongconst m) Enil)
  | addlimm_case2: forall s m, addlimm_cases (Eop (Oaddrsymbol s m) Enil)
  | addlimm_case3: forall m, addlimm_cases (Eop (Oaddrstack m) Enil)
  | addlimm_case4: forall m t, addlimm_cases (Eop (Oaddlimm m) (t ::: Enil))
  | addlimm_default: forall (e: expr), addlimm_cases e.

Definition addlimm_match (e: expr) :=
  match e as zz1 return addlimm_cases zz1 with
  | Eop (Olongconst m) Enil => addlimm_case1 m
  | Eop (Oaddrsymbol s m) Enil => addlimm_case2 s m
  | Eop (Oaddrstack m) Enil => addlimm_case3 m
  | Eop (Oaddlimm m) (t ::: Enil) => addlimm_case4 m t
  | e => addlimm_default e
  end.

Definition addlimm (n: int64) (e: expr) :=
 if Int64.eq n Int64.zero then e else match addlimm_match e with
  | addlimm_case1 m => (* Eop (Olongconst m) Enil *) 
      longconst (Int64.add n m)
  | addlimm_case2 s m => (* Eop (Oaddrsymbol s m) Enil *) 
      Eop (Oaddrsymbol s (Ptrofs.add (Ptrofs.of_int64 n) m)) Enil
  | addlimm_case3 m => (* Eop (Oaddrstack m) Enil *) 
      Eop (Oaddrstack (Ptrofs.add (Ptrofs.of_int64 n) m)) Enil
  | addlimm_case4 m t => (* Eop (Oaddlimm m) (t ::: Enil) *) 
      Eop (Oaddlimm(Int64.add n m)) (t ::: Enil)
  | addlimm_default e =>
      Eop (Oaddlimm n) (e ::: Enil)
  end.


(** Original definition:
<<
Nondetfunction addl (e1: expr) (e2: expr) :=
  if Archi.splitlong then SplitLong.addl e1 e2 else
  match e1, e2 with
  | Eop (Olongconst n1) Enil, t2 => addlimm n1 t2
  | t1, Eop (Olongconst n2) Enil => addlimm n2 t1
  | Eop (Oaddlimm n1) (t1:::Enil), Eop (Oaddlimm n2) (t2:::Enil) =>
      addlimm (Int64.add n1 n2) (Eop Oaddl (t1:::t2:::Enil))
  | Eop (Oaddlimm n1) (t1:::Enil), Eop (Oaddrstack n2) Enil =>
      Eop Oaddl (Eop (Oaddrstack (Ptrofs.add (Ptrofs.of_int64 n1) n2)) Enil ::: t1 ::: Enil)
  | Eop (Oaddrstack n1) Enil, Eop (Oaddlimm n2) (t2:::Enil) =>
      Eop Oaddl (Eop (Oaddrstack (Ptrofs.add n1 (Ptrofs.of_int64 n2))) Enil ::: t2 ::: Enil)
  | Eop (Oaddlimm n1) (t1:::Enil), t2 =>
      addlimm n1 (Eop Oaddl (t1:::t2:::Enil))
  | t1, Eop (Oaddlimm n2) (t2:::Enil) =>
      addlimm n2 (Eop Oaddl (t1:::t2:::Enil))
  | _, _ => Eop Oaddl (e1:::e2:::Enil)
  end.
>>
*)

Inductive addl_cases: forall (e1: expr) (e2: expr), Type :=
  | addl_case1: forall n1 t2, addl_cases (Eop (Olongconst n1) Enil) (t2)
  | addl_case2: forall t1 n2, addl_cases (t1) (Eop (Olongconst n2) Enil)
  | addl_case3: forall n1 t1 n2 t2, addl_cases (Eop (Oaddlimm n1) (t1:::Enil)) (Eop (Oaddlimm n2) (t2:::Enil))
  | addl_case4: forall n1 t1 n2, addl_cases (Eop (Oaddlimm n1) (t1:::Enil)) (Eop (Oaddrstack n2) Enil)
  | addl_case5: forall n1 n2 t2, addl_cases (Eop (Oaddrstack n1) Enil) (Eop (Oaddlimm n2) (t2:::Enil))
  | addl_case6: forall n1 t1 t2, addl_cases (Eop (Oaddlimm n1) (t1:::Enil)) (t2)
  | addl_case7: forall t1 n2 t2, addl_cases (t1) (Eop (Oaddlimm n2) (t2:::Enil))
  | addl_default: forall (e1: expr) (e2: expr), addl_cases e1 e2.

Definition addl_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return addl_cases zz1 zz2 with
  | Eop (Olongconst n1) Enil, t2 => addl_case1 n1 t2
  | t1, Eop (Olongconst n2) Enil => addl_case2 t1 n2
  | Eop (Oaddlimm n1) (t1:::Enil), Eop (Oaddlimm n2) (t2:::Enil) => addl_case3 n1 t1 n2 t2
  | Eop (Oaddlimm n1) (t1:::Enil), Eop (Oaddrstack n2) Enil => addl_case4 n1 t1 n2
  | Eop (Oaddrstack n1) Enil, Eop (Oaddlimm n2) (t2:::Enil) => addl_case5 n1 n2 t2
  | Eop (Oaddlimm n1) (t1:::Enil), t2 => addl_case6 n1 t1 t2
  | t1, Eop (Oaddlimm n2) (t2:::Enil) => addl_case7 t1 n2 t2
  | e1, e2 => addl_default e1 e2
  end.

Definition addl (e1: expr) (e2: expr) :=
 if Archi.splitlong then SplitLong.addl e1 e2 else match addl_match e1 e2 with
  | addl_case1 n1 t2 => (* Eop (Olongconst n1) Enil, t2 *) 
      addlimm n1 t2
  | addl_case2 t1 n2 => (* t1, Eop (Olongconst n2) Enil *) 
      addlimm n2 t1
  | addl_case3 n1 t1 n2 t2 => (* Eop (Oaddlimm n1) (t1:::Enil), Eop (Oaddlimm n2) (t2:::Enil) *) 
      addlimm (Int64.add n1 n2) (Eop Oaddl (t1:::t2:::Enil))
  | addl_case4 n1 t1 n2 => (* Eop (Oaddlimm n1) (t1:::Enil), Eop (Oaddrstack n2) Enil *) 
      Eop Oaddl (Eop (Oaddrstack (Ptrofs.add (Ptrofs.of_int64 n1) n2)) Enil ::: t1 ::: Enil)
  | addl_case5 n1 n2 t2 => (* Eop (Oaddrstack n1) Enil, Eop (Oaddlimm n2) (t2:::Enil) *) 
      Eop Oaddl (Eop (Oaddrstack (Ptrofs.add n1 (Ptrofs.of_int64 n2))) Enil ::: t2 ::: Enil)
  | addl_case6 n1 t1 t2 => (* Eop (Oaddlimm n1) (t1:::Enil), t2 *) 
      addlimm n1 (Eop Oaddl (t1:::t2:::Enil))
  | addl_case7 t1 n2 t2 => (* t1, Eop (Oaddlimm n2) (t2:::Enil) *) 
      addlimm n2 (Eop Oaddl (t1:::t2:::Enil))
  | addl_default e1 e2 =>
      Eop Oaddl (e1:::e2:::Enil)
  end.


(** ** Integer and pointer subtraction *)

(** Original definition:
<<
Nondetfunction subl (e1: expr) (e2: expr) :=
  if Archi.splitlong then SplitLong.subl e1 e2 else
  match e1, e2 with
  | t1, Eop (Olongconst n2) Enil =>
      addlimm (Int64.neg n2) t1
  | Eop (Oaddlimm n1) (t1:::Enil), Eop (Oaddlimm n2) (t2:::Enil) =>
      addlimm (Int64.sub n1 n2) (Eop Osubl (t1:::t2:::Enil))
  | Eop (Oaddlimm n1) (t1:::Enil), t2 =>
      addlimm n1 (Eop Osubl (t1:::t2:::Enil))
  | t1, Eop (Oaddlimm n2) (t2:::Enil) =>
      addlimm (Int64.neg n2) (Eop Osubl (t1:::t2:::Enil))
  | _, _ => Eop Osubl (e1:::e2:::Enil)
  end.
>>
*)

Inductive subl_cases: forall (e1: expr) (e2: expr), Type :=
  | subl_case1: forall t1 n2, subl_cases (t1) (Eop (Olongconst n2) Enil)
  | subl_case2: forall n1 t1 n2 t2, subl_cases (Eop (Oaddlimm n1) (t1:::Enil)) (Eop (Oaddlimm n2) (t2:::Enil))
  | subl_case3: forall n1 t1 t2, subl_cases (Eop (Oaddlimm n1) (t1:::Enil)) (t2)
  | subl_case4: forall t1 n2 t2, subl_cases (t1) (Eop (Oaddlimm n2) (t2:::Enil))
  | subl_default: forall (e1: expr) (e2: expr), subl_cases e1 e2.

Definition subl_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return subl_cases zz1 zz2 with
  | t1, Eop (Olongconst n2) Enil => subl_case1 t1 n2
  | Eop (Oaddlimm n1) (t1:::Enil), Eop (Oaddlimm n2) (t2:::Enil) => subl_case2 n1 t1 n2 t2
  | Eop (Oaddlimm n1) (t1:::Enil), t2 => subl_case3 n1 t1 t2
  | t1, Eop (Oaddlimm n2) (t2:::Enil) => subl_case4 t1 n2 t2
  | e1, e2 => subl_default e1 e2
  end.

Definition subl (e1: expr) (e2: expr) :=
 if Archi.splitlong then SplitLong.subl e1 e2 else match subl_match e1 e2 with
  | subl_case1 t1 n2 => (* t1, Eop (Olongconst n2) Enil *) 
      addlimm (Int64.neg n2) t1
  | subl_case2 n1 t1 n2 t2 => (* Eop (Oaddlimm n1) (t1:::Enil), Eop (Oaddlimm n2) (t2:::Enil) *) 
      addlimm (Int64.sub n1 n2) (Eop Osubl (t1:::t2:::Enil))
  | subl_case3 n1 t1 t2 => (* Eop (Oaddlimm n1) (t1:::Enil), t2 *) 
      addlimm n1 (Eop Osubl (t1:::t2:::Enil))
  | subl_case4 t1 n2 t2 => (* t1, Eop (Oaddlimm n2) (t2:::Enil) *) 
      addlimm (Int64.neg n2) (Eop Osubl (t1:::t2:::Enil))
  | subl_default e1 e2 =>
      Eop Osubl (e1:::e2:::Enil)
  end.


Definition negl (e: expr) :=
  if Archi.splitlong then SplitLong.negl e else
  match is_longconst e with
  | Some n => longconst (Int64.neg n)
  | None =>  Eop Onegl (e ::: Enil)
  end.

(** ** Immediate shifts *)

(** Original definition:
<<
Nondetfunction shllimm (e1: expr) (n: int) :=
  if Archi.splitlong then SplitLong.shllimm e1 n else
  if Int.eq n Int.zero then
    e1
  else if negb (Int.ltu n Int64.iwordsize') then
    Eop Oshll (e1 ::: Eop (Ointconst n) Enil ::: Enil)
  else match e1 with
    | Eop (Olongconst n1) Enil =>
        longconst (Int64.shl' n1 n)
    | Eop (Oshllimm n1) (t1:::Enil) =>
        if Int.ltu (Int.add n n1) Int64.iwordsize'
        then Eop (Oshllimm (Int.add n n1)) (t1:::Enil)
        else Eop (Oshllimm n) (e1:::Enil)
    | _ =>
        Eop (Oshllimm n) (e1:::Enil)
  end.
>>
*)

Inductive shllimm_cases: forall (e1: expr) , Type :=
  | shllimm_case1: forall n1, shllimm_cases (Eop (Olongconst n1) Enil)
  | shllimm_case2: forall n1 t1, shllimm_cases (Eop (Oshllimm n1) (t1:::Enil))
  | shllimm_default: forall (e1: expr) , shllimm_cases e1.

Definition shllimm_match (e1: expr)  :=
  match e1 as zz1 return shllimm_cases zz1 with
  | Eop (Olongconst n1) Enil => shllimm_case1 n1
  | Eop (Oshllimm n1) (t1:::Enil) => shllimm_case2 n1 t1
  | e1 => shllimm_default e1
  end.

Definition shllimm (e1: expr) (n: int) :=
 if Archi.splitlong then SplitLong.shllimm e1 n else if Int.eq n Int.zero then e1 else if negb (Int.ltu n Int64.iwordsize') then Eop Oshll (e1 ::: Eop (Ointconst n) Enil ::: Enil) else match shllimm_match e1 with
  | shllimm_case1 n1 => (* Eop (Olongconst n1) Enil *) 
      longconst (Int64.shl' n1 n)
  | shllimm_case2 n1 t1 => (* Eop (Oshllimm n1) (t1:::Enil) *) 
      if Int.ltu (Int.add n n1) Int64.iwordsize' then Eop (Oshllimm (Int.add n n1)) (t1:::Enil) else Eop (Oshllimm n) (e1:::Enil)
  | shllimm_default e1 =>
      Eop (Oshllimm n) (e1:::Enil)
  end.


(** Original definition:
<<
Nondetfunction shrluimm (e1: expr) (n: int) :=
  if Archi.splitlong then SplitLong.shrluimm e1 n else
  if Int.eq n Int.zero then e1 else
  if negb (Int.ltu n Int64.iwordsize') then
    Eop Oshrlu (e1:::Eop (Ointconst n) Enil:::Enil)
  else
    match e1 with
    | Eop (Olongconst n1) Enil =>
        longconst (Int64.shru' n1 n)
    | Eop (Oshrluimm n1) (t1:::Enil) =>
        if Int.ltu (Int.add n n1) Int64.iwordsize'
        then Eop (Oshrluimm (Int.add n n1)) (t1:::Enil)
        else Eop (Oshrluimm n) (e1:::Enil)
    | _ =>
        Eop (Oshrluimm n) (e1:::Enil)
    end.
>>
*)

Inductive shrluimm_cases: forall (e1: expr) , Type :=
  | shrluimm_case1: forall n1, shrluimm_cases (Eop (Olongconst n1) Enil)
  | shrluimm_case2: forall n1 t1, shrluimm_cases (Eop (Oshrluimm n1) (t1:::Enil))
  | shrluimm_default: forall (e1: expr) , shrluimm_cases e1.

Definition shrluimm_match (e1: expr)  :=
  match e1 as zz1 return shrluimm_cases zz1 with
  | Eop (Olongconst n1) Enil => shrluimm_case1 n1
  | Eop (Oshrluimm n1) (t1:::Enil) => shrluimm_case2 n1 t1
  | e1 => shrluimm_default e1
  end.

Definition shrluimm (e1: expr) (n: int) :=
 if Archi.splitlong then SplitLong.shrluimm e1 n else if Int.eq n Int.zero then e1 else if negb (Int.ltu n Int64.iwordsize') then Eop Oshrlu (e1:::Eop (Ointconst n) Enil:::Enil) else match shrluimm_match e1 with
  | shrluimm_case1 n1 => (* Eop (Olongconst n1) Enil *) 
      longconst (Int64.shru' n1 n)
  | shrluimm_case2 n1 t1 => (* Eop (Oshrluimm n1) (t1:::Enil) *) 
      if Int.ltu (Int.add n n1) Int64.iwordsize' then Eop (Oshrluimm (Int.add n n1)) (t1:::Enil) else Eop (Oshrluimm n) (e1:::Enil)
  | shrluimm_default e1 =>
      Eop (Oshrluimm n) (e1:::Enil)
  end.


(** Original definition:
<<
Nondetfunction shrlimm (e1: expr) (n: int) :=
  if Archi.splitlong then SplitLong.shrlimm e1 n else
  if Int.eq n Int.zero then e1 else
  if negb (Int.ltu n Int64.iwordsize') then
    Eop Oshrl (e1:::Eop (Ointconst n) Enil:::Enil)
  else
  match e1 with
  | Eop (Olongconst n1) Enil =>
      longconst (Int64.shr' n1 n)
  | Eop (Oshrlimm n1) (t1:::Enil) =>
      if Int.ltu (Int.add n n1) Int64.iwordsize'
      then Eop (Oshrlimm (Int.add n n1)) (t1:::Enil)
      else Eop (Oshrlimm n) (e1:::Enil)
  | _ =>
      Eop (Oshrlimm n) (e1:::Enil)
  end.
>>
*)

Inductive shrlimm_cases: forall (e1: expr) , Type :=
  | shrlimm_case1: forall n1, shrlimm_cases (Eop (Olongconst n1) Enil)
  | shrlimm_case2: forall n1 t1, shrlimm_cases (Eop (Oshrlimm n1) (t1:::Enil))
  | shrlimm_default: forall (e1: expr) , shrlimm_cases e1.

Definition shrlimm_match (e1: expr)  :=
  match e1 as zz1 return shrlimm_cases zz1 with
  | Eop (Olongconst n1) Enil => shrlimm_case1 n1
  | Eop (Oshrlimm n1) (t1:::Enil) => shrlimm_case2 n1 t1
  | e1 => shrlimm_default e1
  end.

Definition shrlimm (e1: expr) (n: int) :=
 if Archi.splitlong then SplitLong.shrlimm e1 n else if Int.eq n Int.zero then e1 else if negb (Int.ltu n Int64.iwordsize') then Eop Oshrl (e1:::Eop (Ointconst n) Enil:::Enil) else match shrlimm_match e1 with
  | shrlimm_case1 n1 => (* Eop (Olongconst n1) Enil *) 
      longconst (Int64.shr' n1 n)
  | shrlimm_case2 n1 t1 => (* Eop (Oshrlimm n1) (t1:::Enil) *) 
      if Int.ltu (Int.add n n1) Int64.iwordsize' then Eop (Oshrlimm (Int.add n n1)) (t1:::Enil) else Eop (Oshrlimm n) (e1:::Enil)
  | shrlimm_default e1 =>
      Eop (Oshrlimm n) (e1:::Enil)
  end.


(** ** General shifts *)

Definition shll (e1: expr) (e2: expr) :=
  if Archi.splitlong then SplitLong.shll e1 e2 else
  match is_intconst e2 with
  | Some n2 => shllimm e1 n2
  | None => Eop Oshll (e1:::e2:::Enil)
  end.

Definition shrl (e1: expr) (e2: expr) :=
  if Archi.splitlong then SplitLong.shrl e1 e2 else
  match is_intconst e2 with
  | Some n2 => shrlimm e1 n2
  | None => Eop Oshrl (e1:::e2:::Enil)
  end.

Definition shrlu (e1: expr) (e2: expr) :=
  if Archi.splitlong then SplitLong.shrlu e1 e2 else
  match is_intconst e2 with
  | Some n2 => shrluimm e1 n2
  | _ => Eop Oshrlu (e1:::e2:::Enil)
  end.

(** ** Integer multiply *)

Definition mullimm_base (n1: int64) (e2: expr) :=
  match Int64.one_bits' n1 with
  | i :: nil =>
      shllimm e2 i
  | i :: j :: nil =>
      Elet e2 (addl (shllimm (Eletvar 0) i) (shllimm (Eletvar 0) j))
  | _ =>
      Eop Omull (e2 ::: longconst n1 ::: Enil)
  end.

(** Original definition:
<<
Nondetfunction mullimm (n1: int64) (e2: expr) :=
  if Archi.splitlong then SplitLong.mullimm n1 e2
  else if Int64.eq n1 Int64.zero then longconst Int64.zero
  else if Int64.eq n1 Int64.one then e2
  else match e2 with
  | Eop (Olongconst n2) Enil => longconst (Int64.mul n1 n2)
  | Eop (Oaddlimm n2) (t2:::Enil) => addlimm (Int64.mul n1 n2) (mullimm_base n1 t2)
  | _ => mullimm_base n1 e2
  end.
>>
*)

Inductive mullimm_cases: forall (e2: expr), Type :=
  | mullimm_case1: forall n2, mullimm_cases (Eop (Olongconst n2) Enil)
  | mullimm_case2: forall n2 t2, mullimm_cases (Eop (Oaddlimm n2) (t2:::Enil))
  | mullimm_default: forall (e2: expr), mullimm_cases e2.

Definition mullimm_match (e2: expr) :=
  match e2 as zz1 return mullimm_cases zz1 with
  | Eop (Olongconst n2) Enil => mullimm_case1 n2
  | Eop (Oaddlimm n2) (t2:::Enil) => mullimm_case2 n2 t2
  | e2 => mullimm_default e2
  end.

Definition mullimm (n1: int64) (e2: expr) :=
 if Archi.splitlong then SplitLong.mullimm n1 e2 else if Int64.eq n1 Int64.zero then longconst Int64.zero else if Int64.eq n1 Int64.one then e2 else match mullimm_match e2 with
  | mullimm_case1 n2 => (* Eop (Olongconst n2) Enil *) 
      longconst (Int64.mul n1 n2)
  | mullimm_case2 n2 t2 => (* Eop (Oaddlimm n2) (t2:::Enil) *) 
      addlimm (Int64.mul n1 n2) (mullimm_base n1 t2)
  | mullimm_default e2 =>
      mullimm_base n1 e2
  end.


(** Original definition:
<<
Nondetfunction mull (e1: expr) (e2: expr) :=
  if Archi.splitlong then SplitLong.mull e1 e2 else
  match e1, e2 with
  | Eop (Olongconst n1) Enil, t2 => mullimm n1 t2
  | t1, Eop (Olongconst n2) Enil => mullimm n2 t1
  | _, _ => Eop Omull (e1:::e2:::Enil)
  end.
>>
*)

Inductive mull_cases: forall (e1: expr) (e2: expr), Type :=
  | mull_case1: forall n1 t2, mull_cases (Eop (Olongconst n1) Enil) (t2)
  | mull_case2: forall t1 n2, mull_cases (t1) (Eop (Olongconst n2) Enil)
  | mull_default: forall (e1: expr) (e2: expr), mull_cases e1 e2.

Definition mull_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return mull_cases zz1 zz2 with
  | Eop (Olongconst n1) Enil, t2 => mull_case1 n1 t2
  | t1, Eop (Olongconst n2) Enil => mull_case2 t1 n2
  | e1, e2 => mull_default e1 e2
  end.

Definition mull (e1: expr) (e2: expr) :=
 if Archi.splitlong then SplitLong.mull e1 e2 else match mull_match e1 e2 with
  | mull_case1 n1 t2 => (* Eop (Olongconst n1) Enil, t2 *) 
      mullimm n1 t2
  | mull_case2 t1 n2 => (* t1, Eop (Olongconst n2) Enil *) 
      mullimm n2 t1
  | mull_default e1 e2 =>
      Eop Omull (e1:::e2:::Enil)
  end.


Definition mullhu (e1: expr) (n2: int64) :=
  if Archi.splitlong then SplitLong.mullhu e1 n2 else
  Eop Omullhu (e1 ::: longconst n2 ::: Enil).

Definition mullhs (e1: expr) (n2: int64) :=
  if Archi.splitlong then SplitLong.mullhs e1 n2 else
  Eop Omullhs (e1 ::: longconst n2 ::: Enil).

(** ** Bitwise and, or, xor *)

(** Original definition:
<<
Nondetfunction andlimm (n1: int64) (e2: expr) := 
  if Int64.eq n1 Int64.zero then longconst Int64.zero else
  if Int64.eq n1 Int64.mone then e2 else
  match e2 with
  | Eop (Olongconst n2) Enil =>
      longconst (Int64.and n1 n2)
  | Eop (Oandlimm n2) (t2:::Enil) =>
      Eop (Oandlimm (Int64.and n1 n2)) (t2:::Enil)
  | _ =>
      Eop (Oandlimm n1) (e2:::Enil)
  end.
>>
*)

Inductive andlimm_cases: forall (e2: expr), Type :=
  | andlimm_case1: forall n2, andlimm_cases (Eop (Olongconst n2) Enil)
  | andlimm_case2: forall n2 t2, andlimm_cases (Eop (Oandlimm n2) (t2:::Enil))
  | andlimm_default: forall (e2: expr), andlimm_cases e2.

Definition andlimm_match (e2: expr) :=
  match e2 as zz1 return andlimm_cases zz1 with
  | Eop (Olongconst n2) Enil => andlimm_case1 n2
  | Eop (Oandlimm n2) (t2:::Enil) => andlimm_case2 n2 t2
  | e2 => andlimm_default e2
  end.

Definition andlimm (n1: int64) (e2: expr) :=
 if Int64.eq n1 Int64.zero then longconst Int64.zero else if Int64.eq n1 Int64.mone then e2 else match andlimm_match e2 with
  | andlimm_case1 n2 => (* Eop (Olongconst n2) Enil *) 
      longconst (Int64.and n1 n2)
  | andlimm_case2 n2 t2 => (* Eop (Oandlimm n2) (t2:::Enil) *) 
      Eop (Oandlimm (Int64.and n1 n2)) (t2:::Enil)
  | andlimm_default e2 =>
      Eop (Oandlimm n1) (e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction andl (e1: expr) (e2: expr) :=
  if Archi.splitlong then SplitLong.andl e1 e2 else
  match e1, e2 with
  | Eop (Olongconst n1) Enil, t2 => andlimm n1 t2
  | t1, Eop (Olongconst n2) Enil => andlimm n2 t1
  | _, _ => Eop Oandl (e1:::e2:::Enil)
  end.
>>
*)

Inductive andl_cases: forall (e1: expr) (e2: expr), Type :=
  | andl_case1: forall n1 t2, andl_cases (Eop (Olongconst n1) Enil) (t2)
  | andl_case2: forall t1 n2, andl_cases (t1) (Eop (Olongconst n2) Enil)
  | andl_default: forall (e1: expr) (e2: expr), andl_cases e1 e2.

Definition andl_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return andl_cases zz1 zz2 with
  | Eop (Olongconst n1) Enil, t2 => andl_case1 n1 t2
  | t1, Eop (Olongconst n2) Enil => andl_case2 t1 n2
  | e1, e2 => andl_default e1 e2
  end.

Definition andl (e1: expr) (e2: expr) :=
 if Archi.splitlong then SplitLong.andl e1 e2 else match andl_match e1 e2 with
  | andl_case1 n1 t2 => (* Eop (Olongconst n1) Enil, t2 *) 
      andlimm n1 t2
  | andl_case2 t1 n2 => (* t1, Eop (Olongconst n2) Enil *) 
      andlimm n2 t1
  | andl_default e1 e2 =>
      Eop Oandl (e1:::e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction orlimm (n1: int64) (e2: expr) :=
  if Int64.eq n1 Int64.zero then e2 else
  if Int64.eq n1 Int64.mone then longconst Int64.mone else
  match e2 with
  | Eop (Olongconst n2) Enil => longconst (Int64.or n1 n2)
  | Eop (Oorlimm n2) (t2:::Enil) => Eop (Oorlimm (Int64.or n1 n2)) (t2:::Enil)
  | _ => Eop (Oorlimm n1) (e2:::Enil)
  end.
>>
*)

Inductive orlimm_cases: forall (e2: expr), Type :=
  | orlimm_case1: forall n2, orlimm_cases (Eop (Olongconst n2) Enil)
  | orlimm_case2: forall n2 t2, orlimm_cases (Eop (Oorlimm n2) (t2:::Enil))
  | orlimm_default: forall (e2: expr), orlimm_cases e2.

Definition orlimm_match (e2: expr) :=
  match e2 as zz1 return orlimm_cases zz1 with
  | Eop (Olongconst n2) Enil => orlimm_case1 n2
  | Eop (Oorlimm n2) (t2:::Enil) => orlimm_case2 n2 t2
  | e2 => orlimm_default e2
  end.

Definition orlimm (n1: int64) (e2: expr) :=
 if Int64.eq n1 Int64.zero then e2 else if Int64.eq n1 Int64.mone then longconst Int64.mone else match orlimm_match e2 with
  | orlimm_case1 n2 => (* Eop (Olongconst n2) Enil *) 
      longconst (Int64.or n1 n2)
  | orlimm_case2 n2 t2 => (* Eop (Oorlimm n2) (t2:::Enil) *) 
      Eop (Oorlimm (Int64.or n1 n2)) (t2:::Enil)
  | orlimm_default e2 =>
      Eop (Oorlimm n1) (e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction orl (e1: expr) (e2: expr) :=
  if Archi.splitlong then SplitLong.orl e1 e2 else
  match e1, e2 with
  | Eop (Olongconst n1) Enil, t2 => orlimm n1 t2
  | t1, Eop (Olongconst n2) Enil => orlimm n2 t1
  | _, _ => Eop Oorl (e1:::e2:::Enil)
  end.
>>
*)

Inductive orl_cases: forall (e1: expr) (e2: expr), Type :=
  | orl_case1: forall n1 t2, orl_cases (Eop (Olongconst n1) Enil) (t2)
  | orl_case2: forall t1 n2, orl_cases (t1) (Eop (Olongconst n2) Enil)
  | orl_default: forall (e1: expr) (e2: expr), orl_cases e1 e2.

Definition orl_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return orl_cases zz1 zz2 with
  | Eop (Olongconst n1) Enil, t2 => orl_case1 n1 t2
  | t1, Eop (Olongconst n2) Enil => orl_case2 t1 n2
  | e1, e2 => orl_default e1 e2
  end.

Definition orl (e1: expr) (e2: expr) :=
 if Archi.splitlong then SplitLong.orl e1 e2 else match orl_match e1 e2 with
  | orl_case1 n1 t2 => (* Eop (Olongconst n1) Enil, t2 *) 
      orlimm n1 t2
  | orl_case2 t1 n2 => (* t1, Eop (Olongconst n2) Enil *) 
      orlimm n2 t1
  | orl_default e1 e2 =>
      Eop Oorl (e1:::e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction xorlimm (n1: int64) (e2: expr) :=
  if Int64.eq n1 Int64.zero then e2 else
  match e2 with
  | Eop (Olongconst n2) Enil => longconst (Int64.xor n1 n2)
  | Eop (Oxorlimm n2) (t2:::Enil) =>
      let n := Int64.xor n1 n2 in
      if Int64.eq n Int64.zero then t2 else Eop (Oxorlimm n) (t2:::Enil)
  | _ => Eop (Oxorlimm n1) (e2:::Enil)
  end.
>>
*)

Inductive xorlimm_cases: forall (e2: expr), Type :=
  | xorlimm_case1: forall n2, xorlimm_cases (Eop (Olongconst n2) Enil)
  | xorlimm_case2: forall n2 t2, xorlimm_cases (Eop (Oxorlimm n2) (t2:::Enil))
  | xorlimm_default: forall (e2: expr), xorlimm_cases e2.

Definition xorlimm_match (e2: expr) :=
  match e2 as zz1 return xorlimm_cases zz1 with
  | Eop (Olongconst n2) Enil => xorlimm_case1 n2
  | Eop (Oxorlimm n2) (t2:::Enil) => xorlimm_case2 n2 t2
  | e2 => xorlimm_default e2
  end.

Definition xorlimm (n1: int64) (e2: expr) :=
 if Int64.eq n1 Int64.zero then e2 else match xorlimm_match e2 with
  | xorlimm_case1 n2 => (* Eop (Olongconst n2) Enil *) 
      longconst (Int64.xor n1 n2)
  | xorlimm_case2 n2 t2 => (* Eop (Oxorlimm n2) (t2:::Enil) *) 
      let n := Int64.xor n1 n2 in if Int64.eq n Int64.zero then t2 else Eop (Oxorlimm n) (t2:::Enil)
  | xorlimm_default e2 =>
      Eop (Oxorlimm n1) (e2:::Enil)
  end.


(** Original definition:
<<
Nondetfunction xorl (e1: expr) (e2: expr) :=
  if Archi.splitlong then SplitLong.xorl e1 e2 else
  match e1, e2 with
  | Eop (Olongconst n1) Enil, t2 => xorlimm n1 t2
  | t1, Eop (Olongconst n2) Enil => xorlimm n2 t1
  | _, _ => Eop Oxorl (e1:::e2:::Enil)
  end.
>>
*)

Inductive xorl_cases: forall (e1: expr) (e2: expr), Type :=
  | xorl_case1: forall n1 t2, xorl_cases (Eop (Olongconst n1) Enil) (t2)
  | xorl_case2: forall t1 n2, xorl_cases (t1) (Eop (Olongconst n2) Enil)
  | xorl_default: forall (e1: expr) (e2: expr), xorl_cases e1 e2.

Definition xorl_match (e1: expr) (e2: expr) :=
  match e1 as zz1, e2 as zz2 return xorl_cases zz1 zz2 with
  | Eop (Olongconst n1) Enil, t2 => xorl_case1 n1 t2
  | t1, Eop (Olongconst n2) Enil => xorl_case2 t1 n2
  | e1, e2 => xorl_default e1 e2
  end.

Definition xorl (e1: expr) (e2: expr) :=
 if Archi.splitlong then SplitLong.xorl e1 e2 else match xorl_match e1 e2 with
  | xorl_case1 n1 t2 => (* Eop (Olongconst n1) Enil, t2 *) 
      xorlimm n1 t2
  | xorl_case2 t1 n2 => (* t1, Eop (Olongconst n2) Enil *) 
      xorlimm n2 t1
  | xorl_default e1 e2 =>
      Eop Oxorl (e1:::e2:::Enil)
  end.


(** ** Integer logical negation *)

Definition notl (e: expr) :=
  if Archi.splitlong then SplitLong.notl e else xorlimm Int64.mone e.

(** ** Integer division and modulus *)

Definition divlu_base (e1: expr) (e2: expr) :=
  if Archi.splitlong then SplitLong.divlu_base e1 e2 else Eop Odivlu (e1:::e2:::Enil).
Definition modlu_base (e1: expr) (e2: expr) :=
  if Archi.splitlong then SplitLong.modlu_base e1 e2 else Eop Omodlu (e1:::e2:::Enil).
Definition divls_base (e1: expr) (e2: expr) :=
  if Archi.splitlong then SplitLong.divls_base e1 e2 else Eop Odivl (e1:::e2:::Enil).
Definition modls_base (e1: expr) (e2: expr) :=
  if Archi.splitlong then SplitLong.modls_base e1 e2 else Eop Omodl (e1:::e2:::Enil).

Definition shrxlimm (e: expr) (n: int) :=
  if Archi.splitlong then SplitLong.shrxlimm e n else
  if Int.eq n Int.zero then e else Eop (Oshrxlimm n) (e ::: Enil).

(** ** Comparisons *)

Definition cmplu (c: comparison) (e1 e2: expr) :=
  if Archi.splitlong then SplitLong.cmplu c e1 e2 else
  match is_longconst e1, is_longconst e2 with
  | Some n1, Some n2 =>
      Eop (Ointconst (if Int64.cmpu c n1 n2 then Int.one else Int.zero)) Enil
  | Some n1, None => Eop (Ocmp (Ccompluimm (swap_comparison c) n1)) (e2:::Enil)
  | None, Some n2 => Eop (Ocmp (Ccompluimm c n2)) (e1:::Enil)
  | None, None => Eop (Ocmp (Ccomplu c)) (e1:::e2:::Enil)
  end.

Definition cmpl (c: comparison) (e1 e2: expr) :=
  if Archi.splitlong then SplitLong.cmpl c e1 e2 else
  match is_longconst e1, is_longconst e2 with
  | Some n1, Some n2 =>
      Eop (Ointconst (if Int64.cmp c n1 n2 then Int.one else Int.zero)) Enil
  | Some n1, None => Eop (Ocmp (Ccomplimm (swap_comparison c) n1)) (e2:::Enil)
  | None, Some n2 => Eop (Ocmp (Ccomplimm c n2)) (e1:::Enil)
  | None, None => Eop (Ocmp (Ccompl c)) (e1:::e2:::Enil)
  end.

(** ** Floating-point conversions *)

Definition longoffloat (e: expr) :=
  if Archi.splitlong then SplitLong.longoffloat e else 
  Eop Olongoffloat (e:::Enil).

Definition longuoffloat (e: expr) :=
  if Archi.splitlong then SplitLong.longuoffloat e else 
  Eop Olonguoffloat (e:::Enil).

Definition floatoflong (e: expr) := 
  if Archi.splitlong then SplitLong.floatoflong e else 
  Eop Ofloatoflong (e:::Enil).

Definition floatoflongu (e: expr) := 
  if Archi.splitlong then SplitLong.floatoflongu e else 
  Eop Ofloatoflongu (e:::Enil).

Definition longofsingle (e: expr) := 
  if Archi.splitlong then SplitLong.longofsingle e else 
  Eop Olongofsingle (e:::Enil).

Definition longuofsingle (e: expr) := 
  if Archi.splitlong then SplitLong.longuofsingle e else 
  Eop Olonguofsingle (e:::Enil).

Definition singleoflong (e: expr) := 
  if Archi.splitlong then SplitLong.singleoflong e else 
  Eop Osingleoflong (e:::Enil).

Definition singleoflongu (e: expr) := 
  if Archi.splitlong then SplitLong.singleoflongu e else 
  Eop Osingleoflongu (e:::Enil).

End SELECT.
