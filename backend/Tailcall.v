(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Recognition of tail calls. *)

Require Import Coqlib Maps AST Registers Op RTL Conventions.

(** An [Icall] instruction that stores its result in register [rreg]
  can be turned into a tail call if:
- its successor is a [Ireturn None] or [Ireturn (Some rreg)] instruction;
- the stack block of the current function is empty: [stacksize = 0].

If the current function had a non-empty stack block, it could be that
the called function accesses it, for instance if a pointer into the
stack block is passed as an argument.  In this case, it would be
semantically incorrect to deallocate the stack block before the call,
as [Itailcall] does.  Therefore, the optimization can only be performed if
the stack block of the current function is empty, in which case it makes
no semantic difference to deallocate it before or after the call.

Another complication is that the [Ireturn] instruction does not, in general,
follow immediately the [Icall] instruction: the RTL code generator
can have inserted moves and no-ops between these instructions.
The general pattern we recognize is therefore:
<<
       r1 <- call(....)
       nop
       r2 <- r1
       r3 <- r2
       return r3
>>
The [is_return] function below recognizes this pattern.
*)

Fixpoint is_return (n: nat) (f: function) (pc: node) (rret: reg)
                   {struct n}: bool :=
  match n with
  | O => false
  | S n' =>
      match f.(fn_code)!pc with
      | Some(Ireturn None) => true
      | Some(Ireturn (Some r)) => Reg.eq r rret
      | Some(Inop s) => is_return n' f s rret
      | Some(Iop op args dst s) =>
          match is_move_operation op args with
          | None => false
          | Some src =>
              if Reg.eq rret src
              then is_return n' f s dst
              else false
          end
      | _ => false
      end
  end.

(** To ensure termination, we bound arbitrarily the number of iterations
of the [is_return] function: we look ahead for a nop/move/return of length
at most [niter] instructions. *)

Definition niter := 5%nat.

(** Tailcalls between compartments are not allowed.  The [ce: compenv]
  environments below record which functions belong to which compartments, so
  that we can prevent inter-compartment calls from turning into tailcalls.
  Currently, this forces us to prevent tailcalls to any function that is not a
  constant. *)

Definition compenv := PTree.t compartment.

Definition add_globdef (ce: compenv) (idg: ident * globdef fundef unit): compenv :=
  match idg with
  | (id, Gfun f) => PTree.set id (comp_of f) ce
  | (id, Gvar _) => PTree.remove id ce
  end.

Definition compenv_program (p: program): compenv :=
  List.fold_left add_globdef p.(prog_defs) (PTree.empty compartment).

Definition intra_compartment_call (ce: compenv) (ros: reg + ident) (cp: compartment): bool :=
  match ros with
  | inr id =>
    match ce!id with
    | Some cp' => eq_compartment cp cp'
    | None     => false
    end
  | _ => false
  end.

(** The code transformation is straightforward: call instructions
  followed by an appropriate nop/move/return sequence become
  tail calls; other instructions are unchanged.

  To ensure that the resulting RTL code is well typed, we
  restrict the transformation to the cases where a tail call is
  allowed by the calling conventions, and where the result signatures
  match. *)

Definition transf_instr (ce: compenv) (f: function) (pc: node) (instr: instruction) :=
  match instr with
  | Icall sig ros args res s =>
      if is_return niter f s res
      && tailcall_is_possible sig
      && opt_typ_eq sig.(sig_res) f.(fn_sig).(sig_res)
      && intra_compartment_call ce ros f.(fn_comp)
      then Itailcall sig ros args
      else instr
  | _ => instr
  end.

(** A function is transformed only if its stack block is empty,
    as explained above.  *)

Definition transf_function (ce: compenv) (f: function) : function :=
  if zeq f.(fn_stacksize) 0
  then RTL.transf_function (transf_instr ce f) f
  else f.

Definition transf_fundef (ce: compenv) (fd: fundef) : fundef :=
  AST.transf_fundef (transf_function ce) fd.

Definition transf_program (p: program) : program :=
  transform_program (transf_fundef (compenv_program p)) p.
