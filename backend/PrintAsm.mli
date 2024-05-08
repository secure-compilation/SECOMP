(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

val print_program: out_channel -> Asm.program -> unit

(* val print_program_asm: out_channel -> Asm.program -> unit *)

(* val print_if: Asm.program -> unit *)

(* val destination: string option ref *)

(* val print_instruction_asm: Format.formatter -> Asm.instruction -> unit *)
