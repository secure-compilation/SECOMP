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

(** Abstract syntax and semantics for RISC-V assembly language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Split.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Stacklayout.
Require Import Conventions.

Require Import Exec Determinism.

Notation offset_arg := Stacklayout.offset_arg.

(** * Abstract syntax *)

(** Integer registers.  X0 is treated specially because it always reads 
  as zero and is never used as a destination of an instruction. *)

Inductive ireg: Type :=
  | X1:  ireg | X2:  ireg | X3:  ireg | X4:  ireg | X5:  ireg
  | X6:  ireg | X7:  ireg | X8:  ireg | X9:  ireg | X10: ireg
  | X11: ireg | X12: ireg | X13: ireg | X14: ireg | X15: ireg
  | X16: ireg | X17: ireg | X18: ireg | X19: ireg | X20: ireg
  | X21: ireg | X22: ireg | X23: ireg | X24: ireg | X25: ireg
  | X26: ireg | X27: ireg | X28: ireg | X29: ireg | X30: ireg
  | X31: ireg.

Inductive ireg0: Type :=
  | X0: ireg0 | X: ireg -> ireg0.

Coercion X: ireg >-> ireg0.

(** Floating-point registers *)

Inductive freg: Type :=
  | F0: freg  | F1: freg  | F2: freg  | F3: freg
  | F4: freg  | F5: freg  | F6: freg  | F7: freg
  | F8: freg  | F9: freg  | F10: freg | F11: freg
  | F12: freg | F13: freg | F14: freg | F15: freg
  | F16: freg | F17: freg | F18: freg | F19: freg
  | F20: freg | F21: freg | F22: freg | F23: freg
  | F24: freg | F25: freg | F26: freg | F27: freg
  | F28: freg | F29: freg | F30: freg | F31: freg.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma ireg0_eq: forall (x y: ireg0), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. Defined.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.
  
(** We model the following registers of the RISC-V architecture. *)

Inductive preg: Type :=
  | IR: ireg -> preg                    (**r integer registers *)
  | FR: freg -> preg                    (**r double-precision float registers *)
  | PC: preg.                           (**r program counter *)

Coercion IR: ireg >-> preg.
Coercion FR: freg >-> preg.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. apply freg_eq. Defined.

Module PregEq.
  Definition t  := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

(** Conventional names for stack pointer ([SP]) and return address ([RA]). *)

Declare Scope asm.
Notation "'SP'" := X2 (only parsing) : asm.
Notation "'RA'" := X1 (only parsing) : asm.

(** Offsets for load and store instructions.  An offset is either an
  immediate integer or the low part of a symbol. *)

Inductive offset : Type :=
  | Ofsimm (ofs: ptrofs)
  | Ofslow (id: ident) (ofs: ptrofs).

(** The RISC-V instruction set is composed of several subsets.  We model
  the "32I" (32-bit integers), "64I" (64-bit integers),
  "M" (multiplication and division), 
  "F" (single-precision floating-point)
  and "D" (double-precision floating-point) subsets.  

  For 32- and 64-bit integer arithmetic, the RISC-V instruction set comprises
  generic integer operations such as ADD that operate over the full width
  of an integer register (either 32 or 64 bit), plus specific instructions
  such as ADDW that normalize their results to signed 32-bit integers.
  Other instructions such as AND work equally well over 32- and 64-bit
  integers, with the convention that 32-bit integers are represented
  sign-extended in 64-bit registers.

  This clever design is challenging to formalize in the CompCert value
  model.  As a first step, we follow a more traditional approach,
  also used in the x86 port, whereas we have two sets of (pseudo-)
  instructions, one for 32-bit integer arithmetic, with suffix W,
  the other for 64-bit integer arithmetic, with suffix L.  The mapping
  to actual instructions is done when printing assembly code, as follows:
  - In 32-bit mode:
    ADDW becomes ADD, ADDL is an error, ANDW becomes AND, ANDL is an error.
  - In 64-bit mode:
    ADDW becomes ADDW, ADDL becomes ADD, ANDW and ANDL both become AND.
*)

Definition label := positive.

(** A note on immediates: there are various constraints on immediate
  operands to RISC-V instructions.  We do not attempt to capture these
  restrictions in the abstract syntax nor in the semantics.  The
  assembler will emit an error if immediate operands exceed the
  representable range.  Of course, our RISC-V generator (file
  [Asmgen]) is careful to respect this range. *)

Inductive instruction : Type :=
  | Pmv     (rd: ireg) (rs: ireg)                    (**r integer move *)

(** 32-bit integer register-immediate instructions *)
  | Paddiw  (rd: ireg) (rs: ireg0) (imm: int)        (**r add immediate *)
  | Psltiw  (rd: ireg) (rs: ireg0) (imm: int)        (**r set-less-than immediate *)
  | Psltiuw (rd: ireg) (rs: ireg0) (imm: int)        (**r set-less-than unsigned immediate *)
  | Pandiw  (rd: ireg) (rs: ireg0) (imm: int)        (**r and immediate *)
  | Poriw   (rd: ireg) (rs: ireg0) (imm: int)        (**r or immediate *)
  | Pxoriw  (rd: ireg) (rs: ireg0) (imm: int)        (**r xor immediate *)
  | Pslliw  (rd: ireg) (rs: ireg0) (imm: int)        (**r shift-left-logical immediate *)
  | Psrliw  (rd: ireg) (rs: ireg0) (imm: int)        (**r shift-right-logical immediate *)
  | Psraiw  (rd: ireg) (rs: ireg0) (imm: int)        (**r shift-right-arith immediate *)
  | Pluiw   (rd: ireg)             (imm: int)        (**r load upper-immediate *)
(** 32-bit integer register-register instructions *)
  | Paddw   (rd: ireg) (rs1 rs2: ireg0)              (**r integer addition *)
  | Psubw   (rd: ireg) (rs1 rs2: ireg0)              (**r integer subtraction *)

  | Pmulw   (rd: ireg) (rs1 rs2: ireg0)              (**r integer multiply low *)
  | Pmulhw  (rd: ireg) (rs1 rs2: ireg0)              (**r integer multiply high signed *)
  | Pmulhuw (rd: ireg) (rs1 rs2: ireg0)              (**r integer multiply high unsigned *)
  | Pdivw   (rd: ireg) (rs1 rs2: ireg0)              (**r integer division *)
  | Pdivuw  (rd: ireg) (rs1 rs2: ireg0)              (**r unsigned integer division *)
  | Premw   (rd: ireg) (rs1 rs2: ireg0)              (**r integer remainder *)
  | Premuw  (rd: ireg) (rs1 rs2: ireg0)              (**r unsigned integer remainder *)
  | Psltw   (rd: ireg) (rs1 rs2: ireg0)              (**r set-less-than *)
  | Psltuw  (rd: ireg) (rs1 rs2: ireg0)              (**r set-less-than unsigned *)
  | Pseqw   (rd: ireg) (rs1 rs2: ireg0)              (**r [rd <- rs1 == rs2] (pseudo) *)
  | Psnew   (rd: ireg) (rs1 rs2: ireg0)              (**r [rd <- rs1 != rs2] (pseudo) *)
  | Pandw   (rd: ireg) (rs1 rs2: ireg0)              (**r bitwise and *)
  | Porw    (rd: ireg) (rs1 rs2: ireg0)              (**r bitwise or *)
  | Pxorw   (rd: ireg) (rs1 rs2: ireg0)              (**r bitwise xor *)
  | Psllw   (rd: ireg) (rs1 rs2: ireg0)              (**r shift-left-logical *)
  | Psrlw   (rd: ireg) (rs1 rs2: ireg0)              (**r shift-right-logical *)
  | Psraw   (rd: ireg) (rs1 rs2: ireg0)              (**r shift-right-arith *)

(** 64-bit integer register-immediate instructions *)
  | Paddil  (rd: ireg) (rs: ireg0) (imm: int64)      (**r add immediate *)
  | Psltil  (rd: ireg) (rs: ireg0) (imm: int64)      (**r set-less-than immediate *)
  | Psltiul (rd: ireg) (rs: ireg0) (imm: int64)      (**r set-less-than unsigned immediate *)
  | Pandil  (rd: ireg) (rs: ireg0) (imm: int64)      (**r and immediate *)
  | Poril   (rd: ireg) (rs: ireg0) (imm: int64)      (**r or immediate *)
  | Pxoril  (rd: ireg) (rs: ireg0) (imm: int64)      (**r xor immediate *)
  | Psllil  (rd: ireg) (rs: ireg0) (imm: int)        (**r shift-left-logical immediate *)
  | Psrlil  (rd: ireg) (rs: ireg0) (imm: int)        (**r shift-right-logical immediate *)
  | Psrail  (rd: ireg) (rs: ireg0) (imm: int)        (**r shift-right-arith immediate *)
  | Pluil   (rd: ireg)             (imm: int64)      (**r load upper-immediate *)
(** 64-bit integer register-register instructions *)
  | Paddl   (rd: ireg) (rs1 rs2: ireg0)              (**r integer addition *)
  | Psubl   (rd: ireg) (rs1 rs2: ireg0)              (**r integer subtraction *)

  | Pmull   (rd: ireg) (rs1 rs2: ireg0)              (**r integer multiply low *)
  | Pmulhl  (rd: ireg) (rs1 rs2: ireg0)              (**r integer multiply high signed *)
  | Pmulhul (rd: ireg) (rs1 rs2: ireg0)              (**r integer multiply high unsigned *)
  | Pdivl   (rd: ireg) (rs1 rs2: ireg0)              (**r integer division *)
  | Pdivul  (rd: ireg) (rs1 rs2: ireg0)              (**r unsigned integer division *)
  | Preml   (rd: ireg) (rs1 rs2: ireg0)              (**r integer remainder *)
  | Premul  (rd: ireg) (rs1 rs2: ireg0)              (**r unsigned integer remainder *)
  | Psltl   (rd: ireg) (rs1 rs2: ireg0)              (**r set-less-than *)
  | Psltul  (rd: ireg) (rs1 rs2: ireg0)              (**r set-less-than unsigned *)
  | Pseql   (rd: ireg) (rs1 rs2: ireg0)              (**r [rd <- rs1 == rs2] (pseudo) *)
  | Psnel   (rd: ireg) (rs1 rs2: ireg0)              (**r [rd <- rs1 != rs2] (pseudo) *)
  | Pandl   (rd: ireg) (rs1 rs2: ireg0)              (**r bitwise and *)
  | Porl    (rd: ireg) (rs1 rs2: ireg0)              (**r bitwise or *)
  | Pxorl   (rd: ireg) (rs1 rs2: ireg0)              (**r bitwise xor *)
  | Pslll   (rd: ireg) (rs1 rs2: ireg0)              (**r shift-left-logical *)
  | Psrll   (rd: ireg) (rs1 rs2: ireg0)              (**r shift-right-logical *)
  | Psral   (rd: ireg) (rs1 rs2: ireg0)              (**r shift-right-arith *)

  | Pcvtl2w (rd: ireg) (rs: ireg0)                   (**r int64->int32 (pseudo) *)
  | Pcvtw2l (r: ireg)                                (**r int32 signed -> int64 (pseudo) *)

  (* Unconditional jumps.  Links are always to X1/RA. *)
  | Pj_l    (l: label)                              (**r jump to label *)
  | Pj_s    (symb: ident) (sg: signature)           (**r jump to symbol *)
  | Pj_r    (r: ireg)     (sg: signature) (iscl: bool) (**r jump register *)
  | Pjal_s  (symb: ident) (sg: signature) (iscl: bool) (**r jump-and-link symbol *)
  | Pjal_r  (r: ireg)     (sg: signature) (iscl: bool) (**r jump-and-link register *)

  (* Conditional branches, 32-bit comparisons *)
  | Pbeqw   (rs1 rs2: ireg0) (l: label)             (**r branch-if-equal *)
  | Pbnew   (rs1 rs2: ireg0) (l: label)             (**r branch-if-not-equal signed *)
  | Pbltw   (rs1 rs2: ireg0) (l: label)             (**r branch-if-less signed *)
  | Pbltuw  (rs1 rs2: ireg0) (l: label)             (**r branch-if-less unsigned *)
  | Pbgew   (rs1 rs2: ireg0) (l: label)             (**r branch-if-greater-or-equal signed *)
  | Pbgeuw  (rs1 rs2: ireg0) (l: label)             (**r branch-if-greater-or-equal unsigned *)

  (* Conditional branches, 64-bit comparisons *)
  | Pbeql   (rs1 rs2: ireg0) (l: label)             (**r branch-if-equal *)
  | Pbnel   (rs1 rs2: ireg0) (l: label)             (**r branch-if-not-equal signed *)
  | Pbltl   (rs1 rs2: ireg0) (l: label)             (**r branch-if-less signed *)
  | Pbltul  (rs1 rs2: ireg0) (l: label)             (**r branch-if-less unsigned *)
  | Pbgel   (rs1 rs2: ireg0) (l: label)             (**r branch-if-greater-or-equal signed *)
  | Pbgeul  (rs1 rs2: ireg0) (l: label)             (**r branch-if-greater-or-equal unsigned *)

  (* Loads and stores *)
  | Plb     (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)     (**r load signed int8 *)
  | Plbu    (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load unsigned int8 *)
  | Plh     (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load signed int16 *)
  | Plhu    (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load unsigned int16 *)
  | Plw     (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)   (**r load int32 *)
  | Plw_a   (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load any32 *)
  | Pld     (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load int64 *)
  | Pld_a   (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load any64 *)


  | Psb     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int8 *)
  | Psh     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int16 *)
  | Psw     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int32 *)
  | Psw_a   (rs: ireg) (ra: ireg) (ofs: offset)     (**r store any32 *)
  | Psd     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int64 *)
  | Psd_a   (rs: ireg) (ra: ireg) (ofs: offset)     (**r store any64 *)

            (* Probably doesn't need privilged stores because can't write directly to parameters. Instead
             writing to a parameter writes to a /copy/ of the parameter *)

  (* Synchronization *)
  | Pfence                                          (**r fence *)

  (* floating point register move *)
  | Pfmv     (rd: freg) (rs: freg)                  (**r move *)
  | Pfmvxs   (rd: ireg) (rs: freg)                  (**r move FP single to integer register *)
  | Pfmvsx   (rd: freg) (rs: ireg)                  (**r move integer register to FP single *)
  | Pfmvxd   (rd: ireg) (rs: freg)                  (**r move FP double to integer register *)
  | Pfmvdx   (rd: freg) (rs: ireg)                  (**r move integer register to FP double *)

  (* 32-bit (single-precision) floating point *)
  | Pfls     (rd: freg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load float *)
  | Pfss     (rs: freg) (ra: ireg) (ofs: offset)    (**r store float *)

  | Pfnegs   (rd: freg) (rs: freg)                  (**r negation *)
  | Pfabss   (rd: freg) (rs: freg)                  (**r absolute value *)

  | Pfadds   (rd: freg) (rs1 rs2: freg)             (**r addition *)
  | Pfsubs   (rd: freg) (rs1 rs2: freg)             (**r subtraction *)
  | Pfmuls   (rd: freg) (rs1 rs2: freg)             (**r multiplication *)
  | Pfdivs   (rd: freg) (rs1 rs2: freg)             (**r division *)
  | Pfmins   (rd: freg) (rs1 rs2: freg)             (**r minimum *)
  | Pfmaxs   (rd: freg) (rs1 rs2: freg)             (**r maximum *)

  | Pfeqs    (rd: ireg) (rs1 rs2: freg)             (**r compare equal *)
  | Pflts    (rd: ireg) (rs1 rs2: freg)             (**r compare less-than *)
  | Pfles    (rd: ireg) (rs1 rs2: freg)             (**r compare less-than/equal *)

  | Pfsqrts  (rd: freg) (rs: freg)                  (**r square-root *)

  | Pfmadds  (rd: freg) (rs1 rs2 rs3: freg)         (**r fused multiply-add *)
  | Pfmsubs  (rd: freg) (rs1 rs2 rs3: freg)         (**r fused multiply-sub *)
  | Pfnmadds (rd: freg) (rs1 rs2 rs3: freg)         (**r fused negated multiply-add *)
  | Pfnmsubs (rd: freg) (rs1 rs2 rs3: freg)         (**r fused negated multiply-sub *)

  | Pfcvtws  (rd: ireg) (rs: freg)                  (**r float32 -> int32 conversion *)
  | Pfcvtwus (rd: ireg) (rs: freg)                  (**r float32 -> unsigned int32 conversion *)
  | Pfcvtsw  (rd: freg) (rs: ireg0)                 (**r int32 -> float32 conversion *)
  | Pfcvtswu (rd: freg) (rs: ireg0)                 (**r unsigned int32 -> float32 conversion *)

  | Pfcvtls  (rd: ireg) (rs: freg)                  (**r float32 -> int64 conversion *)
  | Pfcvtlus (rd: ireg) (rs: freg)                  (**r float32 -> unsigned int64 conversion *)
  | Pfcvtsl  (rd: freg) (rs: ireg0)                 (**r int64 -> float32 conversion *)
  | Pfcvtslu (rd: freg) (rs: ireg0)                 (**r unsigned int 64-> float32 conversion *)

  (* 64-bit (double-precision) floating point *)
  | Pfld     (rd: freg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load 64-bit float *)
  | Pfld_a   (rd: freg) (ra: ireg) (ofs: offset) (priv: bool)   (**r load any64 *)
  | Pfsd     (rd: freg) (ra: ireg) (ofs: offset)    (**r store 64-bit float *)
  | Pfsd_a   (rd: freg) (ra: ireg) (ofs: offset)    (**r store any64 *)

  | Pfnegd   (rd: freg) (rs: freg)                  (**r negation *)
  | Pfabsd   (rd: freg) (rs: freg)                  (**r absolute value *)

  | Pfaddd   (rd: freg) (rs1 rs2: freg)             (**r addition *)
  | Pfsubd   (rd: freg) (rs1 rs2: freg)             (**r subtraction *)
  | Pfmuld   (rd: freg) (rs1 rs2: freg)             (**r multiplication *)
  | Pfdivd   (rd: freg) (rs1 rs2: freg)             (**r division *)
  | Pfmind   (rd: freg) (rs1 rs2: freg)             (**r minimum *)
  | Pfmaxd   (rd: freg) (rs1 rs2: freg)             (**r maximum *)

  | Pfeqd    (rd: ireg) (rs1 rs2: freg)             (**r compare equal *)
  | Pfltd    (rd: ireg) (rs1 rs2: freg)             (**r compare less-than *)
  | Pfled    (rd: ireg) (rs1 rs2: freg)             (**r compare less-than/equal *)

  | Pfsqrtd  (rd: freg) (rs: freg)                  (**r square-root *)

  | Pfmaddd  (rd: freg) (rs1 rs2 rs3: freg)         (**r fused multiply-add *)
  | Pfmsubd  (rd: freg) (rs1 rs2 rs3: freg)         (**r fused multiply-sub *)
  | Pfnmaddd (rd: freg) (rs1 rs2 rs3: freg)         (**r fused negated multiply-add *)
  | Pfnmsubd (rd: freg) (rs1 rs2 rs3: freg)         (**r fused negated multiply-sub *)

  | Pfcvtwd  (rd: ireg) (rs: freg)                  (**r float -> int32 conversion *)
  | Pfcvtwud (rd: ireg) (rs: freg)                  (**r float -> unsigned int32 conversion *)
  | Pfcvtdw  (rd: freg) (rs: ireg0)                 (**r int32 -> float conversion *)
  | Pfcvtdwu (rd: freg) (rs: ireg0)                 (**r unsigned int32 -> float conversion *)

  | Pfcvtld  (rd: ireg) (rs: freg)                  (**r float -> int64 conversion *)
  | Pfcvtlud (rd: ireg) (rs: freg)                  (**r float -> unsigned int64 conversion *)
  | Pfcvtdl  (rd: freg) (rs: ireg0)                 (**r int64 -> float conversion *)
  | Pfcvtdlu (rd: freg) (rs: ireg0)                 (**r unsigned int64 -> float conversion *)

  | Pfcvtds  (rd: freg) (rs: freg)                  (**r float32 -> float   *)
  | Pfcvtsd  (rd: freg) (rs: freg)                  (**r float   -> float32 *)

  (* Pseudo-instructions *)
  | Pld_arg   (ch: memory_chunk) (rd: ireg + freg) (ra: ireg) (ofs: offset)   (**r load arg *)
  | Pallocframe (sz: Z) (pos: ptrofs)               (**r allocate new stack frame *)
  | Pfreeframe  (sz: Z) (pos: ptrofs)               (**r deallocate stack frame and restore previous frame *)
  | Plabel  (lbl: label)                            (**r define a code label *)
  | Ploadsymbol (rd: ireg) (id: ident) (ofs: ptrofs) (**r load the address of a symbol *)
  | Ploadsymbol_high (rd: ireg) (id: ident) (ofs: ptrofs) (**r load the high part of the address of a symbol *)
  | Ploadli (rd: ireg) (i: int64)                   (**r load an immediate int64 *)
  | Ploadfi (rd: freg) (f: float)                   (**r load an immediate float *)
  | Ploadsi (rd: freg) (f: float32)                 (**r load an immediate single *)
  | Pbtbl   (r: ireg)  (tbl: list label)            (**r N-way branch through a jump table *)
  | Pbuiltin: external_function -> list (builtin_arg preg)
              -> builtin_res preg -> instruction    (**r built-in function (pseudo) *)
  | Pnop : instruction.                             (**r nop instruction *)


(** The pseudo-instructions are the following:

- [Plabel]: define a code label at the current program point.

- [Ploadsymbol]: load the address of a symbol in an integer register.
  Expands to the [la] assembler pseudo-instruction, which does the right
  thing even if we are in PIC mode.

- [Ploadli rd ival]: load an immediate 64-bit integer into an integer
  register rd.  Expands to a load from an address in the constant data section,
  using the integer register x31 as temporary:
<<
        lui x31, %hi(lbl)
        ld rd, %lo(lbl)(x31)
lbl:
        .quad ival
>>

- [Ploadfi rd fval]: similar to [Ploadli] but loads a double FP constant fval
  into a float register rd.

- [Ploadsi rd fval]: similar to [Ploadli] but loads a single FP constant fval
  into a float register rd.

- [Pallocframe sz pos]: in the formal semantics, this
  pseudo-instruction allocates a memory block with bounds [0] and
  [sz], stores the value of the stack pointer at offset [pos] in this
  block, and sets the stack pointer to the address of the bottom of
  this block.
  In the printed ASM assembly code, this allocation is:
<<
        mv      x30, sp
        sub     sp,  sp, #sz
        sw      x30, #pos(sp)
>>
  This cannot be expressed in our memory model, which does not reflect
  the fact that stack frames are adjacent and allocated/freed
  following a stack discipline.

- [Pfreeframe sz pos]: in the formal semantics, this pseudo-instruction
  reads the word at [pos] of the block pointed by the stack pointer,
  frees this block, and sets the stack pointer to the value read.
  In the printed ASM assembly code, this freeing is just an increment of [sp]:
<<
        add     sp,  sp, #sz
>>
  Again, our memory model cannot comprehend that this operation
  frees (logically) the current stack frame.

- [Pbtbl reg table]: this is a N-way branch, implemented via a jump table
  as follows:
<<
        la      x31, table
        add     x31, x31, reg
        jr      x31
table:  .long   table[0], table[1], ...
>>
  Note that [reg] contains 4 times the index of the desired table entry.

- [Pseq rd rs1 rs2]: since unsigned comparisons have particular
  semantics for pointers, we cannot encode equality directly using
  xor/sub etc, which have only integer semantics.
<<
        xor     rd, rs1, rs2
        sltiu   rd, rd, 1
>>
  The [xor] is omitted if one of [rs1] and [rs2] is [x0].

- [Psne rd rs1 rs2]: similarly for unsigned inequality.
<<
        xor     rd, rs1, rs2
        sltu    rd, x0, rd
>>
*)

Definition code := list instruction.
Record function : Type := mkfunction { fn_comp: compartment; fn_sig: signature; fn_code: code }.
#[global]
Instance has_comp_function: has_comp function := fn_comp.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain
  the convention that integer registers are mapped to values of
  type [Tint] or [Tlong] (in 64 bit mode),
  and float registers to values of type [Tsingle] or [Tfloat]. *)

Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef unit.

Definition get0w (rs: regset) (r: ireg0) : val :=
  match r with
  | X0 => Vint Int.zero
  | X r => rs r
  end.

Definition get0l (rs: regset) (r: ireg0) : val :=
  match r with
  | X0 => Vlong Int64.zero
  | X r => rs r
  end.

Notation "a # b" := (a b) (at level 1, only parsing) : asm.
Notation "a ## b" := (get0w a b) (at level 1) : asm.
Notation "a ### b" := (get0l a b) (at level 1) : asm.
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level) : asm.

Open Scope asm.

(** Undefining some registers *)

Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.

(** Assigning a register pair *)

Definition set_pair (p: rpair preg) (v: val) (rs: regset) : regset :=
  match p with
  | One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

(** Assigning multiple registers *)

Fixpoint set_regs (rl: list preg) (vl: list val) (rs: regset) : regset :=
  match rl, vl with
  | r1 :: rl', v1 :: vl' => set_regs rl' vl' (rs#r1 <- v1)
  | _, _ => rs
  end.

(** Assigning the result of a builtin *)

Fixpoint set_res (res: builtin_res preg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => rs#r <- v
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.

Section RELSEM.

(** Looking up instructions in a code sequence by position. *)

Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl lbl0); intro; congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.

Variable ge: genv.
Variable cp_main: compartment.

(** The two functions below axiomatize how the linker processes
  symbolic references [symbol + offset)] and splits their
  actual values into a 20-bit high part [%hi(symbol + offset)] and 
  a 12-bit low part [%lo(symbol + offset)]. *)

(* Parameter low_half: genv -> ident -> ptrofs -> ptrofs. *)
(* Parameter high_half: genv -> ident -> ptrofs -> val. *)
Program Definition low_half: genv -> ident -> ptrofs -> ptrofs :=
  (fun _ _ _ => Ptrofs.zero).
Definition high_half: genv -> ident -> ptrofs -> val :=
  (fun ge id ofs => match Genv.find_symbol ge id with
                    | Some b => Vptr b ofs
                    | None => Vundef
                    end).

(** The fundamental property of these operations is that, when applied
  to the address of a symbol, their results can be recombined by
  addition, rebuilding the original address. *)

(* Axiom low_high_half: *)
(*   forall id ofs, *)
(*   Val.offset_ptr (high_half ge id ofs) (low_half ge id ofs) = Genv.symbol_address ge id ofs. *)
Lemma low_high_half:
  forall id ofs,
  Val.offset_ptr (high_half ge id ofs) (low_half ge id ofs) = Genv.symbol_address ge id ofs.
Proof.
  intros id ofs.
  unfold Val.offset_ptr, high_half, low_half, Genv.symbol_address.
  unfold Genv.symbol_address.
  destruct (Genv.find_symbol ge id); [| reflexivity].
  rewrite Ptrofs.add_zero. reflexivity.
Qed.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome: Type :=
  | Next:  regset -> mem -> outcome
  | Stuck: outcome.

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]). *)

Definition nextinstr (rs: regset) :=
  rs#PC <- (Val.offset_ptr rs#PC Ptrofs.one).

Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_code f) with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Ptrofs.repr pos))) m
      | _          => Stuck
      end
  end.

(** Auxiliaries for memory accesses *)

Definition eval_offset (ofs: offset) : ptrofs :=
  match ofs with
  | Ofsimm n => n
  | Ofslow id delta => low_half ge id delta
  end.

Definition exec_load (chunk: memory_chunk) (rs: regset) (m: mem)
                     (d: preg) (a: ireg) (ofs: offset) (cp: compartment) (priv: bool) :=
  match Mem.loadv chunk m (Val.offset_ptr (rs a) (eval_offset ofs))
                  (if priv then top else cp) with
    | None => Stuck
    | Some v => Next (nextinstr (rs#d <- v)) m
    end.


Definition exec_store (chunk: memory_chunk) (rs: regset) (m: mem)
                      (s: preg) (a: ireg) (ofs: offset) (cp: compartment) :=
  match Mem.storev chunk m (Val.offset_ptr (rs a) (eval_offset ofs)) (rs s) cp with
  | None => Stuck
  | Some m' => Next (nextinstr rs) m'
  end.

(** Evaluating a branch *)

Definition eval_branch (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) : outcome :=
  match res with
    | Some true  => goto_label f l rs m
    | Some false => Next (nextinstr rs) m
    | None => Stuck
  end.

(** Execution of a single instruction [i] in initial state [rs] and
    [m].  Return updated state.  For instructions that correspond to
    actual RISC-V instructions, the cases are straightforward
    transliterations of the informal descriptions given in the RISC-V
    user-mode specification.  For pseudo-instructions, refer to the
    informal descriptions given above.

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the RISC-V code
    we generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction. *)

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) (cp: compartment)
                      : outcome :=
  match i with
  | Pmv d s =>
      Next (nextinstr (rs#d <- (rs#s))) m

(** 32-bit integer register-immediate instructions *)
  | Paddiw d s i =>
      Next (nextinstr (rs#d <- (Val.add rs##s (Vint i)))) m
  | Psltiw d s i =>
      Next (nextinstr (rs#d <- (Val.cmp Clt rs##s (Vint i)))) m
  | Psltiuw d s i =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs##s (Vint i)))) m
  | Pandiw d s i =>
      Next (nextinstr (rs#d <- (Val.and rs##s (Vint i)))) m
  | Poriw d s i =>
      Next (nextinstr (rs#d <- (Val.or rs##s (Vint i)))) m
  | Pxoriw d s i =>
      Next (nextinstr (rs#d <- (Val.xor rs##s (Vint i)))) m
  | Pslliw d s i =>
      Next (nextinstr (rs#d <- (Val.shl rs##s (Vint i)))) m
  | Psrliw d s i =>
      Next (nextinstr (rs#d <- (Val.shru rs##s (Vint i)))) m
  | Psraiw d s i =>
      Next (nextinstr (rs#d <- (Val.shr rs##s (Vint i)))) m
  | Pluiw d i =>
      Next (nextinstr (rs#d <- (Vint (Int.shl i (Int.repr 12))))) m

(** 32-bit integer register-register instructions *)
  | Paddw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.add rs##s1 rs##s2))) m
  | Psubw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.sub rs##s1 rs##s2))) m
  | Pmulw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mul rs##s1 rs##s2))) m
  | Pmulhw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulhs rs##s1 rs##s2))) m
  | Pmulhuw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulhu rs##s1 rs##s2))) m
  | Pdivw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divs rs##s1 rs##s2)))) m
  | Pdivuw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divu rs##s1 rs##s2)))) m
  | Premw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.mods rs##s1 rs##s2)))) m
  | Premuw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.modu rs##s1 rs##s2)))) m
  | Psltw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmp Clt rs##s1 rs##s2))) m
  | Psltuw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs##s1 rs##s2))) m
  | Pseqw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Ceq rs##s1 rs##s2))) m
  | Psnew d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Cne rs##s1 rs##s2))) m
  | Pandw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.and rs##s1 rs##s2))) m
  | Porw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.or rs##s1 rs##s2))) m
  | Pxorw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.xor rs##s1 rs##s2))) m
  | Psllw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shl rs##s1 rs##s2))) m
  | Psrlw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shru rs##s1 rs##s2))) m
  | Psraw d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shr rs##s1 rs##s2))) m

(** 64-bit integer register-immediate instructions *)
  | Paddil d s i =>
      Next (nextinstr (rs#d <- (Val.addl rs###s (Vlong i)))) m
  | Psltil d s i =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmpl Clt rs###s (Vlong i))))) m
  | Psltiul d s i =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt rs###s (Vlong i))))) m
  | Pandil d s i =>
      Next (nextinstr (rs#d <- (Val.andl rs###s (Vlong i)))) m
  | Poril d s i =>
      Next (nextinstr (rs#d <- (Val.orl rs###s (Vlong i)))) m
  | Pxoril d s i =>
      Next (nextinstr (rs#d <- (Val.xorl rs###s (Vlong i)))) m
  | Psllil d s i =>
      Next (nextinstr (rs#d <- (Val.shll rs###s (Vint i)))) m
  | Psrlil d s i =>
      Next (nextinstr (rs#d <- (Val.shrlu rs###s (Vint i)))) m
  | Psrail d s i =>
      Next (nextinstr (rs#d <- (Val.shrl rs###s (Vint i)))) m
  | Pluil d i =>
      Next (nextinstr (rs#d <- (Vlong (Int64.sign_ext 32 (Int64.shl i (Int64.repr 12)))))) m

(** 64-bit integer register-register instructions *)
  | Paddl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.addl rs###s1 rs###s2))) m
  | Psubl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.subl rs###s1 rs###s2))) m
  | Pmull d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mull rs###s1 rs###s2))) m
  | Pmulhl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mullhs rs###s1 rs###s2))) m
  | Pmulhul d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mullhu rs###s1 rs###s2))) m
  | Pdivl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divls rs###s1 rs###s2)))) m
  | Pdivul d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.divlu rs###s1 rs###s2)))) m
  | Preml d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.modls rs###s1 rs###s2)))) m
  | Premul d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.modlu rs###s1 rs###s2)))) m
  | Psltl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmpl Clt rs###s1 rs###s2)))) m
  | Psltul d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt rs###s1 rs###s2)))) m
  | Pseql d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Ceq rs###s1 rs###s2)))) m
  | Psnel d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Cne rs###s1 rs###s2)))) m
  | Pandl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.andl rs###s1 rs###s2))) m
  | Porl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.orl rs###s1 rs###s2))) m
  | Pxorl d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.xorl rs###s1 rs###s2))) m
  | Pslll d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shll rs###s1 rs###s2))) m
  | Psrll d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shrlu rs###s1 rs###s2))) m
  | Psral d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.shrl rs###s1 rs###s2))) m

  | Pcvtl2w d s =>
      Next (nextinstr (rs#d <- (Val.loword rs##s))) m
  | Pcvtw2l r =>
      Next (nextinstr (rs#r <- (Val.longofint rs#r))) m

(** Unconditional jumps.  Links are always to X1/RA. *)
  | Pj_l l =>
      goto_label f l rs m
  | Pj_s s sg =>
      if Genv.allowed_addrof_b ge cp s then
        Next (rs#PC <- (Genv.symbol_address ge s Ptrofs.zero) #X31 <- Vundef) m
      else
        Stuck
  | Pj_r r sg _ =>
      Next (rs#PC <- (rs#r)) m
  | Pjal_s s sg _ =>
      if Genv.allowed_addrof_b ge cp s then
    Next (rs#PC <- (Genv.symbol_address ge s Ptrofs.zero)
            #RA <- (Val.offset_ptr rs#PC Ptrofs.one)
         ) m
      else
        Stuck
  | Pjal_r r sg _ =>
      Next (rs#PC <- (rs#r)
              #RA <- (Val.offset_ptr rs#PC Ptrofs.one)
           ) m
(** Conditional branches, 32-bit comparisons *)
  | Pbeqw s1 s2 l =>
      eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Ceq rs##s1 rs##s2)
  | Pbnew s1 s2 l =>
      eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Cne rs##s1 rs##s2)
  | Pbltw s1 s2 l =>
      eval_branch f l rs m (Val.cmp_bool Clt rs##s1 rs##s2)
  | Pbltuw s1 s2 l =>
      eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Clt rs##s1 rs##s2)
  | Pbgew s1 s2 l =>
      eval_branch f l rs m (Val.cmp_bool Cge rs##s1 rs##s2)
  | Pbgeuw s1 s2 l =>
      eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Cge rs##s1 rs##s2)

(** Conditional branches, 64-bit comparisons *)
  | Pbeql s1 s2 l =>
      eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Ceq rs###s1 rs###s2)
  | Pbnel s1 s2 l =>
      eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Cne rs###s1 rs###s2)
  | Pbltl s1 s2 l =>
      eval_branch f l rs m (Val.cmpl_bool Clt rs###s1 rs###s2)
  | Pbltul s1 s2 l =>
      eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Clt rs###s1 rs###s2)
  | Pbgel s1 s2 l =>
      eval_branch f l rs m (Val.cmpl_bool Cge rs###s1 rs###s2)
  | Pbgeul s1 s2 l =>
      eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Cge rs###s1 rs###s2)

(** Loads and stores *)
  | Plb d a ofs priv =>
      exec_load Mint8signed rs m d a ofs cp priv
  | Plbu d a ofs priv =>
      exec_load Mint8unsigned rs m d a ofs cp priv
  | Plh d a ofs priv =>
      exec_load Mint16signed rs m d a ofs cp priv
  | Plhu d a ofs priv =>
      exec_load Mint16unsigned rs m d a ofs cp priv
  | Plw d a ofs priv =>
      exec_load Mint32 rs m d a ofs cp priv
  | Plw_a d a ofs priv =>
      exec_load Many32 rs m d a ofs cp priv
  | Pld d a ofs priv =>
      exec_load Mint64 rs m d a ofs cp priv
  | Pld_a d a ofs priv =>
      exec_load Many64 rs m d a ofs cp priv
  | Psb s a ofs =>
      exec_store Mint8unsigned rs m s a ofs cp
  | Psh s a ofs =>
      exec_store Mint16unsigned rs m s a ofs cp
  | Psw s a ofs =>
      exec_store Mint32 rs m s a ofs cp
  | Psw_a s a ofs =>
      exec_store Many32 rs m s a ofs cp
  | Psd s a ofs =>
      exec_store Mint64 rs m s a ofs cp
  | Psd_a s a ofs =>
      exec_store Many64 rs m s a ofs cp

(** Floating point register move *)
  | Pfmv d s =>
      Next (nextinstr (rs#d <- (rs#s))) m

(** 32-bit (single-precision) floating point *)
  | Pfls d a ofs b =>
      exec_load Mfloat32 rs m d a ofs cp b
  | Pfss s a ofs =>
      exec_store Mfloat32 rs m s a ofs cp

  | Pfnegs d s =>
      Next (nextinstr (rs#d <- (Val.negfs rs#s))) m
  | Pfabss d s =>
      Next (nextinstr (rs#d <- (Val.absfs rs#s))) m

  | Pfadds d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.addfs rs#s1 rs#s2))) m
  | Pfsubs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.subfs rs#s1 rs#s2))) m
  | Pfmuls d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulfs rs#s1 rs#s2))) m
  | Pfdivs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.divfs rs#s1 rs#s2))) m
  | Pfeqs d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Ceq rs#s1 rs#s2))) m
  | Pflts d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Clt rs#s1 rs#s2))) m
  | Pfles d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpfs Cle rs#s1 rs#s2))) m

  | Pfcvtws d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intofsingle rs#s)))) m
  | Pfcvtwus d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intuofsingle rs#s)))) m
  | Pfcvtsw d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleofint rs##s)))) m
  | Pfcvtswu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleofintu rs##s)))) m

  | Pfcvtls d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.longofsingle rs#s)))) m
  | Pfcvtlus d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.longuofsingle rs#s)))) m
  | Pfcvtsl d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleoflong rs###s)))) m
  | Pfcvtslu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.singleoflongu rs###s)))) m

(** 64-bit (double-precision) floating point *)
  | Pfld d a ofs b =>
      exec_load Mfloat64 rs m d a ofs cp b
  | Pfld_a d a ofs b =>
      exec_load Many64 rs m d a ofs cp b
  | Pfsd s a ofs =>
      exec_store Mfloat64 rs m s a ofs cp
  | Pfsd_a s a ofs =>
      exec_store Many64 rs m s a ofs cp

  | Pfnegd d s =>
      Next (nextinstr (rs#d <- (Val.negf rs#s))) m
  | Pfabsd d s =>
      Next (nextinstr (rs#d <- (Val.absf rs#s))) m

  | Pfaddd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.addf rs#s1 rs#s2))) m
  | Pfsubd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.subf rs#s1 rs#s2))) m
  | Pfmuld d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.mulf rs#s1 rs#s2))) m
  | Pfdivd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.divf rs#s1 rs#s2))) m
  | Pfeqd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Ceq rs#s1 rs#s2))) m
  | Pfltd d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Clt rs#s1 rs#s2))) m
  | Pfled d s1 s2 =>
      Next (nextinstr (rs#d <- (Val.cmpf Cle rs#s1 rs#s2))) m

  | Pfcvtwd d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intoffloat rs#s)))) m
  | Pfcvtwud d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.intuoffloat rs#s)))) m
  | Pfcvtdw d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatofint rs##s)))) m
  | Pfcvtdwu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatofintu rs##s)))) m

  | Pfcvtld d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.longoffloat rs#s)))) m
  | Pfcvtlud d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.longuoffloat rs#s)))) m
  | Pfcvtdl d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatoflong rs###s)))) m
  | Pfcvtdlu d s =>
      Next (nextinstr (rs#d <- (Val.maketotal (Val.floatoflongu rs###s)))) m

  | Pfcvtds d s =>
      Next (nextinstr (rs#d <- (Val.floatofsingle rs#s))) m
  | Pfcvtsd d s =>
      Next (nextinstr (rs#d <- (Val.singleoffloat rs#s))) m

(** Pseudo-instructions *)
  | Pld_arg _ _ _ _ => Stuck
  | Pallocframe sz pos =>
      let (m1, stk) := Mem.alloc m (comp_of f) 0 sz in
      let sp := (Vptr stk Ptrofs.zero) in
      match Mem.storev Mptr m1 (Val.offset_ptr sp pos) rs#SP cp with
      | None => Stuck
      | Some m2 => Next (nextinstr (rs #X30 <- (rs SP) #SP <- sp #X31 <- Vundef)) m2
      end
  | Pfreeframe sz pos =>
      match Mem.loadv Mptr m (Val.offset_ptr rs#SP pos) cp with
      | None => Stuck
      | Some v =>
          match rs SP with
          | Vptr stk ofs =>
              match Mem.free m stk 0 sz cp with
              | None => Stuck
              | Some m' => Next (nextinstr (rs#SP <- v #X31 <- Vundef)) m'
              end
          | _ => Stuck
          end
      end
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Ploadsymbol rd s ofs =>
      if Genv.allowed_addrof_b ge cp s then
        Next (nextinstr (rs#rd <- (Genv.symbol_address ge s ofs))) m
      else
        Stuck
  | Ploadsymbol_high rd s ofs =>
      if Genv.allowed_addrof_b ge cp s then
        Next (nextinstr (rs#rd <- (high_half ge s ofs))) m
      else
        Stuck
  | Ploadli rd i =>
      Next (nextinstr (rs#X31 <- Vundef #rd <- (Vlong i))) m
  | Ploadfi rd f =>
      Next (nextinstr (rs#X31 <- Vundef #rd <- (Vfloat f))) m
  | Ploadsi rd f =>
      Next (nextinstr (rs#X31 <- Vundef #rd <- (Vsingle f))) m
  | Pbtbl r tbl =>
      match rs r with
      | Vint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs#X5 <- Vundef #X31 <- Vundef) m
          end
      | _ => Stuck
      end
  | Pbuiltin ef args res =>
      Stuck (**r treated specially below *)

  (** The following instructions and directives are not generated directly by Asmgen,
      so we do not model them. *)
  | Pfence

  | Pfmvxs _ _
  | Pfmvsx _ _
  | Pfmvxd _ _
  | Pfmvdx _ _

  | Pfmins _ _ _
  | Pfmaxs _ _ _
  | Pfsqrts _ _
  | Pfmadds _ _ _ _
  | Pfmsubs _ _ _ _
  | Pfnmadds _ _ _ _
  | Pfnmsubs _ _ _ _

  | Pfmind _ _ _
  | Pfmaxd _ _ _
  | Pfsqrtd _ _
  | Pfmaddd _ _ _ _
  | Pfmsubd _ _ _ _
  | Pfnmaddd _ _ _ _
  | Pfnmsubd _ _ _ _
  | Pnop
    => Stuck
  end.

(* RB: NOTE: Where should we expose compartments to the execution of Asm
   instructions? A possibility is to encapsulate them in [exec_instr], wrapping
   the original definition as follows. At some level, this requires fewer
   modifications to the proofs that immediately follow, but other proofs where
   the wrapped [exec_instr] appears in the conclusion may not be solved without
   additional assumptions. *)

(* Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) : outcome := *)
(*   match rs#PC with *)
(*   | Vptr b _ => *)
(*     match PTree.get b (Mem.mem_compartments m) with (* RB: NOTE Encapsulate? *) *)
(*     | Some cp => exec_instr' f i rs m cp *)
(*     | _ => Stuck *)
(*     end *)
(*   | _ => Stuck *)
(*   end. *)

(** Translation of the LTL/Linear/Mach view of machine registers to
  the RISC-V view.  Note that no LTL register maps to [X31].  This
  register is reserved as temporary, to be used by the generated RV32G
  code.  *)

Definition preg_of (r: mreg) : preg :=
  match r with
               | R5  => X5  | R6  => X6  | R7  => X7
  | R8  => X8  | R9  => X9  | R10 => X10 | R11 => X11
  | R12 => X12 | R13 => X13 | R14 => X14 | R15 => X15
  | R16 => X16 | R17 => X17 | R18 => X18 | R19 => X19
  | R20 => X20 | R21 => X21 | R22 => X22 | R23 => X23
  | R24 => X24 | R25 => X25 | R26 => X26 | R27 => X27
  | R28 => X28 | R29 => X29 | R30 => X30

  | Machregs.F0  => F0  | Machregs.F1  => F1  | Machregs.F2  => F2  | Machregs.F3  => F3
  | Machregs.F4  => F4  | Machregs.F5  => F5  | Machregs.F6  => F6  | Machregs.F7  => F7
  | Machregs.F8  => F8  | Machregs.F9  => F9  | Machregs.F10 => F10 | Machregs.F11 => F11
  | Machregs.F12 => F12 | Machregs.F13 => F13 | Machregs.F14 => F14 | Machregs.F15 => F15
  | Machregs.F16 => F16 | Machregs.F17 => F17 | Machregs.F18 => F18 | Machregs.F19 => F19
  | Machregs.F20 => F20 | Machregs.F21 => F21 | Machregs.F22 => F22 | Machregs.F23 => F23
  | Machregs.F24 => F24 | Machregs.F25 => F25 | Machregs.F26 => F26 | Machregs.F27 => F27
  | Machregs.F28 => F28 | Machregs.F29 => F29 | Machregs.F30 => F30 | Machregs.F31 => F31
  end.

(** Undefine all registers except SP and callee-save registers *)

Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r =>
    if preg_eq r SP
    || In_dec preg_eq r (List.map preg_of (List.filter is_callee_save all_mregs))
    then rs r
    else Vundef.

Definition list_option_option_list {A: Type} (l: list (option A)): option (list A) :=
  List.fold_right (fun a x => match a, x with
                           | _, None => None
                           | Some y, Some xs => Some (y :: xs)
                           | None, _ => None
                           end) (Some nil) l.

Definition get_loc (rs: regset) (sp: val) (m: mem) (l: loc): option val :=
  match l with
  | R r => Some (rs (preg_of r))
  | S Incoming ofs ty =>
      let bofs := Stacklayout.fe_ofs_arg + 4 * ofs in
      Mem.loadv (chunk_of_type ty) m (Val.offset_ptr sp (Ptrofs.repr bofs)) top
  | _ => None
  end.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use RISC-V registers instead of locations. *)

Inductive extcall_arg (rs: regset) (sp: val) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs sp m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs cp v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr sp (Ptrofs.repr bofs)) cp = Some v ->
      extcall_arg rs sp m (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (sp: val) (m: mem): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs sp m l v ->
      extcall_arg_pair rs sp m (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs sp m hi vhi ->
      extcall_arg rs sp m lo vlo ->
      extcall_arg_pair rs sp m (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (sp: val) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs sp m) (loc_arguments sg) args.

Definition get_extcall_arguments' (rs: regset) (sp: val) (m: mem) (sg: signature) :=
  List.map (fun x => match x with
                  | One l => get_loc rs sp m l
                  | Twolong hi lo =>
                      match get_loc rs sp m hi, get_loc rs sp m lo with
                      | Some vhi, Some vlo => Some (Val.longofwords vhi vlo)
                      | _, _ => None
                      end
                  end) (loc_arguments sg).

Definition get_extcall_arguments (rs: regset) (sp: val) (m: mem) (sg: signature) :=
  list_option_option_list (get_extcall_arguments' rs sp m sg).

Lemma extcall_arguments_equiv:
  forall rs sp m sg args,
    extcall_arguments rs sp m sg args <-> get_extcall_arguments rs sp m sg = Some args.
Proof.
  admit.
Admitted.

(** Extract the values of the arguments to a call. *)
(* Note the difference: [loc_parameters] vs [loc_arguments] *)
Inductive call_arg (rs: regset) (sp: val) (m: mem): loc -> val -> Prop :=
  | call_arg_reg: forall r,
      call_arg rs sp m (R r) (rs (preg_of r))
  | call_arg_stack: forall ofs ty bofs cp v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr sp (Ptrofs.repr bofs)) cp = Some v ->
      call_arg rs sp m (S Incoming ofs ty) v.

Inductive call_arg_pair (rs: regset) (sp: val) (m: mem): rpair loc -> val -> Prop :=
  | call_arg_one: forall l v,
      call_arg rs sp m l v ->
      call_arg_pair rs sp m (One l) v
  | call_arg_twolong: forall hi lo vhi vlo,
      call_arg rs sp m hi vhi ->
      call_arg rs sp m lo vlo ->
      call_arg_pair rs sp m (Twolong hi lo) (Val.longofwords vhi vlo).

Definition call_arguments
    (rs: regset) (sp: val) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (call_arg_pair rs sp m) (loc_parameters sg) args.

Definition get_call_arguments' (rs: regset) (sp: val) (m: mem) (sg: signature) :=
  List.map (fun x => match x with
                  | One l => get_loc rs sp m l
                  | Twolong hi lo =>
                      match get_loc rs sp m hi, get_loc rs sp m lo with
                      | Some vhi, Some vlo => Some (Val.longofwords vhi vlo)
                      | _, _ => None
                      end
                  end) (loc_parameters sg).

Definition get_call_arguments (rs: regset) (sp: val) (m: mem) (sg: signature) :=
  list_option_option_list (get_call_arguments' rs sp m sg).

Lemma call_arguments_equiv:
  forall rs sp m sg args,
    call_arguments rs sp m sg args <-> get_call_arguments rs sp m sg = Some args.
Proof.
  admit.
Admitted.

Definition loc_external_result (sg: signature) : rpair preg :=
  map_rpair preg_of (loc_result sg).

Definition return_value (rs: regset) (sg: signature) :=
  match loc_result sg with
  | One l => rs (preg_of l)
  | Twolong l1 l2 => Val.longofwords (rs (preg_of l1)) (rs (preg_of l2))
  end.
(** Execution of the instruction at [rs PC]. *)

Inductive stackframe: Type :=
| Stackframe:
    forall (f: block)       (**r pointer to calling function *)
      (sg: signature)   (**r signature of the callee *)
      (cp: compartment) (**r compartment of the callee *)
      (sp: val)         (**r stack pointer in calling function *)
      (retaddr: ptrofs) (**r Asm return address in calling function *)
      (dummy_retaddr: block)
      (dummy_sp: block),
      stackframe.

Definition stack := list stackframe.

Definition call_comp (s: stack) :=
  match s with
  | nil => top
  | Stackframe f _ _ _ _ _ _ :: _ => Genv.find_comp_of_block ge f
  end.

Definition callee_comp_stackframe (st: stackframe) :=
  match st with
  | Stackframe _ _ cp _ _ _ _ => cp
  end.

Definition callee_comp (s: stack) :=
  match s with
  | nil => cp_main
  | f :: _ => callee_comp_stackframe f
  end.

(* The state of the stack when we start the execution *)
Definition initial_stack: stack := nil.

(* Updates to the stack *)
(* These two definitions shouldn't really do any real enforcement. Instead,
   they should just be used to keep track of the stack and use it in the
   invariants *)
(* The two definitions only update the stack when a cross-compartment change
   is detected *)
  Definition update_stack_call (s: stack) (sg: signature) (cp: compartment) rs' (m: mem):=
    let pc' := rs' # PC in
    let ra' := rs' # RA in
    let sp' := rs' # SP in
    let cp' := Genv.find_comp_in_genv ge pc' in
    if cp_eq_dec cp' cp then
      (* If we are in the same compartment as previously recorded, we
           don't update the stack *)
      Some (s, rs', m)
    else
      (* Otherwise, we simply push the new frame on the stack *)
      let (m', dummy_ra) := Mem.alloc m cp' 0 0 in
      let (m'', dummy_sp) := Mem.alloc m' cp' 0 0 in
      match sp' with
        | Vptr bsp _ => match Mem.set_perm m'' bsp Readable with
                         | Some m''' => match ra' with
                                       | Vptr f retaddr =>
                                           Some (Stackframe f sg cp' sp' retaddr dummy_ra dummy_sp :: s,
                                               (rs' # SP <- (Vptr dummy_sp Ptrofs.zero) # RA <- (Vptr dummy_ra Ptrofs.zero)),
                                               m''')
                                       | _ => None
                                       end
                       | _ => None
                       end
      | _ => None
      end.

  Lemma update_stack_call_PC s sg cp rs m:
    forall s' rs' m',
      update_stack_call s sg cp rs m = Some (s', rs', m') ->
      rs' PC = rs PC.
  Proof.
    intros.
    unfold update_stack_call in H.
    destruct cp_eq_dec; try congruence.
    do 2 destruct Mem.alloc.
    destruct (rs X2); try discriminate.
    destruct (Mem.set_perm); try discriminate.
    destruct (rs X1); try discriminate. inv H.
    rewrite Pregmap.gso; auto; now congruence.
  Qed.

  Definition update_stack_return (s: stack) :=
    match s with
    | nil => None
    | _ :: st' => Some st'
    end
  .

  Inductive state: Type :=
  | State: stack -> regset -> mem -> compartment -> state
  | ReturnState: stack -> regset -> mem -> compartment -> state.

Definition sig_call i :=
  match i with
  | Pjal_s _ sig flag | Pjal_r _ sig flag =>
                          if flag then Some sig else None
  | _ => None
  end.

(* Probably need to do the same thing and to define a [sig_return] function *)
Definition is_return i :=
  match i with
  | Pj_r _ _ flag => flag
  | _ => false
  end.

  Definition asm_parent_ra s :=
    match s with
    | nil => Vnullptr
    | Stackframe b _ _ sp retaddr _ _ :: _ => Vptr b retaddr
    end.

  Definition asm_parent_sp s :=
    match s with
    | nil => Vnullptr
    | Stackframe b _ _ sp retaddr _ _ :: _ => sp
    end.

  Definition asm_parent_dummy_ra s :=
    match s with
    | nil => Vnullptr
    | Stackframe _ _ _ _ _ b _ :: _ => Vptr b Ptrofs.zero
    end.

  Definition asm_parent_dummy_sp s :=
    match s with
    | nil => Vnullptr
    | Stackframe _ _ _ _ _ _ b :: _ => Vptr b Ptrofs.zero
    end.

  Definition parent_signature (stack: list stackframe) : signature :=
  match stack with
  | nil => signature_main
  | Stackframe _ sig _ _ _ _ _:: _ => sig
  end.

  Definition sig_of_call s :=
    match s with
    | Stackframe _ sg _ _ _ _ _ :: _ => sg
    | _ => signature_main
    end.

  Definition funsig (fd: fundef): signature :=
    match fd with
    | Internal f => fn_sig f
    | External ef => ef_sig ef
    end.

  Definition invalidate_call (rs: regset) (sig: signature) : regset :=
    fun r =>
      if preg_eq r PC || preg_eq r RA || preg_eq r SP ||
           in_dec preg_eq r (map preg_of (filter (fun x => LTL.in_mreg x (LTL.parameters_mregs sig)) all_mregs)) then
        rs r
      else
        Vundef.

  Notation "'SP'" := X2 (only parsing) : asm.
  Notation "'RA'" := X1 (only parsing) : asm.

  Definition invalidate_return (rs: regset) (sig: signature): regset :=
    fun r =>
      if preg_eq r PC || preg_eq r SP ||
           in_dec preg_eq r (map preg_of
                               (filter (fun x => LTL.in_mreg x (regs_of_rpair (loc_result sig))) all_mregs)) then
        rs r
      else
        Vundef.

  Definition invalidate_cross_return (rs: regset) (st: stack): regset :=
    fun r =>
      if preg_eq r PC then asm_parent_ra st
      else if preg_eq r SP then
             asm_parent_sp st
           else rs r.

  Lemma invalidate_call_PC: forall rs sig, invalidate_call rs sig PC = rs PC.
    unfold invalidate_call. intros. reflexivity.
  Qed.

  Lemma invalidate_return_PC: forall rs sig, invalidate_return rs sig PC = rs PC.
    unfold invalidate_return. intros. reflexivity.
  Qed.

  Lemma exec_instr_call_pc: forall f i sig rs rs' m m' cp,
    sig_call i = Some sig ->
    exec_instr f i rs m cp = Next rs' m' ->
    rs' X1 = (Val.offset_ptr (rs PC) Ptrofs.one).
  Proof.
    intros f i sig rs rs' m m' cp H exec.
    destruct i; simpl in H; try congruence;
      match goal with
      | H: (if ?iscl then Some _ else None) = Some _ |- _ => destruct iscl; try congruence; inv H
      end;
      simpl in exec; inv exec; auto.
    destruct Genv.allowed_addrof_b; inv H0; auto.
  Qed.

  Definition diff_sp_X2 (st: stack) (v: val) :=
    match asm_parent_sp st, v with
    | Vptr b1 _, Vptr b2 _ => b1 <> b2
    | _, _ => True
    end.

  
  Definition diff_sp (st: stack) (f: stackframe) :=
    match asm_parent_sp st, f with
    | Vptr b1 _, Stackframe _ _ _ (Vptr b2 _) _ _ _ => b1 <> b2
    | _, _ => True
    end.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m' b' ofs' st cp,
      rs PC = Vptr b ofs ->
      Genv.find_def ge b = Some (Gfun (Internal f)) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m (comp_of f) = Next rs' m' ->
      sig_call i = None ->
      is_return i = false ->
      forall (NEXTPC: rs' PC = Vptr b' ofs'),
      forall (ALLOWED: comp_of f = Genv.find_comp_of_block ge b'),
      step (State st rs m cp) E0 (State st rs' m' (comp_of f))

  | exec_step_load_arg_cross:
      forall b ofs f ch rd ra rs m st cp dsp o o' sp v rs' ty,
      rs PC = Vptr b ofs ->
      Genv.find_def ge b = Some (Gfun (Internal f)) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some (Pld_arg ch rd ra o) ->

      (* Loading from dummy stack pointer *)
      asm_parent_dummy_sp st = Vptr dsp Ptrofs.zero ->
      rs ra = Vptr dsp o' ->
     
      (* gets replaced with actual stack pointer *)
      asm_parent_sp st = sp ->

      Stacklayout.is_valid_param_loc (fn_sig f)
        (Ptrofs.unsigned (Ptrofs.add o' (eval_offset o))) ->

      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr sp (Ptrofs.add o' (eval_offset o))) top = Some v ->
      (forall ird, rd = inl ird -> rs' = nextinstr rs # ird <- v) ->
      (forall frd, rd = inr frd -> rs' = nextinstr rs # frd <- v) ->

      step (State st rs m cp) E0 (State st rs' m (comp_of f))

  | exec_step_load_arg_int:
      forall b ofs f ch rd ra rs m st cp o rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_def ge b = Some (Gfun (Internal f)) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some (Pld_arg ch rd ra o) ->

      forall (EXECi: forall ird, rd = inl ird ->
                       exec_load ch rs m ird ra o (comp_of f) false = Next rs' m'),
      forall (EXECf: forall frd, rd = inr frd ->
                       exec_load ch rs m frd ra o (comp_of f) false = Next rs' m'),

      step (State st rs m cp) E0 (State st rs' m' (comp_of f))

  | exec_step_internal_call:
      forall b ofs f i sig rs m rs' m' m'' b'  st st' args t rs'' rs''',
      rs PC = Vptr b ofs ->
      Genv.find_def ge b = Some (Gfun (Internal f)) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m (comp_of f) = Next rs' m' ->
      sig_call i = Some sig ->
      forall (NEXTPC: rs' PC = Vptr b' Ptrofs.zero), (* Only allow to call to ofs zero *)
      forall (ALLOWED: Genv.allowed_call ge (comp_of f) (Vptr b' Ptrofs.zero)),
      forall cp' (NEXTCOMP: Genv.find_comp_of_block ge b' = cp'),
      (* Is a call, we update the stack *)
      (* forall (SP_HAS_PTR: comp_of f <> cp' -> *)
      (*                exists bsp osp, rs SP = Vptr bsp osp *)
      (*                           /\ (forall fd, (Genv.find_def ge bsp <> Some (Gfun fd))) *)
      (*                           /\ (Mem.perm m bsp 0 Max Nonempty)), *)
      (* forall (DIFF_SP: (* Genv.type_of_call (comp_of f) cp' = Genv.CrossCompartmentCall -> *) *)
      (*     comp_of f <> cp' -> *)
      (*             diff_sp_X2 st (rs X2)), (* makes proof simpler. Check if really needed *) *)

      forall (STUPD: update_stack_call st sig (comp_of f) rs' m' = Some (st', rs'', m'')),
      forall (ARGS: call_arguments rs' (rs'#SP) m' sig args),
      (* note: it doesn't matter which register file we use to get the arguments *)
      (* Check signature *)
      forall (CALLSIG:
          Genv.type_of_call (comp_of f) cp' = Genv.CrossCompartmentCall ->
        (exists fd, Genv.find_def ge b' = Some (Gfun fd) /\ sig = funsig fd)),
      (* Is a call, we check whether we are allowed to pass pointers *)
      forall (NO_CROSS_PTR:
          Genv.type_of_call (comp_of f) cp' = Genv.CrossCompartmentCall ->
          List.Forall not_ptr args),
      forall (EV: call_trace ge (comp_of f) cp' (Vptr b' Ptrofs.zero)
              args (sig_args sig) t),
      forall (INVALIDATE: invalidate_call rs'' sig = rs'''),
      step (State st rs m (comp_of f)) t (State st' rs''' m'' (comp_of f))
  | exec_step_internal_return:
      forall b ofs f i rs m rs' m' st cp,
      rs PC = Vptr b ofs ->
      Genv.find_def ge b = Some (Gfun (Internal f)) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exec_instr f i rs m (comp_of f) = Next rs' m' ->
      is_return i = true ->
      (* We attempt a return, so we go to a ReturnState*)
      step (State st rs m cp) E0 (ReturnState st rs' m' (comp_of f))
  | exec_step_return:
      forall st rs rs' m rec_cp cp b ofs fd,
        rs PC <> Vnullptr ->
        rs PC <> Vundef ->
        forall (ATPC: rs PC = Vptr b ofs),
        forall (FD: Genv.find_def ge b = Some (Gfun (Internal fd))),
        forall (NEXTCOMP: Genv.find_comp_in_genv ge (rs PC) = cp),
        forall (INTERNAL_RET: rec_cp = cp),
        forall (INVALIDATE: invalidate_return rs (fn_sig fd) = rs'),
          step (ReturnState st rs m rec_cp) E0 (State st rs' m cp)
  | exec_step_return_cross:
      forall st st' rs rs' rs'' m m' sg t rec_cp cp',
        rs PC <> Vnullptr ->
        rs PC <> Vundef ->
        rs PC = asm_parent_dummy_ra st ->
        (* rs PC = Vone -> *)
        forall (RESTORE_SP: rs SP = asm_parent_dummy_sp st),
        (* Note that in the same manner, this definition only updates the stack when doing
         cross-compartment returns *)
        forall (STUPD: update_stack_return st = Some st'),
        forall (SIG_STACK: sig_of_call st = sg),
        (* We do not return a pointer *)
        forall (NO_CROSS_PTR: Genv.type_of_call cp' rec_cp = Genv.CrossCompartmentCall ->
                         not_ptr (return_value rs sg)),
        forall (COMP: Genv.find_comp_in_genv ge (asm_parent_ra st) = cp'),
        forall (EV: return_trace ge cp' rec_cp (return_value rs sg) (sig_res sg) t),
        forall (DUMMY_DIFF: asm_parent_dummy_sp st <> asm_parent_sp st),
      forall (INVALIDATE: invalidate_return rs sg = rs'),
      forall (INVALIDATE: invalidate_cross_return rs' st = rs''),
      forall (MAKE_FREEABLE: Some m' = match asm_parent_sp st with
                             | Vptr bsp _ => Mem.set_perm m bsp Freeable
                             | _ => None
                             end),
          step (ReturnState st rs m rec_cp) t (State st' rs'' m' cp')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m' st,
      rs PC = Vptr b ofs ->
      Genv.find_def ge b= Some (Gfun (Internal f)) ->
      find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge (comp_of f) rs (rs SP) m args vargs ->
      external_call ef ge (comp_of f) vargs m t vres m' ->
        (* this condition makes explicit the fact a builtin can't modify the PC directly *)
      forall (RES_NOT_PC: exists reg, res = map_builtin_res preg_of reg),
      rs' = nextinstr
              (set_res res vres
                (undef_regs (map preg_of (destroyed_by_builtin ef))
                   (rs #X1 <- Vundef #X31 <- Vundef))) ->
      step (State st rs m (comp_of f)) t (State st rs' m' (comp_of f))
  | exec_step_external:
      forall b ef args res rs m t rs' m' st sp cp,
      rs PC = Vptr b Ptrofs.zero ->
      forall (SP0: cp = bottom -> sp = rs SP)
        (SP1: cp <> bottom -> sp = asm_parent_sp st),
      Genv.find_def ge b = Some (Gfun (External ef)) ->
      external_call ef ge cp args m t res m' ->
      extcall_arguments rs sp m (ef_sig ef) args ->
      rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_caller_save_regs rs))#PC <- (rs RA) ->
      step (State st rs m cp) t (ReturnState st rs' m' bottom).

End RELSEM.

(** Execution of whole programs. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
        # SP <- Vnullptr
        # RA <- Vnullptr in
      Genv.init_mem p = Some m0 ->
      initial_state p (State nil rs0 m0 top).

Inductive final_state (p: program): state -> int -> Prop :=
  | final_state_intro: forall rs m r cp,
      rs PC = Vnullptr ->
      rs X10 = Vint r ->
      final_state p (ReturnState nil rs m cp) r
.

Definition comp_of_main (p: program) :=
  let ge := Genv.globalenv p in
  Genv.find_comp_of_ident ge (prog_main p).
Definition semantics (p: program) :=
  Semantics step (initial_state p) (final_state p) (Genv.globalenv p).
(** Determinacy of the [Asm] semantics. *)

Remark extcall_arguments_determ:
  forall rs sp m sg args1 args2,
  extcall_arguments rs sp m sg args1 -> extcall_arguments rs sp m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             extcall_arg rs sp m l v1 -> extcall_arg rs sp m l v2 -> v1 = v2).
  { intros. inv H; inv H0. congruence.
    destruct sp; try discriminate.
    simpl in H2, H5.
    apply Mem.load_result in H2.
    apply Mem.load_result in H5. congruence. }
  assert (B: forall p v1 v2,
             extcall_arg_pair rs sp m p v1 -> extcall_arg_pair rs sp m p v2 -> v1 = v2).
  { intros. inv H; inv H0. 
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs sp m) ll vl1 ->
             forall vl2, list_forall2 (extcall_arg_pair rs sp m) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

Remark call_arguments_determ:
  forall rs sp m sg args1 args2,
  call_arguments rs sp m sg args1 -> call_arguments rs sp m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (A: forall l v1 v2,
             call_arg rs sp m l v1 -> call_arg rs sp m l v2 -> v1 = v2).
  { intros. inv H; inv H0. congruence.
    destruct sp; try discriminate.
    simpl in H2, H5.
    apply Mem.load_result in H2.
    apply Mem.load_result in H5. congruence. }
  assert (B: forall p v1 v2,
             call_arg_pair rs sp m p v1 -> call_arg_pair rs sp m p v2 -> v1 = v2).
  { intros. inv H; inv H0.
    eapply A; eauto.
    f_equal; eapply A; eauto. }
  assert (C: forall ll vl1, list_forall2 (call_arg_pair rs sp m) ll vl1 ->
             forall vl2, list_forall2 (call_arg_pair rs sp m) ll vl2 -> vl1 = vl2).
  {
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; eauto. }
  intros. eapply C; eauto.
Qed.

(* RB: NOTE: In the next proof, the wrapped [exec_instr] would require extra
   processing, such as this. *)
(* Ltac peel_exec_instr := *)
(*   match goal with *)
(*   | Hexec : exec_instr _ _ _ ?RS ?M = _, *)
(*     Hpc : ?RS PC = Vptr ?B _ |- _ *)
(*     => *)
(*     unfold exec_instr in Hexec; *)
(*     rewrite Hpc in Hexec; *)
(*     destruct ((Mem.mem_compartments M) ! B) *)
(*   end. *)

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
intros; constructor; simpl; intros.
- (* determ *)
  inv H; inv H0; Equalities; try discriminate.
  + split. constructor. auto.
  + split. constructor.
    destruct rd0.
    admit. admit.
  + admit.
  + admit.
  + split. constructor. auto.
    destruct rd0.
    * exploit EXECi; eauto. exploit EXECi0; eauto.
      congruence.
    * exploit EXECf; eauto. exploit EXECf0; eauto.
      congruence.
  + inv EV; inv EV0; try congruence.
    split. constructor. auto.
    assert (i1 = i) by congruence. subst.
    assert (args0 = args) by (eapply call_arguments_determ; eauto). subst.
    assert (vl0 = vl) by (eapply eventval_list_match_determ_2; eauto). subst.
    split. constructor. auto.
  + now destruct i0.
  + now destruct i0.
  + split. constructor. auto.
  + split; constructor; auto.
  + admit.
  + admit.
  + inv EV; inv EV0; try congruence.
    admit. admit.
  + assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0.
    exploit external_call_determ. eexact H5. eexact H15. intros [A B].
    split. auto. intros. destruct B; auto. subst. auto.
  + assert (sp = sp0).
    { destruct cp; try now rewrite SP0, SP2.
      now rewrite SP1, SP3.
      now rewrite SP1, SP3. }
    subst sp0.
    assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
    exploit external_call_determ. eexact H3. eexact H12. intros [A B].
    split. auto. intros. destruct B; auto. subst. congruence.
- (* trace length *)
  red; intros. inv H; simpl.
  lia. lia. lia.
  inv EV; auto.
  lia. lia.
  inv EV; auto.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
- (* initial states *)
  inv H; inv H0. f_equal. congruence.
- (* final no step *)
  inv H.
  red; intros; red; intros.
  inv H. congruence. congruence.
- (* final states *)
  inv H; inv H0. congruence.
Admitted.

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | IR RA  => false
  | IR X31 => false
  | IR _   => true
  | FR _   => true
  | PC     => false
  end.

Section ExecSem.

  Declare Scope reducts_monad_scope.

  Notation "'do' U <- A ; B" := (match A with Some U => B | None => None end)
                                 (at level 200, U ident, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation "'do' 'Vptr' U Y <- A ; B" := (match A with Vptr U Y => B | _ => None end)
                                          (at level 200, U ident, Y ident, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation "'do' U , Y <- A ; B" := (match A with Some (U, Y) => B | None => None end)
                                     (at level 200, U ident, Y ident, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation "'do' U , Y , Z <- A ; B" := (match A with Some (U, Y, Z) => B | None => None end)
                                         (at level 200, U ident, Y ident, Z ident, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation "'do' U , Y , Z , W <- A ; B" := (match A with Some (U, Y, Z, W) => B | None => None end)
                                             (at level 200, U ident, Y ident, Z ident, W ident, A at level 100, B at level 200)
      : reducts_monad_scope.

  Notation " 'check' A ; B" := (if A then B else None)
                                 (at level 200, A at level 100, B at level 200)
      : reducts_monad_scope.

  Local Open Scope reducts_monad_scope.

  Variable do_external_function:
    string -> signature -> Senv.t -> compartment -> world -> list val -> mem -> option (world * trace * val * mem).

  Hypothesis do_external_function_sound:
    forall cp id sg ge vargs m t vres m' w w',
      do_external_function id sg ge cp w vargs m = Some(w', t, vres, m') ->
      external_functions_sem id sg ge cp vargs m t vres m' /\ possible_trace w t w'.

  Hypothesis do_external_function_complete:
    forall cp id sg ge vargs m t vres m' w w',
      external_functions_sem id sg ge cp vargs m t vres m' ->
      possible_trace w t w' ->
      do_external_function id sg ge cp w vargs m = Some(w', t, vres, m').

  Variable do_inline_assembly:
    string -> signature -> Senv.t -> compartment -> world -> list val -> mem -> option (world * trace * val * mem).

  Hypothesis do_inline_assembly_sound:
    forall txt sg ge cp vargs m t vres m' w w',
      do_inline_assembly txt sg ge cp w vargs m = Some(w', t, vres, m') ->
      inline_assembly_sem txt sg ge cp vargs m t vres m' /\ possible_trace w t w'.

  Hypothesis do_inline_assembly_complete:
    forall txt sg ge cp vargs m t vres m' w w',
      inline_assembly_sem txt sg ge cp vargs m t vres m' ->
      possible_trace w t w' ->
      do_inline_assembly txt sg ge cp w vargs m = Some(w', t, vres, m').


Definition build_initial_state (p: program): option state :=
  let ge := Genv.globalenv p in
  let rs0 :=
    (Pregmap.init Vundef)
      # PC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
               # SP <- Vnullptr
                        # RA <- Vnullptr in
  do m0 <- Genv.init_mem p;
  Some (State initial_stack rs0 m0 top).

End ExecSem.


Section SECURITY.

Definition asm_in_side (s: split) (lr: side) (p: Asm.program) :=
  List.Forall (fun '(id, gd) =>
                 match gd with
                 | Gfun (Internal f) => s (comp_of f) = lr
                 | _ => True
                 end)
    (prog_defs p).

#[export] Instance asm_has_side: has_side (Asm.program) :=
  { in_side s := fun p δ => asm_in_side s δ p }.

Definition asm_compatible (s: split) (p p': Asm.program) :=
  s |= p ∈ Left /\ s |= p' ∈ Right.

End SECURITY.
