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

Require Import Coqlib List.
Require Import Maps.
Require Import CapAST.
Require Import Integers.
Require Import Floats.
Require Import OCapValues.
Require Import CapMemory.
Require Import Events.
Require Import CapGlobalenvs.
Require Import Smallstep.
Require Import CapLocations.
Require Stacklayout.
Require Import Conventions.

Notation offset_arg := Stacklayout.offset_arg.

Local Open Scope error_monad_scope.

(** * Abstract syntax *)

(** Integer registers.  X0 is treated specially because it always reads 
  as zero and is never used as a destination of an instruction. *)

(** We model a merged integer register machine, in which integer
    registers can hold integers and capabilities *)

Inductive ireg: Type :=
  | X1:  ireg | X2:  ireg | X3:  ireg | X4:  ireg | X5:  ireg
  | X6:  ireg | X7:  ireg | X8:  ireg | X9:  ireg | X10: ireg
  | X11: ireg | X12: ireg | X13: ireg | X14: ireg | X15: ireg
  | X16: ireg | X17: ireg | X18: ireg | X19: ireg | X20: ireg
  | X21: ireg | X22: ireg | X23: ireg | X24: ireg | X25: ireg
  | X26: ireg | X27: ireg | X28: ireg | X29: ireg | X30: ireg
  | X31: ireg | X32 : ireg.

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

(** In particular, we model the following special capability registers

   - PCC : extends the existing PC to be a full capability, imposing
     validity, permission, bounds checks on instruction fetch

   - DDC : indirects non-capability loads and stores, controlling and
     relocating data accesses to memory

 *)

(** registers that can contain capabilities *)
Inductive creg: Type :=
  | IRcap: ireg -> creg
  | PCcap: creg
  | DDcap: creg.

Inductive preg: Type :=
  | IR: ireg -> preg                    (**r integer registers *)
  | FR: freg -> preg                    (**r double-precision float registers *)
  | PCC: preg                          (**r program counter capability *)
  | DDC: preg.                         (**r default data capability *) 

Definition creg_to_preg (c: creg) : preg :=
  match c with
  | IRcap i => IR i
  | PCcap => PCC
  | DDcap => DDC
  end.

Coercion creg_to_preg: creg >-> preg.
Coercion IRcap: ireg >-> creg.
Coercion IR: ireg >-> preg.
Coercion FR: freg >-> preg.

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. apply freg_eq. Defined.

Module PregEq.
  Definition t  := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

(** Conventional names for stack pointer ([SPC]) and return address code and data ([RAC] & [RAD]). *)

(** Each will hold capabilities: an uninitialized directed capability
    in SPC and a sealed return & data capability pair in RAC and RAD
*)

Notation "'SPC'" := X3 (only parsing) : asm.
Notation "'RAC'" := X1 (only parsing) : asm.
Notation "'SPPC'" := X2 (only parsing) : asm.
Notation "'EC'" := X31 (only parsing) : asm.

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

(** CHERI RISC-V extends both 32-bit and 64-bit integers with 64-bit
    and 128-bit capabilities respectively.

    CLEN refers to the capability length, XLEN to the architecture
    address space length. CLEN equals twice the XLEN.

    Both a merged and split integer and capability register files are
    supported, we choose here to model a merged register file. Thus,
    "64I" and "128I" can hold both integers and capabilities.
    non-capability instructions ignore the upper XLEN bits of the
    register. e.g., an i32 bit instruction ignores the upper 32 bits
    in the (merged) integer/capability register.

    CHERI RISC-V adheres to a strong type safety property for all
    capability-aware instructions: all instructions explicitly encode
    whether an integer or capability operand is being used, and
    attempts to use untagged values where tagged ones are expected
    will lead to an exception.

    We choose to similarly trap whenever tagged values are used when
    untagged ones are expected


    CHERI RISC-V supports legacy load/store immediate operations by
    using the default data capability. A core design choice of CHERI
    is to maintain instruction intentionality. To that end, multiple
    approaches have been investigated to maintain intentionality while
    conserving opcode space

    1) introduce a full set of new load/store instructions to
    distinguish between direct and indirect capability use

    2) introduce a limited aset of load/store instructions

    3) introduce a new capability encoding mode in which existing
    load/store opcode space is reused for capability-relative
    accesses, allowing rich set of load-store instructions

    
    We will here model option (1), but note that it is possible to map
    this approach to one with an encoding mode bit.

    There are three kinds of added instructions: instructions that use
    capabilities to load/store from and to memory and to jump,
    instructions that manipulate capabilities, and instructions that
    loads capability fields

    The instruction set architecture is an extension of the existing
    CompCert model of RISC-V, with the exception of stack related
    pseudo instructions.

*)

Definition label := positive.

(** A note on immediates: there are various constraints on immediate
  operands to RISC-V instructions.  We do not attempt to capture these
  restrictions in the abstract syntax nor in the semantics.  The
  assembler will emit an error if immediate operands exceed the
  representable range.  Of course, our RISC-V generator (file
  [Asmgen]) is careful to respect this range. *)

Inductive instruction : Type :=
  | Pmv     (rd: creg) (rs: creg)                    (**r integer or capability move, 
                                                        includes from a special purpose 
                                                        capability register 
                                                        ([CReadHwr] and [CWriteHwr] in CHERI) *)

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

  (* Branches to a register will expect a capability, potentially
     sealed as a sentry capability. 
     Branches to labels or symbols indirectly use the PCC. *)
            
  (* Unconditional jumps.  Links are always to X1/RA. *)
  | Pj_l    (l: label)                                        (**r jump to label *)
  (* | Pj_s    (symb: ident)           (sg: signature)           (**r jump to symbol *) *)
  | Pj_r    (r: ireg)               (* (sg: signature) (iscl: bool) jump is no longer a return event marker *) (**r jump register *)
  (* | Pjal_s  (symb: ident)           (sg: signature) (iscl: bool) (**r jump-and-link symbol *) *)
  | Pjal_r  (r: ireg)               (sg: signature) (iscl: bool) (**r jump-and-link register *)
  (* | PCjal_s (symb: ident) (s: ireg) (sg: signature) (iscl: bool) (**r jump-and-sealed-link symbol *) *)
  | PCjal_r (r s: ireg)             (sg: signature) (iscl: bool) (**r jump-and-sealed-link register *)
            
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

  (* Sealed capability invocation *)
  | PCinvoke (rs1 rs2: ireg0) (iscl: bool)             (**r unseal and jump to rs2 while unsealing rs1 *)

  (* Legacy loads and stores: semantics use the DDC: ireg is expected to hold a heap pointer (integer) *)
  | Plb     (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load signed int8 *)
  | Plbu    (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load unsigned int8 *)
  | Plh     (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load signed int16 *)
  | Plhu    (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load unsigned int16 *)
  | Plw     (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load int32 *)
  | Plw_a   (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load any32 *)
  | Pld     (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load int64 *)
  | Pld_a   (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load any64 *)
  | Plcw    (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load cap64 *)
  | Plcd    (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load cap128 *)
  | Plcd_a  (rd: ireg) (ra: ireg) (ofs: offset) (priv: bool)    (**r load any128 *)
            
  | Psb     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int8 *)
  | Psh     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int16 *)
  | Psw     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int32 *)
  | Psw_a   (rs: ireg) (ra: ireg) (ofs: offset)     (**r store any32 *)
  | Psd     (rs: ireg) (ra: ireg) (ofs: offset)     (**r store int64 *)
  | Psd_a   (rs: ireg) (ra: ireg) (ofs: offset)     (**r store any64 *)
  | Pscw    (rs: ireg) (ra: ireg) (ofs: offset)     (**r store cap64 *)
  | Pscd    (rs: ireg) (ra: ireg) (ofs: offset)     (**r store cap128 *)
  | Pscd_a  (rs: ireg) (ra: ireg) (ofs: offset)     (**r store any128 *)

  (* Capability load and stores: ra is expected to hold an unsealed initialized capability *)
  | PClb    (rd: ireg) (ra: ireg) (ofs: offset) (h priv: bool)    (**r load signed int8 *)
  | PClbu   (rd: ireg) (ra: ireg) (ofs: offset) (h priv: bool)    (**r load unsigned int8 *)
  | PClh    (rd: ireg) (ra: ireg) (ofs: offset) (h priv: bool)    (**r load signed int16 *)
  | PClhu   (rd: ireg) (ra: ireg) (ofs: offset) (h priv: bool)    (**r load unsigned int16 *)
  | PClw    (rd: ireg) (ra: ireg) (ofs: offset) (h priv: bool)    (**r load int32 *)
  | PClw_a  (rd: ireg) (ra: ireg) (ofs: offset) (h priv: bool)    (**r load any32 *)
  | PCld    (rd: ireg) (ra: ireg) (ofs: offset) (h priv: bool)    (**r load int64 *)
  | PCld_a  (rd: ireg) (ra: ireg) (ofs: offset) (h priv: bool)    (**r load any64 *)
  | PClwc   (rd: ireg) (ra: ireg) (ofs: offset) (h priv: bool)    (**r load cap64 *)
  | PClcd   (rd: ireg) (ra: ireg) (ofs: offset) (h priv: bool)    (**r load cap128 *)
  | PClcd_a (rd: ireg) (ra: ireg) (ofs: offset) (h priv: bool)    (**r load any128 *)
            
  | PCsb    (rs: ireg) (ra: ireg) (ofs: offset) (h: bool)    (**r store int8 *)
  | PCsh    (rs: ireg) (ra: ireg) (ofs: offset) (h: bool)    (**r store int16 *)
  | PCsw    (rs: ireg) (ra: ireg) (ofs: offset) (h: bool)    (**r store int32 *)
  | PCsw_a  (rs: ireg) (ra: ireg) (ofs: offset) (h: bool)    (**r store any32 *)
  | PCsd    (rs: ireg) (ra: ireg) (ofs: offset) (h: bool)    (**r store int64 *)
  | PCsd_a  (rs: ireg) (ra: ireg) (ofs: offset) (h: bool)    (**r store any64 *)
  | PCscw   (rs: ireg) (ra: ireg) (ofs: offset) (h: bool)    (**r store cap64 *)
  | PCscd   (rs: ireg) (ra: ireg) (ofs: offset) (h: bool)    (**r store cap128 *)
  | PCscd_a (rs: ireg) (ra: ireg) (ofs: offset) (h: bool)    (**r store any128 *)

  | PCfls     (rd: freg) (ra: ireg) (ofs: offset) (h priv: bool)    (**r load float *)
  | PCfss     (rs: freg) (ra: ireg) (ofs: offset) (h: bool)         (**r store float *)
  | PCfld     (rd: freg) (ra: ireg) (ofs: offset) (h priv: bool)    (**r load 64-bit float *)
  | PCfld_a   (rd: freg) (ra: ireg) (ofs: offset) (h priv: bool)    (**r load any64 *)
  | PCfsd     (rd: freg) (ra: ireg) (ofs: offset) (h: bool)         (**r store 64-bit float *)
  | PCfsd_a   (rd: freg) (ra: ireg) (ofs: offset) (h: bool)         (**r store any64 *)
            
  (* Capability load and stores: ra is expected to hold an unsealed uninitialized capability *)
  | PCUlb    (rd: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h priv: bool)    (**r load signed int8 *)
  | PCUlbu   (rd: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h priv: bool)    (**r load unsigned int8 *)
  | PCUlh    (rd: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h priv: bool)    (**r load signed int16 *)
  | PCUlhu   (rd: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h priv: bool)    (**r load unsigned int16 *)
  | PCUlw    (rd: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h priv: bool)    (**r load int32 *)
  | PCUlw_a  (rd: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h priv: bool)    (**r load any32 *)
  | PCUld    (rd: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h priv: bool)    (**r load int64 *)
  | PCUld_a  (rd: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h priv: bool)    (**r load any64 *)
  | PCUlwc   (rd: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h priv: bool)    (**r load cap64 *)
  | PCUlcd   (rd: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h priv: bool)    (**r load cap128 *)
  | PCUlcd_a (rd: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h priv: bool)    (**r load any128 *)
            
  | PCUsb    (rs: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h: bool)    (**r store int8 *)
  | PCUsh    (rs: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h: bool)    (**r store int16 *)
  | PCUsw    (rs: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h: bool)    (**r store int32 *)
  | PCUsw_a  (rs: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h: bool)    (**r store any32 *)
  | PCUsd    (rs: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h: bool)    (**r store int64 *)
  | PCUsd_a  (rs: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h: bool)    (**r store any64 *)
  | PCUscw   (rs: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h: bool)    (**r store cap64 *)
  | PCUscd   (rs: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h: bool)    (**r store cap128 *)
  | PCUscd_a (rs: ireg) (ra: ireg) (ro: ireg) (ofs: offset) (h: bool)    (**r store any128 *)
             
  | PCUfls     (rd: freg) (ra: ireg) (ro: ireg) (ofs: offset) (h priv: bool)    (**r load float *)
  | PCUfss     (rs: freg) (ra: ireg) (ro: ireg) (ofs: offset) (h: bool)         (**r store float *)
  | PCUfld     (rd: freg) (ra: ireg) (ro: ireg) (ofs: offset) (h priv: bool)    (**r load 64-bit float *)
  | PCUfld_a   (rd: freg) (ra: ireg) (ro: ireg) (ofs: offset) (h priv: bool)    (**r load any64 *)
  | PCUfsd     (rd: freg) (ra: ireg) (ro: ireg) (ofs: offset) (h: bool)         (**r store 64-bit float *)
  | PCUfsd_a   (rd: freg) (ra: ireg) (ro: ireg) (ofs: offset) (h: bool)         (**r store any64 *)

  (* Capability-inspection instructions *)
  | PCgp    (rd: ireg) (ra: ireg)                   (**r get permission *)
  | PCgt    (rd: ireg) (ra: ireg)                   (**r get object type *)
  | PCgg    (rd: ireg) (ra: ireg)                   (**r get tag *)    
  | PCgs    (rd: ireg) (ra: ireg)                   (**r get sealed status *)
  | PCga_s  (rd: ireg) (ra: ireg)                   (**r get address offset *)
  | PCga_h  (rd: ireg) (ra: ireg)                   (**r get address offset *)
  | PCgb_s  (rd: ireg) (ra: ireg)                   (**r get base *)    
  | PCge_s  (rd: ireg) (ra: ireg)                   (**r get end *)    
  | PCgb_h  (rd: ireg) (ra: ireg)                   (**r get base *)    
  | PCge_h  (rd: ireg) (ra: ireg)                   (**r get end *)
  | PCgl_s  (rd: ireg) (ra: ireg)                   (**r get length *)
  | PCgl_h  (rd: ireg) (ra: ireg)                   (**r get length *)

  (* Capability-modification instructions *)          
  | PCseal      (rd: ireg) (rs1 rs2: ireg)             (**r sealing *)
  | PCunseal    (rd: ireg) (rs1 rs2: ireg)             (**r unsealing *)
  | PCpermand   (rd: ireg) (rs1 rs2: ireg)             (**r restricting the permission *)
  | PCsaddr_w   (rd: ireg) (rs1 rs2: ireg)             (**r sets address of rs1 to rs2 *)
  | PCsaddr_l   (rd: ireg) (rs1 rs2: ireg)             (**r sets address of rs1 to rs2 *)
  | PCiaddr_w   (rd: ireg) (rs1 rs2: ireg0)            (**r increments address of rs1 by rs2 *)
  | PCiaddr_l   (rd: ireg) (rs1 rs2: ireg0)            (**r increments address of rs1 by rs2 *)
  | PCiaddr_iw  (rd: ireg) (rs1 : ireg0) (imm: int)    (**r increments address of rs1 by imm for 32 bit arch *)
  | PCiaddr_il  (rd: ireg) (rs1 : ireg0) (imm: int64)  (**r increments address of rs1 by imm for 64 bit arch *)
  | PCsbase     (rd: ireg) (rs1 rs2: ireg)             (**r sets base to current address with length rs2 *)
  | PCsbase_iw  (rd: ireg) (rs1 : ireg) (imm: int)     (**r sets base to current address with length imm for 32 bit arch*)
  | PCsbase_il  (rd: ireg) (rs1 : ireg) (imm: int64)   (**r sets base to current address with length imm for 64 bit arch*)
  (* | PCcleart    (rd: ireg) (rs: ireg)                  (**r clears tag of capability in rs *) *)
  | PCCseal     (rd: ireg) (rs1 rs2: ireg)             (**r conditional sealing *)
  | PCseal_e    (rd: ireg) (rs: ireg)                  (**r seals to a sentry capability (E permission) *)
  | PCpromote   (rd: ireg) (rs: ireg)                  (**r promotes an uninitialized capability to its initialized counterpart *)

  (* Capability pointer arithmetic instructions *)
  | PCtoPtr_h  (rd: ireg) (rs1 rs2: ireg)             (**r rd is set to rs1.address - rs2.base *)
  | PCsub_h    (rd: ireg) (rs1 rs2: ireg)             (**r rd is set to rs1.address - rs2.address *)
  | PCtoPtr_s  (rd: ireg) (rs1 rs2: ireg)             (**r rd is set to rs1.address - rs2.base *)
  | PCsub_s    (rd: ireg) (rs1 rs2: ireg)             (**r rd is set to rs1.address - rs2.address *)
  | PCUtoPtr_h (rd: ireg) (rs1 rs2: ireg)             (**r rd is set to rs1.end - rs2.address *)
  | PCUtoPtr_s (rd: ireg) (rs1 rs2: ireg)             (**r rd is set to rs1.end - rs2.address *)
               
  (* Capability pointer comparison instructions *)
  | PCsubset (rd: ireg) (rs1 rs2: ireg)             (**r rd is set to 1 if rs2 was derived from rs1 *)
  | PCeex    (rd: ireg) (rs1 rs2: ireg)             (**r rd is set to 1 if the in memory representations of rs1 and rs2 are equal *)

  (* fast register clearing instructions *)
  | PCCclear  (imm: int)                            (**r i'th iregister is cleared if bit i in imm is 1, 0'th bit refers to DDC *)
  | PCCclearf (imm: int)                            (**r i'th fregister is cleared if bit i in imm is 1 *)

  (* tag-memory access instructions *)
  | PCloadtag (dst: ireg) (rs1: ireg)               (**r rd is set to a bitstring with the tags of capabilities located 
                                                       in rs1.address to rs1.address + CAPS_PER_CACHE_LINE (bit i == 1 <-> rs1) *)
              
(* Probably doesn't need privilged stores because can't write directly to parameters. Instead
   writing to a parameter writes to a /copy/ of the parameter *)

  (* Synchronization *)
  | Pfence                                          (**r fence *)

  (* floating point register move *)
  | Pfmv     (rd: freg) (rs: freg)                  (**r move *)
  | Pfmvxs   (rd: ireg) (rs: freg)                  (**r move FP single to integer register *)
  | Pfmvxd   (rd: ireg) (rs: freg)                  (**r move FP double to integer register *)

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
  (* | Pallocframe (sz: Z) (pos: ptrofs)               (**r allocate new stack frame *) *)
  (* | Pfreeframe  (sz: Z) (pos: ptrofs)               (**r deallocate stack frame and restore previous frame *) *)
  | Plabel  (lbl: label)                            (**r define a code label *)
  | Pptrbr  (rd: ireg) (lbl1 lbl2: label)           (**r branches to lbl1 if rd contains a heap ptr, lbl2 if rd contains a stack ptr *)
  (* | Ploadsymbol (rd: ireg) (id: ident) (ofs: ptrofs) (**r load the address of a symbol *) *)
  (* | Ploadsymbol_high (rd: ireg) (id: ident) (ofs: ptrofs) (**r load the high part of the address of a symbol *) *)
  | Ploadli (rd: ireg) (i: int64)                   (**r load an immediate int64 *)
  | Ploadfi (rd: freg) (f: float)                   (**r load an immediate float *)
  | Ploadsi (rd: freg) (f: float32)                 (**r load an immediate single *)
  | Pbtbl   (r: ireg)  (tbl: list label)            (**r N-way branch through a jump table *)
  | Pbuiltin: external_function -> list (builtin_arg preg)
              -> builtin_res preg -> instruction    (**r built-in function (pseudo) *)
  | Pnop : instruction                              (**r nop instruction *)
  | Pfail : instruction.                            (**r fail instruction (deliberate crash) *)


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

(** The capability machine backend is modelled in a flat memory model,
    thus we do not need the stack related pseudo instructions *)

Definition code := list instruction.
Record function : Type := mkfunction { fn_comp: compartment; fn_sig: signature; fn_wrapper: code; fn_code: code }.
Instance has_comp_function: has_comp function := fn_comp.
Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

(** * Operational semantics *)

(** The semantics operates over a single mapping from registers
  (type [preg]) to values.  We maintain
  the convention that integer registers are mapped to values of
  type [Tcap], or [Tint] or [Tlong] (in 64 bit mode),
  and float registers to values of type [Tsingle] or [Tfloat]. *)

Definition regset := Pregmap.t ocval.
Definition genv := Genv.t fundef unit.

Definition get0w (rs: regset) (r: ireg0) : ocval :=
  match r with
  | X0 => OCVint Int.zero
  | X r => rs r
  end.

Definition get0l (rs: regset) (r: ireg0) : ocval :=
  match r with
  | X0 => OCVlong Int64.zero
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
  | r :: l' => undef_regs l' (rs#r <- OCVundef)
  end.

(** Assigning a register pair *)

Definition set_pair (p: rpair preg) (v: ocval) (rs: regset) : regset :=
  match p with
  | One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

(** Assigning multiple registers *)

Fixpoint set_regs (rl: list preg) (vl: list ocval) (rs: regset) : regset :=
  match rl, vl with
  | r1 :: rl', v1 :: vl' => set_regs rl' vl' (rs#r1 <- v1)
  | _, _ => rs
  end.

Fixpoint set_regs_default (rl: list preg) (v: ocval) (rs: regset) : regset :=
  match rl with
  | r1 :: rl' => set_regs_default rl' v (rs#r1 <- v)
  | _ => rs
  end.

(** Assigning the result of a builtin *)

Fixpoint set_res (res: builtin_res preg) (v: ocval) (rs: regset) : regset :=
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

(* ALG: TODO: discuss below -> in a capability machine, the high part
is specifically a capability *)
(** The two functions below axiomatize how the linker processes
  symbolic references [symbol + offset)] and splits their
  actual values into a 20-bit high part [%hi(symbol + offset)] and 
  a 12-bit low part [%lo(symbol + offset)]. *)

Parameter low_half: genv -> ident -> ptrofs -> ptrofs.
Parameter high_half: genv -> ident -> ptrofs -> ocval.

(** The fundamental property of these operations is that, when applied
  to the address of a symbol, their results can be recombined by
  addition, rebuilding the original address. *)

Axiom low_high_half:
  forall id ofs,
    match Val.offset_ptr (high_half ge id ofs) (low_half ge id ofs) with
    | Some ofs' => ofs' = (Genv.symbol_address ge id ofs)
    | None => True
    end.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome: Type :=
  | Next:  regset -> mem -> outcome
  | Stuck: outcome
  | Crashed: outcome. (* we model capability failure as a crash *)

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]). *)

Definition nextinstr (rs: regset) (m: mem) : outcome :=
  match Val.offset_ptr rs#PCC Ptrofs.one with
  | Some pc' => Next (rs#PCC <- pc') m
  | None => Crashed
  end.

(* ALG: We do not model capability checks of the program
counter. Thus, the address it points to is the relative offset within
the program, rather than obsolute address *)
Definition goto_label (f: function) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 (fn_wrapper f ++ fn_code f) with
  | None => Stuck
  | Some pos => (* pos is the relative offset *)
      match rs#PCC with
      | OCVcap (OCsealable (OCVmem RX Global b e a))
                 => let a_lbl := Ptrofs.repr pos in (* a_lbl is the relative offset *)
                   Next (rs#PCC <- (OCVcap (OCsealable (OCVmem RX Global b e a_lbl)))) m
      | OCVcap (OCsealable (OCVmem RWX Global b e a))
                 => let a_lbl := Ptrofs.repr pos in (* a_lbl is the relative offset *)
                   Next (rs#PCC <- (OCVcap (OCsealable (OCVmem RX Global b e a_lbl)))) m
      | _        => Crashed (* anything but an unsealed executable capability crashes *)
      end
  end.

(** Auxiliaries for memory accesses *)

Definition eval_offset (ofs: offset) : ptrofs :=
  match ofs with
  | Ofsimm n => n
  | Ofslow id delta => low_half ge id delta
  end.

(* Definition eval_offset_val (rs: regset) (ofs: offset + ireg) (h: bool) : ocval := *)
(*   match ofs with *)
(*   | inl ofs' => if h then (OCVptr (heap_ptr (eval_offset ofs'))) *)
(*                else (OCVptr (stack_ptr (eval_offset ofs'))) *)
(*   | inr r => rs#r *)
(*   end.       *)

(* (* eval_act_kind detects if the givel value is an uninitialized *)
(*   capability. By default the action kind is DIR *) *)
(* Definition eval_act_kind (v: ocval) := *)
(*   match v with *)
(*   | OCVcap c => if isUCap c then UNINIT else DIR *)
(*   | _ => DIR *)
(*   end. *)

Definition zero_offset (h: bool) : ocval :=
  if h then (OCVptr (heap_ptr Ptrofs.zero))
  else (OCVptr (stack_ptr Ptrofs.zero)).

Definition exec_load_capability (chunk: cap_memory_chunk) (rs: regset) (m: mem)
           (d: preg) (a: ireg) (ofs: offset) (cp: compartment) (h priv: bool) :=
  match Val.offset_ptr (rs a) (eval_offset ofs) with
  | Some c => match Mem.loadv DIR chunk m c (zero_offset h)
                             (if priv then None else Some cp) with
             | inr PtrErr => Stuck
             | inr CapErr => Crashed
             | inl v => nextinstr (rs#d <- v) m
             end
  | _ => Stuck
  end.

Definition exec_load_Ucapability (chunk: cap_memory_chunk) (rs: regset) (m: mem)
           (d: preg) (a: ireg) (rofs: ireg) (ofs: offset) (cp: compartment) (h priv: bool) :=
  match Val.sub_offset_ptr (rs rofs) (eval_offset ofs) with
  | Some ofsv => match Mem.loadv UNINIT chunk m (rs a) ofsv
                                (if priv then None else Some cp) with
                | inr PtrErr => Stuck
                | inr CapErr => Crashed
                | inl v => nextinstr (rs#d <- v) m
                end
  | _ => Stuck
  end.

Definition exec_load_ddc (chunk: cap_memory_chunk) (rs: regset) (m: mem)
           (d: preg) (a: ireg) (ofs: offset) (cp: compartment) (priv: bool) :=
  (* calculate offset from a and ofs *)
  match Val.offset_ptr (rs a) (eval_offset ofs) with
  | Some ofsv => match Mem.loadv DEFAULT chunk m (rs DDC) ofsv
                                (if priv then None else Some cp) with
                | inr PtrErr => Stuck
                | inr CapErr => Crashed
                | inl v => nextinstr (rs#d <- v) m
                end
  | None => Stuck
  end.

Definition exec_store_capability (chunk: cap_memory_chunk) (rs: regset) (m: mem)
           (s: preg) (a: ireg) (ofs: offset) (cp: compartment) (h: bool) :=
  match Val.offset_ptr (rs a) (eval_offset ofs) with
  | Some c => match Mem.storev DIR chunk m c (zero_offset h) (rs s) cp with
             | inr PtrErr => Stuck
             | inr CapErr => Crashed
             | inl (_,m') => nextinstr rs m'
             end
  | None => Stuck
  end.

Definition exec_store_Ucapability (chunk: cap_memory_chunk) (rs: regset) (m: mem)
           (s: preg) (a: ireg) (rofs: ireg) (ofs: offset) (cp: compartment) (h: bool) :=
  match Val.sub_offset_ptr (rs rofs) (eval_offset ofs) with
  | Some ofsv => match Mem.storev UNINIT chunk m (rs a) ofsv (rs s) cp with
                | inr PtrErr => Stuck
                | inr CapErr => Crashed
                | inl (c',m') => nextinstr (rs#s <- (OCVcap c')) m'
                end
  | None => Stuck
  end.

Definition exec_store_ddc (chunk: cap_memory_chunk) (rs: regset) (m: mem)
           (s: preg) (a: ireg) (ofs: offset) (cp: compartment) :=
  (* calculate offset from a and ofs *)
  match Val.offset_ptr (rs a) (eval_offset ofs) with
  | Some ofsv => match Mem.storev DEFAULT chunk m (rs DDC) ofsv (rs s) cp with
                | inr PtrErr => Stuck
                | inr CapErr => Crashed
                | inl (_,m') => nextinstr rs m'
                end
  | None => Stuck
  end.

(** Evaluating a branch *)

Definition eval_branch (f: function) (l: label) (rs: regset) (m: mem) (res: option bool) : outcome :=
  match res with
    | Some true  => goto_label f l rs m
    | Some false => nextinstr rs m
    | None => Stuck
  end.

Definition eval_ptr_branch (f: function) (l1 l2: label) (rs: regset) (m: mem) (ptr: ocval) : outcome :=
  match ptr with
  | OCVptr (stack_ptr _) => goto_label f l1 rs m
  | OCVptr (heap_ptr _) => goto_label f l2 rs m
  | _ => nextinstr rs m
  end.

Definition exec_jal (rs: regset) (m: mem) (t: ocval) : outcome :=
  match Val.offset_ptr rs#PCC Ptrofs.one with 
  | Some ret => Next (rs#PCC <- (Val.update_pc_perm t) #RAC <- ret) m
  | _ => Crashed
  end.

Definition exec_jal_seal (rs: regset) (m: mem) (t s: ocval) : outcome :=
  match Val.offset_ptr rs#PCC Ptrofs.one with
  | Some ret => match Val.seal_capability ret s with
               | Some res => Next (rs#PCC <- (Val.update_pc_perm t) #RAC <- res) m
               | _ => Crashed
               end
  | _ => Crashed
  end.

(** Clearing registers *)
Arguments cons & _ _ _.


(* AINA: how to make coercions work within list constructor? *)
Fixpoint list_ip_coercion (l: list ireg) : list preg :=
  match l with
  | a :: l' => a :: list_ip_coercion l'
  | nil => nil
  end.
Fixpoint list_fp_coercion (l: list freg) : list preg :=
  match l with
  | a :: l' => a :: list_fp_coercion l'
  | nil => nil
  end.

(* AINA: the following is a bit hardcoded.. see if there is a better way of doing it *)
Definition int_regs : list ireg :=
  X1::X2::X3::X4::X5::X6::X7::X8::X9::X10::X11::X12::X13::X14::X15::X16::X17::X18::X19::
  X20::X21::X22::X23::X24::X25::X26::X27::X28::X29::X30::X31::nil.
Definition float_regs : list freg :=
  F0::F1::F2::F3::F4::F5::F6::F7::F8::F9::F10::F11::F12::F13::F14::F15::F16::F17::F18::F19::
  F20::F21::F22::F23::F24::F25::F26::F27::F28::F29::F30::F31::nil.

Fixpoint filter_index {A: Type} (l: list A) (idx: list nat) : list A :=
  match idx with
  | nil => nil
  | i :: idx' => match nth_error l i with
               | Some a => a :: filter_index l idx'
               | None => filter_index l idx'
               end
  end.

Definition clear_registers (rs: regset) (vec: int) (is_int: bool) : regset :=
  if is_int
  then (* we shift vec in case of iregs to skip X0 *)
    let idx := List.map Z.to_nat (Zbits.Z_one_bits Int.wordsize (Int.unsigned vec / 2) 0) in
    let regs := list_ip_coercion (filter_index int_regs idx) in
    set_regs_default regs (OCVint Int.zero) rs
  else
    let idx := List.map Z.to_nat (Zbits.Z_one_bits Int.wordsize (Int.unsigned vec) 0) in
    let regs := list_fp_coercion (filter_index float_regs idx) in
    set_regs_default regs (OCVint Int.zero) rs.

(** Auxiliary definition that interprets partial operations into outcomes *)

Definition exec_capability_outcome {A: Type} (v: option A) (rso: A -> outcome) : outcome :=
  match v with
  | Some res => rso res
  | None => Crashed
  end.

Definition ptrofs_heap_res (ofs: ptrofs) : ocval :=
  OCVptr (heap_ptr ofs).
Definition ptrofs_stack_res (ofs: ptrofs) : ocval :=
  OCVptr (stack_ptr ofs).

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

Definition exec_instr (f: function) (i: instruction) (rs: regset) (m: mem) (cp: compartment) : outcome :=
  match i with
  | Pmv d s =>
      nextinstr (rs#d <- (rs#s)) m

(** 32-bit integer register-immediate instructions *)
  | Paddiw d s i =>
      nextinstr (rs#d <- (Val.add rs##s (OCVint i))) m
  | Psltiw d s i =>
      nextinstr (rs#d <- (Val.cmp Clt rs##s (OCVint i))) m
  (* | Psltiuw d s i => (* ALG: ?? -- uses memory model *) *)
  (*     nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs##s (OCVint i))) m *)
  | Pandiw d s i =>
      nextinstr (rs#d <- (Val.and rs##s (OCVint i))) m
  | Poriw d s i =>
      nextinstr (rs#d <- (Val.or rs##s (OCVint i))) m
  | Pxoriw d s i =>
      nextinstr (rs#d <- (Val.xor rs##s (OCVint i))) m
  | Pslliw d s i =>
      nextinstr (rs#d <- (Val.shl rs##s (OCVint i))) m
  | Psrliw d s i =>
      nextinstr (rs#d <- (Val.shru rs##s (OCVint i))) m
  | Psraiw d s i =>
      nextinstr (rs#d <- (Val.shr rs##s (OCVint i))) m
  | Pluiw d i =>
      nextinstr (rs#d <- (OCVint (Int.shl i (Int.repr 12)))) m

(** 32-bit integer register-register instructions *)
  | Paddw d s1 s2 =>
       (nextinstr (rs#d <- (Val.add rs##s1 rs##s2))) m
  | Psubw d s1 s2 =>
       (nextinstr (rs#d <- (Val.sub rs##s1 rs##s2))) m
  | Pmulw d s1 s2 =>
       (nextinstr (rs#d <- (Val.mul rs##s1 rs##s2))) m
  | Pmulhw d s1 s2 =>
       (nextinstr (rs#d <- (Val.mulhs rs##s1 rs##s2))) m
  | Pmulhuw d s1 s2 =>
       (nextinstr (rs#d <- (Val.mulhu rs##s1 rs##s2))) m
  | Pdivw d s1 s2 =>
       (nextinstr (rs#d <- (Val.maketotal (Val.divs rs##s1 rs##s2)))) m
  | Pdivuw d s1 s2 =>
       (nextinstr (rs#d <- (Val.maketotal (Val.divu rs##s1 rs##s2)))) m
  | Premw d s1 s2 =>
       (nextinstr (rs#d <- (Val.maketotal (Val.mods rs##s1 rs##s2)))) m
  | Premuw d s1 s2 =>
       (nextinstr (rs#d <- (Val.maketotal (Val.modu rs##s1 rs##s2)))) m
  | Psltw d s1 s2 =>
       (nextinstr (rs#d <- (Val.cmp Clt rs##s1 rs##s2))) m
  (* | Psltuw d s1 s2 => *)
  (*      (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Clt rs##s1 rs##s2))) m *)
  (* | Pseqw d s1 s2 => *)
  (*      (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Ceq rs##s1 rs##s2))) m *)
  (* | Psnew d s1 s2 => *)
  (*      (nextinstr (rs#d <- (Val.cmpu (Mem.valid_pointer m) Cne rs##s1 rs##s2))) m *)
  | Pandw d s1 s2 =>
       (nextinstr (rs#d <- (Val.and rs##s1 rs##s2))) m
  | Porw d s1 s2 =>
       (nextinstr (rs#d <- (Val.or rs##s1 rs##s2))) m
  | Pxorw d s1 s2 =>
       (nextinstr (rs#d <- (Val.xor rs##s1 rs##s2))) m
  | Psllw d s1 s2 =>
       (nextinstr (rs#d <- (Val.shl rs##s1 rs##s2))) m
  | Psrlw d s1 s2 =>
       (nextinstr (rs#d <- (Val.shru rs##s1 rs##s2))) m
  | Psraw d s1 s2 =>
       (nextinstr (rs#d <- (Val.shr rs##s1 rs##s2))) m

(** 64-bit integer register-immediate instructions *)
  | Paddil d s i =>
       (nextinstr (rs#d <- (Val.addl rs###s (OCVlong i)))) m
  | Psltil d s i =>
       (nextinstr (rs#d <- (Val.maketotal (Val.cmpl Clt rs###s (OCVlong i))))) m
  (* | Psltiul d s i => *)
  (*      (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt rs###s (OCVlong i))))) m *)
  | Pandil d s i =>
       (nextinstr (rs#d <- (Val.andl rs###s (OCVlong i)))) m
  | Poril d s i =>
       (nextinstr (rs#d <- (Val.orl rs###s (OCVlong i)))) m
  | Pxoril d s i =>
       (nextinstr (rs#d <- (Val.xorl rs###s (OCVlong i)))) m
  | Psllil d s i =>
       (nextinstr (rs#d <- (Val.shll rs###s (OCVint i)))) m
  | Psrlil d s i =>
       (nextinstr (rs#d <- (Val.shrlu rs###s (OCVint i)))) m
  | Psrail d s i =>
       (nextinstr (rs#d <- (Val.shrl rs###s (OCVint i)))) m
  | Pluil d i =>
       (nextinstr (rs#d <- (OCVlong (Int64.sign_ext 32 (Int64.shl i (Int64.repr 12)))))) m

(** 64-bit integer register-register instructions *)
  | Paddl d s1 s2 =>
       (nextinstr (rs#d <- (Val.addl rs###s1 rs###s2))) m
  | Psubl d s1 s2 =>
       (nextinstr (rs#d <- (Val.subl rs###s1 rs###s2))) m
  | Pmull d s1 s2 =>
       (nextinstr (rs#d <- (Val.mull rs###s1 rs###s2))) m
  | Pmulhl d s1 s2 =>
       (nextinstr (rs#d <- (Val.mullhs rs###s1 rs###s2))) m
  | Pmulhul d s1 s2 =>
       (nextinstr (rs#d <- (Val.mullhu rs###s1 rs###s2))) m
  | Pdivl d s1 s2 =>
       (nextinstr (rs#d <- (Val.maketotal (Val.divls rs###s1 rs###s2)))) m
  | Pdivul d s1 s2 =>
       (nextinstr (rs#d <- (Val.maketotal (Val.divlu rs###s1 rs###s2)))) m
  | Preml d s1 s2 =>
       (nextinstr (rs#d <- (Val.maketotal (Val.modls rs###s1 rs###s2)))) m
  | Premul d s1 s2 =>
       (nextinstr (rs#d <- (Val.maketotal (Val.modlu rs###s1 rs###s2)))) m
  | Psltl d s1 s2 =>
       (nextinstr (rs#d <- (Val.maketotal (Val.cmpl Clt rs###s1 rs###s2)))) m
  (* | Psltul d s1 s2 => *)
  (*      (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Clt rs###s1 rs###s2)))) m *)
  (* | Pseql d s1 s2 => *)
  (*      (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Ceq rs###s1 rs###s2)))) m *)
  (* | Psnel d s1 s2 => *)
  (*      (nextinstr (rs#d <- (Val.maketotal (Val.cmplu (Mem.valid_pointer m) Cne rs###s1 rs###s2)))) m *)
  | Pandl d s1 s2 =>
       (nextinstr (rs#d <- (Val.andl rs###s1 rs###s2))) m
  | Porl d s1 s2 =>
       (nextinstr (rs#d <- (Val.orl rs###s1 rs###s2))) m
  | Pxorl d s1 s2 =>
       (nextinstr (rs#d <- (Val.xorl rs###s1 rs###s2))) m
  | Pslll d s1 s2 =>
       (nextinstr (rs#d <- (Val.shll rs###s1 rs###s2))) m
  | Psrll d s1 s2 =>
       (nextinstr (rs#d <- (Val.shrlu rs###s1 rs###s2))) m
  | Psral d s1 s2 =>
       (nextinstr (rs#d <- (Val.shrl rs###s1 rs###s2))) m

  | Pcvtl2w d s =>
       (nextinstr (rs#d <- (Val.loword rs##s))) m
  | Pcvtw2l r =>
       (nextinstr (rs#r <- (Val.longofint rs#r))) m

(** Unconditional jumps.  Links are always to X1/RA. *)
  | Pj_l l =>
      goto_label f l rs m
  (* | Pj_s s sg => *)
  (*    Next (rs#PCC <- (update_pc_perm (Genv.symbol_address ge s Ptrofs.zero))) m *)
  | Pj_r r =>
      Next (rs#PCC <- (Val.update_pc_perm (rs#r))) m
  (* | Pjal_s s sg _ => *)
  (*     exec_jal rs m (Genv.symbol_address ge s Ptrofs.zero) *)
  | Pjal_r r sg _ =>
      exec_jal rs m (rs#r)
  | PCjal_r r s _ _ =>
      exec_jal_seal rs m (rs#r) (rs#s)
  (* | PCjal_s f s _ _ => *)
  (*     exec_jal_seal rs m (Genv.symbol_address ge f Ptrofs.zero) (rs#s) *)

(** Sealed capability invocation *)
  (* FIXME unseal_capability_paor undefined *)
  (* | PCinvoke r s _ => *)
  (*     exec_capability_outcome (Val.unseal_capability_pair (rs##r) (rs##s)) *)
  (*                             (fun c => Next (rs#PCC <- (fst c) #EC <- (snd c)) m) *)
      
(** Conditional branches, 32-bit comparisons *)
  (* | Pbeqw s1 s2 l => *)
  (*     eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Ceq rs##s1 rs##s2) *)
  (* | Pbnew s1 s2 l => *)
  (*     eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Cne rs##s1 rs##s2) *)
  | Pbltw s1 s2 l =>
      eval_branch f l rs m (Val.cmp_bool Clt rs##s1 rs##s2)
  (* | Pbltuw s1 s2 l => *)
  (*     eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Clt rs##s1 rs##s2) *)
  | Pbgew s1 s2 l =>
      eval_branch f l rs m (Val.cmp_bool Cge rs##s1 rs##s2)
  (* | Pbgeuw s1 s2 l => *)
  (*     eval_branch f l rs m (Val.cmpu_bool (Mem.valid_pointer m) Cge rs##s1 rs##s2) *)

(** Conditional branches, 64-bit comparisons *)
  (* | Pbeql s1 s2 l => *)
  (*     eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Ceq rs###s1 rs###s2) *)
  (* | Pbnel s1 s2 l => *)
  (*     eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Cne rs###s1 rs###s2) *)
  | Pbltl s1 s2 l =>
      eval_branch f l rs m (Val.cmpl_bool Clt rs###s1 rs###s2)
  (* | Pbltul s1 s2 l => *)
  (*     eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Clt rs###s1 rs###s2) *)
  | Pbgel s1 s2 l =>
      eval_branch f l rs m (Val.cmpl_bool Cge rs###s1 rs###s2)
  (* | Pbgeul s1 s2 l => *)
  (*     eval_branch f l rs m (Val.cmplu_bool (Mem.valid_pointer m) Cge rs###s1 rs###s2) *)

(** Loads and stores *)
  | Plb d a ofs priv =>
      exec_load_ddc CMint8signed rs m d a ofs cp priv
  | Plbu d a ofs priv =>
      exec_load_ddc CMint8unsigned rs m d a ofs cp priv
  | Plh d a ofs priv =>
      exec_load_ddc CMint16signed rs m d a ofs cp priv
  | Plhu d a ofs priv =>
      exec_load_ddc CMint16unsigned rs m d a ofs cp priv
  | Plw d a ofs priv =>
      exec_load_ddc CMint32 rs m d a ofs cp priv
  | Plw_a d a ofs priv =>
      exec_load_ddc CMany32 rs m d a ofs cp priv
  | Pld d a ofs priv =>
      exec_load_ddc CMint64 rs m d a ofs cp priv
  | Pld_a d a ofs priv =>
      exec_load_ddc CMany64 rs m d a ofs cp priv
  | Plcw d a ofs priv =>
      exec_load_ddc CMcap64 rs m d a ofs cp priv
  | Plcd d a ofs priv =>
      exec_load_ddc CMcap128 rs m d a ofs cp priv
  | Plcd_a d a ofs priv =>
      exec_load_ddc CMany128 rs m d a ofs cp priv
  
  | Psb s a ofs =>
      exec_store_ddc CMint8unsigned rs m s a ofs cp
  | Psh s a ofs =>
      exec_store_ddc CMint16unsigned rs m s a ofs cp
  | Psw s a ofs =>
      exec_store_ddc CMint32 rs m s a ofs cp
  | Psw_a s a ofs =>
      exec_store_ddc CMany32 rs m s a ofs cp
  | Psd s a ofs =>
      exec_store_ddc CMint64 rs m s a ofs cp
  | Psd_a s a ofs =>
      exec_store_ddc CMany64 rs m s a ofs cp
  | Pscw s a ofs =>
      exec_store_ddc CMcap64 rs m s a ofs cp
  | Pscd s a ofs =>
      exec_store_ddc CMcap128 rs m s a ofs cp
  | Pscd_a s a ofs =>
      exec_store_ddc CMany128 rs m s a ofs cp

(** Capability loads and stores *)
  | PClb d a ofs h priv =>
      exec_load_capability CMint8signed rs m d a ofs cp h priv
  | PClbu d a ofs h priv =>
      exec_load_capability CMint8unsigned rs m d a ofs cp h priv
  | PClh d a ofs h priv =>
      exec_load_capability CMint16signed rs m d a ofs cp h priv
  | PClhu d a ofs h priv =>
      exec_load_capability CMint16unsigned rs m d a ofs cp h priv
  | PClw d a ofs h priv =>
      exec_load_capability CMint32 rs m d a ofs cp h priv
  | PClw_a d a ofs h priv =>
      exec_load_capability CMany32 rs m d a ofs cp h priv
  | PCld d a ofs h priv =>
      exec_load_capability CMint64 rs m d a ofs cp h priv
  | PCld_a d a ofs h priv =>
      exec_load_capability CMany64 rs m d a ofs cp h priv
  | PClwc d a ofs h priv =>
      exec_load_capability CMcap64 rs m d a ofs cp h priv
  | PClcd d a ofs h priv =>
      exec_load_capability CMcap128 rs m d a ofs cp h priv
  | PClcd_a d a ofs h priv =>
      exec_load_capability CMany128 rs m d a ofs cp h priv
            
  | PCsb s a ofs h =>
      exec_store_capability CMint8unsigned rs m s a ofs cp h
  | PCsh s a ofs h =>
      exec_store_capability CMint16unsigned rs m s a ofs cp h
  | PCsw s a ofs h =>
      exec_store_capability CMint32 rs m s a ofs cp h
  | PCsw_a s a ofs h =>
      exec_store_capability CMany32 rs m s a ofs cp h
  | PCsd s a ofs h =>
      exec_store_capability CMint64 rs m s a ofs cp h
  | PCsd_a s a ofs h =>
      exec_store_capability CMany64 rs m s a ofs cp h
  | PCscw s a ofs h =>
      exec_store_capability CMcap64 rs m s a ofs cp h
  | PCscd s a ofs h =>
      exec_store_capability CMcap128 rs m s a ofs cp h
  | PCscd_a s a ofs h =>
      exec_store_capability CMany128 rs m s a ofs cp h

  | PCfls d a ofs h priv =>
      exec_load_capability CMfloat32 rs m d a ofs cp h priv
  | PCfss s a ofs h =>
      exec_store_capability CMfloat32 rs m s a ofs cp h
  | PCfld d a ofs h priv =>
      exec_load_capability CMfloat64 rs m d a ofs cp h priv
  | PCfld_a d a ofs h priv =>
      exec_load_capability CMany64 rs m d a ofs cp h priv
  | PCfsd s a ofs h =>
      exec_store_capability CMfloat64 rs m s a ofs cp h
  | PCfsd_a s a ofs h =>
      exec_store_capability CMany64 rs m s a ofs cp h
                            
  (** Uninitialized Capability loads and stores *)
  | PCUlb d a rofs ofs h priv =>
      exec_load_Ucapability CMint8signed rs m d a rofs ofs cp h priv
  | PCUlbu d a rofs ofs h priv =>
      exec_load_Ucapability CMint8unsigned rs m d a rofs ofs cp h priv
  | PCUlh d a rofs ofs h priv =>
      exec_load_Ucapability CMint16signed rs m d a rofs ofs cp h priv
  | PCUlhu d a rofs ofs h priv =>
      exec_load_Ucapability CMint16unsigned rs m d a rofs ofs cp h priv
  | PCUlw d a rofs ofs h priv =>
      exec_load_Ucapability CMint32 rs m d a rofs ofs cp h priv
  | PCUlw_a d a rofs ofs h priv =>
      exec_load_Ucapability CMany32 rs m d a rofs ofs cp h priv
  | PCUld d a rofs ofs h priv =>
      exec_load_Ucapability CMint64 rs m d a rofs ofs cp h priv
  | PCUld_a d a rofs ofs h priv =>
      exec_load_Ucapability CMany64 rs m d a rofs ofs cp h priv
  | PCUlwc d a rofs ofs h priv =>
      exec_load_Ucapability CMcap64 rs m d a rofs ofs cp h priv
  | PCUlcd d a rofs ofs h priv =>
      exec_load_Ucapability CMcap128 rs m d a rofs ofs cp h priv
  | PCUlcd_a d a rofs ofs h priv =>
      exec_load_Ucapability CMany128 rs m d a rofs ofs cp h priv
            
  | PCUsb s a rofs ofs h =>
      exec_store_Ucapability CMint8unsigned rs m s a rofs ofs cp h
  | PCUsh s a rofs ofs h =>
      exec_store_Ucapability CMint16unsigned rs m s a rofs ofs cp h
  | PCUsw s a rofs ofs h =>
      exec_store_Ucapability CMint32 rs m s a rofs ofs cp h
  | PCUsw_a s a rofs ofs h =>
      exec_store_Ucapability CMany32 rs m s a rofs ofs cp h
  | PCUsd s a rofs ofs h =>
      exec_store_Ucapability CMint64 rs m s a rofs ofs cp h
  | PCUsd_a s a rofs ofs h =>
      exec_store_Ucapability CMany64 rs m s a rofs ofs cp h
  | PCUscw s a rofs ofs h =>
      exec_store_Ucapability CMcap64 rs m s a rofs ofs cp h
  | PCUscd s a rofs ofs h =>
      exec_store_Ucapability CMcap128 rs m s a rofs ofs cp h
  | PCUscd_a s a rofs ofs h =>
      exec_store_Ucapability CMany128 rs m s a rofs ofs cp h

  | PCUfls d a rofs ofs h priv =>
      exec_load_Ucapability CMfloat32 rs m d a rofs ofs cp h priv
  | PCUfss s a rofs ofs h =>
      exec_store_Ucapability CMfloat32 rs m s a rofs ofs cp h
  | PCUfld d a rofs ofs h priv =>
      exec_load_Ucapability CMfloat64 rs m d a rofs ofs cp h priv
  | PCUfld_a d a rofs ofs h priv =>
      exec_load_Ucapability CMany64 rs m d a rofs ofs cp h priv
  | PCUfsd s a rofs ofs h =>
      exec_store_Ucapability CMfloat64 rs m s a rofs ofs cp h
  | PCUfsd_a s a rofs ofs h =>
      exec_store_Ucapability CMany64 rs m s a rofs ofs cp h
                             
(** Capability inspection *)
  (* FIXME get_cap undefined *)
  (* | PCgp d s => *)
  (*     Next (rs#d <- (Val.maketotal (do X <- get_cap rs#s >>= get_perm; Some (encode_perm X)))) m *)
  (* | PCgt d s => *)
  (*     Next (rs#d <- (Val.maketotal (do X <- get_cap rs#s >>= get_otype; Some (OCVint (Ptrofs.to_int X))))) m *)
  (* | PCgb_h d s => *)
  (*     Next (rs#d <- (Val.maketotal (do X <- get_cap rs#s; Some (ptrofs_heap_res (get_lo X))))) m *)
  (* | PCge_h d s => *)
  (*     Next (rs#d <- (Val.maketotal (do X <- get_cap rs#s; Some (ptrofs_heap_res (get_hi X))))) m *)
  (* | PCgb_s d s => *)
  (*     Next (rs#d <- (Val.maketotal (do X <- get_cap rs#s; Some (ptrofs_stack_res (get_lo X))))) m *)
  (* | PCge_s d s => *)
  (*     Next (rs#d <- (Val.maketotal (do X <- get_cap rs#s; Some (ptrofs_stack_res (get_hi X))))) m *)
  | PCgg d s =>
      Next (rs#d <- (OCVint (Int.repr (Z.b2z (is_cap_b rs#s))))) m
  (* FIXME is_sealed_cap undefined *)
  (* | PCgs d s => *)
  (*     Next (rs#d <- (OCVint (Int.repr (Z.b2z (is_sealed_cap rs#s))))) m *)
  (* | PCga_h d s => *)
  (*     Next (rs#d <- (Val.maketotal (do X <- get_cap rs#s; Some (ptrofs_heap_res (get_addr X))))) m *)
  (* | PCga_s d s => *)
  (*     Next (rs#d <- (Val.maketotal (do X <- get_cap rs#s; Some (ptrofs_stack_res (get_addr X))))) m *)
  (* | PCgl_h d s => *)
  (*     Next (rs#d <- (Val.maketotal (do X <- get_cap rs#s; Some (ptrofs_heap_res (get_region_size_ptrofs X))))) m *)
  (* | PCgl_s d s => *)
  (*     Next (rs#d <- (Val.maketotal (do X <- get_cap rs#s; Some (ptrofs_stack_res (get_region_size_ptrofs X))))) m *)

(** Capability modification *)
  | PCseal d r1 r2 =>
      exec_capability_outcome (Val.seal_capability rs#r1 rs#r2) (fun b => Next (rs#d <- b) m)
  | PCunseal d r1 r2 =>
      exec_capability_outcome (Val.unseal_capability rs#r1 rs#r2) (fun b => Next (rs#d <- b) m)
  (* FIXME decode_permit_int undefined *)
  (* | PCpermand d r1 r2 => *)
  (*     exec_capability_outcome (Val.restrict_perm decode_perm_int rs#r1 rs#r2) (fun b => Next (rs#d <- b) m) *)
  | PCsaddr_w d r1 r2 =>
      exec_capability_outcome (Val.set_address rs#r1 rs#r2) (fun b => Next (rs#d <- b) m)
  | PCsaddr_l d r1 r2 =>
      exec_capability_outcome (Val.set_addressl rs#r1 rs#r2) (fun b => Next (rs#d <- b) m)
  | PCiaddr_w d r1 r2 =>
      exec_capability_outcome (Val.incr_address rs##r1 rs##r2) (fun b => Next (rs#d <- b) m)
  | PCiaddr_l d r1 r2 =>
      exec_capability_outcome (Val.incr_addressl rs##r1 rs##r2) (fun b => Next (rs#d <- b) m)
  | PCiaddr_il d r1 imm =>
      exec_capability_outcome (Val.incr_addressl rs##r1 (OCVlong imm)) (fun b => Next (rs#d <- b) m)
  | PCiaddr_iw d r1 imm =>
      exec_capability_outcome (Val.incr_address rs##r1 (OCVint imm)) (fun b => Next (rs#d <- b) m)
  (* FIXME sub_bounds undefined *)
  (* | PCsbase d r1 r2 => *)
  (*     exec_capability_outcome (Val.sub_bounds rs#r1 rs#r2) (fun b => Next (rs#d <- b) m) *)
  (* | PCsbase_il d r1 imm => *)
  (*     exec_capability_outcome (Val.sub_bounds rs#r1 (OCVlong imm)) (fun b => Next (rs#d <- b) m) *)
  (* | PCsbase_iw d r1 imm => *)
  (*     exec_capability_outcome (Val.sub_bounds rs#r1 (OCVint imm)) (fun b => Next (rs#d <- b) m) *)
  (* | PCcleart _ _ *) (* removed for now => needs some kind of
  enconding from capabilities to integers, however issues with space:
  the encoding has to go from a capability to two integers/two
  longs *)
  (* FIXME conditional_seal_capability undefined *)
  (* | PCCseal d r1 r2 => *)
  (*     exec_capability_outcome (Val.conditional_seal_capability rs#r1 rs#r2) (fun b => Next (rs#d <- b) m) *)
  (* | PCseal_e d r => *)
  (*     exec_capability_outcome (Val.restrict_perm decode_perm_int rs#r (OCVint (encode_perm_int E))) *)
  (*                             (fun b => Next (rs#d <- b) m) *)
  (* FIXME promote undefined  *)
  (* | PCpromote d r1 => *)
  (*     exec_capability_outcome (Val.promote rs#r1) (fun b => Next (rs#d <- b) m) *)
                              
(** Capability arithmetic *)
  (* FIXME c_to_ptr_heap undefined *)
  (* | PCtoPtr_h d r1 r2 => *)
  (*     exec_capability_outcome (Val.c_to_ptr_heap rs#r1 rs#r2) (fun b => Next (rs#d <- b) m) *)
  (* FIXME capability_sub_heap undefined *)
  (* | PCsub_h d r1 r2 => *)
  (*     Next (rs#d <- (Val.capability_sub_heap rs#r1 rs#r2)) m *)
  (* FIXME c_to_ptr_stack undefined *)
  (* | PCtoPtr_s d r1 r2 => *)
  (*     exec_capability_outcome (Val.c_to_ptr_stack rs#r1 rs#r2) (fun b => Next (rs#d <- b) m) *)
  (* FIXME capability_sub_stack undefined *)
  (* | PCsub_s d r1 r2 => *)
  (*     Next (rs#d <- (Val.capability_sub_stack rs#r1 rs#r2)) m *)
  (* FIXME c_to_Uptr_heap undefined *)
  (* | PCUtoPtr_h d r1 r2 => *)
  (*     exec_capability_outcome (Val.c_to_Uptr_heap rs#r1 rs#r2) (fun b => Next (rs#d <- b) m) *)
  (* | PCUtoPtr_s d r1 r2 =>  *)
  (*     exec_capability_outcome (Val.c_to_Uptr_heap rs#r1 rs#r2) (fun b => Next (rs#d <- b) m) *)
                              
(** Capability comparisons *)
  (* | PCsubset d r1 r2 => *)
  (*     Next (rs#d <- (Val.maketotal (do X1 <- get_cap rs#r1; *)
  (*                                  do X2 <- get_cap rs#r2; *)
  (*                   Some (OCVint (Int.repr (Z.b2z (Mem.derived_cap_dec X1 X2))))))) m *)
  (* | PCeex d r1 r2 => *)
  (*     Next (rs#d <- (Val.maketotal (do X1 <- get_cap rs#r1; *)
  (*                                  do X2 <- get_cap rs#r2; *)
  (*                   Some (OCVint (Int.repr (Z.b2z (occap_dec X1 X2))))))) m *)

(** Fast clearing *)
  | PCCclear imm => Next (clear_registers rs imm true) m
  | PCCclearf imm => Next (clear_registers rs imm false) m

              
(** Floating point register move *)
  | Pfmv d s =>
      (nextinstr (rs#d <- (rs#s))) m

(** 32-bit (single-precision) floating point *)
  | Pfls d a ofs b =>
      exec_load_ddc CMfloat32 rs m d a ofs cp b
  | Pfss s a ofs =>
      exec_store_ddc CMfloat32 rs m s a ofs cp

  | Pfnegs d s =>
      (nextinstr (rs#d <- (Val.negfs rs#s))) m
  | Pfabss d s =>
      (nextinstr (rs#d <- (Val.absfs rs#s))) m

  | Pfadds d s1 s2 =>
       (nextinstr (rs#d <- (Val.addfs rs#s1 rs#s2))) m
  | Pfsubs d s1 s2 =>
       (nextinstr (rs#d <- (Val.subfs rs#s1 rs#s2))) m
  | Pfmuls d s1 s2 =>
       (nextinstr (rs#d <- (Val.mulfs rs#s1 rs#s2))) m
  | Pfdivs d s1 s2 =>
       (nextinstr (rs#d <- (Val.divfs rs#s1 rs#s2))) m
  | Pfeqs d s1 s2 =>
       (nextinstr (rs#d <- (Val.cmpfs Ceq rs#s1 rs#s2))) m
  | Pflts d s1 s2 =>
       (nextinstr (rs#d <- (Val.cmpfs Clt rs#s1 rs#s2))) m
  | Pfles d s1 s2 =>
       (nextinstr (rs#d <- (Val.cmpfs Cle rs#s1 rs#s2))) m

  | Pfcvtws d s =>
       (nextinstr (rs#d <- (Val.maketotal (Val.intofsingle rs#s)))) m
  | Pfcvtwus d s =>
       (nextinstr (rs#d <- (Val.maketotal (Val.intuofsingle rs#s)))) m
  | Pfcvtsw d s =>
       (nextinstr (rs#d <- (Val.maketotal (Val.singleofint rs##s)))) m
  | Pfcvtswu d s =>
       (nextinstr (rs#d <- (Val.maketotal (Val.singleofintu rs##s)))) m

  | Pfcvtls d s =>
       (nextinstr (rs#d <- (Val.maketotal (Val.longofsingle rs#s)))) m
  | Pfcvtlus d s =>
       (nextinstr (rs#d <- (Val.maketotal (Val.longuofsingle rs#s)))) m
  | Pfcvtsl d s =>
       (nextinstr (rs#d <- (Val.maketotal (Val.singleoflong rs###s)))) m
  | Pfcvtslu d s =>
       (nextinstr (rs#d <- (Val.maketotal (Val.singleoflongu rs###s)))) m

(** 64-bit (double-precision) floating point *)
  | Pfld d a ofs b =>
      exec_load_ddc CMfloat64 rs m d a ofs cp b
  | Pfld_a d a ofs b =>
      exec_load_ddc CMany64 rs m d a ofs cp b
  | Pfsd s a ofs =>
      exec_store_ddc CMfloat64 rs m s a ofs cp
  | Pfsd_a s a ofs =>
      exec_store_ddc CMany64 rs m s a ofs cp

  | Pfnegd d s =>
       (nextinstr (rs#d <- (Val.negf rs#s))) m
  | Pfabsd d s =>
       (nextinstr (rs#d <- (Val.absf rs#s))) m

  | Pfaddd d s1 s2 =>
       (nextinstr (rs#d <- (Val.addf rs#s1 rs#s2))) m
  | Pfsubd d s1 s2 =>
       (nextinstr (rs#d <- (Val.subf rs#s1 rs#s2))) m
  | Pfmuld d s1 s2 =>
       (nextinstr (rs#d <- (Val.mulf rs#s1 rs#s2))) m
  | Pfdivd d s1 s2 =>
       (nextinstr (rs#d <- (Val.divf rs#s1 rs#s2))) m
  | Pfeqd d s1 s2 =>
       (nextinstr (rs#d <- (Val.cmpf Ceq rs#s1 rs#s2))) m
  | Pfltd d s1 s2 =>
       (nextinstr (rs#d <- (Val.cmpf Clt rs#s1 rs#s2))) m
  | Pfled d s1 s2 =>
       (nextinstr (rs#d <- (Val.cmpf Cle rs#s1 rs#s2))) m

  | Pfcvtwd d s =>
       (nextinstr (rs#d <- (Val.maketotal (Val.intoffloat rs#s)))) m
  | Pfcvtwud d s =>
       (nextinstr (rs#d <- (Val.maketotal (Val.intuoffloat rs#s)))) m
  | Pfcvtdw d s =>
       (nextinstr (rs#d <- (Val.maketotal (Val.floatofint rs##s)))) m
  | Pfcvtdwu d s =>
       (nextinstr (rs#d <- (Val.maketotal (Val.floatofintu rs##s)))) m

  | Pfcvtld d s =>
       (nextinstr (rs#d <- (Val.maketotal (Val.longoffloat rs#s)))) m
  | Pfcvtlud d s =>
       (nextinstr (rs#d <- (Val.maketotal (Val.longuoffloat rs#s)))) m
  | Pfcvtdl d s =>
       (nextinstr (rs#d <- (Val.maketotal (Val.floatoflong rs###s)))) m
  | Pfcvtdlu d s =>
       (nextinstr (rs#d <- (Val.maketotal (Val.floatoflongu rs###s)))) m

  | Pfcvtds d s =>
       (nextinstr (rs#d <- (Val.floatofsingle rs#s))) m
  | Pfcvtsd d s =>
       (nextinstr (rs#d <- (Val.singleoffloat rs#s))) m

(** Pseudo-instructions *)
  (* | Pallocframe sz pos => *)
  (*     let (m1, stk) := Mem.alloc m (comp_of f) 0 sz in *)
  (*     let sp := (Vptr stk Ptrofs.zero) in *)
  (*     match Mem.storev Mptr m1 (Val.offset_ptr sp pos) rs#SP cp with *)
  (*     | None => Stuck *)
  (*     | Some m2 => Next (nextinstr (rs #X30 <- (rs SP) #SP <- sp #X31 <- Vundef)) m2 *)
  (*     end *)
  (* | Pfreeframe sz pos => *)
  (*     match Mem.loadv Mptr m (Val.offset_ptr rs#SP pos) (Some cp) with *)
  (*     | None => Stuck *)
  (*     | Some v => *)
  (*         match rs SP with *)
  (*         | Vptr stk ofs => *)
  (*             match Mem.free m stk 0 sz cp with *)
  (*             | None => Stuck *)
  (*             | Some m' => Next (nextinstr (rs#SP <- v #X31 <- Vundef)) m' *)
  (*             end *)
  (*         | _ => Stuck *)
  (*         end *)
  (*     end *)
  | Plabel lbl =>
      (nextinstr rs) m
  | Pptrbr r lbl1 lbl2 =>
      eval_ptr_branch f lbl1 lbl2 rs m (rs##r)
  (* | Ploadsymbol rd s ofs => *)
  (*      (nextinstr (rs#rd <- (Genv.symbol_address ge s ofs))) m *)
  (* | Ploadsymbol_high rd s ofs => *)
  (*      (nextinstr (rs#rd <- (high_half ge s ofs))) m *)
  | Ploadli rd i =>
       (nextinstr (rs#X31 <- OCVundef #rd <- (OCVlong i))) m
  | Ploadfi rd f =>
       (nextinstr (rs#X31 <- OCVundef #rd <- (OCVfloat f))) m
  | Ploadsi rd f =>
       (nextinstr (rs#X31 <- OCVundef #rd <- (OCVsingle f))) m
  | Pbtbl r tbl =>
      match rs r with
      | OCVint n =>
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label f lbl (rs#X5 <- OCVundef #X31 <- OCVundef) m
          end
      | _ => Stuck
      end
  | Pbuiltin ef args res =>
      Stuck (**r treated specially below *)
  | Pfail => Crashed

  (** The following instructions and directives are not generated directly by Asmgen,
      so we do not model them. *)
  | PCloadtag _ _ (* TODO /!\  -- needed by Asmgen *)
  | Pfence

  | Pfmvxs _ _
  | Pfmvxd _ _

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
  | _ => Stuck (* FIXME commented out operations *)
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
  the RISC-V view.  Note that no LTL register maps to [X31 X32].  This
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

  | CapMachregs.F0  => F0  | CapMachregs.F1  => F1  | CapMachregs.F2  => F2  | CapMachregs.F3  => F3
  | CapMachregs.F4  => F4  | CapMachregs.F5  => F5  | CapMachregs.F6  => F6  | CapMachregs.F7  => F7
  | CapMachregs.F8  => F8  | CapMachregs.F9  => F9  | CapMachregs.F10 => F10 | CapMachregs.F11 => F11
  | CapMachregs.F12 => F12 | CapMachregs.F13 => F13 | CapMachregs.F14 => F14 | CapMachregs.F15 => F15
  | CapMachregs.F16 => F16 | CapMachregs.F17 => F17 | CapMachregs.F18 => F18 | CapMachregs.F19 => F19
  | CapMachregs.F20 => F20 | CapMachregs.F21 => F21 | CapMachregs.F22 => F22 | CapMachregs.F23 => F23
  | CapMachregs.F24 => F24 | CapMachregs.F25 => F25 | CapMachregs.F26 => F26 | CapMachregs.F27 => F27
  | CapMachregs.F28 => F28 | CapMachregs.F29 => F29 | CapMachregs.F30 => F30 | CapMachregs.F31 => F31
  end.

(** Undefine all registers except SP and callee-save registers *)

(* FIXME should be part of CapConventions *)
Definition is_callee_save (* (is_cross_compartment: bool) *) (r: mreg) : bool := (* false *)
  (* is_cross_compartment || *)
  match r with
  | R5 | R6 | R7 => false
  | R8 | R9 => true
  | R10 | R11 | R12 | R13 | R14 | R15 | R16 | R17 => false
  | R18 | R19 | R20 | R21 | R22 | R23 | R24 | R25 | R26 | R27 => true
  | R28 | R29 | R30 => false
  | CapMachregs.F0 | CapMachregs.F1 | CapMachregs.F2 | CapMachregs.F3 | CapMachregs.F4 | CapMachregs.F5 | CapMachregs.F6 | CapMachregs.F7 => false
  | CapMachregs.F8 | CapMachregs.F9 => true
  | CapMachregs.F10 | CapMachregs.F11 | CapMachregs.F12 | CapMachregs.F13 | CapMachregs.F14 | CapMachregs.F15 | CapMachregs.F16 | CapMachregs.F17 => false
  | CapMachregs.F18 | CapMachregs.F19 | CapMachregs.F20 | CapMachregs.F21 | CapMachregs.F22 | CapMachregs.F23 | CapMachregs.F24 | CapMachregs.F25 | CapMachregs.F26 | CapMachregs.F27 => true
  | CapMachregs.F28 | CapMachregs.F29 | CapMachregs.F30 | CapMachregs.F31 => false
  end.

Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r =>
    if preg_eq r SPC
    || In_dec preg_eq r (List.map preg_of (List.filter is_callee_save all_mregs))
    then rs r
    else OCVundef.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use RISC-V registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): caploc -> ocval -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs cp v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv UNINIT (chunk_of_type ty) m rs#SPC (OCVptr (stack_ptr (Ptrofs.repr bofs))) cp (* false *) = inl v ->
      extcall_arg rs m (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (m: mem): rpair caploc -> ocval -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m l v ->
      extcall_arg_pair rs m (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m hi vhi ->
      extcall_arg rs m lo vlo ->
      extcall_arg_pair rs m (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: capsignature) (args: list ocval) : Prop :=
  (* FIXME *)
  (* list_forall2 (extcall_arg_pair rs m) (caploc_arguments sg) args. *)
  list_forall2 (extcall_arg_pair rs m) nil args.

Definition loc_external_result (sg: capsignature) : rpair preg :=
  (* FIXME *)
  (* map_rpair preg_of (caploc_result sg). *)
  map_rpair preg_of (One R10).

(** Execution of the instruction at [rs PC]. *)

(* Inductive stackframe: Type := *)
(* | Stackframe: *)
(*     forall (f: block)       (**r pointer to calling function *) *)
(*       (sp: val)         (**r stack pointer in calling function *) *)
(*       (retaddr: ptrofs), (**r Asm return address in calling function *) *)
(*       stackframe. *)

(* Definition stack := list stackframe. *)

(* (* The state of the stack when we start the execution *) *)
(* Definition initial_stack: stack := nil. *)

(* (* Updates to the stack *) *)
(* (* These two definitions shouldn't really do any real enforcement. Instead, *)
(*    they should just be used to keep track of the stack and use it in the *)
(*    invariants *) *)
(* (* The two definitions only update the stack when a cross-compartment change *)
(*    is detected *) *)
(* Definition update_stack_call (s: stack) (cp: compartment) rs' := *)
(*   let pc' := rs' # PC in *)
(*   let ra' := rs' # RA in *)
(*   let sp' := rs' # SP in *)
(*   (* match Genv.find_comp ge pc' with *) *)
(*   (* | Some cp' => *) *)
(*   if Pos.eqb cp (Genv.find_comp ge pc') then *)
(*     (* If we are in the same compartment as previously recorded, we *)
(*          don't update the stack *) *)
(*     Some s *)
(*   else *)
(*     (* Otherwise, we simply push a new frame on the stack *) *)
(*     match ra' with *)
(*     | Vptr f retaddr => *)
(*         Some (Stackframe f sp' retaddr :: s) *)
(*     | _ => None *)
(*     end *)
(*   . *)

(* Definition update_stack_return (s: stack) (cp: compartment) rs' := *)
(*   let pc' := rs' # PC in *)
(*   if Pos.eqb cp (Genv.find_comp ge pc') then *)
(*     (* If we are in the same compartment as previously recorded, we *)
(*          don't update the stack *) *)
(*     Some s *)
(*   else *)
(*     (* Otherwise we just pop the top stackframe, if it exists *) *)
(*     match s with *)
(*     | nil => Some nil *)
(*     | _ :: st' => Some st' *)
(*     end *)
(*   . *)

Inductive state: Type :=
  | State: regset -> mem -> state.

(* Definition is_call i := *)
(*   match i with *)
(*   | Pjal_s _ _ flag | Pjal_r _ _ flag => flag *)
(*   | _ => false *)
(*   end. *)

(* ALG: a call is denoted by a capability jump and link, which seals the next instruction in RA *)
Definition sig_call i :=
  match i with
  | PCjal_r _ _ sig flag =>
      if flag then Some sig else None
  | _ => None
  end.

(* Probably need to do the same thing and to define a [sig_return] function *)
(* ALG: a return is denotes by a sealed invocation *)
Definition is_return i rs :=
  match i with
  | PCinvoke _ r_data flag =>
      match rs###r_data with
      | OCVcap (OCsealed _ (OCVmem _ Directed _ _ _)) => flag
      | _ => false
      end
  | _ => false
  end.

(* Definition asm_parent_ra s := *)
(*   match s with *)
(*   | nil => Vnullptr *)
(*   | Stackframe b sp retaddr :: _ => Vptr b retaddr *)
(*   end. *)

(* Definition asm_parent_sp s := *)
(*   match s with *)
(*   | nil => Vnullptr *)
(*   | Stackframe b sp retaddr :: _ => sp *)
(*   end. *)

Definition executeAllowedCap (c : occap) : bool := false. (* FIXME *)

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
    forall c ofs f i rs m rs' m' c' cp,
      get_addr c = ofs ->
      executeAllowedCap c = true -> (* checks that the program counter is unsealed and has executable permission *)
      rs PCC = OCVcap c ->
      Genv.find_funct_ptr ge c = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_wrapper f ++ fn_code f) = Some i ->
      forall (COMP: Genv.find_comp ge (rs PCC) = cp),
      exec_instr f i rs m cp = Next rs' m' ->
      sig_call i = None ->
      is_return i rs = false ->
      forall (NEXTPC: rs' PCC = OCVcap c'),
      (* forall (ALLOWED: Genv.allowed_call ge (comp_of f) (Vptr b' ofs')), *) (* ownership of the capability determines allowed calls *)
      step (State rs m) E0 (State rs' m')
  | exec_step_internal_call:
      forall c ofs f i sig rs m rs' m' c' cp,
      get_addr c = ofs ->
      executeAllowedCap c = true -> (* checks that the program counter is unsealed and has executable permission *)
      rs PCC = OCVcap c ->
      Genv.find_funct_ptr ge c = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_wrapper f ++ fn_code f) = Some i ->
      exec_instr f i rs m cp = Next rs' m' ->
      sig_call i = Some sig ->
      forall (NEXTPC: rs' PCC = OCVcap c'),
      (* FIXME *)
      (* forall (ALLOWED: Genv.allowed_call ge (comp_of f) (Vptr b' ofs')), *) (* ownership of the capability determines allowed calls *)
      forall (ALLOWED: Genv.allowed_call ge (comp_of f) (OCVcap c')),
      (* forall (ALLOWED: Genv.allowed_call_capability ge (OCVcap c')), (* a step is only flagged as a call if it targets an E capability of the environment *) *)
      forall (CURCOMP: Genv.find_comp ge (OCVcap c) = cp),
      (* Is a call, we update the stack *)
      (* forall (STUPD: update_stack_call st cp rs' = Some st'), *)
        
      (* Is a call, we check whether we are allowed to pass pointers *)
      (* forall (NO_CROSS_PTR_REGS: *)
      (*     Genv.type_of_call ge (comp_of f) (Genv.find_comp ge (OCVcap c')) = Genv.CrossCompartmentCall -> *)
      (*     forall r, List.In (R r) (regs_of_rpairs (caploc_parameters sig)) -> *)
      (*          not_ptr (rs' (preg_of r))), *)
      (* forall (NO_CROSS_PTR_STACK: *)
      (*     Genv.type_of_call ge (comp_of f) (Genv.find_comp ge (Vptr b' ofs')) = Genv.CrossCompartmentCall -> *)
      (*     forall ofs v ty, *)
      (*       List.In (S Incoming ofs ty) (regs_of_rpairs (loc_parameters sig)) -> *)
      (*       Mem.loadv (chunk_of_type ty) m *)
      (*         (Val.offset_ptr (rs' SP) (* this is the stack pointer *) *)
      (*            (Ptrofs.repr (offset_arg ofs))) None *)
      (*                 = Some v -> *)
      (*       (* load_stack m sp ty (Ptrofs.repr (offset_arg ofs)) None = Some v -> *) *)
      (*       not_ptr v), *)
      (* The capability secure calling convention enforces the above:
      all functions are surrounded by wrappers that zero out
      registers, and checks that parameters are well typed. moreover,
      the calling convention makes sure not to pass any faulty stack
      pointers *)
        
      step (State rs m) E0 (State rs' m')
  | exec_step_internal_return:
      forall c ofs f i rs m rs' m' cp cp',
      get_addr c = ofs ->
      executeAllowedCap c = true ->
      rs PCC = OCVcap c ->
      Genv.find_funct_ptr ge c = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_wrapper f ++ fn_code f) = Some i ->
      exec_instr f i rs m cp = Next rs' m' ->
      is_return i rs = true ->
      forall (CURCOMP: Genv.find_comp ge (rs PCC) = cp),
      forall (NEXTCOMP: Genv.find_comp ge (rs' PCC) = cp'),

      (* We only impose conditions on when returns can be executed for cross-compartment
         returns. These conditions are that we restore the previous RA and SP *)
      (* forall (PC_RA: cp <> cp' -> rs' PCC = asm_parent_ra st), *)
      (* forall (RESTORE_SP: cp <> cp' -> rs' SP = asm_parent_sp st), *)
      (* Note that in the same manner, this definition only updates the stack when doing
         cross-compartment returns *)
      (* forall (STUPD: update_stack_return st cp rs' = Some st'), *)

      (* (* No cross-compartment pointer return *) *)
      (* forall (NO_CROSS_PTR: *)
      (*     Genv.type_of_call ge cp' cp = Genv.CrossCompartmentCall -> *)
      (*     forall r, List.In r (regs_of_rpair (loc_result (fn_sig f))) -> *)
      (*          not_ptr (rs' (preg_of r))), *)
      (* For the above to hold, it is up to the caller to do this check. TODO: discuss! *)  
        
      step (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall c ofs f ef args res rs m (* vargs *) t vres (rs' : regset) m',
      get_addr c = ofs ->
      executeAllowedCap c = true ->
      rs PCC = OCVcap c ->
      Genv.find_funct_ptr ge c = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_wrapper f ++ fn_code f) = Some (Pbuiltin ef args res) ->
      (* eval_builtin_args ge rs (rs SPC) m args vargs -> *)
      (* external_call ef ge (comp_of f) vargs m t vres m' ->  *)
  (* TODO: external calls are currently parametrized by the common environment *)
  (* definition, maybe use some kind of subtyping? or redo all definitions.... *)
      nextinstr
        (set_res res vres
                 (undef_regs (map preg_of (destroyed_by_builtin ef))
                             (rs#X31 <- OCVundef))) m = Next rs' m' ->
      step (State rs m) t (State rs' m')
  | exec_step_external:
      forall c ef (* args res  *)rs m t rs' m' cp cp' cp'',
      get_addr c = get_lo c ->
      executeAllowedCap c = true ->
      rs PCC = OCVcap c ->
      Genv.find_funct_ptr ge c = Some (External ef) ->
      forall COMP: Genv.find_comp ge (rs RAC) = cp,

      (* external_call ef ge cp args m t res m' -> *) (* TODO: same as above *)
      (* extcall_arguments rs m (ef_sig ef) args -> *) (* TODO *)
      (* rs' = (set_pair (loc_external_result (ef_sig ef) ) res (undef_caller_save_regs rs))#PCC <- (rs RAC) -> *) (* TODO: same as above. something is off with how i do define the new more detailed environment *)

      (* These steps behave like returns. So we must update the stack *)
      forall (CURCOMP: Genv.find_comp ge (rs PCC) = cp'),
      forall (NEXTCOMP: Genv.find_comp ge (rs' PCC) = cp''),
      (* We only impose conditions on when returns can be executed for cross-compartment
         returns. These conditions are that we restore the previous RA and SP *)
      (* forall (PC_RA: cp' <> cp'' -> rs' PCC = asm_parent_ra st), *)
      (* forall (RESTORE_SP: cp' <> cp'' -> rs' SPC = asm_parent_sp st), *)
      (* Note that in the same manner, this definition only updates the stack when doing
         cross-compartment returns *)
      step (State rs m) t (State rs' m').

End RELSEM.

(** Execution of whole programs. *)

Parameter stack_size: Z.
Parameter heap_size: Z.
Parameter seal_size: compartment -> program -> Z. (* TODO: define this one here? *)
Parameter seal_size_pos: forall c gls, seal_size c gls >= 0.

(* Parameter *)

(* FIXME? *)
Parameter build_capability : ptrofs -> globdef fundef unit -> occap.
Parameter build_capability_inv :
  forall base glob,
    Genv.globdef_capability_spec base glob (build_capability base glob).

(* Definition globalenv := Genv.globalenv stack_size heap_size seal_size seal_size_pos. *)
Definition globalenv := Genv.globalenv build_capability build_capability_inv.
(* Definition init_mem := Genv.init_mem stack_size heap_size seal_size seal_size_pos. *)
Definition init_mem := Genv.init_mem build_capability build_capability_inv.

Inductive initial_state (p: program) (gstart gend sstart send : ptrofs) : state -> Prop :=
  | initial_state_intro: forall m0 ge,
      globalenv p gstart gend (* sstart send *) = Some ge ->
      let rs0 :=
        (Pregmap.init OCVundef)
        # PCC <- (Genv.symbol_address ge p.(prog_main) Ptrofs.zero)
        # SPC <- OCVnullcap
                  # RAC <- Vnullptr in
      init_mem p gstart gend (* sstart send *) = Some m0 ->
      initial_state p gstart gend sstart send (State rs0 m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r,
      rs PCC = Vnullptr ->
      rs X10 = OCVint r ->
      final_state (State rs m) r.

Print Globalenvs.Genv.t. Locate Globalenvs.Genv.t
Print Genv.t.
Print genv. Locate genv.
Check step : (Genv.t fundef unit -> state -> trace -> state -> Prop).
(* disagreement between Globalenv and CapGlobal env, and older versions as well, + missing data *)
Check Semantics step (initial_state _ _ _ _ _) final_state.
Definition semantics (p: program) (gstart gend sstart send : ptrofs) :=
  do X <- (globalenv p gstart gend (* sstart send *));
  (* FIXME *)
  (* Some (Semantics_alt Genv.to_senv step (initial_state p gstart gend sstart send) final_state X). *)
  Some (Semantics_alt Genv.to_senv step (initial_state p gstart gend sstart send) final_state X).

(** Determinacy of the [Asm] semantics. *)

(* Remark extcall_arguments_determ: *)
(*   forall rs m sg args1 args2, *)
(*   extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2. *)
(* Proof. *)
(*   intros until m. *)
(*   assert (A: forall l v1 v2, *)
(*              extcall_arg rs m l v1 -> extcall_arg rs m l v2 -> v1 = v2). *)
(*   { intros. inv H; inv H0. congruence. *)
(*     destruct (rs X2); try discriminate. *)
(*     simpl in H2, H5. *)
(*     apply Mem.load_result in H2. *)
(*     apply Mem.load_result in H5. congruence. } *)
(*   assert (B: forall p v1 v2, *)
(*              extcall_arg_pair rs m p v1 -> extcall_arg_pair rs m p v2 -> v1 = v2). *)
(*   { intros. inv H; inv H0.  *)
(*     eapply A; eauto. *)
(*     f_equal; eapply A; eauto. } *)
(*   assert (C: forall ll vl1, list_forall2 (extcall_arg_pair rs m) ll vl1 -> *)
(*              forall vl2, list_forall2 (extcall_arg_pair rs m) ll vl2 -> vl1 = vl2). *)
(*   { *)
(*     induction 1; intros vl2 EA; inv EA. *)
(*     auto. *)
(*     f_equal; eauto. } *)
(*   intros. eapply C; eauto. *)
(* Qed. *)

(* (* RB: NOTE: In the next proof, the wrapped [exec_instr] would require extra *)
(*    processing, such as this. *) *)
(* (* Ltac peel_exec_instr := *) *)
(* (*   match goal with *) *)
(* (*   | Hexec : exec_instr _ _ _ ?RS ?M = _, *) *)
(* (*     Hpc : ?RS PC = Vptr ?B _ |- _ *) *)
(* (*     => *) *)
(* (*     unfold exec_instr in Hexec; *) *)
(* (*     rewrite Hpc in Hexec; *) *)
(* (*     destruct ((Mem.mem_compartments M) ! B) *) *)
(* (*   end. *) *)

(* Lemma semantics_determinate: forall p, determinate (semantics p). *)
(* Proof. *)
(* Ltac Equalities := *)
(*   match goal with *)
(*   | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] => *)
(*       rewrite H1 in H2; inv H2; Equalities *)
(*   | _ => idtac *)
(*   end. *)
(*   intros; constructor; simpl; intros. *)
(* - (* determ *) *)
(*   inv H; inv H0; Equalities; try now discriminate. *)
(*   + split. constructor. auto. *)
(*   + split. constructor. auto. *)
(*   + now destruct i0. *)
(*   + now destruct i0. *)
(*   + split. constructor. congruence. *)

(*   + assert (vargs0 = vargs) by (eapply eval_builtin_args_determ; eauto). subst vargs0. *)
(*     exploit external_call_determ. eexact H5. eexact H14.  intros [A B]. *)
(*     split. auto. intros. destruct B; auto. subst. auto. *)
(*   + assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0. *)
(*     exploit external_call_determ. eexact H3. eexact H9. intros [A B]. *)
(*     split. auto. intros. destruct B; auto. subst. congruence. *)
(* - (* trace length *) *)
(*   red; intros. inv H; simpl. *)
(*   omega. *)
(*   omega. *)
(*   omega. *)
(*   eapply external_call_trace_length; eauto. *)
(*   eapply external_call_trace_length; eauto. *)
(* - (* initial states *) *)
(*   inv H; inv H0. f_equal. congruence. *)
(* - (* final no step *) *)
(*   assert (NOTNULL: forall b ofs, Vnullptr <> Vptr b ofs). *)
(*   { intros; unfold Vnullptr; destruct Archi.ptr64; congruence. } *)
(*   inv H. unfold Vzero in H0. red; intros; red; intros. *)
(*   inv H; rewrite H0 in *; eelim NOTNULL; eauto. *)
(* - (* final states *) *)
(*   inv H; inv H0. congruence. *)
(* Qed. *)

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | IR RAC  => false
  | IR X31 => false
  | IR _   => true
  | FR _   => true
  | PC     => false
  end.
