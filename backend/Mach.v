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

(** The Mach intermediate language: abstract syntax.

  Mach is the last intermediate language before generation of assembly
  code.
*)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Stacklayout.

(** * Abstract syntax *)

(** Like Linear, the Mach language is organized as lists of instructions
  operating over machine registers, with default fall-through behaviour
  and explicit labels and branch instructions.

  The main difference with Linear lies in the instructions used to
  access the activation record.  Mach has three such instructions:
  [Mgetstack] and [Msetstack] to read and write within the activation
  record for the current function, at a given word offset and with a
  given type; and [Mgetparam], to read within the activation record of
  the caller.

  These instructions implement a more concrete view of the activation
  record than the the [Lgetstack] and [Lsetstack] instructions of
  Linear: actual offsets are used instead of abstract stack slots, and the
  distinction between the caller's frame and the callee's frame is
  made explicit. *)

Definition label := positive.

Inductive instruction: Type :=
  | Mgetstack: ptrofs -> typ -> mreg -> instruction
  | Msetstack: mreg -> ptrofs -> typ -> instruction
  | Mgetparam: ptrofs -> typ -> mreg -> instruction
  | Mop: operation -> list mreg -> mreg -> instruction
  | Mload: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Mstore: memory_chunk -> addressing -> list mreg -> mreg -> instruction
  | Mcall: signature -> mreg + ident -> instruction
  | Mtailcall: signature -> mreg + ident -> instruction
  | Mbuiltin: external_function -> list (builtin_arg mreg) -> builtin_res mreg -> instruction
  | Mlabel: label -> instruction
  | Mgoto: label -> instruction
  | Mcond: condition -> list mreg -> label -> instruction
  | Mjumptable: mreg -> list label -> instruction
  | Mreturn: instruction.

Definition code := list instruction.

Record function: Type := mkfunction
  { fn_comp: compartment;
    fn_sig: signature;
    fn_code: code;
    fn_stacksize: Z;
    fn_link_ofs: ptrofs;
    fn_retaddr_ofs: ptrofs }.

Instance has_comp_function: has_comp function := fn_comp.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

Definition genv := Genv.t fundef unit.

(** * Operational semantics *)

(** The semantics for Mach is close to that of [Linear]: they differ only
  on the interpretation of stack slot accesses.  In Mach, these
  accesses are interpreted as memory accesses relative to the
  stack pointer.  More precisely:
- [Mgetstack ofs ty r] is a memory load at offset [ofs * 4] relative
  to the stack pointer.
- [Msetstack r ofs ty] is a memory store at offset [ofs * 4] relative
  to the stack pointer.
- [Mgetparam ofs ty r] is a memory load at offset [ofs * 4]
  relative to the pointer found at offset 0 from the stack pointer.
  The semantics maintain a linked structure of activation records,
  with the current record containing a pointer to the record of the
  caller function at offset 0.

In addition to this linking of activation records, the
semantics also make provisions for storing a back link at offset
[f.(fn_link_ofs)] from the stack pointer, and a return address at
offset [f.(fn_retaddr_ofs)].  The latter stack location will be used
by the Asm code generated by [Asmgen] to save the return address into
the caller at the beginning of a function, then restore it and jump to
it at the end of a function.  The Mach concrete semantics does not
attach any particular meaning to the pointer stored in this reserved
location, but makes sure that it is preserved during execution of a
function.  The [return_address_offset] parameter is used to guess the
value of the return address that the Asm code generated later will
store in the reserved location.
*)

Definition load_stack (m: mem) (sp: val) (ty: typ) (ofs: ptrofs) :=
  Mem.loadv (chunk_of_type ty) m (Val.offset_ptr sp ofs).

Definition store_stack (m: mem) (sp: val) (ty: typ) (ofs: ptrofs) (v: val) :=
  Mem.storev (chunk_of_type ty) m (Val.offset_ptr sp ofs) v.

Notation offset_arg := Stacklayout.offset_arg.

Module RegEq.
  Definition t := mreg.
  Definition eq := mreg_eq.
End RegEq.

Module Regmap := EMap(RegEq).

Definition regset := Regmap.t val.

Notation "a ## b" := (List.map a b) (at level 1).
Notation "a # b <- c" := (Regmap.set b c a) (at level 1, b at next level).

Fixpoint undef_regs (rl: list mreg) (rs: regset) {struct rl} : regset :=
  match rl with
  | nil => rs
  | r1 :: rl' => Regmap.set r1 Vundef (undef_regs rl' rs)
  end.

Lemma undef_regs_other:
  forall r rl rs, ~In r rl -> undef_regs rl rs r = rs r.
Proof.
  induction rl; simpl; intros. auto. rewrite Regmap.gso. apply IHrl. intuition. intuition.
Qed.

Lemma undef_regs_same:
  forall r rl rs, In r rl -> undef_regs rl rs r = Vundef.
Proof.
  induction rl; simpl; intros. tauto.
  destruct H. subst a. apply Regmap.gss.
  unfold Regmap.set. destruct (RegEq.eq r a); auto.
Qed.

Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r => if is_callee_save r then rs r else Vundef.

Definition undef_caller_save_regs_ext (rs: regset) (callee_sig: signature) : regset :=
  fun r => if LTL.in_mreg r (LTL.parameters_mregs callee_sig) then rs r else Vundef.

Definition undef_non_return_regs_ext (rs: regset) (callee_sig: signature) : regset :=
  fun r => if LTL.in_mreg r (regs_of_rpair (loc_result callee_sig)) then rs r else Vundef.

Definition set_pair (p: rpair mreg) (v: val) (rs: regset) : regset :=
  match p with
  | One r => rs#r <- v
  | Twolong rhi rlo => rs#rhi <- (Val.hiword v) #rlo <- (Val.loword v)
  end.

Fixpoint set_res (res: builtin_res mreg) (v: val) (rs: regset) : regset :=
  match res with
  | BR r => Regmap.set r v rs
  | BR_none => rs
  | BR_splitlong hi lo => set_res lo (Val.loword v) (set_res hi (Val.hiword v) rs)
  end.

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Mlabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Mlabel lbl else instr <> Mlabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | i1 :: il => if is_label lbl i1 then Some il else find_label lbl il
  end.

Lemma find_label_tail:
  forall lbl c c', find_label lbl c = Some c' -> is_tail c' c.
Proof.
  induction c; simpl; intros. discriminate.
  destruct (is_label lbl a). inv H. auto with coqlib. eauto with coqlib.
Qed.

Lemma find_label_incl:
  forall lbl c c', find_label lbl c = Some c' -> incl c' c.
Proof.
  intros; red; intros. eapply is_tail_incl; eauto. eapply find_label_tail; eauto.
Qed.

Section RELSEM.

Variable return_address_offset: function -> code -> ptrofs -> Prop.

Variable comp_of_main: compartment.
Variable ge: genv.

Definition find_function_ptr
        (ge: genv) (ros: mreg + ident) (rs: regset) : option block :=
  match ros with
  | inl r =>
      match rs r with
      | Vptr b ofs => if Ptrofs.eq ofs Ptrofs.zero then Some b else None
      | _ => None
      end
  | inr symb =>
      Genv.find_symbol ge symb
  end.

(** Extract the values of the arguments to an external call. *)

Inductive extcall_arg (rs: regset) (m: mem) (sp: val): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m sp (R r) (rs r)
  | extcall_arg_stack: forall ofs ty cp v, (** TODO: should this [cp] be [None]? *)
      load_stack m sp ty (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs)) cp = Some v ->
      extcall_arg rs m sp (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (m: mem) (sp: val): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m sp l v ->
      extcall_arg_pair rs m sp (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m sp hi vhi ->
      extcall_arg rs m sp lo vlo ->
      extcall_arg_pair rs m sp (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (m: mem) (sp: val) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m sp) (loc_arguments sg) args.

(* NOTE: the option type will make these functions difficult to use, so lets stick to
  the previous definition*)
(* (** Functional equivalent to the previous definition, to be used to extract *)
(*     call arguments *) *)

(* Definition call_arg (rs: regset) (m: mem) (sp: val) (l: loc): option val := *)
(*   match l with *)
(*   | R r => Some (rs r) *)
(*   | S Outgoing ofs ty => load_stack m sp ty (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs)) None *)
(*   | _ => None *)
(*   end. *)

(* Definition call_arg_pair (rs: regset) (m: mem) (sp: val) (l: rpair loc): option val := *)
(*   match l with *)
(* | One r => call_arg rs m sp r *)
(* | Twolong r1 r2 => *)
(*     match call_arg rs m sp r1, call_arg rs m sp r2 with *)
(*     | Some rhi, Some rlo => Some (Val.longofwords rhi rlo) *)
(*     | _, _ => None *)
(*     end *)
(* end. *)

(* Definition call_arguments (rs: regset) (m: mem) (sp: val) (sg: signature): list (option val) := *)
(*   List.map (call_arg_pair rs m sp) (loc_arguments sg). *)


(** Extract the values of the arguments to a call. *)
(* Note the difference: [loc_parameters] vs [loc_arguments] *)
Inductive call_arg (rs: regset) (m: mem) (sp: val): loc -> val -> Prop :=
  | call_arg_reg: forall r,
      call_arg rs m sp (R r) (rs r)
  | call_arg_stack: forall ofs ty cp v, (** TODO: should this [cp] be [None]? *)
      load_stack m sp ty (Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * ofs)) cp = Some v ->
      call_arg rs m sp (S Incoming ofs ty) v.

Inductive call_arg_pair (rs: regset) (m: mem) (sp: val): rpair loc -> val -> Prop :=
  | call_arg_one: forall l v,
      call_arg rs m sp l v ->
      call_arg_pair rs m sp (One l) v
  | call_arg_twolong: forall hi lo vhi vlo,
      call_arg rs m sp hi vhi ->
      call_arg rs m sp lo vlo ->
      call_arg_pair rs m sp (Twolong hi lo) (Val.longofwords vhi vlo).

Definition call_arguments
    (rs: regset) (m: mem) (sp: val) (sg: signature) (args: list val) : Prop :=
  list_forall2 (call_arg_pair rs m sp) (loc_parameters sg) args.

Definition return_value (rs: regset) (sg: signature) :=
  match loc_result sg with
  | One l => rs l
  | Twolong l1 l2 => Val.longofwords (rs l1) (rs l2)
  end.

      (* forall (NO_CROSS_PTR: *)
      (*     Genv.type_of_call ge (Genv.find_comp ge (Vptr f Ptrofs.zero)) cp = Genv.CrossCompartmentCall -> *)
      (*     forall l, List.In l (regs_of_rpair (loc_result sg)) -> *)
      (*         not_ptr (rs l)), *)
(** Mach execution states. *)

Inductive stackframe: Type :=
  | Stackframe:
      forall (f: block)        (**r pointer to calling function *)
        (cp: compartment) (**r compartment of the callee *)
        (sg: signature)   (**r callee's signature *)
             (sp: val)         (**r stack pointer in calling function *)
             (retaddr: ptrofs) (**r Asm return address in calling function *)
             (c: code),        (**r program point in calling function *)
      stackframe.

Definition callee_comp (s: list stackframe) :=
  match s with
  | nil => comp_of_main
  | Stackframe _ cp _ _ _ _ :: _ => cp
  end.

Definition callee_comp_stackframe (f: stackframe) :=
  match f with
    Stackframe _ cp _ _ _ _ => cp
  end.

Inductive state: Type :=
  | State:
      forall (stack: list stackframe)  (**r call stack *)
             (f: block)                (**r pointer to current function *)
             (sp: val)                 (**r stack pointer *)
             (c: code)                 (**r current program point *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state
  | Callstate:
      forall (stack: list stackframe)  (**r call stack *)
             (f: block)                (**r pointer to function to call *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state
  | Returnstate:
      forall (stack: list stackframe)  (**r call stack *)
             (rs: regset)              (**r register state *)
             (m: mem),                  (**r memory state *)
      state.

Definition parent_sp (s: list stackframe) : val :=
  match s with
  | nil => Vnullptr
  | Stackframe f _ _ sp ra c :: s' => sp
  end.

Definition parent_ra (s: list stackframe) : val :=
  match s with
  | nil => Vnullptr
  | Stackframe f _ _ sp ra c :: s' => Vptr f ra
  end.

Definition call_comp (s: list stackframe): compartment :=
  match parent_ra s with
  | Vptr b _ => Genv.find_comp ge (Vptr b Ptrofs.zero)
  | _ => default_compartment
  end.

(* TODO: Better name (also LTL)! *)
Definition parent_signature (stack: list stackframe) : signature :=
  match stack with
  | nil => signature_main
  | Stackframe _ _ sig _ _ _ :: _ => sig
  end.

Inductive step: state -> trace -> state -> Prop :=
  | exec_Mlabel:
      forall s f sp lbl c rs m,
      step (State s f sp (Mlabel lbl :: c) rs m)
        E0 (State s f sp c rs m)
  | exec_Mgetstack:
      forall s f sp ofs ty dst c rs m v cp,
      forall (CURCOMP: Genv.find_comp ge (Vptr f Ptrofs.zero) = cp),
      load_stack m sp ty ofs (Some cp) = Some v ->
      step (State s f sp (Mgetstack ofs ty dst :: c) rs m)
        E0 (State s f sp c (rs#dst <- v) m)
  | exec_Msetstack:
      forall s f sp src ofs ty c rs m m' rs' cp,
      forall (CURCOMP: Genv.find_comp ge (Vptr f Ptrofs.zero) = cp),
      store_stack m sp ty ofs (rs src) cp = Some m' ->
      rs' = undef_regs (destroyed_by_setstack ty) rs ->
      step (State s f sp (Msetstack src ofs ty :: c) rs m)
        E0 (State s f sp c rs' m')
  | exec_Mgetparam:
      forall s fb f sp ofs ty dst c rs m (* cp' *) v rs' cp,
      forall (CURCOMP: Genv.find_comp ge (Vptr fb Ptrofs.zero) = cp),
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m sp Tptr f.(fn_link_ofs) (Some cp) = Some (parent_sp s) ->
      (* forall (COMPSP: call_comp s = Some cp'), *)
      load_stack m (parent_sp s) ty ofs None = Some v -> (* /!\ Privileged!! *)
      rs' = (rs # temp_for_parent_frame <- Vundef # dst <- v) ->
      step (State s fb sp (Mgetparam ofs ty dst :: c) rs m)
        E0 (State s fb sp c rs' m)
  | exec_Mop:
      forall s f sp op args res c rs m v rs',
      eval_operation ge sp op rs##args m = Some v ->
      rs' = ((undef_regs (destroyed_by_op op) rs)#res <- v) ->
      step (State s f sp (Mop op args res :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mload:
      forall s f sp chunk addr args dst c rs m a v rs' cp,
      forall (CURCOMP: Genv.find_comp ge (Vptr f Ptrofs.zero) = cp),
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a (Some cp) = Some v ->
      rs' = ((undef_regs (destroyed_by_load chunk addr) rs)#dst <- v) ->
      step (State s f sp (Mload chunk addr args dst :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mstore:
      forall s f sp chunk addr args src c rs m m' a rs' cp,
      forall (CURCOMP: Genv.find_comp ge (Vptr f Ptrofs.zero) = cp),
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) cp = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      step (State s f sp (Mstore chunk addr args src :: c) rs m)
        E0 (State s f sp c rs' m')
  | exec_Mcall:
      forall s fb sp sig ros c rs m f f' ra fd args t,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      return_address_offset f c ra ->
      forall (CALLED: Genv.find_funct_ptr ge f' = Some fd),
      forall (ALLOWED: Genv.allowed_call ge (comp_of f) (Vptr f' Ptrofs.zero)),
      (* call_arguments are never invalidated *)
      forall (ARGS: call_arguments (undef_regs destroyed_at_function_entry rs) m sp sig args),
      forall (NO_CROSS_PTR:
          Genv.type_of_call ge (comp_of f) (Genv.find_comp ge (Vptr f' Ptrofs.zero)) = Genv.CrossCompartmentCall ->
          List.Forall not_ptr args),
      forall (EV: call_trace ge (comp_of f) (Genv.find_comp ge (Vptr f' Ptrofs.zero)) (Vptr f' Ptrofs.zero)
               args (sig_args sig) t),
      step (State s fb sp (Mcall sig ros :: c) rs m)
        t (Callstate (Stackframe fb (Genv.find_comp ge (Vptr f' Ptrofs.zero)) sig sp ra c :: s)
                       f' rs m)
  | exec_Mtailcall:
      forall s fb stk soff sig ros c rs m f f' m' fd cp,
      forall (CURCOMP: Genv.find_comp ge (Vptr fb Ptrofs.zero) = cp),
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) (Some cp) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) (Some cp) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) cp = Some m' ->
      forall (CALLED: Genv.find_funct_ptr ge f' = Some fd),
      forall (COMP: comp_of fd = comp_of f),
      forall (ALLOWED: needs_calling_comp cp = false),
      forall (ALLOWED': Genv.allowed_call ge cp (Vptr f' Ptrofs.zero)),
      step (State s fb (Vptr stk soff) (Mtailcall sig ros :: c) rs m)
        E0 (Callstate s f' rs m')
  | exec_Mbuiltin:
      forall s fb f sp rs m ef args res b vargs t vres rs' m' cp,
      forall (CURCOMP: Genv.find_comp ge (Vptr fb Ptrofs.zero) = cp),
      eval_builtin_args ge rs sp m args vargs ->
      forall (FUN: Genv.find_funct_ptr ge fb = Some (Internal f)),
      external_call ef ge cp vargs m t vres m' ->
      rs' = set_res res vres (undef_regs (destroyed_by_builtin ef) rs) ->
      step (State s fb sp (Mbuiltin ef args res :: b) rs m)
         t (State s fb sp b rs' m')
  | exec_Mgoto:
      forall s fb f sp lbl c rs m c',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      step (State s fb sp (Mgoto lbl :: c) rs m)
        E0 (State s fb sp c' rs m)
  | exec_Mcond_true:
      forall s fb f sp cond args lbl c rs m c' rs',
      eval_condition cond rs##args m = Some true ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (State s fb sp (Mcond cond args lbl :: c) rs m)
        E0 (State s fb sp c' rs' m)
  | exec_Mcond_false:
      forall s f sp cond args lbl c rs m rs',
      eval_condition cond rs##args m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      step (State s f sp (Mcond cond args lbl :: c) rs m)
        E0 (State s f sp c rs' m)
  | exec_Mjumptable:
      forall s fb f sp arg tbl c rs m n lbl c' rs',
      rs arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs destroyed_by_jumptable rs ->
      step (State s fb sp (Mjumptable arg tbl :: c) rs m)
        E0 (State s fb sp c' rs' m)
  | exec_Mreturn:
      (* RB: NOTE: Think about compartment variables, here and in a similar case. *)
      forall s fb stk soff c rs m f m' retrs cp,
      forall (CURCOMP: Genv.find_comp ge (Vptr fb Ptrofs.zero) = cp),
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_link_ofs) (Some cp) = Some (parent_sp s) ->
      load_stack m (Vptr stk soff) Tptr f.(fn_retaddr_ofs) (Some cp) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) cp = Some m' ->
      forall (RETREGS:
               retrs =
               (*   match Genv.type_of_call ge (call_comp s) (comp_of f) with *)
               (*   | Genv.CrossCompartmentCall => undef_non_return_regs_ext rs (parent_signature s) *)
               (*   | _ => rs *)
               (*   end), *)
                 undef_non_return_regs_ext rs (parent_signature s)),
      step (State s fb (Vptr stk soff) (Mreturn :: c) rs m)
        E0 (Returnstate s retrs m')
  | exec_function_internal:
      forall s fb rs m f m1 m2 m3 stk callrs rs' cp,
      forall (CURCOMP: Genv.find_comp ge (Vptr fb Ptrofs.zero) = cp),
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      Mem.alloc m cp 0 f.(fn_stacksize) = (m1, stk) ->
      let sp := Vptr stk Ptrofs.zero in
      store_stack m1 sp Tptr f.(fn_link_ofs) (parent_sp s) cp = Some m2 ->
      store_stack m2 sp Tptr f.(fn_retaddr_ofs) (parent_ra s) cp = Some m3 ->
      forall (CALLREGS:
               callrs =
                 (* match Genv.type_of_call ge (call_comp s) (Genv.find_comp ge (Vptr fb Ptrofs.zero)) with *)
                 (* | Genv.CrossCompartmentCall => undef_caller_save_regs_ext rs (parent_signature s) *)
                 (* | _ => rs *)
                 (* end), *)
                 undef_caller_save_regs_ext rs (parent_signature s)),
      rs' = undef_regs destroyed_at_function_entry callrs ->
      step (Callstate s fb rs m)
        E0 (State s fb sp f.(fn_code) rs' m3)
  | exec_function_external:
      forall s fb rs m t rs' ef args res m' cp,
      Genv.find_funct_ptr ge fb = Some (External ef) ->
      extcall_arguments rs m (parent_sp s) (ef_sig ef) args ->
      forall (COMP: call_comp s = cp),
      external_call ef ge cp args m t res m' ->
      rs' = set_pair (loc_result (ef_sig ef)) res (undef_caller_save_regs rs) ->
      step (Callstate s fb rs m)
         t (Returnstate s rs' m')
  | exec_return:
      forall s f sp ra c rs m sg cp t,
      forall (NO_CROSS_PTR:
          Genv.type_of_call ge (Genv.find_comp ge (Vptr f Ptrofs.zero)) cp = Genv.CrossCompartmentCall ->
          not_ptr (return_value rs sg)),
      forall (EV: return_trace ge (Genv.find_comp ge (Vptr f Ptrofs.zero)) cp (return_value rs sg) (sig_res sg) t),
      step (Returnstate (Stackframe f cp sg sp ra c :: s) rs m)
        t (State s f sp c rs m).

End RELSEM.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall fb m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some fb ->
      initial_state p (Callstate nil fb (Regmap.init Vundef) m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r retcode,
      loc_result signature_main = One r ->
      rs r = Vint retcode ->
      final_state (Returnstate nil rs m) retcode.

Definition semantics (rao: function -> code -> ptrofs -> Prop) (p: program) :=
  Semantics (step rao) (initial_state p) final_state (Genv.globalenv p).

(** * Leaf functions *)

(** A leaf function is a function that contains no [Mcall] instruction. *)

Definition is_leaf_function (f: function) : bool :=
  List.forallb
    (fun i => match i with Mcall _ _ => false | _ => true end)
    f.(fn_code).  

(** Semantic characterization of leaf functions: 
    functions in the call stack are never leaf functions. *)

Section WF_STATES.

Variable rao: function -> code -> ptrofs -> Prop.

Variable ge: genv.

Inductive wf_frame: stackframe -> Prop :=
  | wf_stackframe_intro: forall fb sg cp sp ra c f
        (CODE: Genv.find_funct_ptr ge fb = Some (Internal f))
        (LEAF: is_leaf_function f = false)
        (TAIL: is_tail c f.(fn_code)),
      wf_frame (Stackframe fb cp sg sp ra c).

Inductive wf_state: state -> Prop :=
  | wf_normal_state: forall s fb sp c rs m f
        (STACK: Forall wf_frame s)
        (CODE: Genv.find_funct_ptr ge fb = Some (Internal f))
        (TAIL: is_tail c f.(fn_code)),
      wf_state (State s fb sp c rs m)
  | wf_call_state: forall s fb rs m
        (STACK: Forall wf_frame s),
      wf_state (Callstate s fb rs m)
  | wf_return_state: forall s rs m
        (STACK: Forall wf_frame s),
      wf_state (Returnstate s rs m).

Lemma wf_step:
  forall S1 t S2, step rao ge S1 t S2 -> wf_state S1 -> wf_state S2.
Proof.
  induction 1; intros WF; inv WF; try (econstructor; now eauto with coqlib).
- (* call *)
  assert (f0 = f) by congruence. subst f0.
  econstructor.
  constructor; auto. econstructor; eauto with coqlib.
  destruct (is_leaf_function f) eqn:E; auto.
  unfold is_leaf_function in E; rewrite forallb_forall in E.
  symmetry. apply (E (Mcall sig ros)). eapply is_tail_in; eauto.
- (* goto *)
  assert (f0 = f) by congruence. subst f0.
  econstructor; eauto using find_label_tail.
- (* cond *)
  assert (f0 = f) by congruence. subst f0. econstructor; eauto using find_label_tail.  
- (* jumptable *)
  assert (f0 = f) by congruence. subst f0. econstructor; eauto using find_label_tail.  
- (* return *)
  inv STACK. inv H1. econstructor; eauto.
Qed.

End WF_STATES.

Lemma wf_initial:
  forall p S, initial_state p S -> wf_state (Genv.globalenv p) S.
Proof.
  intros. inv H. fold ge. constructor. constructor.
Qed.
