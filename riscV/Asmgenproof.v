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

(** Correctness proof for RISC-V generation: main proof. *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm.
Require Import Asmgen Asmgenproof0 Asmgenproof1.

Definition match_prog (p: Mach.program) (tp: Asm.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

#[global]
Instance comp_transf_function: has_comp_transl_partial transf_function.
Proof.
  unfold transf_function, transl_function.
  intros f ? H; monadInv H; trivial.
  destruct transl_code'; simpl in *; try easy.
  inv EQ. destruct zlt; try easy.
  now inv EQ0.
Qed.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Section PRESERVATION.

Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Let comp_of_main := comp_of_main tprog.


Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma functions_translated:
  forall b f,
  Genv.find_def ge b = Some (Gfun f) ->
  exists tf,
  Genv.find_def tge b = Some (Gfun tf) /\ transf_fundef f = OK tf.
Proof (Genv.find_def_transf_partial TRANSF).

Lemma find_comp_of_block_translated:
  forall b,
    Genv.find_comp_of_block ge b = Genv.find_comp_of_block tge b.
Proof.
  eapply (Genv.find_comp_of_block_transf_partial TRANSF).
Qed.

Lemma find_comp_translated:
  forall vf,
    Genv.find_comp ge vf = Genv.find_comp tge vf.
Proof.
  eapply (Genv.find_comp_transf_partial TRANSF).
Qed.

Lemma functions_transl:
  forall fb f tf,
  Genv.find_def ge fb = Some (Gfun (Internal f)) ->
  transf_function f = OK tf ->
  Genv.find_def tge fb = Some (Gfun (Internal tf)).
Proof.
  intros. exploit functions_translated; eauto. intros [tf' [A B]].
  monadInv B. rewrite H0 in EQ; inv EQ; auto.
Qed.

Lemma allowed_call_translated:
  forall cp vf,
    Genv.allowed_call ge cp vf ->
    Genv.allowed_call tge cp vf.
Proof.
  intros cp vf H.
  eapply (Genv.match_genvs_allowed_calls TRANSF). eauto.
Qed.


(** * Properties of control flow *)

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> list_length_z tf.(fn_code) <= Ptrofs.max_unsigned.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z x.(fn_code))); inv EQ0.
  lia.
Qed.

Lemma exec_straight_exec:
  forall fb f c ep tf tc c' rs m rs' m' st,
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  exec_straight tge tf tc rs m c' rs' m' ->
  plus step tge (State st rs m) E0 (State st rs' m').
Proof.
  intros. inv H.
  eapply exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
Qed.

Lemma exec_straight_at:
  forall fb f c ep tf tc c' ep' tc' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  transl_code f c' ep' = OK tc' ->
  exec_straight tge tf tc rs m tc' rs' m' ->
  transl_code_at_pc ge (rs' PC) fb f c' ep' tf tc'.
Proof.
  intros. inv H.
  exploit exec_straight_steps_2; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  intros [ofs' [PC' CT']].
  rewrite PC'. econstructor; eauto.
Qed.

(** The following lemmas show that the translation from Mach to Asm
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ Asm instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- Asm instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that Asm constructor
  functions do not introduce new labels.
*)

Section TRANSL_LABEL.

Remark loadimm32_label:
  forall r n k, tail_nolabel k (loadimm32 r n k).
Proof.
  intros; unfold loadimm32. destruct (make_immed32 n); TailNoLabel.
  unfold load_hilo32. destruct (Int.eq lo Int.zero); TailNoLabel.
Qed.
Hint Resolve loadimm32_label: labels.

Remark opimm32_label:
  forall op opimm r1 r2 n k,
  (forall r1 r2 r3, nolabel (op r1 r2 r3)) ->
  (forall r1 r2 n, nolabel (opimm r1 r2 n)) ->
  tail_nolabel k (opimm32 op opimm r1 r2 n k).
Proof.
  intros; unfold opimm32. destruct (make_immed32 n); TailNoLabel.
  unfold load_hilo32. destruct (Int.eq lo Int.zero); TailNoLabel.
Qed.
Hint Resolve opimm32_label: labels.

Remark loadimm64_label:
  forall r n k, tail_nolabel k (loadimm64 r n k).
Proof.
  intros; unfold loadimm64. destruct (make_immed64 n); TailNoLabel.
  unfold load_hilo64. destruct (Int64.eq lo Int64.zero); TailNoLabel.
Qed.
Hint Resolve loadimm64_label: labels.

Remark opimm64_label:
  forall op opimm r1 r2 n k,
  (forall r1 r2 r3, nolabel (op r1 r2 r3)) ->
  (forall r1 r2 n, nolabel (opimm r1 r2 n)) ->
  tail_nolabel k (opimm64 op opimm r1 r2 n k).
Proof.
  intros; unfold opimm64. destruct (make_immed64 n); TailNoLabel.
  unfold load_hilo64. destruct (Int64.eq lo Int64.zero); TailNoLabel.
Qed.
Hint Resolve opimm64_label: labels.

Remark addptrofs_label:
  forall r1 r2 n k, tail_nolabel k (addptrofs r1 r2 n k).
Proof.
  unfold addptrofs; intros. destruct (Ptrofs.eq_dec n Ptrofs.zero). TailNoLabel.
  destruct Archi.ptr64. apply opimm64_label; TailNoLabel. apply opimm32_label; TailNoLabel.
Qed.
Hint Resolve addptrofs_label: labels.

Remark transl_cond_float_nolabel:
  forall c r1 r2 r3 insn normal,
  transl_cond_float c r1 r2 r3 = (insn, normal) -> nolabel insn.
Proof.
  unfold transl_cond_float; intros. destruct c; inv H; exact I.
Qed.

Remark transl_cond_single_nolabel:
  forall c r1 r2 r3 insn normal,
  transl_cond_single c r1 r2 r3 = (insn, normal) -> nolabel insn.
Proof.
  unfold transl_cond_single; intros. destruct c; inv H; exact I.
Qed.

Remark transl_cbranch_label:
  forall cond args lbl k c,
  transl_cbranch cond args lbl k = OK c -> tail_nolabel k c.
Proof.
  intros. unfold transl_cbranch in H; destruct cond; TailNoLabel.
- destruct c0; simpl; TailNoLabel.
- destruct c0; simpl; TailNoLabel.
- destruct (Int.eq n Int.zero).
  destruct c0; simpl; TailNoLabel.
  apply tail_nolabel_trans with (transl_cbranch_int32s c0 x X31 lbl :: k).
  auto with labels. destruct c0; simpl; TailNoLabel.
- destruct (Int.eq n Int.zero).
  destruct c0; simpl; TailNoLabel.
  apply tail_nolabel_trans with (transl_cbranch_int32u c0 x X31 lbl :: k).
  auto with labels. destruct c0; simpl; TailNoLabel.
- destruct c0; simpl; TailNoLabel.
- destruct c0; simpl; TailNoLabel.
- destruct (Int64.eq n Int64.zero).
  destruct c0; simpl; TailNoLabel.
  apply tail_nolabel_trans with (transl_cbranch_int64s c0 x X31 lbl :: k).
  auto with labels. destruct c0; simpl; TailNoLabel.
- destruct (Int64.eq n Int64.zero).
  destruct c0; simpl; TailNoLabel.
  apply tail_nolabel_trans with (transl_cbranch_int64u c0 x X31 lbl :: k).
  auto with labels. destruct c0; simpl; TailNoLabel.
- destruct (transl_cond_float c0 X31 x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_float_nolabel; eauto. 
  destruct normal; TailNoLabel.
- destruct (transl_cond_float c0 X31 x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_float_nolabel; eauto. 
  destruct normal; TailNoLabel.
- destruct (transl_cond_single c0 X31 x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_single_nolabel; eauto. 
  destruct normal; TailNoLabel.
- destruct (transl_cond_single c0 X31 x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_single_nolabel; eauto. 
  destruct normal; TailNoLabel.
Qed.

Remark transl_cond_op_label:
  forall cond args r k c,
  transl_cond_op cond r args k = OK c -> tail_nolabel k c.
Proof.
  intros. unfold transl_cond_op in H; destruct cond; TailNoLabel.
- destruct c0; simpl; TailNoLabel.
- destruct c0; simpl; TailNoLabel. 
- unfold transl_condimm_int32s.
  destruct (Int.eq n Int.zero).
+ destruct c0; simpl; TailNoLabel.
+ destruct c0; simpl.
* eapply tail_nolabel_trans; [apply opimm32_label; intros; exact I | TailNoLabel].
* eapply tail_nolabel_trans; [apply opimm32_label; intros; exact I | TailNoLabel].
* apply opimm32_label; intros; exact I.
* destruct (Int.eq n (Int.repr Int.max_signed)). apply loadimm32_label. apply opimm32_label; intros; exact I.
* eapply tail_nolabel_trans. apply loadimm32_label. TailNoLabel.
* eapply tail_nolabel_trans. apply loadimm32_label. TailNoLabel.
- unfold transl_condimm_int32u.
  destruct (Int.eq n Int.zero).
+ destruct c0; simpl; TailNoLabel.
+ destruct c0; simpl; 
  try (eapply tail_nolabel_trans; [apply loadimm32_label | TailNoLabel]).
  apply opimm32_label; intros; exact I.
- destruct c0; simpl; TailNoLabel.
- destruct c0; simpl; TailNoLabel. 
- unfold transl_condimm_int64s.
  destruct (Int64.eq n Int64.zero).
+ destruct c0; simpl; TailNoLabel.
+ destruct c0; simpl.
* eapply tail_nolabel_trans; [apply opimm64_label; intros; exact I | TailNoLabel].
* eapply tail_nolabel_trans; [apply opimm64_label; intros; exact I | TailNoLabel].
* apply opimm64_label; intros; exact I.
* destruct (Int64.eq n (Int64.repr Int64.max_signed)). apply loadimm32_label. apply opimm64_label; intros; exact I.
* eapply tail_nolabel_trans. apply loadimm64_label. TailNoLabel.
* eapply tail_nolabel_trans. apply loadimm64_label. TailNoLabel.
- unfold transl_condimm_int64u.
  destruct (Int64.eq n Int64.zero).
+ destruct c0; simpl; TailNoLabel.
+ destruct c0; simpl; 
  try (eapply tail_nolabel_trans; [apply loadimm64_label | TailNoLabel]).
  apply opimm64_label; intros; exact I.
- destruct (transl_cond_float c0 r x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_float_nolabel; eauto. 
  destruct normal; TailNoLabel.
- destruct (transl_cond_float c0 r x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_float_nolabel; eauto. 
  destruct normal; TailNoLabel.
- destruct (transl_cond_single c0 r x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_single_nolabel; eauto. 
  destruct normal; TailNoLabel.
- destruct (transl_cond_single c0 r x x0) as [insn normal] eqn:F; inv EQ2.
  apply tail_nolabel_cons. eapply transl_cond_single_nolabel; eauto. 
  destruct normal; TailNoLabel.
Qed.

Remark transl_op_label:
  forall op args r k c,
  transl_op op args r k = OK c -> tail_nolabel k c.
Proof.
Opaque Int.eq.
  unfold transl_op; intros; destruct op; TailNoLabel.
- destruct (preg_of r); try discriminate; destruct (preg_of m); inv H; TailNoLabel.
- destruct (Float.eq_dec n Float.zero); TailNoLabel.
- destruct (Float32.eq_dec n Float32.zero); TailNoLabel.
- destruct (Archi.pic_code tt && negb (Ptrofs.eq ofs Ptrofs.zero)).
+ eapply tail_nolabel_trans; [|apply addptrofs_label]. TailNoLabel.
+ TailNoLabel. 
- apply opimm32_label; intros; exact I.
- apply opimm32_label; intros; exact I.
- apply opimm32_label; intros; exact I.
- apply opimm32_label; intros; exact I.
- destruct (Int.eq n Int.zero); TailNoLabel.
- apply opimm64_label; intros; exact I.
- apply opimm64_label; intros; exact I.
- apply opimm64_label; intros; exact I.
- apply opimm64_label; intros; exact I.
- destruct (Int.eq n Int.zero); TailNoLabel.
- eapply transl_cond_op_label; eauto.
Qed.

Remark indexed_memory_access_label:
  forall (mk_instr: ireg -> offset -> instruction) base ofs k,
  (forall r o, nolabel (mk_instr r o)) ->
  tail_nolabel k (indexed_memory_access mk_instr base ofs k).
Proof.
  unfold indexed_memory_access; intros. 
  destruct Archi.ptr64.
  destruct (make_immed64 (Ptrofs.to_int64 ofs)); TailNoLabel.
  destruct (make_immed32 (Ptrofs.to_int ofs)); TailNoLabel.
Qed.

Remark loadind_label:
  forall base ofs ty dst k c b,
  loadind base ofs ty dst k b = OK c -> tail_nolabel k c.
Proof.
  unfold loadind; intros.
  destruct ty, (preg_of dst); inv H; apply indexed_memory_access_label; intros; exact I.
Qed.

Remark storeind_label:
  forall src base ofs ty k c,
  storeind src base ofs ty k = OK c -> tail_nolabel k c.
Proof.
  unfold storeind; intros.
  destruct ty, (preg_of src); inv H; apply indexed_memory_access_label; intros; exact I.
Qed.

Remark loadind_ptr_label:
  forall base ofs dst k b, tail_nolabel k (loadind_ptr base ofs dst k b).
Proof.
  intros. apply indexed_memory_access_label. intros; destruct Archi.ptr64; exact I.
Qed.

Remark storeind_ptr_label:
  forall src base ofs k, tail_nolabel k (storeind_ptr src base ofs k).
Proof.
  intros. apply indexed_memory_access_label. intros; destruct Archi.ptr64; exact I.
Qed.

Remark transl_memory_access_label:
  forall (mk_instr: ireg -> offset -> instruction) addr args k c,
  (forall r o, nolabel (mk_instr r o)) ->
  transl_memory_access mk_instr addr args k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_memory_access; intros; destruct addr; TailNoLabel; apply indexed_memory_access_label; auto. 
Qed.

Remark make_epilogue_label:
  forall f k, tail_nolabel k (make_epilogue f k).
Proof.
  unfold make_epilogue; intros. eapply tail_nolabel_trans. apply loadind_ptr_label. TailNoLabel.
Qed.

Lemma transl_instr_label:
  forall f i ep k c,
  transl_instr f i ep k = OK c ->
  match i with Mlabel lbl => c = Plabel lbl :: k | _ => tail_nolabel k c end.
Proof.
  unfold transl_instr; intros; destruct i; TailNoLabel.
- eapply loadind_label; eauto.
- eapply storeind_label; eauto.
- destruct ep. eapply loadind_label; eauto.
  eapply tail_nolabel_trans. apply loadind_ptr_label. eapply loadind_label; eauto. 
- eapply transl_op_label; eauto.
- destruct m; monadInv H; eapply transl_memory_access_label; eauto; intros; exact I.
- destruct m; monadInv H; eapply transl_memory_access_label; eauto; intros; exact I.
- destruct s0; monadInv H; TailNoLabel.
- destruct s0; monadInv H; (eapply tail_nolabel_trans; [eapply make_epilogue_label|TailNoLabel]).
- eapply transl_cbranch_label; eauto.
- eapply tail_nolabel_trans; [eapply make_epilogue_label|TailNoLabel].
Qed.

Lemma transl_instr_label':
  forall lbl f i ep k c,
  transl_instr f i ep k = OK c ->
  find_label lbl c = if Mach.is_label lbl i then Some k else find_label lbl k.
Proof.
  intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply B).
  intros. subst c. simpl. auto.
Qed.

Lemma transl_code_label:
  forall lbl f c ep tc,
  transl_code f c ep = OK tc ->
  match Mach.find_label lbl c with
  | None => find_label lbl tc = None
  | Some c' => exists tc', find_label lbl tc = Some tc' /\ transl_code f c' false = OK tc'
  end.
Proof.
  induction c; simpl; intros.
  inv H. auto.
  monadInv H. rewrite (transl_instr_label' lbl _ _ _ _ _ EQ0).
  generalize (Mach.is_label_correct lbl a).
  destruct (Mach.is_label lbl a); intros.
  subst a. simpl in EQ. exists x; auto.
  eapply IHc; eauto.
Qed.

Lemma transl_find_label:
  forall lbl f tf,
  transf_function f = OK tf ->
  match Mach.find_label lbl f.(Mach.fn_code) with
  | None => find_label lbl tf.(fn_code) = None
  | Some c => exists tc, find_label lbl tf.(fn_code) = Some tc /\ transl_code f c false = OK tc
  end.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z x.(fn_code))); inv EQ0.
  monadInv EQ. rewrite transl_code'_transl_code in EQ0. unfold fn_code. 
  simpl. destruct (storeind_ptr_label X1 X2 (fn_retaddr_ofs f) x) as [A B]; rewrite B. 
  eapply transl_code_label; eauto.
Qed.

End TRANSL_LABEL.

(** A valid branch in a piece of Mach code translates to a valid ``go to''
  transition in the generated Asm code. *)

Lemma find_label_goto_label:
  forall f tf lbl rs m c' b ofs,
  Genv.find_def ge b = Some (Gfun (Internal f)) ->
  transf_function f = OK tf ->
  rs PC = Vptr b ofs ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  exists tc', exists rs',
    goto_label tf lbl rs m = Next rs' m
  /\ transl_code_at_pc ge (rs' PC) b f c' false tf tc'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. exploit (transl_find_label lbl f tf); eauto. rewrite H2.
  intros [tc [A B]].
  exploit label_pos_code_tail; eauto. instantiate (1 := 0).
  intros [pos' [P [Q R]]].
  exists tc; exists (rs#PC <- (Vptr b (Ptrofs.repr pos'))).
  split. unfold goto_label. rewrite P. rewrite H1. auto.
  split. rewrite Pregmap.gss. econstructor; eauto.
  rewrite Ptrofs.unsigned_repr. replace (pos' - 0) with pos' in Q.
  auto. lia.
  generalize (transf_function_no_overflow _ _ H0). lia.
  intros. apply Pregmap.gso; auto.
Qed.

(** Existence of return addresses *)

Lemma return_address_exists:
  forall f sg ros c, is_tail (Mcall sg ros :: c) f.(Mach.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. eapply Asmgenproof0.return_address_exists; eauto.
- intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply A). intros. subst c0. repeat constructor.
- intros. monadInv H0.
  destruct (zlt Ptrofs.max_unsigned (list_length_z x.(fn_code))); inv EQ0. monadInv EQ.
  rewrite transl_code'_transl_code in EQ0.
  exists x; exists true; split; auto. unfold fn_code.
  constructor. apply (storeind_ptr_label X1 X2 (fn_retaddr_ofs f0) x).
- exact transf_function_no_overflow.
Qed.

(** * Proof of semantic preservation *)

(** Semantic preservation is proved using simulation diagrams
  of the following form.
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant is the [match_states] predicate below, which includes:
- The Asm code pointed by the PC register is the translation of
  the current Mach code sequence.
- Mach register values and Asm register values agree.
*)

Inductive match_stackframe: Mach.stackframe -> stackframe -> Prop :=
| match_sf: forall b ofs sg v c,
    match_stackframe (Mach.Stackframe b sg v ofs c) (Stackframe b sg v ofs)
.

Definition val_of_stackframe (f: Mach.stackframe) :=
  match f with
  | Mach.Stackframe b _ _ ofs _ => Vptr b ofs
  end.

Inductive match_stacks cp : list Mach.stackframe -> stack -> Prop :=
| match_stacks_nil:
      match_stacks cp nil nil
| match_stacks_intra_compartment:
    (* Intra-compartment calls create a new frame in the source, but not the target *)
    forall s s' f,
    match_stacks cp s s' ->
    Mach.call_comp ge (f :: s) = Some cp -> (* meaning, we are staying in the same
                                               compartment *)
    match_stacks cp (f :: s) s'
| match_stacks_cross_compartment:
    (* Cross-compartment calls create a new frame in both the source and the target *)
    forall cp' s s' f f',
    match_stacks cp' s s' ->
    Mach.call_comp ge (f :: s) = Some cp' ->
    call_comp tge (f' :: s') = Some cp' ->
    cp <> cp' ->
    match_stackframe f f' ->
    match_stacks cp (f :: s) (f' :: s')
.

Inductive match_states: Mach.state -> Asm.state -> Prop :=
  | match_states_intro:
      forall s s' fb sp c ep ms m m' rs f tf tc
        (STACKS: match_stack ge s)
        (STACKS': match_stacks (comp_of f) s s')
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m')
        (AT: transl_code_at_pc ge (rs PC) fb f c ep tf tc)
        (AG: agree ms sp rs)
        (DXP: ep = true -> rs#X30 = parent_sp s),
      match_states (Mach.State s fb sp c ms m)
                   (Asm.State s' rs m')
  | match_states_call:
      forall s s' fb ms m m' rs sig cp
        (STACKS: match_stack ge s)
        (STACKS_COMP: Genv.find_comp_of_block ge fb = Some cp)
        (STACKS': match_stacks cp s s')
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = Vptr fb Ptrofs.zero)
        (ATLR: rs RA = parent_ra s),
      match_states (Mach.Callstate s fb sig ms m)
                   (Asm.State s' rs m')
  | match_states_return:
    forall s s' ms m m' rs cp
      (STACKS: match_stack ge s)
      (STACKS': match_stacks cp s s')
      (MEXT: Mem.extends m m')
      (AG: agree ms (parent_sp s) rs)
      (ATPC: rs PC = parent_ra s),
      match_states (Mach.Returnstate s ms m cp)
                   (Asm.ReturnState s' rs m' cp).

Lemma exec_straight_steps:
  forall s s' fb f rs1 i c ep tf tc m1' m2 m2' sp ms2,
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  forall (STACKS: match_stacks (comp_of f) s s'),
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists rs2,
       exec_straight tge tf c rs1 m1' k rs2 m2'
    /\ agree ms2 sp rs2
    /\ (it1_is_parent ep i = true -> rs2#X30 = parent_sp s)) ->
  exists st',
  plus step tge (State s' rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c ms2 m2) st'.
Proof.
  intros. inversion H2. subst. monadInv H7.
  exploit H3; eauto. intros [rs2 [A [B C]]].
  exists (State s' rs2 m2'); split.
  eapply exec_straight_exec; eauto.
  econstructor; eauto.
  eapply exec_straight_at; eauto.
Qed.

Lemma exec_straight_steps_goto:
  forall s s' fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c',
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  it1_is_parent ep i = false ->
  forall (STACKS: match_stacks (comp_of f) s s'),
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight tge tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree ms2 sp rs2
    /\ exec_instr tge tf jmp rs2 m2' (comp_of f) = goto_label tf lbl rs2 m2'
    /\ sig_call jmp = None
    /\ is_return jmp = false) ->
  exists st',
  plus step tge (State s' rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c' ms2 m2) st'.
Proof.
  intros. inversion H3. subst. monadInv H9.
  exploit H5; eauto. intros [jmp [k' [rs2 [A [B [C [D E]]]]]]].
  generalize (functions_transl _ _ _ H7 H8); intro FN.
  generalize (transf_function_no_overflow _ _ H8); intro NOOV.
  exploit exec_straight_steps_2; eauto.
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  inversion AT'; subst.
  exists (State s' rs3 m2'); split.
  eapply plus_right'.
  eapply exec_straight_steps_1; eauto. unfold Genv.find_comp.
  { econstructor. eauto. eauto.
    eapply find_instr_tail. eauto.
    rewrite <- comp_transf_function; eauto.
    rewrite C. eexact GOTO. auto. auto.
    eauto.
    simpl. now rewrite (Genv.find_def_find_comp_of_block _ _ FN).
  }
  traceEq.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
Qed.

Lemma exec_straight_opt_steps_goto:
  forall s s' fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c',
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  it1_is_parent ep i = false ->
  forall (STACKS: match_stacks (comp_of f) s s'),
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight_opt tge tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree ms2 sp rs2
    /\ exec_instr tge tf jmp rs2 m2' (comp_of tf) = goto_label tf lbl rs2 m2'
    /\ sig_call jmp = None
    /\ is_return jmp = false) ->
  exists st',
  plus step tge (State s' rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c' ms2 m2) st'.
Proof.
  intros. inversion H3. subst. monadInv H9.
  exploit H5; eauto. intros [jmp [k' [rs2 [A [B [C [D E]]]]]]].
  generalize (functions_transl _ _ _ H7 H8); intro FN.
  generalize (transf_function_no_overflow _ _ H8); intro NOOV.
  inv A.
- exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  inversion AT'; subst.
  exists (State s' rs3 m2'); split.
  apply plus_one.
  { econstructor. eauto. eauto.
    eapply find_instr_tail. eauto.
    rewrite C. eexact GOTO. auto. auto.
    eauto. simpl. now rewrite (Genv.find_def_find_comp_of_block _ _ FN).
  }
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
- exploit exec_straight_steps_2; eauto.
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  inversion AT'; subst.
  exists (State s' rs3 m2'); split.
  eapply plus_right'.
  eapply exec_straight_steps_1; eauto.
  { econstructor. eauto. eauto.
    eapply find_instr_tail. eauto.
    rewrite C. eexact GOTO. auto. auto.
    eauto. simpl. now rewrite (Genv.find_def_find_comp_of_block _ _ FN).
  }
  traceEq.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
Qed.

(** We need to show that, in the simulation diagram, we cannot
  take infinitely many Mach transitions that correspond to zero
  transitions on the Asm side.  Actually, all Mach transitions
  correspond to at least one Asm transition, except the
  transition from [Machsem.Returnstate] to [Machsem.State].
  So, the following integer measure will suffice to rule out
  the unwanted behaviour. *)

Definition measure (s: Mach.state) : nat :=
  match s with
  | Mach.State _ _ _ _ _ _ => 0%nat
  | Mach.Callstate _ _ _ _ _ => 2%nat
  | Mach.Returnstate _ _ _ _ => 1%nat
  end.

Remark preg_of_not_X30: forall r, negb (mreg_eq r R30) = true -> IR X30 <> preg_of r.
Proof.
  intros. change (IR X30) with (preg_of R30). red; intros.
  exploit preg_of_injective; eauto. intros; subst r; discriminate.
Qed.

Ltac unfold_find_comp A R :=
  rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ R) in A;
  injection A as A.

(** This is the simulation diagram.  We prove it by case analysis on the Mach transition. *)

Theorem step_simulation:
  forall S1 t S2, Mach.step return_address_offset ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS.

- (* Mlabel *)
  left; eapply exec_straight_steps; eauto; intros.
  monadInv TR. econstructor; split. eapply exec_straight_one. simpl; eauto. auto. auto. auto.
  split. apply agree_nextinstr; auto. simpl; congruence.

- (* Mgetstack *)
  unfold load_stack in H.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  inv AT.
  unfold_find_comp CURCOMP FIND.
  rewrite <- CURCOMP in A. setoid_rewrite (comp_transf_function) in A; eauto.
  exploit loadind_correct; eauto with asmgen. intros [rs' [P [Q R]]].
  exists rs'; split. eauto.
  split. eapply agree_set_mreg; eauto with asmgen. congruence.
  simpl; congruence.

- (* Msetstack *)
  unfold store_stack in H.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [A B]].
  left; eapply exec_straight_steps; eauto.
  rewrite (sp_val _ _ _ AG) in A. intros. simpl in TR.
  inv AT.
  unfold_find_comp CURCOMP FIND.
  setoid_rewrite <- CURCOMP in A. setoid_rewrite (comp_transf_function) in A; eauto.
  exploit storeind_correct; eauto with asmgen. intros [rs' [P Q]].
  exists rs'; split. eauto.
  split. eapply agree_undef_regs; eauto with asmgen.
  simpl; intros. rewrite Q; auto with asmgen.

- (* Mgetparam *)
  assert (f0 = f) by congruence; subst f0.
  unfold load_stack in *.
  exploit Mem.loadv_extends. eauto. eexact H0. auto.
  intros [parent' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit lessdef_parent_sp; eauto. clear B; intros B; subst parent'.
  exploit Mem.loadv_extends. eauto. eexact H1. auto.
  intros [v' [C D]].
Opaque loadind.
  left; eapply exec_straight_steps; eauto; intros. monadInv TR. 
  destruct ep.
(* X30 contains parent *)
  exploit loadind_priv_correct. eexact EQ.
  instantiate (2 := rs0). rewrite DXP; eauto.
  congruence.
  intros [rs1 [P [Q R]]].
  exists rs1; split. eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto with asmgen.
  simpl; intros. rewrite R; auto with asmgen.
  apply preg_of_not_X30; auto.
(* GPR11 does not contain parent *)
  rewrite chunk_of_Tptr in A.
  inv AT.
  unfold_find_comp CURCOMP FIND.
  setoid_rewrite <- CURCOMP in A. setoid_rewrite (comp_transf_function) in A; eauto.
  exploit loadind_ptr_correct. eexact A. congruence. intros [rs1 [P [Q R]]].
  exploit loadind_priv_correct. eexact EQ. instantiate (2 := rs1). rewrite Q. eauto. congruence.
  intros [rs2 [S [T U]]].
  exists rs2; split. eapply exec_straight_trans; eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg. eauto. eauto.
  instantiate (1 := rs1#X30 <- (rs2#X30)). intros.
  rewrite Pregmap.gso; auto with asmgen.
  congruence.
  intros. unfold Pregmap.set. destruct (PregEq.eq r' X30). congruence. auto with asmgen.
  simpl; intros. rewrite U; auto with asmgen.
  apply preg_of_not_X30; auto.

- (* Mop *)
  assert (eval_operation tge cp sp op (map rs args) m = Some v).
    rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
    admit. admit. admit.
  exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto.
  eexact H0.
  intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_op_correct; eauto. admit. (* issue with [comp_of] *)
  intros [rs2 [P [Q R]]].
  exists rs2; split. eauto. split. auto.
  apply agree_set_undef_mreg with rs0; auto. 
  apply Val.lessdef_trans with v'; eauto.
  simpl; intros. destruct (andb_prop _ _ H1); clear H1.
  rewrite R; auto. apply preg_of_not_X30; auto.
Local Transparent destroyed_by_op.
  destruct op; simpl; auto; congruence.

- (* Mload *)
  assert (eval_addressing tge cp sp addr (map rs args) = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
    admit. admit. admit.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  inv AT.
  unfold_find_comp CURCOMP FIND.
  setoid_rewrite <- CURCOMP in C. setoid_rewrite (comp_transf_function) in C; eauto.
  subst cp.
  exploit transl_load_correct; eauto. replace (comp_of tf) with (comp_of (Internal f0)). eauto.
  rewrite <- comp_transf_function; eauto. reflexivity.
  intros [rs2 [P [Q R]]].
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto. congruence.
  intros; auto with asmgen.
  simpl; congruence.

- (* Mstore *)
  assert (eval_addressing tge cp sp addr (map rs args) = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
    admit. admit. admit.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [C D]].
  left; eapply exec_straight_steps; eauto.
  inv AT.
  unfold_find_comp CURCOMP FIND.
  setoid_rewrite <- CURCOMP in C. setoid_rewrite (comp_transf_function) in C; eauto.
  subst cp.
  intros. simpl in TR. exploit transl_store_correct; eauto.
  replace (comp_of tf) with (comp_of (Internal f0)). eauto.
  rewrite <- comp_transf_function; eauto. reflexivity.
  intros [rs2 [P Q]].
  exists rs2; split. eauto.
  split. eapply agree_undef_regs; eauto with asmgen.
  simpl; congruence.

- (* Mcall *)
  assert (f0 = f) by congruence.  subst f0.
  inv AT.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  pose proof Genv.find_funct_ptr_match TRANSF _ CALLED as [_ [tf' [TFIND [TTRANSF _]]]].
  destruct ros as [rf|fid]; simpl in H; monadInv H5.
+ (* Indirect call *)
  assert (rs rf = Vptr f' Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
  assert (rs0 x0 = Vptr f' Ptrofs.zero).
    exploit ireg_val; eauto. rewrite H5; intros LD; inv LD; auto.
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  exploit (call_arguments_match (Mach.undef_regs destroyed_at_function_entry rs)); eauto.
  instantiate (1 := (rs0 # PC <- (rs0 x0)) # X1 <- (Val.offset_ptr (rs0 PC) Ptrofs.one)).
  simpl. eapply agree_exten. eapply agree_undef_regs; eauto. intros. Simpl.
  intros [args' [ARGS' LDARGS]].
  destruct ((comp_of (Internal tf) =? comp_of tf')%positive) eqn:Heq.
  * left; econstructor; split.
    apply plus_one. eapply exec_step_internal_call with (args := args').
    rewrite <- H2; simpl; eauto.
    eapply functions_transl; eauto.
    eapply find_instr_tail; eauto.
    simpl; eauto.
    simpl; eauto.
    Simpl; eauto.
    rewrite <- (comp_transl_partial _ H4).
    eapply allowed_call_translated; eauto.
    unfold tge. now rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ TFIND).
    unfold update_stack_call. Simpl.
    rewrite H7; simpl.
    unfold tge.
    rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ TFIND).
    unfold comp_of in *; simpl in *; unfold comp_of in *; now rewrite Heq.
    auto.
    (* Not a cross-compartment call *)
    { unfold Genv.type_of_call; simpl in *.
      unfold comp_of. unfold comp_of in Heq. now setoid_rewrite Heq. }
    { unfold Genv.type_of_call; simpl in *.
      unfold comp_of. unfold comp_of in Heq. now setoid_rewrite Heq. }
    { rewrite <- comp_transf_function; eauto.
      rewrite <- (comp_transl_partial _ TTRANSF); eauto.
      eapply call_trace_lessdef; eauto using senv_preserved, symbols_preserved. }
    reflexivity.
    reflexivity.
    econstructor; eauto.
    econstructor; eauto.
    eapply agree_sp_def; eauto.
    { rewrite find_comp_of_block_translated. unfold tge.
      now rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ TFIND). }
    { Simpl.
      change (comp_of (Internal tf)) with (comp_of tf) in Heq.
      apply Peqb_true_eq in Heq. rewrite <- Heq.
      rewrite <- (comp_transf_function _ _ H4).
      apply match_stacks_intra_compartment; trivial.
      unfold Mach.call_comp. simpl.
      now rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ FIND). }
    simpl.
    assert (agree_undef_caller: forall rs sp rs0 sig,
             agree rs sp rs0 ->
             agree (undef_caller_save_regs_ext rs sig) sp
               (invalidate_call rs0 sig)).
    { clear. intros. admit. }

    (* eapply agree_undef_caller. *) admit. admit.
    (* eapply agree_exten; eauto. intros. Simpl. *)
    Simpl. rewrite <- H2. auto. admit.
  * left; econstructor; split.
    apply plus_one. eapply exec_step_internal_call.
    rewrite <- H2; simpl; eauto.
    eapply functions_transl; eauto.
    eapply find_instr_tail; eauto.
    simpl; eauto.
    simpl; eauto.
    Simpl; eauto.
    rewrite <- (comp_transl_partial _ H4).
    eapply allowed_call_translated; eauto.
    simpl.
    now rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ TFIND).
    unfold update_stack_call. Simpl.
    rewrite H7; simpl.
    simpl.
    unfold tge; rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ TFIND).
    rewrite <- H2. simpl.
    (* replace (comp_of (Internal tf) =? comp_of tf')%positive with false. *)
    (* unfold comp_of in *; simpl in *; unfold comp_of in *; simpl in *. rewrite Heq. *)
    replace (comp_of tf =? comp_of tf')%positive with false.
    reflexivity.
    eauto.
    { simpl. intros. unfold Genv.find_funct_ptr in TFIND.
      destruct (Genv.find_def (Genv.globalenv tprog) f') as [[] |] eqn:?; try congruence.
      inv TFIND.
      exists tf'; split; eauto.
      clear -TTRANSF. unfold transf_fundef in TTRANSF. unfold transf_partial_fundef in TTRANSF.
      destruct fd.
      - monadInv TTRANSF.
        simpl in EQ. monadInv EQ.
        destruct zlt; try congruence. inv EQ1; auto.
        monadInv EQ0; auto.
      - inv TTRANSF; auto. }
    { simpl.
      intros.
      rewrite <- (comp_transl_partial _ H4) in H8.
      rewrite <- (comp_transl_partial _ TTRANSF) in H8.
      specialize (NO_CROSS_PTR H8).
      now eapply Val.lessdef_list_not_ptr; eauto. }
    { simpl. rewrite <- comp_transf_function; eauto.
      rewrite <- (comp_transl_partial _ TTRANSF).
      eapply call_trace_lessdef; eauto using senv_preserved, symbols_preserved. }
    reflexivity. reflexivity.
    econstructor; eauto.
    econstructor; eauto.
    eapply agree_sp_def; eauto.
    { Simpl.
      now rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ CALLED). }
    (* TODO: clean *)
    { eapply match_stacks_cross_compartment. exact STACKS'.
      - unfold Mach.call_comp. simpl.
        now rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ FIND).
      - simpl.
        rewrite <- find_comp_of_block_translated.
        now rewrite (Genv.find_def_find_comp_of_block _ _ H3).
      - rewrite (comp_transl_partial _ TTRANSF).
        rewrite (comp_transl_partial _ H4).
        intros contra. now rewrite contra, Pos.eqb_refl in Heq.
      - erewrite agree_sp; eauto.
        constructor.
    }
    assert (agree_undef_caller: forall rs sp rs0 sig,
             agree rs sp rs0 ->
             agree (undef_caller_save_regs_ext rs sig) sp
               (invalidate_call rs0 sig)).
    { clear. intros. admit. }
    (* eapply agree_undef_caller. admit. *) admit.
    simpl. admit.
    (* eapply agree_exten; eauto. intros. Simpl. *)
    Simpl. rewrite <- H2. auto. admit.
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  exploit (call_arguments_match (Mach.undef_regs destroyed_at_function_entry rs)); eauto.
  instantiate (1 := (rs0 # PC <-
   match Genv.symbol_address tge fid Ptrofs.zero with
   | Vptr b ofs0 =>
       match Genv.find_comp_of_block tge b with
       | Some cp' =>
           if (comp_of tf =? cp')%positive
           then Vptr b ofs0
           else match Genv.find_def tge b with
                | Some (Gfun _) => Vptr b ofs0
                | _ => Vundef
                end
       | None => Vundef
       end
   | _ => Vundef
   end) # X1 <- (Val.offset_ptr (rs0 PC) Ptrofs.one)).
  (* instantiate (1 := (rs0 # PC <- (Genv.symbol_address tge fid Ptrofs.zero)) # X1 <- (Val.offset_ptr (rs0 PC) Ptrofs.one)). *)
  simpl. eapply agree_exten. eapply agree_undef_regs; eauto. intros. Simpl.
  intros [args' [ARGS' LDARGS]].
  destruct (comp_of (Internal tf) =? comp_of tf')%positive eqn:Heq.
  * left; econstructor; split.
    apply plus_one. eapply exec_step_internal_call.
    rewrite <- H2; simpl; eauto.
    eapply functions_transl; eauto.
    eapply find_instr_tail; eauto.
    simpl; eauto.
    simpl; eauto.
    { unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H.
      rewrite <- find_comp_of_block_translated; eauto.
      destruct (Genv.find_comp_of_block ge f') eqn:?.
      destruct (comp_of tf =? c0)%positive; try Simpl; eauto.
      unfold Genv.find_funct_ptr in CALLED.
      pose proof (Genv.find_def_match_2 TRANSF f') as G.
      unfold ge, tge in *. inv G.
      { unfold ge, tge in *.
        rewrite <- H7 in CALLED. try congruence. }
      { inv H8. congruence. rewrite <- H5 in CALLED. congruence. }
      Simpl; eauto. unfold Genv.find_comp_of_block in Heqo.
      unfold Genv.find_funct_ptr in CALLED.
      destruct (Genv.find_def ge f'); try congruence. }
    Simpl; eauto.
    (* unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. eauto. *)
    rewrite <- (comp_transl_partial _ H4).
    eapply allowed_call_translated; eauto.
    simpl.
    now rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ TFIND).
    unfold update_stack_call. Simpl.
    unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H.
    simpl.
    simpl; unfold tge; rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ TFIND).
    unfold comp_of in *; simpl in *. unfold comp_of in *. rewrite Heq.
    simpl; unfold tge; rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ TFIND).
    unfold comp_of in *; simpl in *. unfold comp_of in *. now rewrite Heq.
    eauto.
    (* Not a cross-compartment call *)
    { simpl. intros. unfold Genv.find_funct_ptr in TFIND.
      destruct (Genv.find_def (Genv.globalenv tprog) f') as [[] |] eqn:?;
                                                              try congruence.
      inv TFIND.
      exists tf'; split; eauto.
      clear -TTRANSF. unfold transf_fundef in TTRANSF. unfold transf_partial_fundef in TTRANSF.
      destruct fd.
      - monadInv TTRANSF.
        simpl in EQ. monadInv EQ.
        destruct zlt; try congruence. inv EQ1; auto.
        monadInv EQ0; auto.
      - inv TTRANSF; auto. }
    { unfold Genv.type_of_call; simpl in *.
      unfold comp_of. unfold comp_of in Heq. now setoid_rewrite Heq. }
    { simpl. rewrite <- comp_transf_function; eauto.
      rewrite <- (comp_transl_partial _ TTRANSF).
      eapply call_trace_lessdef; eauto using senv_preserved, symbols_preserved. }
    reflexivity. reflexivity.
    econstructor; eauto.
    econstructor; eauto.
    eapply agree_sp_def; eauto.
    { Simpl.
      now rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ CALLED). }
    { Simpl.
      rewrite (comp_transl_partial _ TTRANSF).
      apply Pos.eqb_eq in Heq. rewrite <- Heq.
      change (comp_of (Internal tf)) with (comp_of tf).
      rewrite <- (comp_transl_partial _ H4).
      apply match_stacks_intra_compartment. exact STACKS'.
      unfold Mach.call_comp. simpl.
      now rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ FIND). }
    assert (agree_undef_caller: forall rs sp rs0 sig,
             agree rs sp rs0 ->
             agree (undef_caller_save_regs_ext rs sig) sp
               (invalidate_call rs0 sig)).
    { clear. intros. admit. }
    admit.
    (* eapply agree_undef_caller. *)
    admit.
    (* simpl. eapply agree_exten; eauto. intros. Simpl. *)
    Simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. eauto.
    Simpl. rewrite <- H2. auto. admit.
  * left; econstructor; split.
    apply plus_one. eapply exec_step_internal_call.
    rewrite <- H2; simpl; eauto.
    eapply functions_transl; eauto.
    eapply find_instr_tail; eauto.
    simpl; eauto.
    simpl; eauto.
    { unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H.
      rewrite <- find_comp_of_block_translated; eauto.
      destruct (Genv.find_comp_of_block ge f') eqn:?.
      destruct (comp_of tf =? c0)%positive; try Simpl; eauto.
      unfold Genv.find_funct_ptr in CALLED.
      pose proof (Genv.find_def_match_2 TRANSF f') as G.
      unfold ge, tge in *. inv G.
      { unfold ge, tge in *.
        rewrite <- H7 in CALLED. try congruence. }
      { inv H8. congruence. rewrite <- H5 in CALLED. congruence. }
      Simpl; eauto. unfold Genv.find_comp_of_block in Heqo.
      unfold Genv.find_funct_ptr in CALLED.
      destruct (Genv.find_def ge f'); try congruence. }
    (* Simpl; eauto. *)
    (* unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. eauto. *)
    rewrite <- (comp_transl_partial _ H4).
    eapply allowed_call_translated; eauto.
    rewrite <- find_comp_of_block_translated.
    now rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ CALLED).
    unfold update_stack_call. Simpl.
    unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H.
    simpl; unfold tge. rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ TFIND).
    replace (comp_of tf =? comp_of tf')%positive with false.
    rewrite <- H2. simpl. admit. eauto.
    { simpl. intros. unfold Genv.find_funct_ptr in TFIND.
      destruct (Genv.find_def (Genv.globalenv tprog) f') as [[] |] eqn:?;
                                                              try congruence.
      inv TFIND.
      exists tf'; split; eauto.
      clear -TTRANSF. unfold transf_fundef in TTRANSF. unfold transf_partial_fundef in TTRANSF.
      destruct fd.
      - monadInv TTRANSF.
        simpl in EQ. monadInv EQ.
        destruct zlt; try congruence. inv EQ1; auto.
        monadInv EQ0; auto.
      - inv TTRANSF; auto. }
    { simpl. intros.
      rewrite <- (comp_transl_partial _ H4) in H5.
      specialize (NO_CROSS_PTR H5).
      now eapply Val.lessdef_list_not_ptr; eauto. }
    { simpl. rewrite <- comp_transf_function; eauto.
      eapply call_trace_lessdef; eauto using senv_preserved, symbols_preserved. }
    reflexivity. reflexivity.
    econstructor; eauto.
    econstructor; eauto.
    eapply agree_sp_def; eauto.
    (* TODO: clean *)
    { Simpl.
      rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ CALLED).
      rewrite (comp_transl_partial _ TTRANSF). reflexivity. }
    { change (comp_of (Internal tf)) with (comp_of tf) in *.
      eapply match_stacks_cross_compartment. exact STACKS'.
      - unfold Mach.call_comp. simpl.
        now rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ FIND).
      - simpl. admit.
      (* - simpl. rewrite <- find_comp_of_block_translated. *)
      (*   now rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ FIND). *)
      - rewrite (comp_transl_partial _ H4).
        intros contra. now rewrite contra, Pos.eqb_refl in Heq.
      - admit. }
      (* - erewrite agree_sp; eauto. *)
      (*   constructor. } *)
    assert (agree_undef_caller: forall rs sp rs0 sig,
             agree rs sp rs0 ->
             agree (undef_caller_save_regs_ext rs sig) sp
               (invalidate_call rs0 sig)).
    { clear. intros. admit. }
    admit.
    (* eapply agree_undef_caller. *)
    admit.
    (* simpl. eapply agree_exten; eauto. intros. Simpl. *)
    Simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. eauto.
    Simpl. rewrite <- H2. auto. admit.

- (* Mtailcall *)
  assert (f0 = f) by congruence.  subst f0.
  inversion AT; subst.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  exploit Mem.loadv_extends. eauto. eexact H1. auto. simpl.
  intros [parent' [A B]].
  destruct ros as [rf|fid]; simpl in H; monadInv H7.
+ (* Indirect call *)
  assert (rs rf = Vptr f' Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
  assert (rs0 x0 = Vptr f' Ptrofs.zero).
    exploit ireg_val; eauto. rewrite H7; intros LD; inv LD; auto.
  exploit make_epilogue_correct; eauto using (comp_transl_partial _ H6).
  intros (rs1 & m1 & U & V & W & X & Y & Z).
  exploit exec_straight_steps_2; eauto using functions_transl.
  intros (ofs' & P & Q).
  left; econstructor; split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor. eexact P. eapply functions_transl; eauto. eapply find_instr_tail. eexact Q.
  reflexivity.
  simpl. reflexivity. eauto. eauto.
  Simpl; eauto.
  rewrite Z by (rewrite <- (ireg_of_eq _ _ EQ1); eauto with asmgen). eauto.
  rewrite <- (comp_transl_partial _ H6).
  now rewrite <- find_comp_of_block_translated, NEXTCOMP.
  traceEq.
  (* match states *)
  econstructor; eauto.
  apply agree_set_other; auto with asmgen.
  Simpl. rewrite Z by (rewrite <- (ireg_of_eq _ _ EQ1); eauto with asmgen). assumption.
+ (* Direct call *)
  exploit make_epilogue_correct; eauto using (comp_transl_partial _ H6).
  intros (rs1 & m1 & U & V & W & X & Y & Z).
  exploit exec_straight_steps_2; eauto using functions_transl.
  intros (ofs' & P & Q).
  left; econstructor; split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor. eexact P. eapply functions_transl; eauto. eapply find_instr_tail. eexact Q.
  reflexivity.
  simpl. reflexivity. eauto. eauto.
  Simpl; eauto.
  unfold Genv.symbol_address. admit.
  (* now rewrite symbols_preserved, H. *)
  rewrite <- (comp_transl_partial _ H6).
  simpl. admit.
  (* now rewrite <- find_comp_of_block_translated. *)
  traceEq.
  (* match states *)
  econstructor; eauto.
  apply agree_set_other; auto with asmgen.
  apply agree_set_other; auto with asmgen.
  Simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. auto.
  admit.

- (* Mbuiltin *)
  inv AT. monadInv H4.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H3); intro NOOV.
  exploit (@builtin_args_match Mach.fundef _
                               (@has_comp_fundef _ Mach.has_comp_function)
             ge); eauto. intros [vargs' [P Q]].
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  left. econstructor; split. apply plus_one.
  eapply exec_step_builtin. eauto. eauto.
  eapply find_instr_tail; eauto.
  erewrite <- sp_val by eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  admit. admit. admit.
  rewrite <- (comp_transl_partial _ H3). replace (comp_of f) with (comp_of ef).
  eauto. { admit. }
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  rewrite <- (comp_transl_partial _ H3).
  unfold_find_comp CURCOMP FIND. rewrite <- CURCOMP. reflexivity.
  eauto. eauto.
  econstructor; eauto.
  instantiate (2 := tf); instantiate (1 := x).
  unfold nextinstr. rewrite Pregmap.gss.
  rewrite set_res_other. rewrite undef_regs_other_2.
  rewrite ! Pregmap.gso by congruence.
  rewrite <- H1. simpl. econstructor; eauto.
  eapply code_tail_next_int; eauto.
  rewrite preg_notin_charact. intros. auto with asmgen.
  auto with asmgen.
  apply agree_nextinstr. eapply agree_set_res; auto.
  eapply agree_undef_regs; eauto. intros. rewrite undef_regs_other_2; auto.
  rewrite ! Pregmap.gso; auto with asmgen.
  congruence.

- (* Mgoto *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H4.
  exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
  exploit functions_transl; eauto. intro FN.
  left. inversion AT2; subst. exists (State s' rs' m'); split.
  apply plus_one. econstructor; eauto.
  eapply find_instr_tail; eauto.
  simpl; eauto. eauto. eauto.
  simpl; unfold Genv.find_comp; simpl.
  now rewrite (Genv.find_def_find_comp_of_block _ _ FN).
  econstructor; eauto.
  eapply agree_exten; eauto with asmgen.
  congruence.

- (* Mcond true *)
  assert (f0 = f) by congruence. subst f0.
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_opt_steps_goto; eauto.
  intros. simpl in TR.
  exploit transl_cbranch_correct_true; eauto. intros (rs' & jmp & A & B & C & D & E).
  exists jmp; exists k; exists rs'.
  split. eexact A. 
  split. apply agree_exten with rs0; auto with asmgen.
  split. eexact B. auto.

- (* Mcond false *)
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  exploit transl_cbranch_correct_false; eauto. intros (rs' & A & B).
  exists rs'.
  split. eexact A.
  split. apply agree_exten with rs0; auto with asmgen.
  simpl. congruence.

- (* Mjumptable *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H6.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H5); intro NOOV.
  exploit find_label_goto_label. eauto. eauto.
  instantiate (2 := rs0#X5 <- Vundef #X31 <- Vundef).
  Simpl. eauto.
  eauto.
  intros [tc' [rs' [A [B C]]]].
  exploit ireg_val; eauto. rewrite H. intros LD; inv LD.
  left; econstructor; split.
  assert (exists ofs, rs' PC = Vptr fb ofs) as [ofs' Hptr]. {
    destruct (rs' PC); inversion B.
    eauto.
  }
  apply plus_one. econstructor. eauto. eauto.
  eapply find_instr_tail; eauto.
  simpl. rewrite <- H9. unfold Mach.label in H0; unfold label; rewrite H0.
  eexact A. eauto. eauto. eauto.
  simpl; unfold Genv.find_comp; simpl.
  now rewrite (Genv.find_def_find_comp_of_block _ _ FN).

  assert (exists ofs, rs' PC = Vptr fb ofs) as [ofs' Hptr]. {
    destruct (rs' PC); inversion B.
    eauto.
  }
  econstructor; eauto.
  eapply agree_undef_regs; eauto.
  simpl. intros. rewrite C; auto with asmgen. Simpl.
  congruence.

- (* Mreturn *)
  assert (f0 = f) by congruence. subst f0.
  inversion AT; subst. simpl in H6; monadInv H6.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
  { eapply transf_function_no_overflow; eauto. }
  exploit make_epilogue_correct; eauto using (comp_transf_function _ _ H5).
  intros (rs1 & m1 & U & V & W & X & Y & Z).
  exploit exec_straight_steps_2; eauto using functions_transl.

  intros (ofs' & P & Q).
  left; econstructor; split.
  eapply plus_star_trans.
  eapply exec_straight_exec; eauto.
  eapply star_step. eapply exec_step_internal_return; eauto.
  eapply functions_transl; eauto. eapply find_instr_tail. eexact Q.
  simpl. reflexivity. eauto.
  econstructor. traceEq. traceEq.
  rewrite <- (comp_transl_partial _ H5).
  econstructor; eauto.
  rewrite X; simpl; Simpl; eauto.

  apply agree_set_other; auto with asmgen.
  (* { (* An easy lemma to add: more case analysis, but we undefine more so the *)
  (*      constructor takes care of the case that is not covered by the assumption *)
  (*      in the context *) *)
  (*   inv V. constructor; auto. *)
  (*   intros r. specialize (agree_mregs r). unfold undef_non_return_regs_ext. *)
  (*   destruct (LTL.in_mreg r (regs_of_rpair (loc_result (parent_signature s)))); auto. } *)

- (* internal function *)
  unfold Genv.find_funct_ptr in H.
  destruct (Genv.find_def ge fb) as [[] |] eqn:?; try congruence.
  injection H; intros ->.
  exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
  generalize EQ; intros EQ'. monadInv EQ'.
  destruct (zlt Ptrofs.max_unsigned (list_length_z x0.(fn_code))); inversion EQ1. clear EQ1. subst x0.
  unfold store_stack in *.
  exploit Mem.alloc_extends. eauto. eauto. apply Z.le_refl. apply Z.le_refl.
  intros [m1' [C D]].
  exploit Mem.storev_extends. eexact D. eexact H1. eauto. eauto.
  intros [m2' [F G]].
  simpl chunk_of_type in F.
  exploit Mem.storev_extends. eexact G. eexact H2. eauto. eauto.
  intros [m3' [P Q]].
  (* Execution of function prologue *)
  monadInv EQ0. rewrite transl_code'_transl_code in EQ1.
  set (tfbody := Pallocframe (fn_stacksize f) (fn_link_ofs f) ::
                 storeind_ptr RA SP (fn_retaddr_ofs f) x0) in *.
  set (tf := {| fn_sig := Mach.fn_sig f; fn_code := tfbody |}) in *.
  set (rs2 := nextinstr (rs0#X30 <- (parent_sp s) #SP <- sp #X31 <- Vundef)).
  exploit (storeind_ptr_correct tge tf SP (fn_retaddr_ofs f) RA x0 rs2 m2').
    rewrite chunk_of_Tptr in P. change (rs2 X1) with (rs0 X1). rewrite ATLR.
    change (rs2 X2) with sp. eexact P.
    congruence. congruence.
  intros (rs3 & U & V).
  assert (EXEC_PROLOGUE:
            exec_straight tge tf
              tf.(fn_code) rs0 m'
              x0 rs3 m3').
  { change (fn_code tf) with tfbody; unfold tfbody.
    eapply exec_straight_step with rs2 m2'.
    unfold exec_instr.
    change (comp_of tf) with (comp_of f).
    change (comp_of (Internal f)) with (comp_of f) in *.
    rewrite C. fold sp.
    rewrite <- (sp_val _ _ _ AG). rewrite chunk_of_Tptr in F. rewrite F. reflexivity.
    reflexivity. reflexivity. reflexivity.
    eexact U. }
  exploit exec_straight_steps_2; eauto using functions_transl. lia. constructor.
  intros (ofs' & X & Y).
  left; eexists; split.
  eapply exec_straight_steps_1; eauto. lia. simpl. constructor.
  econstructor; eauto.
  erewrite (Genv.find_def_find_comp_of_block _ _ Heqo) in STACKS_COMP.
  injection STACKS_COMP. intros. subst cp. eauto.
  unfold Genv.find_funct_ptr; rewrite Heqo; eauto.
  (* unfold_find_comp STACKS_COMP H. now subst cp. *)
  rewrite X; econstructor; eauto.
  apply agree_exten with rs2; eauto with asmgen.
  unfold rs2.
  apply agree_nextinstr. apply agree_set_other; auto with asmgen.
  apply agree_change_sp with (parent_sp s).
  apply agree_undef_regs with rs0. auto.
(*   { unfold undef_caller_save_regs_ext. *)
(*     inv AG. constructor; auto. *)
(*     intros r. specialize (agree_mregs r). *)
(*     destruct (LTL.in_mreg r (LTL.parameters_mregs sig)); *)
(*     auto. } *)
(* Local Transparent destroyed_at_function_entry. *)
  simpl; intros; Simpl.
  unfold sp; congruence.
  intros. rewrite V by auto with asmgen. reflexivity.

- (* external function *)
  unfold Genv.find_funct_ptr in H; destruct (Genv.find_def ge fb) as [[] |] eqn:G;
    try congruence.
  inv H.
  exploit functions_translated; eauto.
  intros [tf [A B]]. simpl in B. inv B.
  exploit extcall_arguments_match; eauto.
  intros [args' [C D]].
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [P [Q [R S]]]]].

  left; econstructor; split.
  apply plus_one. eapply exec_step_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  rewrite (Genv.find_def_find_comp_of_block _ _ G) in STACKS_COMP; injection STACKS_COMP as STACKS_COMP.
  subst cp.
  econstructor; eauto.
  Simpl. rewrite ATLR. eauto.
  eapply agree_set_other; eauto.
  eapply agree_set_pair; eauto. eapply agree_undef_caller_save_regs; eauto.

- inv STACKS.
  assert (exists s'', update_stack_return tge s' cp rs0 = Some s'' /\
         match_stacks (comp_of f0) s s'') as [s'' [Hs''1 Hs''2]].
  { unfold update_stack_return.
    rewrite ATPC in *. simpl in *.
    rewrite <- find_comp_of_block_translated.
    rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ H3).
    change (comp_of (Internal f0)) with (comp_of f0).
    destruct (cp =? comp_of f0)%positive eqn:e.
    - apply Pos.eqb_eq in e. subst cp.
      eexists; split; auto.
      inv STACKS'; auto.
      unfold Mach.call_comp in *; simpl in *.
      rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ H3) in H2.
      change (comp_of (Internal f0)) with (comp_of f0) in *.
      congruence.
    - inv STACKS'; auto.
      + unfold Mach.call_comp in *. simpl in *.
        rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ H3) in H4.
        injection H4 as E. subst cp.
        now rewrite Pos.eqb_refl in e.
      + unfold Mach.call_comp in *. simpl in *.
        rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ H3) in H2.
        injection H2 as E. subst cp'0. eauto.
  }

  left. eexists (State s'' (invalidate_return rs0 (sig_of_call s')) m'). split.
  assert (LD: Val.lessdef (Mach.return_value rs sg) (return_value rs0 sg)).
  { unfold Mach.return_value, return_value.
    destruct (loc_result sg).
    - eapply agree_mregs; eauto.
    - eapply Val.longofwords_lessdef.
      eapply agree_mregs; eauto.
      eapply agree_mregs; eauto. }
  eapply plus_one.
  econstructor; eauto.
  rewrite ATPC. unfold Vnullptr. now destruct Archi.ptr64.
  rewrite ATPC. simpl. congruence.
  { rewrite ATPC. simpl. rewrite <- find_comp_of_block_translated.
    eauto. }
  { rewrite ATPC. simpl.
    intros diff.
    inv STACKS'; auto.
    - simpl in *. subst. unfold Mach.call_comp in *. simpl in *. congruence.
    - inv H10. reflexivity. }
  { intros diff.
    inv STACKS'; auto.
    - simpl in *. subst. unfold Mach.call_comp in *. simpl in *.
      congruence.
    - inv H10. eapply agree_sp; eauto. }
  { intros TYPE.
    inv STACKS'; auto.
    - simpl in *. subst. unfold Mach.call_comp in *. simpl in *.
      assert (cp' = cp) by congruence. subst cp'.
      now eapply Genv.type_of_call_same_cp in TYPE.
    - simpl in *. subst. unfold Mach.call_comp in *. simpl in *.
      inv H10.
      specialize (NO_CROSS_PTR TYPE).
      (* TODO: factorize into a lemma Val.lessdef_not_ptr *)
      inv LD; auto. now rewrite <- H0 in NO_CROSS_PTR. }
  { inv STACKS'; auto.
    - simpl in *. subst. unfold Mach.call_comp in *. simpl in *.
      rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ H3) in H4.
      change (comp_of (Internal f0)) with (comp_of f0) in *.
      injection H4 as <-.
      rewrite (Genv.find_funct_ptr_find_comp_of_block _ _ H3) in CURCOMP.
      injection CURCOMP as <-.
      assert (t = E0).
      { inv EV; auto.
        exfalso. eapply Genv.type_of_call_same_cp. eauto. }
      subst. constructor. now apply Genv.type_of_call_same_cp.
    - simpl in *. unfold Mach.call_comp in *. simpl in *.
      inv H10.
      eapply return_trace_lessdef with (ge := ge) (v := Mach.return_value rs sg);
        eauto using senv_preserved. }
  admit.

  econstructor; eauto.
  { rewrite invalidate_return_PC. rewrite ATPC in *. eauto. }
  { admit. }
  easy.

Admitted.

Lemma transf_initial_states:
  forall st1, Mach.initial_state prog st1 ->
  exists st2, Asm.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. unfold ge0 in *.
  destruct (Genv.find_symbol_find_def_inversion _ _ H1)
    as [main_def find_main].
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_transf_partial TRANSF); eauto.
  replace (Genv.symbol_address (Genv.globalenv tprog) (prog_main tprog) Ptrofs.zero)
     with (Vptr fb Ptrofs.zero).
  econstructor; eauto.
  constructor.
  unfold Genv.find_comp_of_block, ge. rewrite find_main. eauto.

  constructor.
  apply Mem.extends_refl.
  split. auto. simpl. unfold Vnullptr; destruct Archi.ptr64; congruence.
  intros. rewrite Regmap.gi. auto.
  unfold Genv.symbol_address.
  rewrite (match_program_main TRANSF).
  rewrite symbols_preserved.
  unfold ge; rewrite H1. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> Mach.final_state st1 r -> Asm.final_state tprog st2 r.
Proof.
  intros. inv H0. inv H.
  - inv STACKS'.
    constructor. auto.
    compute in H1. inv H1.
    generalize (preg_val _ _ _ R10 AG). rewrite H2. intros LD; inv LD. auto.
Qed.

Theorem transf_program_correct:
  forward_simulation (Mach.semantics return_address_offset prog) (Asm.semantics tprog).
Proof.
  eapply forward_simulation_star with (measure := measure).
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact step_simulation.
Qed.

End PRESERVATION.
