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

Instance comp_transf_function: has_comp_transl_partial transf_function.
Proof.
  unfold transf_function, transl_function.
  intros f ? H; monadInv H; trivial.
  destruct transl_code'; simpl in *; try easy.
  inv EQ. destruct zlt; try easy.
  now inv EQ0.
Qed.

Instance external_transf_fundef: is_external_transl_partial transf_fundef.
Proof.
  unfold transf_fundef, transf_function, transl_function.
  intros [f | ef] ? ? H; monadInv H; trivial.
  destruct transl_code'; simpl in *; try easy.
  reflexivity.
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
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSF).

Lemma find_comp_translated:
  forall vf,
    Genv.find_comp ge vf = Genv.find_comp tge vf.
Proof.
  eapply (Genv.find_comp_transf_partial TRANSF).
Qed.

Lemma find_comp_ignore_offset_translated:
  forall vf,
    Genv.find_comp_ignore_offset ge vf = Genv.find_comp_ignore_offset tge vf.
Proof.
  unfold Genv.find_comp_ignore_offset.
  intros. destruct vf; auto. now rewrite find_comp_translated.
Qed.

Lemma functions_transl:
  forall fb f tf,
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transf_function f = OK tf ->
  Genv.find_funct_ptr tge fb = Some (Internal tf).
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

Lemma type_of_call_translated:
  forall cp cp',
    Genv.type_of_call ge cp cp' = Genv.type_of_call tge cp cp'.
Proof.
  intros cp cp'.
  eapply Genv.match_genvs_type_of_call.
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
  plus (step comp_of_main) tge (State st rs m) E0 (State st rs' m').
Proof.
  intros. inv H.
  eapply exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  unfold Genv.find_comp.
  simpl; erewrite functions_transl; eauto.
  destruct Ptrofs.eq_dec; try congruence; reflexivity.
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
  Genv.find_funct_ptr ge b = Some (Internal f) ->
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
| match_sf: forall b ofs cp sg v c,
    match_stackframe (Mach.Stackframe b cp sg v ofs c) (Stackframe b cp sg v ofs)
.

Definition val_of_stackframe (f: Mach.stackframe) :=
  match f with
  | Mach.Stackframe b _ _ _ ofs _ => Vptr b ofs
  end.

(* How are the source and target stack related? *)
(* There is no reason to inspect the current RA or SP in the source, because they
   can be modified. *)
(* Inductive match_stacks: val -> list Mach.stackframe -> stack -> Prop := *)
(* | match_stacks_nil: *)
(*     forall pc, *)
(*       Genv.find_comp_ignore_offset ge pc = default_compartment -> *)
(*       match_stacks pc nil nil *)
(* | match_stacks_intra_compartment: *)
(*     (* Intra-compartment calls create a new frame in the source, not the target *) *)
(*     forall newpc pc s s' f, *)
(*     match_stacks pc s s' -> *)
(*     (* TODO: define function [callee_comp] but for stackframes and use it there *) *)
(*     Genv.find_comp_ignore_offset ge newpc = callee_comp s' -> *)
(*     Genv.find_comp_ignore_offset ge (val_of_stackframe f) = Genv.find_comp_ignore_offset ge pc -> *)
(*     Genv.find_comp_ignore_offset ge (val_of_stackframe f) = Genv.find_comp_ignore_offset ge newpc -> *)
(*     (* no condition on the frame *) *)
(*     match_stacks newpc (f :: s) s' *)
(* | match_stacks_cross_compartment: *)
(*     (* Cross-compartment calls create a new frame in both the source and the target *) *)
(*     forall newpc pc s s' f f', *)
(*     match_stacks pc s s' -> *)
(*     Genv.find_comp_ignore_offset ge newpc = callee_comp (f' :: s') -> *)
(*     Genv.find_comp_ignore_offset ge (val_of_stackframe f) = Genv.find_comp_ignore_offset ge pc -> *)
(*     Genv.find_comp_ignore_offset ge (val_of_stackframe f) <> Genv.find_comp_ignore_offset ge newpc -> *)
(*     match_stackframe f f' -> *)
(*     match_stacks newpc (f :: s) (f' :: s') *)
(* . *)

Inductive match_stacks: list Mach.stackframe -> stack -> Prop :=
| match_stacks_nil:
      match_stacks nil nil
| match_stacks_intra_compartment:
    (* Intra-compartment calls create a new frame in the source, not the target *)
    forall s s' f,
    match_stacks s s' ->
    Mach.call_comp ge (f :: s) = Mach.callee_comp comp_of_main (f :: s) -> (* meaning, we are staying in the same
                                                            compartment *)
    Mach.callee_comp comp_of_main (f :: s) = Mach.callee_comp comp_of_main s ->
    match_stacks (f :: s) s'
| match_stacks_cross_compartment:
    (* Cross-compartment calls create a new frame in both the source and the target *)
    forall s s' f f',
    match_stacks s s' ->
    Mach.call_comp ge (f :: s) <> Mach.callee_comp comp_of_main (f :: s) ->
    Mach.callee_comp comp_of_main (f :: s) <> Mach.callee_comp comp_of_main s ->
    Mach.call_comp ge (f :: s) = Mach.callee_comp comp_of_main s ->
    match_stackframe f f' ->
    match_stacks (f :: s) (f' :: s')
.

Lemma match_stacks_callee:
  forall s s',
    match_stacks s s' ->
    Mach.callee_comp comp_of_main s = callee_comp comp_of_main s'.
Proof.
  intros. induction H.
  - reflexivity.
  - congruence.
  - now inv H3; auto.
Qed.

(* Lemma match_stacks_xx: *)
(*   forall s s', *)
(*     match_stacks s s' -> *)
(*     Mach.call_comp ge s = call_comp tge s'. *)
(* Proof. *)
(*   intros. induction H; unfold Mach.call_comp; simpl. *)
(*   - unfold Vnullptr; destruct Archi.ptr64; auto. *)
(*   - unfold Mach.call_comp in *. simpl in *. *)
(*     destruct f; simpl in *.  *)
(*   reflexivity. *)

(* Inductive match_stacks: list Mach.stackframe -> stack -> Prop := *)
(* | match_stacks_nil: *)
(*     match_stacks nil nil *)
(* | match_stacks_intra_compartment: *)
(*     (* Intra-compartment calls create a new frame in the source, not the target *) *)
(*     forall s s' b v ofs c, *)
(*     match_stacks s s' -> *)
(*     Genv.find_comp ge (Vptr b Ptrofs.zero) = Mach.call_comp ge s -> *)
(*     match_stacks (Mach.Stackframe b (Genv.find_comp ge (Vptr b Ptrofs.zero)) v ofs c :: s) s' *)
(* | match_stacks_cross_compartment: *)
(*     (* Cross-compartment calls create a new frame in both the source and the target *) *)
(*     forall s s' f f', *)
(*     match_stacks s s' -> *)
(*     Genv.find_comp_ignore_offset ge (val_of_stackframe f) <> Mach.callee_comp f -> *)
(*     match_stackframe f f' -> *)
(*     match_stacks (f :: s) (f' :: s') *)
(* . *)

(* Lemma match_stacks_same_compartment: *)
(*   forall newpc pc s s', *)
(*   match_stacks pc s s' -> *)
(*   Genv.find_comp_ignore_offset ge pc = Genv.find_comp_ignore_offset ge newpc -> *)
(*   match_stacks newpc s s'. *)
(* Proof. *)
(*   intros newpc pc s s' H; revert newpc. *)
(*   induction H. *)
(*   - intros. constructor. congruence. *)
(*   - intros. *)
(*     eapply match_stacks_intra_compartment; auto. *)
(*     congruence. congruence. *)
(*   - intros. *)
(*     eapply match_stacks_cross_compartment; auto. *)
(*     congruence. congruence. *)
(* Qed. *)

Inductive match_states: Mach.state -> Asm.state -> Prop :=
  | match_states_intro:
      forall s s' fb sp c ep ms m m' rs f tf tc
        (STACKS: match_stack ge s)
        (STACKS': match_stacks s s')
        (STACKS_COMP: Genv.find_comp_ignore_offset ge (rs PC) = callee_comp comp_of_main s')
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m')
        (AT: transl_code_at_pc ge (rs PC) fb f c ep tf tc)
        (AG: agree ms sp rs)
        (DXP: ep = true -> rs#X30 = parent_sp s),
      match_states (Mach.State s fb sp c ms m)
                   (Asm.State s' rs m')
  | match_states_call:
      forall s s' fb ms m m' rs sig
        (STACKS: match_stack ge s)
        (STACKS': match_stacks s s')
        (STACKS_COMP: Genv.find_comp_ignore_offset ge (rs PC) = callee_comp comp_of_main s')
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp s) rs)
        (ATPC: rs PC = Vptr fb Ptrofs.zero)
        (ATLR: rs RA = parent_ra s),
      match_states (Mach.Callstate s fb sig ms m)
                   (Asm.State s' rs m')
  | match_states_return:
    forall s s' ms m m' rs
      (STACKS: match_stack ge s)
      (STACKS': match_stacks s s')
      (STACKS_COMP: Genv.find_comp_ignore_offset ge (rs PC) = Mach.call_comp ge s)
      (MEXT: Mem.extends m m')
      (AG: agree ms (parent_sp s) rs)
      (ATPC: rs PC = parent_ra s),
      match_states (Mach.Returnstate s ms m)
                   (Asm.ReturnState s' rs m').

Lemma exec_straight_steps:
  forall s s' fb f rs1 i c ep tf tc m1' m2 m2' sp ms2,
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  forall (STACKS: match_stacks s s'),
  forall (STACKS_COMP: Genv.find_comp_ignore_offset ge (rs1 PC) = callee_comp comp_of_main s'),
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists rs2,
       exec_straight tge tf c rs1 m1' k rs2 m2'
    /\ agree ms2 sp rs2
    /\ (it1_is_parent ep i = true -> rs2#X30 = parent_sp s)) ->
  exists st',
  plus (step comp_of_main) tge (State s' rs1 m1') E0 st' /\
  match_states (Mach.State s fb sp c ms2 m2) st'.
Proof.
  intros. inversion H2. subst. monadInv H7.
  exploit H3; eauto. intros [rs2 [A [B C]]].
  exists (State s' rs2 m2'); split.
  eapply exec_straight_exec; eauto.
  econstructor; eauto.
  rewrite <- STACKS_COMP.
  { clear -A H4.
    rename H4 into PTR. revert fb ofs PTR.
    induction A; intros.
    - rewrite H2, <- PTR.
      now simpl.
    - erewrite IHA; rewrite H2, <- PTR; now simpl. }
  (* { clear -A STACKS. *)
  (*   induction A. *)
  (*   - rewrite H2. *)
  (*     eapply match_stacks_same_compartment; eauto. *)
  (*     now destruct (rs1 PC). *)
  (*   - eapply IHA. rewrite H2. *)
  (*     eapply match_stacks_same_compartment; eauto. *)
  (*     now destruct (rs1 PC). *)
  (* } *)
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
  forall (STACKS: match_stacks (* (rs1 PC) *) s s'),
  forall (STACKS_COMP: Genv.find_comp_ignore_offset ge (rs1 PC) = callee_comp comp_of_main s'),
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight tge tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree ms2 sp rs2
    /\ exec_instr tge tf jmp rs2 m2' (comp_of f) = goto_label tf lbl rs2 m2'
    /\ sig_call jmp = None
    /\ is_return jmp = false) ->
  exists st',
  plus (step comp_of_main) tge (State s' rs1 m1') E0 st' /\
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
  simpl; erewrite functions_transl; eauto. destruct Ptrofs.eq_dec; try congruence; reflexivity.
  { econstructor. eauto. eauto.
    eapply find_instr_tail. eauto.
    reflexivity.
    rewrite <- comp_transf_function; eauto.
    rewrite C. eexact GOTO. auto. auto.
    eauto.
    simpl. unfold Genv.find_comp; simpl; destruct Ptrofs.eq_dec; try congruence. now rewrite FN.
  }
  traceEq.
  econstructor; eauto.
  { rewrite <- H9. rewrite <- H6 in STACKS_COMP.
    now simpl in *. }
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
  forall (STACKS: match_stacks (* (rs1 PC) *) s s'),
  forall (STACKS_COMP: Genv.find_comp_ignore_offset ge (rs1 PC) = callee_comp comp_of_main s'),
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight_opt tge tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree ms2 sp rs2
    /\ exec_instr tge tf jmp rs2 m2' (comp_of tf) = goto_label tf lbl rs2 m2'
    /\ sig_call jmp = None
    /\ is_return jmp = false) ->
  exists st',
  plus (step comp_of_main) tge (State s' rs1 m1') E0 st' /\
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
    reflexivity.
    rewrite C. eexact GOTO. auto. auto.
    eauto. simpl. unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence. now rewrite FN.
  }
  econstructor; eauto.
  { rewrite <- H9. rewrite <- H6 in STACKS_COMP.
    now simpl in *. }
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
  unfold Genv.find_comp. simpl. rewrite FN. destruct Ptrofs.eq_dec; try congruence. reflexivity.
  { econstructor. eauto. eauto.
    eapply find_instr_tail. eauto.
    reflexivity.
    rewrite C. eexact GOTO. auto. auto.
    eauto. simpl. unfold Genv.find_comp; simpl; destruct Ptrofs.eq_dec; try congruence. now rewrite FN.
  }
  traceEq.
  econstructor; eauto.
  { rewrite <- H11. rewrite <- H6 in STACKS_COMP.
    now simpl in *. }
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
  | Mach.Returnstate _ _ _ => 1%nat
  end.

Remark preg_of_not_X30: forall r, negb (mreg_eq r R30) = true -> IR X30 <> preg_of r.
Proof.
  intros. change (IR X30) with (preg_of R30). red; intros.
  exploit preg_of_injective; eauto. intros; subst r; discriminate.
Qed.

(** This is the simulation diagram.  We prove it by case analysis on the Mach transition. *)

Theorem step_simulation:
  (* forall S1 t S2, Mach.step return_address_offset ge S1 t S2 -> *)
  (* forall S1' (MS: match_states S1 S1'), *)
  (* exists S3, *)
  (*     star (Mach.step return_address_offset) ge S2 E0 S3 *)
  (*  /\ ((exists S2', plus step tge S1' t S2' /\ match_states S3 S2') *)
  (*     \/ (exists S2', star step tge S1' t S2' /\ measure S3 < measure S1 /\ match_states S3 S2'))%nat. *)

  (* forall S1 t S2, Mach.step return_address_offset ge S1 t S2 -> *)
  (* forall S1' (MS: match_states S1 S1'), *)
  (* exists S3 S2', *)
  (*     star (Mach.step return_address_offset) ge S2 E0 S3 *)
  (*  /\ (plus step tge S1' t S2' \/ (star step tge S1' t S2' /\ measure S3 < measure S1))%nat *)
  (*  /\ match_states S3 S2'. *)

  forall S1 t S2, Mach.step return_address_offset ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus (step comp_of_main) tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.

  (* forall s1 t s1', Step L1 s1 t s1' -> *)
  (* forall s2, match_states s1 s2 -> *)
  (* exists s1'' s2', Star L1 s1' E0 s1'' /\ Plus L2 s2 t s2' /\ match_states s1'' s2'. *)

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
  (* unfold find_comp_ptr in CURCOMP. rewrite FIND in CURCOMP. inv CURCOMP. *)
  Ltac unfold_find_comp A R :=
    unfold Genv.find_comp in A; simpl in A; rewrite R in A; destruct Ptrofs.eq_dec; try congruence.
  unfold_find_comp A FIND.
  unfold comp_of in A; simpl in A. erewrite (comp_transf_function) in A; eauto.
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
  unfold_find_comp A FIND.
  unfold comp_of in A; simpl in A. erewrite (comp_transf_function) in A; eauto.
  exploit storeind_correct; eauto with asmgen. intros [rs' [P Q]].
  exists rs'; split. eauto.
  split. eapply agree_undef_regs; eauto with asmgen.
  simpl; intros. rewrite Q; auto with asmgen.

- (* Mgetparam *)
  assert (f0 = f) by congruence; subst f0.
  (* assert (cp = comp_of f). *)
  (* unfold find_comp_ptr in CURCOMP. rewrite FIND in CURCOMP. inv CURCOMP. *)
  (* reflexivity. subst. *)
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
  unfold_find_comp A FIND.
  unfold comp_of in A; simpl in A. erewrite (comp_transf_function) in A; eauto.
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
  assert (eval_operation tge sp op (map rs args) m = Some v).
    rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
  exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. eexact H0.
  intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_op_correct; eauto. intros [rs2 [P [Q R]]].
  exists rs2; split. eauto. split. auto.
  apply agree_set_undef_mreg with rs0; auto. 
  apply Val.lessdef_trans with v'; auto.
  simpl; intros. destruct (andb_prop _ _ H1); clear H1.
  rewrite R; auto. apply preg_of_not_X30; auto.
Local Transparent destroyed_by_op.
  destruct op; simpl; auto; congruence.

- (* Mload *)
  assert (eval_addressing tge sp addr (map rs args) = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  inv AT.
  unfold_find_comp C FIND.
  unfold comp_of in C; simpl in C. erewrite (comp_transf_function) in C; eauto.
  exploit transl_load_correct; eauto. intros [rs2 [P [Q R]]].
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto. congruence.
  intros; auto with asmgen.
  simpl; congruence.

- (* Mstore *)
  assert (eval_addressing tge sp addr (map rs args) = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [C D]].
  left; eapply exec_straight_steps; eauto.
  inv AT.
  unfold_find_comp C FIND.
  unfold comp_of in C; simpl in C. erewrite (comp_transf_function) in C; eauto.
  intros. simpl in TR. exploit transl_store_correct; eauto. intros [rs2 [P Q]].
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
    simpl. unfold Genv.find_comp, Genv.find_funct. rewrite (functions_transl _ _ _ FIND H4).
    destruct Ptrofs.eq_dec; try congruence; reflexivity.
    unfold update_stack_call. Simpl.
    rewrite H7; simpl. unfold Genv.find_comp, Genv.find_funct.
    unfold tge; rewrite TFIND. destruct Ptrofs.eq_dec; try congruence.
    unfold comp_of in *; simpl in *. now rewrite Heq.
    auto.
    (* Not a cross-compartment call *)
    { unfold Genv.type_of_call; simpl in *.
      unfold tge. unfold Genv.find_comp; simpl. rewrite TFIND. unfold comp_of in Heq. simpl in Heq.
      destruct Ptrofs.eq_dec; try congruence.
      unfold comp_of. unfold comp_of in Heq. now rewrite Heq. }
    { simpl.
      rewrite <- find_comp_translated, <- comp_transf_function; eauto.
      eapply call_trace_lessdef; eauto using senv_preserved, symbols_preserved. }
    econstructor; eauto.
    econstructor; eauto.
    eapply agree_sp_def; eauto.
    { (* replace (Genv.find_comp ge (Vptr f' Ptrofs.zero)) with *)
      (*   (Genv.find_comp ge (Vptr fb Ptrofs.zero)). *)
      Simpl.
      apply match_stacks_intra_compartment. exact STACKS'.
      - unfold Mach.call_comp. simpl.
        unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence.
        rewrite FIND, CALLED.
        rewrite (comp_transl_partial _ TTRANSF).
        unfold comp_of in *; simpl in *.
        rewrite (comp_transf_function _ _ H4).
        apply Peqb_true_eq in Heq. now rewrite Heq.
      - simpl. erewrite match_stacks_callee; eauto.
        rewrite <- STACKS_COMP. rewrite <- H2. simpl.
        unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence.
        rewrite FIND, CALLED.
        rewrite (comp_transl_partial _ TTRANSF).
        unfold comp_of in *; simpl in *.
        rewrite (comp_transf_function _ _ H4).
        apply Peqb_true_eq in Heq. now rewrite Heq.
    }
    { Simpl. rewrite <- STACKS_COMP.
      rewrite H7, <- H2. simpl.
      unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence.
      rewrite FIND, CALLED.
      rewrite (comp_transl_partial _ TTRANSF).
      unfold comp_of in *; simpl in *.
      rewrite (comp_transf_function _ _ H4).
      apply Peqb_true_eq in Heq. now rewrite Heq. }
    simpl. eapply agree_exten; eauto. intros. Simpl.
    Simpl. rewrite <- H2. auto.
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
    simpl. unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence.
    simpl. rewrite (functions_transl _ _ _ FIND H4). reflexivity.
    unfold update_stack_call. Simpl.
    rewrite H7; simpl.
    simpl. unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence.
    unfold tge; rewrite TFIND.
    rewrite <- H2. simpl.
    replace (comp_of (Internal tf) =? comp_of tf')%positive with false.
    (* unfold comp_of in *; simpl in *. rewrite Heq. *)
    reflexivity.
    eauto.
    { simpl.
      intros.
      rewrite <- (comp_transl_partial _ H4) in H8.
      rewrite <- find_comp_translated, <- type_of_call_translated in H8; eauto.
      specialize (NO_CROSS_PTR H8).
      now eapply Val.lessdef_list_not_ptr; eauto. }
    { simpl. rewrite <- find_comp_translated, <- comp_transf_function; eauto.
      eapply call_trace_lessdef; eauto using senv_preserved, symbols_preserved. }
    econstructor; eauto.
    econstructor; eauto.
    eapply agree_sp_def; eauto.
    (* TODO: clean *)
    { eapply match_stacks_cross_compartment. exact STACKS'.
      - unfold Mach.call_comp. simpl.
        unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence.
        rewrite FIND, CALLED. rewrite (comp_transl_partial _ TTRANSF).
        unfold comp_of in *; simpl in *.
        rewrite (comp_transf_function _ _ H4).
        intros Heq'. rewrite Heq' in Heq; now rewrite Pos.eqb_refl in Heq.
      - simpl. erewrite match_stacks_callee; eauto.
        rewrite <- STACKS_COMP, <- H2. simpl.
        unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence.
        rewrite FIND, CALLED. rewrite (comp_transl_partial _ TTRANSF).
        unfold comp_of in *; simpl in *.
        rewrite (comp_transf_function _ _ H4).
        intros Heq'. rewrite Heq' in Heq; now rewrite Pos.eqb_refl in Heq.
      - unfold Mach.call_comp; simpl.
        erewrite match_stacks_callee; eauto. rewrite <- STACKS_COMP.
        now rewrite <- H2.
      - erewrite agree_sp; eauto.
        rewrite find_comp_translated.
        unfold Genv.find_comp, Genv.find_funct; destruct Ptrofs.eq_dec; try congruence.
        unfold tge; rewrite TFIND. constructor.
    }
    { Simpl. unfold callee_comp.
      rewrite H7. simpl.
      unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence.
      rewrite CALLED. rewrite (comp_transl_partial _ TTRANSF).
      reflexivity.
    }
    simpl. eapply agree_exten; eauto. intros. Simpl.
    Simpl. rewrite <- H2. auto.
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  exploit (call_arguments_match (Mach.undef_regs destroyed_at_function_entry rs)); eauto.
  instantiate (1 := (rs0 # PC <- (Genv.symbol_address tge fid Ptrofs.zero)) # X1 <- (Val.offset_ptr (rs0 PC) Ptrofs.one)).
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
    Simpl; eauto.
    unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. eauto.
    rewrite <- (comp_transl_partial _ H4).
    eapply allowed_call_translated; eauto.
    simpl. unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence.
    simpl. rewrite (functions_transl _ _ _ FIND H4). reflexivity.
    unfold update_stack_call. Simpl.
    unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H.
    simpl. unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence.
    simpl; unfold tge; rewrite TFIND.
    unfold comp_of in *; simpl in *. now rewrite Heq.
    eauto.
    (* Not a cross-compartment call *)
    { unfold Genv.type_of_call; simpl in *.
      unfold tge.
    simpl. unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence.
      rewrite TFIND. unfold comp_of in Heq. simpl in Heq.
      unfold comp_of. unfold comp_of in Heq. now rewrite Heq. }
    { simpl. rewrite <- find_comp_translated, <- comp_transf_function; eauto.
      eapply call_trace_lessdef; eauto using senv_preserved, symbols_preserved. }
    econstructor; eauto.
    econstructor; eauto.
    eapply agree_sp_def; eauto.
    { Simpl.
      apply match_stacks_intra_compartment. exact STACKS'.
      - unfold Mach.call_comp. simpl.
        unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence.
        rewrite FIND, CALLED.
        rewrite (comp_transl_partial _ TTRANSF).
        unfold comp_of in *; simpl in *.
        rewrite (comp_transf_function _ _ H4).
        apply Peqb_true_eq in Heq. now rewrite Heq.
      - simpl. erewrite match_stacks_callee; eauto.
        rewrite <- STACKS_COMP. rewrite <- H2. simpl.
        unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence.
        rewrite FIND, CALLED.
        rewrite (comp_transl_partial _ TTRANSF).
        unfold comp_of in *; simpl in *.
        rewrite (comp_transf_function _ _ H4).
        apply Peqb_true_eq in Heq. now rewrite Heq. }
    (* { apply match_stacks_intra_compartment with (pc := rs0 PC). exact STACKS'. *)
    (*   rewrite <- H2. simpl. unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence. *)
    (*   Simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. simpl. *)
    (*   unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence. *)
    (*   rewrite FIND, CALLED. *)
    (*   rewrite (comp_transl_partial _ TTRANSF). *)
    (*   unfold comp_of in *; simpl in *. *)
    (*   rewrite (comp_transf_function _ _ H4). *)
    (*   apply Peqb_true_eq in Heq. now rewrite Heq. } *)
    { Simpl. rewrite <- STACKS_COMP.
      unfold Genv.symbol_address; rewrite symbols_preserved, H.
      rewrite <- H2. simpl.
      unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence.
      rewrite FIND, CALLED.
      rewrite (comp_transl_partial _ TTRANSF).
      unfold comp_of in *; simpl in *.
      rewrite (comp_transf_function _ _ H4).
      apply Peqb_true_eq in Heq. now rewrite Heq. }
    simpl. eapply agree_exten; eauto. intros. Simpl.
    Simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. eauto.
    Simpl. rewrite <- H2. auto.
  * left; econstructor; split.
    apply plus_one. eapply exec_step_internal_call.
    rewrite <- H2; simpl; eauto.
    eapply functions_transl; eauto.
    eapply find_instr_tail; eauto.
    simpl; eauto.
    simpl; eauto.
    Simpl; eauto.
    unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. eauto.
    rewrite <- (comp_transl_partial _ H4).
    eapply allowed_call_translated; eauto.
    simpl. unfold Genv.find_comp; simpl. rewrite (functions_transl _ _ _ FIND H4).
    destruct Ptrofs.eq_dec; try congruence. reflexivity.
    unfold update_stack_call. Simpl.
    unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H.
    simpl; unfold tge. unfold Genv.find_comp; simpl. rewrite TFIND.
    destruct Ptrofs.eq_dec; try congruence.
    rewrite <- H2; simpl.
    replace (comp_of (Internal tf) =? comp_of tf')%positive with false.
    reflexivity.
    eauto.
    { simpl. intros.
      rewrite <- (comp_transl_partial _ H4) in H5.
      rewrite <- find_comp_translated, <- type_of_call_translated in H5; eauto.
      specialize (NO_CROSS_PTR H5).
      now eapply Val.lessdef_list_not_ptr; eauto. }
    { simpl. rewrite <- find_comp_translated, <- comp_transf_function; eauto.
      eapply call_trace_lessdef; eauto using senv_preserved, symbols_preserved. }
    econstructor; eauto.
    econstructor; eauto.
    eapply agree_sp_def; eauto.
    (* TODO: clean *)
    { eapply match_stacks_cross_compartment. exact STACKS'.
      - unfold Mach.call_comp. simpl. unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence.
        rewrite FIND, CALLED. rewrite (comp_transl_partial _ TTRANSF).
        unfold comp_of in *; simpl in *.
        rewrite (comp_transf_function _ _ H4).
        intros Heq'. rewrite Heq' in Heq; now rewrite Pos.eqb_refl in Heq.
      - simpl. erewrite match_stacks_callee; eauto.
        rewrite <- STACKS_COMP, <- H2. simpl.
        unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence.
        rewrite FIND, CALLED. rewrite (comp_transl_partial _ TTRANSF).
        unfold comp_of in *; simpl in *.
        rewrite (comp_transf_function _ _ H4).
        intros Heq'. rewrite Heq' in Heq; now rewrite Pos.eqb_refl in Heq.
      - unfold Mach.call_comp; simpl.
        erewrite match_stacks_callee; eauto. rewrite <- STACKS_COMP.
        now rewrite <- H2.
      - erewrite agree_sp; eauto.
        rewrite find_comp_translated.
        unfold Genv.find_comp, Genv.find_funct; destruct Ptrofs.eq_dec; try congruence.
        unfold tge; rewrite TFIND. constructor.
    }
    { Simpl. unfold callee_comp.
      unfold Genv.symbol_address; rewrite symbols_preserved, H. simpl.
      unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence.
      rewrite CALLED. rewrite (comp_transl_partial _ TTRANSF). reflexivity. }
    (* { eapply match_stacks_cross_compartment. exact STACKS'. *)
    (*   rewrite <- H2. simpl. unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence. *)
    (*   rewrite <- H2. *)
    (*   Simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. simpl. *)
    (*   unfold Genv.find_comp; simpl. destruct Ptrofs.eq_dec; try congruence. *)
    (*   rewrite FIND, CALLED. *)
    (*   rewrite (comp_transl_partial _ TTRANSF). *)
    (*   unfold comp_of in *; simpl in *. *)
    (*   rewrite (comp_transf_function _ _ H4). *)
    (*   intros Heq'. rewrite Heq' in Heq; now rewrite Pos.eqb_refl in Heq. *)
    (*   erewrite agree_sp; eauto. *)
    (*   (* TODO: clean *) *)
    (*   rewrite find_comp_translated. *)
    (*   unfold Genv.find_comp, Genv.find_funct; destruct Ptrofs.eq_dec; try congruence. *)
    (*   unfold tge; rewrite TFIND. constructor. *)
    (* } *)
    simpl. eapply agree_exten; eauto. intros. Simpl.
    Simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. eauto.
    Simpl. rewrite <- H2. auto.

- (* Mtailcall *)
  assert (f0 = f) by congruence.  subst f0.
  inversion AT; subst.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  exploit Mem.loadv_extends. eauto. eexact H1. auto. simpl.
  intros [parent' [A B]].
  (* pose proof Genv.find_funct_ptr_match TRANSF _ CALLED as [_ [tf' [TFIND [TTRANSF _]]]]. *)
  destruct ros as [rf|fid]; simpl in H; monadInv H7.
+ (* Indirect call *)
  assert (rs rf = Vptr f' Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
  assert (rs0 x0 = Vptr f' Ptrofs.zero).
    exploit ireg_val; eauto. rewrite H7; intros LD; inv LD; auto.
  unfold_find_comp H3 FIND.
  unfold_find_comp H2 FIND.
  unfold_find_comp H1 FIND.
  exploit make_epilogue_correct; eauto using (comp_transl_partial _ H6).
  intros (rs1 & m1 & U & V & W & X & Y & Z).
  exploit exec_straight_steps_2; eauto using functions_transl.
  intros (ofs' & P & Q).
  left; econstructor; split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor. eexact P. eapply functions_transl; eauto. eapply find_instr_tail. eexact Q.
  reflexivity.
  (* rewrite P. simpl. erewrite functions_transl; eauto. *)
  simpl. reflexivity. eauto. eauto.
  Simpl; eauto.
  rewrite Z by (rewrite <- (ireg_of_eq _ _ EQ1); eauto with asmgen). eauto.
  rewrite <- (comp_transl_partial _ H6).
  simpl. rewrite <- find_comp_translated, <- COMP.
  unfold Genv.find_comp; simpl; rewrite FIND. destruct Ptrofs.eq_dec; try congruence.
  reflexivity.
  traceEq.
  (* match states *)
  econstructor; eauto.
  { Simpl. rewrite Z by (rewrite <- (ireg_of_eq _ _ EQ1); eauto with asmgen).
    rewrite H9. rewrite <- H4 in *. rewrite <- STACKS_COMP.
    simpl. eauto. }
  apply agree_set_other; auto with asmgen.
  Simpl. rewrite Z by (rewrite <- (ireg_of_eq _ _ EQ1); eauto with asmgen). assumption.
+ (* Direct call *)
  unfold_find_comp H3 FIND.
  unfold_find_comp H2 FIND.
  unfold_find_comp H1 FIND.
  exploit make_epilogue_correct; eauto using (comp_transl_partial _ H6).
  intros (rs1 & m1 & U & V & W & X & Y & Z).
  exploit exec_straight_steps_2; eauto using functions_transl.
  intros (ofs' & P & Q).
  left; econstructor; split.
  (* execution *)
  eapply plus_right'. eapply exec_straight_exec; eauto.
  econstructor. eexact P. eapply functions_transl; eauto. eapply find_instr_tail. eexact Q.
  reflexivity.
  (* rewrite P. simpl. erewrite functions_transl; eauto. *)
  simpl. reflexivity. eauto. eauto.
  Simpl; eauto.
  unfold Genv.symbol_address. now rewrite symbols_preserved, H.
  rewrite <- (comp_transl_partial _ H6).
  simpl. rewrite <- find_comp_translated, <- COMP. unfold Genv.find_comp; simpl.
  now destruct Ptrofs.eq_dec; try congruence; rewrite FIND.
  traceEq.
  (* match states *)
  econstructor; eauto.
  { Simpl.
    unfold Genv.symbol_address. rewrite symbols_preserved, H.
    rewrite <- STACKS_COMP, <- H4. simpl; eauto. }
  apply agree_set_other; auto with asmgen.
  apply agree_set_other; auto with asmgen.
  Simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. auto.

- (* Mbuiltin *)
  inv AT. monadInv H4.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H3); intro NOOV.
  exploit builtin_args_match; eauto. intros [vargs' [P Q]].
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  (* unfold_find_comp A FUN. *)
  (* unfold comp_of in A; simpl in A. *)
  left. econstructor; split. apply plus_one.
  eapply exec_step_builtin. eauto. eauto.
  eapply find_instr_tail; eauto.
  erewrite <- sp_val by eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  rewrite <- (comp_transl_partial _ H3).
  unfold Genv.find_comp in ALLOWED. simpl in ALLOWED; rewrite FIND in ALLOWED.
  now destruct Ptrofs.eq_dec; try congruence.
  eauto.
  econstructor; eauto.
  { unfold nextinstr. rewrite Pregmap.gss.
    rewrite set_res_other. rewrite undef_regs_other_2. rewrite Pregmap.gso by congruence.
    rewrite Pregmap.gso by congruence.
    rewrite <- STACKS_COMP, <- H1. reflexivity.
    rewrite preg_notin_charact. intros. auto with asmgen.
    auto with asmgen. }
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
  rewrite FN. reflexivity.
  econstructor; eauto.
  { now rewrite <- STACKS_COMP, <- H1, <- H4. }
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
  reflexivity.
  simpl. rewrite <- H9. unfold Mach.label in H0; unfold label; rewrite H0.
  eexact A. eauto. eauto. eauto.
  simpl.
  simpl; unfold Genv.find_comp; simpl.
  rewrite FN. reflexivity.

  assert (exists ofs, rs' PC = Vptr fb ofs) as [ofs' Hptr]. {
    destruct (rs' PC); inversion B.
    eauto.
  }
  econstructor; eauto.
  { now rewrite <- STACKS_COMP, Hptr, <- H3. }
  eapply agree_undef_regs; eauto.
  simpl. intros. rewrite C; auto with asmgen. Simpl.
  congruence.

- (* Mreturn *)
  assert (f0 = f) by congruence. subst f0.
  inversion AT; subst. simpl in H6; monadInv H6.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  unfold_find_comp H2 FIND.
  unfold_find_comp H1 FIND.
  unfold_find_comp H0 FIND.
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
  { Simpl. rewrite P, <- find_comp_ignore_offset_translated.
    rewrite <- STACKS_COMP, <- H3. simpl.
    unfold Genv.find_comp; simpl; rewrite FIND;
      destruct Ptrofs.eq_dec; try congruence. }
  econstructor. traceEq. traceEq.
  (* destruct (Genv.type_of_call ge (Mach.call_comp ge s) (comp_of f)) eqn:TY_CALL. *)
  (* { *)
  (* replace (Mach.fn_sig f) with (fn_sig tf). *)
  (* econstructor; eauto. *)
  (* rewrite X; simpl; Simpl; eauto. *)

  (* apply agree_set_other; auto with asmgen. *)
  (* { monadInv H5. destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x0))); try discriminate. *)
  (*   inv EQ1. monadInv EQ0. reflexivity. } *)
  (* } *)
  { (* new case *)

  replace (Mach.fn_sig f) with (fn_sig tf).
  econstructor; eauto.
  rewrite X; simpl; Simpl; eauto.

  apply agree_set_other; auto with asmgen.
  { (* An easy lemma to add: more case analysis, but we undefine more so the
       constructor takes care of the case that is not covered by the assumption
       in the context *)
    inv V. constructor; auto.
    intros r. specialize (agree_mregs r). unfold undef_non_return_regs_ext.
    destruct (LTL.in_mreg r (regs_of_rpair (loc_result (parent_signature s)))); auto. }
  { monadInv H5. destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x0))); try discriminate.
    inv EQ1. monadInv EQ0. reflexivity. }
  }
  (* { (* same as Genv.InternalCall *) *)
  (* replace (Mach.fn_sig f) with (fn_sig tf). *)
  (* econstructor; eauto. *)
  (* rewrite X; simpl; Simpl; eauto. *)

  (* apply agree_set_other; auto with asmgen. *)
  (* { monadInv H5. destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x0))); try discriminate. *)
  (*   inv EQ1. monadInv EQ0. reflexivity. } *)
  (* } *)

- (* internal function *)
  (* assert (cp = comp_of f). *)
  (* unfold find_comp_ptr in CURCOMP. rewrite H in CURCOMP. inv CURCOMP. *)
  (* reflexivity. subst. *)
  inv H.
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
  assert (COMP_FB: Genv.find_comp ge (Vptr fb Ptrofs.zero) = comp_of tf).
  { subst tf. unfold Genv.find_comp; simpl; rewrite H4.
    destruct Ptrofs.eq_dec; try congruence. reflexivity. }
  set (rs2 := nextinstr (rs0#X30 <- (parent_sp s) #SP <- sp #X31 <- Vundef)).
  exploit (storeind_ptr_correct tge tf SP (fn_retaddr_ofs f) RA x0 rs2 m2').
    rewrite chunk_of_Tptr in P. change (rs2 X1) with (rs0 X1). rewrite ATLR.
    change (rs2 X2) with sp. rewrite <- COMP_FB. eexact P.
    congruence. congruence.
  intros (rs3 & U & V).
  assert (EXEC_PROLOGUE:
            exec_straight tge tf
              tf.(fn_code) rs0 m'
              x0 rs3 m3').
  { change (fn_code tf) with tfbody; unfold tfbody.
    eapply exec_straight_step with rs2 m2'.
    unfold exec_instr.
    rewrite COMP_FB in C, F.
    rewrite C. fold sp.
    rewrite <- (sp_val _ _ _ AG). rewrite chunk_of_Tptr in F. rewrite F. reflexivity.
    reflexivity. reflexivity. reflexivity.
    eexact U. }
  exploit exec_straight_steps_2; eauto using functions_transl. lia. constructor.
  intros (ofs' & X & Y).
  left; eexists; split.
  eapply exec_straight_steps_1; eauto. lia. simpl. unfold Genv.find_comp; simpl.
  now rewrite A. constructor.
(*   destruct (Genv.type_of_call ge (Mach.call_comp ge s) (Genv.find_comp ge (Vptr fb Ptrofs.zero))) eqn:TY_CALL. *)
(*   { *)
(*   econstructor; eauto. *)
(*   { rewrite X, <- STACKS_COMP, ATPC. reflexivity. } *)
(*   (* rewrite X. rewrite ATPC in STACKS'. eapply match_stacks_same_compartment; eauto. *) *)
(*   rewrite X; econstructor; eauto. *)
(*   apply agree_exten with rs2; eauto with asmgen. *)
(*   unfold rs2. *)
(*   apply agree_nextinstr. apply agree_set_other; auto with asmgen. *)
(*   apply agree_change_sp with (parent_sp s). *)
(*   apply agree_undef_regs with rs0. auto. *)
(* Local Transparent destroyed_at_function_entry. *)
(*   simpl; intros; Simpl. *)
(*   unfold sp; congruence. *)
(*   intros. rewrite V by auto with asmgen. reflexivity. *)
(*   } *)
  { (* new case*)
  econstructor; eauto.
  { rewrite X, <- STACKS_COMP, ATPC. reflexivity. }
  (* rewrite X. rewrite ATPC in STACKS'. eapply match_stacks_same_compartment; eauto. *)
  rewrite X; econstructor; eauto.
  apply agree_exten with rs2; eauto with asmgen.
  unfold rs2.
  apply agree_nextinstr. apply agree_set_other; auto with asmgen.
  apply agree_change_sp with (parent_sp s).
  apply agree_undef_regs with rs0.
  { unfold undef_caller_save_regs_ext.
    inv AG. constructor; auto.
    intros r. specialize (agree_mregs r).
    destruct (LTL.in_mreg r (LTL.parameters_mregs sig));
    auto. }
Local Transparent destroyed_at_function_entry.
  simpl; intros; Simpl.
  unfold sp; congruence.
  intros. rewrite V by auto with asmgen. reflexivity.
  }
(*   { (* same as Genv.InternalCall *) *)
(*   econstructor; eauto. *)
(*   { rewrite X, <- STACKS_COMP, ATPC. reflexivity. } *)
(*   (* rewrite X. rewrite ATPC in STACKS'. eapply match_stacks_same_compartment; eauto. *) *)
(*   rewrite X; econstructor; eauto. *)
(*   apply agree_exten with rs2; eauto with asmgen. *)
(*   unfold rs2. *)
(*   apply agree_nextinstr. apply agree_set_other; auto with asmgen. *)
(*   apply agree_change_sp with (parent_sp s). *)
(*   apply agree_undef_regs with rs0. auto. *)
(* Local Transparent destroyed_at_function_entry. *)
(*   simpl; intros; Simpl. *)
(*   unfold sp; congruence. *)
(*   intros. rewrite V by auto with asmgen. reflexivity. *)
(*   } *)

- (* external function *)
  exploit functions_translated; eauto.
  intros [tf [A B]]. simpl in B. inv B.
  exploit extcall_arguments_match; eauto.
  intros [args' [C D]].
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [P [Q [R S]]]]].

  left; econstructor; split.
  apply plus_one. eapply exec_step_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  rewrite <- find_comp_ignore_offset_translated; eauto.

  econstructor; eauto.
  Simpl. rewrite ATLR. eauto.
  eapply agree_set_other; eauto.
  eapply agree_set_pair; eauto. eapply agree_undef_caller_save_regs; eauto.

- inv STACKS.
  assert (exists s'', update_stack_return tge s' (callee_comp comp_of_main s') rs0 = Some s'' /\
         match_stacks s s'') as [s'' [Hs''1 Hs''2]].
  { unfold update_stack_return.
    rewrite ATPC in *. simpl in *.

    rewrite <- find_comp_translated.
    destruct (callee_comp comp_of_main s' =? Genv.find_comp ge (Vptr f Ptrofs.zero))%positive eqn:e.
    - eexists; split; auto.
      inv STACKS'; auto.
      unfold Mach.call_comp in *; simpl in *.
      inv H10. apply Peqb_true_eq in e. congruence.
    - inv STACKS'; auto.
      + unfold Mach.call_comp in *; simpl in *.
        subst. apply Pos.eqb_neq in e.
        apply match_stacks_callee in H1. congruence.
      + eexists; split; auto. }

  left. eexists (State s'' rs0 m'). split.
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
  { rewrite ATPC. simpl.
    intros diff.
    inv STACKS'; auto.
    - simpl in *. subst. unfold Mach.call_comp in *. simpl in *.
      rewrite <- find_comp_translated in diff. now apply match_stacks_callee in H1; congruence.
    - inv H10. reflexivity. }
  { rewrite ATPC. simpl.
    intros diff.
    inv STACKS'; auto.
    - simpl in *. subst. unfold Mach.call_comp in *. simpl in *.
      rewrite <- find_comp_translated in diff. now apply match_stacks_callee in H1; congruence.
    - inv H10. eapply agree_sp; eauto. }
  { rewrite ATPC. simpl. rewrite <- find_comp_translated.
    intros TYPE.
    inv STACKS'; auto.
    - simpl in *. subst. unfold Mach.call_comp in *. simpl in *.
      apply match_stacks_callee in H1. rewrite <- H1, <- H2 in TYPE.
      exfalso. eapply Genv.type_of_call_same_cp. eauto.
    - simpl in *. subst. unfold Mach.call_comp in *. simpl in *.
      inv H10.
      specialize (NO_CROSS_PTR TYPE).
      (* TODO: factorize into a lemma Val.lessdef_not_ptr *)
      inv LD; auto. now rewrite <- H0 in NO_CROSS_PTR. }
  { rewrite ATPC; simpl; rewrite <- find_comp_translated.
    inv STACKS'; auto.
    - simpl in *. subst. unfold Mach.call_comp in *. simpl in *.
      apply match_stacks_callee in H1. rewrite <- H1, <- H2.
      assert (t = E0).
      { rewrite <- H2 in EV.
        inv EV; auto.
        exfalso. eapply Genv.type_of_call_same_cp. eauto. }
      subst. constructor. now apply Genv.type_of_call_same_cp.
    - simpl in *. subst. unfold Mach.call_comp in *. simpl in *.
      inv H10.
      eapply return_trace_lessdef with (ge := ge) (v := Mach.return_value rs sg);
        eauto using senv_preserved. }

  econstructor; eauto.
  { unfold update_stack_return in Hs''1.
    rewrite ATPC in *.
    simpl in *.
    inv STACKS'; auto.
    - simpl in *. unfold Mach.call_comp in H2. simpl in *.
      apply match_stacks_callee in Hs''2.
      congruence.
    - simpl in *. inv H10. unfold Mach.call_comp in *; simpl in *.
      erewrite <- match_stacks_callee; eauto. }
  rewrite ATPC; simpl; eauto.
  congruence.
Qed.

Lemma transf_initial_states:
  forall st1, Mach.initial_state prog st1 ->
  exists st2, Asm.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. unfold ge0 in *.
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_transf_partial TRANSF); eauto.
  replace (Genv.symbol_address (Genv.globalenv tprog) (prog_main tprog) Ptrofs.zero)
     with (Vptr fb Ptrofs.zero).
  econstructor; eauto.
  constructor. constructor.
  Simpl. simpl. subst comp_of_main. unfold Asm.comp_of_main.
  rewrite symbols_preserved. rewrite (match_program_main TRANSF). unfold ge. rewrite H1.
  now rewrite find_comp_translated.
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
