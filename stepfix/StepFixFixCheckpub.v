(** * Counterexample 1 (CHECKPUB), from the initial state of a whole program.

    The program [prog1] (the Asm analogue of the C program
<<
      // compartment c1                  // compartment c2
      int y = 0;                         int g(void) { return 0; }
      int *px = &y;
      int main(void) { g(); ... }
>>
    with policy "c1 imports g from c2, c2 exports g") has a public variable
    [px] initialised with [Init_addrof y 0].  [Genv.init_mem] stores a pointer
    in [px]'s block, i.e. [Fragment] bytes, so [public_first_order] fails in
    the initial memory.  The first instruction of [main] is the
    cross-compartment call [Pjal_s g signature_main true].

    - [Asm.step] takes this call (it has no CHECKPUB premise);
    - [step_fix] cannot take any step from the initial state: its only rule
      that could fire is [exec_step_fix_internal_call], whose premise
      CHECKPUB demands [public_first_order ge m0];
    - all other premises of [exec_step_fix_internal_call] hold, in particular
      CALLSIG ([signature_main = funsig (Internal f_g)]), so CHECKPUB is the
      only violated check.

    Initial memory is reasoned about abstractly ([Genv.init_mem_exists],
    [Genv.init_mem_characterization]); nothing depends on [Archi.ptr64]. *)

Require Import Coqlib Maps Integers Values Memory Globalenvs.
Require Import AST Smallstep Events.
Require Import riscV.Asm.
Require Import StepFixFix.StepFixFixCommon.

Definition y_id : ident := 1%positive.
Definition px_id : ident := 2%positive.
Definition main_id : ident := 3%positive.
Definition g_id : ident := 4%positive.

Definition c1 : compartment := 2%positive. (* main, y, px *)
Definition c2 : compartment := 3%positive. (* g *)

Definition gv_y : globvar unit :=
  {| gvar_info := tt; gvar_comp := c1; gvar_init := Init_int32 Int.zero :: nil;
     gvar_readonly := false; gvar_volatile := false |}.

Definition gv_px : globvar unit :=
  {| gvar_info := tt; gvar_comp := c1; gvar_init := Init_addrof y_id Ptrofs.zero :: nil;
     gvar_readonly := false; gvar_volatile := false |}.

(** Only the first instruction of [main] matters for the counterexample. *)
Definition f_main : Asm.function :=
  {| fn_comp := c1; fn_sig := signature_main;
     fn_code := Pjal_s g_id signature_main true :: Pj_r X1 signature_main true :: nil |}.

Definition f_g : Asm.function :=
  {| fn_comp := c2; fn_sig := signature_main;
     fn_code := Paddiw X10 X0 Int.zero :: Pj_r X1 signature_main true :: nil |}.

Definition pol1 : Policy.t :=
  Policy.mkpolicy (PTree.set c2 (g_id :: nil) (PTree.empty _))
                  (PTree.set c1 ((c2, g_id) :: nil) (PTree.empty _)).

Definition prog1 : Asm.program :=
  {| prog_defs := (y_id, Gvar gv_y) :: (px_id, Gvar gv_px)
                  :: (main_id, Gfun (Internal f_main)) :: (g_id, Gfun (Internal f_g)) :: nil;
     prog_public := y_id :: px_id :: main_id :: g_id :: nil;
     prog_main := main_id;
     prog_pol := pol1 |}.

Definition ge1 : Asm.genv := Genv.globalenv prog1.

(** ** The global environment (computed) *)

Lemma ge1_symb_y: Genv.find_symbol ge1 y_id = Some 1%positive.
Proof. reflexivity. Qed.
Lemma ge1_symb_px: Genv.find_symbol ge1 px_id = Some 2%positive.
Proof. reflexivity. Qed.
Lemma ge1_symb_main: Genv.find_symbol ge1 main_id = Some 3%positive.
Proof. reflexivity. Qed.
Lemma ge1_symb_g: Genv.find_symbol ge1 g_id = Some 4%positive.
Proof. reflexivity. Qed.
Lemma ge1_var_px: Genv.find_var_info ge1 2%positive = Some gv_px.
Proof. reflexivity. Qed.
Lemma ge1_funct_main: Genv.find_funct_ptr ge1 3%positive = Some (Internal f_main).
Proof. reflexivity. Qed.
Lemma ge1_funct_g: Genv.find_funct_ptr ge1 4%positive = Some (Internal f_g).
Proof. reflexivity. Qed.
Lemma ge1_invert_g: Genv.invert_symbol ge1 4%positive = Some g_id.
Proof. reflexivity. Qed.
Lemma ge1_public_px: Senv.public_symbol ge1 px_id = true.
Proof. reflexivity. Qed.
Lemma ge1_policy: Genv.genv_policy ge1 = pol1.
Proof. reflexivity. Qed.

Lemma ge1_comp_main: Genv.find_comp_ignore_offset ge1 (Vptr 3%positive Ptrofs.zero) = c1.
Proof.
  unfold Genv.find_comp_ignore_offset, Genv.find_comp.
  rewrite Genv.find_funct_find_funct_ptr, ge1_funct_main. reflexivity.
Qed.

Lemma ge1_comp_g: Genv.find_comp_ignore_offset ge1 (Vptr 4%positive Ptrofs.zero) = c2.
Proof.
  unfold Genv.find_comp_ignore_offset, Genv.find_comp.
  rewrite Genv.find_funct_find_funct_ptr, ge1_funct_g. reflexivity.
Qed.

Lemma comp_of_main1: comp_of_main prog1 = c1.
Proof.
  unfold comp_of_main. cbv zeta. change (Genv.globalenv prog1) with ge1.
  change (prog_main prog1) with main_id.
  rewrite ge1_symb_main. apply ge1_comp_main.
Qed.

(** ** Initial memory: the public variable [px] holds a pointer *)

Lemma prog1_init_mem_exists: exists m0, Genv.init_mem prog1 = Some m0.
Proof.
  apply Genv.init_mem_exists.
  intros id v IN. simpl in IN.
  destruct IN as [E | [E | [E | [E | []]]]]; inversion E; subst; simpl.
  - split.
    + split; [apply Z.divide_0_r | exact I].
    + intros i o [H | []]. discriminate.
  - split.
    + split; [apply Z.divide_0_r | exact I].
    + intros i o [H | []]. inversion H; subst. exists 1%positive. reflexivity.
Qed.

(** [Mem.loadbytes] is declared [Global Opaque] in common/Memory.v; we unfold
    it to relate the loaded bytes to [Mem.mem_contents]. *)
Transparent Mem.loadbytes.

Lemma init_px_not_first_order:
  forall m0, Genv.init_mem prog1 = Some m0 ->
    Mem.perm m0 2%positive 0 Cur Readable /\ ~ loc_first_order m0 2%positive 0.
Proof.
  intros m0 INIT.
  destruct (Genv.init_mem_characterization _ _ ge1_var_px INIT)
    as (RP & _ & _ & LB).
  specialize (LB eq_refl).
  change (Genv.globalenv prog1) with ge1 in LB.
  change (gvar_init gv_px) with (Init_addrof y_id Ptrofs.zero :: nil) in LB, RP.
  change (gvar_comp gv_px) with c1 in LB.
  unfold Genv.bytes_of_init_data_list, Genv.bytes_of_init_data in LB.
  rewrite ge1_symb_y in LB.
  unfold Mem.loadbytes in LB.
  destruct (Mem.range_perm_dec _ _ _ _ _ _ && Mem.can_access_block_dec _ _ _);
    [| discriminate].
  injection LB as LB.
  revert RP LB. unfold loc_first_order, init_data_list_size, init_data_size, inj_value.
  simpl (Genv.perm_globvar gv_px).
  destruct Archi.ptr64; simpl; intros RP LB.
  - split.
    + eapply Mem.perm_implies. apply RP. lia. constructor.
    + injection LB as LB0 _. rewrite LB0. auto.
  - split.
    + eapply Mem.perm_implies. apply RP. lia. constructor.
    + injection LB as LB0 _. rewrite LB0. auto.
Qed.

(** The violated premise: [public_first_order] fails in the initial memory. *)
Lemma init_not_public_first_order:
  forall m0, Genv.init_mem prog1 = Some m0 -> ~ public_first_order ge1 m0.
Proof.
  intros m0 INIT PFO.
  destruct (init_px_not_first_order m0 INIT) as [READ NFO].
  apply NFO. eapply PFO; eauto.
  - apply ge1_public_px.
  - apply ge1_symb_px.
Qed.

(** ** The initial state and the Asm call step *)

Definition rs0 : regset :=
  (Pregmap.init Vundef)
    # PC <- (Genv.symbol_address ge1 main_id Ptrofs.zero)
    # SP <- Vnullptr
    # RA <- Vnullptr.

Definition s0 (m0: mem) : Asm.state := State initial_stack rs0 m0.

Lemma s0_initial: forall m0, Genv.init_mem prog1 = Some m0 -> initial_state prog1 (s0 m0).
Proof. intros m0 INIT. econstructor. exact INIT. Qed.

Lemma initial_state_s0: forall s, initial_state prog1 s ->
  exists m0, Genv.init_mem prog1 = Some m0 /\ s = s0 m0.
Proof. intros s INIT. inversion INIT; subst. eexists; split; eauto. Qed.

Lemma rs0_PC: rs0 PC = Vptr 3%positive Ptrofs.zero.
Proof.
  unfold rs0. rewrite Pregmap.gso by discriminate. rewrite Pregmap.gso by discriminate.
  rewrite Pregmap.gss. unfold Genv.symbol_address. rewrite ge1_symb_main. reflexivity.
Qed.

Definition rs1 : regset :=
  rs0 # PC <- (Genv.symbol_address ge1 g_id Ptrofs.zero)
      # RA <- (Val.offset_ptr (rs0 PC) Ptrofs.one).

Lemma rs1_PC: rs1 PC = Vptr 4%positive Ptrofs.zero.
Proof.
  unfold rs1. rewrite Pregmap.gso by discriminate. rewrite Pregmap.gss.
  unfold Genv.symbol_address. rewrite ge1_symb_g. reflexivity.
Qed.

Lemma rs1_RA: rs1 RA = Vptr 3%positive (Ptrofs.add Ptrofs.zero Ptrofs.one).
Proof. unfold rs1. rewrite Pregmap.gss. rewrite rs0_PC. reflexivity. Qed.

Definition st1 : stack :=
  Stackframe 3%positive c2 signature_main (rs1 SP) (Ptrofs.add Ptrofs.zero Ptrofs.one) :: nil.

Definition s1 (m0: mem) : Asm.state := State st1 rs1 m0.

Definition tr1 : trace := Event_call c1 c2 g_id nil :: nil.

Lemma exec_call_main:
  forall m0 cp, exec_instr ge1 f_main (Pjal_s g_id signature_main true) rs0 m0 cp = Next rs1 m0.
Proof. reflexivity. Qed.

Lemma allowed_main_g: Genv.allowed_call ge1 (comp_of f_main) (Vptr 4%positive Ptrofs.zero).
Proof.
  right. exists g_id, c2. split; [| split; [| split; [| split]]].
  - apply ge1_invert_g.
  - intros fd FD. rewrite Genv.find_funct_find_funct_ptr, ge1_funct_g in FD.
    inversion FD; subst. exact I.
  - change (Genv.find_comp ge1 (Vptr 4%positive Ptrofs.zero) = c2). apply ge1_comp_g.
  - rewrite ge1_policy. simpl. left. reflexivity.
  - rewrite ge1_policy. simpl. left. reflexivity.
Qed.

Lemma asm_step_call:
  forall m0, Asm.step (comp_of_main prog1) ge1 (s0 m0) tr1 (s1 m0).
Proof.
  intros m0. unfold s0, s1.
  eapply exec_step_internal_call with
    (b := 3%positive) (ofs := Ptrofs.zero) (f := f_main)
    (i := Pjal_s g_id signature_main true) (sig := signature_main)
    (b' := 4%positive) (ofs' := Ptrofs.zero) (cp := c1) (args := nil).
  - apply rs0_PC.
  - apply ge1_funct_main.
  - rewrite Ptrofs.unsigned_zero. reflexivity.
  - apply exec_call_main.
  - reflexivity.
  - apply rs1_PC.
  - apply allowed_main_g.
  - apply ge1_comp_main.
  - unfold update_stack_call. rewrite rs1_PC, rs1_RA, ge1_comp_g. reflexivity.
  - constructor.
  - intros _. constructor.
  - rewrite ge1_comp_g. change (comp_of f_main) with c1.
    eapply call_trace_cross.
    + reflexivity.
    + reflexivity.
    + apply ge1_invert_g.
    + constructor.
Qed.

(** CALLSIG holds for this call: the only violated premise is CHECKPUB. *)
Lemma callsig_holds:
  exists fd, Genv.find_funct_ptr ge1 4%positive = Some fd /\ signature_main = funsig fd.
Proof. exists (Internal f_g). split; [apply ge1_funct_g | reflexivity]. Qed.

(** ** No [step_fix] step from the initial state *)

Lemma s0_instr:
  forall b ofs f i,
    rs0 PC = Vptr b ofs ->
    Genv.find_funct_ptr ge1 b = Some (Internal f) ->
    find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
    b = 3%positive /\ ofs = Ptrofs.zero /\ f = f_main /\ i = Pjal_s g_id signature_main true.
Proof.
  intros b ofs f i PC FF FI.
  rewrite rs0_PC in PC. inversion PC; subst.
  rewrite ge1_funct_main in FF. inversion FF; subst.
  rewrite Ptrofs.unsigned_zero in FI. simpl in FI. inversion FI; subst. auto.
Qed.

Lemma s0_not_external:
  forall b ofs ef, rs0 PC = Vptr b ofs -> Genv.find_funct_ptr ge1 b = Some (External ef) -> False.
Proof.
  intros b ofs ef PC FF. rewrite rs0_PC in PC. inversion PC; subst.
  rewrite ge1_funct_main in FF. discriminate.
Qed.

Ltac use_s0_instr :=
  match goal with
  | H1: rs0 PC = Vptr ?b ?ofs, H2: Genv.find_funct_ptr _ ?b = Some (Internal ?f),
    H3: find_instr _ (fn_code ?f) = Some _ |- _ =>
      destruct (s0_instr _ _ _ _ H1 H2 H3) as (? & ? & ? & ?); subst
  end.

Lemma no_step_fix_s0:
  forall m0, Genv.init_mem prog1 = Some m0 ->
    forall t s, ~ step_fix (comp_of_main prog1) ge1 (s0 m0) t s.
Proof.
  intros m0 INIT t s STEP. unfold s0 in STEP.
  inversion STEP; subst.
  - (* exec_step_fix_internal: sig_call (Pjal_s ..) <> None *)
    use_s0_instr. discriminate.
  - (* exec_step_fix_internal_call: CHECKPUB fails *)
    use_s0_instr.
    match goal with
    | H: exec_instr _ _ _ _ _ _ = Next _ _ |- _ =>
        rewrite exec_call_main in H; inversion H; subst
    end.
    rewrite rs1_PC in NEXTPC. inversion NEXTPC; subst.
    apply (init_not_public_first_order _ INIT).
    apply CHECKPUB. rewrite ge1_comp_g. reflexivity.
  - (* exec_step_fix_internal_return: is_return (Pjal_s ..) = false *)
    use_s0_instr. discriminate.
  - (* exec_step_fix_builtin: the instruction is not a builtin *)
    use_s0_instr. discriminate.
  - (* exec_step_fix_external: main is internal *)
    eapply s0_not_external; eauto.
Qed.

(** ** Result: from every initial state of [prog1], Asm makes the call with
    trace [tr1], and [step_fix] has no run with trace [tr1] at all. *)

Theorem checkpub_counterexample:
  (exists s, initial_state prog1 s) /\
  (forall s, initial_state prog1 s ->
     exists s', star (Asm.step (comp_of_main prog1)) (Genv.globalenv prog1) s tr1 s') /\
  (forall s s', initial_state prog1 s ->
     ~ star (step_fix (comp_of_main prog1)) (Genv.globalenv prog1) s tr1 s').
Proof.
  split; [| split].
  - destruct prog1_init_mem_exists as [m0 INIT]. exists (s0 m0). apply s0_initial; auto.
  - intros s INIT. destruct (initial_state_s0 s INIT) as (m0 & IM & ->).
    exists (s1 m0). apply star_one. apply asm_step_call.
  - intros s s' INIT. destruct (initial_state_s0 s INIT) as (m0 & IM & ->).
    eapply no_star_nonempty_from_stuck. apply no_step_fix_s0; auto.
Qed.

Theorem not_step_fix_fix_checkpub: ~ step_fix_fix_stmt.
Proof.
  intros SFF.
  destruct checkpub_counterexample as ([s INIT] & RUN & NORUN).
  destruct (RUN s INIT) as [s' STAR].
  apply (NORUN s s' INIT). apply SFF. exact STAR.
Qed.
