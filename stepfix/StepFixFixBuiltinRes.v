(** * Counterexample 3 (builtin result register), from the initial state of a
    hand-written Asm program.

    [step_fix]'s builtin rule only matches instructions of the syntactic form
    [Pbuiltin ef args (map_builtin_res preg_of res)] with [res: builtin_res mreg],
    i.e. the result must be [BR_none] or registers in the image of [preg_of]
    (X5..X30, F0..F31).  [Asm.step]'s builtin rule accepts any [builtin_res preg].

    [prog3] (hand-written Asm, no globals) has [main] in compartment c1 whose
    first instruction is [Pbuiltin (EF_debug c1 1 1 nil) nil (BR (IR X31))]
    (a debug annotation, trace [E0], result written to X31, which is not
    [preg_of] of any [mreg]), followed by a cross-compartment call to [g] in
    compartment c2 (policy "c1 imports g from c2, c2 exports g").

    - [Asm.step] executes the builtin (trace [E0], PC advanced) and then the
      call, producing the trace [Event_call c1 c2 g nil :: nil];
      already the one-step run [star Asm.step s0 E0 s1] is a counterexample
      ([builtin_res_counterexample_E0]);
    - [step_fix] has no step from the initial state.

    The builtin step itself does not involve compartments, CHECKPUB, CALLSIG or
    ECC (EF_debug has [external_call_conds] = [True]); the call is only there
    to make the trace non-empty. *)

Require Import Coqlib Maps Integers Values Memory Globalenvs.
Require Import AST Smallstep Events Machregs.
Require Import riscV.Asm.
Require Import StepFixFix.StepFixFixCommon.

Definition main_id : ident := 1%positive.
Definition g_id : ident := 2%positive.
Definition c1 : compartment := 2%positive. (* main *)
Definition c2 : compartment := 3%positive. (* g *)

Definition ef_dbg : external_function := EF_debug c1 1%positive 1%positive nil.

Definition f_main : Asm.function :=
  {| fn_comp := c1; fn_sig := signature_main;
     fn_code := Pbuiltin ef_dbg nil (BR (IR X31))
                :: Pjal_s g_id signature_main true
                :: Pj_r X1 signature_main true :: nil |}.

Definition f_g : Asm.function :=
  {| fn_comp := c2; fn_sig := signature_main;
     fn_code := Paddiw X10 X0 Int.zero :: Pj_r X1 signature_main true :: nil |}.

Definition pol3 : Policy.t :=
  Policy.mkpolicy (PTree.set c2 (g_id :: nil) (PTree.empty _))
                  (PTree.set c1 ((c2, g_id) :: nil) (PTree.empty _)).

Definition prog3 : Asm.program :=
  {| prog_defs := (main_id, Gfun (Internal f_main)) :: (g_id, Gfun (Internal f_g)) :: nil;
     prog_public := main_id :: g_id :: nil;
     prog_main := main_id;
     prog_pol := pol3 |}.

Definition ge3 : Asm.genv := Genv.globalenv prog3.

Lemma ge3_symb_main: Genv.find_symbol ge3 main_id = Some 1%positive.
Proof. reflexivity. Qed.
Lemma ge3_funct_main: Genv.find_funct_ptr ge3 1%positive = Some (Internal f_main).
Proof. reflexivity. Qed.
Lemma ge3_symb_g: Genv.find_symbol ge3 g_id = Some 2%positive.
Proof. reflexivity. Qed.
Lemma ge3_funct_g: Genv.find_funct_ptr ge3 2%positive = Some (Internal f_g).
Proof. reflexivity. Qed.
Lemma ge3_invert_g: Genv.invert_symbol ge3 2%positive = Some g_id.
Proof. reflexivity. Qed.
Lemma ge3_policy: Genv.genv_policy ge3 = pol3.
Proof. reflexivity. Qed.

Lemma ge3_comp_main: Genv.find_comp_ignore_offset ge3 (Vptr 1%positive Ptrofs.zero) = c1.
Proof.
  unfold Genv.find_comp_ignore_offset, Genv.find_comp.
  rewrite Genv.find_funct_find_funct_ptr, ge3_funct_main. reflexivity.
Qed.

Lemma ge3_comp_g: Genv.find_comp_ignore_offset ge3 (Vptr 2%positive Ptrofs.zero) = c2.
Proof.
  unfold Genv.find_comp_ignore_offset, Genv.find_comp.
  rewrite Genv.find_funct_find_funct_ptr, ge3_funct_g. reflexivity.
Qed.

Lemma prog3_init_mem_exists: exists m0, Genv.init_mem prog3 = Some m0.
Proof.
  apply Genv.init_mem_exists.
  intros id v IN. simpl in IN. destruct IN as [E | [E | []]]; discriminate.
Qed.

Definition rs0 : regset :=
  (Pregmap.init Vundef)
    # PC <- (Genv.symbol_address ge3 main_id Ptrofs.zero)
    # SP <- Vnullptr
    # RA <- Vnullptr.

Definition s0 (m0: mem) : Asm.state := State initial_stack rs0 m0.

Lemma s0_initial: forall m0, Genv.init_mem prog3 = Some m0 -> initial_state prog3 (s0 m0).
Proof. intros m0 INIT. econstructor. exact INIT. Qed.

Lemma initial_state_s0: forall s, initial_state prog3 s ->
  exists m0, Genv.init_mem prog3 = Some m0 /\ s = s0 m0.
Proof. intros s INIT. inversion INIT; subst. eexists; split; eauto. Qed.

Lemma rs0_PC: rs0 PC = Vptr 1%positive Ptrofs.zero.
Proof.
  unfold rs0. rewrite Pregmap.gso by discriminate. rewrite Pregmap.gso by discriminate.
  rewrite Pregmap.gss. unfold Genv.symbol_address. rewrite ge3_symb_main. reflexivity.
Qed.

Definition rs1 : regset :=
  nextinstr (set_res (BR (IR X31)) Vundef
               (undef_regs (map preg_of (destroyed_by_builtin ef_dbg))
                  (rs0 # X1 <- Vundef # X31 <- Vundef))).

Lemma rs1_PC: rs1 PC = Vptr 1%positive (Ptrofs.add Ptrofs.zero Ptrofs.one).
Proof.
  unfold rs1, nextinstr. rewrite Pregmap.gss. reflexivity.
Qed.

Definition s1 (m0: mem) : Asm.state := State initial_stack rs1 m0.

Lemma asm_step_builtin:
  forall m0, Asm.step (comp_of_main prog3) ge3 (s0 m0) E0 (s1 m0).
Proof.
  intros m0. unfold s0, s1.
  eapply exec_step_builtin with
    (b := 1%positive) (ofs := Ptrofs.zero) (f := f_main) (ef := ef_dbg)
    (args := nil) (res := BR (IR X31)) (vargs := nil) (vres := Vundef).
  - apply rs0_PC.
  - apply ge3_funct_main.
  - rewrite Ptrofs.unsigned_zero. reflexivity.
  - constructor.
  - constructor.
  - reflexivity.
  - reflexivity.
Qed.

Lemma s1_not_s0: forall m0, s1 m0 <> s0 m0.
Proof.
  intros m0 E. unfold s0, s1 in E. inversion E as [RS].
  assert (PCEQ: rs1 PC = rs0 PC) by (rewrite RS; reflexivity).
  rewrite rs1_PC, rs0_PC in PCEQ.
  assert (OFS: Ptrofs.add Ptrofs.zero Ptrofs.one = Ptrofs.zero) by congruence.
  rewrite Ptrofs.add_zero_l in OFS. apply Ptrofs.one_not_zero. exact OFS.
Qed.

Definition rs2 : regset :=
  rs1 # PC <- (Genv.symbol_address ge3 g_id Ptrofs.zero)
      # RA <- (Val.offset_ptr (rs1 PC) Ptrofs.one).

Lemma rs2_PC: rs2 PC = Vptr 2%positive Ptrofs.zero.
Proof.
  unfold rs2. rewrite Pregmap.gso by discriminate. rewrite Pregmap.gss.
  unfold Genv.symbol_address. rewrite ge3_symb_g. reflexivity.
Qed.

Lemma rs2_RA: rs2 RA = Vptr 1%positive (Ptrofs.add (Ptrofs.add Ptrofs.zero Ptrofs.one) Ptrofs.one).
Proof. unfold rs2. rewrite Pregmap.gss. rewrite rs1_PC. reflexivity. Qed.

Definition st2 : stack :=
  Stackframe 1%positive c2 signature_main (rs2 SP)
             (Ptrofs.add (Ptrofs.add Ptrofs.zero Ptrofs.one) Ptrofs.one) :: nil.

Definition tr3 : trace := Event_call c1 c2 g_id nil :: nil.

Lemma allowed_main_g: Genv.allowed_call ge3 (comp_of f_main) (Vptr 2%positive Ptrofs.zero).
Proof.
  right. exists g_id, c2. split; [| split; [| split; [| split]]].
  - apply ge3_invert_g.
  - intros fd FD. rewrite Genv.find_funct_find_funct_ptr, ge3_funct_g in FD.
    inversion FD; subst. exact I.
  - change (Genv.find_comp ge3 (Vptr 2%positive Ptrofs.zero) = c2). apply ge3_comp_g.
  - rewrite ge3_policy. simpl. left. reflexivity.
  - rewrite ge3_policy. simpl. left. reflexivity.
Qed.

Lemma asm_step_call:
  forall m0, Asm.step (comp_of_main prog3) ge3 (s1 m0) tr3 (State st2 rs2 m0).
Proof.
  intros m0. unfold s1.
  eapply exec_step_internal_call with
    (b := 1%positive) (ofs := Ptrofs.add Ptrofs.zero Ptrofs.one) (f := f_main)
    (i := Pjal_s g_id signature_main true) (sig := signature_main)
    (b' := 2%positive) (ofs' := Ptrofs.zero) (cp := c1) (args := nil).
  - apply rs1_PC.
  - apply ge3_funct_main.
  - rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_one. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply rs2_PC.
  - apply allowed_main_g.
  - apply ge3_comp_main.
  - unfold update_stack_call. rewrite rs2_PC, rs2_RA, ge3_comp_g. reflexivity.
  - constructor.
  - intros _. constructor.
  - rewrite ge3_comp_g. change (comp_of f_main) with c1.
    eapply call_trace_cross.
    + reflexivity.
    + reflexivity.
    + apply ge3_invert_g.
    + constructor.
Qed.

(** ** No [step_fix] step from the initial state *)

Lemma not_map_builtin_res:
  forall res, BR (IR X31) <> map_builtin_res preg_of res.
Proof.
  intros res E. destruct res; simpl in E; try discriminate.
  inversion E as [E']. destruct x; discriminate.
Qed.

Lemma s0_instr:
  forall b ofs f i,
    rs0 PC = Vptr b ofs ->
    Genv.find_funct_ptr ge3 b = Some (Internal f) ->
    find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
    b = 1%positive /\ ofs = Ptrofs.zero /\ f = f_main /\ i = Pbuiltin ef_dbg nil (BR (IR X31)).
Proof.
  intros b ofs f i PC FF FI.
  rewrite rs0_PC in PC. inversion PC; subst.
  rewrite ge3_funct_main in FF. inversion FF; subst.
  rewrite Ptrofs.unsigned_zero in FI. simpl in FI. inversion FI; subst. auto.
Qed.

Lemma s0_not_external:
  forall b ofs ef, rs0 PC = Vptr b ofs -> Genv.find_funct_ptr ge3 b = Some (External ef) -> False.
Proof.
  intros b ofs ef PC FF. rewrite rs0_PC in PC. inversion PC; subst.
  rewrite ge3_funct_main in FF. discriminate.
Qed.

Ltac use_s0_instr :=
  match goal with
  | H1: rs0 PC = Vptr ?b ?ofs, H2: Genv.find_funct_ptr _ ?b = Some (Internal ?f),
    H3: find_instr _ (fn_code ?f) = Some _ |- _ =>
      destruct (s0_instr _ _ _ _ H1 H2 H3) as (? & ? & ? & ?); subst
  end.

Lemma no_step_fix_s0:
  forall m0 t s, ~ step_fix (comp_of_main prog3) ge3 (s0 m0) t s.
Proof.
  intros m0 t s STEP. unfold s0 in STEP.
  inversion STEP; subst.
  - (* internal: exec_instr of Pbuiltin is Stuck *)
    use_s0_instr. discriminate.
  - use_s0_instr. discriminate.
  - use_s0_instr. discriminate.
  - (* builtin: the result register is not in the image of preg_of *)
    use_s0_instr.
    match goal with
    | H: Pbuiltin _ _ _ = Pbuiltin _ _ _ |- _ => inversion H as [[E1 E2 E3]]
    end.
    eapply not_map_builtin_res; eauto.
  - eapply s0_not_external; eauto.
Qed.

Theorem builtin_res_counterexample_E0:
  (exists s, initial_state prog3 s) /\
  (forall s, initial_state prog3 s ->
     exists s', star (Asm.step (comp_of_main prog3)) (Genv.globalenv prog3) s E0 s' /\
                ~ star (step_fix (comp_of_main prog3)) (Genv.globalenv prog3) s E0 s').
Proof.
  split.
  - destruct prog3_init_mem_exists as [m0 INIT]. exists (s0 m0). apply s0_initial; auto.
  - intros s INIT. destruct (initial_state_s0 s INIT) as (m0 & IM & ->).
    exists (s1 m0). split.
    + apply star_one. apply asm_step_builtin.
    + intros STAR.
      destruct (star_from_stuck _ _ _ _ _ _ _ (no_step_fix_s0 m0) STAR) as [_ E].
      apply (s1_not_s0 m0). exact E.
Qed.

Theorem builtin_res_counterexample:
  (exists s, initial_state prog3 s) /\
  (forall s, initial_state prog3 s ->
     exists s', star (Asm.step (comp_of_main prog3)) (Genv.globalenv prog3) s tr3 s') /\
  (forall s s', initial_state prog3 s ->
     ~ star (step_fix (comp_of_main prog3)) (Genv.globalenv prog3) s tr3 s').
Proof.
  split; [| split].
  - destruct prog3_init_mem_exists as [m0 INIT]. exists (s0 m0). apply s0_initial; auto.
  - intros s INIT. destruct (initial_state_s0 s INIT) as (m0 & IM & ->).
    exists (State st2 rs2 m0). eapply star_two.
    + apply asm_step_builtin.
    + apply asm_step_call.
    + reflexivity.
  - intros s s' INIT. destruct (initial_state_s0 s INIT) as (m0 & IM & ->).
    eapply no_star_nonempty_from_stuck. apply no_step_fix_s0.
Qed.

Theorem not_step_fix_fix_builtin_res: ~ step_fix_fix_stmt.
Proof.
  intros SFF.
  destruct builtin_res_counterexample as ([s INIT] & RUN & NORUN).
  destruct (RUN s INIT) as [s' STAR].
  apply (NORUN s s' INIT). apply SFF. exact STAR.
Qed.
