(** * Counterexample 2 (CALLSIG), from the initial state of a whole program.

    A hand-written Asm program [prog2] with two compartments:
<<
      // compartment c1 (hand-written Asm)   // compartment c2
      main:  jal g   (call annotated with     int g(int x) { return 0; }
                      signature int(void))
>>
    policy "c1 imports g from c2, c2 exports g".  The call instruction
    [Pjal_s g signature_main true] carries the signature [int(void)] while [g]
    has signature [int(int)].  There are no global variables, so
    [public_first_order] holds in the initial memory (the only public
    symbols are the two functions, whose blocks have [Nonempty] permission
    only).

    - [Asm.step] takes the call (the Asm step on ccs-backtranslation does not check the
      signature of a call against the callee);
    - [step_fix] cannot take any step from the initial state: the only
      candidate rule [exec_step_fix_internal_call] requires CALLSIG,
      [exists fd, find_funct_ptr ge b' = Some fd /\ sig = funsig fd];
    - CHECKPUB holds ([init_public_first_order]); all other premises are those
      of the Asm step, so CALLSIG is the only violated check. *)

Require Import Coqlib Maps Integers Values Memory Globalenvs.
Require Import AST Smallstep Events.
Require Import riscV.Asm.
Require Import StepFixFix.StepFixFixCommon.

Definition main_id : ident := 1%positive.
Definition g_id : ident := 2%positive.

Definition c1 : compartment := 2%positive. (* main *)
Definition c2 : compartment := 3%positive. (* g *)

Definition sig_g : signature :=
  {| sig_args := Tint :: nil; sig_res := Tint; sig_cc := cc_default |}.

(** The call is annotated with [signature_main] = [int(void)], not [sig_g]. *)
Definition f_main : Asm.function :=
  {| fn_comp := c1; fn_sig := signature_main;
     fn_code := Pjal_s g_id signature_main true :: Pj_r X1 signature_main true :: nil |}.

Definition f_g : Asm.function :=
  {| fn_comp := c2; fn_sig := sig_g;
     fn_code := Paddiw X10 X0 Int.zero :: Pj_r X1 sig_g true :: nil |}.

Definition pol2 : Policy.t :=
  Policy.mkpolicy (PTree.set c2 (g_id :: nil) (PTree.empty _))
                  (PTree.set c1 ((c2, g_id) :: nil) (PTree.empty _)).

Definition prog2 : Asm.program :=
  {| prog_defs := (main_id, Gfun (Internal f_main)) :: (g_id, Gfun (Internal f_g)) :: nil;
     prog_public := main_id :: g_id :: nil;
     prog_main := main_id;
     prog_pol := pol2 |}.

Definition ge2 : Asm.genv := Genv.globalenv prog2.

Lemma ge2_symb_main: Genv.find_symbol ge2 main_id = Some 1%positive.
Proof. reflexivity. Qed.
Lemma ge2_symb_g: Genv.find_symbol ge2 g_id = Some 2%positive.
Proof. reflexivity. Qed.
Lemma ge2_funct_main: Genv.find_funct_ptr ge2 1%positive = Some (Internal f_main).
Proof. reflexivity. Qed.
Lemma ge2_funct_g: Genv.find_funct_ptr ge2 2%positive = Some (Internal f_g).
Proof. reflexivity. Qed.
Lemma ge2_invert_g: Genv.invert_symbol ge2 2%positive = Some g_id.
Proof. reflexivity. Qed.
Lemma ge2_policy: Genv.genv_policy ge2 = pol2.
Proof. reflexivity. Qed.

Lemma ge2_comp_main: Genv.find_comp_ignore_offset ge2 (Vptr 1%positive Ptrofs.zero) = c1.
Proof.
  unfold Genv.find_comp_ignore_offset, Genv.find_comp.
  rewrite Genv.find_funct_find_funct_ptr, ge2_funct_main. reflexivity.
Qed.

Lemma ge2_comp_g: Genv.find_comp_ignore_offset ge2 (Vptr 2%positive Ptrofs.zero) = c2.
Proof.
  unfold Genv.find_comp_ignore_offset, Genv.find_comp.
  rewrite Genv.find_funct_find_funct_ptr, ge2_funct_g. reflexivity.
Qed.

Lemma comp_of_main2: comp_of_main prog2 = c1.
Proof.
  unfold comp_of_main. cbv zeta. change (Genv.globalenv prog2) with ge2.
  change (prog_main prog2) with main_id.
  rewrite ge2_symb_main. apply ge2_comp_main.
Qed.

(** ** Initial memory: exists, and public symbols are first-order *)

Lemma prog2_init_mem_exists: exists m0, Genv.init_mem prog2 = Some m0.
Proof.
  apply Genv.init_mem_exists.
  intros id v IN. simpl in IN.
  destruct IN as [E | [E | []]]; discriminate.
Qed.

Lemma ge2_symbols_are_functions:
  forall id b, Genv.find_symbol ge2 id = Some b -> exists fd, Genv.find_funct_ptr ge2 b = Some fd.
Proof.
  intros id b FIND.
  pose proof (Genv.find_symbol_inversion _ _ FIND) as IN. simpl in IN.
  destruct IN as [E | [E | []]]; subst.
  - rewrite ge2_symb_main in FIND. inversion FIND; subst. eexists. apply ge2_funct_main.
  - rewrite ge2_symb_g in FIND. inversion FIND; subst. eexists. apply ge2_funct_g.
Qed.

(** CHECKPUB holds in the initial memory. *)
Lemma init_public_first_order:
  forall m0, Genv.init_mem prog2 = Some m0 -> public_first_order ge2 m0.
Proof.
  intros m0 INIT id b ofs PUB FIND READ. exfalso.
  destruct (ge2_symbols_are_functions id b FIND) as [fd FF].
  destruct (Genv.init_mem_characterization_2 _ _ FF INIT) as [_ PERM].
  destruct (PERM _ _ _ READ) as [_ E]. discriminate.
Qed.

(** ** The initial state and the Asm call step *)

Definition rs0 : regset :=
  (Pregmap.init Vundef)
    # PC <- (Genv.symbol_address ge2 main_id Ptrofs.zero)
    # SP <- Vnullptr
    # RA <- Vnullptr.

Definition s0 (m0: mem) : Asm.state := State initial_stack rs0 m0.

Lemma s0_initial: forall m0, Genv.init_mem prog2 = Some m0 -> initial_state prog2 (s0 m0).
Proof. intros m0 INIT. econstructor. exact INIT. Qed.

Lemma initial_state_s0: forall s, initial_state prog2 s ->
  exists m0, Genv.init_mem prog2 = Some m0 /\ s = s0 m0.
Proof. intros s INIT. inversion INIT; subst. eexists; split; eauto. Qed.

Lemma rs0_PC: rs0 PC = Vptr 1%positive Ptrofs.zero.
Proof.
  unfold rs0. rewrite Pregmap.gso by discriminate. rewrite Pregmap.gso by discriminate.
  rewrite Pregmap.gss. unfold Genv.symbol_address. rewrite ge2_symb_main. reflexivity.
Qed.

Definition rs1 : regset :=
  rs0 # PC <- (Genv.symbol_address ge2 g_id Ptrofs.zero)
      # RA <- (Val.offset_ptr (rs0 PC) Ptrofs.one).

Lemma rs1_PC: rs1 PC = Vptr 2%positive Ptrofs.zero.
Proof.
  unfold rs1. rewrite Pregmap.gso by discriminate. rewrite Pregmap.gss.
  unfold Genv.symbol_address. rewrite ge2_symb_g. reflexivity.
Qed.

Lemma rs1_RA: rs1 RA = Vptr 1%positive (Ptrofs.add Ptrofs.zero Ptrofs.one).
Proof. unfold rs1. rewrite Pregmap.gss. rewrite rs0_PC. reflexivity. Qed.

Definition st1 : stack :=
  Stackframe 1%positive c2 signature_main (rs1 SP) (Ptrofs.add Ptrofs.zero Ptrofs.one) :: nil.

Definition s1 (m0: mem) : Asm.state := State st1 rs1 m0.

Definition tr2 : trace := Event_call c1 c2 g_id nil :: nil.

Lemma exec_call_main:
  forall m0 cp, exec_instr ge2 f_main (Pjal_s g_id signature_main true) rs0 m0 cp = Next rs1 m0.
Proof. reflexivity. Qed.

Lemma allowed_main_g: Genv.allowed_call ge2 (comp_of f_main) (Vptr 2%positive Ptrofs.zero).
Proof.
  right. exists g_id, c2. split; [| split; [| split; [| split]]].
  - apply ge2_invert_g.
  - intros fd FD. rewrite Genv.find_funct_find_funct_ptr, ge2_funct_g in FD.
    inversion FD; subst. exact I.
  - change (Genv.find_comp ge2 (Vptr 2%positive Ptrofs.zero) = c2). apply ge2_comp_g.
  - rewrite ge2_policy. simpl. left. reflexivity.
  - rewrite ge2_policy. simpl. left. reflexivity.
Qed.

Lemma asm_step_call:
  forall m0, Asm.step (comp_of_main prog2) ge2 (s0 m0) tr2 (s1 m0).
Proof.
  intros m0. unfold s0, s1.
  eapply exec_step_internal_call with
    (b := 1%positive) (ofs := Ptrofs.zero) (f := f_main)
    (i := Pjal_s g_id signature_main true) (sig := signature_main)
    (b' := 2%positive) (ofs' := Ptrofs.zero) (cp := c1) (args := nil).
  - apply rs0_PC.
  - apply ge2_funct_main.
  - rewrite Ptrofs.unsigned_zero. reflexivity.
  - apply exec_call_main.
  - reflexivity.
  - apply rs1_PC.
  - apply allowed_main_g.
  - apply ge2_comp_main.
  - unfold update_stack_call. rewrite rs1_PC, rs1_RA, ge2_comp_g. reflexivity.
  - constructor.
  - intros _. constructor.
  - rewrite ge2_comp_g. change (comp_of f_main) with c1.
    eapply call_trace_cross.
    + reflexivity.
    + reflexivity.
    + apply ge2_invert_g.
    + constructor.
Qed.

(** The violated premise: CALLSIG. *)
Lemma callsig_fails:
  ~ (exists fd, Genv.find_funct_ptr ge2 2%positive = Some fd /\ signature_main = funsig fd).
Proof.
  intros (fd & FF & SG). rewrite ge2_funct_g in FF. inversion FF; subst.
  discriminate.
Qed.

(** ** No [step_fix] step from the initial state *)

Lemma s0_instr:
  forall b ofs f i,
    rs0 PC = Vptr b ofs ->
    Genv.find_funct_ptr ge2 b = Some (Internal f) ->
    find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
    b = 1%positive /\ ofs = Ptrofs.zero /\ f = f_main /\ i = Pjal_s g_id signature_main true.
Proof.
  intros b ofs f i PC FF FI.
  rewrite rs0_PC in PC. inversion PC; subst.
  rewrite ge2_funct_main in FF. inversion FF; subst.
  rewrite Ptrofs.unsigned_zero in FI. simpl in FI. inversion FI; subst. auto.
Qed.

Lemma s0_not_external:
  forall b ofs ef, rs0 PC = Vptr b ofs -> Genv.find_funct_ptr ge2 b = Some (External ef) -> False.
Proof.
  intros b ofs ef PC FF. rewrite rs0_PC in PC. inversion PC; subst.
  rewrite ge2_funct_main in FF. discriminate.
Qed.

Ltac use_s0_instr :=
  match goal with
  | H1: rs0 PC = Vptr ?b ?ofs, H2: Genv.find_funct_ptr _ ?b = Some (Internal ?f),
    H3: find_instr _ (fn_code ?f) = Some _ |- _ =>
      destruct (s0_instr _ _ _ _ H1 H2 H3) as (? & ? & ? & ?); subst
  end.

Lemma no_step_fix_s0:
  forall m0, Genv.init_mem prog2 = Some m0 ->
    forall t s, ~ step_fix (comp_of_main prog2) ge2 (s0 m0) t s.
Proof.
  intros m0 INIT t s STEP. unfold s0 in STEP.
  inversion STEP; subst.
  - use_s0_instr. discriminate.
  - (* exec_step_fix_internal_call: CALLSIG fails *)
    use_s0_instr.
    match goal with
    | H: exec_instr _ _ _ _ _ _ = Next _ _ |- _ =>
        rewrite exec_call_main in H; inversion H; subst
    end.
    rewrite rs1_PC in NEXTPC. inversion NEXTPC; subst.
    match goal with
    | H: sig_call _ = Some _ |- _ => simpl in H; inversion H; subst
    end.
    apply callsig_fails. apply CALLSIG. rewrite ge2_comp_g. reflexivity.
  - use_s0_instr. discriminate.
  - use_s0_instr. discriminate.
  - eapply s0_not_external; eauto.
Qed.

(** CHECKPUB holds at this call, so the failure is due to CALLSIG alone. *)
Lemma checkpub_holds:
  forall m0, Genv.init_mem prog2 = Some m0 ->
    Genv.type_of_call ge2 (comp_of f_main)
      (Genv.find_comp_ignore_offset ge2 (Vptr 2%positive Ptrofs.zero)) = Genv.CrossCompartmentCall ->
    public_first_order ge2 m0.
Proof. intros m0 INIT _. apply init_public_first_order; auto. Qed.

Theorem callsig_counterexample:
  (exists s, initial_state prog2 s) /\
  (forall s, initial_state prog2 s ->
     exists s', star (Asm.step (comp_of_main prog2)) (Genv.globalenv prog2) s tr2 s') /\
  (forall s s', initial_state prog2 s ->
     ~ star (step_fix (comp_of_main prog2)) (Genv.globalenv prog2) s tr2 s').
Proof.
  split; [| split].
  - destruct prog2_init_mem_exists as [m0 INIT]. exists (s0 m0). apply s0_initial; auto.
  - intros s INIT. destruct (initial_state_s0 s INIT) as (m0 & IM & ->).
    exists (s1 m0). apply star_one. apply asm_step_call.
  - intros s s' INIT. destruct (initial_state_s0 s INIT) as (m0 & IM & ->).
    eapply no_star_nonempty_from_stuck. apply no_step_fix_s0; auto.
Qed.

Theorem not_step_fix_fix_callsig: ~ step_fix_fix_stmt.
Proof.
  intros SFF.
  destruct callsig_counterexample as ([s INIT] & RUN & NORUN).
  destruct (RUN s INIT) as [s' STAR].
  apply (NORUN s s' INIT). apply SFF. exact STAR.
Qed.
