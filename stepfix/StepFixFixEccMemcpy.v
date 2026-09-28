(** * Counterexample 4 (ECC, memcpy into a public global), from the initial
    state of a whole program.

    [prog4] is the Asm analogue of the C program
<<
      // compartment c1                       // compartment c2
      struct S { int a; } dst, src = { 0 };   int g(void) { return 0; }
      int main(void) { dst = src; g(); ... }
>>
    (policy "c1 imports g from c2, c2 exports g").  In CompCert, a struct
    assignment is compiled (Cshmgen [make_store], access mode [By_copy]) to the
    builtin [EF_memcpy sz al], which stays a [Pbuiltin] in Asm.  Here the
    builtin arguments are [BA_addrglobal dst 0] and [BA_addrglobal src 0]
    (compiled code would first load the addresses into registers; this does not
    matter for the argument).

    [step_fix]'s builtin rule requires ECC = [external_call_conds ef ge m vargs],
    which for [EF_memcpy] is [EF_memcpy_dest_not_pub]: the destination block
    must not be public.  [dst] is public, so:

    - [Asm.step] executes the memcpy and then the cross-compartment call to [g],
      producing the trace [Event_call c1 c2 g nil :: nil];
    - [step_fix] has no step from the initial state (the builtin rule fails
      only on ECC: the result [BR_none] is [map_builtin_res preg_of BR_none]).

    Initial memory is reasoned about abstractly. *)

Require Import Coqlib Maps Integers Values Memory Globalenvs.
Require Import AST Smallstep Events Machregs.
Require Import riscV.Asm.
Require Import StepFixFix.StepFixFixCommon.

Definition dst_id : ident := 1%positive.
Definition src_id : ident := 2%positive.
Definition main_id : ident := 3%positive.
Definition g_id : ident := 4%positive.

Definition c1 : compartment := 2%positive. (* main, dst, src *)
Definition c2 : compartment := 3%positive. (* g *)

Definition gv_int0 : globvar unit :=
  {| gvar_info := tt; gvar_comp := c1; gvar_init := Init_int32 Int.zero :: nil;
     gvar_readonly := false; gvar_volatile := false |}.

Definition ef_cpy : external_function := EF_memcpy c1 4 4.
Definition args_cpy : list (builtin_arg preg) :=
  BA_addrglobal dst_id Ptrofs.zero :: BA_addrglobal src_id Ptrofs.zero :: nil.

Definition f_main : Asm.function :=
  {| fn_comp := c1; fn_sig := signature_main;
     fn_code := Pbuiltin ef_cpy args_cpy BR_none
                :: Pjal_s g_id signature_main true
                :: Pj_r X1 signature_main true :: nil |}.

Definition f_g : Asm.function :=
  {| fn_comp := c2; fn_sig := signature_main;
     fn_code := Paddiw X10 X0 Int.zero :: Pj_r X1 signature_main true :: nil |}.

Definition pol4 : Policy.t :=
  Policy.mkpolicy (PTree.set c2 (g_id :: nil) (PTree.empty _))
                  (PTree.set c1 ((c2, g_id) :: nil) (PTree.empty _)).

Definition prog4 : Asm.program :=
  {| prog_defs := (dst_id, Gvar gv_int0) :: (src_id, Gvar gv_int0)
                  :: (main_id, Gfun (Internal f_main)) :: (g_id, Gfun (Internal f_g)) :: nil;
     prog_public := dst_id :: src_id :: main_id :: g_id :: nil;
     prog_main := main_id;
     prog_pol := pol4 |}.

Definition ge4 : Asm.genv := Genv.globalenv prog4.

Lemma ge4_symb_main: Genv.find_symbol ge4 main_id = Some 3%positive.
Proof. reflexivity. Qed.
Lemma ge4_symb_g: Genv.find_symbol ge4 g_id = Some 4%positive.
Proof. reflexivity. Qed.
Lemma ge4_var_dst: Genv.find_var_info ge4 1%positive = Some gv_int0.
Proof. reflexivity. Qed.
Lemma ge4_var_src: Genv.find_var_info ge4 2%positive = Some gv_int0.
Proof. reflexivity. Qed.
Lemma ge4_funct_main: Genv.find_funct_ptr ge4 3%positive = Some (Internal f_main).
Proof. reflexivity. Qed.
Lemma ge4_funct_g: Genv.find_funct_ptr ge4 4%positive = Some (Internal f_g).
Proof. reflexivity. Qed.
Lemma ge4_invert_g: Genv.invert_symbol ge4 4%positive = Some g_id.
Proof. reflexivity. Qed.
Lemma ge4_policy: Genv.genv_policy ge4 = pol4.
Proof. reflexivity. Qed.

(** The destination block (block 1, symbol [dst]) is public. *)
Lemma ge4_dst_public: block_public ge4 1%positive.
Proof. exists dst_id. split; reflexivity. Qed.

Lemma ge4_comp_main: Genv.find_comp_ignore_offset ge4 (Vptr 3%positive Ptrofs.zero) = c1.
Proof.
  unfold Genv.find_comp_ignore_offset, Genv.find_comp.
  rewrite Genv.find_funct_find_funct_ptr, ge4_funct_main. reflexivity.
Qed.

Lemma ge4_comp_g: Genv.find_comp_ignore_offset ge4 (Vptr 4%positive Ptrofs.zero) = c2.
Proof.
  unfold Genv.find_comp_ignore_offset, Genv.find_comp.
  rewrite Genv.find_funct_find_funct_ptr, ge4_funct_g. reflexivity.
Qed.

(** ** Initial memory *)

Lemma prog4_init_mem_exists: exists m0, Genv.init_mem prog4 = Some m0.
Proof.
  apply Genv.init_mem_exists.
  intros id v IN. simpl in IN.
  destruct IN as [E | [E | [E | [E | []]]]]; inversion E; subst; simpl.
  - split.
    + split; [apply Z.divide_0_r | exact I].
    + intros i o [H | []]. discriminate.
  - split.
    + split; [apply Z.divide_0_r | exact I].
    + intros i o [H | []]. discriminate.
Qed.

(** The memcpy of [src] (4 bytes) into [dst] succeeds in the initial memory. *)
Lemma memcpy_succeeds:
  forall m0, Genv.init_mem prog4 = Some m0 ->
    exists m1, external_call ef_cpy ge4
                 (Vptr 1%positive Ptrofs.zero :: Vptr 2%positive Ptrofs.zero :: nil)
                 m0 E0 Vundef m1.
Proof.
  intros m0 INIT.
  destruct (Genv.init_mem_characterization _ _ ge4_var_dst INIT) as (RPD & _ & _ & LBD).
  destruct (Genv.init_mem_characterization _ _ ge4_var_src INIT) as (_ & _ & _ & LBS).
  specialize (LBD eq_refl). specialize (LBS eq_refl).
  change (init_data_list_size (gvar_init gv_int0)) with 4%Z in RPD, LBD, LBS.
  change (gvar_comp gv_int0) with c1 in LBD, LBS.
  set (bytes := Genv.bytes_of_init_data_list (Genv.globalenv prog4) (gvar_init gv_int0)) in *.
  assert (LEN: Z.of_nat (length bytes) = 4%Z).
  { rewrite (Mem.loadbytes_length _ _ _ _ _ _ LBS). reflexivity. }
  assert (ACC: Mem.can_access_block m0 1%positive (Some c1)).
  { eapply Mem.loadbytes_can_access_block_inj. exact LBD. }
  destruct (Mem.range_perm_storebytes m0 1%positive 0 bytes c1) as [m1 ST].
  { rewrite LEN. intros ofs R. eapply Mem.perm_implies. apply RPD. simpl in R. lia. constructor. }
  { exact ACC. }
  exists m1. simpl. econstructor.
  - right; right; left; reflexivity.
  - lia.
  - apply Z.divide_refl.
  - intros _. rewrite Ptrofs.unsigned_zero. apply Z.divide_0_r.
  - intros _. rewrite Ptrofs.unsigned_zero. apply Z.divide_0_r.
  - left. discriminate.
  - rewrite Ptrofs.unsigned_zero. exact LBS.
  - rewrite Ptrofs.unsigned_zero. exact ST.
Qed.

(** ** Initial state, the memcpy step and the call step *)

Definition rs0 : regset :=
  (Pregmap.init Vundef)
    # PC <- (Genv.symbol_address ge4 main_id Ptrofs.zero)
    # SP <- Vnullptr
    # RA <- Vnullptr.

Definition s0 (m0: mem) : Asm.state := State initial_stack rs0 m0.

Lemma s0_initial: forall m0, Genv.init_mem prog4 = Some m0 -> initial_state prog4 (s0 m0).
Proof. intros m0 INIT. econstructor. exact INIT. Qed.

Lemma initial_state_s0: forall s, initial_state prog4 s ->
  exists m0, Genv.init_mem prog4 = Some m0 /\ s = s0 m0.
Proof. intros s INIT. inversion INIT; subst. eexists; split; eauto. Qed.

Lemma rs0_PC: rs0 PC = Vptr 3%positive Ptrofs.zero.
Proof.
  unfold rs0. rewrite Pregmap.gso by discriminate. rewrite Pregmap.gso by discriminate.
  rewrite Pregmap.gss. unfold Genv.symbol_address. rewrite ge4_symb_main. reflexivity.
Qed.

Definition rs1 : regset :=
  nextinstr (set_res BR_none Vundef
               (undef_regs (map preg_of (destroyed_by_builtin ef_cpy))
                  (rs0 # X1 <- Vundef # X31 <- Vundef))).

Lemma rs1_PC: rs1 PC = Vptr 3%positive (Ptrofs.add Ptrofs.zero Ptrofs.one).
Proof. unfold rs1, nextinstr. rewrite Pregmap.gss. reflexivity. Qed.

Lemma asm_step_memcpy:
  forall m0 m1,
    external_call ef_cpy ge4 (Vptr 1%positive Ptrofs.zero :: Vptr 2%positive Ptrofs.zero :: nil)
                  m0 E0 Vundef m1 ->
    Asm.step (comp_of_main prog4) ge4 (s0 m0) E0 (State initial_stack rs1 m1).
Proof.
  intros m0 m1 EC. unfold s0.
  eapply exec_step_builtin with
    (b := 3%positive) (ofs := Ptrofs.zero) (f := f_main) (ef := ef_cpy)
    (args := args_cpy) (res := BR_none)
    (vargs := Vptr 1%positive Ptrofs.zero :: Vptr 2%positive Ptrofs.zero :: nil) (vres := Vundef).
  - apply rs0_PC.
  - apply ge4_funct_main.
  - rewrite Ptrofs.unsigned_zero. reflexivity.
  - constructor.
    + change (Vptr 1%positive Ptrofs.zero) with (Senv.symbol_address ge4 dst_id Ptrofs.zero).
      constructor.
    + constructor.
      * change (Vptr 2%positive Ptrofs.zero) with (Senv.symbol_address ge4 src_id Ptrofs.zero).
        constructor.
      * constructor.
  - exact EC.
  - reflexivity.
  - reflexivity.
Qed.

Definition rs2 : regset :=
  rs1 # PC <- (Genv.symbol_address ge4 g_id Ptrofs.zero)
      # RA <- (Val.offset_ptr (rs1 PC) Ptrofs.one).

Lemma rs2_PC: rs2 PC = Vptr 4%positive Ptrofs.zero.
Proof.
  unfold rs2. rewrite Pregmap.gso by discriminate. rewrite Pregmap.gss.
  unfold Genv.symbol_address. rewrite ge4_symb_g. reflexivity.
Qed.

Lemma rs2_RA: rs2 RA = Vptr 3%positive (Ptrofs.add (Ptrofs.add Ptrofs.zero Ptrofs.one) Ptrofs.one).
Proof. unfold rs2. rewrite Pregmap.gss. rewrite rs1_PC. reflexivity. Qed.

Definition st2 : stack :=
  Stackframe 3%positive c2 signature_main (rs2 SP)
             (Ptrofs.add (Ptrofs.add Ptrofs.zero Ptrofs.one) Ptrofs.one) :: nil.

Definition tr4 : trace := Event_call c1 c2 g_id nil :: nil.

Lemma allowed_main_g: Genv.allowed_call ge4 (comp_of f_main) (Vptr 4%positive Ptrofs.zero).
Proof.
  right. exists g_id, c2. split; [| split; [| split; [| split]]].
  - apply ge4_invert_g.
  - intros fd FD. rewrite Genv.find_funct_find_funct_ptr, ge4_funct_g in FD.
    inversion FD; subst. exact I.
  - change (Genv.find_comp ge4 (Vptr 4%positive Ptrofs.zero) = c2). apply ge4_comp_g.
  - rewrite ge4_policy. simpl. left. reflexivity.
  - rewrite ge4_policy. simpl. left. reflexivity.
Qed.

Lemma asm_step_call:
  forall m1, Asm.step (comp_of_main prog4) ge4 (State initial_stack rs1 m1) tr4 (State st2 rs2 m1).
Proof.
  intros m1.
  eapply exec_step_internal_call with
    (b := 3%positive) (ofs := Ptrofs.add Ptrofs.zero Ptrofs.one) (f := f_main)
    (i := Pjal_s g_id signature_main true) (sig := signature_main)
    (b' := 4%positive) (ofs' := Ptrofs.zero) (cp := c1) (args := nil).
  - apply rs1_PC.
  - apply ge4_funct_main.
  - rewrite Ptrofs.add_zero_l, Ptrofs.unsigned_one. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply rs2_PC.
  - apply allowed_main_g.
  - apply ge4_comp_main.
  - unfold update_stack_call. rewrite rs2_PC, rs2_RA, ge4_comp_g. reflexivity.
  - constructor.
  - intros _. constructor.
  - rewrite ge4_comp_g. change (comp_of f_main) with c1.
    eapply call_trace_cross.
    + reflexivity.
    + reflexivity.
    + apply ge4_invert_g.
    + constructor.
Qed.

(** ** No [step_fix] step from the initial state *)

Lemma s0_instr:
  forall b ofs f i,
    rs0 PC = Vptr b ofs ->
    Genv.find_funct_ptr ge4 b = Some (Internal f) ->
    find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
    b = 3%positive /\ ofs = Ptrofs.zero /\ f = f_main /\ i = Pbuiltin ef_cpy args_cpy BR_none.
Proof.
  intros b ofs f i PC FF FI.
  rewrite rs0_PC in PC. inversion PC; subst.
  rewrite ge4_funct_main in FF. inversion FF; subst.
  rewrite Ptrofs.unsigned_zero in FI. simpl in FI. inversion FI; subst. auto.
Qed.

Lemma s0_not_external:
  forall b ofs ef, rs0 PC = Vptr b ofs -> Genv.find_funct_ptr ge4 b = Some (External ef) -> False.
Proof.
  intros b ofs ef PC FF. rewrite rs0_PC in PC. inversion PC; subst.
  rewrite ge4_funct_main in FF. discriminate.
Qed.

Lemma eval_args_cpy:
  forall m vargs,
    eval_builtin_args ge4 rs0 (rs0 SP) m args_cpy vargs ->
    vargs = Vptr 1%positive Ptrofs.zero :: Vptr 2%positive Ptrofs.zero :: nil.
Proof.
  intros m vargs EV.
  inversion EV as [| a1 al1 v1 vl1 EV1 EVS]; subst.
  inversion EVS as [| a2 al2 v2 vl2 EV2 EVS']; subst.
  inversion EVS'; subst.
  inversion EV1; subst. inversion EV2; subst. reflexivity.
Qed.

(** The violated premise: ECC for [EF_memcpy] (destination is public). *)
Lemma ecc_fails:
  forall m, ~ external_call_conds ef_cpy ge4 m
                (Vptr 1%positive Ptrofs.zero :: Vptr 2%positive Ptrofs.zero :: nil).
Proof. intros m ECC. apply ECC. apply ge4_dst_public. Qed.

(** The other syntactic requirement of the [step_fix] builtin rule holds. *)
Lemma builtin_res_ok: (BR_none : builtin_res preg) = map_builtin_res preg_of BR_none.
Proof. reflexivity. Qed.

Ltac use_s0_instr :=
  match goal with
  | H1: rs0 PC = Vptr ?b ?ofs, H2: Genv.find_funct_ptr _ ?b = Some (Internal ?f),
    H3: find_instr _ (fn_code ?f) = Some _ |- _ =>
      destruct (s0_instr _ _ _ _ H1 H2 H3) as (? & ? & ? & ?); subst
  end.

Lemma no_step_fix_s0:
  forall m0 t s, ~ step_fix (comp_of_main prog4) ge4 (s0 m0) t s.
Proof.
  intros m0 t s STEP. unfold s0 in STEP.
  inversion STEP; subst.
  - use_s0_instr. discriminate.
  - use_s0_instr. discriminate.
  - use_s0_instr. discriminate.
  - (* builtin: ECC fails *)
    use_s0_instr.
    match goal with
    | H: Pbuiltin _ _ _ = Pbuiltin _ _ _ |- _ => inversion H; subst
    end.
    match goal with
    | H: eval_builtin_args _ _ _ _ _ _ |- _ => apply eval_args_cpy in H; subst
    end.
    eapply ecc_fails; eauto.
  - eapply s0_not_external; eauto.
Qed.

Theorem ecc_memcpy_counterexample:
  (exists s, initial_state prog4 s) /\
  (forall s, initial_state prog4 s ->
     exists s', star (Asm.step (comp_of_main prog4)) (Genv.globalenv prog4) s tr4 s') /\
  (forall s s', initial_state prog4 s ->
     ~ star (step_fix (comp_of_main prog4)) (Genv.globalenv prog4) s tr4 s').
Proof.
  split; [| split].
  - destruct prog4_init_mem_exists as [m0 INIT]. exists (s0 m0). apply s0_initial; auto.
  - intros s INIT. destruct (initial_state_s0 s INIT) as (m0 & IM & ->).
    destruct (memcpy_succeeds m0 IM) as [m1 EC].
    exists (State st2 rs2 m1). eapply star_two.
    + apply asm_step_memcpy. exact EC.
    + apply asm_step_call.
    + reflexivity.
  - intros s s' INIT. destruct (initial_state_s0 s INIT) as (m0 & IM & ->).
    eapply no_star_nonempty_from_stuck. apply no_step_fix_s0.
Qed.

Theorem not_step_fix_fix_ecc_memcpy: ~ step_fix_fix_stmt.
Proof.
  intros SFF.
  destruct ecc_memcpy_counterexample as ([s INIT] & RUN & NORUN).
  destruct (RUN s INIT) as [s' STAR].
  apply (NORUN s s' INIT). apply SFF. exact STAR.
Qed.
