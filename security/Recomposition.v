Require Import Coqlib Maps Errors Integers.
Require Import Integers Floats AST Linking.
Require Import AST Globalenvs Linking Smallstep Events Behaviors Memory Values.
Require Import Op Locations Mach Conventions Asm.
Require Import Complements.

Require Import Split.

#[local] Instance has_side_stackframe: has_side stackframe :=
  { in_side s := fun '(Stackframe b _ _ _) δ => s b = δ  }.

#[local] Instance has_side_stack: has_side stack :=
  { in_side s := fun st δ => List.Forall (fun f => s |= f ∈ δ) st }.

Print Instances has_side.

#[local] Instance has_side_regset: has_side regset :=
  (* { in_side '(s, ge) := fun (rs: regset) δ => s (@Genv.find_comp fundef unit _ ge (rs PC)) = δ }. (* FIXME *) *)
  { in_side '(s, ge) := fun (rs: regset) δ => exists cp, @Genv.find_comp fundef unit _ ge (rs PC) = Some cp /\ s cp = δ }.
  

Variant match_fundef (s: split) (δ: side): unit -> fundef -> fundef -> Prop :=
  | match_function_opp: forall cp sig code code',
      s |= cp ∈ opposite δ ->
      match_fundef s δ tt (Internal {| fn_comp := cp; fn_sig := sig; fn_code := code |})
        (Internal {| fn_comp := cp; fn_sig := sig; fn_code := code' |})
  | match_external_opp: forall ef,
      s |= ef ∈ opposite δ ->
      match_fundef s δ tt (External ef) (External ef)
  | match_δ : forall fd,
      s |= fd ∈ δ ->
      match_fundef s δ tt fd fd
.

#[local] Instance has_comp_match_fundef (s: split) (δ: side): has_comp_match (match_fundef s δ).
intros ? x y H.
inv H; auto.
Qed.

Definition match_varinfo (_ _: unit) := True.

Definition match_prog (s: split) (δ: side) := match_program_gen (match_fundef s δ) match_varinfo.

Section Invariants.
  Variable s: split.

  Variant stackframe_rel (j: meminj): stackframe -> stackframe -> Prop :=
    | stackframe_related: forall b b' sg sp sp' ofs ofs',
        Val.inject j (Vptr b ofs) (Vptr b' ofs') ->
        Val.inject j sp sp' ->
        stackframe_rel j (Stackframe b sg sp ofs) (Stackframe b' sg sp' ofs')
  .

  (* Inductive stack_rel (j: meminj) (δ: side): stack -> stack -> Prop := *)
  (* | stack_rel_empty: forall st1' st2', *)
  (*     s |= st1' ∈ opposite δ -> *)
  (*     s |= st2' ∈ opposite δ -> *)
  (*     stack_rel j δ st1' st2' *)
  (* | stack_rel_frame_in_δ: forall st1 st2 st1' st2' f1 f2, *)
  (*     s |= st1' ∈ opposite δ -> *)
  (*     s |= st2' ∈ opposite δ -> *)
  (*     s |= f1 ∈ δ -> *)
  (*     s |= f2 ∈ δ -> *)
  (*     stack_rel j δ st1 st2 -> *)
  (*     stackframe_rel j f1 f2 -> *)
  (*     stack_rel j δ (st1' ++ f1 :: st1) (st2' ++ f2 :: st2) *)
  (* . *)

  (* Lemma stack_rel_opposite_cons: *)
  (*   forall j δ f2 st1 st2, *)
  (*     s |= f2 ∈ opposite δ -> *)
  (*     stack_rel j δ st1 st2 -> *)
  (*     stack_rel j δ st1 (f2 :: st2). *)
  (* Proof. *)
  (*   intros. *)
  (*   induction H0. *)
  (*   - econstructor; simpl; eauto. *)
  (*   - eapply stack_rel_frame_in_δ with (st1' := st1') (st2' := f2 :: st2'); simpl; eauto. *)
  (* Qed. *)

  Inductive stack_rel (j__left j__right: meminj): stack -> stack -> stack -> Prop :=
  | stack_rel_empty:
    stack_rel j__left j__right nil nil nil
  | stack_rel_cons_left: forall st1 st2 st2' st3 f1 f3,
      stack_rel j__left j__right st1 st2 st3 ->
      s |= f1 ∈ Left ->
      s |= st2' ∈ Left ->
      s |= f3 ∈ Left ->
      stackframe_rel j__left f1 f3 ->
      stack_rel j__left j__right (f1 :: st1) (st2' ++ st2) (f3 :: st3)
  | stack_rel_cons_right: forall st1 st1' st2 st3 f2 f3,
      stack_rel j__left j__right st1 st2 st3 ->
      s |= st1' ∈ Right ->
      s |= f2 ∈ Right ->
      s |= f3 ∈ Right ->
      stackframe_rel j__right f2 f3 ->
      stack_rel j__left j__right (st1' ++ st1) (f2 :: st2) (f3 :: st3)
  .

  Definition regset_rel (j: meminj) (rs rs': regset): Prop :=
    forall r, Val.inject j (rs r) (rs' r).


  Record mem_rel (ge1 ge2: genv) (j: meminj) (δ: side) (m1 m2: mem) :=
    { (* Uncomment as needed *)
      same_dom: Mem.same_domain s j δ m1;

      partial_mem_inject: Mem.inject j m1 m2;

      delta_zero: Mem.delta_zero j;

      symb_inj: symbols_inject j ge1 ge2;
      (* pres_globals: meminj_preserves_globals ge1 j; *)
      ple_nextblock1: Ple (Senv.nextblock ge1) (Mem.nextblock m1);
      ple_nextblock2: Ple (Senv.nextblock ge2) (Mem.nextblock m2);

      (* Functions *)
      funct_preserved1: forall b fd, Genv.find_funct_ptr ge1 b = Some fd -> j b = Some (b, 0);
      funct_preserved2: forall b1 b2 fd, Genv.find_funct_ptr ge2 b2 = Some fd -> j b1 = Some (b2, 0) -> b1 = b2;
      (* Varinfo *)
      var_info_valid: forall b gv, Genv.find_var_info ge2 b = Some gv -> Mem.valid_block m2 b;

      (* genv_preserved: Separation.globalenv_preserved ge1 j (Senv.nextblock ge1); *)

      same_high_half: forall id ofs,
        Val.inject j (high_half ge1 id ofs) (high_half ge2 id ofs)
    }.

  Inductive strong_equivalence (ge ge': genv) (j: meminj) (δ: side): state -> state -> Prop :=
  | strong_equivalence_State: forall st st' rs rs' m m',
      (s, ge) |= rs ∈ δ ->
      (* (s, ge') |= rs' ∈ δ -> *)
      (* stack_rel j δ st st' -> *)
      regset_rel j rs rs' ->
      mem_rel ge ge' j δ m m' ->
      strong_equivalence ge ge' j δ (State st rs m) (State st' rs' m')
  | strong_equivalence_ReturnState: forall st st' rs rs' m m',
      (s, ge) |= rs ∈ δ ->
      (* (s, ge') |= rs' ∈ δ -> *)
      (* stack_rel j δ st st' -> *)
      regset_rel j rs rs' ->
      mem_rel ge ge' j δ m m' ->
      strong_equivalence ge ge' j δ (ReturnState st rs m default_compartment) (ReturnState st' rs' m' default_compartment) (* FIXME *)
  .

  Inductive weak_equivalence (ge ge': genv) (j: meminj) (δ: side): state -> state -> Prop :=
  | weak_equivalence_State: forall st st' rs rs' m m',
      (s, ge) |= rs ∈ opposite δ ->
      (* (s, ge') |= rs' ∈ opposite δ -> *)
      (* stack_rel j δ st st' -> *)
      mem_rel ge ge' j δ m m' ->
      weak_equivalence ge ge' j δ (State st rs m) (State st' rs' m')
  | weak_equivalence_ReturnState: forall st st' rs rs' m m',
      (s, m) |= rs PC ∈ opposite δ ->
      (* (s, m') |= rs' PC ∈ opposite δ -> *)
      (* stack_rel j δ st st' -> *)
      mem_rel ge ge' j δ m m' ->
      weak_equivalence ge ge' j δ (ReturnState st rs m default_compartment) (ReturnState st' rs' m' default_compartment) (* FIXME *)
  .

End Invariants.


Section Simulation.
  Context (c1 c2 p1 p2: Asm.program).
  Variable s: split.

  Context (W1 W2 W3: Asm.program).
  Hypothesis c1_p1: link p1 c1 = Some W1.
  Hypothesis c2_p2: link p2 c2 = Some W2.
  Hypothesis c2_p1: link p1 c2 = Some W3.

  Hypothesis match_W1_W3: match_prog s Left tt W1 W3.
  Hypothesis match_W2_W3: match_prog s Right tt W2 W3.

  (* Context (ge1 ge2: genv). *)
  Notation ge1 := (Genv.globalenv W1).
  Notation ge2 := (Genv.globalenv W2).
  Notation ge3 := (Genv.globalenv W3).

  Hypothesis same_low_half1: low_half ge1 = low_half ge3.
  Hypothesis same_low_half2: low_half ge2 = low_half ge3.
  Hypothesis same_high_half1: high_half ge1 = high_half ge3.
  Hypothesis same_high_half2: high_half ge2 = high_half ge3.

  Let single_L1 := sd_traces (semantics_determinate W1).
  Let single_L2 := sd_traces (semantics_determinate W2).
  Let single_L3 := sd_traces (semantics_determinate W3).

  Lemma public_symbol_eq21: forall (id: ident),
      Senv.public_symbol (symbolenv (semantics W2)) id = Senv.public_symbol (symbolenv (semantics W1)) id.
  Proof.
    apply Genv.senv_match in match_W1_W3 as [? [? ?]], match_W2_W3 as [? [? ?]]. simpl in *; now intuition.
  Qed.

  Lemma public_symbol_eq32: forall (id: ident),
      Senv.public_symbol (symbolenv (semantics W3)) id = Senv.public_symbol (symbolenv (semantics W2)) id.
  Proof.
    apply Genv.senv_match in match_W1_W3 as [? [? ?]], match_W2_W3 as [? [? ?]]. simpl in *; now intuition.
  Qed.

  Local Arguments comp_of /.
  Local Arguments Genv.find_comp _ /.

  Ltac RecompSimpl :=
    (* unfold ge1 in *; *)
    (* unfold ge2 in *; *)
    (* unfold ge3 in *; *)
    repeat (simpl in *;
            multimatch goal with
            | H: ?rs PC = _, H': context [ ?rs PC ] |- _ => rewrite H in H'; simpl in *; try congruence
            | H: Genv.find_funct_ptr ?ge ?b = _, H': context [ Genv.find_funct_ptr ?ge ?b ] |- _ =>
                rewrite H in H'; simpl in *; try congruence
            | _: context [ Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero ] |- _ => destruct Ptrofs.eq_dec; [| contradiction]
            | H: regset_rel _ _ _ |- context [PC] =>
                let H' := fresh "H" in
                assert (H' := H);
                specialize (H' PC); inv H'; try congruence
            | H: Vptr _ _ = Vptr _ _ |- _ => inv H
            (* | H: _ = ?rs PC, H': context [ ?rs PC ] |- _ => rewrite H in H'; simpl in *; try congruence *)
            end).

  Ltac exploit_globalenv_preserved :=
    repeat match goal with
      | H: Separation.globalenv_preserved _ _ _ |- _ => destruct H as [? ? ? ? ?]
      | H: forall b, Plt b ?bound -> ?j b = Some (b, 0),
        H': ?j ?b = Some (_, _),
        H'': Genv.find_funct_ptr ?ge ?b = Some _,
        FUNCTIONS : forall b fd, Genv.find_funct_ptr ?ge b = Some fd -> Plt b _ |- _ =>
          rewrite H in H'; [inv H' | now eapply FUNCTIONS; eauto]
      end.

  (** Useful simplification tactic *)
  (** Taken from Asmgenproof1.v *)

  Ltac Simplif :=
    ((rewrite Asmgenproof0.nextinstr_inv by eauto with asmgen)
     || (rewrite Asmgenproof0.nextinstr_inv1 by eauto with asmgen)
     || (rewrite Pregmap.gss)
     || (rewrite Asmgenproof0.nextinstr_pc)
     || (rewrite Pregmap.gso by eauto with asmgen)); auto with asmgen.

  Ltac Simpl := repeat Simplif.

  (* Some tactics *)
  Ltac simpl_nextinstr_PC r :=
    destruct (Pregmap.elt_eq r PC);
    [subst r; Simpl; eapply Val.offset_ptr_inject; eauto|
      Simpl].


  Lemma ptrofs_of_int_zero:
    Ptrofs.of_int Int.zero = Ptrofs.zero.
  Proof.
    Local Transparent Ptrofs.repr Int.repr.
    simpl.
    Local Opaque Ptrofs.repr Int.repr.
    reflexivity.
  Qed.

  Lemma lt_xx_false: forall x,
    Int.lt x x = false.
  Proof.
    intros. unfold Int.lt. apply zlt_false. lia.
  Qed.

  Lemma ltu_xx_false: forall x,
    Int.ltu x x = false.
  Proof.
    intros. unfold Int.ltu. apply zlt_false. lia.
  Qed.

  Lemma lt64_xx_false: forall x,
    Int64.lt x x = false.
  Proof.
    intros. unfold Int64.lt. apply zlt_false. lia.
  Qed.

  Lemma ltu64_xx_false: forall x,
    Int64.ltu x x = false.
  Proof.
    intros. unfold Int64.ltu. apply zlt_false. lia.
  Qed.

  (* Comparisons *)

  (* TODO: rename variables *)
  Lemma cmpu_bool_preserved: forall ge ge' j δ m1' m3 v1 v2 v1' v2' op b,
      mem_rel s ge ge' j δ m1' m3 ->
      Val.inject j v1 v1' ->
      Val.inject j v2 v2' ->
      Val.cmpu_bool (Mem.valid_pointer m1') op v1 v2 = Some b ->
      Val.cmpu_bool (Mem.valid_pointer m3) op v1' v2' = Some b.
  Proof.
    intros until b. intros m1_m3 inj1 inj2.
    inv inj1; simpl; inv inj2; simpl; destruct Archi.ptr64; simpl; auto; try congruence.
    - destruct Int.eq; simpl; try congruence. destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
      eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
      clear valid. destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
      assert (delta = 0) by (eapply delta_zero; eauto); subst.
      eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
      rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'.
      now rewrite orb_true_r.
    - destruct Int.eq; simpl; try congruence. destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
      eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
      clear valid. destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
      assert (delta = 0) by (eapply delta_zero; eauto); subst.
      eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
      rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'.
      now rewrite orb_true_r.
    - destruct eq_block; subst; simpl in *; try congruence.
      + assert (b3 = b2) by congruence; subst; simpl.
        assert (delta = delta0) by congruence; subst; simpl.
        destruct eq_block; try congruence.
        destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
        eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
        clear valid.
        destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
        assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
        eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
        rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'. rewrite Ptrofs.add_zero; auto.
        clear valid'.
        destruct Mem.valid_pointer eqn:valid''; simpl; try congruence.
        assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
        eapply Mem.valid_pointer_inject in valid''; eauto using partial_mem_inject.
        rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid''. rewrite valid''. rewrite Ptrofs.add_zero; auto.
        now rewrite orb_true_r.
        clear valid.
        destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
        assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
        eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
        rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'. rewrite Ptrofs.add_zero; auto.
        rewrite orb_true_r. simpl.
        clear valid'.
        destruct Mem.valid_pointer eqn:valid''; simpl; try congruence.
        eapply Mem.valid_pointer_inject in valid''; eauto using partial_mem_inject.
        rewrite Z.add_0_r in valid''. rewrite valid''. now auto.
        clear valid''.
        destruct Mem.valid_pointer eqn:valid'''; simpl; try congruence.
        eapply Mem.valid_pointer_inject in valid'''; eauto using partial_mem_inject.
        rewrite Z.add_0_r in valid'''. rewrite valid'''.
        now rewrite orb_true_r.
      + destruct eq_block; subst; simpl in *.
        * destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
          destruct (Mem.valid_pointer m1' b0) eqn:valid'; simpl; try congruence.
          assert (delta = 0) by (eapply delta_zero; eauto); subst.
          assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
          eapply Mem.mi_no_overlap with (f := j) in n; [| now eapply partial_mem_inject; eauto].
          specialize (n H H0 (Mem.perm_cur_max _ _ _ _ ((proj1 (Mem.valid_pointer_nonempty_perm _ _ _)) valid))
                        (Mem.perm_cur_max _ _ _ _ ((proj1 (Mem.valid_pointer_nonempty_perm _ _ _)) valid')));
            rewrite !Z.add_0_r in n.
          destruct n; [contradiction |].
          eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
          eapply Mem.valid_pointer_inject_val in valid'; eauto using partial_mem_inject; rewrite valid'; simpl; auto.
          destruct op; simpl; try congruence.
          intros. inv H2. rewrite !Ptrofs.add_zero. unfold Ptrofs.eq. destruct zeq; auto; congruence.
          intros. inv H2. rewrite !Ptrofs.add_zero. unfold Ptrofs.eq. destruct zeq; auto; congruence.
        * destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
          eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
          clear valid.
          destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
          assert (delta = 0) by (eapply delta_zero; eauto); subst.
          assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
          eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
          rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'. auto.
  Qed.


  Lemma cmpu_inject:
    forall ge ge' j δ op m1 m3 v1 v1' v2 v2',
      mem_rel s ge ge' j δ m1 m3 ->
      Val.inject j v1 v1' ->
      Val.inject j v2 v2' ->
      Val.inject j (Val.cmpu (Mem.valid_pointer m1) op v1 v2)
        (Val.cmpu (Mem.valid_pointer m3) op v1' v2').
  Proof.
    intros ge ge' j δ op m1 m3 v1 v1' v2 v2' m1_m3 v1_v1' v2_v2'.
    unfold Val.cmpu.
    destruct (Val.cmpu_bool) eqn:eq_cmpu.
    - eapply cmpu_bool_preserved in eq_cmpu; eauto. rewrite eq_cmpu; now eapply Cminorgenproof.val_inject_val_of_optbool.
    - auto.
  Qed.

  (* TODO: this is the same proof as [cmpu_bool_preserved] above, but with [Int64] substituted for [Int] *)
  Lemma cmplu_bool_preserved: forall ge ge' j δ m1' m3 v1 v2 v1' v2' op b,
      mem_rel s ge ge' j δ m1' m3 ->
      Val.inject j v1 v1' ->
      Val.inject j v2 v2' ->
      Val.cmplu_bool (Mem.valid_pointer m1') op v1 v2 = Some b ->
      Val.cmplu_bool (Mem.valid_pointer m3) op v1' v2' = Some b.
  Proof.
    intros until b. intros m1_m3 inj1 inj2.
    inv inj1; simpl; inv inj2; simpl; destruct Archi.ptr64; simpl; auto; try congruence.
    - destruct Int64.eq; simpl; try congruence. destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
      eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
      clear valid. destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
      assert (delta = 0) by (eapply delta_zero; eauto); subst.
      eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
      rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'.
      now rewrite orb_true_r.
    - destruct Int64.eq; simpl; try congruence. destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
      eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
      clear valid. destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
      assert (delta = 0) by (eapply delta_zero; eauto); subst.
      eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
      rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'.
      now rewrite orb_true_r.
    - destruct eq_block; subst; simpl in *; try congruence.
      + assert (b3 = b2) by congruence; subst; simpl.
        assert (delta = delta0) by congruence; subst; simpl.
        destruct eq_block; try congruence.
        destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
        eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
        clear valid.
        destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
        assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
        eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
        rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'. rewrite Ptrofs.add_zero; auto.
        clear valid'.
        destruct Mem.valid_pointer eqn:valid''; simpl; try congruence.
        assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
        eapply Mem.valid_pointer_inject in valid''; eauto using partial_mem_inject.
        rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid''. rewrite valid''. rewrite Ptrofs.add_zero; auto.
        now rewrite orb_true_r.
        clear valid.
        destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
        assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
        eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
        rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'. rewrite Ptrofs.add_zero; auto.
        rewrite orb_true_r. simpl.
        clear valid'.
        destruct Mem.valid_pointer eqn:valid''; simpl; try congruence.
        eapply Mem.valid_pointer_inject in valid''; eauto using partial_mem_inject.
        rewrite Z.add_0_r in valid''. rewrite valid''. now auto.
        clear valid''.
        destruct Mem.valid_pointer eqn:valid'''; simpl; try congruence.
        eapply Mem.valid_pointer_inject in valid'''; eauto using partial_mem_inject.
        rewrite Z.add_0_r in valid'''. rewrite valid'''.
        now rewrite orb_true_r.
      + destruct eq_block; subst; simpl in *.
        * destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
          destruct (Mem.valid_pointer m1' b0) eqn:valid'; simpl; try congruence.
          assert (delta = 0) by (eapply delta_zero; eauto); subst.
          assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
          eapply Mem.mi_no_overlap with (f := j) in n; [| now eapply partial_mem_inject; eauto].
          specialize (n H H0 (Mem.perm_cur_max _ _ _ _ ((proj1 (Mem.valid_pointer_nonempty_perm _ _ _)) valid))
                        (Mem.perm_cur_max _ _ _ _ ((proj1 (Mem.valid_pointer_nonempty_perm _ _ _)) valid')));
            rewrite !Z.add_0_r in n.
          destruct n; [contradiction |].
          eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
          eapply Mem.valid_pointer_inject_val in valid'; eauto using partial_mem_inject; rewrite valid'; simpl; auto.
          destruct op; simpl; try congruence.
          intros. inv H2. rewrite !Ptrofs.add_zero. unfold Ptrofs.eq. destruct zeq; auto; congruence.
          intros. inv H2. rewrite !Ptrofs.add_zero. unfold Ptrofs.eq. destruct zeq; auto; congruence.
        * destruct Mem.valid_pointer eqn:valid; simpl; try congruence.
          eapply Mem.valid_pointer_inject_val in valid; eauto using partial_mem_inject; rewrite valid; simpl; auto.
          clear valid.
          destruct Mem.valid_pointer eqn:valid'; simpl; try congruence.
          assert (delta = 0) by (eapply delta_zero; eauto); subst.
          assert (delta0 = 0) by (eapply delta_zero; eauto); subst.
          eapply Mem.valid_pointer_inject in valid'; eauto using partial_mem_inject.
          rewrite Ptrofs.add_zero in *. rewrite Z.add_0_r in valid'. rewrite valid'. auto.
  Qed.

  Lemma cmplu_inject:
    forall ge ge' j δ op m1 m3 v1 v1' v2 v2',
      mem_rel s ge ge' j δ m1 m3 ->
      Val.inject j v1 v1' ->
      Val.inject j v2 v2' ->
      Val.inject j (Val.maketotal (Val.cmplu (Mem.valid_pointer m1) op v1 v2))
        (Val.maketotal (Val.cmplu (Mem.valid_pointer m3) op v1' v2')).
  Proof.
    intros ge ge' j δ op m1 m3 v1 v1' v2 v2' m1_m3 v1_v1' v2_v2'.
    unfold Val.cmplu.
    destruct (Val.cmplu_bool) eqn:eq_cmplu.
    - eapply cmplu_bool_preserved in eq_cmplu; eauto. rewrite eq_cmplu.
      simpl. now eapply Cop.val_inject_of_bool.
    - auto.
  Qed.

  Hint Resolve cmpu_inject cmplu_inject : solve_inject.
  Hint Resolve Cop.val_inject_of_bool: solve_inject.

  Local Opaque Val.add Val.addl Val.sub Val.subl
    Val.mul Val.mulhs Val.mulhu Val.mull Val.mullhs Val.mullhu
    Val.and Val.or Val.xor Val.andl Val.orl Val.xorl
    Val.shl Val.shru Val.shr Val.shll Val.shrlu Val.shrl
    Val.cmp Val.cmpl Val.cmpf Val.cmpfs
    Val.cmpu Val.cmplu
    Val.divs Val.divu Val.divls Val.divlu
    Val.mods Val.modu Val.modls Val.modlu
    Val.negfs Val.negf Val.absfs Val.absf
    Val.addfs Val.addf Val.subfs Val.subf Val.mulfs Val.mulf
    Val.divfs Val.divf.

  Locate symbols_inject.
  Lemma alloc_preserves_rel_left1:
    forall cp j__left j__right m1 m1' m2 m3 lo hi b1 rs1 rs3,
      s |= cp ∈ Left ->
      mem_rel s ge1 ge3 j__left Left m1 m3 ->
      mem_rel s ge2 ge3 j__right Right m2 m3 ->
      regset_rel j__left rs1 rs3 ->
      Mem.alloc m1 cp lo hi = (m1', b1) ->
      exists j__left' m3' b3, Mem.alloc m3 cp lo hi = (m3', b3) /\
                     mem_rel s ge1 ge3 j__left' Left m1' m3' /\
                     mem_rel s ge2 ge3 j__right Right m2 m3' /\
                     regset_rel j__left' rs1 rs3 /\
                     j__left' b1 = Some (b3, 0) /\
                     inject_incr j__left j__left'.
  Proof.
    intros cp j__left j__right m1 m1' m2 m3 lo hi b1 rs1 rs3 side_cp m1_m3 m2_m3 rs1_rs3 alloc1.
    exploit (Mem.alloc_parallel_inject j__left m1); eauto using partial_mem_inject, Z.le_refl.
    intros [j' [m3' [b3 [? [? [? [? rewr]]]]]]].
    exists j', m3', b3.
    split; [| split; [| split; [| split; [| split]]]];
      [assumption | | | intros ?; eauto using val_inject_incr | assumption | assumption].
    { clear dependent j__right.
      constructor.
      - intros b. destruct (Pos.eq_dec b b1); subst.
        + split; [| congruence].
          intros _. apply Mem.owned_new_block in alloc1. simpl in alloc1. simpl; now rewrite alloc1.
        + rewrite (rewr _ n).
          eapply same_dom in m1_m3. specialize (m1_m3 b).
          eapply Mem.alloc_block_compartment with (b' := b) in alloc1.
          simpl. rewrite alloc1. rewrite peq_false; eauto.
      - assumption.
      - intros b b' delta.
        destruct (Pos.eq_dec b b1); subst.
        + congruence.
        + rewrite (rewr _ n).
          intros G. exploit delta_zero; eauto.
      - exploit symb_inj; eauto.
        intros (A & B & C & D).
        split; [| split; [| split]].
        + intros. exploit A; eauto.
        + intros. exploit B; eauto. rewrite <- rewr. eauto.
          exploit (Mem.alloc_result m1 cp lo hi m1' b1) ; eauto. intros ->.
          exploit Senv.find_symbol_below; eauto.
          eapply ple_nextblock1 in m1_m3. intros ? ?. subst.
          exploit Plt_Ple_trans; eauto. now apply Plt_strict.
            (* exploit C; eauto. *)
        + intros. exploit C; eauto. intros ?.
          destruct H5 as [b2 ?]. exists b2.
          rewrite rewr; eauto.
          exploit (Mem.alloc_result m1 cp lo hi m1' b1) ; eauto. intros ->.
          exploit Senv.find_symbol_below; eauto.
          eapply ple_nextblock1 in m1_m3. intros ? ?. subst.
          exploit Plt_Ple_trans; eauto. now apply Plt_strict.
        + intros. destruct (Pos.eq_dec b0 b1); subst.
          * assert (Senv.block_is_volatile ge1 b1 = false).
            { destruct (Senv.block_is_volatile ge1 b1) eqn:?; auto.
              exfalso.
              exploit (Mem.alloc_result m1 cp lo hi m1' b1) ; eauto. intros ->.
              exploit Senv.block_is_volatile_below; eauto.
              eapply ple_nextblock1 in m1_m3. intros ?.
              exploit Plt_Ple_trans; eauto. intros ?. now eapply Plt_strict; eauto. }
            assert (b3 = b2) by congruence. subst b2.
            assert (Senv.block_is_volatile ge3 b3 = false).
            { destruct (Senv.block_is_volatile ge3 b3) eqn:?; auto.
              exfalso.
              exploit (Mem.alloc_result m3 cp lo hi m3' b3) ; eauto. intros ->.
              exploit Senv.block_is_volatile_below; eauto.
              eapply ple_nextblock2 in m1_m3. intros ?.
              exploit Plt_Ple_trans; eauto. intros ?. now eapply Plt_strict; eauto. }
            now congruence.
          * exploit D; eauto.
            rewrite <- rewr; eauto.
      - erewrite Mem.nextblock_alloc; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - erewrite Mem.nextblock_alloc; eauto using Ple_trans, Ple_succ, ple_nextblock2.
      - intros. exploit funct_preserved1; eauto.
      - intros. exploit funct_preserved2; eauto.
        rewrite <- rewr; eauto.
        intros ?. subst. assert (b3 = b2) by congruence; subst b3.
        apply Genv.find_funct_ptr_iff in H3.
        apply Genv.genv_defs_range in H3. apply Mem.alloc_result in H. subst.
        apply ple_nextblock2 in m1_m3. simpl in *.
        eapply Plt_strict. eapply Plt_Ple_trans; eauto.
      - intros. exploit var_info_valid; eauto. eapply Mem.valid_block_alloc. eauto.
      - intros id ofs.
        exploit same_high_half; eauto. }
    { clear dependent j__left.
      destruct m2_m3.
      constructor; eauto.
      - eapply Mem.alloc_right_inject; eauto using partial_mem_inject.
      - erewrite Mem.nextblock_alloc; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - intros. eapply Mem.valid_block_alloc; eauto. }
  Qed.

  Lemma alloc_preserves_rel_left2:
    forall cp j__left j__right m1 m1' m2 m3 lo hi b1 rs1 rs3,
      s |= cp ∈ Right ->
      mem_rel s ge1 ge3 j__left Left m1 m3 ->
      mem_rel s ge2 ge3 j__right Right m2 m3 ->
      regset_rel j__left rs1 rs3 ->
      Mem.alloc m1 cp lo hi = (m1', b1) ->
      exists j__left' m3' b3, Mem.alloc m3 cp lo hi = (m3', b3) /\
                         mem_rel s ge1 ge3 j__left' Left m1' m3' /\
                         mem_rel s ge2 ge3 j__right Right m2 m3' /\
                         regset_rel j__left' rs1 rs3 /\
                         inject_incr j__left j__left'.
  Proof.
    intros cp j__left j__right m1 m1' m2 m3 lo hi b1 rs1 rs3 side_cp m1_m3 m2_m3 rs1_rs3 alloc1.
    exploit (Mem.alloc_parallel_inject j__left m1); eauto using partial_mem_inject, Z.le_refl.
    intros [_ [m3' [b3 [alloc3 [_ [_ [_ _]]]]]]].
    exploit (Mem.alloc_left_unmapped_inject j__left m1); eauto using partial_mem_inject.
    intros [j' [inj [incr [isnone diff]]]].
    exploit Mem.alloc_right_inject; eauto. intros inj'.
    exists j', m3', b3. split; [| split; [| split; [| split]]];
      [assumption |  | | intros ?; eauto using val_inject_incr | assumption].
    { clear dependent j__right.
      constructor; auto.
      - intros b. destruct (Pos.eq_dec b b1); subst.
        + split; [congruence |].
          intros ?. apply Mem.owned_new_block in alloc1. simpl in *. rewrite alloc1 in H.
          congruence.
        + rewrite (diff _ n).
          eapply same_dom in m1_m3. specialize (m1_m3 b).
          eapply Mem.alloc_block_compartment with (b' := b) in alloc1.
          simpl. rewrite alloc1. rewrite peq_false; eauto.
    (* - auto. *)
    - intros b b' delta.
      destruct (Pos.eq_dec b b1); subst.
      + congruence.
      + rewrite (diff _ n).
        intros G. exploit delta_zero; eauto.
      - exploit symb_inj; eauto.
        intros (A & B & C & D).
        split; [| split; [| split]].
        + intros. exploit A; eauto.
        + intros. exploit B; eauto. rewrite <- diff. eauto.
          exploit (Mem.alloc_result m1 cp lo hi m1' b1) ; eauto. intros ->.
          exploit Senv.find_symbol_below; eauto.
          eapply ple_nextblock1 in m1_m3. intros ? ?. subst.
          exploit Plt_Ple_trans; eauto. now apply Plt_strict.
            (* exploit C; eauto. *)
        + intros. exploit C; eauto. intros ?.
          destruct H1 as [b2 ?]. exists b2.
          rewrite diff; eauto.
          exploit (Mem.alloc_result m1 cp lo hi m1' b1) ; eauto. intros ->.
          exploit Senv.find_symbol_below; eauto.
          eapply ple_nextblock1 in m1_m3. intros ? ?. subst.
          exploit Plt_Ple_trans; eauto. now apply Plt_strict.
        + intros. destruct (Pos.eq_dec b0 b1); subst.
          * assert (Senv.block_is_volatile ge1 b1 = false).
            { destruct (Senv.block_is_volatile ge1 b1) eqn:?; auto.
              exfalso.
              exploit (Mem.alloc_result m1 cp lo hi m1' b1) ; eauto. intros ->.
              exploit Senv.block_is_volatile_below; eauto.
              eapply ple_nextblock1 in m1_m3. intros ?.
              exploit Plt_Ple_trans; eauto. intros ?. now eapply Plt_strict; eauto. }
            assert (b3 = b2) by congruence. subst b2.
            assert (Senv.block_is_volatile ge3 b3 = false).
            { destruct (Senv.block_is_volatile ge3 b3) eqn:?; auto.
              exfalso.
              exploit (Mem.alloc_result m3 cp lo hi m3' b3) ; eauto. intros ->.
              exploit Senv.block_is_volatile_below; eauto.
              eapply ple_nextblock2 in m1_m3. intros ?.
              exploit Plt_Ple_trans; eauto. intros ?. now eapply Plt_strict; eauto. }
            now congruence.
          * exploit D; eauto.
            rewrite <- diff; eauto.
    - erewrite Mem.nextblock_alloc; eauto using Ple_trans, Ple_succ, ple_nextblock1.
    - erewrite Mem.nextblock_alloc; eauto using Ple_trans, Ple_succ, ple_nextblock2.
    - intros. exploit funct_preserved1; eauto.
    - intros. exploit funct_preserved2; eauto.
      rewrite <- diff; eauto.
      intros ?. subst. assert (b3 = b2) by congruence; subst b3.
      apply Genv.find_funct_ptr_iff in H.
      apply Genv.genv_defs_range in H. apply Mem.alloc_result in alloc3. subst.
      apply ple_nextblock2 in m1_m3. simpl in *.
      eapply Plt_strict. eapply Plt_Ple_trans; eauto.
    - intros. exploit var_info_valid; eauto. eapply Mem.valid_block_alloc. eauto.
    - intros id ofs.
      exploit same_high_half; eauto.
    }
    { clear dependent j__left.
      destruct m2_m3.
      constructor; eauto.
      - eapply Mem.alloc_right_inject; eauto using partial_mem_inject.
      - erewrite Mem.nextblock_alloc; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - intros. eapply Mem.valid_block_alloc; eauto. }
  Qed.

  Lemma alloc_preserves_rel_left:
    forall cp j__left j__right m1 m1' m2 m3 lo hi b1 rs1 rs3,
      mem_rel s ge1 ge3 j__left Left m1 m3 ->
      mem_rel s ge2 ge3 j__right Right m2 m3 ->
      regset_rel j__left rs1 rs3 ->
      Mem.alloc m1 cp lo hi = (m1', b1) ->
      exists j__left' m3' b3, Mem.alloc m3 cp lo hi = (m3', b3) /\
                         mem_rel s ge1 ge3 j__left' Left m1' m3' /\
                         mem_rel s ge2 ge3 j__right Right m2 m3' /\
                         regset_rel j__left' rs1 rs3 /\
                         (s |= cp ∈ Left -> j__left' b1 = Some (b3, 0)) /\
                         inject_incr j__left j__left'.
  Proof.
    intros.
    destruct (s cp) eqn:s_cp.
    - exploit alloc_preserves_rel_left1; eauto. now simpl.
      intros [? [? [? [? [? [? [? [? ?]]]]]]]].
      eexists; eexists; eexists; repeat (split; eauto).
    - exploit alloc_preserves_rel_left2; eauto. now simpl.
      intros [? [? [? [? [? [? [? ?]]]]]]].
      eexists; eexists; eexists; repeat (split; eauto). simpl; congruence.
  Qed.

  Lemma free_preserves_rel_left:
    forall cp j__left j__right m1 m1' m2 m3 lo hi b1 b3,
      j__left b1 = Some (b3, 0) -> (* we are necessarily in the Left case *)
      mem_rel s ge1 ge3 j__left Left m1 m3 ->
      mem_rel s ge2 ge3 j__right Right m2 m3 ->
      Mem.free m1 b1 lo hi cp = Some m1' ->
      exists m3', Mem.free m3 b3 lo hi cp = Some m3' /\
               mem_rel s ge1 ge3 j__left Left m1' m3' /\
               mem_rel s ge2 ge3 j__right Right m2 m3'.
  Proof.
    intros cp j__left j__right m1 m1' m2 m3 lo hi b1 b3 ptr_inj m1_m3 m2_m3 free1.
    exploit (Mem.free_parallel_inject j__left m1); eauto using partial_mem_inject.
    intros [m3' [free3 m1'_m3']].
    rewrite 2!Z.add_0_r in free3.
    exists m3'; split; [| split]; [assumption | |].
    { clear dependent j__right.
      constructor.
      - intros b. apply same_dom in m1_m3.
        specialize (m1_m3 b).
        simpl in *. apply Mem.free_result in free1. unfold Mem.unchecked_free in free1.
        destruct (zle hi lo); now subst.
      - assumption.
      - intros b b' delta.
        intros G. exploit delta_zero; eauto.
      - exploit symb_inj; eauto.
      - erewrite Mem.nextblock_free; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - erewrite Mem.nextblock_free; eauto using Ple_trans, Ple_succ, ple_nextblock2.
      - intros. exploit funct_preserved1; eauto.
      - intros. exploit funct_preserved2; eauto.
      - intros. exploit var_info_valid; eauto. eapply Mem.valid_block_free_1; eauto.
      - intros id ofs.
        exploit same_high_half; eauto. }
    { (* clear dependent j__left. *)
      destruct m2_m3.
      constructor; auto.
      - eapply Mem.free_right_inject; eauto.
        intros.
        apply Mem.mi_inj in partial_mem_inject0.
        eapply Mem.mi_own with (cp := (Mem.block_compartment m2 b0)) in partial_mem_inject0; eauto;
          [| now destruct Mem.block_compartment eqn:?]; eauto.
        specialize (same_dom0 b0).
        assert (X: j__right b0 <> None) by congruence.
        apply same_dom0 in X. simpl in *.
        apply same_dom in m1_m3 as G.
        specialize (G b1).
        assert (Y: j__left b1 <> None) by congruence.
        apply G in Y. simpl in *. clear G.
        apply partial_mem_inject in m1_m3.
        apply Mem.mi_inj in m1_m3.
        eapply Mem.mi_own with (cp := (Mem.block_compartment m1 b1)) in m1_m3; eauto;
          [| now destruct (Mem.block_compartment m1 b1) eqn:?]; eauto.
        unfold Mem.can_access_block in *.
        destruct (Mem.block_compartment m2 b0); destruct (Mem.block_compartment m1 b1); try congruence.
      - erewrite Mem.nextblock_free; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - intros. eapply Mem.valid_block_free_1; eauto. }
  (* Qed. *)
  Admitted.

  Lemma store_preserves_rel_left:
    forall cp j__left j__right m1 m1' m2 m3 ch ofs v1 v3 b1 b3,
      j__left b1 = Some (b3, 0) -> (* we are necessarily in the δ case *)
      mem_rel s ge1 ge3 j__left Left m1 m3 ->
      mem_rel s ge2 ge3 j__right Right m2 m3 ->
      Val.inject j__left v1 v3 ->
      Mem.store ch m1 b1 ofs v1 cp = Some m1' ->
      exists m3', Mem.store ch m3 b3 ofs v3 cp = Some m3' /\
               mem_rel s ge1 ge3 j__left Left m1' m3' /\
               mem_rel s ge2 ge3 j__right Right m2 m3'.
  Proof.
    intros cp j__left j__right m1 m1' m2 m3 ch ofs v1 v3 b1 b3 ptr_inj m1_m3 m2_m3 val_inj store1.
    exploit (Mem.store_mapped_inject j__left); eauto using partial_mem_inject.
    intros [m3' [store3 ?]].
    rewrite Z.add_0_r in store3.
    exists m3'; split; [| split]; [assumption | |].
    { clear dependent j__right.
      constructor.
      - intros b. apply same_dom in m1_m3.
        specialize (m1_m3 b). simpl in *.
        eapply Mem.store_block_compartment in store1. now rewrite store1.
      - assumption.
      - now eapply delta_zero; eauto.
      - exploit symb_inj; eauto.
      - erewrite Mem.nextblock_store; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - erewrite Mem.nextblock_store; eauto using Ple_trans, Ple_succ, ple_nextblock2.
      - intros. exploit funct_preserved1; eauto.
      - intros. exploit funct_preserved2; eauto.
      - intros. exploit var_info_valid; eauto. eapply Mem.store_valid_block_1; eauto.
      - intros id ofs0.
        exploit same_high_half; eauto. }
    { destruct m2_m3.
      constructor; eauto.
      (* - Mem.store_outside_inject *)
      - eapply Mem.store_outside_inject; eauto.
        intros.
        apply Mem.mi_inj in partial_mem_inject0.
        eapply Mem.mi_own with (cp := (Mem.block_compartment m2 b')) in partial_mem_inject0; eauto;
          [| now destruct Mem.block_compartment eqn:?]; eauto.
        specialize (same_dom0 b').
        assert (X: j__right b' <> None) by congruence.
        apply same_dom0 in X. simpl in *.
        apply same_dom in m1_m3 as G.
        specialize (G b1).
        assert (Y: j__left b1 <> None) by congruence.
        apply G in Y. simpl in *. clear G.
        apply partial_mem_inject in m1_m3.
        apply Mem.mi_inj in m1_m3.
        eapply Mem.mi_own with (cp := (Mem.block_compartment m1 b1)) in m1_m3; eauto;
          [| now destruct (Mem.block_compartment m1 b1) eqn:?]; eauto.
        unfold Mem.can_access_block in *.
        destruct (Mem.block_compartment m2 b'); destruct (Mem.block_compartment m1 b1); try congruence.
      - erewrite Mem.nextblock_store; eauto using Ple_trans, Ple_succ, ple_nextblock1.
      - intros. exploit var_info_valid; eauto. eapply Mem.store_valid_block_1; eauto. }
  Qed.

  Lemma regset_rel_inject: forall j rs1 rs3 rd v v',
      regset_rel j rs1 rs3 ->
      Val.inject j v v' ->
      regset_rel j (rs1 # rd <- v) (rs3 # rd <- v').
  Proof.
    intros.
    intros r.
    destruct (Pregmap.elt_eq r rd); now try subst r; Simpl.
  Qed.

  Lemma inject_incr_stack_rel1:
    forall δ j1 j1' j2 st st',
      inject_incr j1 j1' ->
      stack_rel s j1 j2 δ st st' ->
      stack_rel s j1' j2 δ st st'.
  Proof.
    intros * incr st_rel.
    induction st_rel.
    - constructor; eauto.
    - constructor; eauto.
      inv H2. constructor; eauto.
    - constructor; eauto.
  Qed.

  Lemma inject_incr_stack_rel2:
    forall δ j1 j2 j2' st st',
      inject_incr j2 j2' ->
      stack_rel s j1 j2 δ st st' ->
      stack_rel s j1 j2' δ st st'.
  Proof.
    intros * incr st_rel.
    induction st_rel.
    - constructor; eauto.
    - constructor; eauto.
    - constructor; eauto.
      inv H2. constructor; eauto.
  Qed.

  Ltac Simplif_all :=
    ((rewrite Asmgenproof0.nextinstr_inv in * by eauto with asmgen)
     || (rewrite Asmgenproof0.nextinstr_inv1 in * by eauto with asmgen)
     || (rewrite Pregmap.gss in *)
     || (rewrite Asmgenproof0.nextinstr_pc in *)
     || (rewrite Pregmap.gso in * by eauto with asmgen)); auto with asmgen.

  Ltac Simpl_all := repeat Simplif_all.

  Ltac eexists_and_split :=
    fun k =>
      match goal with
      | m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
          rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
          exists j; eexists; eexists; split; [| split; [| split; [| split]]]; eauto;
          k j rs1 rs3 rs1_rs3 m1 m3 m1_m3
      end.

  Ltac simpl_before_exists :=
    repeat (Simpl_all;
            match goal with
            (* Goto *)
            | _: goto_label _ _ ?rs _ = Next _ _ |- _ =>
                unfold goto_label in *; destruct label_pos; try congruence
            | _: eval_branch _ _ ?rs _ _ = Next _ _ |- _ =>
                unfold eval_branch in *; simpl in *
            | _: exec_load _ _ _ _ _ _ _ _ _ = Next _ _ |- _ =>
                unfold exec_load in *; simpl in *
            | _: exec_store _ _ _ _ _ _ _ _ = Next _ _ |- _ =>
                unfold exec_store in *; simpl in *
            | _: context [Val.cmp_bool] |- _ =>
                unfold Val.cmp_bool in *; simpl in *
            | _: context [Val.cmpl_bool] |- _ =>
                unfold Val.cmpl_bool in *; simpl in *
            | _: context [eval_offset _ ?ofs] |- _ =>
                destruct ofs eqn:?; subst; simpl in *

            | _: context [low_half] |- _ =>
                unfold low_half in *; simpl in *
                (* rewrite same_low_half1 in * *)


            | H: Mem.alloc ?m1 ?cp ?lo1 ?hi1 = (?m1', ?b1),
              m1_m3: mem_rel _ _ _ ?j__left Left ?m1 ?m3,
              m2_m3: mem_rel _ _ _ ?j__right Right ?m2 ?m3,
              rs1_rs3: regset_rel _ _ _ |- _ =>
                (* idtac "alloc case"; *)
                let j__left' := fresh "j__left" in
                let m3' := fresh "m3" in
                let b3 := fresh "b3" in
                let alloc3 := fresh "alloc3" in
                let m1'_m3' := fresh "m1'_m3'" in
                let m2_m3' := fresh "m2_m3'" in
                let proj := fresh "proj" in
                let incr := fresh "incr" in
                apply (alloc_preserves_rel_left _ _ _ _ _ _ _ _ _ _ _ _ m1_m3 m2_m3 rs1_rs3) in H as
                    [j__left' [m3' [b3 [alloc3 [m1'_m3' [m2_m3' [? [proj incr]]]]]]]];
                (* idtac "done with alloc"; *)
                clear m1_m3 rs1_rs3 m2_m3
            | H: s ?cp = ?δ -> _,
              side_cp: s ?cp = ?δ |- _ =>
                specialize (H side_cp)

            | H: Mem.store ?ch ?m1 ?b1 ?ofs (?rs1 ?r) ?cp = Some ?m1',
              m1_m3: mem_rel _ _ _ ?j__left Left ?m1 ?m3,
              m2_m3: mem_rel _ _ _ ?j__right Right ?m2 ?m3,
              ptr_inj: ?j__left ?b1 = Some (?b3, 0),
              rs1_rs3: regset_rel ?j__left ?rs1 ?rs3 |- _ =>
                (* idtac "store case"; *)
                let m3' := fresh "m3" in
                apply (store_preserves_rel_left _ _ _ _ _ _ _ _ _ _ _ _ _ ptr_inj m1_m3 m2_m3 (rs1_rs3 r)) in H as
                    [m3' [? [? ?]]];
                (* idtac "done with store"; *)
                clear m1_m3 m2_m3

            | H: Mem.free ?m1 ?b1 ?lo ?hi ?cp = Some ?m1',
              m1_m3: mem_rel _ _ _ ?j__left Left ?m1 ?m3,
              m2_m3: mem_rel _ _ _ ?j__right Right ?m2 ?m3,
              ptr_inj: ?j__left ?b1 = Some (?b3, 0) |- _ =>
                (* rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ => *)
                (* idtac "free case"; *)
                let m3' := fresh "m3" in
                apply (free_preserves_rel_left _ _ _ _ _ _ _ _ _ _ _ ptr_inj m1_m3 m2_m3) in H as
                    [m3' [? [? ?]]];
                (* idtac "done with free"; *)
                clear m1_m3

            | H: Mem.load ?ch ?m1 ?b1 ?ofs ?cp = Some ?v1,
                m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                  ptr_inj: ?j ?b1 = Some (?b3, 0) |- _ =>
                idtac "load case";
                let v3 := fresh "v3" in
                let load3 := fresh "load3" in
                destruct (Mem.load_inject _ _ _ _ _ _ _ _ _ _ (partial_mem_inject _ _ _ _ _ _ _ m1_m3) H ptr_inj) as
                  [v3 [load3 ?]];
                rewrite Z.add_0_r in load3;
                idtac "done with load";
                clear H

            | H: Val.cmpu_bool (Mem.valid_pointer ?m1) ?op (?rs1 ?r) (?rs1 ?r') = Some ?b,
                m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
                (* idtac "Val.cmpu_bool case 0"; *)
                eapply cmpu_bool_preserved with (m3 := m3) in H; eauto using rs1_rs3;
                try rewrite H in *;
                (* idtac "done with Val.cmpu_bool 0"; *)
                try congruence

            | H: Val.cmpu_bool (Mem.valid_pointer ?m1) ?op (Vint ?x) (?rs1 ?r') = Some ?b,
                m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
                (* idtac "Val.cmpu_bool case 1"; *)
                eapply cmpu_bool_preserved with (m3 := m3) (v1' := Vint x) in H; eauto using rs1_rs3;
                try rewrite H in *;
                (* idtac "done with Val.cmpu_bool 1"; *)
                try congruence

            | H: Val.cmpu_bool (Mem.valid_pointer ?m1) ?op (?rs1 ?r) (Vint ?x) = Some ?b,
                m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
                (* idtac "Val.cmpu_bool case 2"; *)
                eapply cmpu_bool_preserved with (m3 := m3) (v2' := Vint x) in H; eauto using rs1_rs3;
                try rewrite H in *;
                (* idtac "done with Val.cmpu_bool 2"; *)
                try congruence

            | H: Val.cmpu_bool (Mem.valid_pointer ?m1) ?op (Vint ?x) (Vint ?y) = Some ?b,
                m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
                (* idtac "Val.cmpu_bool case 3"; *)
                eapply cmpu_bool_preserved with (m3 := m3) (v1' := Vint x) (v2' := Vint y) in H; eauto using rs1_rs3;
                try rewrite H in *;
                (* idtac "done with Val.cmpu_bool 3"; *)
                try congruence

            | H: Val.cmplu_bool (Mem.valid_pointer ?m1) ?op (?rs1 ?r) (?rs1 ?r') = Some ?b,
                m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
                (* idtac "Val.cmplu_bool case 0"; *)
                eapply cmplu_bool_preserved with (m3 := m3) in H; eauto using rs1_rs3;
                try rewrite H in *;
                (* idtac "done with Val.cmplu_bool 0"; *)
                try congruence

            | H: Val.cmplu_bool (Mem.valid_pointer ?m1) ?op (Vlong ?x) (?rs1 ?r') = Some ?b,
                m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
                (* idtac "Val.cmplu_bool case 1"; *)
                eapply cmplu_bool_preserved with (m3 := m3) (v1' := Vlong x) in H; eauto using rs1_rs3;
                try rewrite H in *;
                (* idtac "done with Val.cmplu_bool 1"; *)
                try congruence

            | H: Val.cmplu_bool (Mem.valid_pointer ?m1) ?op (?rs1 ?r) (Vlong ?x) = Some ?b,
                m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
                (* idtac "Val.cmplu_bool case 2"; *)
                eapply cmplu_bool_preserved with (m3 := m3) (v2' := Vlong x) in H; eauto using rs1_rs3;
                try rewrite H in *;
                (* idtac "done with Val.cmplu_bool 2"; *)
                try congruence

            | H: Val.cmplu_bool (Mem.valid_pointer ?m1) ?op (Vlong ?x) (Vlong ?y) = Some ?b,
                m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
                (* idtac "Val.cmplu_bool case 3"; *)
                eapply cmplu_bool_preserved with (m3 := m3) (v1' := Vlong x) (v2' := Vlong y) in H; eauto using rs1_rs3;
                try rewrite H in *;
                (* idtac "done with Val.cmplu_bool 3"; *)
                try congruence

            | H: Val.cmp_bool ?op (?rs1 ?r) (?rs1 ?r') = Some ?b,
                m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3,
                rs1_rs3: regset_rel ?j ?rs1 ?rs3 |- _ =>
                (* idtac "Val.cmp_bool case"; *)
                eapply Val.cmp_bool_inject in H; eauto using rs1_rs3;
                try rewrite H in *;
                (* idtac "done with Val.cmp_bool"; *)
                try congruence

            | d: Z |- _ =>
                match goal with
                | H: ?j _ = Some (_, d) ,
                    m1_m3: mem_rel _ _ _ ?j _ ?m1 ?m3 |- _ =>
                    let G := fresh "G" in
                    pose proof (delta_zero _ _ _ _ _ _ _ m1_m3 _ _ _ H) as G;
                    subst d
                end


            | |- context [Ptrofs.repr 0] => replace (Ptrofs.repr 0) with Ptrofs.zero by reflexivity; auto
            | H: context [Ptrofs.repr 0] |- _ => replace (Ptrofs.repr 0) with Ptrofs.zero in H by reflexivity; auto
            | |- context [Ptrofs.add _ Ptrofs.zero] => rewrite Ptrofs.add_zero; auto
            | H: context [Ptrofs.add _ Ptrofs.zero] |- _ => rewrite Ptrofs.add_zero in H; simpl in *; try congruence
            | |- context [Ptrofs.sub _ Ptrofs.zero] => rewrite Ptrofs.sub_zero_l; auto
            | H: context [Ptrofs.sub _ Ptrofs.zero] |- _ => rewrite Ptrofs.sub_zero_l in H; simpl in *; try congruence

            (* hypothesis manipulation *)
            | rs1_rs3: regset_rel ?j ?rs1 ?rs3,
              _: context [match ?rs1 ?i with | _ => _ end] |- _ =>
                let H := fresh "rs1_rs3" in
                assert (H := rs1_rs3 i);
                destruct (rs1 i); inv H; try congruence; simpl in *; eauto

            | rs1_rs3: regset_rel ?j ?rs1 ?rs3,
              _: context [Val.offset_ptr (?rs1 ?i) _] |- _ =>
                let H := fresh "rs1_rs3" in
                assert (H := rs1_rs3 i);
                destruct (rs1 i); inv H; try congruence; simpl in *; eauto

            | H: Next _ _ = Next _ _ |- _ => inv H
            | H: Some _ = Some _ |- _ => inv H
            | H: Some _ = None |- _ => inv H
            | H: None = Some _ |- _ => inv H
            | H: Stuck = Next _ _ |- _ => inv H
            | H: Next _ _ = Stuck |- _ => inv H
            | H: negb _ = true |- _ => apply negb_true_iff in H
            | H: negb _ = false |- _ => apply negb_false_iff in H
            | H: Int.eq ?x ?x = false |- _ => rewrite Int.eq_true in H
            | H: Int64.eq ?x ?x = false |- _ => rewrite Int64.eq_true in H
            | H: Int.lt ?x ?x = true |- _ => rewrite lt_xx_false in H
            | H: Int64.lt ?x ?x = true |- _ => rewrite lt64_xx_false in H
            | H: Int.ltu ?x ?x = true |- _ => rewrite ltu_xx_false in H
            | H: Int64.ltu ?x ?x = true |- _ => rewrite ltu64_xx_false in H
            | H: false = true |- _ => congruence
            | H: true = false |- _ => congruence
            | H: ?x = false, H': ?x = true |- _ => congruence
            | H: match ?x with | _ => _ end = Next _ _ |- _ =>
                let eq := fresh "eq" in
                destruct x eqn:eq; simpl in *; try congruence
            | _: context [?rs1 ### ?rs] |- context [?rs3 ### ?rs] =>
                let i := fresh "i" in destruct rs as [| i]; simpl in *
            | _: context [?rs1 ## ?rs] |- context [?rs3 ## ?rs] =>
                let i := fresh "i" in destruct rs as [| i]; simpl in *
            | H: ?x = _ |- context [if ?x then _ else _] =>
                setoid_rewrite H; simpl
            | H: ?x = _ |- context [match ?x with | _ => _ end] =>
                setoid_rewrite H; simpl
            | |- context [(if ?x then _ else _) = Next _ _] =>
                let eq := fresh "eq" in destruct x eqn:eq; simpl in *
            | |- context [(match ?x with | _ => _ end) = Next _ _] =>
                let eq := fresh "eq" in destruct x eqn:eq; simpl in *

            end);
    simpl.

  Ltac solve_simple_regset_rel j rs1 rs3 rs1_rs3 m1 m3 m1_m3:=
    repeat (Simpl;
            match goal with
            | |- regset_rel j (nextinstr _) (nextinstr _) => unfold nextinstr
            | |- regset_rel j (_ # _ <- _) (_ # _ <- _) => eapply regset_rel_inject
            | |- regset_rel j rs1 rs3 => assumption

            | |- stack_rel _ _ _ _ _ _ => eauto using inject_incr_stack_rel1, inject_incr_stack_rel2, inject_incr_refl

            | _: ?x |- ?x => assumption

            | d: Z |- _ =>
                match goal with
                | H: j _ = Some (_, d) |- _ =>
                    let G := fresh "G" in
                    pose proof (delta_zero _ _ _ _ _ _ _ m1_m3 _ _ _ H) as G;
                    subst d
                end


            | |- Ptrofs.add (Ptrofs.add ?ofs1 ?delta) ?imm = Ptrofs.add (Ptrofs.add ?ofs1 ?imm) ?delta =>
                now rewrite (Ptrofs.add_assoc ofs1 delta imm), (Ptrofs.add_commut delta imm), <- Ptrofs.add_assoc

            | |- context [_ ### ?rs] =>
                let i := fresh "i" in destruct rs as [| i]; simpl in *
            | |- context [_ ## ?rs] =>
                let i := fresh "i" in destruct rs as [| i]; simpl in *
            (* | |- context [rs1 # ?i] => *)
            (*     match goal with *)
            (*     | |- context [rs3 # ?i] => *)
            (*         let H := fresh "rs1_rs3" in *)
            (*         assert (H := rs1_rs3 i); inv H; simpl; eauto *)
            (*     end *)


            | |- context [Ptrofs.sub (Ptrofs.add _ _) _] => rewrite Ptrofs.sub_add_l; simpl; auto
            | |- context [Ptrofs.repr 0] => replace (Ptrofs.repr 0) with Ptrofs.zero by reflexivity; auto
            | |- context [Ptrofs.add _ Ptrofs.zero] => rewrite Ptrofs.add_zero; auto
            | |- context [Ptrofs.sub _ Ptrofs.zero] => rewrite Ptrofs.sub_zero_l; auto



            | |- Val.inject _ _ _ => eauto using Ptrofs.add_zero with solve_inject
            end).

  (* Lemma exec_instr_preserved: *)
  (*   forall δ j f i rs1 rs1' rs3 m1 m1' m3 st1 st3, *)
  (*     s |= has_comp_function f ∈ δ -> *)
  (*     mem_rel s ge1 ge3 j δ m1 m3 -> *)
  (*     regset_rel j rs1 rs3 -> *)
  (*     stack_rel s j δ st1 st3 -> *)
  (*     exec_instr ge1 f i rs1 m1 (has_comp_function f) = Next rs1' m1' -> *)
  (*     exists j' rs3' m3', *)
  (*       exec_instr ge3 f i rs3 m3 (has_comp_function f) = Next rs3' m3' /\ *)
  (*         mem_rel s ge1 ge3 j' δ m1' m3' /\ *)
  (*         regset_rel j' rs1' rs3' /\ *)
  (*         stack_rel s j' δ st1 st3. *)

  Lemma exec_instr_preserved_left:
    forall j__left j__right f i rs1 rs1' rs3 m1 m1' m2 m3 st1 st2 st3,
      s |= has_comp_function f ∈ Left ->
      mem_rel s ge1 ge3 j__left Left m1 m3 ->
      mem_rel s ge2 ge3 j__right Right m2 m3 ->
      regset_rel j__left rs1 rs3 ->
      stack_rel s j__left j__right st1 st2 st3 ->
      (* stack_rel s j δ st1 st3 -> *)
      exec_instr ge1 f i rs1 m1 (has_comp_function f) = Next rs1' m1' ->
      exists j__left' rs3' m3',
        exec_instr ge3 f i rs3 m3 (has_comp_function f) = Next rs3' m3' /\
          mem_rel s ge1 ge3 j__left' Left m1' m3' /\
          mem_rel s ge2 ge3 j__right Right m2 m3' /\
          regset_rel j__left' rs1' rs3' /\
          stack_rel s j__left' j__right st1 st2 st3.
  Proof.
    intros until st3.
    intros side_cp m1_m3 m2_m3 rs1_rs3 st1_st3 exec.

    Local Opaque Val.cmpu_bool Val.cmplu_bool.
    (* Local Opaque low_half high_half. *)

    destruct i; inv exec; simpl in *;
      try now (simpl_before_exists; (eexists_and_split
                  ltac:(fun j rs1 rs3 rs1_rs3 m1 m3 m1_m3 =>
                          (simpl; try reflexivity; try eassumption;
                           solve_simple_regset_rel j rs1 rs3 rs1_rs3 m1 m3 m1_m3; try reflexivity)))).
    - (eexists_and_split
         ltac:(fun j rs1 rs3 rs1_rs3 m1 m3 m1_m3 =>
                 (simpl; try reflexivity; try eassumption;
                  solve_simple_regset_rel j rs1 rs3 rs1_rs3 m1 m3 m1_m3; try reflexivity))).
      (* apply Genv.find_symbol_match with (s := symb) in match_W1_W3. *)
      exploit symb_inj. exact m1_m3. intros (A & B & C & D).
      unfold Genv.symbol_address. admit.
    - (eexists_and_split
         ltac:(fun j rs1 rs3 rs1_rs3 m1 m3 m1_m3 =>
                 (simpl; try reflexivity; try eassumption;
                  solve_simple_regset_rel j rs1 rs3 rs1_rs3 m1 m3 m1_m3; try reflexivity))).
      (* apply Genv.find_symbol_match with (s := symb) in match_W1_W3. *)
      admit.
      (* unfold Genv.symbol_address. rewrite match_W1_W3. *)
      (* now eapply symbol_address_inject; eauto using pres_globals. *)
    - (eexists_and_split
         ltac:(fun j rs1 rs3 rs1_rs3 m1 m3 m1_m3 =>
                 (simpl; try reflexivity; try eassumption;
                  solve_simple_regset_rel j rs1 rs3 rs1_rs3 m1 m3 m1_m3; try reflexivity))).
      apply Genv.find_symbol_match with (s := id) in match_W1_W3.
      admit.
      (* unfold Genv.symbol_address. rewrite match_W1_W3. *)
      (* now eapply symbol_address_inject; eauto using pres_globals. *)
    - (eexists_and_split
         ltac:(fun j rs1 rs3 rs1_rs3 m1 m3 m1_m3 =>
                 (simpl; try reflexivity; try eassumption;
                  solve_simple_regset_rel j rs1 rs3 rs1_rs3 m1 m3 m1_m3; try reflexivity))).
      eapply same_high_half; eauto.
  Admitted.

  Lemma store_inj_outside_domain:
    forall f chunk m1 b1 ofs v1 cp n2 m2,
      Mem.mem_inj f m1 m2 ->
      Mem.store chunk m2 b1 ofs v1 cp = Some n2 ->
      (forall b0 delta, f b0 = Some (b1, delta) -> False) ->
      Mem.mem_inj f m1 n2.
  Proof.
    intros. constructor.
    (* perm *)
    intros. eapply Mem.mi_perm in H; eauto. eapply Mem.perm_store_1; eauto.
    (* own *)
    intros. eapply Mem.mi_own in H; eauto.
    (* RB: NOTE: Should be solvable by properly extended hint databases. *)
    apply (proj1 (Mem.store_can_access_block_inj _ _ _ _ _ _ _ H0 _ _)).
    assumption.
    (* align *)
    intros. eapply Mem.mi_align with (ofs := ofs0) (p := p) in H; eauto.
    (* mem_contents *)
    intros.
    (* Local Transparent Mem.store. *)
    (* unfold Mem.store in H0. *)
    (* destruct Mem.valid_access_dec; try congruence. *)
    (* inv H0. simpl. *)
    eapply Mem.mi_memval in H; eauto.
    rewrite (Mem.store_mem_contents _ _ _ _ _ _ _ H0).
    rewrite PMap.gso. eauto with mem.
    intros ?. subst. now eapply H1; eauto.
  Qed.


  Theorem store_inject_outside_domain:
    forall f chunk m1 b1 ofs v1 cp n2 m2,
      Mem.inject f m1 m2 ->
      Mem.store chunk m2 b1 ofs v1 cp = Some n2 ->
      (forall b0 delta, f b0 = Some (b1, delta) -> False) ->
      Mem.inject f m1 n2.
  Proof.
    intros. inversion H.
    constructor.
    (* inj *)
    eapply store_inj_outside_domain; eauto.
    (* freeblocks *)
    eauto with mem.
    (* mappedblocks *)
    eauto with mem.
    (* no overlap *)
    red; intros. eauto with mem.
    (* representable *)
    intros. eapply mi_representable; try eassumption.
    (* destruct H3; eauto with mem. *)
    (* perm inv *)
    intros. exploit mi_perm_inv; eauto using Mem.perm_store_2.
  Qed.

  (* Lemma exec_instr_preserved': *)
  (*   forall δ j f i rs3 rs3' m1 m3 m3' st1 st3, *)
  (*     s |= has_comp_function f ∈ opposite δ -> *)
  (*     mem_rel s ge2 ge3 j δ m1 m3 -> *)
  (*     stack_rel s j δ st1 st3 -> *)
  (*     exec_instr ge3 f i rs3 m3 (has_comp_function f) = Next rs3' m3' -> *)
  (*     mem_rel s ge2 ge3 j δ m1 m3' /\ *)
  (*       stack_rel s j δ st1 st3. *)
  (* Proof. *)
  (*   intros until st3. *)
  (*   intros side_cp m1_m3 st1_st3 exec. *)

  (*   assert ( forall chunk addr v, *)
  (*       s |= has_comp_function f ∈ opposite δ -> *)
  (*       mem_rel s ge2 ge3 j δ m1 m3 -> *)
  (*       Mem.storev chunk m3 addr v (has_comp_function f) = Some m3' -> *)
  (*       mem_rel s ge2 ge3 j δ m1 m3' *)
  (*          ). *)
  (*   { clear. *)
  (*     intros chunk addr v side_cp m1_m3 store. *)
  (*     destruct m1_m3. *)
  (*     constructor; auto. *)
  (*     - destruct addr; simpl in store; try congruence. *)
  (*       eapply store_inject_outside_domain; eauto. *)
  (*       intros. *)
  (*       specialize (same_dom0 b0) as [G _]. *)
  (*       assert (N: j b0 <> None) by now congruence. *)
  (*       specialize (G N). simpl in *. *)
  (*       apply Mem.store_can_access_block_1 in store. simpl in store. *)
  (*       destruct (Mem.block_compartment m1 b0) as [c' |] eqn:eq; try congruence. *)
  (*       assert (Mem.can_access_block m1 b0 (Some c')) by auto. *)
  (*       exploit Mem.mi_own; eauto using Mem.mi_inj. *)
  (*       intros ?. simpl in H1. subst. rewrite H1 in store; inv store. *)
  (*       now destruct (s (has_comp_function f)). *)
  (*     - destruct addr; simpl in store; try congruence. *)
  (*       erewrite Mem.nextblock_store; eauto. *)
  (*     - intros. *)
  (*       destruct addr; simpl in store; try congruence. *)
  (*       eapply Mem.store_valid_block_1; eauto. } *)
  (*   destruct i; inv exec; simpl in *; split; auto; *)
  (*     simpl_before_exists; *)
  (*     simpl in *; try now eapply H; eauto. *)
  (*   admit. *)
  (*   admit. *)
  (* Admitted. *)


  Lemma strong_equiv_state_inv_left:
    forall j__left st1 rs1 m1 s3 b ofs f i,
      strong_equivalence s ge1 ge3 j__left Left (State st1 rs1 m1) s3 ->
      rs1 PC = Vptr b ofs ->
      Genv.find_funct_ptr ge1 b = Some (Internal f) ->
      find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
      exists st3 rs3 m3,
        s3 = State st3 rs3 m3 /\
          rs3 PC = Vptr b ofs /\
          Genv.find_funct_ptr ge3 b = Some (Internal f) /\
          mem_rel s ge1 ge3 j__left Left m1 m3 /\
          regset_rel j__left rs1 rs3 /\
          s (has_comp_function f) = Left.
  Proof.
    intros * equiv eq_pc find_fun find_ins.
    inv equiv.
    eexists; eexists; eexists; split; eauto.
    exploit (Genv.find_funct_ptr_match match_W1_W3); eauto.
    intros [[] [f' [find_f' [match_f_f' _]]]].
    inv match_f_f'; simpl in *.
    - rewrite eq_pc in *; simpl in *.
      (* destruct Ptrofs.eq_dec; try congruence. unfold ge1 in *. rewrite find_fun in H2. *)
      (* simpl in *; congruence. *)
      admit.
    - pose proof (H4 PC) as inj.
      rewrite eq_pc in *; simpl in *. inv inj.
      exploit funct_preserved1; eauto. intros.
      assert (b2 = b) by congruence; assert (delta = 0) by congruence; subst b2 delta.

      apply Genv.globalenvs_match in match_W1_W3.
      apply Genv.mge_defs with (b := b) in match_W1_W3.
      inv match_W1_W3.
      + unfold Genv.find_funct_ptr in *. unfold Genv.find_def in *. rewrite <- H7 in *. congruence.
      + unfold Genv.find_funct_ptr in *. unfold Genv.find_def in *. rewrite <- H7 in *. rewrite <- H1 in *.
        inv H8; inv find_fun.
        inv H10; repeat (split; eauto).
        * now rewrite Ptrofs.add_zero.
        * now rewrite Ptrofs.add_zero.
  (* Qed. *)
  Admitted.

  Lemma find_comp_preserved:
    forall j rs rs' r
      (funct_preserved1: forall (b : block) (fd : fundef), Genv.find_funct_ptr ge1 b = Some fd -> j b = Some (b, 0))
      (funct_preserved2: forall (b1 b2 : block) (fd : fundef), Genv.find_funct_ptr ge3 b2 = Some fd -> j b1 = Some (b2, 0) -> b1 = b2)
      (delta_zero: Mem.delta_zero j),
      rs r <> Vundef ->
      regset_rel j rs rs' ->
      Genv.find_comp ge1 (rs r) =
        Genv.find_comp ge3 (rs' r).
  Proof.
    intros j rs rs' r funct_preserved1 funct_preserved2 delta_zero nundef H.
    specialize (H r).
    inv H; simpl; auto; try congruence.
(*
    destruct Ptrofs.eq_dec; auto.
    { destruct (Genv.find_funct_ptr ge1 b1) eqn:find_funct;
        destruct (Genv.find_funct_ptr ge3 b2) eqn:find_funct';
        auto.
      - exploit funct_preserved1; eauto; intros.
        assert (b1 = b2) by congruence; assert (delta = 0) by congruence; subst b2 delta.
        eapply Genv.find_funct_ptr_match in match_W1_W3 as [? [f' [? [match_fd ?]]]]; eauto.
        assert (f0 = f') by congruence; subst f0.
        now inv match_fd.
      - exploit funct_preserved1; eauto; intros.
        assert (b1 = b2) by congruence; assert (delta = 0) by congruence; subst b2 delta.
        eapply Genv.find_funct_ptr_match in match_W1_W3 as [? [f' [? [match_fd ?]]]]; eauto.
        congruence.
      - exploit delta_zero; eauto; intros ->.
        exploit funct_preserved2; eauto; intros <-.
        eapply Genv.find_funct_ptr_match_conv in match_W1_W3 as [? [f' [? [match_fd ?]]]]; eauto.
        congruence.
      - exploit delta_zero; eauto; intros ->.
        rewrite Ptrofs.add_zero.
        destruct Ptrofs.eq_dec; auto. }
    { destruct Ptrofs.eq_dec; auto.
      exploit delta_zero; eauto; intros ->.
      rewrite Ptrofs.add_zero in *; congruence. }
  Qed.
*)
  Admitted.

(*
  Lemma find_comp_ignore_offset_preserved:
    forall j rs rs' r
      (funct_preserved1: forall (b : block) (fd : fundef), Genv.find_funct_ptr ge1 b = Some fd -> j b = Some (b, 0))
      (funct_preserved2: forall (b1 b2 : block) (fd : fundef), Genv.find_funct_ptr ge3 b2 = Some fd -> j b1 = Some (b2, 0) -> b1 = b2)
      (delta_zero: Mem.delta_zero j),
      rs r <> Vundef ->
      regset_rel j rs rs' ->
      Genv.find_comp_ignore_offset ge1 (rs r) =
        Genv.find_comp_ignore_offset ge3 (rs' r).
  Proof.
    intros j rs rs' r funct_preserved1 funct_preserved2 delta_zero nundef H.
    specialize (H r).
    inv H; simpl; auto; try congruence.
    destruct Ptrofs.eq_dec; auto.
    destruct (Genv.find_funct_ptr ge1 b1) eqn:find_funct;
      destruct (Genv.find_funct_ptr ge3 b2) eqn:find_funct';
      auto.
    - exploit funct_preserved1; eauto; intros.
      assert (b1 = b2) by congruence; assert (delta = 0) by congruence; subst b2 delta.
      eapply Genv.find_funct_ptr_match in match_W1_W3 as [? [f' [? [match_fd ?]]]]; eauto.
      assert (f0 = f') by congruence; subst f0.
      now inv match_fd.
    - exploit funct_preserved1; eauto; intros.
      assert (b1 = b2) by congruence; assert (delta = 0) by congruence; subst b2 delta.
      eapply Genv.find_funct_ptr_match in match_W1_W3 as [? [f' [? [match_fd ?]]]]; eauto.
      congruence.
    - exploit delta_zero; eauto; intros ->.
      exploit funct_preserved2; eauto; intros <-.
      eapply Genv.find_funct_ptr_match_conv in match_W1_W3 as [? [f' [? [match_fd ?]]]]; eauto.
      congruence.
  Qed.
*)

  Lemma allowed_call_preserved:
    forall j cp v v'
      (funct_preserved1: forall (b : block) (fd : fundef), Genv.find_funct_ptr ge1 b = Some fd -> j b = Some (b, 0))
      (funct_preserved2: forall (b1 b2 : block) (fd : fundef), Genv.find_funct_ptr ge3 b2 = Some fd -> j b1 = Some (b2, 0) -> b1 = b2)
      (delta_zero: Mem.delta_zero j),
      v <> Vundef ->
      Val.inject j v v' ->
      Genv.allowed_call ge1 cp v ->
      Genv.allowed_call ge3 cp v'.
  Proof.
    intros * funct_preserved1 funct_preserved2 delta_zero nundef H allowed.
    inv H; auto; try congruence.
    (* unfold Genv.allowed_call, Genv.find_comp in allowed. *)
    destruct (Genv.find_funct ge1 (Vptr b1 ofs1)) eqn:find_v.
    - simpl in find_v; destruct Ptrofs.eq_dec; try congruence; subst.
      (* exploit delta_zero; eauto; intros ?; subst delta0. *)
      exploit funct_preserved1; eauto. intros ?.
      assert (b1 = b2) by congruence. assert (delta = 0) by congruence. subst b2 delta.
      rewrite Ptrofs.add_zero.
      eapply Genv.match_genvs_allowed_calls in match_W1_W3; eauto using has_comp_match_fundef.
    - destruct (Genv.find_funct ge3 (Vptr b2 (Ptrofs.add ofs1 (Ptrofs.repr delta)))) eqn:find_v'.
      + exploit delta_zero; eauto. intros ->. rewrite Ptrofs.add_zero in *.
        simpl in find_v'. destruct Ptrofs.eq_dec; try congruence; subst.
        exploit funct_preserved2; eauto. intros <-.
        eapply Genv.find_funct_match_conv with (v := Vptr b1 Ptrofs.zero) in match_W1_W3; eauto.
        destruct match_W1_W3 as [? [? [? [? ?]]]]; congruence.
      + destruct allowed.
(*
        * left; subst; auto. simpl in *; now rewrite find_v, find_v'.
        * right. simpl in *. rewrite find_v, find_v' in *.
          admit.
*)
  Admitted.

  Lemma update_stack_call_preserved_left:
    forall j__left j__right rs1 rs3 st1 st1' st2 st3 cp sig
      (funct_preserved1: forall (b : block) (fd : fundef), Genv.find_funct_ptr ge1 b = Some fd -> j__left b = Some (b, 0))
      (funct_preserved2: forall (b1 b2 : block) (fd : fundef), Genv.find_funct_ptr ge3 b2 = Some fd -> j__left b1 = Some (b2, 0) -> b1 = b2)
      (delta_zero: Mem.delta_zero j__left)
      (left_side: (s, ge3) |= rs3 ∈ Left),
      (rs1 PC <> Vundef) ->
      regset_rel j__left rs1 rs3 ->
      stack_rel s j__left j__right st1 st2 st3 ->
      update_stack_call ge1 st1 sig cp rs1 = Some st1' ->
      exists st3',
        update_stack_call ge3 st3 sig cp rs3 = Some st3' /\
          stack_rel s j__left j__right st1' st2 st3'.
  Proof.
    intros * funct_preserved1 funct_preserved2 delta_zero left_side nundef rs1_rs3 st_rel.
    unfold update_stack_call.
(*
    erewrite find_comp_ignore_offset_preserved; eauto.
    destruct ((cp =? Genv.find_comp_ignore_offset ge3 (rs3 PC))%positive); auto.
    - intros R; inv R.
      eexists; split; auto.
    - pose proof (rs1_rs3 X1) as I.
      inv I; try congruence.
      intros R; inv R.
      eexists; split; auto.
      + eapply stack_rel_cons_left with (st2' := nil); simpl; eauto.
        constructor; auto. econstructor; eauto.
  Qed.
*)
  Admitted.

  Lemma call_arguments_preserved:
    forall j δ m1 m3 rs1 rs3,
      mem_rel s ge1 ge3 j δ m1 m3 ->
      regset_rel j rs1 rs3 ->
      forall sig args, call_arguments rs1 m1 sig args ->
                  exists args', Val.inject_list j args args'
                           /\ call_arguments rs3 m3 sig args'.
  Proof.
    intros * m1_m3 rs1_rs3 sig args H.
    unfold call_arguments in H.
    unfold call_arguments.
    induction H.
    - exists nil. split; auto. constructor.
    - assert (exists b1', Val.inject j b1 b1' /\ call_arg_pair rs3 m3 a1 b1').
      { inv H.
        - inv H1.
          + specialize (rs1_rs3 (preg_of r)).
            exists (rs3 (preg_of r)). split; eauto. constructor; constructor.
          + exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject. eapply rs1_rs3.
            intros [b1' [? ?]].
            exists b1'; split. eauto. constructor. econstructor; eauto.
        - inv H1; inv H2.
          + pose proof (rs1_rs3 (preg_of r)).
            pose proof (rs1_rs3 (preg_of r0)).
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; constructor; eauto.
          + pose proof (rs1_rs3 (preg_of r)).
            exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject. eapply rs1_rs3.
            intros [b1' [? ?]].
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; econstructor; eauto.
          + pose proof (rs1_rs3 (preg_of r)).
            exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject. eapply rs1_rs3.
            intros [b1' [? ?]].
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; econstructor; eauto.
          + exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject. eapply rs1_rs3. clear H1.
            exploit Mem.loadv_inject; eauto using partial_mem_inject.
            eapply Val.offset_ptr_inject. eapply rs1_rs3.
            intros [b1' [? ?]].
            intros [b0' [? ?]].
            eexists; split; [eapply Val.longofwords_inject; eauto |].
            constructor; econstructor; eauto. }
      destruct IHlist_forall2 as [? [? ?]].
      destruct H1 as [? [? ?]].
      eexists (cons _ _); split.
      + constructor; eassumption.
      + constructor; eauto.
  Qed.

  Notation comp_of1 := (@comp_of _ (has_comp_state W1)).
  Notation comp_of2 := (@comp_of _ (has_comp_state W2)).
  Notation comp_of3 := (@comp_of _ (has_comp_state W3)).

  Definition stack_of_state (s: state) :=
    match s with
    | State st _ _ | ReturnState st _ _ _ => st
    end.

  Lemma step_E0_strong_Left: forall (s1 s1': state),
      Step (semantics W1) s1 E0 s1' ->
      (s (comp_of1 s1) = s (comp_of1 s1')) ->
      forall (s2 s3: state) j__left j__right,
        stack_rel s j__left j__right (stack_of_state s1) (stack_of_state s2) (stack_of_state s3) ->
        strong_equivalence s ge1 ge3 j__left Left s1 s3 ->
        weak_equivalence s ge2 ge3 j__right Right s2 s3 ->
        exists (s3': state) j__left' j__right',
          Plus (semantics W3) s3 E0 s3' /\
            stack_rel s j__left' j__right' (stack_of_state s1') (stack_of_state s2) (stack_of_state s3') /\
            strong_equivalence s ge1 ge3 j__left' Left s1' s3' /\
            weak_equivalence s ge2 ge3 j__right' Right s2 s3'.
  Proof.
    simpl.
    intros s1 s1' H same_side s2 s3 j__left j__right st_rel strong_s1_s3 weak_s2_s3; inv H.
    - exploit strong_equiv_state_inv_left; eauto.
      intros (st3 & rs3 & m3 & ? & eq_pc' & find_funct & m1_m3 & rs1_rs3 & side_f); subst.
      inv weak_s2_s3.
      exploit exec_instr_preserved_left; simpl; eauto.
      intros (j__left' & rs3' & m3' & exec_instr' & m1_m3' & m2_m3' & rs1_rs3' & st_rel').
(*
      assert (pc_comp: Genv.find_comp_ignore_offset ge1 (rs' PC) = Genv.find_comp_ignore_offset ge3 (rs3' PC)).
      { pose proof (rs1_rs3' PC) as inj_pc; rewrite NEXTPC in *; inv inj_pc.
        assert (delta = 0) by now eapply delta_zero with (j := j__left'); eauto. subst delta.
        rewrite Ptrofs.add_zero.
        simpl. destruct Ptrofs.eq_dec; try congruence.
        destruct (Genv.find_funct_ptr ge1 b') eqn:A.
        - exploit (Genv.find_funct_ptr_match match_W1_W3); eauto.
          intros [[] [f' [find_f' [match_f_f' _]]]].
          exploit (funct_preserved1 s ge1 ge3); eauto. intros.
          assert (b2 = b') by congruence; subst. rewrite find_f'.
          now inv match_f_f'.
        - destruct (Genv.find_funct_ptr ge3 b2) eqn:B; [| reflexivity].
          exploit (funct_preserved2 s ge1 ge3); eauto. intros; subst.
          (* Find a contradiction *)
          apply Genv.find_funct_ptr_iff in B.
          apply Genv.find_def_match_2 with (b := b2) in match_W1_W3.
          inv match_W1_W3; try congruence.
          inv H11; try congruence.
          symmetry in H. apply <- Genv.find_funct_ptr_iff in H. congruence.
      }
      exists (State st3 rs3' m3'), j__left', j__right; split; [| split; [| split]].
      + econstructor; [| now eapply star_refl | now traceEq].
        (* unfold ge3 in exec_instr'. *)
        pose proof (rs1_rs3' PC) as inj_pc; rewrite NEXTPC in *; inv inj_pc. rewrite <- H7 in *.
        econstructor; eauto.
        * rewrite <- ALLOWED; eauto.
      + eauto.
      + econstructor; eauto.
        * simpl; rewrite NEXTPC; simpl in *; rewrite <- ALLOWED. auto.
        (* * simpl. rewrite <- pc_comp. rewrite NEXTPC; simpl in *; rewrite <- ALLOWED. auto. *)
      + econstructor; eauto.

    - exploit strong_equiv_state_inv_left; eauto.
      intros (st3 & rs3 & m3 & ? & eq_pc' & find_funct & m1_m3 & rs1_rs3 & side_f); subst.
      simpl in H3. destruct Ptrofs.eq_dec; try congruence. simpl in H1; rewrite H1 in H3.
      inv weak_s2_s3.
      exploit exec_instr_preserved_left; simpl; eauto.
      intros (j__left' & rs3' & m3' & exec_instr' & m1_m3' & m2_m3' & rs1_rs3' & st_rel').
      assert (pc_comp: Genv.find_comp_ignore_offset ge1 (rs' PC) = Genv.find_comp_ignore_offset ge3 (rs3' PC)).
      { pose proof (rs1_rs3' PC) as inj_pc; rewrite NEXTPC in *; inv inj_pc.
        assert (delta = 0) by now eapply (delta_zero s ge1 ge3); eauto. subst delta.
        rewrite Ptrofs.add_zero.
        simpl. destruct Ptrofs.eq_dec; try congruence.
        destruct (Genv.find_funct_ptr ge1 b') eqn:A.
        - exploit (Genv.find_funct_ptr_match match_W1_W3); eauto.
          intros [[] [f' [find_f' [match_f_f' _]]]].
          exploit (funct_preserved1 s ge1 ge3); eauto. intros.
          assert (b2 = b') by congruence; subst. rewrite find_f'.
          now inv match_f_f'.
        - destruct (Genv.find_funct_ptr (Genv.globalenv W3) b2) eqn:B; [| reflexivity].
          exploit (funct_preserved2 s ge1 ge3); eauto. intros; subst.
          (* Find a contradiction *)
          apply Genv.find_funct_ptr_iff in B.
          apply Genv.find_def_match_2 with (b := b2) in match_W1_W3.
          inv match_W1_W3; try congruence. inv H10; try congruence.
          symmetry in H. apply <- Genv.find_funct_ptr_iff in H. congruence.
      }

      assert (is_left: s (Genv.find_comp_ignore_offset ge3 (rs3' PC)) = Left).
      { simpl in same_side. rewrite <- pc_comp, <- same_side, H0.
        simpl. rewrite H1. auto. }
      exploit update_stack_call_preserved_left; [| | | exact is_left | | | | |];
        eauto using funct_preserved1, funct_preserved2, delta_zero;
        [congruence |].
      intros [st3' [STUPD' st_rel'']].
      exploit call_arguments_preserved; eauto.
      intros [args' [inj_args call_args]].

      exists (State st3' rs3' m3'), j__left', j__right; split; [| split; [| split]].
      + econstructor; [| now eapply star_refl | now traceEq].
        pose proof (rs1_rs3' PC) as inj_pc; rewrite NEXTPC in *; inv inj_pc. rewrite <- H6 in *.
        (* clear dependent j0. *)
        exploit (delta_zero s ge1 ge3); eauto. intros ->.
        eapply exec_step_internal_call; eauto.
        * eapply allowed_call_preserved with (v := Vptr b' Ptrofs.zero);
            eauto using funct_preserved1, funct_preserved2, delta_zero.
          congruence.
        * simpl; now rewrite find_funct.
        * simpl in STUPD'; now rewrite H1 in STUPD'.
        * intros is_cross. unfold Genv.find_comp_ignore_offset in pc_comp.
          rewrite <- pc_comp in is_cross.
          specialize (NO_CROSS_PTR is_cross).
          now eapply Val.inject_list_not_ptr; eauto.
        * inv EV. constructor. unfold Genv.find_comp_ignore_offset in pc_comp.
          now rewrite <- pc_comp.
      + eauto.
      + simpl in same_side.
        econstructor; eauto.
        simpl. rewrite <- same_side. rewrite H0. simpl. now rewrite H1.
      + simpl in same_side.
        econstructor; eauto.

    (** [State] to [ReturnState] *)
    - exploit strong_equiv_state_inv_left; eauto.
      intros (st3 & rs3 & m3 & ? & eq_pc' & find_funct & m1_m3 & rs1_rs3 & side_f); subst.
      rewrite H0 in H3. simpl in H3. destruct Ptrofs.eq_dec; try congruence. simpl in H1; rewrite H1 in H3.
      inv weak_s2_s3.
      exploit exec_instr_preserved_left; simpl; eauto.
      intros (j__left' & rs3' & m3' & exec_instr' & m1_m3' & m2_m3' & rs1_rs3' & st_rel').
      (* assert (pc_comp: Genv.find_comp_ignore_offset ge1 (rs' PC) = Genv.find_comp_ignore_offset ge3 (rs3' PC)). *)
      (* { pose proof (rs1_rs3' PC) as inj_pc; inv inj_pc; auto. admit. *)
      (*   assert (delta = 0) by now eapply delta_zero; eauto. subst delta. *)
      (*   rewrite Ptrofs.add_zero. *)
      (*   simpl. destruct Ptrofs.eq_dec; try congruence. *)
      (*   destruct (Genv.find_funct_ptr ge1 b') eqn:A. *)
      (*   - exploit (Genv.find_funct_ptr_match match_W1_W3); eauto. *)
      (*     intros [[] [f' [find_f' [match_f_f' _]]]]. *)
      (*     exploit funct_preserved1; eauto. intros. *)
      (*     assert (b2 = b') by congruence; subst. rewrite find_f'. *)
      (*     now inv match_f_f'. *)
      (*   - destruct (Genv.find_funct_ptr (Genv.globalenv W3) b2) eqn:B; [| reflexivity]. *)
      (*     exploit funct_preserved2; eauto. intros; subst. *)
      (*     (* Find a contradiction *) *)
      (*     apply Genv.find_funct_ptr_iff in B. *)
      (*     apply Genv.find_def_match_2 with (b := b2) in match_W1_W3. *)
      (*     inv match_W1_W3; try congruence. inv H8; try congruence. *)
      (*     symmetry in H. apply <- Genv.find_funct_ptr_iff in H. congruence. *)
      (* } *)

      (* assert (is_left: s (Genv.find_comp_ignore_offset ge3 (rs3' PC)) = Left). *)
      (* { simpl in same_side. rewrite <- pc_comp, <- same_side, H0. *)
      (*   simpl. rewrite H1. auto. } *)
      (* exploit update_stack_call_preserved; [| | | exact is_left | | | | | | ]; *)
      (*   eauto using funct_preserved1, funct_preserved2, delta_zero; *)
      (*   [congruence |]. *)
      (* intros [st3' [STUPD' [st'_st3' st2_st3']]]. *)
      (* exploit call_arguments_preserved; eauto. *)
      (* intros [args' [inj_args call_args]]. *)

      exists (ReturnState st3 rs3' m3'), j__left', j__right; split; [| split; [| split]].
      + econstructor; [| now eapply star_refl | now traceEq].
        (* pose proof (rs1_rs3' PC) as inj_pc; rewrite NEXTPC in *; inv inj_pc. rewrite <- H6 in *. *)
        (* clear dependent j0. *)
        eapply exec_step_internal_return; eauto.
        * rewrite eq_pc'. simpl. destruct Ptrofs.eq_dec; try congruence; now rewrite find_funct.
        * rewrite eq_pc'. simpl. destruct Ptrofs.eq_dec; try congruence; rewrite find_funct.
          rewrite H0 in REC_CURCOMP; simpl in REC_CURCOMP. destruct Ptrofs.eq_dec; try congruence; rewrite H1 in REC_CURCOMP.
          rewrite REC_CURCOMP.
          (* Q: am I missing something?? *)
          admit.
      + eauto.
      + simpl in same_side.
        econstructor; eauto.
        simpl. rewrite <- same_side. rewrite H0. simpl. now rewrite H1.
      + (* Am missing the weak relation between state and returnstate *)
        admit.

    (** [ReturnState] to [State] *)
    - admit.

    (** Builtin *)
    - admit.

    (** External call *)
    - admit.
*)
  Admitted.

  Lemma simulation:
    @threeway_simulation (semantics W1) (semantics W2) (semantics W3) single_L1 single_L2 single_L3.
  Proof.
    (* apply threeway_simulation_diagram with (strong_equivalence1 := strong_equivalence s ge1 ge3 Left) *)
    (*                                        (strong_equivalence2 := strong_equivalence s ge2 ge3 Right) *)
    (*                                        (weak_equivalence1   := weak_equivalence   s ge1 ge3 Left) *)
    (*                                        (weak_equivalence2   := weak_equivalence   s ge1 ge3 Right) *)
    (*                                        (order := fun _ _ => True). *)
    (* - apply public_symbol_eq21. *)
    (* - apply public_symbol_eq32. *)
    (* - admit. *)
    (* - admit. *)
    (* - admit. *)
    (* - *)
  Admitted.

End Simulation.

