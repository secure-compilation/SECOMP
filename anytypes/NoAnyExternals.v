(* A syntactic premise that excludes the Asm programs that declare an
   external function with an any type (ccs-main + PR #18).

   - no_any_externals / no_any_externals_b (+ no_any_externals_b_spec):
     the premise, as a Prop and as a decision procedure;
   - link_no_any_externals: linking preserves it;
   - W_t_no_any_externals: in the setting of security/RSC.v it holds for
     W_t = link p_compiled Ct as soon as it holds for Ct, given that
     compiled programs satisfy it (proved as transf_clight_program_no_any in
     AnyTypes.v; see RecompNoAnyClosed.v for the combination);
   - bt_declarations_accepted: under the premise, every External
     declaration that gen_program emits passes the check of
     Cshmgen.transl_fundef, for every informative trace.
   Where the premise would go:
     security/RSC.v:     Hypothesis Ct_no_any: no_any_externals Ct.
     Assumption 1:       a premise no_any_externals W_t. *)

Require Import Coqlib Maps Errors AST Linking Globalenvs Ctypes Clight.
Require compcert.cfrontend.Cshmgen compcert.riscV.Asm.
Require Import Compiler.
Require Import compcert.security.Backtranslation.

Definition xtype_is_any (x: xtype): bool :=
  match x with Xany32 | Xany64 => true | _ => false end.

Definition sig_has_any (sg: signature): bool :=
  existsb xtype_is_any sg.(sig_args) || xtype_is_any sg.(sig_res).

(* No External definition of [p] has an any type in its signature.  (Same
   statement as no_any_ext in AnyTypes.v.) *)
Definition no_any_externals {F V: Type} {CF: has_comp (AST.fundef F)} (p: AST.program (AST.fundef F) V) : Prop :=
  forall id ef, In (id, Gfun (AST.External ef)) (AST.prog_defs p) -> sig_has_any (ef_sig ef) = false.

Definition no_any_externals_b {F V: Type} {CF: has_comp (AST.fundef F)} (p: AST.program (AST.fundef F) V) : bool :=
  forallb (fun '(id, gd) => match gd with
                            | Gfun (AST.External ef) => negb (sig_has_any (ef_sig ef))
                            | _ => true
                            end) (AST.prog_defs p).

Lemma no_any_externals_b_spec {F V: Type} {CF: has_comp (AST.fundef F)} (p: AST.program (AST.fundef F) V):
  no_any_externals_b p = true <-> no_any_externals p.
Proof.
  unfold no_any_externals_b, no_any_externals. rewrite forallb_forall. split.
  - intros H id ef IN. specialize (H _ IN). simpl in H. destruct (sig_has_any (ef_sig ef)); auto.
  - intros H [id gd] IN. destruct gd as [[f|ef]|v]; auto.
    rewrite (H _ _ IN). reflexivity.
Qed.

(* ---------- linking ---------- *)

Local Transparent Linker_prog Linker_def Linker_fundef.

Lemma link_fundef_External {F: Type} (f1 f2: AST.fundef F) ef:
  Linking.link_fundef f1 f2 = Some (AST.External ef) -> f1 = AST.External ef.
Proof.
  destruct f1 as [f1|ef1], f2 as [f2|ef2]; simpl; intros H; try discriminate.
  - destruct ef2; discriminate.
  - destruct ef1; discriminate.
  - destruct (external_function_eq ef1 ef2); inversion H; subst; reflexivity.
Qed.

Lemma link_no_any_externals (p1 p2 p: Asm.program):
  no_any_externals p1 -> no_any_externals p2 -> link p1 p2 = Some p -> no_any_externals p.
Proof.
  intros N1 N2 L id ef IN.
  simpl in L. apply link_prog_inv in L as (_ & _ & yes & E). subst p. simpl in IN.
  apply PTree.elements_complete in IN. rewrite PTree.gcombine in IN by reflexivity.
  unfold link_prog_merge in IN.
  destruct (prog_defmap p1) ! id as [gd1|] eqn:G1; destruct (prog_defmap p2) ! id as [gd2|] eqn:G2.
  - simpl in IN. destruct gd1 as [f1|v1], gd2 as [f2|v2]; simpl in IN; try discriminate.
    + destruct (link f1 f2) as [f|] eqn:LF; [|discriminate].
      change (Linking.link_fundef f1 f2 = Some f) in LF.
      injection IN as E. rewrite E in LF.
      apply link_fundef_External in LF; subst.
      eapply N1. apply in_prog_defmap. eauto.
    + destruct (link v1 v2); discriminate.
  - inversion IN; subst. eapply N1. apply in_prog_defmap. eauto.
  - inversion IN; subst. eapply N2. apply in_prog_defmap. exact G2.
  - discriminate.
Qed.

(* ---------- discharging the premise for W_t ---------- *)

Theorem W_t_no_any_externals
  (COMPILED: forall p tp, transf_clight_program p = OK tp -> no_any_externals tp)
  (p: Clight.program) (p_compiled Ct W_t: Asm.program):
  transf_clight_program p = OK p_compiled ->
  no_any_externals Ct ->
  link p_compiled Ct = Some W_t ->
  no_any_externals W_t.
Proof.
  intros C N L. apply (link_no_any_externals p_compiled Ct W_t); [exact (COMPILED p p_compiled C) | exact N | exact L].
Qed.

(* ---------- under the premise, the back-translated declarations compile ---------- *)

Lemma argtype_xtype_to_type_ext x: xtype_is_any x = false -> argtype_of_type (xtype_to_type_ext x) = x.
Proof. destruct x; simpl; congruence. Qed.

Lemma rettype_xtype_to_type_ext x: xtype_is_any x = false -> rettype_of_type (xtype_to_type_ext x) = x.
Proof. destruct x; simpl; congruence. Qed.

Lemma signature_of_type_ext sg:
  sig_has_any sg = false ->
  signature_of_type (map xtype_to_type_ext (sig_args sg)) (xtype_to_type_ext (sig_res sg)) (sig_cc sg) = sg.
Proof.
  destruct sg as [args res cc]. unfold sig_has_any, signature_of_type; simpl.
  intros H. apply orb_false_iff in H as [A R].
  rewrite rettype_xtype_to_type_ext by auto. f_equal.
  induction args as [|a args IH]; simpl in *; auto.
  apply orb_false_iff in A as [A1 A2]. rewrite argtype_xtype_to_type_ext by auto. f_equal; auto.
Qed.

(* Stated for [gen_prog_defs] (see the comment in FixF1.v); the corollary
   for [gen_program] inherits its admitted obligations. *)
Theorem bt_defs_declarations_accepted a_ge tr (gds: list (ident * globdef Asm.fundef unit)):
  (forall id ef, In (id, Gfun (AST.External ef)) gds -> sig_has_any (ef_sig ef) = false) ->
  forall id ef targs tres cc,
  In (id, Gfun (Ctypes.External ef targs tres cc)) (gen_prog_defs a_ge tr gds) ->
  ef_sig ef = signature_of_type targs tres cc
  /\ forall ce, Cshmgen.transl_fundef ce id (Ctypes.External ef targs tres cc) = OK (AST.External ef).
Proof.
  intros N id ef targs tres cc IN.
  assert (S: ef_sig ef = signature_of_type targs tres cc).
  { revert IN. unfold gen_prog_defs.
    intros IN. apply in_app_or in IN as [IN | IN].
    - apply in_map_iff in IN as [[id0 gd] [EQ IN]]. inversion EQ; subst id0. clear EQ.
      revert H1. unfold gen_progdef.
      destruct (PTree.get id _) as [[cnt c]|]; [|discriminate].
      destruct (PTree.get id _) as [params|]; [|discriminate].
      unfold gen_globdef. destruct gd as [[f|ef0]|v]; try discriminate.
      unfold gen_fundef. intros E. inversion E; subst. clear E.
      unfold from_extfun_fun_data, from_sig_fun_data_ext; simpl.
      rewrite signature_of_type_ext; auto. eapply N; eauto.
    - apply in_map_iff in IN as [[k [id' gd']] [EQ IN]]. simpl in EQ. inversion EQ; subst. clear EQ.
      apply PTree.elements_complete in IN. unfold gen_counter_defs in IN.
      apply PTree_Properties.in_of_list in IN.
      apply in_map_iff in IN as [[i g] [EQ _]]. unfold gen_counter in EQ. inversion EQ. }
  split; auto. intros ce. unfold Cshmgen.transl_fundef.
  destruct (signature_eq _ _); congruence.
Qed.

Corollary bt_declarations_accepted tr (W: Asm.program):
  no_any_externals W ->
  forall id ef targs tres cc,
  In (id, Gfun (Ctypes.External ef targs tres cc)) (Ctypes.prog_defs (gen_program tr W)) ->
  ef_sig ef = signature_of_type targs tres cc
  /\ forall ce, Cshmgen.transl_fundef ce id (Ctypes.External ef targs tres cc) = OK (AST.External ef).
Proof.
  intros N. unfold gen_program; simpl. apply bt_defs_declarations_accepted. exact N.
Qed.
