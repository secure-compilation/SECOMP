(** * More results about any types (ccs-main + PR #18), on top of AnyTypes.v

    [bt_split_general], [bt_split_incl]: for Clight programs [p], [C] with
    [link p C = Some W], if [W] contains a declaration of an any-typed
    external function (with any C types), then [p] or [C] fails
    [transf_clight_program].  [compiles_no_any_decl]: a Clight program that
    compiles has no such declaration, whatever its C types.
    [bt_defs_rejected_nonvacuous]: the hypotheses of [bt_defs_rejected] can
    be met for every [W_t] and trace.  [gen_program_obligation_3_false]: the
    admitted obligation 3 of [gen_program] (agr_comps) is false too.
    [bt_split_vacuous_W2] shows why [bt_split_does_not_compile] in AnyTypes.v,
    stated with a list equality, is weaker than [bt_split_incl]. *)


From Stdlib Require Import String List.
Require Import Coqlib Maps Errors AST Linking Globalenvs.
Require Import Ctypes Clight.
Require Import Compiler.
Require compcert.riscV.Asm.
Require Import compcert.security.Backtranslation.
Require Import anytypes.AnyTypes.
Import ListNotations.

(** ** K3: a compiled Clight program declares no any-typed external function *)

Theorem compiles_no_any_decl:
  forall (p: Clight.program) tp id ef targs tres cc,
  transf_clight_program p = OK tp ->
  In (id, Gfun (Ctypes.External ef targs tres cc)) (Ctypes.prog_defs p) ->
  sig_has_any (ef_sig ef) = false.
Proof.
  intros p tp id ef targs tres cc T IN.
  destruct (sig_has_any (ef_sig ef)) eqn:A; auto. exfalso.
  assert (NE: ef_sig ef <> signature_of_type targs tres cc).
  { intros E. rewrite E, signature_of_type_no_any in A. discriminate. }
  destruct (transf_clight_program_rejects_bad_external p id ef targs tres cc IN NE) as [e E].
  congruence.
Qed.

(** ** K2: the split result with containment instead of list equality *)

Theorem bt_split_general:
  forall (p C W: Clight.program) id ef targs tres cc,
  link p C = Some W ->
  In (id, Gfun (Ctypes.External ef targs tres cc)) (Ctypes.prog_defs W) ->
  sig_has_any (ef_sig ef) = true ->
  (exists e, transf_clight_program p = Error e) \/
  (exists e, transf_clight_program C = Error e).
Proof.
  intros p C W id ef targs tres cc L IN A.
  assert (NE: ef_sig ef <> signature_of_type targs tres cc).
  { intros E. rewrite E, signature_of_type_no_any in A. discriminate. }
  destruct (clight_link_external_side p C W id ef targs tres cc L IN) as [I|I];
    [left|right]; eapply transf_clight_program_rejects_bad_external; eauto.
Qed.

Corollary bt_split_incl:
  forall (W_t: Asm.program) tr (p C W: Clight.program) id ef,
  link p C = Some W ->
  incl (gen_prog_defs (Genv.globalenv W_t) tr (AST.prog_defs W_t)) (Ctypes.prog_defs W) ->
  In (id, Gfun (AST.External ef)) (AST.prog_defs W_t) ->
  sig_has_any (ef_sig ef) = true ->
  (exists e, transf_clight_program p = Error e) \/
  (exists e, transf_clight_program C = Error e).
Proof.
  intros W_t tr p C W id ef L INC IN A.
  eapply bt_split_general;
    [exact L | apply INC; apply gen_prog_defs_external_decl; exact IN | exact A].
Qed.

(** ** K1: the original split hypothesis is unsatisfiable for some W_t *)

Local Transparent Ctypes.Linker_program.

Lemma linked_defs_are_elements:
  forall (p C W: Clight.program), link p C = Some W ->
  exists m: PTree.t (globdef Clight.fundef type), Ctypes.prog_defs W = PTree.elements m.
Proof.
  intros p C W L. simpl in L. unfold link_program in L.
  destruct (link (program_of_program p) (program_of_program C)) as [pw|] eqn:LP; try discriminate.
  destruct (lift_option (link (prog_types p) (prog_types C))) as [[typs EQ]|EQ]; try discriminate.
  destruct (link_build_composite_env (prog_types p) (prog_types C) typs
       (prog_comp_env p) (prog_comp_env C) (prog_comp_env_eq p)
       (prog_comp_env_eq C) EQ) as (env & P & Q & R).
  inv L. simpl.
  apply link_prog_inv in LP. destruct LP as (_ & _ & yes & E). subst pw. simpl. eauto.
Qed.

Lemma elements_fixpoint:
  forall {A: Type} (m: PTree.t A) l,
  PTree.elements m = l -> PTree.elements (PTree_Properties.of_list l) = l.
Proof.
  intros A m l E. subst l. f_equal. apply PTree.extensionality. intros i.
  apply PTree_Properties.of_list_elements.
Qed.

(** [W2]: two any-typed declarations, listed in [PTree.elements] order
    (ids 2 then 1), as in a linked [W_t]. *)
Definition W2_defs : list (ident * globdef Asm.fundef unit) :=
  (2%positive, Gfun (AST.External ef_any)) :: (1%positive, Gfun (AST.External ef_any)) :: nil.

Lemma W2_defs_linked_order:
  PTree.elements (PTree_Properties.of_list W2_defs) = W2_defs.
Proof. reflexivity. Qed.

Definition W2_pol : Policy.t :=
  Policy.mkpolicy (PTree.set 2%positive bottom (PTree.set 1%positive bottom (PTree.empty _)))
                  (CompTree.empty _) (CompTree.empty _) (CompTree.empty _).

Lemma W2_pol_pub: Policy.in_pub W2_pol nil.
Proof.
  split; intros cp l H; unfold W2_pol in H; simpl in H; rewrite CompTree.gempty in H; discriminate.
Qed.

Lemma W2_agr: agr_comps W2_pol W2_defs.
Proof.
  unfold agr_comps. rewrite Forall_forall. intros [id gd] IN cp E.
  simpl in IN. destruct IN as [H|[H|[]]]; inv H; apply bottom_flowsto.
Qed.

Lemma W2_complete: pol_complete W2_pol W2_defs.
Proof.
  unfold pol_complete. rewrite Forall_forall. intros [id gd] IN.
  simpl in IN. destruct IN as [H|[H|[]]]; inv H; exists bottom; reflexivity.
Qed.

Definition W2 : Asm.program :=
  mkprogram W2_defs nil 3%positive W2_pol W2_pol_pub W2_agr W2_complete.

Lemma W2_keys: forall a_ge tr,
  map fst (gen_prog_defs a_ge tr (AST.prog_defs W2)) = [2; 1; 5; 4]%positive.
Proof. intros; reflexivity. Qed.

Lemma W2_sorted_keys: forall a_ge tr,
  map fst (PTree.elements (PTree_Properties.of_list (gen_prog_defs a_ge tr (AST.prog_defs W2))))
  = [4; 2; 1; 5]%positive.
Proof. intros. vm_compute. reflexivity. Qed.

Theorem bt_split_vacuous_W2:
  forall tr (p C W: Clight.program),
  link p C = Some W ->
  Ctypes.prog_defs W <> gen_prog_defs (Genv.globalenv W2) tr (AST.prog_defs W2).
Proof.
  intros tr p C W L E.
  destruct (linked_defs_are_elements p C W L) as [m M].
  rewrite E in M. symmetry in M. apply elements_fixpoint in M.
  assert (K: map fst (PTree.elements (PTree_Properties.of_list
                (gen_prog_defs (Genv.globalenv W2) tr (AST.prog_defs W2))))
             = map fst (gen_prog_defs (Genv.globalenv W2) tr (AST.prog_defs W2)))
    by (f_equal; exact M).
  rewrite W2_sorted_keys, W2_keys in K. discriminate.
Qed.

(** W2 has an any-typed [External], so all other hypotheses of
    [bt_split_does_not_compile] hold for it. *)
Lemma W2_has_any_external:
  In (1%positive, Gfun (AST.External ef_any)) (AST.prog_defs W2) /\ sig_has_any (ef_sig ef_any) = true.
Proof. split; [right; left; reflexivity | reflexivity]. Qed.

(** ** K4: every list of Clight definitions is realizable as a Clight program *)

Definition pol_top (defs: list (ident * globdef Clight.fundef type)) : Policy.t :=
  Policy.mkpolicy (PTree_Properties.of_list (map (fun idg => (fst idg, top)) defs))
                  (CompTree.empty _) (CompTree.empty _) (CompTree.empty _).

Lemma pol_top_pub: forall defs, Policy.in_pub (pol_top defs) nil.
Proof.
  split; intros cp l H; unfold pol_top in H; simpl in H; rewrite CompTree.gempty in H; discriminate.
Qed.

Lemma pol_top_agr: forall defs, agr_comps (pol_top defs) defs.
Proof.
  intros defs. unfold agr_comps. rewrite Forall_forall. intros [id gd] IN cp E.
  simpl in E. apply PTree_Properties.in_of_list in E.
  apply in_map_iff in E. destruct E as ([id' gd'] & E & _). simpl in E. inv E.
  apply flowsto_top.
Qed.

Lemma pol_top_complete: forall defs, pol_complete (pol_top defs) defs.
Proof.
  intros defs. unfold pol_complete. rewrite Forall_forall. intros [id gd] IN.
  simpl. apply PTree_Properties.of_list_dom.
  rewrite map_map. simpl. change id with (fst (id, gd)). apply in_map. auto.
Qed.

Definition clight_of_defs (defs: list (ident * globdef Clight.fundef type)) : Clight.program := {|
  Ctypes.prog_defs := defs;
  Ctypes.prog_public := nil;
  Ctypes.prog_main := 1%positive;
  Ctypes.prog_pol := pol_top defs;
  Ctypes.prog_types := nil;
  Ctypes.prog_comp_env := PTree.empty _;
  Ctypes.prog_comp_env_eq := eq_refl;
  Ctypes.prog_pol_pub := pol_top_pub defs;
  Ctypes.prog_agr_comps := pol_top_agr defs;
  Ctypes.prog_pol_complete := pol_top_complete defs |}.

Lemma clight_defs_realizable:
  forall defs, exists p: Clight.program, Ctypes.prog_defs p = defs.
Proof. intros. exists (clight_of_defs defs). reflexivity. Qed.

Theorem bt_defs_rejected_nonvacuous:
  forall (W_t: Asm.program) tr id ef,
  In (id, Gfun (AST.External ef)) (AST.prog_defs W_t) ->
  sig_has_any (ef_sig ef) = true ->
  exists p: Clight.program,
    Ctypes.prog_defs p = gen_prog_defs (Genv.globalenv W_t) tr (AST.prog_defs W_t) /\
    (exists e, transf_clight_program p = Error e).
Proof.
  intros. exists (clight_of_defs (gen_prog_defs (Genv.globalenv W_t) tr (AST.prog_defs W_t))).
  split; auto. eapply bt_defs_rejected; eauto. reflexivity.
Qed.

(** ** K5: obligation 3 of [gen_program] is false too; obligation 2 holds *)

Lemma gen_program_obligation_2_provable:
  forall (tr: BtInfoAsm.bundle_trace) (a_p: Asm.program),
  Policy.in_pub (AST.prog_pol a_p) (AST.prog_public a_p).
Proof. intros. apply AST.prog_pol_pub. Qed.

Definition gv3 : globvar unit := mkglobvar tt (Comp 7%positive) nil false false.
Definition W3_defs : list (ident * globdef Asm.fundef unit) := (1%positive, Gvar gv3) :: nil.
Definition W3_pol : Policy.t :=
  Policy.mkpolicy (PTree.set 3%positive (Comp 8%positive)
                    (PTree.set 1%positive (Comp 7%positive) (PTree.empty _)))
                  (CompTree.empty _) (CompTree.empty _) (CompTree.empty _).

Lemma W3_pol_pub: Policy.in_pub W3_pol nil.
Proof.
  split; intros cp l H; unfold W3_pol in H; simpl in H; rewrite CompTree.gempty in H; discriminate.
Qed.

Lemma W3_agr: agr_comps W3_pol W3_defs.
Proof.
  constructor; [|constructor]. simpl. intros cp H. inv H. apply flowsto_refl.
Qed.

Lemma W3_complete: pol_complete W3_pol W3_defs.
Proof. constructor; [|constructor]. exists (Comp 7%positive). reflexivity. Qed.

Definition W3 : Asm.program :=
  mkprogram W3_defs nil 2%positive W3_pol W3_pol_pub W3_agr W3_complete.

Lemma gen_program_obligation_3_false:
  ~ (forall tr (a_p: Asm.program),
       agr_comps (AST.prog_pol a_p) (gen_prog_defs (Genv.globalenv a_p) tr (AST.prog_defs a_p))).
Proof.
  intros H. specialize (H nil W3). unfold agr_comps in H. rewrite Forall_forall in H.
  specialize (H (3%positive, gen_counter (Comp 7%positive))).
  assert (IN: In (3%positive, gen_counter (Comp 7%positive))
                 (gen_prog_defs (Genv.globalenv W3) nil (AST.prog_defs W3))).
  { unfold gen_prog_defs. apply in_or_app; right. simpl. left; reflexivity. }
  specialize (H IN (Comp 8%positive) eq_refl). simpl in H. inv H.
Qed.

Lemma gen_program_obligation_3_inconsistent: False.
Proof.
  apply gen_program_obligation_3_false. exact Backtranslation.gen_program_obligation_3.
Qed.

(** ** K6: the linking hypothesis of [assumption1_fails] is satisfiable *)

Local Transparent Linker_prog.

Definition E0_defs : list (ident * globdef Asm.fundef unit) := nil.
Lemma E0_agr: agr_comps W_ex_pol E0_defs. Proof. constructor. Qed.
Lemma E0_complete: pol_complete W_ex_pol E0_defs. Proof. constructor. Qed.
Definition E0 : Asm.program :=
  mkprogram E0_defs nil 2%positive W_ex_pol W_ex_pol_pub E0_agr E0_complete.

Lemma W_ex_link_nonvacuous:
  exists W_t, link E0 W_ex = Some W_t /\
    (prog_defmap W_ex) ! 1%positive = Some (Gfun (AST.External ef_any)) /\
    (prog_defmap E0) ! 1%positive = None /\
    In (1%positive, Gfun (AST.External ef_any)) (AST.prog_defs W_t).
Proof.
  destruct (link E0 W_ex) as [W_t|] eqn:L.
  - exists W_t. split; auto. split; [reflexivity|]. split; [reflexivity|].
    eapply link_keeps_context_external; eauto; reflexivity.
  - exfalso. simpl in L. unfold link_prog in L. simpl in L.
    vm_compute in L. discriminate.
Qed.

Corollary assumption1_fails_W_ex_instance:
  forall tr, exists W_t (pc: Clight.program),
    link E0 W_ex = Some W_t /\
    Ctypes.prog_defs pc = gen_prog_defs (Genv.globalenv W_t) tr (AST.prog_defs W_t) /\
    exists e, transf_clight_program pc = Error e.
Proof.
  intros tr. destruct W_ex_link_nonvacuous as (W_t & L & G2 & G1 & _).
  exists W_t, (clight_of_defs (gen_prog_defs (Genv.globalenv W_t) tr (AST.prog_defs W_t))).
  split; auto. split; auto.
  eapply (assumption1_fails (clight_of_defs nil) E0 W_ex W_t tr _ 1%positive ef_any); eauto.
Qed.
