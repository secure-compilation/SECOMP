(** * More results about any types (ccs-backtranslation + PR #19), on top
    of AnyTypesBT.v: the same as AnyTypesExtra.v, except the result about
    the obligations of [gen_program], which has none on this branch. *)


Require Import String List.
Require Import Coqlib Maps Errors AST Linking Globalenvs.
Require Import Ctypes Clight.
Require Import Compiler.
Require compcert.riscV.Asm.
Require Import compcert.security.Backtranslation.
Require Import anytypes.AnyTypesBT.
Import ListNotations.

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
  apply link_prog_inv in LP. destruct LP as (_ & _ & _ & E). subst pw. simpl. eauto.
Qed.

Lemma elements_fixpoint:
  forall {A: Type} (m: PTree.t A) l,
  PTree.elements m = l -> PTree.elements (PTree_Properties.of_list l) = l.
Proof.
  intros A m l E. subst l. f_equal. apply PTree.extensionality. intros i.
  apply PTree_Properties.of_list_elements.
Qed.

Definition W2_defs : list (ident * globdef Asm.fundef unit) :=
  (2%positive, Gfun (AST.External ef_any)) :: (1%positive, Gfun (AST.External ef_any)) :: nil.

Lemma W2_defs_linked_order:
  PTree.elements (PTree_Properties.of_list W2_defs) = W2_defs.
Proof. reflexivity. Qed.

Definition W2 : Asm.program := mkprogram W2_defs nil 3%positive Policy.empty_pol.

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

Lemma W2_has_any_external:
  In (1%positive, Gfun (AST.External ef_any)) (AST.prog_defs W2) /\ sig_has_any (ef_sig ef_any) = true.
Proof. split; [right; left; reflexivity | reflexivity]. Qed.

Definition clight_of_defs (defs: list (ident * globdef Clight.fundef type)) : Clight.program := {|
  Ctypes.prog_defs := defs;
  Ctypes.prog_public := nil;
  Ctypes.prog_main := 1%positive;
  Ctypes.prog_pol := Policy.empty_pol;
  Ctypes.prog_types := nil;
  Ctypes.prog_comp_env := PTree.empty _;
  Ctypes.prog_comp_env_eq := eq_refl |}.

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
