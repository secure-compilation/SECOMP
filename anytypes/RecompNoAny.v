(* The recomposition theorem of security/Recomposition.v needs
   match_prog s δ W1 W3, which requires every External definition of W1 to
   be an External definition of W3 with the same external function
   (match_prog_external_same).  In the proof of RSC, W1 = W_t and
   W3 = link p_compiled Cs_compiled, a program compiled from Clight, which
   has no any-typed External (transf_clight_program_no_any in AnyTypes.v,
   and link_no_any_externals in NoAnyExternals.v).  Hence
   (recomposition_premise_no_any): if W_t has an any-typed External,
   match_prog s δ W_t W3 is false for every such W3, whatever the
   back-translation. *)

Require Import Coqlib Maps AST Globalenvs.
Require Import compcert.riscV.Asm.
Require Import compcert.security.Split compcert.security.Recomposition.
Require Import NoAnyExternals.

Lemma kept_prog_external s (p: Asm.program) δ id ef:
  (prog_defmap p) ! id = Some (Gfun (External ef)) -> kept_prog s p δ id = true.
Proof.
  intros H. apply Genv.find_def_symbol in H as (b & FS & FD).
  unfold kept_prog.
  match goal with |- context [Genv.find_symbol ?ge id] =>
    replace (Genv.find_symbol ge id) with (Some b) by (symmetry; exact FS) end.
  unfold Genv.find_def in FD.
  match goal with |- context [PTree.get b (Genv.genv_defs ?ge)] =>
    replace (PTree.get b (Genv.genv_defs ge)) with (Some (@Gfun Asm.fundef unit (External ef))) by (symmetry; exact FD) end.
  reflexivity.
Qed.

Theorem match_prog_external_same s δ (W1 W3: Asm.program) id ef:
  match_prog s δ W1 W3 ->
  (prog_defmap W1) ! id = Some (Gfun (External ef)) ->
  (prog_defmap W3) ! id = Some (Gfun (External ef)).
Proof.
  intros M H. rewrite (match_prog_def _ _ _ _ M id); auto. eapply kept_prog_external; eauto.
Qed.

Theorem recomposition_premise_no_any s δ (W1 W3: Asm.program):
  match_prog s δ W1 W3 -> no_any_externals W3 ->
  forall id ef, (prog_defmap W1) ! id = Some (Gfun (External ef)) -> sig_has_any (ef_sig ef) = false.
Proof.
  intros M N id ef H. apply (N id). apply in_prog_defmap. eapply match_prog_external_same; eauto.
Qed.

(* W1 and W2 must have the same external function at every identifier where
   both have an External definition.  With a back-translation that declares a stand-in
   [External (ef_erase_any ef)] for an any-typed [External ef], W1 = W_t has [External ef]
   and W2 (the compiled back-translation) has the stand-in at the same
   identifier, with a different
   signature when [ef] has an any type, so no W3 satisfies both premises of
   the recomposition theorem (Recomposition.v, Section Theorems). *)
Theorem recomposition_same_externals s δ δ' (W1 W2 W3: Asm.program) id ef1 ef2:
  match_prog s δ W1 W3 -> match_prog s δ' W2 W3 ->
  (prog_defmap W1) ! id = Some (Gfun (External ef1)) ->
  (prog_defmap W2) ! id = Some (Gfun (External ef2)) ->
  ef1 = ef2.
Proof.
  intros M1 M2 H1 H2.
  apply (match_prog_external_same _ _ _ _ _ _ M1) in H1.
  apply (match_prog_external_same _ _ _ _ _ _ M2) in H2.
  rewrite H1 in H2. congruence.
Qed.
