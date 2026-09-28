(* Combines RecompNoAny.v with the compiler lemmas of AnyTypes.v
   (W_t_any_external_no_recomposition): in the setting of security/RSC.v, if
   the target program W_t has an External definition with an any type, then
   for every back-translated context Cs that compiles, the recombined
   program W3 = link p_compiled Cs_compiled does not satisfy the premise
   match_prog s δ W_t W3 of the recomposition theorem, whatever the
   back-translation. *)

Require Import Coqlib Maps AST Linking Globalenvs Errors.
Require Import Compiler.
Require compcert.riscV.Asm Clight.
Require Import compcert.security.Split compcert.security.Recomposition.
Require Import NoAnyExternals RecompNoAny.
Require AnyTypes.

Lemma no_any_ext_equiv {F V: Type} {CF: has_comp (AST.fundef F)} (p: AST.program (AST.fundef F) V):
  AnyTypes.no_any_ext p <-> no_any_externals p.
Proof. split; intros H id ef IN; exact (H id ef IN). Qed.

Theorem W_t_any_external_no_recomposition
  s δ (p Cs: Clight.program) (p_compiled Cs_compiled W_t W3: Asm.program) id ef:
  transf_clight_program p = OK p_compiled ->
  transf_clight_program Cs = OK Cs_compiled ->
  link p_compiled Cs_compiled = Some W3 ->
  (prog_defmap W_t) ! id = Some (Gfun (External ef)) ->
  sig_has_any (ef_sig ef) = true ->
  ~ match_prog s δ W_t W3.
Proof.
  intros P C L D A M.
  assert (N: no_any_externals W3).
  { apply no_any_ext_equiv.
    eapply AnyTypes.link_no_any; [exact L | |];
      eapply AnyTypes.transf_clight_program_no_any; eauto. }
  pose proof (recomposition_premise_no_any _ _ _ _ M N id ef D). congruence.
Qed.
