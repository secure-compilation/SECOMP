(** * The statement of the admitted lemma [step_fix_fix] and generic facts.

    Checked on this branch, which is ccs-backtranslation with PR #19
    (fix-13-ccs-backtranslation); its riscV/Asm.v, common/ and
    security/BtInfoAsm.v are identical to ccs-backtranslation's.

    Admitted lemma, security/BacktranslationProof2.v:1243-1250 on
    ccs-backtranslation (1279-1286 on fix-13-ccs-backtranslation):

<<
  Lemma step_fix_fix p s tr s' :
    star (Asm.step (comp_of_main p)) (Genv.globalenv p) s tr s'
    -> star (step_fix (comp_of_main p)) (Genv.globalenv p) s tr s'.
  Proof. (* TODO: FIXME *) Admitted.
>>
*)

Require Import Coqlib Maps Integers Values Memory Globalenvs.
Require Import AST Smallstep Events.
Require Import riscV.Asm.

Definition step_fix_fix_stmt : Prop :=
  forall (p: Asm.program) (s: Asm.state) (tr: trace) (s': Asm.state),
    star (Asm.step (comp_of_main p)) (Genv.globalenv p) s tr s' ->
    star (step_fix (comp_of_main p)) (Genv.globalenv p) s tr s'.

(** If no step is possible from [s], a [star] from [s] is the empty run. *)
Lemma star_from_stuck:
  forall (genv state: Type) (step: genv -> state -> trace -> state -> Prop)
         (ge: genv) (s: state) (t: trace) (s': state),
    (forall t1 s1, ~ step ge s t1 s1) ->
    star step ge s t s' -> t = E0 /\ s' = s.
Proof.
  intros genv state step ge s t s' NOSTEP STAR.
  inversion STAR; subst.
  - auto.
  - exfalso. eapply NOSTEP; eauto.
Qed.

(** Hence: if [step_fix] is stuck at [s], there is no [step_fix] run from [s]
    with a non-empty trace, whatever the final state. *)
Lemma no_star_nonempty_from_stuck:
  forall (genv state: Type) (step: genv -> state -> trace -> state -> Prop)
         (ge: genv) (s: state) (e: event) (t: trace) (s': state),
    (forall t1 s1, ~ step ge s t1 s1) ->
    ~ star step ge s (e :: t) s'.
Proof.
  intros genv state step ge s e t s' NOSTEP STAR.
  destruct (star_from_stuck _ _ _ _ _ _ _ NOSTEP STAR) as [E _].
  discriminate.
Qed.
