# Counterexamples to `step_fix_fix`

*These files were prepared by Claude, quickly reviewed by Cătălin Hrițcu.*

The proof of the back-translation (`backtranslation_proof` and `asm_to_clight` in `security/BacktranslationProof2.v`) uses the admitted lemma `step_fix_fix`, which says that every run of `Asm.step` is a run of `step_fix`, a variant of `Asm.step` with four additional checks (`riscV/Asm.v`). The files in this folder prove that this lemma is false, also where the proof uses it, and that the proof goes through when this use is replaced by a hypothesis. See the issue about `step_fix_fix` for the discussion.

This branch is `fix-13-ccs-backtranslation` (`ccs-backtranslation` with PR #19) plus this folder. PR #19 changes neither `riscV/Asm.v` nor the statements used here.

## Building

Build the tree as described in the README (`make`), then run

    stepfix/build.sh

It compiles `security/BacktranslationProof2.v`, which is not in the Makefile, if needed, and then the files below, printing the output of their `Print Assumptions` commands. None of these files uses an admitted lemma, except `step_fix_fix_proves_False`, which applies the refutation to `step_fix_fix` itself.

## Files

| File | Main results |
|---|---|
| `StepFixChecks.v` | `step_fix_iff`: `step_fix` is exactly `Asm.step` plus the four checks (CALLSIG, CHECKPUB at calls and returns, builtin results in machine registers, ECC). `Print Assumptions backtranslation_proof`. |
| `StepFixFixCommon.v` | `step_fix_fix_stmt`, the statement of `step_fix_fix`. |
| `StepFixFixCheckpub.v` | Counterexample 1: a public `int *px = &y;` (in Asm form) and a cross-compartment call; fails CHECKPUB. |
| `StepFixFixCallsig.v` | Counterexample 2: a hand-written call whose signature differs from the callee's; fails CALLSIG. |
| `StepFixFixBuiltinRes.v` | Counterexample 3: a hand-written builtin with result register `X31`; fails the check on builtin results. |
| `StepFixFixEccMemcpy.v` | Counterexample 4: a `memcpy` into a public variable (a struct assignment), then a call; fails ECC. |
| `StepFixFixMain.v` | `not_step_fix_fix`; `step_fix_fix_proves_False`; `not_step_fix_fix_use_site`, for programs and traces that satisfy all hypotheses of `asm_to_clight` and `asm_program_is_wf`; `checks_summary`, which check fails in which counterexample. |
| `InitMemPublic.v` | `init_mem_public_first_order_iff`: in the initial memory, public memory is first-order exactly when no public, non-volatile variable is initialized with an address; related facts about stores and ECC. |
| `AsmToClightStepFix.v` | `asm_to_clight_stepfix_prefix` and `backtranslation_proof_stepfix_prefix`: the proof of `asm_to_clight`, copied from `security/BacktranslationProof2.v`, with its single use of `step_fix_fix` replaced by the hypothesis that some `step_fix` run from the initial state produces the trace. |
