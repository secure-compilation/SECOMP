# External functions with `any` types and the back-translation

*These files were prepared by Claude, quickly reviewed by Cătălin Hrițcu.*

Coq proofs for the issue about target contexts that declare external functions with `any` types (`Xany32`, `Xany64`). The back-translation's output does not compile for such contexts, programs compiled from C never have such declarations, and recomposition's premise fails for them.

This branch is `fix-13-ccs-main` (`ccs-main` with PR #18) plus this folder.

## Building

Build the tree as described in the README (`make`), then run

    anytypes/build.sh

It compiles the files below and prints the axioms of the main results. The files in `ccs-backtranslation/` are the same results for `ccs-backtranslation` with PR #19; compile them against a built tree of that branch with

    anytypes/build.sh --bt <tree>

## Files

| File | Main results |
|---|---|
| `AnyTypes.v` | `signature_of_type_no_any`: no C type gives an `any` type. `transl_fundef_external_no_any`: Cshmgen rejects external declarations with `any` types, whatever their C types. `gen_fundef_external_accepted`: the back-translated declaration of an external function is accepted exactly when its signature has no `any` type. `bt_defs_rejected`, `assumption1_fails`: for every trace, the back-translation of a target program with such a declaration fails `transf_clight_program`. `transf_clight_program_no_any`, `transf_c_program_no_any`, `link_no_any`, `W_t_no_any`: programs compiled from Clight or C have no such declaration, and linking preserves this. `bt_externals_accepted`: without such declarations in the target context, every declaration of the back-translation passes Cshmgen. `gen_program_obligation_4_false`: an admitted obligation of `gen_program` is false. |
| `AnyTypesExtra.v` | `bt_split_general`, `bt_split_incl`: for every Clight split whose link contains such a declaration, one of the two parts does not compile. `compiles_no_any_decl`. `gen_program_obligation_3_false`: another admitted obligation of `gen_program` is false. |
| `NoAnyExternals.v` | `no_any_externals` and its decision procedure (`no_any_externals_b_spec`), the syntactic premise that excludes such declarations; `link_no_any_externals`, `W_t_no_any_externals`. |
| `RecompNoAny.v` | `match_prog_external_same`, `recomposition_premise_no_any`: recomposition's `match_prog` requires identical external declarations, so it fails when the target program has an `any`-typed one and the recombined program has none. |
| `RecompNoAnyClosed.v` | `W_t_any_external_no_recomposition`: in the setting of `security/RSC.v`, no recombined program compiled from Clight satisfies recomposition's premise when the target program has such a declaration. |
| `ccs-backtranslation/` | `AnyTypesBT.v` and `AnyTypesExtraBT.v`: the same results on `ccs-backtranslation` with PR #19. There, the results about compiled programs rely on `Selectionproof.transf_program_match`, which is admitted on that branch. |

The only results that use admitted lemmas are those stated for `gen_program` itself, whose obligations are admitted (such as `NoAnyExternals.bt_declarations_accepted`), and, on `ccs-backtranslation`, the ones relying on `Selectionproof.transf_program_match`.
