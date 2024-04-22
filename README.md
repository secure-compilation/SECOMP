## Overview

This repository contains the SECOMP formally secure compiler.

## Requirements

This development is built and tested with Coq 8.15.2. It is based on the 64-bit
RISC-V backend of CompCert 3.12.

General requirements:
 - OCaml version 4.5.0 or greater (OCaml 5 is not supported).
   + systematic testing needs OCaml version 4.14.0 or later (see below)
 - Coq version 8.15.2 (OPAM package: `coq`)
 - Menhir version 20190626 or greater (OPAM package: `menhir`).

Extended requirements for systematic testing:
 - OCaml version 4.14.0 or later.
 - QCheck (OPAM package: `qcheck`).
 - MenhirLib (OPAM package: `menhirLib`).

Here are the OPAM commands one can use to install all OCaml dependencies above:

    $ opam switch create 4.14.0
    $ eval $(opam env --switch=4.14.0)
    $ opam install coq.8.15.2 menhir qcheck menhirLib

In addition to the above, some of the toolchain relies on the riscv64
architecture version of the GCC compiler, available for example from the
`gcc-riscv64-linux-gnu` package on Debian-based systems.

System requirements can be verified through CompCert's `configure` script
(see Building below).

## Structure

The development is currently split into four branches, which we are working on
merging into a single release:
 - `ccs-submission`: compiler correctness proof and testing infrastructure (main)
 - `backtranslation`: proof of back-translation
 - `recomp-ccs`: proof of recomposition
 - `secure-compilation`: proof of blame

## Building

Each branch can be built after installing its dependencies by configuring the
CompCert build process, e.g., by going to that folder and running:

    $ ./configure -toolprefix "riscv64-linux-gnu-" rv64-linux

where `riscv64-linux–gnu-` stands for the prefix used by the local RISC-V
compilation chain. Installing and using a RISC-V compiler is only necessary
for running the tests and examples in the `ccs-submission` branch.

One can then compile CompCert and check the proofs on that branch by running
`make`, optionally with the `-j` command line option, where an optional
argument number `N` can limit the number of simultaneous jobs:

    $ make -jN

After building once, or after running `make depend`, the alternative command
`make proof` can be used to only check the proofs.

## Main branch: `ccs-submission`

This branch contains the extension of CompCert to compartments, which involved
updating the languages, passes, and correctness proofs. This extension can be
built into a compiler binary that can be used to compile compartmentalized C
programs that can be executed. It also includes the systematic testing
infrastructure employed to validate the assumptions and expected behavior of the
back-translation function.

The updated correctness proof is complete and can be
found in file `driver/Compiler.v`, theorems
`transf_c_program_correct` and `separate_transf_c_program_correct`, and only
depends on CompCert's existing axioms, or small adaptions thereof to account for
the addition of compartments to the compiler.
To verify this, uncomment and execute `Print Assumptions transf_c_program_correct` and
`Print Assumptions separate_transf_c_program_correct`. This will load and print the list
of axiomatised results used in the proofs.

The following files include the most interesting changes:
 - Compartment model: file `common/AST.v`, modules `COMPTYPE` and `COMP`.
 - The notion of interface can be found in `common/Globalenvs.v` and is named
 `Policy`. The same file describes how we check for allowed calls.
 - Events: file `common/Events.v`, inductive `event`. The same file contains
 the buffer-based IO development and the detailed models for the `read` and
 `write` system calls.

### Examples

Compartmentalized program examples can be found under `test/compartments`. You can inspect
the source code of the examples by opening the C files, and test the functionality of the compiler by using
`../../ccomp file.c -o file`.

To run the compiled files, we suggest using [Fabrice Bellard's
TinyEmu](https://bellard.org/tinyemu/), which is included in the virtual image.

On the virtual image, you can use the following to run compiled programs:

Start the emulator with `temu root_9p-riscv64.cfg` then `mount -t 9p /dev/root /mnt`
in the guest to be able to access the content of the folder `/tmp` on the host.

Then, compile a file and copy it to the `/tmp` directory:
```
../../ccomp -L../../runtime test/c/fib.c -v -static
cp a.out /tmp/a.out
```

Then, on the guest, run `/mnt/a.out`.

We statically link the libraries to avoid issues arising from version
discrepancies between the system's libc and the emulator's libc.

### Testing the compilation of the back-translation

The property-based testing infrastructure for Assumption 1 can be found under
`test/backtranslation`. After compiling CompCert, from this folder, run:

    $ touch .depend
    $ make clean
    $ make depend
    $ make test_backtranslation

Running the `test_backtranslation` binary performs the testing:

    $ ./test_backtranslation

A few more details are provided in `test/backtranslation/README.md`.

### Claims

| Claim | File | Location in file | Notes |
| --- | --- | --- | --- |
| Compartment model | common/AST.v | Module COMP |  |
| Compartments | common/AST.v | Definition compartment |  |
| Interfaces | common/AST.v | Module Policy |  |
| Programs | common/AST.v | Record program | Standard CompCert definition with the addition of a Policy.t(interface) component, properties related to well-formedness of this component |
| Assignment of compartment to definitions and objects | common/AST.v | Typeclass has_comp | This is defined as a typeclass because the type of functions varies. |
| Interface checks: definition of allowed cross-compartment calls | common/Globalenvs.v | Definition allowed_cross_call |  |
| Interface checks: allowed calls | common/Globalenvs.v | Definition allowed_call | Builds on top of the previous definition to allow for intra-compartment calls  |
| Interface checks: preservation by compilation of allowed calls | common/Globalenvs.v | Theorems match_genvs_allowed_calls, allowed_call_transf_partial, allowed_call_transf |  |
| Trace events | common/Events.v | Definition event |  |
| Properties of system calls | common/Events.v | Record extcall_properties |  |
| Generation of the new trace events | common/Events.v | Definitions call_trace and return_trace |  |
| Memory containing compartment information | common/Memory.v | Record mem' and in particular field mem_compartments |  |
| Memory operations require compartment permissions | common/Memory.v | Definition valid_access  | Given by the conjunct can_access_block m b cp meaning that cp can access the block b in memory m |

Checking changes to CompCert’s languages:
all the languages are changed in similar ways. As such, we describe the location of the changes on the Cminor language, and invite the reviewers to check the other languages if they wish to do so.

| Claim | File | Location in file | Notes |
| --- | --- | --- | --- |
| Interface checks at the point of calls and returns | backend/Cminor.v | In step, conditions (ALLOWED: Genv.allowed_call ge (comp_of f) vf) for calls. | There is no check for allowed returns in most languages, including Cminor. |
| Cross-compartment calls and returns don’t pass pointers | backend/Cminor.v | In step, conditions (NO_CROSS_PTR: Genv.type_of_call (comp_of f) (comp_of fd) = Genv.CrossCompartmentCall -> Forall not_ptr vargs) and (NO_CROSS_PTR: Genv.type_of_call (comp_of f) cp = Genv.CrossCompartmentCall -> not_ptr v) |  |
| Generation of events | backend/Cminor.v | In step, condition (EV: call_trace ge (comp_of f) (comp_of fd) vf vargs (sig_args sig) t) and (EV: return_trace ge (comp_of f) cp v ty t) |  |
| Correctness of the pass from Csharpminor to Cminor | cfrontend/Cminorgenproof.v | Entire file. The most important theorem is the theorem transl_step_correct |  |

Language-specific claims:
| Claim | File | Location in file | Notes |
| --- | --- | --- | --- |
| Cross-compartment inlining disabled | backend/Inlining.v | Definition can_inline | This comes from the check cp_eq_dec cp (comp_of f) |
| Cross-compartment tailcall optimization disabled | backend/Tailcall.v | Definition transf_instr | The Itailcall instruction is only generated when the condition intra_compartment_call holds. |
| Cross-compartment tailcalls disabled | All languages definition | Semantics of the languages | When a tailcall instruction exists, then the semantics prevent it from being executed cross-compartment by having a condition (COMP: comp_of fd = comp_of f)  |




## Back-translation branch: `backtranslation`

This branch contains the back-translation proof. Use `make proof` to replay the proof.

The proof is complete. This proof is done in a slightly more complex setting
where system calls can belong to particular compartments. Also some recent
changes to the mainline `ccs-submission` branch are in the process of being
integrated.

The memory deltas are defined in the file `security/MemoryDelta.v`.

The informative events (called `bundled_events`), and the intermediate language
characterizing the well-formedness of informative traces (`ir_step`) are defined
in `security/BtAsm.v`. The proof going from RISC-V assembly to the intermediate
language is called `asm_to_ir`.

The `security/Backtranslation.v` contains the implementation of the
back-translation function, `gen_program`.

The `security/BacktranslationProof.v` contains the proof of correctness of the
back-translation, starting from the intermediate language: `ir_to_clight`.

The `security/BacktranslationProof2.v` contains the complete proof from assembly
to Clight: `backtranslation_proof`.

## Recomposition branch: `recomp-ccs`

This branch contains the recomposition proof. Use `make proof` to replay the proof.

The proof is complete and most of the main correctness branch has been
merged. Compared to the main correctness branch, this branch contains fixes to
the way programs access arguments stored on the stack. The recomposition proof
is modified to account for these changes.

File `common/Smallstep.v` contains the definition of the three-way simulation
relation (`tsim_properties`), and the proof that it implies preservation
of finite prefixes (`tsimulation_star`). The same file also contains the
simulation diagrams depicted in Section 6 (`Section THREEWAY_SIMU_DIAGRAM`).

File `security/Recomposition.v` contains the proof of recomposition: lemma
`simulation`, as well as the three cores lemmas used to instantiate the diagrams:
`step_E0_strong`, `step_E0_weak`, and `step_t`.  The simulation invariants can
be found at `strong_equivalence`, `weak_equivalence`, `stack_rel`.

There are some low-level lemmas admitted, that we are in the process of fixing:
- `set_perm_preserves_rel` states that a new `set_perm` operation, that we use
  in the enforcement mechanism to protect the stack, respects the invariants.
- `eval_builtin_arg_inject` is used to prove the preservation of the arguments
  to system calls. The similar result `extcall_arguments_preserved` is fully proved.
- `step_t` contains some admits that are the symmetric cases of other proved goals.

## Blame branch: `secure-compilation`

This branch contains the blame proof. Use `make proof` to replay the proof.

The proof is complete. Some recent changes to the mainline `ccs-submission`
branch are in the process of being integrated.

The main blame theorem can be found in file `security/Blame.v`, theorem
`does_prefix_star`.

Definition 6 (Blame) can be found in file `security/Blame.v`, theorem
`blame_program`.

- This follows directly from `does_prefix_star` and uses a simple technical
  lemma that is to be proved after integration on the mainline `ccs-submission`
  branch.

- Theorem `blame` is a simple corollary that matches the one used in the
  top-level security proof.

Full program run lemmas: file `security/Blame.v`, theorems `parallel_exec` and
`parallel_exec'`.

Synchronized execution lemmas: file `security/Blame.v`, theorems `parallel_star_E0`
and `parallel_exec1`.

Stepwise lemmas: file `security/Blame.v`, theorems `parallel_concrete` and
`parallel_abstract_t`.

### Capability backend

Our prototype implementation of the capability-based backend and secure calling
convention is found under `cheririscV/`.

Simple compilation examples are in file `cheririscV/CapAsmgen.v`, section
`Examples`.

The compiler binary is instrumented to produce capability assembly in addition
to regular compartmentalized CompCert assembly.

