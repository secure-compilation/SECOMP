## Overview

This artifact contains the SECOMP formally secure compiler and its
machine-checked security proofs in Coq, both of which are based on the CompCert
formally verified C compiler. The Coq development contains the proofs, theorems,
and testing described in the paper, split into sub-folders that can be compiled
and checked independently from the others.

This README file contains detailed instructions on how to build, run and check
the development. These can be done on most modern hardware, and depend only on
OCaml, Coq, and some libraries that are available via the OCaml package manager
OPAM. Additionally, some tests rely on the GCC RISC-V cross-compiler.

Beyond the SECOMP sources, we also provide a virtual machine (VM) that has all
these dependencies already installed. The `sudo` password of the VM is `secomp`.

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

The development is currently split into six branches, which we are working on
merging into a single release:
 - `ccs-submission`: compiler correctness proof and testing infrastructure (main)
   + A modified version of the compiler with support for generation of
     CHERI RISC-V code is available on the branch `secure-compilation-captest`
 - `ccs-backtranslation`: proof of back-translation
   + A modified version of the compiler with support for systematic testing of
     the compilation of the back-translation (Assumption 1) is available on
     the branch `cross-external-call-removal-test-backtranslation`
 - `ccs-recomposition`: proof of recomposition
 - `secure-compilation`: proof of blame

## Building

Each branch can be built after installing its dependencies by configuring the
CompCert build process, by going to that folder and running:

    $ ./configure -toolprefix "riscv64-linux-gnu-" rv64-linux

where `riscv64-linux–gnu-` stands for the prefix used by the local GCC RISC-V
compilation chain.

One can then compile CompCert and check the proofs on that branch by running
`make`, optionally with the `-j` command line option, where an optional
argument number `N` can limit the number of simultaneous jobs:

    $ make -jN

After building once, or after running `make depend`, the alternative command
`make proof` can be used to only check the proofs.

Installing the GCC RISC-V compiler is not strictly necessary to build CompCert
and run `make proof`, for which the simpler `./configure rv64-linux` command is
enough. But this will result in errors if running `make` as CompCert won't be
able to compile its runtime, resulting in errors resembling:

    error: unsupported argument 'rv64imafd' to option '-march='

Installing and using the GCC RISC-V compiler is necessary in order to compile
the tests and examples in the `ccs-submission` branch (see Examples below).

## How one can inspect the Coq theorems and proofs

For those using the provided virtual machine, we recommend using the built-in
CoqIDE environment to explore the Coq development. Users of the virtual machine
can install other editors, like Proof General, if they prefer.

To start CoqIDE, simply run the `coqide` command and navigate to the files you
wish to inspect. The simplest way to evaluate a file is by using the buttons
"Run to end" and "Run to cursor". Keyboard shortcuts for those commands can be
found on the Navigation menu.

To inspect a particular theorem, locate that theorem, and process the file up to
the start of the theorem. Then, you may step through the proof one step
at a time using the button "Forward one step". The state of the proof (with
goals and assumptions) is displayed in one of the side window. Messages are
displayed in the other side window.

A proved theorem ends with `Qed.`. When running `Qed`, the interactive prover will check
the validity of the proof; if the command succeeds, then the proof is accepted by Coq.
After a theorem is proved, you can use the following command (write it inside
the file and then "Forward one step"): `Print Assumptions theorem.` to display all the
assumptions and axioms `theorem` depends on.

At any point, you can use the commands on the Query menu to Print the definition
of and identifier and Check the type of an identifier, among others.

The file `table.html` contains a mapping from claims from the paper to definitions and proofs.

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
of axiomatized results used in the proofs.

The following files include the most interesting changes:
 - Compartment model: file `common/AST.v`, modules `COMPTYPE` and `COMP`.
 - The notion of interface can be found in `common/Globalenvs.v` and is named
 `Policy`. The same file describes how we check for allowed calls.
 - Events: file `common/Events.v`, inductive `event`. The same file contains
 the buffer-based IO development and the detailed models for the `read` and
 `write` system calls.

### Examples

Compartmentalized program examples can be found under `test/compartments` and
can be run in a custom version of the CompCert source-level interpreter, which
we extended to support compartments, for instance by running:

    [compartments]$ ../../ccomp -interp ccs2.c

These programs can be compiled by running `make` in `test/compartments`:

    [compartments]$ make

You can inspect the examples' source code by opening the C files like `ccs1.c`,
and can test the functioning of the compiler on such individual files using:

    [compartments]$ make ccs1.s

Then, you can inspect the content of the generated assembly in `ccs1.s`.

### Running compartment-stripped binaries in vanilla RISC-V emulator

The binaries above are generated by SECOMP using CompCert's standard RISC-V
backend, which means that the binaries are stripped from the compartment
information and one should be able to run them on a standard RISC-V machine.

If you wish to also run the compiled binaries, we suggest using [Fabrice Bellard's
TinyEmu](https://bellard.org/tinyemu/), which is included in the virtual image.

On the virtual image, you can use the following to run compiled programs:

Start the emulator with `temu root_9p-riscv64.cfg` then `mount -t 9p /dev/root /mnt`
in the guest to be able to access the content of the folder `/tmp` on the host.

Then, compile a file and copy it to the `/tmp` directory:

    [compartments]$ ../../ccomp -L../../runtime test/c/fib.c -v -static
    [compartments]$ cp a.out /tmp/a.out

Then, on the guest, run `/mnt/a.out`.

Above, we statically link the libraries to avoid issues arising from version
discrepancies between the system's libc and the emulator's libc.

### Compiling compartmentalized programs with the capabilities backend

For this part, build the modified compiler available under branch
`secure-compilation-captest` following the general invocations of `configure`
and `make`. One does not need to worry about linking, as only the compilation
procedure is needed for this part.

To compile a compartmentalized program, invoke CompCert as follows, for example
for the compartmentalized addition example available at
`test/compartments/add.c`, from the `test/compartments` folder:

    [compartments]$ ../../ccomp -c add.c

The compiler automatically produces an additional file, `out.cap_asm`, with the
capability assembly code for the given program.

Note that not all instructions are fully supported by the pretty-printer at the
moment, and programs with unsupported instructions will emit invalid
placeholders including the special placeholder `__Inst_Name__` in them.

Our prototype implementation of the capability-based backend and secure calling
convention is found under `cheririscV/`.

Simple compilation examples (in Coq) are in file `cheririscV/CapAsmgen.v`, section
`Examples`.

The compiler binary is instrumented to produce capability assembly in addition
to regular compartmentalized CompCert assembly, as described above.

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

### Systematic testing the compilation of the back-translation (Assumption 1)

For this part, build the modified compiler available under branch
`cross-external-call-removal-test-backtranslation` following the general
invocations of `configure` and `make`. One does not need to worry about linking,
as only the compilation procedure is needed for this part.

The property-based testing infrastructure for Assumption 1 can be found under
`test/backtranslation`. After compiling CompCert, from this folder, run:

    [backtranslation]$ touch .depend
    [backtranslation]$ make clean
    [backtranslation]$ make depend
    [backtranslation]$ make test_backtranslation

Running the `test_backtranslation` binary performs the testing:

    [backtranslation]$ ./test_backtranslation

More in detail, you can run the tests in two modes: *test mode* and
*reproduction mode*. The test mode is the default mode and designed to run
tests. In case of any failures, all intermediate seeds are printed, otherwise a
statistic of the generated values is shown. Note that the number of tests grows
**multiplicatively** so choose the parameters accordingly. In reproduction mode
the specified seeds allow you to reproduce a very specific run.  The commands
below exemplarily show how to run the tests in test- and reproduction mode
respectively.

    [backtranslation]$ ./test_backtranslation -num_asm_progs 5 -num_traces 20
    [backtranslation]$ ./test_backtranslation -root_seed 4 -asm_seed 3 -trace_seed 8

A few more details are provided in `test/backtranslation/README.md`.

If one is interested in reproduction, we have run our tests using QCheck 0.21.3.

## Recomposition branch: `ccs-recomposition`

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
