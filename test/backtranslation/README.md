# Running the backtranslation tests

### 1) Rebuilding CompCert
Change into the root directory of this repo and rebuild the `ccomp` executable with the following commands.
```
$ ./configure -toolprefix "riscv64-linux-gnu-" rv64-linux
$ make -kj
```
More information can be found in `testing.md` in the root directory. You do not need to install `ccomp` globally
or worry to much about linking, as we only need to compilation procedure.

### 2) Install QCheck
We use the `QCheck` library ([Github](https://github.com/c-cube/qcheck)) for property based testing.
You can install it with [opam](https://opam.ocaml.org/) using the command below (we have run our tests with
version `0.21.3`).
```
$ opam install qcheck
```

### 3) Build the test executable
First, change back into the directory with the test code. Then, create an empty `.depend` file
(otherwise `make` will complain). You can then build the test executable with `make` as shown in the following
commands.
```
$ cd ./test/backtranslation
$ touch .depend
$ make depend
$ make test_backtranslation
```

### 4) Run the tests
You can run the tests in two modes: *test mode* and *reproduction mode*. The test mode is the default mode
and designed to run tests. In case of any failures, all intermediate seeds are printed, otherwise a statistic
of the generated values is shown. Note that the number of tests grows **multiplicatively** so choose
the parameters accordingly. In reproduction mode the specified seeds allow you to reproduce a very specific run.
The commands below exemplarily show how to run the tests in test- and reproduction mode respectively.
```
$ ./test_backtranslation -num_asm_progs 5 -num_traces 20
$ ./test_backtranslation -root_seed 4 -asm_seed 3 -trace_seed 8
```

### 5) Check that the output of the back-translation compiles
Assumption 1 requires the output of the back-translation to be accepted by the compiler (see issue #13).
The regression test `test_compiles` checks this for synthetic Asm programs with external declarations, retained
stores of every chunk and kind of value, and builtins, and for the C programs in `test/compartments` and
`test/backtranslation/programs`, each with an empty and a synthetic trace. Unlike `test_backtranslation`, which
prints the generated program as C and recompiles the text with `ccomp`, it compiles the generated Clight program
itself. Besides compilation, it checks which stores are replayed and the types at call sites, but not what the
generated code computes. It does not need QCheck. After step 1, run:
```
$ cd ./test/backtranslation
$ touch .depend
$ make depend
$ make run_test_compiles
```
Run `make depend` again if your `.depend` predates `test_compiles.ml`. The C programs are preprocessed as `ccomp`
does, with the RISC-V toolchain configured in step 1: `make run_test_compiles` sets `COMPCERT_CONFIG` to
`../../compcert.ini`. The test prints every failing check, and fails if any check fails.
