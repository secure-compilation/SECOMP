## Overview

This branch contains the proof of back-translation for the SECOMP compiler.

## Requirements

This development is built and tested with Coq 8.15.2. It is based on the 64-bit
RISC-V backend of CompCert 3.12.

General requirements:

 - OCaml version 4.5.0 or greater (OCaml 5 is not supported).

 - Coq version 8.15.2 (OPAM package: `coq`)

 - Menhir version 20190626 or greater (OPAM package: `menhir`).

System requirements can be verified through CompCert's `configure` script
(see below).

## Building

This branch can be built after installing its dependencies by configuring the
CompCert build process first, by running:
```
./configure rv64-linux
```

Then, one can then compile the project by running `make` (optionally with the `-j` command line argument).

## Proof of back-translation

The proof of back-translation is complete. This proof is done in a slightly more complex setting
where system calls can belong to particular compartments.

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