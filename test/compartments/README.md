# Generating CapASM code from C

### 1) Rebuild the `ccomp` executable
Run the commands below from the root directory of this project. You can refer to
`testing.md` for more information if necessary.
```
$ ./configure -toolprefix "riscv64-linux-gnu-" rv64-linux
$ make -kj
```
You do not need to install `ccomp` globally or worry to much about linking, as
we only need to compilation procedure.

### 2) Compile a compartmentalized program (`add.c`) with CompCert
```
$ ccomp -c ./test/compartments/add.c
```
The compiler automatically produces an additional `out.cap_asm` file with the
capability assembly code for the given program.

Note that not all instructions are fully supported yet. If you see `"TODO: __Inst_Name__"`
then the pretty-printer does not support this instruction yet. Also, not all instructions
are supported internally.
