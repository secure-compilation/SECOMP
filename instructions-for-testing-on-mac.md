# Installing a RISC-V cross-compiler for CompCert on an M1 Mac

## Building and installing the **RISC-V GNU Compiler Toolchain**

[https://github.com/riscv-collab/riscv-gnu-toolchain](https://github.com/riscv-collab/riscv-gnu-toolchain)

Installing this toolchain is a bit tricky on MacOS, for several reasons. First, to build the linux version of the cross-compiler and glibc, we need to create a case-sensitive volume and use it temporarily. Then, MacOS comes by default with outdated versions of `bison` and `gnumake`. We will need to install the new version using `homebrew`.

### Creating a case-sensitive volume

Use `cmd+space` to open Spotlight search, and launch the Disk Utility app. Go to `File > New Image > Blank Image` and create a new volume of sufficient size (I chose 20 GB and it was enough — the README mentions the compilation process taking around 6.5 GB). We will remove the volume after installation.

Clone the `riscv-gnu-toolchain` repo inside that volume (it’s a folder inside `/Volumes/`).

### Installing up-to-date versions of bison and gnumake and configuring the environment

Use `homebrew` to install newer versions of `bison` and `gnumake`:

```bash
brew install bison
brew install make
```

Read the instructions carefully, and add the following to your `$PATH`:

```bash
export PATH="$(brew --prefix bison)/bin:/opt/homebrew/opt/make/libexec/gnubin:$PATH"
```

I added that line to my `.zshrc`, but it might be enough to just run it in your current shell.

Then, go to the `/opt/homebrew/opt/make/libexec/gnubin` folder and create a symlink so that the command `gnumake` points to the right version:

```bash
ln -s make gnumake
```

Increase the maximum number of file descriptors per process: `ulimit -n 4096`. The default, 256, is way too low on MacOS.

### Building the compilation chain and installing it

We can now configure the project, build it, and install it. First, create a new folder to install the compilation chain: `sudo mkdir /opt/riscv` and make it writable: `sudo chmod a+w /opt/riscv`.

Then, configure the project:

```bash
./configure --prefix=/opt/riscv --with-arch=rv64imafd --disable-gdb
```

We disable GDB as we’re not going to use it, and specify the exact architecture that CompCert is targeting. We can now build the chain:

```bash
make linux
```

The chain will be installed in the `/opt/riscv` folder, and we can add this folder to the `$PATH` to get easier access to it.

## Install a RISC-V emulator (Spike)

We install Spike using the following homebrew tap:

[https://github.com/riscv-software-src/homebrew-riscv](https://github.com/riscv-software-src/homebrew-riscv)

```bash
brew tap riscv-software-src/riscv
```

However, do not install the full toolchain. Instead only install Spike and PK:

```bash
brew install riscv-isa-sim
brew install riscv-pk
```

All done for the emulator!

## Building and installing CompCert and testing it

### Building CompCert

Configure the project for the RISC-V backend and using the correct compilation chain, then build the project and install CompCert.

```bash
./configure -toolprefix riscv64-unknown-linux-gnu- rv64-linux
make
sudo make install
```

### Testing CompCert

Go to the `test` folder and build the tests.

```bash
cd test
make
```

If everything works as expected, there should be no error.

### Running tests in the emulator

Compile a program of your choice with:

```bash
ccomp -static prog.c -o prog
```

You must link statically or the emulator will not run the program. Then you can run the program with:

```bash
spike pk prog
```

## Cleaning up after installation

Go to `/opt/homebrew/opt/make/libexec/gnubin` and remove the symlink:

```bash
rm gnumake
```

Unmount the temporary volume in the Disk Utility app. The changes to the environment should only affect the current shell, if you didn’t modify your shell configuration file, so no need to undo them.

## Sources

[Running 64- and 32-bit RISC-V Linux on QEMU — RISC-V - Getting Started Guide](https://risc-v-getting-started-guide.readthedocs.io/en/latest/linux-qemu.html)

[Compile and install RISC-V cross-compiler · lowRISC](https://www.cl.cam.ac.uk/~jrrk2/docs/riscv_compile/)

[building Linux kernel on Mac OS X](https://stackoverflow.com/questions/10018764/building-linux-kernel-on-mac-os-x)