# Testing CompCert+Compartments

## Install a cross-compiler and a RISC-V emulator

On Arch, I installed the content of the group
[`risc-v`](https://archlinux.org/groups/x86_64/risc-v/). It includes the
cross-compiler `riscv64-linux-gnu-gcc` and the emulator `tinyemu`.

For the emulator, I downloaded the image `RISC-V boot loader, Linux kernel and
filesystem with busybox (riscv32 and riscv64 targets):
diskimage-linux-riscv-2018-09-23.tar.gz.` from [Fabrice Bellard's
website](https://bellard.org/tinyemu/). I extracted it, and added the line
`kernel: "kernel-riscv64.bin",` to the file `root_9p-riscv64.cfg`.

Start the emulator with `temu root_9p-riscv64.cfg` then `mount -t 9p /dev/root /mnt`
in the guest to be able to access the content of the folder `/tmp` on the host.

## Install CompCert

Compile using
```
./configure -toolprefix "riscv64-linux-gnu-" rv64-linux
make -kj
```
Change the tool prefix if necessary.

I did `make install`, but I'm not sure if it's necessary.

## Compile and test a program

Compile a file and copy it to the `/tmp` directory:
```
ccomp test/c/fib.c -v -static
cp a.out /tmp/a.out
```

Then test on the guest, using `/mnt/a.out`.

We statically link the libraries to avoid issues arising from version
discrepancies between the system's libc and the emulator's libc.

