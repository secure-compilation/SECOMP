#include <stdio.h>
/* An external with 15 integer parameters: more than the 8 argument
   registers, so some arguments are passed on the stack, and more than the 14
   integer registers that the register allocator can assign to the arguments
   of a builtin, should such calls ever be generated as builtins. */
§comp_main§ imports_syscall ext15
extern int ext15(int, int, int, int, int, int, int, int, int, int, int, int, int, int, int);
§comp_main§ int main() { return ext15(0,1,2,3,4,5,6,7,8,9,10,11,12,13,14); }
