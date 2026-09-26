#include <stdio.h>
/* An external with signed char, unsigned short and _Bool parameters and a
   signed char result. */
§comp_main§ imports_syscall putsmall
extern signed char putsmall(signed char, unsigned short, _Bool);
§comp_main§ int main() { return putsmall(1, 2, 1); }
