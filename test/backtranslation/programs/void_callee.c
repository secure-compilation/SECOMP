#include <stdio.h>
/* A void function called across compartments.  In Asm its return still
   carries the integer register a0. */
§comp_a§ exports f
§comp_a§ int g;
§comp_a§ void f(int x) { g = x; }
§comp_main§ imports §comp_a§[f]
§comp_main§ int main() { f(3); return 0; }
