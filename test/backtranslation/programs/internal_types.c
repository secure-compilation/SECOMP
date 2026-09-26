#include <stdio.h>
/* Functions called across compartments with long, floating-point and
   small-integer parameters and results. */
§comp_a§ exports fl
§comp_a§ exports fd
§comp_a§ exports ff
§comp_a§ exports fsc
§comp_a§ exports fuc
§comp_a§ exports fs
§comp_a§ exports fus
§comp_a§ exports fb
§comp_a§ exports fv
§comp_a§ long g;
§comp_a§ long fl(long x) { return x + 1; }
§comp_a§ double fd(double x, float y) { return x + y; }
§comp_a§ float ff(float x) { return x; }
§comp_a§ signed char fsc(signed char x) { return x; }
§comp_a§ unsigned char fuc(unsigned char x) { return x; }
§comp_a§ short fs(short x) { return x; }
§comp_a§ unsigned short fus(unsigned short x) { return x; }
§comp_a§ _Bool fb(_Bool x) { return x; }
§comp_a§ void fv(long a, double b, float c) { g = a; }
§comp_main§ imports §comp_a§[fl]
§comp_main§ imports §comp_a§[fd]
§comp_main§ imports §comp_a§[ff]
§comp_main§ imports §comp_a§[fsc]
§comp_main§ imports §comp_a§[fuc]
§comp_main§ imports §comp_a§[fs]
§comp_main§ imports §comp_a§[fus]
§comp_main§ imports §comp_a§[fb]
§comp_main§ imports §comp_a§[fv]
§comp_main§ int main() {
  fv(fl(1), fd(2.0, 3.0f), ff(4.0f));
  return fsc(-1) + fuc(255) + fs(-2) + fus(65535) + fb(1);
}
