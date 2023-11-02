#include <stdio.h>

§comp_init§ » init

static §comp_init§ int ready = 0;

§comp_init§ int init() {
  int x;
  x = ready;
  ready = 1;
  return x;
}

§comp_main§ « §comp_init§[init]

§comp_main§ int main() {
  init();
  init();
  return 0;
}
