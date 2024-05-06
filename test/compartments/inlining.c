#include <stdio.h>

§comp_add§ int add(int x, int y) {
  return x + y;
}

§comp_add§ » add

§comp_main§ « §comp_add§[add]

§comp_main§ int main() {
  printf("%d", add(3,3));
  return 0;
}
