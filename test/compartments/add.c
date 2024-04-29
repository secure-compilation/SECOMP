#include <stdio.h>

§comp_add§ » add

§comp_add§ int add(int x, int y) {
  return x + y;
}

§comp_main§ « §comp_add§[add]

§comp_main§ int main() {
  int x;
  x = add(3, 3);
  printf("%d", x);
  return 0;
}
