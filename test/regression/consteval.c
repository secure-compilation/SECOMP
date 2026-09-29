#include <stdio.h>

/* Constant evaluation in cparser/Ceval */

/* Issue #566 */
int f(int x)
{
  switch (x) {
  case ~(unsigned short)0:
    return 0;
  default:
    return 1;
  }
}

/* Issue #565 */
int g(int x)
{
  switch (x % 7u) {
    case -1 % 7u:
      return 0;
    default:
      return 1;
  }
}

volatile int zero = 0;
volatile int one = 1;

int main()
{
  printf("f(~(unsigned short)0) = %d\n", f(~(unsigned short) zero));
  printf("f(0) = %d\n", f(zero));
  printf("f(1) = %d\n", f(one));
  printf("g(-1) = %d\n", g(- one));
  printf("g(0) = %d\n", g(zero));
  printf("g(1) = %d\n", g(one));
}

