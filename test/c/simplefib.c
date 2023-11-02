#include <stdlib.h>
#include <stdio.h>

int fib(int n)
{
  if (n < 2) 
    return 1;
  else
    return fib(n-1) + fib(n-2);
}

/* Modified main to avoid interpreter UB:
   - when using main()'s full interface
   - when using atoi() */
int main(/* int argc, char ** argv */)
{
  int n, r;
  /* if (argc >= 2) n = atoi(argv[1]); else */ n = 10;
  r = fib(n);
  printf("fib(%d) = %d\n", n, r);
  return 0;
}
