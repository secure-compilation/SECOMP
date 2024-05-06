#include <stdio.h>

§comp_fib§ exports fib

§comp_fib§ int fib(int n)
{
  if (n < 2) 
    return 1;
  else
    return fib(n-1) + fib(n-2);
}

§comp_main§ imports §comp_fib§[fib]

// XXX main() full interface and undefined behavior
// §comp_main§ int main(int argc, char ** argv)
§comp_main§ int main()
{
  int n, r;
  // XXX atoi() warning and undefined behavior
  // if (argc >= 2) n = atoi(argv[1]); else n = 35;
  n = 10;
  r = fib(n);
  printf("fib(%d) = %d\n", n, r);
  return 0;
}
