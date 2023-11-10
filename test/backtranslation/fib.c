// #include <stdio.h>

// §comp_fib§ » fib

// static §comp_fib§ int fib(int n) {
//   if (n < 2) {
//     return 1;
//   } else {
//     return fib(n-1) + fib(n-2);
//   }
// }

// §comp_main§ « §comp_fib§[fib]

// §comp_main§ int main(void) {
//   int n = 10;
//   int r = fib(n);
//   printf("fib(%d) = %d\n", n, r);
//   return 0;
//   // return r;
// }

static int fib(int n) {
  if (n < 2) {
    return 1;
  } else {
    return fib(n-1) + fib(n-2);
  }
}

int main(void) {
  int n = 10;
  int r = fib(n);
  // return 0;
  return r;
}