#include <stdio.h>

§comp_copy§ imports_syscall fgets
§comp_copy§ imports_syscall printf

§comp_copy§ exports copy

§comp_copy§ char c[10];

§comp_copy§ int copy()    // making this void leads to UB
{
  char *p  = fgets(c,10,stdin);
  printf("%s",p);
  return 0;
}

§comp_main§ imports §comp_copy§[copy]

// §comp_main§ int main(int argc, char ** argv)
§comp_main§ int main()
{
  copy();
  return 0;
}
