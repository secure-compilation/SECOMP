#include <stdio.h>

§comp_main§ imports_syscall fgets
§comp_main§ imports_syscall printf

§comp_main§ char c[10];

§comp_main§ int main()
{
  char *p  = fgets(c,10,NULL);
  printf("%s",p);
  return 0;
}
