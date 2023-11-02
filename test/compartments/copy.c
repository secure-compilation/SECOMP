#include <stdio.h>

§comp_main§ char c[10];

§comp_main§ int main()
{
  char *p  = fgets(c,10,stdin);
  printf("%s",p);
  return 0;
}

