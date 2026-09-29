/* Issue #537, PR #538 */

#include <stdio.h>

int ungetc(int, FILE*);  // not extern!

int (*p)(int, FILE*);

int main()
{
  p = ungetc;
  printf("OK\n");
}


  
