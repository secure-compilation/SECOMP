#include <stdio.h>

int $1[2];
int $2;

void $3(void)
{
  $1[0] = 12;
  $1[1] = 34;
}

int $4(void)
{
  return $1[0] * $1[1];
}

int * $5(void)
{
  return &$2;
}

int main()
{
  $3();
  printf("%d\n", $4());
  *($5()) = 67;
  printf("%d\n", $2);
}
