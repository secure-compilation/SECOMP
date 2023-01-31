#include <stdio.h>

/* Static initialization of bit-fields */

struct s {
  signed char a: 6;
  unsigned int b: 2;
};

struct t {
  unsigned int c: 16;
  _Bool d: 1;
  short e: 8;
  int : 10;
};

union u {
  int u: 4;
  unsigned int v: 3;
};

void print_s(char * msg, struct s p)
{
  printf("%s = { a = %d, b = %d }\n", msg, p.a, p.b);
}

void print_t(char * msg, struct t p)
{
  printf("%s = { c = %d, d = %d, e = %d }\n", msg, p.c, p.d, p.e);
}

void print_u_u(char * msg, union u p)
{
  printf("%s = { u = %d }\n", msg, p.u);
}

void print_u_v(char * msg, union u p)
{
  printf("%s = { v = %u }\n", msg, p.v);
}

/* Global initialization */
struct s glob_s = { -12, 1 };
struct t glob_t = { 123, 2, -45 };
union u glob_u_u = { -3 };
union u glob_u_v = { .v = 6 };

/* Local, static initialization */
void f(void)
{
  static struct s loc_s = { -12, 1 };
  static struct t loc_t = { 123, 2, -45 };
  static union u loc_u_u = { -3 };
  static union u loc_u_v = { .v = 6 };
  print_s("loc_s", loc_s);
  print_t("loc_t", loc_t);
  print_u_u("loc_u_u", loc_u_u);
  print_u_v("loc_u_v", loc_u_v);
}

int main()
{
  print_s("glob_s", glob_s);
  print_t("glob_t", glob_t);
  print_u_u("glob_u_u", glob_u_u);
  print_u_v("glob_u_v", glob_u_v);
  f();
  return 0;
}

