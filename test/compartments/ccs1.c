#include <stdio.h>

/* component C0 */

§C0§ » valid

§C0§ int valid(int data) {
  return data % 2;
}

/* component C2 */

/* §C2§ imports_syscall [printf] */
§C2§ « §C0§[valid]
§C2§ » init
§C2§ » process

§C2§ int initialized = 0;

§C2§ int init() {
  initialized = 1;
  return 0;
}

// can yield Undef if not initialized
§C2§ int prepare() {
  return 77 / initialized;
}

// can yield Undef for some y
§C2§ int handle(int y) {
  return (y + 1) / y;
}

§C2§ int process(int y) {
  int data;
  prepare();
  data = handle(y);
  if (valid(data)) { printf("%d,%d\n",data,y); }
  else { printf("invalid data\n"); }
  return 0;
}

/* component C1 */

/* §C1§ imports_syscall [fgets] */
§C1§ « §C2§[init]
§C1§ « §C2§[process]

// can yield Undef for some x
§C1§ int parse(char* x) {
  if (x[0]) return 42; /* <- should be atoi(x) */
  else return 0;
}

§C1§ char x[10];

§C1§ int main() {
  init();
  if (fgets(x,10,stdin) != NULL) {
    int y = parse(x);
    process(y);
    return 0;
  }
}
