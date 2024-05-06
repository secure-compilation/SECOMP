#include <stdio.h>

§C1§ exports init
§C1§ exports process

§C1§ int initialized = 0;

§C1§ int init() { return initialized = 1; }

§C1§ int prepare() { return 77 / initialized; }

§C1§ int handle(int y) { return (y + 1) / y; }

§C1§ int process(int y) { 
  prepare();
  return handle(y);
}

/* §C0§ imports_syscall [printf] */
/* §C0§ imports_syscall [fgets] */
§C0§ imports §C1§[init]
§C0§ imports §C1§[process]

§C0§ char x[10];

§C0§ int valid(int data) { return data % 2; }

§C0§ int parse(char* x) { return 42; }

§C0§ int main() {
  init();
  if (fgets(x,100,stdin) != NULL) {
    int y = parse(x); /* <- should be atoi(x) instead (drop parse) */
    int data = process(y);
    if (valid(data)) { printf("%d,%s\n",data,x); }
    else { printf("invalid data\n"); }
  }
  return 0;
}
