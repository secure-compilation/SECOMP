#include <stdio.h>

§C2§ » init
§C2§ int init() { return 0; }

§C1§ » parse
§C1§ int parse(char x) { return x; }

§C2§ » process
§C2§ int process(int y) { return y; }

§C0§ « §C2§[init]
§C0§ « §C1§[parse]
§C0§ « §C2§[process]

§C0§ char x[100];

§C0§ int valid(int data) { return 1; }

§C0§ int main() {
  init();
  if (fgets(x,100,stdin) != NULL) {
    int y = parse(x[0]); /* can only pass single char here */
    int data = process(y);
    if (valid(data)) {
      printf("<%d,%s>\n",data,x);
    }
  }
  return 0;
}
