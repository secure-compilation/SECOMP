#include <stdio.h>

/* environment */

§E§ » read
§E§ » write

§E§ int read() {
  return 0;
}

§E§ int write(int data, int x) {
  return 0;
}

/* component C0 */

§C0§ » valid

§C0§ int valid(int data) {
  return 0;
}

/* component C1 */

§C1§ « §E§[read]
§C1§ « §C2§[init]
§C1§ « §C2§[process]

§C1§ int main() {
  int x, y;
  init();
  x = read();
  y = parse(x);
  process(x, y);
  return 0;
}

// can yield Undef for some x
§C1§ int parse(int x) {
  return 0;
}

/* component C2 */

§C2§ « §E§[write]
§C2§ « §C0§[valid]
§C2§ » init
§C2§ » process

§C2§ int init() {
  return 0;
}

§C2§ int process(int x, int y) {
  int data;
  prepare();
  data = handle(y);
  if (valid(data)) {
    write(data, x);
  }
  return 0;
}

// can yield Undef if not initialized
§C2§ int prepare() {
  return 0;
}

// can yield Undef for some y
§C2§ int handle(int y) {
  return 0;
}
