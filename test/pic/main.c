#include <stdio.h>
#include <dlfcn.h>

#include "lib1.h"
#include "lib2.h"

typedef int (*intfunc)(int);

int main()
{
  printf("x = %d\n", x);
  printf("y = %d\n", y);
  printf("f(8) = %d\n", f(8));
  printf("g(9) = %d\n", g(9));
  void * handle = dlopen("./dylib.so", RTLD_LAZY);
  if (handle == NULL) {
    printf("dlopen failure: %s\n", dlerror());
    return 2;
  }
  void * h = dlsym(handle, "h");
  if (h == NULL) {
    printf("h not found in dylib.so\n");
    return 2;
  }
  printf("h(10) = %d\n", ((intfunc) h)(10));
  dlclose(handle);
  return 0;
}
