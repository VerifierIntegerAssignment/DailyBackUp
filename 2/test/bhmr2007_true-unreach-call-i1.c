#include<stdlib.h>
void __VERIFIER_error() { abort(); }
void __VERIFIER_assume(int expression) { if (!expression) { LOOP: goto LOOP; }; return; }
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
      ERROR: __VERIFIER_error();
  }
  return;
}
int __VERIFIER_nondet_int() { int val; return val; }

int test() {
    int i, n, a, b;
    i = 0; a = 0; b = 0; n = __VERIFIER_nondet_int();
    __VERIFIER_assume(n >= 0 && n <= 1000000);
    return 0;
}
