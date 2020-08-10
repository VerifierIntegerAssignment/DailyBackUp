extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}

int LARGE_INT;

int main() {

int i,pvlen ;
  int t;
  int k = 0;
  int n;
  i = 0;

  pvlen = __VERIFIER_nondet_int();

  while (i < LARGE_INT && __VERIFIER_nondet_int())
    i = i + 1;
  if (i > pvlen) {
    pvlen = i;
  } else {

  }
  i = 0;

  while (k < LARGE_INT && __VERIFIER_nondet_int()) {
    t = i;
    i = i + 1;
    k = k +1;
  }
  while (__VERIFIER_nondet_int());

  int j = 0;
  n = i;
  while (1) {
    __VERIFIER_assert(k >= 0);
    k = k -1;
    i = i - 1;
    j = j + 1;
    if (j < n) {
    } else {
      break;
    }
    }
return 0;
}