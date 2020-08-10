extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main(void) {
int k = 100;
  int b;
  int i;
  int j;
  int n;
  j = __VERIFIER_nondet_int();
  b = __VERIFIER_nondet_int();
  i = j;
  for( n = 0 ; n < 2*k ; n++ ) {
    if(b>0) {
      i++;
    } else {
      j++;
    }
    b = !b;
  }
__VERIFIER_assert(i == j);
}
