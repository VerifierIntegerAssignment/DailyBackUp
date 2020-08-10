
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main() {

 int i, n, a, b;
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume( n >= 0 );

  i = 0; a = 0; b = 0;
  while( i < n ) {
    if(__VERIFIER_nondet_int()) {
      a = a+1;
      b = b+2;
    } else {
      a = a+2;
      b = b+1;
    }
    i = i+1;
  }
__VERIFIER_assert( a+b == 3*n );

}
