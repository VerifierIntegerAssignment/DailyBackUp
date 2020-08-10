extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main() {
  int n = __VERIFIER_nondet_int();
    int m = __VERIFIER_nondet_int();
  __VERIFIER_assume(n>=0);
  __VERIFIER_assume(m>=0);
  __VERIFIER_assume(m<n);
  int x=0; 
  int y=m;
  while(x<n) {
    x++;
    if(x>m) y++;
  }
__VERIFIER_assert(y==n);
}
