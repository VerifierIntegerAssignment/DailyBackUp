
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main() {
int i,k,n,l;

  l = __VERIFIER_nondet_int();
  __VERIFIER_assume(l>0);

  for (k=1;k<n;k++){
    for (i=l;i<n;i++) {
    }
    for (i=l;i<n;i++) {
	__VERIFIER_assert(1<=i);
    }
}}