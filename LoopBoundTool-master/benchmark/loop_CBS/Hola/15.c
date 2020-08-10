extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main() {

  int n;
  int i, k, j;


  n = __VERIFIER_nondet_int();
  k = __VERIFIER_nondet_int();
  __VERIFIER_assume(n>0);

  __VERIFIER_assume(k>n);
  j = 0;
  while( j < n ) {
    j++;
    k--;
  } 
  __VERIFIER_assert(k>=0);
return 0;

}





