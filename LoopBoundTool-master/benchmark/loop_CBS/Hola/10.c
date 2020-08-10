extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main() {
int j=0;
  int i;
  int x=100;
   
   
  for (i =0; i< x ; i++){
    j = j + 2;
  }

__VERIFIER_assert(j == 2*x);
}