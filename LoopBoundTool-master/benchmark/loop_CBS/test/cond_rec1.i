extern void __VERIFIER_error() __attribute__ ((__noreturn__));

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int __VERIFIER_nondet_int();

void main() {

    int x=0;
    int A;
    int C;
    __VERIFIER_assume(A==3*C);
    while (x<C) {
        if (x == A) { x=x+1;}
	        else {x=x+3;}
     }
     __VERIFIER_assert(1==1);
}
