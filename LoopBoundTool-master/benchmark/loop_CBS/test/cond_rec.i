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
    int a;
    int b;
    int c;
      while (x<c) {
        if (x < a) { x=x+1;}
	else if (x < b) {x=x+2;}
	else {x=x+3;}
     }
     __VERIFIER_assert(1==1);
      
}
