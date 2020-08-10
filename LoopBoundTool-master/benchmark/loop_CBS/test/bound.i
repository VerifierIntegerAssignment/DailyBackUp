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
    int y=0;
    while (y<C) {
	y=y+x;
	x=x+1;
     }
     __VERIFIER_assert(1==1);
}
