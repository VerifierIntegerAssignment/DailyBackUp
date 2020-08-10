
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main() {

int x,y;

  x = -50;
  while( x < 0 ) {
	x = x+y;
	y++;
  }
__VERIFIER_assert(y>0);
}