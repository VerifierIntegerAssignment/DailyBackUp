extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}

int LARGE_INT;

void main() {
  int x=0;
  int y=0;
  int n = 0;
  while(x < LARGE_INT && __VERIFIER_nondet_int()) {
      x++;
      y++;
  }
  while(x!=n) {
      x--;
      y--;
  }

__VERIFIER_assert(y==n);

}


