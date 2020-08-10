extern void __VERIFIER_error() __attribute__ ((__noreturn__));

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int __VERIFIER_nondet_int();



void count_down(int x) {
  if (x>0) {
    x--;
    count_down(x);
  }
}

int copy(int x, int y) {
  if (x>0) {
    y++;
    x--;
    y=copy(x, y);
  }
  return y;
}

void start(int x, int y) {
  y = copy(x, y);
  count_down(y);
}

