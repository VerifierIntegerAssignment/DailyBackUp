extern void __VERIFIER_error() __attribute__ ((__noreturn__));

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int __VERIFIER_nondet_int();


int x, y;

void produce() {
  while (x > 0) {
    tick(-1); x--; y++;
  }
}

void consume() {
  while (y > 0) {
    y--; x++; tick(1);
  }
}

void start(int y, int z) {
  consume(); produce(); consume();
}
