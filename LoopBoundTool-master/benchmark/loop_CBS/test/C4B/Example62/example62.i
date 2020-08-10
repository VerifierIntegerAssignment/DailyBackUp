extern void __VERIFIER_error() __attribute__ ((__noreturn__));

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int __VERIFIER_nondet_int();


int main()
{
   int l, int h;
  __VERIFIER_assert(l < h);
  while (1) {
    do { l++;  } while (l<h && __VERIFIER_nondet_int());
    do { h--; } while (l<h && __VERIFIER_nondet_int());
    if (l >= h) break;
  }
}

