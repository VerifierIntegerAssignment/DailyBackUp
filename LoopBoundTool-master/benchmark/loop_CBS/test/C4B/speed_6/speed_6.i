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
  int n;
  while (n>0) {
    n=n-1;
    while (n>0) {
      if (__VERIFIER_nondet_int()) break;
      n=n-1;
    }
  }
}
