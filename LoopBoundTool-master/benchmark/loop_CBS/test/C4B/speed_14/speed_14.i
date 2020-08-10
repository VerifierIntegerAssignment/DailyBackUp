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
  int x=0;

  while (x<n) {
    if (__VERIFIER_nondet_int())
      x=x+1;
    else 
      x=x+1;
  }
}

