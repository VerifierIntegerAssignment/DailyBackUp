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
  int i;
  int j;

  i=0;
  while (i<n) {
    j=i+1;
    while (j<n) {
      if (__VERIFIER_nondet_int()) {
        j=j-1;
        n=n-1;
      }
      j=j+1;
    }
    i=i+1;
  }
}












