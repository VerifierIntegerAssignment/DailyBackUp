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
  int x; int n; int y; int m;
  while (x<n) {
    while (y<m) {
      if (__VERIFIER_nondet_int())
        break;
      y=y+1;
    }
    x=x+1;
  }
}
