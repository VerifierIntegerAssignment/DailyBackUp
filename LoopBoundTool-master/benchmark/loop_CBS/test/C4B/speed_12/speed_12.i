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
  int n; int m;
  int x=0;
  int y=0;

  while (x<n) {
    if (y<m)
      y=y+1;
    else
      x=x+1;
  }
}

