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
   int x; 
   int y;
   int z;
  while (x > y) {
    x -= y+1;
    z = 100 + 2*y;
    while (z > 0)
      z--;
  }
}


