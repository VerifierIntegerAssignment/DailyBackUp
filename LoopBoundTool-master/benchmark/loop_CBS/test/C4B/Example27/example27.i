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
   int y;
  while (n<0) {
    n++;
    y+=1000;
    while (y>=100)
      y-=100;
  }
}

