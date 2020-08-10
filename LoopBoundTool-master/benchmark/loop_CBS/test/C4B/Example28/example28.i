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
  while (x > y) {
    x--;
    x+=1000;
    y+=1000;
  }

  while (y>0)
    y--;
  while (x<0)
    x++;
}
