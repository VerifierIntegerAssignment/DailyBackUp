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
   int flag = 1;

  while (flag>0) {
    if (n>0) {
      n--;
      flag=1;
    } else
      flag=0;
  }
}
