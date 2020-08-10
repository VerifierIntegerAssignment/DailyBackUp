extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main(void) {
int k = __VERIFIER_nondet_int();
  int z = k;
  int x = 0;
  int y = 0;

  while(__VERIFIER_nondet_int())
  {
    int c = 0;
    while(__VERIFIER_nondet_int())
    {
      if(z==k+y-c)
      {
        x++;
        y++;
        c++;
      }else
      {
        x++;
        y--;
        c++;
      }
    }
    while(__VERIFIER_nondet_int())
    {
      x--;
      y--;
    }
    z=k+y;
  }
__VERIFIER_assert(x==y);
}
