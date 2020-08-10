extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}

int LARGE_INT;

int main() {

int x = 0;
  int y = 0;
  int i = 0;
  int j = 0;

  while(x <= LARGE_INT && y <= LARGE_INT && __VERIFIER_nondet_int())
  {
    while(__VERIFIER_nondet_int())
    {
       if(x==y)
          i++;
       else
          j++;
    }
    if(i>=j)
    {
       x++;
       y++;
    }
    else
       y++;
  }

__VERIFIER_assert(i>=j);

}
