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
  int z = 0;
  int k = 0;

  while(y <= LARGE_INT && __VERIFIER_nondet_int())
  {
     if(k%3 == 0)
       x++;
     y++;
     z++;
     k = x+y+z;
  }

  __VERIFIER_assert(x==y);
  __VERIFIER_assert(y==z);
  }