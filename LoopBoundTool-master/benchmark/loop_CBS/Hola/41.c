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


int n = __VERIFIER_nondet_int();
   int flag = __VERIFIER_nondet_int();
   __VERIFIER_assume(n>=0);
   __VERIFIER_assume(n < LARGE_INT);
   int k = 1;
   if(flag) {
	k = __VERIFIER_nondet_int();
	__VERIFIER_assume(k>=0);
   }
   int i = 0, j = 0;
   while(i <= n) {
     i++;
     j+=i;
   }
   int z = k + i + j;
__VERIFIER_assert(z > 2*n);


}