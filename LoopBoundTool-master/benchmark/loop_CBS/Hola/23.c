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
   int i, sum=0;
   __VERIFIER_assume( n >= 0);
   __VERIFIER_assume( n < LARGE_INT);

   for (i=0; i < n; ++i)
      sum = sum +i;
        __VERIFIER_assert(sum >= 0);     

}
