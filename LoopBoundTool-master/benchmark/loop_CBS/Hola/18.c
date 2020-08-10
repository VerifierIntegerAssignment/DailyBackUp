extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main() {
    int flag = __VERIFIER_nondet_int();
    int a = __VERIFIER_nondet_int();
   int b;
   int j = 0;

   for (b=0; b < 100 ; ++b){
      if (flag)
         j = j +1;
   }


   if(flag)
        __VERIFIER_assert(j==100);
}
