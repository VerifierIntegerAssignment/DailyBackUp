extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main() {
int flag=__VERIFIER_nondet_int();
int j = 2; 
   int k = 0;

   while(__VERIFIER_nondet_int()){ 
     if (flag>0)
       j = j + 4;
     else {
       j = j + 2;
       k = k + 1;
     }
   }
   if(k!=0)
__VERIFIER_assert(j==2*k+2);
}





