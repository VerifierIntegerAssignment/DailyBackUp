extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main() {
int A;
int i= A; int k=0; int j=0;
 while(i>0) {
    k=1; j=1;
    while(j<=A)
    { k++; j+=k; }
    
    i=i/2;
}
}

