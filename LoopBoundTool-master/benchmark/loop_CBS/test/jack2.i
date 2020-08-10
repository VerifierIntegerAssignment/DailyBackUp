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

 while(i>1) {
 
    j=i; k=0;
    
    while(j<=A)
    { 
        k=0;
    
        while(k<A)
        {
            k=k+2;
        }
    
      j=j*2;
    
    }
    
   i=i/2;
 }
}


