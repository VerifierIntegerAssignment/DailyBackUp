




extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}


int main() {

  int n = __VERIFIER_nondet_int();
  int x= 0;
  while(x<n) {
    x++;
  } 
if(n>0) __VERIFIER_assert(x==n);
}



