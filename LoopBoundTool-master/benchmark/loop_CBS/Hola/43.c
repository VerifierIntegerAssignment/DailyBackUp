extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}

int main() {


int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int i=0;
  int t=y;
   
  if (x==y) return x;
  
  while (__VERIFIER_nondet_int()){
    if (x > 0)   
      y = y + x;
  }
   
 
__VERIFIER_assert(y>=t);


}