extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main() {

  int c1 = 4000;
  int c2 = 2000;
  int n, v;
  int i, k, j;


  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(n>0);
  __VERIFIER_assume(n<10);


  k = 0;
  i = 0;
  while( i < n ) {
    i++;
    if(__VERIFIER_nondet_int() % 2 == 0) {
      v = 0;
    }
    else{ v = 1;}
    
    if( v == 0 )
      k += c1;
    else 
      k += c2;
  }
  
__VERIFIER_assert(k>n);
return 0;
  }