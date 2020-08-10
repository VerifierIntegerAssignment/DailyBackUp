extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main() {

 int a = 0;
  int j;
  int m;
  int __BLAST_NONDET;
  m = __VERIFIER_nondet_int();
  if(m<=0)
    return 0;
  for(j = 1; j <= m ; j++){
    if(__VERIFIER_nondet_int()) 
       a++;
    else
       a--; 
  }
  __VERIFIER_assert(a>=-m);
  __VERIFIER_assert(a<=m);
}





