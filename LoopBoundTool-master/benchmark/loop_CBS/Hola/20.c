extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main() {
 int x, y, k, j, i, n;
    n = __VERIFIER_nondet_int();
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    k = __VERIFIER_nondet_int();
    __VERIFIER_assume((x+y)== k);
    int m = 0;
    j = 0;
    while(j<n) {
      if(j==i)
      {
         x++;
         y--;
      }else
      {
         y++;
         x--;
      }
	if(__VERIFIER_nondet_int())
  		m = j;
      j++;
    }
    __VERIFIER_assert((x+y)== k);
    if(n>0)
    {
   	__VERIFIER_assert (0<=m); 
	__VERIFIER_assert (m<n);
}

}
