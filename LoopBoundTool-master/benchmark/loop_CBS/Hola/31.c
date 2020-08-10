extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main(void) {
int i,j,k,n,m;
  n = __VERIFIER_nondet_int();
  m = __VERIFIER_nondet_int();
  if( m+1 < n ); else return 0;
  for ( i=0; i<n; i+=4 ) {
    for ( j=i; j<m; ) {
      if (__VERIFIER_nondet_int()){
        __VERIFIER_assert( j >= 0 );
        j++;
        k = 0;
        while( k < j ) {
          k++;
        }
      }
      else { 
	__VERIFIER_assert( n+j+5>i );
	j+= 2;
      }
    }
}
}
