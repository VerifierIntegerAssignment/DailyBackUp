extern void __VERIFIER_error() __attribute__ ((__noreturn__));

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int __VERIFIER_nondet_int();

int main() 
{



    int X;int Y;
    int r,ds,p,q;

    r=X;
    ds=Y;
    p=1;
    q=0;

    while ( r>= ds )
        {
        ds=2*ds;
        p=2*p;
        }

     while ( p!=1 )
         {
         ds=ds/2;
         p=p/2;

         if ( r>=ds ) 
             {
             r=r-ds;
             q=q+p;
             }
         }
	


	

	
	

}
