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
			
            int A;int B;
	    int q;
	    int r;
	    int b;    
	    

	    q=0;
	    r=A;
	    b=B;

    
   	 while(r>=b)
       	 {
       		 b=2*b;
         }

    
    	while(b!=B)
        {
        q=2*q;
        b=b/2;

        if (r>=b) 
            {
            q=q+1;
            r=r-b;
            }

        }
	
	
	
}
