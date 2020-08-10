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
 	int r;
	int l;
	r = X;
    if(Y < 0) 
    {
       l = Y;
       while(l != 0) 
      {
        	r = r - 1;
        	l = l + 1;
      }
    } 
   else 
    {
      l = Y;
      while(l != 0) {
        r = r + 1;
        l = l - 1;
      }
    }	
}
