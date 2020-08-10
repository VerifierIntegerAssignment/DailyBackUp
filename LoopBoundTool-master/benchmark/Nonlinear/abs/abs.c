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
        int X;
	int a;	
	if(X<=0)
	{
		a=-X;
	}
	else
	{
		a=X;
	}
}
