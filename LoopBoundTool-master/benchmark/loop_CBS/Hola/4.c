
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int LARGE_INT;
int main() {

int x = 0;
	int y = 0;

	int j = 0;
	int i = 0;
        int flag;

	while(x < LARGE_INT && __VERIFIER_nondet_int())
	{
	  x++;
	  y++;
	  i+=x;
	  j+=y;
	  if(flag)  j+=1;
	} 
__VERIFIER_assert(j>=i);

}