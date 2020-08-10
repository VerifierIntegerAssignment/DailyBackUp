
extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main() {

int i = 1;
	int j = 0;
	int z = i-j;
	int x = 0;
	int y = 0;
	int w = 0;

	while(__VERIFIER_nondet_int()) 
	{
		z+=x+y+w;
		y++;
		if(z%2==1) 
		  x++;
		w+=2; 
	}

    __VERIFIER_assert(x==y);

}
