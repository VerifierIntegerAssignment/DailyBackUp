extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int main() {
 int i = __VERIFIER_nondet_int();
    int j = __VERIFIER_nondet_int();
  int x = i;
  int y = j;
 
  while(x!=0) {
	x--;
	y--;
  }
  if(i==j)
__VERIFIER_assert(y==0);
}





