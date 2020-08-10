




extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}


int main() {

int n = __VERIFIER_nondet_int();
  int x= 0;
  int m=0;
  while(x<n) {
     if(__VERIFIER_nondet_int()) {
	m = x;
     }
     x= x+1;
  }
if(n>0) __VERIFIER_assert(0<=m && m<n);  

}



