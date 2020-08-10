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
int t = 0;
  int s = 0;
  int a = 0;
  int b = 0;
  int flag;
  while(t < LARGE_INT && __VERIFIER_nondet_int()){
    a++;
    b++;
    s+=a;
    t+=b;
    if(flag){
      t+=a;
    }
  } 
  //2s >= t
  int x = 1;
  if(flag){
    x = t-2*s+2;
  }
  //x <= 2
  int y = 0;
  while(y<=x){
    if(__VERIFIER_nondet_int()) 
       y++;
    else 
       y+=2;
  }
__VERIFIER_assert(y<=4);}





