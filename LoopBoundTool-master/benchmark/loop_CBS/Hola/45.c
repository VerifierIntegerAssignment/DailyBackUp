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

int flag = __VERIFIER_nondet_int(); 
  int x = 0;
  int y = 0;
  int j = 0;
  int i = 0;
  int c = 0;
  int d = 1;
  while(j < LARGE_INT && __VERIFIER_nondet_int())
  {
    x++;
    y++;
    i+=x;
    j+=y;
    if(flag) 
    {
      j+=1;
    }
  } 
  if(j>=i)
    x=y;
  else
    x=y+1;

  int w = 1;
  int z = 0;
  while(w < LARGE_INT && __VERIFIER_nondet_int()){
    while(__VERIFIER_nondet_int()){
      if(w%2 == 1) 
        x++;
      if(z%2==0)
        y++;
      }
      z=x+y;
      w=z+1;
  }
  
__VERIFIER_assert(x==y);
  


}