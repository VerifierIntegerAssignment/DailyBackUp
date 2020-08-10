extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}

int LARGE_INT;

void main() {
   int w=1, z=0, x=0, y=0;
    while(__VERIFIER_nondet_int()){
    while(x <= LARGE_INT && y <= LARGE_INT && __VERIFIER_nondet_int()){
      if(w%2 == 1) 
        x++;
      if(z%2==0)
        y++;
    }
    while(w <= LARGE_INT && __VERIFIER_nondet_int())
    {
      z=x+y;
      w=z+1;
    }
  }
   __VERIFIER_assert(x==y);
}


