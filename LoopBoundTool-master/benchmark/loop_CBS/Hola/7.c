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

int x = 0, y = 0;
 while(x < LARGE_INT && y < LARGE_INT && y > -LARGE_INT && __VERIFIER_nondet_int()){
   if(__VERIFIER_nondet_int()){ 
      x++; 
      y+=100; 
   }
   else if (__VERIFIER_nondet_int()){ 
      if (x >= 4) { 
          x++; 
          y++; 
      } 
      if (x < 0){
          y--;
      }
   }
  
 }
__VERIFIER_assert(x < 4 || y > 2);
}