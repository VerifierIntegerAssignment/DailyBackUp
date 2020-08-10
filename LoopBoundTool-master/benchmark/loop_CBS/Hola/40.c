extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}

int main() {


   int i, j, k;
   int flag = __VERIFIER_nondet_int();
   j = 1;
   if(flag) {i=0;}
   else {i=1;}
   

   while(__VERIFIER_nondet_int()) {
      i+=2;
      if(i%2 == 0) {
	j+=2;
      }
      else j++;
   } 
   
   int a = 0;
   int b=0;
   
   while(__VERIFIER_nondet_int()) {
      a++;      
      b+=(j-i); 
   }
   if(flag)
     __VERIFIER_assert(a==b);


}