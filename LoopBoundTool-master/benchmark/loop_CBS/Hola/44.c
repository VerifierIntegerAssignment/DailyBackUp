extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}

int main() {


  int k = __VERIFIER_nondet_int();
  int flag = __VERIFIER_nondet_int();
  int i=0;
  int j=0;
  int m;
  int __BLAST_NONDET;


  if (flag == 1){
     m=1;
  } else {
     m=2;
  }

  i=0;

  while ( i <= k){
    i++;
    j= j +m;
  }
  if(flag == 1)
    __VERIFIER_assert(j == i);



}