extern void __VERIFIER_error() __attribute__ ((__noreturn__));

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int __VERIFIER_nondet_int();

int main() {
  int n;
  int m;
  int p[m];
  int t[n];
  int i;
  int j;
    
  for (i = 0; i <= n - m; i++) { 
        
       for (j = 0; j < m; j++) 
           if (t[i + j] != p[j]) 
                break; 
  
       if (j == m) return i;

    }   
}

