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
  int p[n];
  int m;
  int t[m];
  int b[m];

  int i = 0, j = 0, k = -1;
  

  while (i < n)
  {
    while (j >= 0 && t[i] != p[j]) {
       k = b[j];
       j -= k;
    }
    i++, j++;
    if (j == m)
        break;
  }
  return i;
}



