void main() {
      int a; 
      int b; 
      int c;
      while (b >= 1) {
        c = 1;
          while (1) {
            if (a >= c) {
              c = c + 1;
            }
            else if (c >= a + 1) {
              b = b - 1;
                break;
            }
            else
              return;
          }
      }
        __VERIFIER_assert(1==1);
          return;
}
