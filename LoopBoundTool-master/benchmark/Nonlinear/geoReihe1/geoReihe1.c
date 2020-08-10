extern void __VERIFIER_error() __attribute__ ((__noreturn__));

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
int __VERIFIER_nondet_int();

int main() 
{

                int Z;
                int K;
		int m ;
  		int l;
  		int k;
		m = 1;
  		l = Z;
  		k = 1;

  		while (k < K){
    			k = k + 1;
    			m = m*Z + 1;
    			l = Z*l;
  		}

  		m = m *(Z -1);

}
