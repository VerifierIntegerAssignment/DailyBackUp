#include <time.h>
#include <stdlib.h>
#include <stdio.h>
int _count_long=0;
int _count_short=0;
char _count_char='\0';
unsigned int _count=0;
int _count_int=0;
double _count_double=0.0;
float _count_float=0.0f;
short __VERIFIER_nondet_short()
{
int value;
_count_short++;
srand(_count_short+(short)time(NULL));
srand(rand());
value=rand()%2;
return value;
}
long __VERIFIER_nondet_long()
{
int value;
_count_long++;
srand(_count_long+(short)time(NULL));
srand(rand());
value=rand()%2;
return value;
}
int __VERIFIER_nondet_bool()
{
int value;
_count++;
srand(_count+(unsigned int)time(NULL));
srand(rand());
value=rand()%2;
return value;
}
char __VERIFIER_nondet_char()
{
char value;
_count_char++;
srand(_count_int+(char)time(NULL));
srand(rand());
value=rand()%1000;
return value;
}
int __VERIFIER_nondet_int()
{
int value;
 _count_int++;
srand(_count_int+(int)time(NULL));
 srand(rand());
value=rand()%1000;
return value;
}

unsigned int __VERIFIER_nondet_uint()
{
unsigned int value;
 _count++;
srand(_count+(unsigned int)time(NULL));
 srand(rand());
value=rand()%1000;
return value;
}

double __VERIFIER_nondet_double()
{
double value;
 _count++;
srand(_count_double+(double)time(NULL));
 srand(rand());
 value=rand()%1000;
return value;
}

float __VERIFIER_nondet_float()
{
float value;
 _count++;
srand(_count_float+(float)time(NULL));
 srand(rand());
 
 value=rand()%1000;
return value;
}
void init_array(int a[],int size)
{
 int x = 0;
 while (x < size) 
{
 a[x]=__VERIFIER_nondet_int();
x=x+1;
 }
}
void init_array_char(char a[],int size)
{
 int x = 0;
 while (x < size) 
{
 a[x]=__VERIFIER_nondet_char();
x=x+1;
 }
}
int main(){
  int M;
  double n = 0;
  double x = 0;
  double y = 0;
  while (y < M)
  {
    y = y + 1;
    n = W_(1 / 2, n + 1, n);
    x = W_(1 / 2, x + n, x);
  }

}
