int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
goto loc2;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 0 <= v3 )) goto end;
  v3 = -1+v3;
  v1 = v2;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 1+v3 <= 0 )) goto end;
  v1 = v2;
  goto loc1;
 }
 goto end;
loc1:
end:
;
}
