int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
goto loc5;
loc5:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  if (!( 101-v4 <= 0 )) goto end;
  v3 = 0;
  v2 = v3;
  v1 = v2;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 0 <= 100-v4 )) goto end;
  if (!( 0 <= -1+v5 )) goto end;
  v4 = 1+v4;
  goto loc2;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc0;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v4 = 0;
  goto loc4;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  if (!( 0 <= 100-v4 )) goto end;
  if (!( v5 <= 0 )) goto end;
  v3 = 0;
  v2 = v3;
  v1 = v2;
  goto loc1;
 }
 if (nondet_bool()) {
  if (!( 0 <= 100-v4 )) goto end;
  if (!( 0 <= -1+v5 )) goto end;
  v4 = 1+v4;
  goto loc0;
 }
 goto end;
loc1:
end:
;
}
