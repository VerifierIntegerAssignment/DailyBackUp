int nondet() { int a; return a; }
_Bool nondet_bool() { _Bool a; return a; }
int main() {
int v1 = nondet();
int v2 = nondet();
int v3 = nondet();
int v4 = nondet();
int v5 = nondet();
int v6 = nondet();
int v7 = nondet();
goto loc6;
loc6:
 if (nondet_bool()) {
  goto loc5;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  v3 = v6;
  v1 = v3;
  goto loc4;
 }
 if (nondet_bool()) {
  v2 = v7;
  v1 = v2;
  v6 = v1;
  v1 = nondet();
  goto loc1;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  v2 = v7;
  v1 = v2;
  v6 = v1;
  v1 = nondet();
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  v2 = v7;
  v1 = v2;
  v6 = v1;
  v1 = nondet();
  goto loc1;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  v5 = 1+v5;
  goto loc3;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v4 = 4;
  v5 = 0;
  v6 = 0;
  goto loc3;
 }
 goto end;
loc4:
end:
;
}
