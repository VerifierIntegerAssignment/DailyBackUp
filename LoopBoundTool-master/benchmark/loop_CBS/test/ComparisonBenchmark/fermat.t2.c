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
int v8 = nondet();
int v9 = nondet();
int v10 = nondet();
int v11 = nondet();
int v12 = nondet();
int v13 = nondet();
int v14 = nondet();
int v15 = nondet();
int v16 = nondet();
int v17 = nondet();
int v18 = nondet();
int v19 = nondet();
int v20 = nondet();
int v21 = nondet();
int v22 = nondet();
goto loc8;
loc8:
 if (nondet_bool()) {
  goto loc7;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  goto loc6;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  if (!( v12 <= v10 )) goto end;
  v19 = v4;
  v22 = v19;
  goto loc3;
 }
 if (nondet_bool()) {
  if (!( 1+v10 <= v12 )) goto end;
  v4 = nondet();
  v10 = 1+v10;
  goto loc4;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  if (!( v11 <= v9 )) goto end;
  v18 = v3;
  v21 = v18;
  v15 = v7;
  v12 = v1;
  v4 = 1;
  v10 = 0;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( 1+v9 <= v11 )) goto end;
  v3 = nondet();
  v9 = 1+v9;
  goto loc5;
 }
 goto end;
loc1:
 if (nondet_bool()) {
  if (!( v13 <= v8 )) goto end;
  v17 = v2;
  v20 = v17;
  v14 = v6;
  v11 = v1;
  v3 = 1;
  v9 = 0;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 1+v8 <= v13 )) goto end;
  v2 = nondet();
  v8 = 1+v8;
  goto loc0;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  v1 = 3;
  v16 = v5;
  v13 = v1;
  v2 = 1;
  v8 = 0;
  goto loc0;
 }
 goto end;
loc3:
end:
;
}
