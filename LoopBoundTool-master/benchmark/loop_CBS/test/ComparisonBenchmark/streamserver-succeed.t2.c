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
int v23 = nondet();
int v24 = nondet();
int v25 = nondet();
goto loc36;
loc36:
 if (nondet_bool()) {
  goto loc35;
 }
 goto end;
loc4:
 if (nondet_bool()) {
  goto loc31;
 }
 goto end;
loc6:
 if (nondet_bool()) {
  goto loc19;
 }
 goto end;
loc23:
 if (nondet_bool()) {
  goto loc25;
 }
 goto end;
loc0:
 if (nondet_bool()) {
  goto loc1;
 }
 goto end;
loc2:
 if (nondet_bool()) {
  goto loc3;
 }
 goto end;
loc3:
 if (nondet_bool()) {
  if (!( 1 <= v14 )) goto end;
  v24 = 1;
  goto loc4;
 }
 if (nondet_bool()) {
  if (!( v14 <= 0 )) goto end;
  v24 = 0;
  goto loc4;
 }
 goto end;
loc5:
 if (nondet_bool()) {
  v15 = 1+v15;
  goto loc6;
 }
 goto end;
loc7:
 if (nondet_bool()) {
  if (!( 0 <= v18 )) goto end;
  v1 = v20;
  v14 = 1+v14;
  goto loc5;
 }
 if (nondet_bool()) {
  if (!( 1+v18 <= 0 )) goto end;
  goto loc5;
 }
 goto end;
loc8:
 if (nondet_bool()) {
  v6 = nondet();
  v18 = v6;
  goto loc7;
 }
 goto end;
loc9:
 if (nondet_bool()) {
  if (!( v22 <= 10 )) goto end;
  goto loc8;
 }
 if (nondet_bool()) {
  if (!( 11 <= v22 )) goto end;
  v22 = 10;
  goto loc8;
 }
 goto end;
loc10:
 if (nondet_bool()) {
  v22 = nondet();
  goto loc9;
 }
 goto end;
loc11:
 if (nondet_bool()) {
  goto loc2;
 }
 goto end;
loc12:
 if (nondet_bool()) {
  if (!( v12 <= 1 )) goto end;
  if (!( 1 <= v12 )) goto end;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( 2 <= v12 )) goto end;
  goto loc11;
 }
 if (nondet_bool()) {
  if (!( 1+v12 <= 1 )) goto end;
  goto loc11;
 }
 goto end;
loc13:
 if (nondet_bool()) {
  if (!( 4 <= v16 )) goto end;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( 1+v16 <= 3 )) goto end;
  goto loc10;
 }
 if (nondet_bool()) {
  if (!( v16 <= 3 )) goto end;
  if (!( 3 <= v16 )) goto end;
  v12 = nondet();
  goto loc12;
 }
 goto end;
loc14:
 if (nondet_bool()) {
  if (!( 0 <= v18 )) goto end;
  goto loc13;
 }
 if (nondet_bool()) {
  if (!( 1+v18 <= 0 )) goto end;
  goto loc5;
 }
 goto end;
loc15:
 if (nondet_bool()) {
  v7 = nondet();
  v18 = v7;
  goto loc14;
 }
 goto end;
loc16:
 if (nondet_bool()) {
  if (!( v11 <= 0 )) goto end;
  goto loc15;
 }
 if (nondet_bool()) {
  if (!( 1 <= v11 )) goto end;
  goto loc5;
 }
 goto end;
loc17:
 if (nondet_bool()) {
  if (!( v10 <= 0 )) goto end;
  goto loc15;
 }
 if (nondet_bool()) {
  if (!( 1 <= v10 )) goto end;
  v11 = nondet();
  goto loc16;
 }
 goto end;
loc18:
 if (nondet_bool()) {
  if (!( v20 <= 0 )) goto end;
  v10 = nondet();
  goto loc17;
 }
 if (nondet_bool()) {
  if (!( 1 <= v20 )) goto end;
  goto loc5;
 }
 goto end;
loc20:
 if (nondet_bool()) {
  goto loc21;
 }
 goto end;
loc21:
 if (nondet_bool()) {
  if (!( 1+v21 <= v4 )) goto end;
  v5 = nondet();
  v20 = v5;
  goto loc18;
 }
 if (nondet_bool()) {
  if (!( v4 <= v21 )) goto end;
  goto loc2;
 }
 goto end;
loc22:
 if (nondet_bool()) {
  v21 = 1+v21;
  goto loc23;
 }
 goto end;
loc24:
 if (nondet_bool()) {
  if (!( 0 <= v1 )) goto end;
  goto loc22;
 }
 if (nondet_bool()) {
  if (!( 1+v1 <= -1 )) goto end;
  goto loc22;
 }
 if (nondet_bool()) {
  if (!( v1 <= -1 )) goto end;
  if (!( -1 <= v1 )) goto end;
  goto loc20;
 }
 goto end;
loc25:
 if (nondet_bool()) {
  if (!( v4 <= v21 )) goto end;
  goto loc24;
 }
 if (nondet_bool()) {
  if (!( 1+v21 <= v4 )) goto end;
  goto loc20;
 }
 goto end;
loc26:
 if (nondet_bool()) {
  if (!( v9 <= 0 )) goto end;
  goto loc23;
 }
 if (nondet_bool()) {
  if (!( 1 <= v9 )) goto end;
  goto loc5;
 }
 goto end;
loc27:
 if (nondet_bool()) {
  if (!( 1 <= v8 )) goto end;
  goto loc23;
 }
 if (nondet_bool()) {
  if (!( v8 <= 0 )) goto end;
  goto loc26;
 }
 goto end;
loc19:
 if (nondet_bool()) {
  if (!( 1+v15 <= v2 )) goto end;
  v8 = nondet();
  v9 = nondet();
  goto loc27;
 }
 if (nondet_bool()) {
  if (!( v2 <= v15 )) goto end;
  goto loc2;
 }
 goto end;
loc28:
 if (nondet_bool()) {
  if (!( 1 <= v17 )) goto end;
  v25 = 0;
  goto loc29;
 }
 if (nondet_bool()) {
  if (!( v17 <= 0 )) goto end;
  v25 = 1;
  goto loc29;
 }
 goto end;
loc29:
 if (nondet_bool()) {
  v15 = v17;
  goto loc6;
 }
 goto end;
loc30:
 if (nondet_bool()) {
  if (!( v24 <= 0 )) goto end;
  goto loc28;
 }
 if (nondet_bool()) {
  if (!( 1 <= v24 )) goto end;
  v25 = 1;
  goto loc29;
 }
 goto end;
loc31:
 if (nondet_bool()) {
  goto loc4;
 }
 goto end;
loc32:
 if (nondet_bool()) {
  goto loc33;
 }
 goto end;
loc33:
 if (nondet_bool()) {
  v13 = nondet();
  v24 = v13;
  goto loc30;
 }
 goto end;
loc34:
 if (nondet_bool()) {
  if (!( 4 <= v19 )) goto end;
  goto loc32;
 }
 if (nondet_bool()) {
  if (!( 1+v19 <= 3 )) goto end;
  goto loc32;
 }
 if (nondet_bool()) {
  if (!( v19 <= 3 )) goto end;
  if (!( 3 <= v19 )) goto end;
  goto loc33;
 }
 goto end;
loc35:
 if (nondet_bool()) {
  v23 = 1;
  v21 = 0;
  v14 = 0;
  v2 = nondet();
  v17 = nondet();
  if (!( 0 <= v17 )) goto end;
  v3 = nondet();
  if (!( 1 <= v3 )) goto end;
  v24 = nondet();
  goto loc34;
 }
 goto end;
loc1:
end:
;
}
