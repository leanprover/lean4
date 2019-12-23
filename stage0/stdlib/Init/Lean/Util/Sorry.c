// Lean compiler output
// Module: Init.Lean.Util.Sorry
// Imports: Init.Lean.Util.Message
#include "runtime/lean.h"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint8_t l_Lean_MessageData_hasSyntheticSorry___main(lean_object*);
uint8_t l_Lean_Expr_isSyntheticSorry(lean_object*);
lean_object* l_Lean_Expr_hasSorry___main___closed__1;
uint8_t l_Array_anyRangeMAux___main___at_Lean_MessageData_hasSyntheticSorry___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hasSorry___main___boxed(lean_object*);
lean_object* l_Lean_MessageData_hasSyntheticSorry___main___boxed(lean_object*);
uint8_t l_Lean_Expr_hasSorry___main(lean_object*);
lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hasSorry___main___boxed(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_isSyntheticSorry___closed__1;
lean_object* l_Lean_Expr_hasSyntheticSorry___boxed(lean_object*);
lean_object* l_Lean_Expr_isSyntheticSorry___boxed(lean_object*);
uint8_t l_Lean_MessageData_hasSorry___main(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_MessageData_hasSorry___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry___main(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_MessageData_hasSorry___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isSorry___closed__1;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_MessageData_hasSyntheticSorry___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hasSorry___boxed(lean_object*);
lean_object* l_Lean_Expr_isSorry___boxed(lean_object*);
extern lean_object* l_Bool_HasRepr___closed__2;
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_Expr_hasSorry___boxed(lean_object*);
lean_object* l_Lean_Expr_hasSyntheticSorry___main___boxed(lean_object*);
uint8_t l_Lean_MessageData_hasSorry(lean_object*);
uint8_t l_Lean_Expr_isSorry(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* _init_l_Lean_Expr_isSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sorryAx");
return x_1;
}
}
uint8_t l_Lean_Expr_isSorry(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = l_Lean_Expr_isSorry___closed__1;
x_8 = lean_string_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
lean_object* l_Lean_Expr_isSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_isSyntheticSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Bool");
return x_1;
}
}
uint8_t l_Lean_Expr_isSyntheticSorry(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_Expr_isSorry___closed__1;
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_Expr_isSyntheticSorry___closed__1;
x_17 = lean_string_dec_eq(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Bool_HasRepr___closed__2;
x_20 = lean_string_dec_eq(x_14, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
else
{
uint8_t x_22; 
x_22 = 1;
return x_22;
}
}
}
else
{
uint8_t x_23; 
x_23 = 0;
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = 0;
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = 0;
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = 0;
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = 0;
return x_31;
}
}
}
lean_object* l_Lean_Expr_isSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isSyntheticSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_hasSorry___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_isSorry___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_hasSorry___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Expr_hasSorry___main___closed__1;
x_4 = lean_name_eq(x_2, x_3);
return x_4;
}
case 5:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_hasSorry___main(x_5);
if (x_7 == 0)
{
x_1 = x_6;
goto _start;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
case 6:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = l_Lean_Expr_hasSorry___main(x_10);
if (x_12 == 0)
{
x_1 = x_11;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
case 7:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
x_17 = l_Lean_Expr_hasSorry___main(x_15);
if (x_17 == 0)
{
x_1 = x_16;
goto _start;
}
else
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
}
case 8:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
x_23 = l_Lean_Expr_hasSorry___main(x_20);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Expr_hasSorry___main(x_21);
if (x_24 == 0)
{
x_1 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
x_26 = 1;
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = 1;
return x_27;
}
}
case 10:
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_1, 1);
x_1 = x_28;
goto _start;
}
case 11:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_1, 2);
x_1 = x_30;
goto _start;
}
default: 
{
uint8_t x_32; 
x_32 = 0;
return x_32;
}
}
}
}
lean_object* l_Lean_Expr_hasSorry___main___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasSorry___main(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_hasSorry(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasSorry___main(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_hasSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_hasSyntheticSorry___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Expr_isSyntheticSorry(x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasSyntheticSorry___main(x_2);
if (x_5 == 0)
{
x_1 = x_3;
goto _start;
}
else
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
case 6:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = l_Lean_Expr_hasSyntheticSorry___main(x_9);
if (x_11 == 0)
{
x_1 = x_10;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
case 7:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = l_Lean_Expr_hasSyntheticSorry___main(x_14);
if (x_16 == 0)
{
x_1 = x_15;
goto _start;
}
else
{
uint8_t x_18; 
x_18 = 1;
return x_18;
}
}
case 8:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
x_22 = l_Lean_Expr_hasSyntheticSorry___main(x_19);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Expr_hasSyntheticSorry___main(x_20);
if (x_23 == 0)
{
x_1 = x_21;
goto _start;
}
else
{
uint8_t x_25; 
x_25 = 1;
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = 1;
return x_26;
}
}
case 10:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_1, 1);
x_1 = x_27;
goto _start;
}
case 11:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_1, 2);
x_1 = x_29;
goto _start;
}
default: 
{
uint8_t x_31; 
x_31 = 0;
return x_31;
}
}
}
}
lean_object* l_Lean_Expr_hasSyntheticSorry___main___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasSyntheticSorry___main(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_hasSyntheticSorry___main(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_hasSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasSyntheticSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_MessageData_hasSorry___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = l_Lean_MessageData_hasSorry___main(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_4);
return x_8;
}
}
}
}
uint8_t l_Lean_MessageData_hasSorry___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Expr_hasSorry___main(x_2);
return x_3;
}
case 5:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
x_1 = x_4;
goto _start;
}
case 6:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
x_1 = x_6;
goto _start;
}
case 7:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
x_1 = x_8;
goto _start;
}
case 8:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Lean_MessageData_hasSorry___main(x_10);
if (x_12 == 0)
{
x_1 = x_11;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
case 9:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 1);
x_1 = x_15;
goto _start;
}
case 10:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_anyRangeMAux___main___at_Lean_MessageData_hasSorry___main___spec__1(x_17, x_17, x_18, x_19);
lean_dec(x_18);
return x_20;
}
default: 
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_MessageData_hasSorry___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_MessageData_hasSorry___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_MessageData_hasSorry___main___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_hasSorry___main(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_MessageData_hasSorry(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_MessageData_hasSorry___main(x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_hasSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_hasSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_MessageData_hasSyntheticSorry___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = l_Lean_MessageData_hasSyntheticSorry___main(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_4);
return x_8;
}
}
}
}
uint8_t l_Lean_MessageData_hasSyntheticSorry___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Expr_hasSyntheticSorry___main(x_2);
return x_3;
}
case 5:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
x_1 = x_4;
goto _start;
}
case 6:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
x_1 = x_6;
goto _start;
}
case 7:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
x_1 = x_8;
goto _start;
}
case 8:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Lean_MessageData_hasSyntheticSorry___main(x_10);
if (x_12 == 0)
{
x_1 = x_11;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = 1;
return x_14;
}
}
case 9:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 1);
x_1 = x_15;
goto _start;
}
case 10:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_anyRangeMAux___main___at_Lean_MessageData_hasSyntheticSorry___main___spec__1(x_17, x_17, x_18, x_19);
lean_dec(x_18);
return x_20;
}
default: 
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_MessageData_hasSyntheticSorry___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_MessageData_hasSyntheticSorry___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_MessageData_hasSyntheticSorry___main___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_hasSyntheticSorry___main(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_MessageData_hasSyntheticSorry___main(x_1);
return x_2;
}
}
lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_hasSyntheticSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Init_Lean_Util_Message(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util_Sorry(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Util_Message(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_isSorry___closed__1 = _init_l_Lean_Expr_isSorry___closed__1();
lean_mark_persistent(l_Lean_Expr_isSorry___closed__1);
l_Lean_Expr_isSyntheticSorry___closed__1 = _init_l_Lean_Expr_isSyntheticSorry___closed__1();
lean_mark_persistent(l_Lean_Expr_isSyntheticSorry___closed__1);
l_Lean_Expr_hasSorry___main___closed__1 = _init_l_Lean_Expr_hasSorry___main___closed__1();
lean_mark_persistent(l_Lean_Expr_hasSorry___main___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
