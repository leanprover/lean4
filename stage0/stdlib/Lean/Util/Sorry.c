// Lean compiler output
// Module: Lean.Util.Sorry
// Imports: Init Lean.Message Lean.Exception
#include <lean/lean.h>
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
size_t l_USize_add(size_t, size_t);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l_Lean_Expr_isSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_MessageData_instantiateMVars(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry_visit(lean_object*);
static lean_object* l_Lean_Expr_isSyntheticSorry___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_hasSyntheticSorry___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isSyntheticSorry___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Exception_hasSyntheticSorry(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1(lean_object*, size_t, size_t);
static lean_object* l_Lean_Expr_isSyntheticSorry___closed__2;
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object*);
static lean_object* l_Lean_Expr_isSorry___closed__1;
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSorry___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isSorry___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_hasSyntheticSorry___boxed(lean_object*);
static lean_object* l_Lean_Expr_hasSorry___closed__1;
LEAN_EXPORT uint8_t l_Lean_Expr_hasSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSorry___spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSorry___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSorry(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_isSorry(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Expr_isSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sorryAx");
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSorry(lean_object* x_1) {
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
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_isSyntheticSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Bool");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_isSyntheticSorry___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("true");
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSyntheticSorry(lean_object* x_1) {
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
x_19 = l_Lean_Expr_isSyntheticSorry___closed__2;
x_20 = lean_string_dec_eq(x_14, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = 0;
return x_22;
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isSyntheticSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_hasSorry___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_isSorry___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasSorry(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Expr_hasSorry___closed__1;
x_4 = lean_name_eq(x_2, x_3);
return x_4;
}
case 5:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_hasSorry(x_5);
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
x_12 = l_Lean_Expr_hasSorry(x_10);
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
x_17 = l_Lean_Expr_hasSorry(x_15);
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
x_23 = l_Lean_Expr_hasSorry(x_20);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Expr_hasSorry(x_21);
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
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object* x_1) {
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
x_5 = l_Lean_Expr_hasSyntheticSorry(x_2);
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
x_11 = l_Lean_Expr_hasSyntheticSorry(x_9);
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
x_16 = l_Lean_Expr_hasSyntheticSorry(x_14);
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
x_22 = l_Lean_Expr_hasSyntheticSorry(x_19);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Expr_hasSyntheticSorry(x_20);
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
LEAN_EXPORT lean_object* l_Lean_Expr_hasSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_hasSyntheticSorry(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSorry___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_MessageData_hasSorry(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_2 + x_7;
x_2 = x_8;
goto _start;
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
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSorry(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Expr_hasSorry(x_2);
lean_dec(x_2);
return x_3;
}
case 6:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_1 = x_4;
goto _start;
}
case 8:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_1 = x_6;
goto _start;
}
case 9:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_1 = x_8;
goto _start;
}
case 10:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_MessageData_hasSorry(x_10);
if (x_12 == 0)
{
x_1 = x_11;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_11);
x_14 = 1;
return x_14;
}
}
case 11:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_1 = x_15;
goto _start;
}
case 12:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_18);
lean_dec(x_17);
x_21 = 0;
return x_21;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_18, x_18);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_18);
lean_dec(x_17);
x_23 = 0;
return x_23;
}
else
{
size_t x_24; size_t x_25; uint8_t x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSorry___spec__1(x_17, x_24, x_25);
lean_dec(x_17);
return x_26;
}
}
}
default: 
{
uint8_t x_27; 
lean_dec(x_1);
x_27 = 0;
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSorry___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSorry___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_hasSorry(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_MessageData_hasSyntheticSorry(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_2 + x_7;
x_2 = x_8;
goto _start;
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
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry_visit(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Expr_hasSyntheticSorry(x_2);
lean_dec(x_2);
return x_3;
}
case 6:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_1 = x_4;
goto _start;
}
case 7:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_1 = x_6;
goto _start;
}
case 8:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_1 = x_8;
goto _start;
}
case 9:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_1 = x_10;
goto _start;
}
case 10:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_MessageData_hasSyntheticSorry_visit(x_12);
if (x_14 == 0)
{
x_1 = x_13;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_13);
x_16 = 1;
return x_16;
}
}
case 11:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_1 = x_17;
goto _start;
}
case 12:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_array_get_size(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_21, x_20);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_20);
lean_dec(x_19);
x_23 = 0;
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_20, x_20);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_20);
lean_dec(x_19);
x_25 = 0;
return x_25;
}
else
{
size_t x_26; size_t x_27; uint8_t x_28; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_28 = l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1(x_19, x_26, x_27);
lean_dec(x_19);
return x_28;
}
}
}
default: 
{
uint8_t x_29; 
lean_dec(x_1);
x_29 = 0;
return x_29;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_MessageData_instantiateMVars(x_1);
x_3 = l_Lean_MessageData_hasSyntheticSorry_visit(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_MessageData_hasSyntheticSorry_visit___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry_visit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_hasSyntheticSorry_visit(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hasSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_hasSyntheticSorry(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_hasSyntheticSorry(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_MessageData_hasSyntheticSorry(x_2);
return x_3;
}
else
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_hasSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Exception_hasSyntheticSorry(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Message(lean_object*);
lean_object* initialize_Lean_Exception(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Sorry(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_isSorry___closed__1 = _init_l_Lean_Expr_isSorry___closed__1();
lean_mark_persistent(l_Lean_Expr_isSorry___closed__1);
l_Lean_Expr_isSyntheticSorry___closed__1 = _init_l_Lean_Expr_isSyntheticSorry___closed__1();
lean_mark_persistent(l_Lean_Expr_isSyntheticSorry___closed__1);
l_Lean_Expr_isSyntheticSorry___closed__2 = _init_l_Lean_Expr_isSyntheticSorry___closed__2();
lean_mark_persistent(l_Lean_Expr_isSyntheticSorry___closed__2);
l_Lean_Expr_hasSorry___closed__1 = _init_l_Lean_Expr_hasSorry___closed__1();
lean_mark_persistent(l_Lean_Expr_hasSorry___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
