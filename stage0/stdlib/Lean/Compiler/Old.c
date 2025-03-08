// Lean compiler output
// Module: Lean.Compiler.Old
// Imports: Lean.Environment
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
LEAN_EXPORT lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_checkIsDefinition___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_mkUnsafeRecName___closed__1;
static lean_object* l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1;
LEAN_EXPORT lean_object* lean_mk_eager_lambda_lifting_name(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getDeclNamesForCodeGen(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_checkIsDefinition___lambda__1(lean_object*);
static lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__5;
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__4;
LEAN_EXPORT lean_object* lean_is_unsafe_rec_name(lean_object*);
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__1;
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__2;
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_checkIsDefinition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_mk_unsafe_rec_name(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_is_eager_lambda_lifting_name(lean_object*);
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__3;
lean_object* l_List_mapTR_loop___at_Lean_Declaration_getTopLevelNames___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* _init_l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_elambda_", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* lean_mk_eager_lambda_lifting_name(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_4 = l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_Lean_Name_str___override(x_1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_isEagerLambdaLiftingName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_elambda", 8, 8);
return x_1;
}
}
LEAN_EXPORT uint8_t lean_is_eager_lambda_lifting_name(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Compiler_isEagerLambdaLiftingName___closed__1;
x_6 = l_String_isPrefixOf(x_5, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
x_1 = x_3;
goto _start;
}
else
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = 1;
return x_8;
}
}
default: 
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_1 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_is_eager_lambda_lifting_name(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getDeclNamesForCodeGen(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = lean_box(0);
return x_2;
}
case 4:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
case 5:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = l_List_mapTR_loop___at_Lean_Declaration_getTopLevelNames___spec__1(x_4, x_5);
return x_6;
}
case 6:
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
default: 
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_checkIsDefinition___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_checkIsDefinition___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown declaration '", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declaration is not a definition '", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_checkIsDefinition(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = l_Lean_Environment_find_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = 1;
x_5 = l_Lean_Compiler_checkIsDefinition___closed__1;
x_6 = l_Lean_Name_toString(x_2, x_4, x_5);
x_7 = l_Lean_Compiler_checkIsDefinition___closed__2;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
switch (lean_obj_tag(x_12)) {
case 0:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = 1;
x_16 = l_Lean_Compiler_checkIsDefinition___closed__1;
x_17 = l_Lean_Name_toString(x_2, x_15, x_16);
x_18 = l_Lean_Compiler_checkIsDefinition___closed__4;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_21 = lean_string_append(x_19, x_20);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_22 = 1;
x_23 = l_Lean_Compiler_checkIsDefinition___closed__1;
x_24 = l_Lean_Name_toString(x_2, x_22, x_23);
x_25 = l_Lean_Compiler_checkIsDefinition___closed__4;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
case 1:
{
lean_object* x_30; 
lean_dec(x_12);
lean_dec(x_2);
x_30 = l_Lean_Compiler_checkIsDefinition___closed__5;
return x_30;
}
case 3:
{
lean_object* x_31; 
lean_dec(x_12);
lean_dec(x_2);
x_31 = l_Lean_Compiler_checkIsDefinition___closed__5;
return x_31;
}
default: 
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_12, 0);
lean_dec(x_33);
x_34 = 1;
x_35 = l_Lean_Compiler_checkIsDefinition___closed__1;
x_36 = l_Lean_Name_toString(x_2, x_34, x_35);
x_37 = l_Lean_Compiler_checkIsDefinition___closed__4;
x_38 = lean_string_append(x_37, x_36);
lean_dec(x_36);
x_39 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_40 = lean_string_append(x_38, x_39);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_40);
return x_12;
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_12);
x_41 = 1;
x_42 = l_Lean_Compiler_checkIsDefinition___closed__1;
x_43 = l_Lean_Name_toString(x_2, x_41, x_42);
x_44 = l_Lean_Compiler_checkIsDefinition___closed__4;
x_45 = lean_string_append(x_44, x_43);
lean_dec(x_43);
x_46 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_47 = lean_string_append(x_45, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_checkIsDefinition___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_checkIsDefinition___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkUnsafeRecName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_unsafe_rec", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* lean_mk_unsafe_rec_name(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_mkUnsafeRecName___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_is_unsafe_rec_name(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Compiler_mkUnsafeRecName___closed__1;
x_5 = lean_string_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
}
else
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
}
}
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Old(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1 = _init_l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkEagerLambdaLiftingName___closed__1);
l_Lean_Compiler_isEagerLambdaLiftingName___closed__1 = _init_l_Lean_Compiler_isEagerLambdaLiftingName___closed__1();
lean_mark_persistent(l_Lean_Compiler_isEagerLambdaLiftingName___closed__1);
l_Lean_Compiler_checkIsDefinition___closed__1 = _init_l_Lean_Compiler_checkIsDefinition___closed__1();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__1);
l_Lean_Compiler_checkIsDefinition___closed__2 = _init_l_Lean_Compiler_checkIsDefinition___closed__2();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__2);
l_Lean_Compiler_checkIsDefinition___closed__3 = _init_l_Lean_Compiler_checkIsDefinition___closed__3();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__3);
l_Lean_Compiler_checkIsDefinition___closed__4 = _init_l_Lean_Compiler_checkIsDefinition___closed__4();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__4);
l_Lean_Compiler_checkIsDefinition___closed__5 = _init_l_Lean_Compiler_checkIsDefinition___closed__5();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__5);
l_Lean_Compiler_mkUnsafeRecName___closed__1 = _init_l_Lean_Compiler_mkUnsafeRecName___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkUnsafeRecName___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
