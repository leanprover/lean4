// Lean compiler output
// Module: Lean.Compiler.Old
// Imports: public import Lean.Environment import Init.Data.String.TakeDrop
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
static lean_object* l_Lean_Compiler_getDeclNamesForCodeGen___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___boxed(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___closed__0;
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_mkEagerLambdaLiftingName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getDeclNamesForCodeGen(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___closed__1;
static lean_object* l_Lean_Compiler_mkUnsafeRecName___closed__0;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_isUnsafeRecName_x3f(lean_object*);
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__1;
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_checkIsDefinition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUnsafeRecName(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(size_t, size_t, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_getDeclNamesForCodeGen___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isUnsafeRecName_x3f___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_Compiler_isEagerLambdaLiftingName(lean_object*);
static lean_object* l_Lean_Compiler_checkIsDefinition___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* _init_l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_elambda_", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkEagerLambdaLiftingName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0;
x_4 = l_Nat_reprFast(x_2);
x_5 = lean_string_append(x_3, x_4);
lean_dec_ref(x_4);
x_6 = l_Lean_Name_str___override(x_1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_isEagerLambdaLiftingName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_elambda", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_isEagerLambdaLiftingName___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_isEagerLambdaLiftingName___closed__0;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isEagerLambdaLiftingName(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Compiler_isEagerLambdaLiftingName___closed__0;
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = l_Lean_Compiler_isEagerLambdaLiftingName___closed__1;
x_7 = lean_nat_dec_le(x_6, x_5);
if (x_7 == 0)
{
x_1 = x_2;
goto _start;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_string_memcmp(x_3, x_4, x_9, x_9, x_6);
if (x_10 == 0)
{
x_1 = x_2;
goto _start;
}
else
{
return x_10;
}
}
}
case 2:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 0);
x_1 = x_12;
goto _start;
}
default: 
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isEagerLambdaLiftingName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_isEagerLambdaLiftingName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_9, x_2, x_7);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_getDeclNamesForCodeGen___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_getDeclNamesForCodeGen___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getDeclNamesForCodeGen(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_Lean_Compiler_getDeclNamesForCodeGen___closed__0;
x_6 = lean_array_push(x_5, x_4);
return x_6;
}
case 3:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_Compiler_getDeclNamesForCodeGen___closed__0;
x_11 = lean_array_push(x_10, x_9);
return x_11;
}
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Compiler_getDeclNamesForCodeGen___closed__0;
x_16 = lean_array_push(x_15, x_14);
return x_16;
}
case 5:
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec_ref(x_1);
x_18 = lean_array_mk(x_17);
x_19 = lean_array_size(x_18);
x_20 = 0;
x_21 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_getDeclNamesForCodeGen_spec__0(x_19, x_20, x_18);
return x_21;
}
default: 
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = l_Lean_Compiler_getDeclNamesForCodeGen___closed__1;
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Declaration `", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` is not a definition", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unknown declaration `", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_checkIsDefinition___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_checkIsDefinition(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
lean_inc(x_2);
x_6 = l_Lean_Environment_findAsync_x3f(x_1, x_2, x_5);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
lean_dec(x_8);
switch (x_9) {
case 0:
{
lean_free_object(x_6);
lean_dec(x_2);
goto block_4;
}
case 3:
{
lean_free_object(x_6);
lean_dec(x_2);
goto block_4;
}
default: 
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_Compiler_checkIsDefinition___closed__1;
x_11 = 1;
x_12 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_11);
x_13 = lean_string_append(x_10, x_12);
lean_dec_ref(x_12);
x_14 = l_Lean_Compiler_checkIsDefinition___closed__2;
x_15 = lean_string_append(x_13, x_14);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_15);
return x_6;
}
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
lean_dec(x_16);
switch (x_17) {
case 0:
{
lean_dec(x_2);
goto block_4;
}
case 3:
{
lean_dec(x_2);
goto block_4;
}
default: 
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = l_Lean_Compiler_checkIsDefinition___closed__1;
x_19 = 1;
x_20 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_19);
x_21 = lean_string_append(x_18, x_20);
lean_dec_ref(x_20);
x_22 = l_Lean_Compiler_checkIsDefinition___closed__2;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_25 = l_Lean_Compiler_checkIsDefinition___closed__3;
x_26 = 1;
x_27 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_26);
x_28 = lean_string_append(x_25, x_27);
lean_dec_ref(x_27);
x_29 = l_Lean_Compiler_checkIsDefinition___closed__4;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
block_4:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_checkIsDefinition___closed__0;
return x_3;
}
}
}
static lean_object* _init_l_Lean_Compiler_mkUnsafeRecName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_unsafe_rec", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUnsafeRecName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_mkUnsafeRecName___closed__0;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isUnsafeRecName_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Compiler_mkUnsafeRecName___closed__0;
x_5 = lean_string_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
lean_inc(x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isUnsafeRecName_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_isUnsafeRecName_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Lean_Environment(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Old(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0 = _init_l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0();
lean_mark_persistent(l_Lean_Compiler_mkEagerLambdaLiftingName___closed__0);
l_Lean_Compiler_isEagerLambdaLiftingName___closed__0 = _init_l_Lean_Compiler_isEagerLambdaLiftingName___closed__0();
lean_mark_persistent(l_Lean_Compiler_isEagerLambdaLiftingName___closed__0);
l_Lean_Compiler_isEagerLambdaLiftingName___closed__1 = _init_l_Lean_Compiler_isEagerLambdaLiftingName___closed__1();
lean_mark_persistent(l_Lean_Compiler_isEagerLambdaLiftingName___closed__1);
l_Lean_Compiler_getDeclNamesForCodeGen___closed__0 = _init_l_Lean_Compiler_getDeclNamesForCodeGen___closed__0();
lean_mark_persistent(l_Lean_Compiler_getDeclNamesForCodeGen___closed__0);
l_Lean_Compiler_getDeclNamesForCodeGen___closed__1 = _init_l_Lean_Compiler_getDeclNamesForCodeGen___closed__1();
lean_mark_persistent(l_Lean_Compiler_getDeclNamesForCodeGen___closed__1);
l_Lean_Compiler_checkIsDefinition___closed__0 = _init_l_Lean_Compiler_checkIsDefinition___closed__0();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__0);
l_Lean_Compiler_checkIsDefinition___closed__1 = _init_l_Lean_Compiler_checkIsDefinition___closed__1();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__1);
l_Lean_Compiler_checkIsDefinition___closed__2 = _init_l_Lean_Compiler_checkIsDefinition___closed__2();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__2);
l_Lean_Compiler_checkIsDefinition___closed__3 = _init_l_Lean_Compiler_checkIsDefinition___closed__3();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__3);
l_Lean_Compiler_checkIsDefinition___closed__4 = _init_l_Lean_Compiler_checkIsDefinition___closed__4();
lean_mark_persistent(l_Lean_Compiler_checkIsDefinition___closed__4);
l_Lean_Compiler_mkUnsafeRecName___closed__0 = _init_l_Lean_Compiler_mkUnsafeRecName___closed__0();
lean_mark_persistent(l_Lean_Compiler_mkUnsafeRecName___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
