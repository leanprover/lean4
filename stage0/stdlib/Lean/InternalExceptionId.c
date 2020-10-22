// Lean compiler output
// Module: Lean.InternalExceptionId
// Imports: Init
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
lean_object* l_Lean_InternalExceptionId_toString(lean_object*);
uint8_t l_Lean_Lean_InternalExceptionId___instance__2(lean_object*, lean_object*);
lean_object* l_Lean_registerInternalExceptionId___closed__1;
lean_object* l_Lean_InternalExceptionId_toString___closed__1;
lean_object* l_Lean_registerInternalExceptionId___closed__2;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_InternalExceptionId_getName___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_registerInternalExceptionId___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Lean_InternalExceptionId___instance__2___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_initFn____x40_Lean_InternalExceptionId___hyg_27____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_registerInternalExceptionId___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*, lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
lean_object* l_Lean_InternalExceptionId_getName___closed__2;
lean_object* l_Array_anyRangeMAux___main___at_Lean_registerInternalExceptionId___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InternalExceptionId_idx___default;
lean_object* l_Array_contains___at_Lean_registerInternalExceptionId___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_registerInternalExceptionId___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InternalExceptionId_getName___boxed(lean_object*, lean_object*);
lean_object* l_Lean_internalExceptionsRef;
lean_object* l_Lean_initFn____x40_Lean_InternalExceptionId___hyg_27_(lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Lean_Lean_InternalExceptionId___instance__1;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_InternalExceptionId_idx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Lean_InternalExceptionId___instance__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
uint8_t l_Lean_Lean_InternalExceptionId___instance__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Lean_InternalExceptionId___instance__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Lean_InternalExceptionId___instance__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_IO_mkRef___at_Lean_initFn____x40_Lean_InternalExceptionId___hyg_27____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
lean_object* l_Lean_initFn____x40_Lean_InternalExceptionId___hyg_27_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = l_IO_mkRef___at_Lean_initFn____x40_Lean_InternalExceptionId___hyg_27____spec__1(x_2, x_1);
return x_3;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_registerInternalExceptionId___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_name_eq(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
uint8_t l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at_Lean_registerInternalExceptionId___spec__2(x_1, x_2, x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_registerInternalExceptionId___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_array_get_size(x_1);
x_6 = l_Lean_internalExceptionsRef;
x_7 = lean_st_ref_take(x_6, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_array_push(x_8, x_2);
x_11 = lean_st_ref_set(x_6, x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
static lean_object* _init_l_Lean_registerInternalExceptionId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid internal exception id, '");
return x_1;
}
}
static lean_object* _init_l_Lean_registerInternalExceptionId___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already been used");
return x_1;
}
}
lean_object* l_Lean_registerInternalExceptionId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_internalExceptionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_6, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_free_object(x_4);
x_9 = lean_box(0);
x_10 = l_Lean_registerInternalExceptionId___lambda__1(x_6, x_1, x_9, x_7);
lean_dec(x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
x_11 = l_System_FilePath_dirName___closed__1;
x_12 = l_Lean_Name_toStringWithSep___main(x_11, x_1);
x_13 = l_Lean_registerInternalExceptionId___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lean_registerInternalExceptionId___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_17);
return x_4;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_18, x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_registerInternalExceptionId___lambda__1(x_18, x_1, x_21, x_19);
lean_dec(x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_18);
x_23 = l_System_FilePath_dirName___closed__1;
x_24 = l_Lean_Name_toStringWithSep___main(x_23, x_1);
x_25 = l_Lean_registerInternalExceptionId___closed__1;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_Lean_registerInternalExceptionId___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_19);
return x_30;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_registerInternalExceptionId___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_registerInternalExceptionId___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_contains___at_Lean_registerInternalExceptionId___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_registerInternalExceptionId___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_registerInternalExceptionId___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_InternalExceptionId_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("internal exception #");
return x_1;
}
}
lean_object* l_Lean_InternalExceptionId_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Nat_repr(x_1);
x_3 = l_Lean_InternalExceptionId_toString___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = l_String_splitAux___main___closed__1;
x_6 = lean_string_append(x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_InternalExceptionId_getName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid internal exception id");
return x_1;
}
}
static lean_object* _init_l_Lean_InternalExceptionId_getName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_InternalExceptionId_getName___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_InternalExceptionId_getName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_internalExceptionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_array_get_size(x_6);
x_8 = lean_nat_dec_lt(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
x_9 = l_Lean_InternalExceptionId_getName___closed__2;
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; 
x_10 = lean_array_fget(x_6, x_1);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_1, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
x_15 = l_Lean_InternalExceptionId_getName___closed__2;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fget(x_11, x_1);
lean_dec(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
}
}
}
lean_object* l_Lean_InternalExceptionId_getName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_InternalExceptionId_getName(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_InternalExceptionId(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_InternalExceptionId_idx___default = _init_l_Lean_InternalExceptionId_idx___default();
lean_mark_persistent(l_Lean_InternalExceptionId_idx___default);
l_Lean_Lean_InternalExceptionId___instance__1 = _init_l_Lean_Lean_InternalExceptionId___instance__1();
lean_mark_persistent(l_Lean_Lean_InternalExceptionId___instance__1);
res = l_Lean_initFn____x40_Lean_InternalExceptionId___hyg_27_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_internalExceptionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_internalExceptionsRef);
lean_dec_ref(res);
l_Lean_registerInternalExceptionId___closed__1 = _init_l_Lean_registerInternalExceptionId___closed__1();
lean_mark_persistent(l_Lean_registerInternalExceptionId___closed__1);
l_Lean_registerInternalExceptionId___closed__2 = _init_l_Lean_registerInternalExceptionId___closed__2();
lean_mark_persistent(l_Lean_registerInternalExceptionId___closed__2);
l_Lean_InternalExceptionId_toString___closed__1 = _init_l_Lean_InternalExceptionId_toString___closed__1();
lean_mark_persistent(l_Lean_InternalExceptionId_toString___closed__1);
l_Lean_InternalExceptionId_getName___closed__1 = _init_l_Lean_InternalExceptionId_getName___closed__1();
lean_mark_persistent(l_Lean_InternalExceptionId_getName___closed__1);
l_Lean_InternalExceptionId_getName___closed__2 = _init_l_Lean_InternalExceptionId_getName___closed__2();
lean_mark_persistent(l_Lean_InternalExceptionId_getName___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
