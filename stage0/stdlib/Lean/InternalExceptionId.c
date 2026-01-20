// Lean compiler output
// Module: Lean.InternalExceptionId
// Imports: public import Init.System.IO import Init.Data.ToString.Name
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_InternalExceptionId_getName___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* l_Lean_InternalExceptionId_toString___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedInternalExceptionId;
LEAN_EXPORT lean_object* l_Lean_instBEqInternalExceptionId_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Lean_instBEqInternalExceptionId___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerInternalExceptionId(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerInternalExceptionId___boxed(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_internalExceptionsRef;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_();
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqInternalExceptionId;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_registerInternalExceptionId___closed__0;
LEAN_EXPORT lean_object* l_Lean_InternalExceptionId_toString(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
static lean_object* l_Lean_InternalExceptionId_getName___closed__0;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_InternalExceptionId_getName___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedInternalExceptionId_default;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_registerInternalExceptionId___closed__1;
static lean_object* l_Lean_initFn___closed__0_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_;
static lean_object* _init_l_Lean_instInhabitedInternalExceptionId_default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedInternalExceptionId() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqInternalExceptionId_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_instBEqInternalExceptionId_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqInternalExceptionId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_instBEqInternalExceptionId_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqInternalExceptionId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqInternalExceptionId___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__0_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn___closed__0_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_;
x_3 = lean_st_mk_ref(x_2);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_name_eq(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_5;
}
else
{
if (x_5 == 0)
{
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_registerInternalExceptionId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid internal exception id, '", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_registerInternalExceptionId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' has already been used", 23, 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_registerInternalExceptionId(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_internalExceptionsRef;
x_4 = lean_st_ref_get(x_3);
x_5 = l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_st_ref_take(x_3);
x_7 = lean_array_push(x_6, x_1);
x_8 = lean_st_ref_set(x_3, x_7);
x_9 = lean_array_get_size(x_4);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_11 = l_Lean_registerInternalExceptionId___closed__0;
x_12 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_5);
x_13 = lean_string_append(x_11, x_12);
lean_dec_ref(x_12);
x_14 = l_Lean_registerInternalExceptionId___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_mk_io_user_error(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerInternalExceptionId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_registerInternalExceptionId(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_InternalExceptionId_toString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal exception #", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_InternalExceptionId_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_InternalExceptionId_toString___closed__0;
x_3 = l_Nat_reprFast(x_1);
x_4 = lean_string_append(x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_InternalExceptionId_getName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid internal exception id", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_InternalExceptionId_getName___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_InternalExceptionId_getName___closed__0;
x_2 = lean_mk_io_user_error(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_InternalExceptionId_getName(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lean_internalExceptionsRef;
x_4 = lean_st_ref_get(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = l_Lean_InternalExceptionId_getName___closed__1;
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_4, x_1);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_InternalExceptionId_getName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_InternalExceptionId_getName(x_1);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_InternalExceptionId(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedInternalExceptionId_default = _init_l_Lean_instInhabitedInternalExceptionId_default();
lean_mark_persistent(l_Lean_instInhabitedInternalExceptionId_default);
l_Lean_instInhabitedInternalExceptionId = _init_l_Lean_instInhabitedInternalExceptionId();
lean_mark_persistent(l_Lean_instInhabitedInternalExceptionId);
l_Lean_instBEqInternalExceptionId___closed__0 = _init_l_Lean_instBEqInternalExceptionId___closed__0();
lean_mark_persistent(l_Lean_instBEqInternalExceptionId___closed__0);
l_Lean_instBEqInternalExceptionId = _init_l_Lean_instBEqInternalExceptionId();
lean_mark_persistent(l_Lean_instBEqInternalExceptionId);
l_Lean_initFn___closed__0_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_ = _init_l_Lean_initFn___closed__0_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___closed__0_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_);
if (builtin) {res = l_Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_internalExceptionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_internalExceptionsRef);
lean_dec_ref(res);
}l_Lean_registerInternalExceptionId___closed__0 = _init_l_Lean_registerInternalExceptionId___closed__0();
lean_mark_persistent(l_Lean_registerInternalExceptionId___closed__0);
l_Lean_registerInternalExceptionId___closed__1 = _init_l_Lean_registerInternalExceptionId___closed__1();
lean_mark_persistent(l_Lean_registerInternalExceptionId___closed__1);
l_Lean_InternalExceptionId_toString___closed__0 = _init_l_Lean_InternalExceptionId_toString___closed__0();
lean_mark_persistent(l_Lean_InternalExceptionId_toString___closed__0);
l_Lean_InternalExceptionId_getName___closed__0 = _init_l_Lean_InternalExceptionId_getName___closed__0();
lean_mark_persistent(l_Lean_InternalExceptionId_getName___closed__0);
l_Lean_InternalExceptionId_getName___closed__1 = _init_l_Lean_InternalExceptionId_getName___closed__1();
lean_mark_persistent(l_Lean_InternalExceptionId_getName___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
