// Lean compiler output
// Module: Lean.InternalExceptionId
// Imports: Init.System.IO
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
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_registerInternalExceptionId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_InternalExceptionId_toString___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedInternalExceptionId;
static lean_object* l_Lean_registerInternalExceptionId___closed__2;
LEAN_EXPORT lean_object* l_Lean_InternalExceptionId_getName(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Lean_instBEqInternalExceptionId___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___Lean_registerInternalExceptionId_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_30_(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_internalExceptionsRef;
LEAN_EXPORT lean_object* l_Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_30____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_registerInternalExceptionId___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqInternalExceptionId;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_InternalExceptionId___hyg_88_(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerInternalExceptionId___lam__0___boxed(lean_object*);
static lean_object* l_Lean_registerInternalExceptionId___closed__0;
LEAN_EXPORT lean_object* l_Lean_InternalExceptionId_toString(lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_InternalExceptionId___hyg_88_;
static lean_object* l_Lean_InternalExceptionId_getName___closed__0;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_InternalExceptionId_getName___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_registerInternalExceptionId___closed__1;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_registerInternalExceptionId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
static lean_object* _init_l_Lean_instInhabitedInternalExceptionId() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_30_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_30____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_30_(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l_Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId___hyg_30____boxed), 2, 0);
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
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_InternalExceptionId___hyg_88_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_InternalExceptionId___hyg_88_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_initFn___closed__0____x40_Lean_InternalExceptionId___hyg_88_;
x_3 = lean_st_mk_ref(x_2, x_1);
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_registerInternalExceptionId_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_registerInternalExceptionId_spec__0_spec__0(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_registerInternalExceptionId___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_registerInternalExceptionId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_internalExceptionsRef;
return x_1;
}
}
static lean_object* _init_l_Lean_registerInternalExceptionId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid internal exception id, '", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_registerInternalExceptionId___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' has already been used", 23, 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_registerInternalExceptionId(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_registerInternalExceptionId___closed__0;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(x_6, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_free_object(x_4);
x_9 = lean_st_ref_take(x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_array_push(x_10, x_1);
x_13 = lean_st_ref_set(x_3, x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_array_get_size(x_6);
lean_dec(x_6);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_array_get_size(x_6);
lean_dec(x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
x_20 = lean_alloc_closure((void*)(l_Lean_registerInternalExceptionId___lam__0___boxed), 1, 0);
x_21 = l_Lean_registerInternalExceptionId___closed__1;
x_22 = l_Lean_Name_toString(x_1, x_8, x_20);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = l_Lean_registerInternalExceptionId___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_26);
return x_4;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_29 = l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(x_27, x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_st_ref_take(x_3, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_push(x_31, x_1);
x_34 = lean_st_ref_set(x_3, x_33, x_32);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_array_get_size(x_27);
lean_dec(x_27);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_27);
x_39 = lean_alloc_closure((void*)(l_Lean_registerInternalExceptionId___lam__0___boxed), 1, 0);
x_40 = l_Lean_registerInternalExceptionId___closed__1;
x_41 = l_Lean_Name_toString(x_1, x_29, x_39);
x_42 = lean_string_append(x_40, x_41);
lean_dec(x_41);
x_43 = l_Lean_registerInternalExceptionId___closed__2;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_28);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_registerInternalExceptionId_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_registerInternalExceptionId_spec__0_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___Lean_registerInternalExceptionId_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_registerInternalExceptionId___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_registerInternalExceptionId___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
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
lean_dec(x_3);
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
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_InternalExceptionId_getName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_registerInternalExceptionId___closed__0;
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
x_9 = l_Lean_InternalExceptionId_getName___closed__1;
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
x_15 = l_Lean_InternalExceptionId_getName___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_InternalExceptionId_getName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_InternalExceptionId_getName(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_InternalExceptionId(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedInternalExceptionId = _init_l_Lean_instInhabitedInternalExceptionId();
lean_mark_persistent(l_Lean_instInhabitedInternalExceptionId);
l_Lean_instBEqInternalExceptionId___closed__0 = _init_l_Lean_instBEqInternalExceptionId___closed__0();
lean_mark_persistent(l_Lean_instBEqInternalExceptionId___closed__0);
l_Lean_instBEqInternalExceptionId = _init_l_Lean_instBEqInternalExceptionId();
lean_mark_persistent(l_Lean_instBEqInternalExceptionId);
l_Lean_initFn___closed__0____x40_Lean_InternalExceptionId___hyg_88_ = _init_l_Lean_initFn___closed__0____x40_Lean_InternalExceptionId___hyg_88_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_InternalExceptionId___hyg_88_);
if (builtin) {res = l_Lean_initFn____x40_Lean_InternalExceptionId___hyg_88_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_internalExceptionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_internalExceptionsRef);
lean_dec_ref(res);
}l_Lean_registerInternalExceptionId___closed__0 = _init_l_Lean_registerInternalExceptionId___closed__0();
lean_mark_persistent(l_Lean_registerInternalExceptionId___closed__0);
l_Lean_registerInternalExceptionId___closed__1 = _init_l_Lean_registerInternalExceptionId___closed__1();
lean_mark_persistent(l_Lean_registerInternalExceptionId___closed__1);
l_Lean_registerInternalExceptionId___closed__2 = _init_l_Lean_registerInternalExceptionId___closed__2();
lean_mark_persistent(l_Lean_registerInternalExceptionId___closed__2);
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
