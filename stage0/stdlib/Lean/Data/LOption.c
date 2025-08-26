// Lean compiler output
// Module: Lean.Data.LOption
// Imports: Init.Data.ToString.Basic
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
LEAN_EXPORT lean_object* l_toLOptionM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption(lean_object*);
static lean_object* l_Lean_instToStringLOption___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Option_toLOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_beqLOption____x40_Lean_Data_LOption_3089415665____hygCtx___hyg_34_(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToStringLOption___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_toLOptionM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_beqLOption____x40_Lean_Data_LOption_3089415665____hygCtx___hyg_34____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToStringLOption___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_instToStringLOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_beqLOption___redArg____x40_Lean_Data_LOption_3089415665____hygCtx___hyg_34____boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instToStringLOption___redArg___lam__0___closed__3;
LEAN_EXPORT uint8_t l_Lean_beqLOption___redArg____x40_Lean_Data_LOption_3089415665____hygCtx___hyg_34_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqLOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_toLOptionM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToStringLOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_toOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToStringLOption___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_toOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toLOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqLOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LOption_ctorIdx___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LOption_ctorIdx___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LOption_ctorIdx(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_beqLOption___redArg____x40_Lean_Data_LOption_3089415665____hygCtx___hyg_34_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_dec_ref(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
case 1:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = lean_apply_2(x_1, x_6, x_7);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_10 = 0;
return x_10;
}
}
default: 
{
lean_dec_ref(x_1);
if (lean_obj_tag(x_3) == 2)
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_3);
x_12 = 0;
return x_12;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_beqLOption____x40_Lean_Data_LOption_3089415665____hygCtx___hyg_34_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_beqLOption___redArg____x40_Lean_Data_LOption_3089415665____hygCtx___hyg_34_(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_beqLOption___redArg____x40_Lean_Data_LOption_3089415665____hygCtx___hyg_34____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_beqLOption___redArg____x40_Lean_Data_LOption_3089415665____hygCtx___hyg_34_(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_beqLOption____x40_Lean_Data_LOption_3089415665____hygCtx___hyg_34____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_beqLOption____x40_Lean_Data_LOption_3089415665____hygCtx___hyg_34_(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_beqLOption____x40_Lean_Data_LOption_3089415665____hygCtx___hyg_34____boxed), 4, 2);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_beqLOption____x40_Lean_Data_LOption_3089415665____hygCtx___hyg_34____boxed), 4, 2);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToStringLOption___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("none", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_instToStringLOption___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(some ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_instToStringLOption___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_instToStringLOption___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("undef", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringLOption___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = l_Lean_instToStringLOption___redArg___lam__0___closed__0;
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_instToStringLOption___redArg___lam__0___closed__1;
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_string_append(x_5, x_6);
lean_dec_ref(x_6);
x_8 = l_Lean_instToStringLOption___redArg___lam__0___closed__2;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
default: 
{
lean_object* x_10; 
lean_dec_ref(x_1);
x_10 = l_Lean_instToStringLOption___redArg___lam__0___closed__3;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringLOption___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToStringLOption___redArg___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringLOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instToStringLOption___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_toOption___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_toOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LOption_toOption___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_toLOption___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_toLOption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_toLOption___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_toLOptionM___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Option_toLOption___redArg(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_toLOptionM___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_alloc_closure((void*)(l_toLOptionM___redArg___lam__0), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_toLOptionM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = lean_alloc_closure((void*)(l_toLOptionM___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_4, x_8);
return x_9;
}
}
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_LOption(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instToStringLOption___redArg___lam__0___closed__0 = _init_l_Lean_instToStringLOption___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_instToStringLOption___redArg___lam__0___closed__0);
l_Lean_instToStringLOption___redArg___lam__0___closed__1 = _init_l_Lean_instToStringLOption___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_instToStringLOption___redArg___lam__0___closed__1);
l_Lean_instToStringLOption___redArg___lam__0___closed__2 = _init_l_Lean_instToStringLOption___redArg___lam__0___closed__2();
lean_mark_persistent(l_Lean_instToStringLOption___redArg___lam__0___closed__2);
l_Lean_instToStringLOption___redArg___lam__0___closed__3 = _init_l_Lean_instToStringLOption___redArg___lam__0___closed__3();
lean_mark_persistent(l_Lean_instToStringLOption___redArg___lam__0___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
