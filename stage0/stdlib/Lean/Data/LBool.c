// Lean compiler output
// Module: Lean.Data.LBool
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
LEAN_EXPORT uint8_t l_Bool_toLBool(uint8_t);
LEAN_EXPORT lean_object* l_Lean_LBool_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Bool_toLBool___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_19____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_toLBoolM___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_toLBoolM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LBool_and(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Lean_instInhabitedLBool;
LEAN_EXPORT uint8_t l_Lean_LBool_neg(uint8_t);
LEAN_EXPORT lean_object* l_Lean_LBool_toString(uint8_t);
static lean_object* l_Lean_LBool_toString___closed__2;
LEAN_EXPORT lean_object* l_Lean_LBool_and___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LBool_toString___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_19_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LBool_neg___boxed(lean_object*);
static lean_object* l_Lean_instBEqLBool___closed__0;
LEAN_EXPORT lean_object* l_Lean_LBool_instToString;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_LBool_instToString___closed__0;
LEAN_EXPORT lean_object* l_Lean_LBool_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_LBool_toString___closed__1;
static lean_object* l_Lean_LBool_toString___closed__0;
LEAN_EXPORT lean_object* l_Lean_LBool_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_toLBoolM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_toLBoolM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqLBool;
LEAN_EXPORT lean_object* l_Lean_LBool_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
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
LEAN_EXPORT lean_object* l_Lean_LBool_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_LBool_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_LBool_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_LBool_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LBool_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_LBool_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_Lean_LBool_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_instInhabitedLBool() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_19_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_LBool_toCtorIdx(x_1);
x_4 = l_Lean_LBool_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_19____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_19_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instBEqLBool___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_beqLBool____x40_Lean_Data_LBool___hyg_19____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_instBEqLBool() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instBEqLBool___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_LBool_neg(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 1:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
default: 
{
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_neg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_LBool_neg(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_LBool_and(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 1)
{
return x_2;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_and___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_LBool_and(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_LBool_toString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_LBool_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_LBool_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("undef", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_toString(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_LBool_toString___closed__0;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_LBool_toString___closed__1;
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = l_Lean_LBool_toString___closed__2;
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LBool_toString___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_LBool_toString(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_LBool_instToString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_LBool_toString___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_LBool_instToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LBool_instToString___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Bool_toLBool(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Bool_toLBool___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = l_Bool_toLBool(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_toLBoolM___redArg___lam__0(lean_object* x_1, uint8_t x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Bool_toLBool(x_2);
x_4 = lean_box(x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_toLBoolM___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_3);
x_6 = lean_alloc_closure((void*)(l_toLBoolM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_toLBoolM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_4);
x_7 = lean_alloc_closure((void*)(l_toLBoolM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_toLBoolM___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_toLBoolM___redArg___lam__0(x_1, x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_LBool(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedLBool = _init_l_Lean_instInhabitedLBool();
l_Lean_instBEqLBool___closed__0 = _init_l_Lean_instBEqLBool___closed__0();
lean_mark_persistent(l_Lean_instBEqLBool___closed__0);
l_Lean_instBEqLBool = _init_l_Lean_instBEqLBool();
lean_mark_persistent(l_Lean_instBEqLBool);
l_Lean_LBool_toString___closed__0 = _init_l_Lean_LBool_toString___closed__0();
lean_mark_persistent(l_Lean_LBool_toString___closed__0);
l_Lean_LBool_toString___closed__1 = _init_l_Lean_LBool_toString___closed__1();
lean_mark_persistent(l_Lean_LBool_toString___closed__1);
l_Lean_LBool_toString___closed__2 = _init_l_Lean_LBool_toString___closed__2();
lean_mark_persistent(l_Lean_LBool_toString___closed__2);
l_Lean_LBool_instToString___closed__0 = _init_l_Lean_LBool_instToString___closed__0();
lean_mark_persistent(l_Lean_LBool_instToString___closed__0);
l_Lean_LBool_instToString = _init_l_Lean_LBool_instToString();
lean_mark_persistent(l_Lean_LBool_instToString);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
