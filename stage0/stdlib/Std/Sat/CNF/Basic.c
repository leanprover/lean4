// Lean compiler output
// Module: Std.Sat.CNF.Basic
// Imports: Init.Data.List.Lemmas Init.Data.List.Impl Std.Sat.CNF.Literal
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
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemOfDecidableEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq___redArg___lam__0___boxed(lean_object*);
static lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t l_List_decidableBEx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___redArg___lam__0___boxed(lean_object*, lean_object*);
uint8_t l_List_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq___redArg___lam__0(lean_object*);
lean_object* l_instDecidableEqBool___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemOfDecidableEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq(lean_object*, lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_unbox(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_unbox(x_5);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l_Std_Sat_CNF_Clause_eval___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_List_any___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_eval(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_Sat_CNF_Clause_eval___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Sat_CNF_Clause_eval___redArg___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Sat_CNF_Clause_eval___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_eval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Sat_CNF_Clause_eval(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_Sat_CNF_Clause_eval___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l_Std_Sat_CNF_eval___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_List_all___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_eval(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_Sat_CNF_eval___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Sat_CNF_eval___redArg___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Sat_CNF_eval___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_eval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Sat_CNF_eval(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
x_2 = l_instBEqOfDecidableEq___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = l_instBEqOfDecidableEq___redArg(x_3);
x_5 = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___closed__0;
x_6 = l_instBEqProd___redArg(x_4, x_5);
x_7 = 0;
x_8 = lean_box(x_7);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_2);
lean_inc_ref(x_6);
x_10 = l_List_elem___redArg(x_6, x_9, x_2);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_List_elem___redArg(x_6, x_13, x_2);
return x_14;
}
else
{
lean_dec_ref(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemOfDecidableEq___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemOfDecidableEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_alloc_closure((void*)(l_Std_Sat_CNF_instDecidableMemOfDecidableEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = l_List_decidableBEx___redArg(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableMemOfDecidableEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Std_Sat_CNF_instDecidableMemOfDecidableEq___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemOfDecidableEq___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Sat_CNF_instDecidableMemOfDecidableEq___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemOfDecidableEq___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Sat_CNF_instDecidableMemOfDecidableEq___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableMemOfDecidableEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_Sat_CNF_instDecidableMemOfDecidableEq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq___redArg___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_List_isEmpty___redArg(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq___redArg___lam__0___boxed), 1, 0);
x_3 = l_List_any___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq___redArg___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq___redArg(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_CNF_Literal(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Literal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___closed__0 = _init_l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___closed__0();
lean_mark_persistent(l_Std_Sat_CNF_Clause_instDecidableMemOfDecidableEq___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
