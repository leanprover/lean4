// Lean compiler output
// Module: Lean.Data.RArray
// Imports: Init.Data.RArray Lean.ToExpr
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_instToExprRArray___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn_go(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_get__eq__def_match__1_splitter(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RArray_toExpr___rarg___closed__7;
static lean_object* l_Lean_RArray_toExpr___rarg___closed__1;
static lean_object* l_Lean_RArray_toExpr___rarg___closed__8;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_RArray_toExpr___rarg___closed__5;
static lean_object* l_Lean_RArray_toExpr___rarg___closed__3;
static lean_object* l_Lean_RArray_toExpr___rarg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_get__eq__def_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprRArray___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn(lean_object*);
static lean_object* l_Lean_instToExprRArray___rarg___closed__1;
static lean_object* l_Lean_RArray_toExpr___rarg___closed__6;
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprRArray___rarg(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_RArray_toExpr___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprRArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_3, x_7);
x_9 = lean_nat_dec_eq(x_8, x_4);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_nat_add(x_3, x_4);
x_11 = lean_unsigned_to_nat(2u);
x_12 = lean_nat_div(x_10, x_11);
lean_dec(x_10);
lean_inc(x_2);
x_13 = l_Lean_RArray_ofFn_go___rarg(x_1, x_2, x_3, x_12, lean_box(0), lean_box(0));
lean_inc(x_12);
x_14 = l_Lean_RArray_ofFn_go___rarg(x_1, x_2, x_12, x_4, lean_box(0), lean_box(0));
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_apply_1(x_2, x_3);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RArray_ofFn_go___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_RArray_ofFn_go___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_RArray_ofFn_go___rarg(x_1, x_2, x_4, x_1, lean_box(0), lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RArray_ofFn___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofFn___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RArray_ofFn___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_array_fget(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_RArray_ofArray___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_RArray_ofFn_go___rarg(x_3, x_4, x_5, x_3, lean_box(0), lean_box(0));
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RArray_ofArray___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_ofArray___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RArray_ofArray___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_get__eq__def_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_3(x_3, x_6, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_RArray_0__Lean_RArray_get__eq__def_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Data_RArray_0__Lean_RArray_get__eq__def_match__1_splitter___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_RArray_toExpr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_RArray_toExpr___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("RArray", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_RArray_toExpr___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leaf", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_RArray_toExpr___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_RArray_toExpr___rarg___closed__1;
x_2 = l_Lean_RArray_toExpr___rarg___closed__2;
x_3 = l_Lean_RArray_toExpr___rarg___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_RArray_toExpr___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_RArray_toExpr___rarg___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_RArray_toExpr___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("branch", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_RArray_toExpr___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_RArray_toExpr___rarg___closed__1;
x_2 = l_Lean_RArray_toExpr___rarg___closed__2;
x_3 = l_Lean_RArray_toExpr___rarg___closed__6;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_RArray_toExpr___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_RArray_toExpr___rarg___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_apply_1(x_2, x_4);
x_6 = l_Lean_RArray_toExpr___rarg___closed__5;
x_7 = l_Lean_mkAppB(x_6, x_1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Lean_mkRawNatLit(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_RArray_toExpr___rarg(x_1, x_2, x_9);
lean_inc(x_1);
x_13 = l_Lean_RArray_toExpr___rarg(x_1, x_2, x_10);
x_14 = l_Lean_RArray_toExpr___rarg___closed__8;
x_15 = l_Lean_mkApp4(x_14, x_1, x_11, x_12, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RArray_toExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RArray_toExpr___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprRArray___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_RArray_toExpr___rarg(x_3, x_4, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_instToExprRArray___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_RArray_toExpr___rarg___closed__1;
x_2 = l_Lean_RArray_toExpr___rarg___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprRArray___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_instToExprRArray___rarg___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprRArray___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_instToExprRArray___rarg___lambda__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_instToExprRArray___rarg___closed__2;
x_5 = l_Lean_Expr_app___override(x_4, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprRArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instToExprRArray___rarg), 1, 0);
return x_2;
}
}
lean_object* initialize_Init_Data_RArray(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ToExpr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_RArray(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_RArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_RArray_toExpr___rarg___closed__1 = _init_l_Lean_RArray_toExpr___rarg___closed__1();
lean_mark_persistent(l_Lean_RArray_toExpr___rarg___closed__1);
l_Lean_RArray_toExpr___rarg___closed__2 = _init_l_Lean_RArray_toExpr___rarg___closed__2();
lean_mark_persistent(l_Lean_RArray_toExpr___rarg___closed__2);
l_Lean_RArray_toExpr___rarg___closed__3 = _init_l_Lean_RArray_toExpr___rarg___closed__3();
lean_mark_persistent(l_Lean_RArray_toExpr___rarg___closed__3);
l_Lean_RArray_toExpr___rarg___closed__4 = _init_l_Lean_RArray_toExpr___rarg___closed__4();
lean_mark_persistent(l_Lean_RArray_toExpr___rarg___closed__4);
l_Lean_RArray_toExpr___rarg___closed__5 = _init_l_Lean_RArray_toExpr___rarg___closed__5();
lean_mark_persistent(l_Lean_RArray_toExpr___rarg___closed__5);
l_Lean_RArray_toExpr___rarg___closed__6 = _init_l_Lean_RArray_toExpr___rarg___closed__6();
lean_mark_persistent(l_Lean_RArray_toExpr___rarg___closed__6);
l_Lean_RArray_toExpr___rarg___closed__7 = _init_l_Lean_RArray_toExpr___rarg___closed__7();
lean_mark_persistent(l_Lean_RArray_toExpr___rarg___closed__7);
l_Lean_RArray_toExpr___rarg___closed__8 = _init_l_Lean_RArray_toExpr___rarg___closed__8();
lean_mark_persistent(l_Lean_RArray_toExpr___rarg___closed__8);
l_Lean_instToExprRArray___rarg___closed__1 = _init_l_Lean_instToExprRArray___rarg___closed__1();
lean_mark_persistent(l_Lean_instToExprRArray___rarg___closed__1);
l_Lean_instToExprRArray___rarg___closed__2 = _init_l_Lean_instToExprRArray___rarg___closed__2();
lean_mark_persistent(l_Lean_instToExprRArray___rarg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
