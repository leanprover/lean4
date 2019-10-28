// Lean compiler output
// Module: Init.Lean.ToExpr
// Imports: Init.Lean.Expr
#include "runtime/lean.h"
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
lean_object* l_Lean_strToExpr(lean_object*);
lean_object* l_Lean_nameToExprAux___main___closed__3;
lean_object* l_Lean_nameToExprAux___main___closed__1;
lean_object* lean_expr_mk_const(lean_object*, lean_object*);
lean_object* l_Lean_nameToExprAux___main___closed__7;
lean_object* l_Lean_nameToExprAux___main___closed__8;
lean_object* l_Lean_mkBinCApp(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_nameToExprAux___main(lean_object*);
lean_object* l_Lean_nameToExprAux___main___closed__6;
lean_object* l_Lean_nameToExprAux(lean_object*);
lean_object* l_Lean_nameToExprAux___main___closed__9;
lean_object* l_Lean_nameToExprAux___main___closed__5;
lean_object* l_Lean_nameToExprAux___main___closed__4;
lean_object* l_Lean_exprToExpr;
lean_object* l_Lean_nameToExpr;
lean_object* l_Lean_natToExpr(lean_object*);
lean_object* l_Lean_nameToExprAux___main___closed__2;
lean_object* lean_expr_mk_lit(lean_object*);
extern lean_object* l_joinM___rarg___closed__1;
lean_object* l_Lean_nameToExpr___closed__1;
lean_object* _init_l_Lean_exprToExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_joinM___rarg___closed__1;
return x_1;
}
}
lean_object* l_Lean_natToExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_expr_mk_lit(x_2);
return x_3;
}
}
lean_object* l_Lean_strToExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_expr_mk_lit(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_nameToExprAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
lean_object* _init_l_Lean_nameToExprAux___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name");
return x_1;
}
}
lean_object* _init_l_Lean_nameToExprAux___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("anonymous");
return x_1;
}
}
lean_object* _init_l_Lean_nameToExprAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_nameToExprAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_nameToExprAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__4;
x_2 = l_Lean_nameToExprAux___main___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_nameToExprAux___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkString");
return x_1;
}
}
lean_object* _init_l_Lean_nameToExprAux___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__5;
x_2 = l_Lean_nameToExprAux___main___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_nameToExprAux___main___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkNumeral");
return x_1;
}
}
lean_object* _init_l_Lean_nameToExprAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__5;
x_2 = l_Lean_nameToExprAux___main___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_nameToExprAux___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_Lean_nameToExprAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = l_Lean_nameToExprAux___main___closed__2;
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = l_Lean_nameToExprAux___main___closed__3;
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean_box(0);
x_9 = lean_expr_mk_const(x_7, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_nameToExprAux___main(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_expr_mk_lit(x_13);
x_15 = l_Lean_nameToExprAux___main___closed__7;
x_16 = l_Lean_mkBinCApp(x_15, x_12, x_14);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Lean_nameToExprAux___main(x_17);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_expr_mk_lit(x_20);
x_22 = l_Lean_nameToExprAux___main___closed__9;
x_23 = l_Lean_mkBinCApp(x_22, x_19, x_21);
return x_23;
}
}
}
}
lean_object* l_Lean_nameToExprAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_nameToExprAux___main(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_nameToExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_nameToExprAux), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_nameToExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_nameToExpr___closed__1;
return x_1;
}
}
lean_object* initialize_Init_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_ToExpr(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_exprToExpr = _init_l_Lean_exprToExpr();
lean_mark_persistent(l_Lean_exprToExpr);
l_Lean_nameToExprAux___main___closed__1 = _init_l_Lean_nameToExprAux___main___closed__1();
lean_mark_persistent(l_Lean_nameToExprAux___main___closed__1);
l_Lean_nameToExprAux___main___closed__2 = _init_l_Lean_nameToExprAux___main___closed__2();
lean_mark_persistent(l_Lean_nameToExprAux___main___closed__2);
l_Lean_nameToExprAux___main___closed__3 = _init_l_Lean_nameToExprAux___main___closed__3();
lean_mark_persistent(l_Lean_nameToExprAux___main___closed__3);
l_Lean_nameToExprAux___main___closed__4 = _init_l_Lean_nameToExprAux___main___closed__4();
lean_mark_persistent(l_Lean_nameToExprAux___main___closed__4);
l_Lean_nameToExprAux___main___closed__5 = _init_l_Lean_nameToExprAux___main___closed__5();
lean_mark_persistent(l_Lean_nameToExprAux___main___closed__5);
l_Lean_nameToExprAux___main___closed__6 = _init_l_Lean_nameToExprAux___main___closed__6();
lean_mark_persistent(l_Lean_nameToExprAux___main___closed__6);
l_Lean_nameToExprAux___main___closed__7 = _init_l_Lean_nameToExprAux___main___closed__7();
lean_mark_persistent(l_Lean_nameToExprAux___main___closed__7);
l_Lean_nameToExprAux___main___closed__8 = _init_l_Lean_nameToExprAux___main___closed__8();
lean_mark_persistent(l_Lean_nameToExprAux___main___closed__8);
l_Lean_nameToExprAux___main___closed__9 = _init_l_Lean_nameToExprAux___main___closed__9();
lean_mark_persistent(l_Lean_nameToExprAux___main___closed__9);
l_Lean_nameToExpr___closed__1 = _init_l_Lean_nameToExpr___closed__1();
lean_mark_persistent(l_Lean_nameToExpr___closed__1);
l_Lean_nameToExpr = _init_l_Lean_nameToExpr();
lean_mark_persistent(l_Lean_nameToExpr);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
