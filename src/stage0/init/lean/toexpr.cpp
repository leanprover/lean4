// Lean compiler output
// Module: init.lean.toexpr
// Imports: init.lean.expr
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
extern "C" {
obj* l_Lean_strToExpr(obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_Lean_nameToExprAux___main___closed__3;
obj* l_Lean_nameToExprAux___main___closed__1;
obj* lean_expr_mk_const(obj*, obj*);
obj* l_Lean_nameToExprAux___main___closed__7;
obj* l_Lean_nameToExprAux___main___closed__8;
obj* l_Lean_mkBinCApp(obj*, obj*, obj*);
obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_nameToExprAux___main(obj*);
obj* l_Lean_nameToExprAux___main___closed__6;
obj* l_Lean_nameToExprAux(obj*);
obj* l_Lean_nameToExprAux___main___closed__9;
obj* l_Lean_nameToExprAux___main___closed__5;
obj* l_Lean_nameToExprAux___main___closed__4;
obj* l_Lean_exprToExpr;
obj* l_Lean_nameToExpr;
obj* l_Lean_natToExpr(obj*);
obj* l_Lean_nameToExprAux___main___closed__2;
obj* lean_expr_mk_lit(obj*);
obj* l_Lean_nameToExpr___closed__1;
obj* _init_l_Lean_exprToExpr() {
_start:
{
obj* x_1; 
x_1 = l_mjoin___rarg___closed__1;
return x_1;
}
}
obj* l_Lean_natToExpr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean_expr_mk_lit(x_2);
return x_3;
}
}
obj* l_Lean_strToExpr(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean_expr_mk_lit(x_2);
return x_3;
}
}
obj* _init_l_Lean_nameToExprAux___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("Lean");
return x_1;
}
}
obj* _init_l_Lean_nameToExprAux___main___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("Name");
return x_1;
}
}
obj* _init_l_Lean_nameToExprAux___main___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("anonymous");
return x_1;
}
}
obj* _init_l_Lean_nameToExprAux___main___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_nameToExprAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_nameToExprAux___main___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__4;
x_2 = l_Lean_nameToExprAux___main___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_nameToExprAux___main___closed__6() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("mkString");
return x_1;
}
}
obj* _init_l_Lean_nameToExprAux___main___closed__7() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__5;
x_2 = l_Lean_nameToExprAux___main___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_nameToExprAux___main___closed__8() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("mkNumeral");
return x_1;
}
}
obj* _init_l_Lean_nameToExprAux___main___closed__9() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_nameToExprAux___main___closed__5;
x_2 = l_Lean_nameToExprAux___main___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_nameToExprAux___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = l_Lean_nameToExprAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = l_Lean_nameToExprAux___main___closed__2;
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = l_Lean_nameToExprAux___main___closed__3;
x_7 = lean_name_mk_string(x_5, x_6);
x_8 = lean::box(0);
x_9 = lean_expr_mk_const(x_7, x_8);
return x_9;
}
case 1:
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
lean::dec(x_1);
x_12 = l_Lean_nameToExprAux___main(x_10);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_11);
x_14 = lean_expr_mk_lit(x_13);
x_15 = l_Lean_nameToExprAux___main___closed__7;
x_16 = l_Lean_mkBinCApp(x_15, x_12, x_14);
return x_16;
}
default: 
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_17 = lean::cnstr_get(x_1, 0);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_1, 1);
lean::inc(x_18);
lean::dec(x_1);
x_19 = l_Lean_nameToExprAux___main(x_17);
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_18);
x_21 = lean_expr_mk_lit(x_20);
x_22 = l_Lean_nameToExprAux___main___closed__9;
x_23 = l_Lean_mkBinCApp(x_22, x_19, x_21);
return x_23;
}
}
}
}
obj* l_Lean_nameToExprAux(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_nameToExprAux___main(x_1);
return x_2;
}
}
obj* _init_l_Lean_nameToExpr___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_nameToExprAux), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_nameToExpr() {
_start:
{
obj* x_1; 
x_1 = l_Lean_nameToExpr___closed__1;
return x_1;
}
}
obj* initialize_init_lean_expr(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_toexpr(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_expr(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_exprToExpr = _init_l_Lean_exprToExpr();
lean::mark_persistent(l_Lean_exprToExpr);
l_Lean_nameToExprAux___main___closed__1 = _init_l_Lean_nameToExprAux___main___closed__1();
lean::mark_persistent(l_Lean_nameToExprAux___main___closed__1);
l_Lean_nameToExprAux___main___closed__2 = _init_l_Lean_nameToExprAux___main___closed__2();
lean::mark_persistent(l_Lean_nameToExprAux___main___closed__2);
l_Lean_nameToExprAux___main___closed__3 = _init_l_Lean_nameToExprAux___main___closed__3();
lean::mark_persistent(l_Lean_nameToExprAux___main___closed__3);
l_Lean_nameToExprAux___main___closed__4 = _init_l_Lean_nameToExprAux___main___closed__4();
lean::mark_persistent(l_Lean_nameToExprAux___main___closed__4);
l_Lean_nameToExprAux___main___closed__5 = _init_l_Lean_nameToExprAux___main___closed__5();
lean::mark_persistent(l_Lean_nameToExprAux___main___closed__5);
l_Lean_nameToExprAux___main___closed__6 = _init_l_Lean_nameToExprAux___main___closed__6();
lean::mark_persistent(l_Lean_nameToExprAux___main___closed__6);
l_Lean_nameToExprAux___main___closed__7 = _init_l_Lean_nameToExprAux___main___closed__7();
lean::mark_persistent(l_Lean_nameToExprAux___main___closed__7);
l_Lean_nameToExprAux___main___closed__8 = _init_l_Lean_nameToExprAux___main___closed__8();
lean::mark_persistent(l_Lean_nameToExprAux___main___closed__8);
l_Lean_nameToExprAux___main___closed__9 = _init_l_Lean_nameToExprAux___main___closed__9();
lean::mark_persistent(l_Lean_nameToExprAux___main___closed__9);
l_Lean_nameToExpr___closed__1 = _init_l_Lean_nameToExpr___closed__1();
lean::mark_persistent(l_Lean_nameToExpr___closed__1);
l_Lean_nameToExpr = _init_l_Lean_nameToExpr();
lean::mark_persistent(l_Lean_nameToExpr);
return w;
}
}
