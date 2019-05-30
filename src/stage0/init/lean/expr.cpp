// Lean compiler output
// Module: init.lean.expr
// Imports: init.lean.level init.lean.kvmap
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
extern "C" obj* lean_expr_mk_mdata(obj*, obj*);
obj* l_Lean_getAppFn___main(obj*);
obj* l_Lean_Expr_lam___boxed(obj*, obj*, obj*, obj*);
extern "C" uint8 lean_expr_quick_lt(obj*, obj*);
obj* l_Lean_Expr_hash___boxed(obj*);
obj* l_Lean_mkBinApp(obj*, obj*, obj*);
obj* l_Lean_MData_empty;
extern "C" obj* lean_expr_mk_sort(obj*);
obj* l_Lean_Expr_pi___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_getAppFn(obj*);
obj* l_Lean_exprIsInhabited;
extern "C" usize lean_expr_hash(obj*);
obj* l_Lean_getAppFn___main___boxed(obj*);
extern "C" obj* lean_expr_dbg_to_string(obj*);
obj* l_Lean_Expr_eqv___boxed(obj*, obj*);
extern "C" obj* lean_expr_mk_pi(obj*, uint8, obj*, obj*);
extern "C" obj* lean_expr_mk_app(obj*, obj*);
obj* l_Lean_Expr_quickLt___boxed(obj*, obj*);
extern "C" obj* lean_expr_mk_let(obj*, obj*, obj*, obj*);
obj* l_Lean_Expr_mkCapp(obj*, obj*);
obj* l_Lean_mkDecIsFalse___closed__1;
obj* l_Lean_Expr_sort___boxed(obj*);
extern "C" obj* lean_expr_mk_fvar(obj*);
extern "C" obj* lean_expr_mk_proj(obj*, obj*, obj*);
extern "C" obj* lean_expr_mk_const(obj*, obj*);
obj* l_Lean_Expr_bvar___boxed(obj*);
extern "C" uint8 lean_expr_eqv(obj*, obj*);
obj* l_List_foldl___main___at_Lean_Expr_mkApp___spec__1(obj*, obj*);
obj* l_Lean_MData_HasEmptyc;
obj* l_Lean_Expr_dbgToString___boxed(obj*);
obj* l_Lean_Expr_elet___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_mkDecIsTrue___closed__1;
obj* l_Lean_mkDecIsFalse(obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Expr_lit___boxed(obj*);
obj* l_Lean_Expr_app___boxed(obj*, obj*);
extern "C" obj* lean_expr_mk_mvar(obj*, obj*);
obj* l_Lean_getAppFn___boxed(obj*);
extern "C" obj* lean_expr_mk_bvar(obj*);
obj* l_Lean_Expr_proj___boxed(obj*, obj*, obj*);
extern "C" uint8 lean_expr_lt(obj*, obj*);
obj* l_Lean_mkDecIsTrue(obj*, obj*);
obj* l_Lean_Expr_const___boxed(obj*, obj*);
obj* l_Lean_Expr_fvar___boxed(obj*);
extern "C" obj* lean_expr_mk_lambda(obj*, uint8, obj*, obj*);
obj* l_Lean_Expr_mdata___boxed(obj*, obj*);
obj* l_Lean_Expr_HasBeq;
obj* l_Lean_Expr_mkApp(obj*, obj*);
obj* l_Lean_Expr_Hashable;
obj* l_Lean_Expr_mvar___boxed(obj*, obj*);
extern "C" obj* lean_expr_mk_lit(obj*);
obj* l_Lean_Expr_lt___boxed(obj*, obj*);
obj* _init_l_Lean_MData_empty() {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* _init_l_Lean_MData_HasEmptyc() {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* _init_l_Lean_exprIsInhabited() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Expr_bvar___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_expr_mk_bvar(x_1);
return x_2;
}
}
obj* l_Lean_Expr_fvar___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_expr_mk_fvar(x_1);
return x_2;
}
}
obj* l_Lean_Expr_mvar___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_expr_mk_mvar(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Expr_sort___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_expr_mk_sort(x_1);
return x_2;
}
}
obj* l_Lean_Expr_const___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_expr_mk_const(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Expr_app___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_expr_mk_app(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Expr_lam___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
x_6 = lean_expr_mk_lambda(x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* l_Lean_Expr_pi___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
x_6 = lean_expr_mk_pi(x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* l_Lean_Expr_elet___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean_expr_mk_let(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_Lean_Expr_lit___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_expr_mk_lit(x_1);
return x_2;
}
}
obj* l_Lean_Expr_mdata___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_expr_mk_mdata(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Expr_proj___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean_expr_mk_proj(x_1, x_2, x_3);
return x_4;
}
}
obj* l_List_foldl___main___at_Lean_Expr_mkApp___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean_expr_mk_app(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
obj* l_Lean_Expr_mkApp(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_foldl___main___at_Lean_Expr_mkApp___spec__1(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Expr_mkCapp(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::box(0);
x_4 = lean_expr_mk_const(x_1, x_3);
x_5 = l_List_foldl___main___at_Lean_Expr_mkApp___spec__1(x_4, x_2);
return x_5;
}
}
obj* l_Lean_Expr_hash___boxed(obj* x_1) {
_start:
{
usize x_2; obj* x_3; 
x_2 = lean_expr_hash(x_1);
x_3 = lean::box_size_t(x_2);
return x_3;
}
}
obj* _init_l_Lean_Expr_Hashable() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expr_hash___boxed), 1, 0);
return x_1;
}
}
obj* l_Lean_Expr_dbgToString___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_expr_dbg_to_string(x_1);
return x_2;
}
}
obj* l_Lean_Expr_quickLt___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean_expr_quick_lt(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_Expr_lt___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean_expr_lt(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Lean_Expr_eqv___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean_expr_eqv(x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* _init_l_Lean_Expr_HasBeq() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Expr_eqv___boxed), 2, 0);
return x_1;
}
}
obj* l_Lean_getAppFn___main(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 5)
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_1, 0);
x_1 = x_2;
goto _start;
}
else
{
lean::inc(x_1);
return x_1;
}
}
}
obj* l_Lean_getAppFn___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_getAppFn___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_getAppFn(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_getAppFn___main(x_1);
return x_2;
}
}
obj* l_Lean_getAppFn___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_getAppFn(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_mkBinApp(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean_expr_mk_app(x_1, x_2);
x_5 = lean_expr_mk_app(x_4, x_3);
return x_5;
}
}
obj* _init_l_Lean_mkDecIsTrue___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Decidable");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("isTrue");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::box(0);
x_7 = lean_expr_mk_const(x_5, x_6);
return x_7;
}
}
obj* l_Lean_mkDecIsTrue(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_mkDecIsTrue___closed__1;
x_4 = l_Lean_mkBinApp(x_3, x_1, x_2);
return x_4;
}
}
obj* _init_l_Lean_mkDecIsFalse___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Decidable");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("isFalse");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::box(0);
x_7 = lean_expr_mk_const(x_5, x_6);
return x_7;
}
}
obj* l_Lean_mkDecIsFalse(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_mkDecIsFalse___closed__1;
x_4 = l_Lean_mkBinApp(x_3, x_1, x_2);
return x_4;
}
}
obj* initialize_init_lean_level(obj*);
obj* initialize_init_lean_kvmap(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_expr(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_level(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_kvmap(w);
if (io_result_is_error(w)) return w;
l_Lean_MData_empty = _init_l_Lean_MData_empty();
lean::mark_persistent(l_Lean_MData_empty);
l_Lean_MData_HasEmptyc = _init_l_Lean_MData_HasEmptyc();
lean::mark_persistent(l_Lean_MData_HasEmptyc);
l_Lean_exprIsInhabited = _init_l_Lean_exprIsInhabited();
lean::mark_persistent(l_Lean_exprIsInhabited);
l_Lean_Expr_Hashable = _init_l_Lean_Expr_Hashable();
lean::mark_persistent(l_Lean_Expr_Hashable);
l_Lean_Expr_HasBeq = _init_l_Lean_Expr_HasBeq();
lean::mark_persistent(l_Lean_Expr_HasBeq);
l_Lean_mkDecIsTrue___closed__1 = _init_l_Lean_mkDecIsTrue___closed__1();
lean::mark_persistent(l_Lean_mkDecIsTrue___closed__1);
l_Lean_mkDecIsFalse___closed__1 = _init_l_Lean_mkDecIsFalse___closed__1();
lean::mark_persistent(l_Lean_mkDecIsFalse___closed__1);
return w;
}
