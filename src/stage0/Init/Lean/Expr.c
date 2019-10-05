// Lean compiler output
// Module: Init.Lean.Expr
// Imports: Init.Lean.Level Init.Lean.KVMap
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
lean_object* lean_expr_mk_mdata(lean_object*, lean_object*);
uint8_t lean_expr_has_fvar(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_quick_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_mkBinApp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MData_empty;
lean_object* l_Lean_Expr_constName(lean_object*);
lean_object* lean_expr_mk_sort(lean_object*);
lean_object* l_Lean_Expr_pi___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isLambda___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_bvarIdx(lean_object*);
lean_object* l_Lean_Expr_HasBeq___closed__1;
lean_object* l_Lean_Expr_isAppOfArity___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_exprIsInhabited;
size_t lean_expr_hash(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_Expr_constName___boxed(lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiate1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsTrue___closed__4;
lean_object* lean_expr_mk_pi(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isBVar___boxed(lean_object*);
lean_object* l_panicWithPos___at_Lean_Expr_constName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarName___closed__1;
lean_object* lean_expr_local(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_expr_mk_app(lean_object*, lean_object*);
lean_object* l_Lean_Expr_quickLt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody(lean_object*);
lean_object* l_Lean_Expr_isAppOf___boxed(lean_object*, lean_object*);
lean_object* lean_expr_mk_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
extern lean_object* l_Lean_Inhabited;
lean_object* l_Lean_mkDecIsFalse___closed__1;
lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_Expr_constLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsTrue___closed__3;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hasMVar___boxed(lean_object*);
lean_object* l_Lean_Expr_sort___boxed(lean_object*);
lean_object* l_Lean_Expr_HasToString___closed__1;
lean_object* lean_expr_mk_fvar(lean_object*);
lean_object* l_List_foldl___main___at_Lean_mkApp___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_BinderInfo_beq___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
lean_object* l_Lean_Expr_bvarIdx___boxed(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Expr_getAppArgsAux(lean_object*, lean_object*);
lean_object* lean_expr_mk_proj(lean_object*, lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__3;
lean_object* lean_expr_mk_const(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName___closed__1;
lean_object* l_Lean_Expr_bvar___boxed(lean_object*);
lean_object* l_Lean_Expr_Hashable___closed__1;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_MData_HasEmptyc;
lean_object* l_Lean_Expr_constLevels___boxed(lean_object*);
lean_object* l_Lean_Expr_isApp___boxed(lean_object*);
lean_object* l_panicWithPos___at_Lean_Expr_constLevels___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain(lean_object*);
lean_object* l_Lean_BinderInfo_HasBeq;
lean_object* l_Lean_Expr_dbgToString___boxed(lean_object*);
lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels___closed__1;
lean_object* l_Lean_Expr_constName___closed__2;
lean_object* l_Lean_Expr_getAppArgsAux___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiate___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Expr_elet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_mkDecIsTrue___closed__1;
lean_object* l_Lean_mkBinCApp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsFalse(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___boxed(lean_object*);
lean_object* l_Lean_Expr_HasRepr;
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsTrue___closed__2;
extern lean_object* l_panicWithPos___rarg___closed__1;
lean_object* l_Lean_Expr_getAppArgs(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main___boxed(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarName___boxed(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Expr_getAppArgsAux___main(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_mkCApp(lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsTrue___closed__5;
lean_object* l_Lean_Expr_hasFVar___boxed(lean_object*);
lean_object* l_Lean_Expr_HasToString;
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isBinding(lean_object*);
lean_object* lean_expr_mk_mvar(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* lean_expr_mk_bvar(lean_object*);
lean_object* l_Lean_Expr_bindingDomain___boxed(lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_BinderInfo_HasBeq___closed__1;
uint8_t lean_expr_lt(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_getAppArgsAux___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsTrue(lean_object*, lean_object*);
lean_object* l_Lean_Expr_abstract___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels(lean_object*);
uint8_t lean_expr_has_mvar(lean_object*);
lean_object* l_Lean_Expr_isFVar___boxed(lean_object*);
lean_object* l_Lean_Expr_abstractRange___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___boxed(lean_object*);
lean_object* lean_expr_mk_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvarIdx___closed__1;
extern lean_object* l_panicWithPos___rarg___closed__2;
lean_object* l_Lean_Expr_HasBeq;
uint8_t l_Lean_Expr_isBVar(lean_object*);
lean_object* l_Lean_Expr_isBinding___boxed(lean_object*);
lean_object* l_Lean_Expr_Hashable;
lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object*);
lean_object* l_Lean_Expr_bindingBody___boxed(lean_object*);
lean_object* l_Lean_Expr_mvar___boxed(lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarName(lean_object*);
lean_object* l_Lean_Expr_isSort___boxed(lean_object*);
lean_object* l_Lean_Expr_local___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isLet___boxed(lean_object*);
lean_object* l_Lean_Expr_getAppFn___boxed(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isForall___boxed(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_isMVar___boxed(lean_object*);
lean_object* l_panicWithPos___at_Lean_Expr_constName___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsFalse___closed__3;
lean_object* l_Lean_exprIsInhabited___closed__1;
lean_object* lean_expr_mk_lit(lean_object*);
lean_object* l_Lean_mkDecIsFalse___closed__2;
lean_object* l_Lean_Expr_getAppArgs___boxed(lean_object*);
lean_object* l_Lean_Expr_isConst___boxed(lean_object*);
lean_object* l_Lean_Expr_lt___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_panicWithPos___at_Array_findIdx_x21___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 3)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 0;
return x_4;
}
}
}
lean_object* l_Lean_BinderInfo_isInstImplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_BinderInfo_isInstImplicit(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_BinderInfo_beq(uint8_t x_1, uint8_t x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; 
x_3 = lean_box(x_2);
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
lean_object* x_6; 
x_6 = lean_box(x_2);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 0;
return x_8;
}
}
case 2:
{
lean_object* x_9; 
x_9 = lean_box(x_2);
if (lean_obj_tag(x_9) == 2)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = 0;
return x_11;
}
}
case 3:
{
lean_object* x_12; 
x_12 = lean_box(x_2);
if (lean_obj_tag(x_12) == 3)
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_12);
x_14 = 0;
return x_14;
}
}
default: 
{
lean_object* x_15; 
x_15 = lean_box(x_2);
if (lean_obj_tag(x_15) == 4)
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_15);
x_17 = 0;
return x_17;
}
}
}
}
}
lean_object* l_Lean_BinderInfo_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_BinderInfo_beq(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* _init_l_Lean_BinderInfo_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_BinderInfo_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_BinderInfo_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_BinderInfo_HasBeq___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_MData_empty() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* _init_l_Lean_MData_HasEmptyc() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* _init_l_Lean_exprIsInhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_exprIsInhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_exprIsInhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Expr_bvar___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_mk_bvar(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_fvar___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_mk_fvar(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_mvar___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_mk_mvar(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_sort___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_mk_sort(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_const___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_mk_const(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_app___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_mk_app(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_lam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_expr_mk_lambda(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Expr_pi___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_expr_mk_pi(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Expr_elet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_expr_mk_let(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_lit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_mk_lit(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_mdata___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_mk_mdata(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_proj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_mk_proj(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_local___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = lean_expr_local(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* l_List_foldl___main___at_Lean_mkApp___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_expr_mk_app(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_Lean_mkApp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___main___at_Lean_mkApp___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkCApp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_expr_mk_const(x_1, x_3);
x_5 = l_List_foldl___main___at_Lean_mkApp___spec__1(x_4, x_2);
return x_5;
}
}
lean_object* l_Lean_Expr_hash___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_expr_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_Hashable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_hash___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Expr_Hashable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_Hashable___closed__1;
return x_1;
}
}
lean_object* l_Lean_Expr_dbgToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_expr_dbg_to_string(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_quickLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_expr_quick_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_expr_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_eqv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_expr_eqv(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Expr_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_eqv___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Expr_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_HasBeq___closed__1;
return x_1;
}
}
lean_object* l_Lean_Expr_hasMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_mvar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_hasFVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_expr_has_fvar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_isSort(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isSort___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isSort(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_isBVar(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isBVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isBVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_isMVar(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isMVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isMVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_isFVar(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isFVar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isFVar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_isApp(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isApp___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isApp(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_isConst(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isConst___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isConst(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_isForall(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isForall___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isForall(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_isLambda(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isLambda___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isLambda(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_isBinding(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 7:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
default: 
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
}
lean_object* l_Lean_Expr_isBinding___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isBinding(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Expr_isLet(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_Expr_isLet___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isLet(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_getAppFn___main(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
x_1 = x_2;
goto _start;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l_Lean_Expr_getAppFn___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppFn___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_getAppFn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppFn___main(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_getAppFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_3;
x_2 = x_5;
goto _start;
}
else
{
return x_2;
}
}
}
lean_object* l_Lean_Expr_getAppNumArgsAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_getAppNumArgsAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppNumArgsAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_getAppNumArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_getAppNumArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppNumArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_getAppArgsAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
x_1 = x_3;
x_2 = x_5;
goto _start;
}
else
{
return x_2;
}
}
}
lean_object* l_Lean_Expr_getAppArgsAux___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppArgsAux___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_getAppArgsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppArgsAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_getAppArgsAux___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppArgsAux(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Expr_getAppArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_Expr_getAppArgsAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_getAppArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_Expr_isAppOf(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_name_dec_eq(x_4, x_2);
lean_dec(x_4);
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
}
}
lean_object* l_Lean_Expr_isAppOf___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_isAppOf(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
lean_dec(x_3);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_name_dec_eq(x_4, x_2);
return x_8;
}
}
case 5:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_3, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_3, x_12);
lean_dec(x_3);
x_1 = x_9;
x_3 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_3);
x_15 = 0;
return x_15;
}
}
default: 
{
uint8_t x_16; 
lean_dec(x_3);
x_16 = 0;
return x_16;
}
}
}
}
lean_object* l_Lean_Expr_isAppOfArity___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_isAppOfArity___main(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Lean_Expr_isAppOfArity(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_isAppOfArity___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_isAppOfArity___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_panicWithPos___at_Lean_Expr_constName___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = l_panicWithPos___rarg___closed__1;
x_6 = lean_string_append(x_5, x_1);
x_7 = l_panicWithPos___rarg___closed__2;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Nat_repr(x_2);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = l_panicWithPos___rarg___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Nat_repr(x_3);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = l_panicWithPos___rarg___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_4);
x_18 = l_Lean_Inhabited;
x_19 = lean_panic_fn(x_17);
return x_19;
}
}
lean_object* _init_l_Lean_Expr_constName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Lean.Expr");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_constName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constName called on non-const");
return x_1;
}
}
lean_object* l_Lean_Expr_constName(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Expr_constName___closed__1;
x_4 = lean_unsigned_to_nat(181u);
x_5 = lean_unsigned_to_nat(15u);
x_6 = l_Lean_Expr_constName___closed__2;
x_7 = l_panicWithPos___at_Lean_Expr_constName___spec__1(x_3, x_4, x_5, x_6);
return x_7;
}
}
}
lean_object* l_panicWithPos___at_Lean_Expr_constName___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_panicWithPos___at_Lean_Expr_constName___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Expr_constName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_constName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_panicWithPos___at_Lean_Expr_constLevels___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = lean_box(0);
x_6 = l_panicWithPos___rarg___closed__1;
x_7 = lean_string_append(x_6, x_1);
x_8 = l_panicWithPos___rarg___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Nat_repr(x_2);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = l_panicWithPos___rarg___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Nat_repr(x_3);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_panicWithPos___rarg___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_4);
x_19 = lean_panic_fn(x_18);
return x_19;
}
}
lean_object* _init_l_Lean_Expr_constLevels___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constLevels called on non-const");
return x_1;
}
}
lean_object* l_Lean_Expr_constLevels(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Expr_constName___closed__1;
x_4 = lean_unsigned_to_nat(185u);
x_5 = lean_unsigned_to_nat(16u);
x_6 = l_Lean_Expr_constLevels___closed__1;
x_7 = l_panicWithPos___at_Lean_Expr_constLevels___spec__1(x_3, x_4, x_5, x_6);
return x_7;
}
}
}
lean_object* l_panicWithPos___at_Lean_Expr_constLevels___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_panicWithPos___at_Lean_Expr_constLevels___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Expr_constLevels___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_constLevels(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_bvarIdx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bvarIdx called on non-bvar");
return x_1;
}
}
lean_object* l_Lean_Expr_bvarIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Expr_constName___closed__1;
x_4 = lean_unsigned_to_nat(189u);
x_5 = lean_unsigned_to_nat(7u);
x_6 = l_Lean_Expr_bvarIdx___closed__1;
x_7 = l_panicWithPos___at_Array_findIdx_x21___spec__1(x_3, x_4, x_5, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Expr_bvarIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bvarIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_fvarName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fvarName called on non-fvar");
return x_1;
}
}
lean_object* l_Lean_Expr_fvarName(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Expr_constName___closed__1;
x_4 = lean_unsigned_to_nat(193u);
x_5 = lean_unsigned_to_nat(7u);
x_6 = l_Lean_Expr_fvarName___closed__1;
x_7 = l_panicWithPos___at_Lean_Expr_constName___spec__1(x_3, x_4, x_5, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Expr_fvarName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_fvarName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_bindingDomain(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
case 7:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = l_Lean_exprIsInhabited___closed__1;
return x_4;
}
}
}
}
lean_object* l_Lean_Expr_bindingDomain___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bindingDomain(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_bindingBody(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
case 7:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = l_Lean_exprIsInhabited___closed__1;
return x_4;
}
}
}
}
lean_object* l_Lean_Expr_bindingBody___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_bindingBody(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_instantiate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_instantiate(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_instantiate1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_instantiate1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_instantiateRev___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_instantiate_rev(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_abstract___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_abstract(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_abstractRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_expr_abstract_range(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Expr_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_dbgToString___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Expr_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_HasToString___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Expr_HasRepr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_HasToString___closed__1;
return x_1;
}
}
lean_object* l_Lean_mkConst(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_expr_mk_const(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_mkBinApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_expr_mk_app(x_1, x_2);
x_5 = lean_expr_mk_app(x_4, x_3);
return x_5;
}
}
lean_object* l_Lean_mkBinCApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_expr_mk_const(x_1, x_4);
x_6 = l_Lean_mkBinApp(x_5, x_2, x_3);
return x_6;
}
}
lean_object* _init_l_Lean_mkDecIsTrue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Decidable");
return x_1;
}
}
lean_object* _init_l_Lean_mkDecIsTrue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkDecIsTrue___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_mkDecIsTrue___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isTrue");
return x_1;
}
}
lean_object* _init_l_Lean_mkDecIsTrue___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkDecIsTrue___closed__2;
x_2 = l_Lean_mkDecIsTrue___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_mkDecIsTrue___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkDecIsTrue___closed__4;
x_3 = lean_expr_mk_const(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_mkDecIsTrue(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_mkDecIsTrue___closed__5;
x_4 = l_Lean_mkBinApp(x_3, x_1, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_mkDecIsFalse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isFalse");
return x_1;
}
}
lean_object* _init_l_Lean_mkDecIsFalse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkDecIsTrue___closed__2;
x_2 = l_Lean_mkDecIsFalse___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_mkDecIsFalse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkDecIsFalse___closed__2;
x_3 = lean_expr_mk_const(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_mkDecIsFalse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_mkDecIsFalse___closed__3;
x_4 = l_Lean_mkBinApp(x_3, x_1, x_2);
return x_4;
}
}
lean_object* initialize_Init_Lean_Level(lean_object*);
lean_object* initialize_Init_Lean_KVMap(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Expr(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Level(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_KVMap(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_BinderInfo_HasBeq___closed__1 = _init_l_Lean_BinderInfo_HasBeq___closed__1();
lean_mark_persistent(l_Lean_BinderInfo_HasBeq___closed__1);
l_Lean_BinderInfo_HasBeq = _init_l_Lean_BinderInfo_HasBeq();
lean_mark_persistent(l_Lean_BinderInfo_HasBeq);
l_Lean_MData_empty = _init_l_Lean_MData_empty();
lean_mark_persistent(l_Lean_MData_empty);
l_Lean_MData_HasEmptyc = _init_l_Lean_MData_HasEmptyc();
lean_mark_persistent(l_Lean_MData_HasEmptyc);
l_Lean_exprIsInhabited___closed__1 = _init_l_Lean_exprIsInhabited___closed__1();
lean_mark_persistent(l_Lean_exprIsInhabited___closed__1);
l_Lean_exprIsInhabited = _init_l_Lean_exprIsInhabited();
lean_mark_persistent(l_Lean_exprIsInhabited);
l_Lean_Expr_Hashable___closed__1 = _init_l_Lean_Expr_Hashable___closed__1();
lean_mark_persistent(l_Lean_Expr_Hashable___closed__1);
l_Lean_Expr_Hashable = _init_l_Lean_Expr_Hashable();
lean_mark_persistent(l_Lean_Expr_Hashable);
l_Lean_Expr_HasBeq___closed__1 = _init_l_Lean_Expr_HasBeq___closed__1();
lean_mark_persistent(l_Lean_Expr_HasBeq___closed__1);
l_Lean_Expr_HasBeq = _init_l_Lean_Expr_HasBeq();
lean_mark_persistent(l_Lean_Expr_HasBeq);
l_Lean_Expr_constName___closed__1 = _init_l_Lean_Expr_constName___closed__1();
lean_mark_persistent(l_Lean_Expr_constName___closed__1);
l_Lean_Expr_constName___closed__2 = _init_l_Lean_Expr_constName___closed__2();
lean_mark_persistent(l_Lean_Expr_constName___closed__2);
l_Lean_Expr_constLevels___closed__1 = _init_l_Lean_Expr_constLevels___closed__1();
lean_mark_persistent(l_Lean_Expr_constLevels___closed__1);
l_Lean_Expr_bvarIdx___closed__1 = _init_l_Lean_Expr_bvarIdx___closed__1();
lean_mark_persistent(l_Lean_Expr_bvarIdx___closed__1);
l_Lean_Expr_fvarName___closed__1 = _init_l_Lean_Expr_fvarName___closed__1();
lean_mark_persistent(l_Lean_Expr_fvarName___closed__1);
l_Lean_Expr_HasToString___closed__1 = _init_l_Lean_Expr_HasToString___closed__1();
lean_mark_persistent(l_Lean_Expr_HasToString___closed__1);
l_Lean_Expr_HasToString = _init_l_Lean_Expr_HasToString();
lean_mark_persistent(l_Lean_Expr_HasToString);
l_Lean_Expr_HasRepr = _init_l_Lean_Expr_HasRepr();
lean_mark_persistent(l_Lean_Expr_HasRepr);
l_Lean_mkDecIsTrue___closed__1 = _init_l_Lean_mkDecIsTrue___closed__1();
lean_mark_persistent(l_Lean_mkDecIsTrue___closed__1);
l_Lean_mkDecIsTrue___closed__2 = _init_l_Lean_mkDecIsTrue___closed__2();
lean_mark_persistent(l_Lean_mkDecIsTrue___closed__2);
l_Lean_mkDecIsTrue___closed__3 = _init_l_Lean_mkDecIsTrue___closed__3();
lean_mark_persistent(l_Lean_mkDecIsTrue___closed__3);
l_Lean_mkDecIsTrue___closed__4 = _init_l_Lean_mkDecIsTrue___closed__4();
lean_mark_persistent(l_Lean_mkDecIsTrue___closed__4);
l_Lean_mkDecIsTrue___closed__5 = _init_l_Lean_mkDecIsTrue___closed__5();
lean_mark_persistent(l_Lean_mkDecIsTrue___closed__5);
l_Lean_mkDecIsFalse___closed__1 = _init_l_Lean_mkDecIsFalse___closed__1();
lean_mark_persistent(l_Lean_mkDecIsFalse___closed__1);
l_Lean_mkDecIsFalse___closed__2 = _init_l_Lean_mkDecIsFalse___closed__2();
lean_mark_persistent(l_Lean_mkDecIsFalse___closed__2);
l_Lean_mkDecIsFalse___closed__3 = _init_l_Lean_mkDecIsFalse___closed__3();
lean_mark_persistent(l_Lean_mkDecIsFalse___closed__3);
return w;
}
#ifdef __cplusplus
}
#endif
