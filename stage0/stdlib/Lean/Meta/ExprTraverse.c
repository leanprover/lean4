// Lean compiler output
// Module: Lean.Meta.ExprTraverse
// Imports: Lean.Meta.Basic Lean.SubExpr
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
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildrenWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0;
lean_object* l_Lean_Meta_mkForallFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushLetBody(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambdaWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildren(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLetWithPos___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_traverseAppWithPos___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_root;
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambdaWithPos___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_SubExpr_Pos_pushBindingDomain(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_SubExpr_Pos_pushLetVarType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushBindingBody(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambda___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildrenWithPos___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForallWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushProj(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForall___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildren___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForallWithPos___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLetWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushLetValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SubExpr_Pos_root;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___closed__0;
x_6 = lean_apply_3(x_1, x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_push(x_1, x_8);
x_10 = l_Lean_SubExpr_Pos_pushBindingBody(x_2);
x_11 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(x_3, x_4, x_5, x_6, x_9, x_10, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = l_Lean_Meta_withLocalDecl___redArg(x_1, x_2, x_3, x_4, x_6, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = 0;
x_5 = 1;
x_6 = 1;
x_7 = lean_box(x_4);
x_8 = lean_box(x_5);
x_9 = lean_box(x_4);
x_10 = lean_box(x_5);
x_11 = lean_box(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_7);
lean_closure_set(x_12, 3, x_8);
lean_closure_set(x_12, 4, x_9);
lean_closure_set(x_12, 5, x_10);
lean_closure_set(x_12, 6, x_11);
x_13 = lean_apply_2(x_2, lean_box(0), x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 6)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_11);
x_12 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec_ref(x_7);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0___boxed), 8, 7);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_2);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_4);
lean_closure_set(x_13, 6, x_11);
x_14 = lean_box(x_12);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1___boxed), 6, 5);
lean_closure_set(x_15, 0, x_3);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_9);
lean_closure_set(x_15, 3, x_14);
lean_closure_set(x_15, 4, x_13);
x_16 = l_Lean_SubExpr_Pos_pushBindingDomain(x_6);
lean_dec(x_6);
x_17 = lean_expr_instantiate_rev(x_10, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_10);
x_18 = lean_apply_2(x_4, x_16, x_17);
x_19 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_18, x_15);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_3);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__2), 3, 2);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_2);
x_22 = lean_expr_instantiate_rev(x_7, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_7);
x_23 = lean_apply_2(x_4, x_6, x_22);
x_24 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_23, x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
x_8 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambdaWithPos___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0;
x_8 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(x_1, x_2, x_3, x_4, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambdaWithPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_traverseLambdaWithPos___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_push(x_1, x_8);
x_10 = l_Lean_SubExpr_Pos_pushBindingBody(x_2);
x_11 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(x_3, x_4, x_5, x_6, x_9, x_10, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = 0;
x_5 = 1;
x_6 = 1;
x_7 = lean_box(x_4);
x_8 = lean_box(x_5);
x_9 = lean_box(x_5);
x_10 = lean_box(x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_8);
lean_closure_set(x_11, 4, x_9);
lean_closure_set(x_11, 5, x_10);
x_12 = lean_apply_2(x_2, lean_box(0), x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 7)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_11);
x_12 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec_ref(x_7);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0___boxed), 8, 7);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_2);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_4);
lean_closure_set(x_13, 6, x_11);
x_14 = lean_box(x_12);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1___boxed), 6, 5);
lean_closure_set(x_15, 0, x_3);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_9);
lean_closure_set(x_15, 3, x_14);
lean_closure_set(x_15, 4, x_13);
x_16 = l_Lean_SubExpr_Pos_pushBindingDomain(x_6);
lean_dec(x_6);
x_17 = lean_expr_instantiate_rev(x_10, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_10);
x_18 = lean_apply_2(x_4, x_16, x_17);
x_19 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_18, x_15);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_3);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2), 3, 2);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_2);
x_22 = lean_expr_instantiate_rev(x_7, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_7);
x_23 = lean_apply_2(x_4, x_6, x_22);
x_24 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_23, x_21);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForallWithPos___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0;
x_8 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(x_1, x_2, x_3, x_4, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForallWithPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_traverseForallWithPos___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_push(x_1, x_8);
x_10 = l_Lean_SubExpr_Pos_pushLetBody(x_2);
x_11 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(x_3, x_4, x_5, x_6, x_9, x_10, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = 0;
x_9 = l_Lean_Meta_withLetDecl___redArg(x_1, x_2, x_3, x_4, x_6, x_5, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__1), 6, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_10);
lean_closure_set(x_11, 4, x_4);
x_12 = l_Lean_SubExpr_Pos_pushLetValue(x_5);
x_13 = lean_expr_instantiate_rev(x_6, x_7);
x_14 = lean_apply_2(x_8, x_12, x_13);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_14, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = 0;
x_5 = 1;
x_6 = 1;
x_7 = lean_box(x_4);
x_8 = lean_box(x_5);
x_9 = lean_box(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_7);
lean_closure_set(x_10, 3, x_8);
lean_closure_set(x_10, 4, x_9);
x_11 = lean_apply_2(x_2, lean_box(0), x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 8)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_7, 3);
lean_inc_ref(x_12);
lean_dec_ref(x_7);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0___boxed), 8, 7);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_2);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_4);
lean_closure_set(x_13, 6, x_12);
lean_inc(x_8);
lean_inc(x_4);
lean_inc_ref(x_5);
lean_inc(x_6);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2___boxed), 10, 9);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_9);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_6);
lean_closure_set(x_14, 5, x_11);
lean_closure_set(x_14, 6, x_5);
lean_closure_set(x_14, 7, x_4);
lean_closure_set(x_14, 8, x_8);
x_15 = l_Lean_SubExpr_Pos_pushLetVarType(x_6);
lean_dec(x_6);
x_16 = lean_expr_instantiate_rev(x_10, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_10);
x_17 = lean_apply_2(x_4, x_15, x_16);
x_18 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_17, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_3);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__3), 3, 2);
lean_closure_set(x_20, 0, x_5);
lean_closure_set(x_20, 1, x_2);
x_21 = lean_expr_instantiate_rev(x_7, x_5);
lean_dec_ref(x_5);
lean_dec_ref(x_7);
x_22 = lean_apply_2(x_4, x_6, x_21);
x_23 = lean_apply_4(x_19, lean_box(0), lean_box(0), x_22, x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLetWithPos___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0;
x_8 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(x_1, x_2, x_3, x_4, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLetWithPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_traverseLetWithPos___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildrenWithPos___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_6)) {
case 5:
{
lean_object* x_7; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_7 = l_Lean_Expr_traverseAppWithPos___redArg(x_1, x_4, x_5, x_6);
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_traverseLambdaWithPos___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_traverseForallWithPos___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_traverseLetWithPos___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
case 10:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(x_15, 0, x_6);
x_16 = lean_apply_2(x_4, x_5, x_13);
x_17 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
case 11:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_6, 2);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(x_22, 0, x_6);
x_23 = l_Lean_SubExpr_Pos_pushProj(x_5);
lean_dec(x_5);
x_24 = lean_apply_2(x_4, x_23, x_20);
x_25 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_22, x_24);
return x_25;
}
default: 
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_26);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_apply_2(x_27, lean_box(0), x_6);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildrenWithPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_traverseChildrenWithPos___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambda___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_traverseLambdaWithPos), 7, 4);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
x_7 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_traverseLambda___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForall___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_traverseForallWithPos), 7, 4);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
x_7 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_traverseForall___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLet___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_traverseLetWithPos), 7, 4);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
x_7 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_traverseLet___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildren___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_traverseChildrenWithPos), 7, 4);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
x_7 = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildren(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_traverseChildren___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_SubExpr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_ExprTraverse(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_SubExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___closed__0 = _init_l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___closed__0);
l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0 = _init_l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
