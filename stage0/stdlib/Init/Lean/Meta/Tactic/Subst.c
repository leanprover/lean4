// Lean compiler output
// Module: Init.Lean.Meta.Tactic.Subst
// Imports: Init.Lean.Meta.AppBuilder Init.Lean.Meta.Message Init.Lean.Meta.Tactic.Util Init.Lean.Meta.Tactic.Revert Init.Lean.Meta.Tactic.Intro Init.Lean.Meta.Tactic.Clear Init.Lean.Meta.Tactic.FVarSubst
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
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___closed__10;
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___closed__6;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___closed__16;
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___closed__18;
lean_object* l_Lean_Meta_substCore___closed__5;
lean_object* l_Lean_Meta_mkEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___closed__15;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_substCore___closed__20;
extern lean_object* l_Lean_Name_inhabited;
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___closed__3;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_subst___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_subst___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___closed__21;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___closed__13;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_assignExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___closed__14;
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___closed__1;
lean_object* l_Lean_Meta_substCore___closed__9;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___closed__4;
lean_object* l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___closed__2;
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___closed__4;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___closed__2;
lean_object* l_Lean_Meta_substCore___closed__1;
lean_object* l_Lean_Meta_substCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___closed__8;
lean_object* l_Lean_Meta_substCore___closed__17;
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___closed__12;
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___closed__7;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___closed__19;
extern lean_object* l___private_Init_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
extern lean_object* l_Lean_Meta_isClassQuick___main___closed__1;
uint8_t l_Lean_LocalInstance_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_Lean_Meta_subst___closed__6;
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___closed__5;
lean_object* l_Lean_Meta_subst___closed__3;
lean_object* l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___closed__11;
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_LocalInstance_beq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_LocalInstance_beq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_LocalInstance_beq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = l_Lean_Meta_mkEqSymm(x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_expr_abstract(x_1, x_2);
x_12 = lean_expr_instantiate1(x_11, x_9);
lean_dec(x_9);
lean_dec(x_11);
x_13 = lean_array_push(x_3, x_4);
x_14 = lean_array_push(x_13, x_5);
x_15 = l_Lean_Meta_mkLambda(x_14, x_12, x_6, x_10);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("subst");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_substCore___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("argument must be an equality proof");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid equality proof, it is not of the form ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(x = t)");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___closed__8;
x_2 = l_Lean_Meta_substCore___closed__11;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(t = x)");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___closed__8;
x_2 = l_Lean_Meta_substCore___closed__15;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_h");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_substCore___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' occurs at");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___closed__20;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_getMVarDecl(x_1, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 4);
lean_inc(x_16);
x_17 = lean_array_get_size(x_12);
x_18 = lean_array_get_size(x_16);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_17);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_16);
lean_inc(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_13);
lean_ctor_set(x_20, 4, x_14);
if (x_19 == 0)
{
lean_object* x_2730; 
lean_dec(x_12);
lean_dec(x_5);
x_2730 = lean_box(0);
x_21 = x_2730;
goto block_2729;
}
else
{
lean_object* x_2731; uint8_t x_2732; lean_object* x_2733; 
x_2731 = lean_unsigned_to_nat(0u);
x_2732 = l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__2(x_5, x_8, lean_box(0), x_12, x_16, x_2731);
lean_dec(x_12);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 x_2733 = x_5;
} else {
 lean_dec_ref(x_5);
 x_2733 = lean_box(0);
}
if (x_2732 == 0)
{
lean_object* x_2734; 
lean_dec(x_2733);
x_2734 = lean_box(0);
x_21 = x_2734;
goto block_2729;
}
else
{
lean_object* x_2735; 
lean_dec(x_10);
lean_inc(x_1);
x_2735 = l_Lean_Meta_getMVarTag(x_1, x_20, x_9);
if (lean_obj_tag(x_2735) == 0)
{
lean_object* x_2736; lean_object* x_2737; lean_object* x_2738; lean_object* x_2739; 
x_2736 = lean_ctor_get(x_2735, 0);
lean_inc(x_2736);
x_2737 = lean_ctor_get(x_2735, 1);
lean_inc(x_2737);
lean_dec(x_2735);
x_2738 = l_Lean_Meta_substCore___closed__2;
lean_inc(x_1);
x_2739 = l_Lean_Meta_checkNotAssigned(x_1, x_2738, x_20, x_2737);
if (lean_obj_tag(x_2739) == 0)
{
lean_object* x_2740; lean_object* x_2741; 
x_2740 = lean_ctor_get(x_2739, 1);
lean_inc(x_2740);
lean_dec(x_2739);
lean_inc(x_20);
lean_inc(x_2);
x_2741 = l_Lean_Meta_getLocalDecl(x_2, x_20, x_2740);
if (lean_obj_tag(x_2741) == 0)
{
lean_object* x_2742; lean_object* x_2743; lean_object* x_2744; lean_object* x_2745; lean_object* x_2746; uint8_t x_2747; 
x_2742 = lean_ctor_get(x_2741, 0);
lean_inc(x_2742);
x_2743 = lean_ctor_get(x_2741, 1);
lean_inc(x_2743);
lean_dec(x_2741);
x_2744 = l_Lean_LocalDecl_type(x_2742);
lean_dec(x_2742);
x_2745 = l_Lean_Expr_eq_x3f___closed__2;
x_2746 = lean_unsigned_to_nat(3u);
x_2747 = l_Lean_Expr_isAppOfArity___main(x_2744, x_2745, x_2746);
if (x_2747 == 0)
{
lean_object* x_2748; lean_object* x_2749; 
lean_dec(x_2744);
lean_dec(x_2736);
lean_dec(x_2733);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
x_2748 = l_Lean_Meta_substCore___closed__5;
x_2749 = l_Lean_Meta_throwTacticEx___rarg(x_2738, x_1, x_2748, x_20, x_2743);
lean_dec(x_20);
return x_2749;
}
else
{
lean_object* x_2750; lean_object* x_2751; lean_object* x_2752; lean_object* x_2753; lean_object* x_2754; lean_object* x_2755; lean_object* x_2756; lean_object* x_2757; lean_object* x_2758; uint8_t x_2759; 
x_2750 = l_Lean_Expr_getAppNumArgsAux___main(x_2744, x_2731);
x_2751 = lean_unsigned_to_nat(1u);
x_2752 = lean_nat_sub(x_2750, x_2751);
x_2753 = lean_nat_sub(x_2752, x_2751);
lean_dec(x_2752);
x_2754 = l_Lean_Expr_getRevArg_x21___main(x_2744, x_2753);
x_2755 = lean_unsigned_to_nat(2u);
x_2756 = lean_nat_sub(x_2750, x_2755);
lean_dec(x_2750);
x_2757 = lean_nat_sub(x_2756, x_2751);
lean_dec(x_2756);
x_2758 = l_Lean_Expr_getRevArg_x21___main(x_2744, x_2757);
if (x_3 == 0)
{
uint8_t x_4047; 
x_4047 = 0;
x_2759 = x_4047;
goto block_4046;
}
else
{
uint8_t x_4048; 
x_4048 = 1;
x_2759 = x_4048;
goto block_4046;
}
block_4046:
{
lean_object* x_2760; lean_object* x_2770; 
if (x_2759 == 0)
{
lean_inc(x_2754);
x_2770 = x_2754;
goto block_4045;
}
else
{
lean_inc(x_2758);
x_2770 = x_2758;
goto block_4045;
}
block_2769:
{
lean_object* x_2761; lean_object* x_2762; 
lean_dec(x_2760);
x_2761 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2761, 0, x_2744);
x_2762 = l_Lean_indentExpr(x_2761);
if (x_2759 == 0)
{
lean_object* x_2763; lean_object* x_2764; lean_object* x_2765; 
x_2763 = l_Lean_Meta_substCore___closed__12;
x_2764 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2764, 0, x_2763);
lean_ctor_set(x_2764, 1, x_2762);
x_2765 = l_Lean_Meta_throwTacticEx___rarg(x_2738, x_1, x_2764, x_20, x_2743);
lean_dec(x_20);
return x_2765;
}
else
{
lean_object* x_2766; lean_object* x_2767; lean_object* x_2768; 
x_2766 = l_Lean_Meta_substCore___closed__16;
x_2767 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2767, 0, x_2766);
lean_ctor_set(x_2767, 1, x_2762);
x_2768 = l_Lean_Meta_throwTacticEx___rarg(x_2738, x_1, x_2767, x_20, x_2743);
lean_dec(x_20);
return x_2768;
}
}
block_4045:
{
lean_object* x_2771; 
if (x_2759 == 0)
{
lean_dec(x_2754);
x_2771 = x_2758;
goto block_4044;
}
else
{
lean_dec(x_2758);
x_2771 = x_2754;
goto block_4044;
}
block_4044:
{
if (lean_obj_tag(x_2770) == 1)
{
lean_object* x_2772; lean_object* x_2773; lean_object* x_2774; lean_object* x_4028; uint8_t x_4029; 
lean_dec(x_2744);
x_2772 = lean_ctor_get(x_2770, 0);
lean_inc(x_2772);
x_2773 = lean_ctor_get(x_2743, 1);
lean_inc(x_2773);
lean_inc(x_2771);
x_4028 = l_Lean_MetavarContext_exprDependsOn(x_2773, x_2771, x_2772);
x_4029 = lean_unbox(x_4028);
lean_dec(x_4028);
if (x_4029 == 0)
{
lean_dec(x_2771);
lean_dec(x_2770);
x_2774 = x_2743;
goto block_4027;
}
else
{
lean_object* x_4030; lean_object* x_4031; lean_object* x_4032; lean_object* x_4033; lean_object* x_4034; lean_object* x_4035; lean_object* x_4036; lean_object* x_4037; lean_object* x_4038; uint8_t x_4039; 
lean_dec(x_2772);
lean_dec(x_2736);
lean_dec(x_2733);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
x_4030 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4030, 0, x_2770);
x_4031 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_4032 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_4032, 0, x_4031);
lean_ctor_set(x_4032, 1, x_4030);
x_4033 = l_Lean_Meta_substCore___closed__21;
x_4034 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_4034, 0, x_4032);
lean_ctor_set(x_4034, 1, x_4033);
x_4035 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_4035, 0, x_2771);
x_4036 = l_Lean_indentExpr(x_4035);
x_4037 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_4037, 0, x_4034);
lean_ctor_set(x_4037, 1, x_4036);
x_4038 = l_Lean_Meta_throwTacticEx___rarg(x_2738, x_1, x_4037, x_20, x_2743);
lean_dec(x_20);
x_4039 = !lean_is_exclusive(x_4038);
if (x_4039 == 0)
{
return x_4038;
}
else
{
lean_object* x_4040; lean_object* x_4041; lean_object* x_4042; 
x_4040 = lean_ctor_get(x_4038, 0);
x_4041 = lean_ctor_get(x_4038, 1);
lean_inc(x_4041);
lean_inc(x_4040);
lean_dec(x_4038);
x_4042 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4042, 0, x_4040);
lean_ctor_set(x_4042, 1, x_4041);
return x_4042;
}
}
block_4027:
{
lean_object* x_2775; 
lean_inc(x_20);
lean_inc(x_2772);
x_2775 = l_Lean_Meta_getLocalDecl(x_2772, x_20, x_2774);
if (lean_obj_tag(x_2775) == 0)
{
lean_object* x_2776; lean_object* x_2777; lean_object* x_2778; lean_object* x_2779; uint8_t x_2780; lean_object* x_2781; 
x_2776 = lean_ctor_get(x_2775, 1);
lean_inc(x_2776);
lean_dec(x_2775);
x_2777 = l_Lean_mkAppStx___closed__9;
x_2778 = lean_array_push(x_2777, x_2772);
x_2779 = lean_array_push(x_2778, x_2);
x_2780 = 1;
x_2781 = l_Lean_Meta_revert(x_1, x_2779, x_2780, x_20, x_2776);
if (lean_obj_tag(x_2781) == 0)
{
lean_object* x_2782; lean_object* x_2783; lean_object* x_2784; lean_object* x_2785; lean_object* x_2786; uint8_t x_2787; lean_object* x_2788; 
x_2782 = lean_ctor_get(x_2781, 0);
lean_inc(x_2782);
x_2783 = lean_ctor_get(x_2781, 1);
lean_inc(x_2783);
lean_dec(x_2781);
x_2784 = lean_ctor_get(x_2782, 0);
lean_inc(x_2784);
x_2785 = lean_ctor_get(x_2782, 1);
lean_inc(x_2785);
lean_dec(x_2782);
x_2786 = lean_box(0);
x_2787 = 0;
x_2788 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_2785, x_2755, x_2786, x_20, x_2783);
if (lean_obj_tag(x_2788) == 0)
{
lean_object* x_2789; lean_object* x_2790; lean_object* x_2791; lean_object* x_2792; lean_object* x_2793; lean_object* x_2794; lean_object* x_2795; lean_object* x_2796; lean_object* x_2797; lean_object* x_2798; lean_object* x_2799; 
x_2789 = lean_ctor_get(x_2788, 0);
lean_inc(x_2789);
x_2790 = lean_ctor_get(x_2788, 1);
lean_inc(x_2790);
if (lean_is_exclusive(x_2788)) {
 lean_ctor_release(x_2788, 0);
 lean_ctor_release(x_2788, 1);
 x_2791 = x_2788;
} else {
 lean_dec_ref(x_2788);
 x_2791 = lean_box(0);
}
x_2792 = lean_ctor_get(x_2789, 0);
lean_inc(x_2792);
x_2793 = lean_ctor_get(x_2789, 1);
lean_inc(x_2793);
lean_dec(x_2789);
x_2794 = l_Lean_Name_inhabited;
x_2795 = lean_array_get(x_2794, x_2792, x_2731);
lean_inc(x_2795);
x_2796 = l_Lean_mkFVar(x_2795);
x_2797 = lean_array_get(x_2794, x_2792, x_2751);
lean_dec(x_2792);
lean_inc(x_2797);
x_2798 = l_Lean_mkFVar(x_2797);
lean_inc(x_2793);
x_2799 = l_Lean_Meta_getMVarDecl(x_2793, x_20, x_2790);
lean_dec(x_20);
if (lean_obj_tag(x_2799) == 0)
{
lean_object* x_2800; lean_object* x_2801; lean_object* x_2802; lean_object* x_2803; lean_object* x_2804; lean_object* x_2805; uint8_t x_2806; lean_object* x_2807; lean_object* x_2808; 
x_2800 = lean_ctor_get(x_2799, 0);
lean_inc(x_2800);
x_2801 = lean_ctor_get(x_2799, 1);
lean_inc(x_2801);
if (lean_is_exclusive(x_2799)) {
 lean_ctor_release(x_2799, 0);
 lean_ctor_release(x_2799, 1);
 x_2802 = x_2799;
} else {
 lean_dec_ref(x_2799);
 x_2802 = lean_box(0);
}
x_2803 = lean_ctor_get(x_2800, 1);
lean_inc(x_2803);
x_2804 = lean_ctor_get(x_2800, 4);
lean_inc(x_2804);
x_2805 = lean_array_get_size(x_2804);
x_2806 = lean_nat_dec_eq(x_18, x_2805);
lean_dec(x_2805);
lean_dec(x_18);
lean_inc(x_2804);
if (lean_is_scalar(x_2733)) {
 x_2807 = lean_alloc_ctor(0, 5, 0);
} else {
 x_2807 = x_2733;
}
lean_ctor_set(x_2807, 0, x_11);
lean_ctor_set(x_2807, 1, x_2803);
lean_ctor_set(x_2807, 2, x_2804);
lean_ctor_set(x_2807, 3, x_13);
lean_ctor_set(x_2807, 4, x_14);
if (x_2806 == 0)
{
lean_object* x_3641; 
lean_dec(x_2804);
lean_dec(x_2800);
lean_dec(x_16);
lean_dec(x_8);
x_3641 = lean_box(0);
x_2808 = x_3641;
goto block_3640;
}
else
{
uint8_t x_3642; 
x_3642 = l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__3(x_8, x_2800, lean_box(0), x_16, x_2804, x_2731);
lean_dec(x_2804);
lean_dec(x_16);
lean_dec(x_2800);
lean_dec(x_8);
if (x_3642 == 0)
{
lean_object* x_3643; 
x_3643 = lean_box(0);
x_2808 = x_3643;
goto block_3640;
}
else
{
lean_object* x_3644; 
lean_dec(x_2802);
lean_dec(x_2791);
lean_inc(x_2793);
x_3644 = l_Lean_Meta_getMVarDecl(x_2793, x_2807, x_2801);
if (lean_obj_tag(x_3644) == 0)
{
lean_object* x_3645; lean_object* x_3646; lean_object* x_3647; lean_object* x_3648; 
x_3645 = lean_ctor_get(x_3644, 0);
lean_inc(x_3645);
x_3646 = lean_ctor_get(x_3644, 1);
lean_inc(x_3646);
lean_dec(x_3644);
x_3647 = lean_ctor_get(x_3645, 2);
lean_inc(x_3647);
lean_dec(x_3645);
lean_inc(x_2807);
lean_inc(x_2797);
x_3648 = l_Lean_Meta_getLocalDecl(x_2797, x_2807, x_3646);
if (lean_obj_tag(x_3648) == 0)
{
lean_object* x_3649; lean_object* x_3650; lean_object* x_3651; lean_object* x_3991; uint8_t x_3992; 
x_3649 = lean_ctor_get(x_3648, 0);
lean_inc(x_3649);
x_3650 = lean_ctor_get(x_3648, 1);
lean_inc(x_3650);
lean_dec(x_3648);
x_3991 = l_Lean_LocalDecl_type(x_3649);
lean_dec(x_3649);
x_3992 = l_Lean_Expr_isAppOfArity___main(x_3991, x_2745, x_2746);
if (x_3992 == 0)
{
lean_object* x_3993; lean_object* x_3994; lean_object* x_3995; 
lean_dec(x_3991);
lean_dec(x_3647);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3993 = l_Lean_Meta_isClassQuick___main___closed__1;
x_3994 = l_unreachable_x21___rarg(x_3993);
x_3995 = lean_apply_2(x_3994, x_2807, x_3650);
return x_3995;
}
else
{
lean_object* x_3996; 
x_3996 = l_Lean_Expr_getAppNumArgsAux___main(x_3991, x_2731);
if (x_2759 == 0)
{
lean_object* x_3997; lean_object* x_3998; lean_object* x_3999; 
x_3997 = lean_nat_sub(x_3996, x_2755);
lean_dec(x_3996);
x_3998 = lean_nat_sub(x_3997, x_2751);
lean_dec(x_3997);
x_3999 = l_Lean_Expr_getRevArg_x21___main(x_3991, x_3998);
lean_dec(x_3991);
x_3651 = x_3999;
goto block_3990;
}
else
{
lean_object* x_4000; lean_object* x_4001; lean_object* x_4002; 
x_4000 = lean_nat_sub(x_3996, x_2751);
lean_dec(x_3996);
x_4001 = lean_nat_sub(x_4000, x_2751);
lean_dec(x_4000);
x_4002 = l_Lean_Expr_getRevArg_x21___main(x_3991, x_4001);
lean_dec(x_3991);
x_3651 = x_4002;
goto block_3990;
}
}
block_3990:
{
lean_object* x_3652; lean_object* x_3653; uint8_t x_3654; 
x_3652 = lean_ctor_get(x_3650, 1);
lean_inc(x_3652);
lean_inc(x_3647);
x_3653 = l_Lean_MetavarContext_exprDependsOn(x_3652, x_3647, x_2797);
x_3654 = lean_unbox(x_3653);
lean_dec(x_3653);
if (x_3654 == 0)
{
lean_object* x_3655; lean_object* x_3656; lean_object* x_3657; 
x_3655 = l_Lean_mkOptionalNode___closed__2;
x_3656 = lean_array_push(x_3655, x_2796);
lean_inc(x_2807);
lean_inc(x_3647);
lean_inc(x_3656);
x_3657 = l_Lean_Meta_mkLambda(x_3656, x_3647, x_2807, x_3650);
if (lean_obj_tag(x_3657) == 0)
{
lean_object* x_3658; lean_object* x_3659; lean_object* x_3660; lean_object* x_3661; lean_object* x_3662; lean_object* x_3663; 
x_3658 = lean_ctor_get(x_3657, 0);
lean_inc(x_3658);
x_3659 = lean_ctor_get(x_3657, 1);
lean_inc(x_3659);
lean_dec(x_3657);
x_3660 = lean_expr_abstract(x_3647, x_3656);
lean_dec(x_3656);
lean_dec(x_3647);
x_3661 = lean_expr_instantiate1(x_3660, x_3651);
lean_dec(x_3651);
lean_dec(x_3660);
if (x_2759 == 0)
{
lean_object* x_3754; 
lean_inc(x_2807);
x_3754 = l_Lean_Meta_mkEqSymm(x_2798, x_2807, x_3659);
if (lean_obj_tag(x_3754) == 0)
{
lean_object* x_3755; lean_object* x_3756; 
x_3755 = lean_ctor_get(x_3754, 0);
lean_inc(x_3755);
x_3756 = lean_ctor_get(x_3754, 1);
lean_inc(x_3756);
lean_dec(x_3754);
x_3662 = x_3755;
x_3663 = x_3756;
goto block_3753;
}
else
{
uint8_t x_3757; 
lean_dec(x_3661);
lean_dec(x_3658);
lean_dec(x_2807);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3757 = !lean_is_exclusive(x_3754);
if (x_3757 == 0)
{
return x_3754;
}
else
{
lean_object* x_3758; lean_object* x_3759; lean_object* x_3760; 
x_3758 = lean_ctor_get(x_3754, 0);
x_3759 = lean_ctor_get(x_3754, 1);
lean_inc(x_3759);
lean_inc(x_3758);
lean_dec(x_3754);
x_3760 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3760, 0, x_3758);
lean_ctor_set(x_3760, 1, x_3759);
return x_3760;
}
}
}
else
{
x_3662 = x_2798;
x_3663 = x_3659;
goto block_3753;
}
block_3753:
{
uint8_t x_3664; lean_object* x_3665; lean_object* x_3666; lean_object* x_3667; lean_object* x_3668; 
x_3664 = 2;
lean_inc(x_2807);
x_3665 = l_Lean_Meta_mkFreshExprMVar(x_3661, x_2736, x_3664, x_2807, x_3663);
x_3666 = lean_ctor_get(x_3665, 0);
lean_inc(x_3666);
x_3667 = lean_ctor_get(x_3665, 1);
lean_inc(x_3667);
lean_dec(x_3665);
lean_inc(x_2807);
lean_inc(x_3666);
x_3668 = l_Lean_Meta_mkEqNDRec(x_3658, x_3666, x_3662, x_2807, x_3667);
if (lean_obj_tag(x_3668) == 0)
{
lean_object* x_3669; lean_object* x_3670; uint8_t x_3671; 
x_3669 = lean_ctor_get(x_3668, 1);
lean_inc(x_3669);
x_3670 = lean_ctor_get(x_3668, 0);
lean_inc(x_3670);
lean_dec(x_3668);
x_3671 = !lean_is_exclusive(x_3669);
if (x_3671 == 0)
{
lean_object* x_3672; lean_object* x_3673; lean_object* x_3674; lean_object* x_3675; 
x_3672 = lean_ctor_get(x_3669, 1);
x_3673 = l_Lean_MetavarContext_assignExpr(x_3672, x_2793, x_3670);
lean_ctor_set(x_3669, 1, x_3673);
x_3674 = l_Lean_Expr_mvarId_x21(x_3666);
lean_dec(x_3666);
x_3675 = l_Lean_Meta_clear(x_3674, x_2797, x_2807, x_3669);
if (lean_obj_tag(x_3675) == 0)
{
lean_object* x_3676; lean_object* x_3677; lean_object* x_3678; 
x_3676 = lean_ctor_get(x_3675, 0);
lean_inc(x_3676);
x_3677 = lean_ctor_get(x_3675, 1);
lean_inc(x_3677);
lean_dec(x_3675);
x_3678 = l_Lean_Meta_clear(x_3676, x_2795, x_2807, x_3677);
if (lean_obj_tag(x_3678) == 0)
{
lean_object* x_3679; lean_object* x_3680; lean_object* x_3681; lean_object* x_3682; lean_object* x_3683; 
x_3679 = lean_ctor_get(x_3678, 0);
lean_inc(x_3679);
x_3680 = lean_ctor_get(x_3678, 1);
lean_inc(x_3680);
lean_dec(x_3678);
x_3681 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_3682 = lean_nat_sub(x_3681, x_2755);
lean_dec(x_3681);
x_3683 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_3679, x_3682, x_2786, x_2807, x_3680);
lean_dec(x_2807);
if (lean_obj_tag(x_3683) == 0)
{
uint8_t x_3684; 
x_3684 = !lean_is_exclusive(x_3683);
if (x_3684 == 0)
{
lean_object* x_3685; uint8_t x_3686; 
x_3685 = lean_ctor_get(x_3683, 0);
x_3686 = !lean_is_exclusive(x_3685);
if (x_3686 == 0)
{
lean_object* x_3687; lean_object* x_3688; 
x_3687 = lean_ctor_get(x_3685, 0);
lean_dec(x_3687);
x_3688 = lean_box(0);
lean_ctor_set(x_3685, 0, x_3688);
return x_3683;
}
else
{
lean_object* x_3689; lean_object* x_3690; lean_object* x_3691; 
x_3689 = lean_ctor_get(x_3685, 1);
lean_inc(x_3689);
lean_dec(x_3685);
x_3690 = lean_box(0);
x_3691 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3691, 0, x_3690);
lean_ctor_set(x_3691, 1, x_3689);
lean_ctor_set(x_3683, 0, x_3691);
return x_3683;
}
}
else
{
lean_object* x_3692; lean_object* x_3693; lean_object* x_3694; lean_object* x_3695; lean_object* x_3696; lean_object* x_3697; lean_object* x_3698; 
x_3692 = lean_ctor_get(x_3683, 0);
x_3693 = lean_ctor_get(x_3683, 1);
lean_inc(x_3693);
lean_inc(x_3692);
lean_dec(x_3683);
x_3694 = lean_ctor_get(x_3692, 1);
lean_inc(x_3694);
if (lean_is_exclusive(x_3692)) {
 lean_ctor_release(x_3692, 0);
 lean_ctor_release(x_3692, 1);
 x_3695 = x_3692;
} else {
 lean_dec_ref(x_3692);
 x_3695 = lean_box(0);
}
x_3696 = lean_box(0);
if (lean_is_scalar(x_3695)) {
 x_3697 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3697 = x_3695;
}
lean_ctor_set(x_3697, 0, x_3696);
lean_ctor_set(x_3697, 1, x_3694);
x_3698 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3698, 0, x_3697);
lean_ctor_set(x_3698, 1, x_3693);
return x_3698;
}
}
else
{
uint8_t x_3699; 
x_3699 = !lean_is_exclusive(x_3683);
if (x_3699 == 0)
{
return x_3683;
}
else
{
lean_object* x_3700; lean_object* x_3701; lean_object* x_3702; 
x_3700 = lean_ctor_get(x_3683, 0);
x_3701 = lean_ctor_get(x_3683, 1);
lean_inc(x_3701);
lean_inc(x_3700);
lean_dec(x_3683);
x_3702 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3702, 0, x_3700);
lean_ctor_set(x_3702, 1, x_3701);
return x_3702;
}
}
}
else
{
uint8_t x_3703; 
lean_dec(x_2807);
lean_dec(x_2784);
x_3703 = !lean_is_exclusive(x_3678);
if (x_3703 == 0)
{
return x_3678;
}
else
{
lean_object* x_3704; lean_object* x_3705; lean_object* x_3706; 
x_3704 = lean_ctor_get(x_3678, 0);
x_3705 = lean_ctor_get(x_3678, 1);
lean_inc(x_3705);
lean_inc(x_3704);
lean_dec(x_3678);
x_3706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3706, 0, x_3704);
lean_ctor_set(x_3706, 1, x_3705);
return x_3706;
}
}
}
else
{
uint8_t x_3707; 
lean_dec(x_2807);
lean_dec(x_2795);
lean_dec(x_2784);
x_3707 = !lean_is_exclusive(x_3675);
if (x_3707 == 0)
{
return x_3675;
}
else
{
lean_object* x_3708; lean_object* x_3709; lean_object* x_3710; 
x_3708 = lean_ctor_get(x_3675, 0);
x_3709 = lean_ctor_get(x_3675, 1);
lean_inc(x_3709);
lean_inc(x_3708);
lean_dec(x_3675);
x_3710 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3710, 0, x_3708);
lean_ctor_set(x_3710, 1, x_3709);
return x_3710;
}
}
}
else
{
lean_object* x_3711; lean_object* x_3712; lean_object* x_3713; lean_object* x_3714; lean_object* x_3715; lean_object* x_3716; lean_object* x_3717; lean_object* x_3718; lean_object* x_3719; lean_object* x_3720; 
x_3711 = lean_ctor_get(x_3669, 0);
x_3712 = lean_ctor_get(x_3669, 1);
x_3713 = lean_ctor_get(x_3669, 2);
x_3714 = lean_ctor_get(x_3669, 3);
x_3715 = lean_ctor_get(x_3669, 4);
x_3716 = lean_ctor_get(x_3669, 5);
lean_inc(x_3716);
lean_inc(x_3715);
lean_inc(x_3714);
lean_inc(x_3713);
lean_inc(x_3712);
lean_inc(x_3711);
lean_dec(x_3669);
x_3717 = l_Lean_MetavarContext_assignExpr(x_3712, x_2793, x_3670);
x_3718 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_3718, 0, x_3711);
lean_ctor_set(x_3718, 1, x_3717);
lean_ctor_set(x_3718, 2, x_3713);
lean_ctor_set(x_3718, 3, x_3714);
lean_ctor_set(x_3718, 4, x_3715);
lean_ctor_set(x_3718, 5, x_3716);
x_3719 = l_Lean_Expr_mvarId_x21(x_3666);
lean_dec(x_3666);
x_3720 = l_Lean_Meta_clear(x_3719, x_2797, x_2807, x_3718);
if (lean_obj_tag(x_3720) == 0)
{
lean_object* x_3721; lean_object* x_3722; lean_object* x_3723; 
x_3721 = lean_ctor_get(x_3720, 0);
lean_inc(x_3721);
x_3722 = lean_ctor_get(x_3720, 1);
lean_inc(x_3722);
lean_dec(x_3720);
x_3723 = l_Lean_Meta_clear(x_3721, x_2795, x_2807, x_3722);
if (lean_obj_tag(x_3723) == 0)
{
lean_object* x_3724; lean_object* x_3725; lean_object* x_3726; lean_object* x_3727; lean_object* x_3728; 
x_3724 = lean_ctor_get(x_3723, 0);
lean_inc(x_3724);
x_3725 = lean_ctor_get(x_3723, 1);
lean_inc(x_3725);
lean_dec(x_3723);
x_3726 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_3727 = lean_nat_sub(x_3726, x_2755);
lean_dec(x_3726);
x_3728 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_3724, x_3727, x_2786, x_2807, x_3725);
lean_dec(x_2807);
if (lean_obj_tag(x_3728) == 0)
{
lean_object* x_3729; lean_object* x_3730; lean_object* x_3731; lean_object* x_3732; lean_object* x_3733; lean_object* x_3734; lean_object* x_3735; lean_object* x_3736; 
x_3729 = lean_ctor_get(x_3728, 0);
lean_inc(x_3729);
x_3730 = lean_ctor_get(x_3728, 1);
lean_inc(x_3730);
if (lean_is_exclusive(x_3728)) {
 lean_ctor_release(x_3728, 0);
 lean_ctor_release(x_3728, 1);
 x_3731 = x_3728;
} else {
 lean_dec_ref(x_3728);
 x_3731 = lean_box(0);
}
x_3732 = lean_ctor_get(x_3729, 1);
lean_inc(x_3732);
if (lean_is_exclusive(x_3729)) {
 lean_ctor_release(x_3729, 0);
 lean_ctor_release(x_3729, 1);
 x_3733 = x_3729;
} else {
 lean_dec_ref(x_3729);
 x_3733 = lean_box(0);
}
x_3734 = lean_box(0);
if (lean_is_scalar(x_3733)) {
 x_3735 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3735 = x_3733;
}
lean_ctor_set(x_3735, 0, x_3734);
lean_ctor_set(x_3735, 1, x_3732);
if (lean_is_scalar(x_3731)) {
 x_3736 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3736 = x_3731;
}
lean_ctor_set(x_3736, 0, x_3735);
lean_ctor_set(x_3736, 1, x_3730);
return x_3736;
}
else
{
lean_object* x_3737; lean_object* x_3738; lean_object* x_3739; lean_object* x_3740; 
x_3737 = lean_ctor_get(x_3728, 0);
lean_inc(x_3737);
x_3738 = lean_ctor_get(x_3728, 1);
lean_inc(x_3738);
if (lean_is_exclusive(x_3728)) {
 lean_ctor_release(x_3728, 0);
 lean_ctor_release(x_3728, 1);
 x_3739 = x_3728;
} else {
 lean_dec_ref(x_3728);
 x_3739 = lean_box(0);
}
if (lean_is_scalar(x_3739)) {
 x_3740 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3740 = x_3739;
}
lean_ctor_set(x_3740, 0, x_3737);
lean_ctor_set(x_3740, 1, x_3738);
return x_3740;
}
}
else
{
lean_object* x_3741; lean_object* x_3742; lean_object* x_3743; lean_object* x_3744; 
lean_dec(x_2807);
lean_dec(x_2784);
x_3741 = lean_ctor_get(x_3723, 0);
lean_inc(x_3741);
x_3742 = lean_ctor_get(x_3723, 1);
lean_inc(x_3742);
if (lean_is_exclusive(x_3723)) {
 lean_ctor_release(x_3723, 0);
 lean_ctor_release(x_3723, 1);
 x_3743 = x_3723;
} else {
 lean_dec_ref(x_3723);
 x_3743 = lean_box(0);
}
if (lean_is_scalar(x_3743)) {
 x_3744 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3744 = x_3743;
}
lean_ctor_set(x_3744, 0, x_3741);
lean_ctor_set(x_3744, 1, x_3742);
return x_3744;
}
}
else
{
lean_object* x_3745; lean_object* x_3746; lean_object* x_3747; lean_object* x_3748; 
lean_dec(x_2807);
lean_dec(x_2795);
lean_dec(x_2784);
x_3745 = lean_ctor_get(x_3720, 0);
lean_inc(x_3745);
x_3746 = lean_ctor_get(x_3720, 1);
lean_inc(x_3746);
if (lean_is_exclusive(x_3720)) {
 lean_ctor_release(x_3720, 0);
 lean_ctor_release(x_3720, 1);
 x_3747 = x_3720;
} else {
 lean_dec_ref(x_3720);
 x_3747 = lean_box(0);
}
if (lean_is_scalar(x_3747)) {
 x_3748 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3748 = x_3747;
}
lean_ctor_set(x_3748, 0, x_3745);
lean_ctor_set(x_3748, 1, x_3746);
return x_3748;
}
}
}
else
{
uint8_t x_3749; 
lean_dec(x_3666);
lean_dec(x_2807);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
x_3749 = !lean_is_exclusive(x_3668);
if (x_3749 == 0)
{
return x_3668;
}
else
{
lean_object* x_3750; lean_object* x_3751; lean_object* x_3752; 
x_3750 = lean_ctor_get(x_3668, 0);
x_3751 = lean_ctor_get(x_3668, 1);
lean_inc(x_3751);
lean_inc(x_3750);
lean_dec(x_3668);
x_3752 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3752, 0, x_3750);
lean_ctor_set(x_3752, 1, x_3751);
return x_3752;
}
}
}
}
else
{
uint8_t x_3761; 
lean_dec(x_3656);
lean_dec(x_3651);
lean_dec(x_3647);
lean_dec(x_2807);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3761 = !lean_is_exclusive(x_3657);
if (x_3761 == 0)
{
return x_3657;
}
else
{
lean_object* x_3762; lean_object* x_3763; lean_object* x_3764; 
x_3762 = lean_ctor_get(x_3657, 0);
x_3763 = lean_ctor_get(x_3657, 1);
lean_inc(x_3763);
lean_inc(x_3762);
lean_dec(x_3657);
x_3764 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3764, 0, x_3762);
lean_ctor_set(x_3764, 1, x_3763);
return x_3764;
}
}
}
else
{
lean_object* x_3765; lean_object* x_3766; lean_object* x_3767; lean_object* x_3768; lean_object* x_3769; 
x_3765 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2796);
x_3766 = lean_array_push(x_3765, x_2796);
x_3767 = lean_expr_abstract(x_3647, x_3766);
lean_dec(x_3766);
x_3768 = lean_expr_instantiate1(x_3767, x_3651);
lean_dec(x_3767);
lean_inc(x_2807);
lean_inc(x_3651);
x_3769 = l_Lean_Meta_mkEqRefl(x_3651, x_2807, x_3650);
if (lean_obj_tag(x_3769) == 0)
{
lean_object* x_3770; lean_object* x_3771; lean_object* x_3772; lean_object* x_3773; lean_object* x_3774; 
x_3770 = lean_ctor_get(x_3769, 0);
lean_inc(x_3770);
x_3771 = lean_ctor_get(x_3769, 1);
lean_inc(x_3771);
lean_dec(x_3769);
lean_inc(x_2798);
x_3772 = lean_array_push(x_3765, x_2798);
x_3773 = lean_expr_abstract(x_3768, x_3772);
lean_dec(x_3768);
x_3774 = lean_expr_instantiate1(x_3773, x_3770);
lean_dec(x_3770);
lean_dec(x_3773);
if (x_2759 == 0)
{
lean_object* x_3775; 
lean_inc(x_2807);
lean_inc(x_2796);
x_3775 = l_Lean_Meta_mkEq(x_3651, x_2796, x_2807, x_3771);
if (lean_obj_tag(x_3775) == 0)
{
lean_object* x_3776; lean_object* x_3777; lean_object* x_3778; lean_object* x_3779; uint8_t x_3780; lean_object* x_3781; 
x_3776 = lean_ctor_get(x_3775, 0);
lean_inc(x_3776);
x_3777 = lean_ctor_get(x_3775, 1);
lean_inc(x_3777);
lean_dec(x_3775);
x_3778 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__1___boxed), 7, 4);
lean_closure_set(x_3778, 0, x_3647);
lean_closure_set(x_3778, 1, x_3772);
lean_closure_set(x_3778, 2, x_2777);
lean_closure_set(x_3778, 3, x_2796);
x_3779 = l_Lean_Meta_substCore___closed__18;
x_3780 = 0;
lean_inc(x_2807);
x_3781 = l_Lean_Meta_withLocalDecl___rarg(x_3779, x_3776, x_3780, x_3778, x_2807, x_3777);
if (lean_obj_tag(x_3781) == 0)
{
lean_object* x_3782; lean_object* x_3783; lean_object* x_3784; 
x_3782 = lean_ctor_get(x_3781, 0);
lean_inc(x_3782);
x_3783 = lean_ctor_get(x_3781, 1);
lean_inc(x_3783);
lean_dec(x_3781);
lean_inc(x_2807);
x_3784 = l_Lean_Meta_mkEqSymm(x_2798, x_2807, x_3783);
if (lean_obj_tag(x_3784) == 0)
{
lean_object* x_3785; lean_object* x_3786; uint8_t x_3787; lean_object* x_3788; lean_object* x_3789; lean_object* x_3790; lean_object* x_3791; 
x_3785 = lean_ctor_get(x_3784, 0);
lean_inc(x_3785);
x_3786 = lean_ctor_get(x_3784, 1);
lean_inc(x_3786);
lean_dec(x_3784);
x_3787 = 2;
lean_inc(x_2807);
x_3788 = l_Lean_Meta_mkFreshExprMVar(x_3774, x_2736, x_3787, x_2807, x_3786);
x_3789 = lean_ctor_get(x_3788, 0);
lean_inc(x_3789);
x_3790 = lean_ctor_get(x_3788, 1);
lean_inc(x_3790);
lean_dec(x_3788);
lean_inc(x_2807);
lean_inc(x_3789);
x_3791 = l_Lean_Meta_mkEqRec(x_3782, x_3789, x_3785, x_2807, x_3790);
if (lean_obj_tag(x_3791) == 0)
{
lean_object* x_3792; lean_object* x_3793; uint8_t x_3794; 
x_3792 = lean_ctor_get(x_3791, 1);
lean_inc(x_3792);
x_3793 = lean_ctor_get(x_3791, 0);
lean_inc(x_3793);
lean_dec(x_3791);
x_3794 = !lean_is_exclusive(x_3792);
if (x_3794 == 0)
{
lean_object* x_3795; lean_object* x_3796; lean_object* x_3797; lean_object* x_3798; 
x_3795 = lean_ctor_get(x_3792, 1);
x_3796 = l_Lean_MetavarContext_assignExpr(x_3795, x_2793, x_3793);
lean_ctor_set(x_3792, 1, x_3796);
x_3797 = l_Lean_Expr_mvarId_x21(x_3789);
lean_dec(x_3789);
x_3798 = l_Lean_Meta_clear(x_3797, x_2797, x_2807, x_3792);
if (lean_obj_tag(x_3798) == 0)
{
lean_object* x_3799; lean_object* x_3800; lean_object* x_3801; 
x_3799 = lean_ctor_get(x_3798, 0);
lean_inc(x_3799);
x_3800 = lean_ctor_get(x_3798, 1);
lean_inc(x_3800);
lean_dec(x_3798);
x_3801 = l_Lean_Meta_clear(x_3799, x_2795, x_2807, x_3800);
if (lean_obj_tag(x_3801) == 0)
{
lean_object* x_3802; lean_object* x_3803; lean_object* x_3804; lean_object* x_3805; lean_object* x_3806; 
x_3802 = lean_ctor_get(x_3801, 0);
lean_inc(x_3802);
x_3803 = lean_ctor_get(x_3801, 1);
lean_inc(x_3803);
lean_dec(x_3801);
x_3804 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_3805 = lean_nat_sub(x_3804, x_2755);
lean_dec(x_3804);
x_3806 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_3802, x_3805, x_2786, x_2807, x_3803);
lean_dec(x_2807);
if (lean_obj_tag(x_3806) == 0)
{
uint8_t x_3807; 
x_3807 = !lean_is_exclusive(x_3806);
if (x_3807 == 0)
{
lean_object* x_3808; uint8_t x_3809; 
x_3808 = lean_ctor_get(x_3806, 0);
x_3809 = !lean_is_exclusive(x_3808);
if (x_3809 == 0)
{
lean_object* x_3810; lean_object* x_3811; 
x_3810 = lean_ctor_get(x_3808, 0);
lean_dec(x_3810);
x_3811 = lean_box(0);
lean_ctor_set(x_3808, 0, x_3811);
return x_3806;
}
else
{
lean_object* x_3812; lean_object* x_3813; lean_object* x_3814; 
x_3812 = lean_ctor_get(x_3808, 1);
lean_inc(x_3812);
lean_dec(x_3808);
x_3813 = lean_box(0);
x_3814 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3814, 0, x_3813);
lean_ctor_set(x_3814, 1, x_3812);
lean_ctor_set(x_3806, 0, x_3814);
return x_3806;
}
}
else
{
lean_object* x_3815; lean_object* x_3816; lean_object* x_3817; lean_object* x_3818; lean_object* x_3819; lean_object* x_3820; lean_object* x_3821; 
x_3815 = lean_ctor_get(x_3806, 0);
x_3816 = lean_ctor_get(x_3806, 1);
lean_inc(x_3816);
lean_inc(x_3815);
lean_dec(x_3806);
x_3817 = lean_ctor_get(x_3815, 1);
lean_inc(x_3817);
if (lean_is_exclusive(x_3815)) {
 lean_ctor_release(x_3815, 0);
 lean_ctor_release(x_3815, 1);
 x_3818 = x_3815;
} else {
 lean_dec_ref(x_3815);
 x_3818 = lean_box(0);
}
x_3819 = lean_box(0);
if (lean_is_scalar(x_3818)) {
 x_3820 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3820 = x_3818;
}
lean_ctor_set(x_3820, 0, x_3819);
lean_ctor_set(x_3820, 1, x_3817);
x_3821 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3821, 0, x_3820);
lean_ctor_set(x_3821, 1, x_3816);
return x_3821;
}
}
else
{
uint8_t x_3822; 
x_3822 = !lean_is_exclusive(x_3806);
if (x_3822 == 0)
{
return x_3806;
}
else
{
lean_object* x_3823; lean_object* x_3824; lean_object* x_3825; 
x_3823 = lean_ctor_get(x_3806, 0);
x_3824 = lean_ctor_get(x_3806, 1);
lean_inc(x_3824);
lean_inc(x_3823);
lean_dec(x_3806);
x_3825 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3825, 0, x_3823);
lean_ctor_set(x_3825, 1, x_3824);
return x_3825;
}
}
}
else
{
uint8_t x_3826; 
lean_dec(x_2807);
lean_dec(x_2784);
x_3826 = !lean_is_exclusive(x_3801);
if (x_3826 == 0)
{
return x_3801;
}
else
{
lean_object* x_3827; lean_object* x_3828; lean_object* x_3829; 
x_3827 = lean_ctor_get(x_3801, 0);
x_3828 = lean_ctor_get(x_3801, 1);
lean_inc(x_3828);
lean_inc(x_3827);
lean_dec(x_3801);
x_3829 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3829, 0, x_3827);
lean_ctor_set(x_3829, 1, x_3828);
return x_3829;
}
}
}
else
{
uint8_t x_3830; 
lean_dec(x_2807);
lean_dec(x_2795);
lean_dec(x_2784);
x_3830 = !lean_is_exclusive(x_3798);
if (x_3830 == 0)
{
return x_3798;
}
else
{
lean_object* x_3831; lean_object* x_3832; lean_object* x_3833; 
x_3831 = lean_ctor_get(x_3798, 0);
x_3832 = lean_ctor_get(x_3798, 1);
lean_inc(x_3832);
lean_inc(x_3831);
lean_dec(x_3798);
x_3833 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3833, 0, x_3831);
lean_ctor_set(x_3833, 1, x_3832);
return x_3833;
}
}
}
else
{
lean_object* x_3834; lean_object* x_3835; lean_object* x_3836; lean_object* x_3837; lean_object* x_3838; lean_object* x_3839; lean_object* x_3840; lean_object* x_3841; lean_object* x_3842; lean_object* x_3843; 
x_3834 = lean_ctor_get(x_3792, 0);
x_3835 = lean_ctor_get(x_3792, 1);
x_3836 = lean_ctor_get(x_3792, 2);
x_3837 = lean_ctor_get(x_3792, 3);
x_3838 = lean_ctor_get(x_3792, 4);
x_3839 = lean_ctor_get(x_3792, 5);
lean_inc(x_3839);
lean_inc(x_3838);
lean_inc(x_3837);
lean_inc(x_3836);
lean_inc(x_3835);
lean_inc(x_3834);
lean_dec(x_3792);
x_3840 = l_Lean_MetavarContext_assignExpr(x_3835, x_2793, x_3793);
x_3841 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_3841, 0, x_3834);
lean_ctor_set(x_3841, 1, x_3840);
lean_ctor_set(x_3841, 2, x_3836);
lean_ctor_set(x_3841, 3, x_3837);
lean_ctor_set(x_3841, 4, x_3838);
lean_ctor_set(x_3841, 5, x_3839);
x_3842 = l_Lean_Expr_mvarId_x21(x_3789);
lean_dec(x_3789);
x_3843 = l_Lean_Meta_clear(x_3842, x_2797, x_2807, x_3841);
if (lean_obj_tag(x_3843) == 0)
{
lean_object* x_3844; lean_object* x_3845; lean_object* x_3846; 
x_3844 = lean_ctor_get(x_3843, 0);
lean_inc(x_3844);
x_3845 = lean_ctor_get(x_3843, 1);
lean_inc(x_3845);
lean_dec(x_3843);
x_3846 = l_Lean_Meta_clear(x_3844, x_2795, x_2807, x_3845);
if (lean_obj_tag(x_3846) == 0)
{
lean_object* x_3847; lean_object* x_3848; lean_object* x_3849; lean_object* x_3850; lean_object* x_3851; 
x_3847 = lean_ctor_get(x_3846, 0);
lean_inc(x_3847);
x_3848 = lean_ctor_get(x_3846, 1);
lean_inc(x_3848);
lean_dec(x_3846);
x_3849 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_3850 = lean_nat_sub(x_3849, x_2755);
lean_dec(x_3849);
x_3851 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_3847, x_3850, x_2786, x_2807, x_3848);
lean_dec(x_2807);
if (lean_obj_tag(x_3851) == 0)
{
lean_object* x_3852; lean_object* x_3853; lean_object* x_3854; lean_object* x_3855; lean_object* x_3856; lean_object* x_3857; lean_object* x_3858; lean_object* x_3859; 
x_3852 = lean_ctor_get(x_3851, 0);
lean_inc(x_3852);
x_3853 = lean_ctor_get(x_3851, 1);
lean_inc(x_3853);
if (lean_is_exclusive(x_3851)) {
 lean_ctor_release(x_3851, 0);
 lean_ctor_release(x_3851, 1);
 x_3854 = x_3851;
} else {
 lean_dec_ref(x_3851);
 x_3854 = lean_box(0);
}
x_3855 = lean_ctor_get(x_3852, 1);
lean_inc(x_3855);
if (lean_is_exclusive(x_3852)) {
 lean_ctor_release(x_3852, 0);
 lean_ctor_release(x_3852, 1);
 x_3856 = x_3852;
} else {
 lean_dec_ref(x_3852);
 x_3856 = lean_box(0);
}
x_3857 = lean_box(0);
if (lean_is_scalar(x_3856)) {
 x_3858 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3858 = x_3856;
}
lean_ctor_set(x_3858, 0, x_3857);
lean_ctor_set(x_3858, 1, x_3855);
if (lean_is_scalar(x_3854)) {
 x_3859 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3859 = x_3854;
}
lean_ctor_set(x_3859, 0, x_3858);
lean_ctor_set(x_3859, 1, x_3853);
return x_3859;
}
else
{
lean_object* x_3860; lean_object* x_3861; lean_object* x_3862; lean_object* x_3863; 
x_3860 = lean_ctor_get(x_3851, 0);
lean_inc(x_3860);
x_3861 = lean_ctor_get(x_3851, 1);
lean_inc(x_3861);
if (lean_is_exclusive(x_3851)) {
 lean_ctor_release(x_3851, 0);
 lean_ctor_release(x_3851, 1);
 x_3862 = x_3851;
} else {
 lean_dec_ref(x_3851);
 x_3862 = lean_box(0);
}
if (lean_is_scalar(x_3862)) {
 x_3863 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3863 = x_3862;
}
lean_ctor_set(x_3863, 0, x_3860);
lean_ctor_set(x_3863, 1, x_3861);
return x_3863;
}
}
else
{
lean_object* x_3864; lean_object* x_3865; lean_object* x_3866; lean_object* x_3867; 
lean_dec(x_2807);
lean_dec(x_2784);
x_3864 = lean_ctor_get(x_3846, 0);
lean_inc(x_3864);
x_3865 = lean_ctor_get(x_3846, 1);
lean_inc(x_3865);
if (lean_is_exclusive(x_3846)) {
 lean_ctor_release(x_3846, 0);
 lean_ctor_release(x_3846, 1);
 x_3866 = x_3846;
} else {
 lean_dec_ref(x_3846);
 x_3866 = lean_box(0);
}
if (lean_is_scalar(x_3866)) {
 x_3867 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3867 = x_3866;
}
lean_ctor_set(x_3867, 0, x_3864);
lean_ctor_set(x_3867, 1, x_3865);
return x_3867;
}
}
else
{
lean_object* x_3868; lean_object* x_3869; lean_object* x_3870; lean_object* x_3871; 
lean_dec(x_2807);
lean_dec(x_2795);
lean_dec(x_2784);
x_3868 = lean_ctor_get(x_3843, 0);
lean_inc(x_3868);
x_3869 = lean_ctor_get(x_3843, 1);
lean_inc(x_3869);
if (lean_is_exclusive(x_3843)) {
 lean_ctor_release(x_3843, 0);
 lean_ctor_release(x_3843, 1);
 x_3870 = x_3843;
} else {
 lean_dec_ref(x_3843);
 x_3870 = lean_box(0);
}
if (lean_is_scalar(x_3870)) {
 x_3871 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3871 = x_3870;
}
lean_ctor_set(x_3871, 0, x_3868);
lean_ctor_set(x_3871, 1, x_3869);
return x_3871;
}
}
}
else
{
uint8_t x_3872; 
lean_dec(x_3789);
lean_dec(x_2807);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
x_3872 = !lean_is_exclusive(x_3791);
if (x_3872 == 0)
{
return x_3791;
}
else
{
lean_object* x_3873; lean_object* x_3874; lean_object* x_3875; 
x_3873 = lean_ctor_get(x_3791, 0);
x_3874 = lean_ctor_get(x_3791, 1);
lean_inc(x_3874);
lean_inc(x_3873);
lean_dec(x_3791);
x_3875 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3875, 0, x_3873);
lean_ctor_set(x_3875, 1, x_3874);
return x_3875;
}
}
}
else
{
uint8_t x_3876; 
lean_dec(x_3782);
lean_dec(x_3774);
lean_dec(x_2807);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3876 = !lean_is_exclusive(x_3784);
if (x_3876 == 0)
{
return x_3784;
}
else
{
lean_object* x_3877; lean_object* x_3878; lean_object* x_3879; 
x_3877 = lean_ctor_get(x_3784, 0);
x_3878 = lean_ctor_get(x_3784, 1);
lean_inc(x_3878);
lean_inc(x_3877);
lean_dec(x_3784);
x_3879 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3879, 0, x_3877);
lean_ctor_set(x_3879, 1, x_3878);
return x_3879;
}
}
}
else
{
uint8_t x_3880; 
lean_dec(x_3774);
lean_dec(x_2807);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3880 = !lean_is_exclusive(x_3781);
if (x_3880 == 0)
{
return x_3781;
}
else
{
lean_object* x_3881; lean_object* x_3882; lean_object* x_3883; 
x_3881 = lean_ctor_get(x_3781, 0);
x_3882 = lean_ctor_get(x_3781, 1);
lean_inc(x_3882);
lean_inc(x_3881);
lean_dec(x_3781);
x_3883 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3883, 0, x_3881);
lean_ctor_set(x_3883, 1, x_3882);
return x_3883;
}
}
}
else
{
uint8_t x_3884; 
lean_dec(x_3774);
lean_dec(x_3772);
lean_dec(x_3647);
lean_dec(x_2807);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3884 = !lean_is_exclusive(x_3775);
if (x_3884 == 0)
{
return x_3775;
}
else
{
lean_object* x_3885; lean_object* x_3886; lean_object* x_3887; 
x_3885 = lean_ctor_get(x_3775, 0);
x_3886 = lean_ctor_get(x_3775, 1);
lean_inc(x_3886);
lean_inc(x_3885);
lean_dec(x_3775);
x_3887 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3887, 0, x_3885);
lean_ctor_set(x_3887, 1, x_3886);
return x_3887;
}
}
}
else
{
lean_object* x_3888; lean_object* x_3889; lean_object* x_3890; 
lean_dec(x_3772);
lean_dec(x_3651);
x_3888 = lean_array_push(x_2777, x_2796);
lean_inc(x_2798);
x_3889 = lean_array_push(x_3888, x_2798);
lean_inc(x_2807);
x_3890 = l_Lean_Meta_mkLambda(x_3889, x_3647, x_2807, x_3771);
if (lean_obj_tag(x_3890) == 0)
{
lean_object* x_3891; lean_object* x_3892; uint8_t x_3893; lean_object* x_3894; lean_object* x_3895; lean_object* x_3896; lean_object* x_3897; 
x_3891 = lean_ctor_get(x_3890, 0);
lean_inc(x_3891);
x_3892 = lean_ctor_get(x_3890, 1);
lean_inc(x_3892);
lean_dec(x_3890);
x_3893 = 2;
lean_inc(x_2807);
x_3894 = l_Lean_Meta_mkFreshExprMVar(x_3774, x_2736, x_3893, x_2807, x_3892);
x_3895 = lean_ctor_get(x_3894, 0);
lean_inc(x_3895);
x_3896 = lean_ctor_get(x_3894, 1);
lean_inc(x_3896);
lean_dec(x_3894);
lean_inc(x_2807);
lean_inc(x_3895);
x_3897 = l_Lean_Meta_mkEqRec(x_3891, x_3895, x_2798, x_2807, x_3896);
if (lean_obj_tag(x_3897) == 0)
{
lean_object* x_3898; lean_object* x_3899; uint8_t x_3900; 
x_3898 = lean_ctor_get(x_3897, 1);
lean_inc(x_3898);
x_3899 = lean_ctor_get(x_3897, 0);
lean_inc(x_3899);
lean_dec(x_3897);
x_3900 = !lean_is_exclusive(x_3898);
if (x_3900 == 0)
{
lean_object* x_3901; lean_object* x_3902; lean_object* x_3903; lean_object* x_3904; 
x_3901 = lean_ctor_get(x_3898, 1);
x_3902 = l_Lean_MetavarContext_assignExpr(x_3901, x_2793, x_3899);
lean_ctor_set(x_3898, 1, x_3902);
x_3903 = l_Lean_Expr_mvarId_x21(x_3895);
lean_dec(x_3895);
x_3904 = l_Lean_Meta_clear(x_3903, x_2797, x_2807, x_3898);
if (lean_obj_tag(x_3904) == 0)
{
lean_object* x_3905; lean_object* x_3906; lean_object* x_3907; 
x_3905 = lean_ctor_get(x_3904, 0);
lean_inc(x_3905);
x_3906 = lean_ctor_get(x_3904, 1);
lean_inc(x_3906);
lean_dec(x_3904);
x_3907 = l_Lean_Meta_clear(x_3905, x_2795, x_2807, x_3906);
if (lean_obj_tag(x_3907) == 0)
{
lean_object* x_3908; lean_object* x_3909; lean_object* x_3910; lean_object* x_3911; lean_object* x_3912; 
x_3908 = lean_ctor_get(x_3907, 0);
lean_inc(x_3908);
x_3909 = lean_ctor_get(x_3907, 1);
lean_inc(x_3909);
lean_dec(x_3907);
x_3910 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_3911 = lean_nat_sub(x_3910, x_2755);
lean_dec(x_3910);
x_3912 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_3908, x_3911, x_2786, x_2807, x_3909);
lean_dec(x_2807);
if (lean_obj_tag(x_3912) == 0)
{
uint8_t x_3913; 
x_3913 = !lean_is_exclusive(x_3912);
if (x_3913 == 0)
{
lean_object* x_3914; uint8_t x_3915; 
x_3914 = lean_ctor_get(x_3912, 0);
x_3915 = !lean_is_exclusive(x_3914);
if (x_3915 == 0)
{
lean_object* x_3916; lean_object* x_3917; 
x_3916 = lean_ctor_get(x_3914, 0);
lean_dec(x_3916);
x_3917 = lean_box(0);
lean_ctor_set(x_3914, 0, x_3917);
return x_3912;
}
else
{
lean_object* x_3918; lean_object* x_3919; lean_object* x_3920; 
x_3918 = lean_ctor_get(x_3914, 1);
lean_inc(x_3918);
lean_dec(x_3914);
x_3919 = lean_box(0);
x_3920 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3920, 0, x_3919);
lean_ctor_set(x_3920, 1, x_3918);
lean_ctor_set(x_3912, 0, x_3920);
return x_3912;
}
}
else
{
lean_object* x_3921; lean_object* x_3922; lean_object* x_3923; lean_object* x_3924; lean_object* x_3925; lean_object* x_3926; lean_object* x_3927; 
x_3921 = lean_ctor_get(x_3912, 0);
x_3922 = lean_ctor_get(x_3912, 1);
lean_inc(x_3922);
lean_inc(x_3921);
lean_dec(x_3912);
x_3923 = lean_ctor_get(x_3921, 1);
lean_inc(x_3923);
if (lean_is_exclusive(x_3921)) {
 lean_ctor_release(x_3921, 0);
 lean_ctor_release(x_3921, 1);
 x_3924 = x_3921;
} else {
 lean_dec_ref(x_3921);
 x_3924 = lean_box(0);
}
x_3925 = lean_box(0);
if (lean_is_scalar(x_3924)) {
 x_3926 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3926 = x_3924;
}
lean_ctor_set(x_3926, 0, x_3925);
lean_ctor_set(x_3926, 1, x_3923);
x_3927 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3927, 0, x_3926);
lean_ctor_set(x_3927, 1, x_3922);
return x_3927;
}
}
else
{
uint8_t x_3928; 
x_3928 = !lean_is_exclusive(x_3912);
if (x_3928 == 0)
{
return x_3912;
}
else
{
lean_object* x_3929; lean_object* x_3930; lean_object* x_3931; 
x_3929 = lean_ctor_get(x_3912, 0);
x_3930 = lean_ctor_get(x_3912, 1);
lean_inc(x_3930);
lean_inc(x_3929);
lean_dec(x_3912);
x_3931 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3931, 0, x_3929);
lean_ctor_set(x_3931, 1, x_3930);
return x_3931;
}
}
}
else
{
uint8_t x_3932; 
lean_dec(x_2807);
lean_dec(x_2784);
x_3932 = !lean_is_exclusive(x_3907);
if (x_3932 == 0)
{
return x_3907;
}
else
{
lean_object* x_3933; lean_object* x_3934; lean_object* x_3935; 
x_3933 = lean_ctor_get(x_3907, 0);
x_3934 = lean_ctor_get(x_3907, 1);
lean_inc(x_3934);
lean_inc(x_3933);
lean_dec(x_3907);
x_3935 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3935, 0, x_3933);
lean_ctor_set(x_3935, 1, x_3934);
return x_3935;
}
}
}
else
{
uint8_t x_3936; 
lean_dec(x_2807);
lean_dec(x_2795);
lean_dec(x_2784);
x_3936 = !lean_is_exclusive(x_3904);
if (x_3936 == 0)
{
return x_3904;
}
else
{
lean_object* x_3937; lean_object* x_3938; lean_object* x_3939; 
x_3937 = lean_ctor_get(x_3904, 0);
x_3938 = lean_ctor_get(x_3904, 1);
lean_inc(x_3938);
lean_inc(x_3937);
lean_dec(x_3904);
x_3939 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3939, 0, x_3937);
lean_ctor_set(x_3939, 1, x_3938);
return x_3939;
}
}
}
else
{
lean_object* x_3940; lean_object* x_3941; lean_object* x_3942; lean_object* x_3943; lean_object* x_3944; lean_object* x_3945; lean_object* x_3946; lean_object* x_3947; lean_object* x_3948; lean_object* x_3949; 
x_3940 = lean_ctor_get(x_3898, 0);
x_3941 = lean_ctor_get(x_3898, 1);
x_3942 = lean_ctor_get(x_3898, 2);
x_3943 = lean_ctor_get(x_3898, 3);
x_3944 = lean_ctor_get(x_3898, 4);
x_3945 = lean_ctor_get(x_3898, 5);
lean_inc(x_3945);
lean_inc(x_3944);
lean_inc(x_3943);
lean_inc(x_3942);
lean_inc(x_3941);
lean_inc(x_3940);
lean_dec(x_3898);
x_3946 = l_Lean_MetavarContext_assignExpr(x_3941, x_2793, x_3899);
x_3947 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_3947, 0, x_3940);
lean_ctor_set(x_3947, 1, x_3946);
lean_ctor_set(x_3947, 2, x_3942);
lean_ctor_set(x_3947, 3, x_3943);
lean_ctor_set(x_3947, 4, x_3944);
lean_ctor_set(x_3947, 5, x_3945);
x_3948 = l_Lean_Expr_mvarId_x21(x_3895);
lean_dec(x_3895);
x_3949 = l_Lean_Meta_clear(x_3948, x_2797, x_2807, x_3947);
if (lean_obj_tag(x_3949) == 0)
{
lean_object* x_3950; lean_object* x_3951; lean_object* x_3952; 
x_3950 = lean_ctor_get(x_3949, 0);
lean_inc(x_3950);
x_3951 = lean_ctor_get(x_3949, 1);
lean_inc(x_3951);
lean_dec(x_3949);
x_3952 = l_Lean_Meta_clear(x_3950, x_2795, x_2807, x_3951);
if (lean_obj_tag(x_3952) == 0)
{
lean_object* x_3953; lean_object* x_3954; lean_object* x_3955; lean_object* x_3956; lean_object* x_3957; 
x_3953 = lean_ctor_get(x_3952, 0);
lean_inc(x_3953);
x_3954 = lean_ctor_get(x_3952, 1);
lean_inc(x_3954);
lean_dec(x_3952);
x_3955 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_3956 = lean_nat_sub(x_3955, x_2755);
lean_dec(x_3955);
x_3957 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_3953, x_3956, x_2786, x_2807, x_3954);
lean_dec(x_2807);
if (lean_obj_tag(x_3957) == 0)
{
lean_object* x_3958; lean_object* x_3959; lean_object* x_3960; lean_object* x_3961; lean_object* x_3962; lean_object* x_3963; lean_object* x_3964; lean_object* x_3965; 
x_3958 = lean_ctor_get(x_3957, 0);
lean_inc(x_3958);
x_3959 = lean_ctor_get(x_3957, 1);
lean_inc(x_3959);
if (lean_is_exclusive(x_3957)) {
 lean_ctor_release(x_3957, 0);
 lean_ctor_release(x_3957, 1);
 x_3960 = x_3957;
} else {
 lean_dec_ref(x_3957);
 x_3960 = lean_box(0);
}
x_3961 = lean_ctor_get(x_3958, 1);
lean_inc(x_3961);
if (lean_is_exclusive(x_3958)) {
 lean_ctor_release(x_3958, 0);
 lean_ctor_release(x_3958, 1);
 x_3962 = x_3958;
} else {
 lean_dec_ref(x_3958);
 x_3962 = lean_box(0);
}
x_3963 = lean_box(0);
if (lean_is_scalar(x_3962)) {
 x_3964 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3964 = x_3962;
}
lean_ctor_set(x_3964, 0, x_3963);
lean_ctor_set(x_3964, 1, x_3961);
if (lean_is_scalar(x_3960)) {
 x_3965 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3965 = x_3960;
}
lean_ctor_set(x_3965, 0, x_3964);
lean_ctor_set(x_3965, 1, x_3959);
return x_3965;
}
else
{
lean_object* x_3966; lean_object* x_3967; lean_object* x_3968; lean_object* x_3969; 
x_3966 = lean_ctor_get(x_3957, 0);
lean_inc(x_3966);
x_3967 = lean_ctor_get(x_3957, 1);
lean_inc(x_3967);
if (lean_is_exclusive(x_3957)) {
 lean_ctor_release(x_3957, 0);
 lean_ctor_release(x_3957, 1);
 x_3968 = x_3957;
} else {
 lean_dec_ref(x_3957);
 x_3968 = lean_box(0);
}
if (lean_is_scalar(x_3968)) {
 x_3969 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3969 = x_3968;
}
lean_ctor_set(x_3969, 0, x_3966);
lean_ctor_set(x_3969, 1, x_3967);
return x_3969;
}
}
else
{
lean_object* x_3970; lean_object* x_3971; lean_object* x_3972; lean_object* x_3973; 
lean_dec(x_2807);
lean_dec(x_2784);
x_3970 = lean_ctor_get(x_3952, 0);
lean_inc(x_3970);
x_3971 = lean_ctor_get(x_3952, 1);
lean_inc(x_3971);
if (lean_is_exclusive(x_3952)) {
 lean_ctor_release(x_3952, 0);
 lean_ctor_release(x_3952, 1);
 x_3972 = x_3952;
} else {
 lean_dec_ref(x_3952);
 x_3972 = lean_box(0);
}
if (lean_is_scalar(x_3972)) {
 x_3973 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3973 = x_3972;
}
lean_ctor_set(x_3973, 0, x_3970);
lean_ctor_set(x_3973, 1, x_3971);
return x_3973;
}
}
else
{
lean_object* x_3974; lean_object* x_3975; lean_object* x_3976; lean_object* x_3977; 
lean_dec(x_2807);
lean_dec(x_2795);
lean_dec(x_2784);
x_3974 = lean_ctor_get(x_3949, 0);
lean_inc(x_3974);
x_3975 = lean_ctor_get(x_3949, 1);
lean_inc(x_3975);
if (lean_is_exclusive(x_3949)) {
 lean_ctor_release(x_3949, 0);
 lean_ctor_release(x_3949, 1);
 x_3976 = x_3949;
} else {
 lean_dec_ref(x_3949);
 x_3976 = lean_box(0);
}
if (lean_is_scalar(x_3976)) {
 x_3977 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3977 = x_3976;
}
lean_ctor_set(x_3977, 0, x_3974);
lean_ctor_set(x_3977, 1, x_3975);
return x_3977;
}
}
}
else
{
uint8_t x_3978; 
lean_dec(x_3895);
lean_dec(x_2807);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
x_3978 = !lean_is_exclusive(x_3897);
if (x_3978 == 0)
{
return x_3897;
}
else
{
lean_object* x_3979; lean_object* x_3980; lean_object* x_3981; 
x_3979 = lean_ctor_get(x_3897, 0);
x_3980 = lean_ctor_get(x_3897, 1);
lean_inc(x_3980);
lean_inc(x_3979);
lean_dec(x_3897);
x_3981 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3981, 0, x_3979);
lean_ctor_set(x_3981, 1, x_3980);
return x_3981;
}
}
}
else
{
uint8_t x_3982; 
lean_dec(x_3774);
lean_dec(x_2807);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3982 = !lean_is_exclusive(x_3890);
if (x_3982 == 0)
{
return x_3890;
}
else
{
lean_object* x_3983; lean_object* x_3984; lean_object* x_3985; 
x_3983 = lean_ctor_get(x_3890, 0);
x_3984 = lean_ctor_get(x_3890, 1);
lean_inc(x_3984);
lean_inc(x_3983);
lean_dec(x_3890);
x_3985 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3985, 0, x_3983);
lean_ctor_set(x_3985, 1, x_3984);
return x_3985;
}
}
}
}
else
{
uint8_t x_3986; 
lean_dec(x_3768);
lean_dec(x_3651);
lean_dec(x_3647);
lean_dec(x_2807);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3986 = !lean_is_exclusive(x_3769);
if (x_3986 == 0)
{
return x_3769;
}
else
{
lean_object* x_3987; lean_object* x_3988; lean_object* x_3989; 
x_3987 = lean_ctor_get(x_3769, 0);
x_3988 = lean_ctor_get(x_3769, 1);
lean_inc(x_3988);
lean_inc(x_3987);
lean_dec(x_3769);
x_3989 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3989, 0, x_3987);
lean_ctor_set(x_3989, 1, x_3988);
return x_3989;
}
}
}
}
}
else
{
uint8_t x_4003; 
lean_dec(x_3647);
lean_dec(x_2807);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_4003 = !lean_is_exclusive(x_3648);
if (x_4003 == 0)
{
return x_3648;
}
else
{
lean_object* x_4004; lean_object* x_4005; lean_object* x_4006; 
x_4004 = lean_ctor_get(x_3648, 0);
x_4005 = lean_ctor_get(x_3648, 1);
lean_inc(x_4005);
lean_inc(x_4004);
lean_dec(x_3648);
x_4006 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4006, 0, x_4004);
lean_ctor_set(x_4006, 1, x_4005);
return x_4006;
}
}
}
else
{
uint8_t x_4007; 
lean_dec(x_2807);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_4007 = !lean_is_exclusive(x_3644);
if (x_4007 == 0)
{
return x_3644;
}
else
{
lean_object* x_4008; lean_object* x_4009; lean_object* x_4010; 
x_4008 = lean_ctor_get(x_3644, 0);
x_4009 = lean_ctor_get(x_3644, 1);
lean_inc(x_4009);
lean_inc(x_4008);
lean_dec(x_3644);
x_4010 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4010, 0, x_4008);
lean_ctor_set(x_4010, 1, x_4009);
return x_4010;
}
}
}
}
block_3640:
{
uint8_t x_2809; 
lean_dec(x_2808);
x_2809 = !lean_is_exclusive(x_2801);
if (x_2809 == 0)
{
lean_object* x_2810; uint8_t x_2811; 
x_2810 = lean_ctor_get(x_2801, 2);
x_2811 = !lean_is_exclusive(x_2810);
if (x_2811 == 0)
{
lean_object* x_2812; lean_object* x_2813; lean_object* x_2814; lean_object* x_2837; lean_object* x_2838; lean_object* x_2861; lean_object* x_2862; 
x_2812 = lean_ctor_get(x_2810, 2);
x_2861 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_2810, 2, x_2861);
lean_inc(x_2793);
x_2862 = l_Lean_Meta_getMVarDecl(x_2793, x_2807, x_2801);
if (lean_obj_tag(x_2862) == 0)
{
lean_object* x_2863; lean_object* x_2864; lean_object* x_2865; lean_object* x_2866; 
x_2863 = lean_ctor_get(x_2862, 0);
lean_inc(x_2863);
x_2864 = lean_ctor_get(x_2862, 1);
lean_inc(x_2864);
lean_dec(x_2862);
x_2865 = lean_ctor_get(x_2863, 2);
lean_inc(x_2865);
lean_dec(x_2863);
lean_inc(x_2807);
lean_inc(x_2797);
x_2866 = l_Lean_Meta_getLocalDecl(x_2797, x_2807, x_2864);
if (lean_obj_tag(x_2866) == 0)
{
lean_object* x_2867; lean_object* x_2868; lean_object* x_2869; lean_object* x_3126; uint8_t x_3127; 
x_2867 = lean_ctor_get(x_2866, 0);
lean_inc(x_2867);
x_2868 = lean_ctor_get(x_2866, 1);
lean_inc(x_2868);
lean_dec(x_2866);
x_3126 = l_Lean_LocalDecl_type(x_2867);
lean_dec(x_2867);
x_3127 = l_Lean_Expr_isAppOfArity___main(x_3126, x_2745, x_2746);
if (x_3127 == 0)
{
lean_object* x_3128; lean_object* x_3129; lean_object* x_3130; 
lean_dec(x_3126);
lean_dec(x_2865);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3128 = l_Lean_Meta_isClassQuick___main___closed__1;
x_3129 = l_unreachable_x21___rarg(x_3128);
x_3130 = lean_apply_2(x_3129, x_2807, x_2868);
if (lean_obj_tag(x_3130) == 0)
{
lean_object* x_3131; lean_object* x_3132; 
lean_dec(x_2791);
x_3131 = lean_ctor_get(x_3130, 0);
lean_inc(x_3131);
x_3132 = lean_ctor_get(x_3130, 1);
lean_inc(x_3132);
lean_dec(x_3130);
x_2813 = x_3131;
x_2814 = x_3132;
goto block_2836;
}
else
{
lean_object* x_3133; lean_object* x_3134; 
lean_dec(x_2802);
x_3133 = lean_ctor_get(x_3130, 0);
lean_inc(x_3133);
x_3134 = lean_ctor_get(x_3130, 1);
lean_inc(x_3134);
lean_dec(x_3130);
x_2837 = x_3133;
x_2838 = x_3134;
goto block_2860;
}
}
else
{
lean_object* x_3135; 
x_3135 = l_Lean_Expr_getAppNumArgsAux___main(x_3126, x_2731);
if (x_2759 == 0)
{
lean_object* x_3136; lean_object* x_3137; lean_object* x_3138; 
x_3136 = lean_nat_sub(x_3135, x_2755);
lean_dec(x_3135);
x_3137 = lean_nat_sub(x_3136, x_2751);
lean_dec(x_3136);
x_3138 = l_Lean_Expr_getRevArg_x21___main(x_3126, x_3137);
lean_dec(x_3126);
x_2869 = x_3138;
goto block_3125;
}
else
{
lean_object* x_3139; lean_object* x_3140; lean_object* x_3141; 
x_3139 = lean_nat_sub(x_3135, x_2751);
lean_dec(x_3135);
x_3140 = lean_nat_sub(x_3139, x_2751);
lean_dec(x_3139);
x_3141 = l_Lean_Expr_getRevArg_x21___main(x_3126, x_3140);
lean_dec(x_3126);
x_2869 = x_3141;
goto block_3125;
}
}
block_3125:
{
lean_object* x_2870; lean_object* x_2871; uint8_t x_2872; 
x_2870 = lean_ctor_get(x_2868, 1);
lean_inc(x_2870);
lean_inc(x_2865);
x_2871 = l_Lean_MetavarContext_exprDependsOn(x_2870, x_2865, x_2797);
x_2872 = lean_unbox(x_2871);
lean_dec(x_2871);
if (x_2872 == 0)
{
lean_object* x_2873; lean_object* x_2874; lean_object* x_2875; 
x_2873 = l_Lean_mkOptionalNode___closed__2;
x_2874 = lean_array_push(x_2873, x_2796);
lean_inc(x_2807);
lean_inc(x_2865);
lean_inc(x_2874);
x_2875 = l_Lean_Meta_mkLambda(x_2874, x_2865, x_2807, x_2868);
if (lean_obj_tag(x_2875) == 0)
{
lean_object* x_2876; lean_object* x_2877; lean_object* x_2878; lean_object* x_2879; lean_object* x_2880; lean_object* x_2881; 
x_2876 = lean_ctor_get(x_2875, 0);
lean_inc(x_2876);
x_2877 = lean_ctor_get(x_2875, 1);
lean_inc(x_2877);
lean_dec(x_2875);
x_2878 = lean_expr_abstract(x_2865, x_2874);
lean_dec(x_2874);
lean_dec(x_2865);
x_2879 = lean_expr_instantiate1(x_2878, x_2869);
lean_dec(x_2869);
lean_dec(x_2878);
if (x_2759 == 0)
{
lean_object* x_2949; 
lean_inc(x_2807);
x_2949 = l_Lean_Meta_mkEqSymm(x_2798, x_2807, x_2877);
if (lean_obj_tag(x_2949) == 0)
{
lean_object* x_2950; lean_object* x_2951; 
x_2950 = lean_ctor_get(x_2949, 0);
lean_inc(x_2950);
x_2951 = lean_ctor_get(x_2949, 1);
lean_inc(x_2951);
lean_dec(x_2949);
x_2880 = x_2950;
x_2881 = x_2951;
goto block_2948;
}
else
{
lean_object* x_2952; lean_object* x_2953; 
lean_dec(x_2879);
lean_dec(x_2876);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_2952 = lean_ctor_get(x_2949, 0);
lean_inc(x_2952);
x_2953 = lean_ctor_get(x_2949, 1);
lean_inc(x_2953);
lean_dec(x_2949);
x_2837 = x_2952;
x_2838 = x_2953;
goto block_2860;
}
}
else
{
x_2880 = x_2798;
x_2881 = x_2877;
goto block_2948;
}
block_2948:
{
uint8_t x_2882; lean_object* x_2883; lean_object* x_2884; lean_object* x_2885; lean_object* x_2886; 
x_2882 = 2;
lean_inc(x_2807);
x_2883 = l_Lean_Meta_mkFreshExprMVar(x_2879, x_2736, x_2882, x_2807, x_2881);
x_2884 = lean_ctor_get(x_2883, 0);
lean_inc(x_2884);
x_2885 = lean_ctor_get(x_2883, 1);
lean_inc(x_2885);
lean_dec(x_2883);
lean_inc(x_2807);
lean_inc(x_2884);
x_2886 = l_Lean_Meta_mkEqNDRec(x_2876, x_2884, x_2880, x_2807, x_2885);
if (lean_obj_tag(x_2886) == 0)
{
lean_object* x_2887; lean_object* x_2888; uint8_t x_2889; 
x_2887 = lean_ctor_get(x_2886, 1);
lean_inc(x_2887);
x_2888 = lean_ctor_get(x_2886, 0);
lean_inc(x_2888);
lean_dec(x_2886);
x_2889 = !lean_is_exclusive(x_2887);
if (x_2889 == 0)
{
lean_object* x_2890; lean_object* x_2891; lean_object* x_2892; lean_object* x_2893; 
x_2890 = lean_ctor_get(x_2887, 1);
x_2891 = l_Lean_MetavarContext_assignExpr(x_2890, x_2793, x_2888);
lean_ctor_set(x_2887, 1, x_2891);
x_2892 = l_Lean_Expr_mvarId_x21(x_2884);
lean_dec(x_2884);
x_2893 = l_Lean_Meta_clear(x_2892, x_2797, x_2807, x_2887);
if (lean_obj_tag(x_2893) == 0)
{
lean_object* x_2894; lean_object* x_2895; lean_object* x_2896; 
x_2894 = lean_ctor_get(x_2893, 0);
lean_inc(x_2894);
x_2895 = lean_ctor_get(x_2893, 1);
lean_inc(x_2895);
lean_dec(x_2893);
x_2896 = l_Lean_Meta_clear(x_2894, x_2795, x_2807, x_2895);
if (lean_obj_tag(x_2896) == 0)
{
lean_object* x_2897; lean_object* x_2898; lean_object* x_2899; lean_object* x_2900; lean_object* x_2901; 
x_2897 = lean_ctor_get(x_2896, 0);
lean_inc(x_2897);
x_2898 = lean_ctor_get(x_2896, 1);
lean_inc(x_2898);
lean_dec(x_2896);
x_2899 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_2900 = lean_nat_sub(x_2899, x_2755);
lean_dec(x_2899);
x_2901 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_2897, x_2900, x_2786, x_2807, x_2898);
lean_dec(x_2807);
if (lean_obj_tag(x_2901) == 0)
{
lean_object* x_2902; lean_object* x_2903; uint8_t x_2904; 
lean_dec(x_2791);
x_2902 = lean_ctor_get(x_2901, 0);
lean_inc(x_2902);
x_2903 = lean_ctor_get(x_2901, 1);
lean_inc(x_2903);
lean_dec(x_2901);
x_2904 = !lean_is_exclusive(x_2902);
if (x_2904 == 0)
{
lean_object* x_2905; lean_object* x_2906; 
x_2905 = lean_ctor_get(x_2902, 0);
lean_dec(x_2905);
x_2906 = lean_box(0);
lean_ctor_set(x_2902, 0, x_2906);
x_2813 = x_2902;
x_2814 = x_2903;
goto block_2836;
}
else
{
lean_object* x_2907; lean_object* x_2908; lean_object* x_2909; 
x_2907 = lean_ctor_get(x_2902, 1);
lean_inc(x_2907);
lean_dec(x_2902);
x_2908 = lean_box(0);
x_2909 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2909, 0, x_2908);
lean_ctor_set(x_2909, 1, x_2907);
x_2813 = x_2909;
x_2814 = x_2903;
goto block_2836;
}
}
else
{
lean_object* x_2910; lean_object* x_2911; 
lean_dec(x_2802);
x_2910 = lean_ctor_get(x_2901, 0);
lean_inc(x_2910);
x_2911 = lean_ctor_get(x_2901, 1);
lean_inc(x_2911);
lean_dec(x_2901);
x_2837 = x_2910;
x_2838 = x_2911;
goto block_2860;
}
}
else
{
lean_object* x_2912; lean_object* x_2913; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2784);
x_2912 = lean_ctor_get(x_2896, 0);
lean_inc(x_2912);
x_2913 = lean_ctor_get(x_2896, 1);
lean_inc(x_2913);
lean_dec(x_2896);
x_2837 = x_2912;
x_2838 = x_2913;
goto block_2860;
}
}
else
{
lean_object* x_2914; lean_object* x_2915; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2795);
lean_dec(x_2784);
x_2914 = lean_ctor_get(x_2893, 0);
lean_inc(x_2914);
x_2915 = lean_ctor_get(x_2893, 1);
lean_inc(x_2915);
lean_dec(x_2893);
x_2837 = x_2914;
x_2838 = x_2915;
goto block_2860;
}
}
else
{
lean_object* x_2916; lean_object* x_2917; lean_object* x_2918; lean_object* x_2919; lean_object* x_2920; lean_object* x_2921; lean_object* x_2922; lean_object* x_2923; lean_object* x_2924; lean_object* x_2925; 
x_2916 = lean_ctor_get(x_2887, 0);
x_2917 = lean_ctor_get(x_2887, 1);
x_2918 = lean_ctor_get(x_2887, 2);
x_2919 = lean_ctor_get(x_2887, 3);
x_2920 = lean_ctor_get(x_2887, 4);
x_2921 = lean_ctor_get(x_2887, 5);
lean_inc(x_2921);
lean_inc(x_2920);
lean_inc(x_2919);
lean_inc(x_2918);
lean_inc(x_2917);
lean_inc(x_2916);
lean_dec(x_2887);
x_2922 = l_Lean_MetavarContext_assignExpr(x_2917, x_2793, x_2888);
x_2923 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2923, 0, x_2916);
lean_ctor_set(x_2923, 1, x_2922);
lean_ctor_set(x_2923, 2, x_2918);
lean_ctor_set(x_2923, 3, x_2919);
lean_ctor_set(x_2923, 4, x_2920);
lean_ctor_set(x_2923, 5, x_2921);
x_2924 = l_Lean_Expr_mvarId_x21(x_2884);
lean_dec(x_2884);
x_2925 = l_Lean_Meta_clear(x_2924, x_2797, x_2807, x_2923);
if (lean_obj_tag(x_2925) == 0)
{
lean_object* x_2926; lean_object* x_2927; lean_object* x_2928; 
x_2926 = lean_ctor_get(x_2925, 0);
lean_inc(x_2926);
x_2927 = lean_ctor_get(x_2925, 1);
lean_inc(x_2927);
lean_dec(x_2925);
x_2928 = l_Lean_Meta_clear(x_2926, x_2795, x_2807, x_2927);
if (lean_obj_tag(x_2928) == 0)
{
lean_object* x_2929; lean_object* x_2930; lean_object* x_2931; lean_object* x_2932; lean_object* x_2933; 
x_2929 = lean_ctor_get(x_2928, 0);
lean_inc(x_2929);
x_2930 = lean_ctor_get(x_2928, 1);
lean_inc(x_2930);
lean_dec(x_2928);
x_2931 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_2932 = lean_nat_sub(x_2931, x_2755);
lean_dec(x_2931);
x_2933 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_2929, x_2932, x_2786, x_2807, x_2930);
lean_dec(x_2807);
if (lean_obj_tag(x_2933) == 0)
{
lean_object* x_2934; lean_object* x_2935; lean_object* x_2936; lean_object* x_2937; lean_object* x_2938; lean_object* x_2939; 
lean_dec(x_2791);
x_2934 = lean_ctor_get(x_2933, 0);
lean_inc(x_2934);
x_2935 = lean_ctor_get(x_2933, 1);
lean_inc(x_2935);
lean_dec(x_2933);
x_2936 = lean_ctor_get(x_2934, 1);
lean_inc(x_2936);
if (lean_is_exclusive(x_2934)) {
 lean_ctor_release(x_2934, 0);
 lean_ctor_release(x_2934, 1);
 x_2937 = x_2934;
} else {
 lean_dec_ref(x_2934);
 x_2937 = lean_box(0);
}
x_2938 = lean_box(0);
if (lean_is_scalar(x_2937)) {
 x_2939 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2939 = x_2937;
}
lean_ctor_set(x_2939, 0, x_2938);
lean_ctor_set(x_2939, 1, x_2936);
x_2813 = x_2939;
x_2814 = x_2935;
goto block_2836;
}
else
{
lean_object* x_2940; lean_object* x_2941; 
lean_dec(x_2802);
x_2940 = lean_ctor_get(x_2933, 0);
lean_inc(x_2940);
x_2941 = lean_ctor_get(x_2933, 1);
lean_inc(x_2941);
lean_dec(x_2933);
x_2837 = x_2940;
x_2838 = x_2941;
goto block_2860;
}
}
else
{
lean_object* x_2942; lean_object* x_2943; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2784);
x_2942 = lean_ctor_get(x_2928, 0);
lean_inc(x_2942);
x_2943 = lean_ctor_get(x_2928, 1);
lean_inc(x_2943);
lean_dec(x_2928);
x_2837 = x_2942;
x_2838 = x_2943;
goto block_2860;
}
}
else
{
lean_object* x_2944; lean_object* x_2945; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2795);
lean_dec(x_2784);
x_2944 = lean_ctor_get(x_2925, 0);
lean_inc(x_2944);
x_2945 = lean_ctor_get(x_2925, 1);
lean_inc(x_2945);
lean_dec(x_2925);
x_2837 = x_2944;
x_2838 = x_2945;
goto block_2860;
}
}
}
else
{
lean_object* x_2946; lean_object* x_2947; 
lean_dec(x_2884);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
x_2946 = lean_ctor_get(x_2886, 0);
lean_inc(x_2946);
x_2947 = lean_ctor_get(x_2886, 1);
lean_inc(x_2947);
lean_dec(x_2886);
x_2837 = x_2946;
x_2838 = x_2947;
goto block_2860;
}
}
}
else
{
lean_object* x_2954; lean_object* x_2955; 
lean_dec(x_2874);
lean_dec(x_2869);
lean_dec(x_2865);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_2954 = lean_ctor_get(x_2875, 0);
lean_inc(x_2954);
x_2955 = lean_ctor_get(x_2875, 1);
lean_inc(x_2955);
lean_dec(x_2875);
x_2837 = x_2954;
x_2838 = x_2955;
goto block_2860;
}
}
else
{
lean_object* x_2956; lean_object* x_2957; lean_object* x_2958; lean_object* x_2959; lean_object* x_2960; 
x_2956 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2796);
x_2957 = lean_array_push(x_2956, x_2796);
x_2958 = lean_expr_abstract(x_2865, x_2957);
lean_dec(x_2957);
x_2959 = lean_expr_instantiate1(x_2958, x_2869);
lean_dec(x_2958);
lean_inc(x_2807);
lean_inc(x_2869);
x_2960 = l_Lean_Meta_mkEqRefl(x_2869, x_2807, x_2868);
if (lean_obj_tag(x_2960) == 0)
{
lean_object* x_2961; lean_object* x_2962; lean_object* x_2963; lean_object* x_2964; lean_object* x_2965; 
x_2961 = lean_ctor_get(x_2960, 0);
lean_inc(x_2961);
x_2962 = lean_ctor_get(x_2960, 1);
lean_inc(x_2962);
lean_dec(x_2960);
lean_inc(x_2798);
x_2963 = lean_array_push(x_2956, x_2798);
x_2964 = lean_expr_abstract(x_2959, x_2963);
lean_dec(x_2959);
x_2965 = lean_expr_instantiate1(x_2964, x_2961);
lean_dec(x_2961);
lean_dec(x_2964);
if (x_2759 == 0)
{
lean_object* x_2966; 
lean_inc(x_2807);
lean_inc(x_2796);
x_2966 = l_Lean_Meta_mkEq(x_2869, x_2796, x_2807, x_2962);
if (lean_obj_tag(x_2966) == 0)
{
lean_object* x_2967; lean_object* x_2968; lean_object* x_2969; lean_object* x_2970; uint8_t x_2971; lean_object* x_2972; 
x_2967 = lean_ctor_get(x_2966, 0);
lean_inc(x_2967);
x_2968 = lean_ctor_get(x_2966, 1);
lean_inc(x_2968);
lean_dec(x_2966);
x_2969 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__1___boxed), 7, 4);
lean_closure_set(x_2969, 0, x_2865);
lean_closure_set(x_2969, 1, x_2963);
lean_closure_set(x_2969, 2, x_2777);
lean_closure_set(x_2969, 3, x_2796);
x_2970 = l_Lean_Meta_substCore___closed__18;
x_2971 = 0;
lean_inc(x_2807);
x_2972 = l_Lean_Meta_withLocalDecl___rarg(x_2970, x_2967, x_2971, x_2969, x_2807, x_2968);
if (lean_obj_tag(x_2972) == 0)
{
lean_object* x_2973; lean_object* x_2974; lean_object* x_2975; 
x_2973 = lean_ctor_get(x_2972, 0);
lean_inc(x_2973);
x_2974 = lean_ctor_get(x_2972, 1);
lean_inc(x_2974);
lean_dec(x_2972);
lean_inc(x_2807);
x_2975 = l_Lean_Meta_mkEqSymm(x_2798, x_2807, x_2974);
if (lean_obj_tag(x_2975) == 0)
{
lean_object* x_2976; lean_object* x_2977; uint8_t x_2978; lean_object* x_2979; lean_object* x_2980; lean_object* x_2981; lean_object* x_2982; 
x_2976 = lean_ctor_get(x_2975, 0);
lean_inc(x_2976);
x_2977 = lean_ctor_get(x_2975, 1);
lean_inc(x_2977);
lean_dec(x_2975);
x_2978 = 2;
lean_inc(x_2807);
x_2979 = l_Lean_Meta_mkFreshExprMVar(x_2965, x_2736, x_2978, x_2807, x_2977);
x_2980 = lean_ctor_get(x_2979, 0);
lean_inc(x_2980);
x_2981 = lean_ctor_get(x_2979, 1);
lean_inc(x_2981);
lean_dec(x_2979);
lean_inc(x_2807);
lean_inc(x_2980);
x_2982 = l_Lean_Meta_mkEqRec(x_2973, x_2980, x_2976, x_2807, x_2981);
if (lean_obj_tag(x_2982) == 0)
{
lean_object* x_2983; lean_object* x_2984; uint8_t x_2985; 
x_2983 = lean_ctor_get(x_2982, 1);
lean_inc(x_2983);
x_2984 = lean_ctor_get(x_2982, 0);
lean_inc(x_2984);
lean_dec(x_2982);
x_2985 = !lean_is_exclusive(x_2983);
if (x_2985 == 0)
{
lean_object* x_2986; lean_object* x_2987; lean_object* x_2988; lean_object* x_2989; 
x_2986 = lean_ctor_get(x_2983, 1);
x_2987 = l_Lean_MetavarContext_assignExpr(x_2986, x_2793, x_2984);
lean_ctor_set(x_2983, 1, x_2987);
x_2988 = l_Lean_Expr_mvarId_x21(x_2980);
lean_dec(x_2980);
x_2989 = l_Lean_Meta_clear(x_2988, x_2797, x_2807, x_2983);
if (lean_obj_tag(x_2989) == 0)
{
lean_object* x_2990; lean_object* x_2991; lean_object* x_2992; 
x_2990 = lean_ctor_get(x_2989, 0);
lean_inc(x_2990);
x_2991 = lean_ctor_get(x_2989, 1);
lean_inc(x_2991);
lean_dec(x_2989);
x_2992 = l_Lean_Meta_clear(x_2990, x_2795, x_2807, x_2991);
if (lean_obj_tag(x_2992) == 0)
{
lean_object* x_2993; lean_object* x_2994; lean_object* x_2995; lean_object* x_2996; lean_object* x_2997; 
x_2993 = lean_ctor_get(x_2992, 0);
lean_inc(x_2993);
x_2994 = lean_ctor_get(x_2992, 1);
lean_inc(x_2994);
lean_dec(x_2992);
x_2995 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_2996 = lean_nat_sub(x_2995, x_2755);
lean_dec(x_2995);
x_2997 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_2993, x_2996, x_2786, x_2807, x_2994);
lean_dec(x_2807);
if (lean_obj_tag(x_2997) == 0)
{
lean_object* x_2998; lean_object* x_2999; uint8_t x_3000; 
lean_dec(x_2791);
x_2998 = lean_ctor_get(x_2997, 0);
lean_inc(x_2998);
x_2999 = lean_ctor_get(x_2997, 1);
lean_inc(x_2999);
lean_dec(x_2997);
x_3000 = !lean_is_exclusive(x_2998);
if (x_3000 == 0)
{
lean_object* x_3001; lean_object* x_3002; 
x_3001 = lean_ctor_get(x_2998, 0);
lean_dec(x_3001);
x_3002 = lean_box(0);
lean_ctor_set(x_2998, 0, x_3002);
x_2813 = x_2998;
x_2814 = x_2999;
goto block_2836;
}
else
{
lean_object* x_3003; lean_object* x_3004; lean_object* x_3005; 
x_3003 = lean_ctor_get(x_2998, 1);
lean_inc(x_3003);
lean_dec(x_2998);
x_3004 = lean_box(0);
x_3005 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3005, 0, x_3004);
lean_ctor_set(x_3005, 1, x_3003);
x_2813 = x_3005;
x_2814 = x_2999;
goto block_2836;
}
}
else
{
lean_object* x_3006; lean_object* x_3007; 
lean_dec(x_2802);
x_3006 = lean_ctor_get(x_2997, 0);
lean_inc(x_3006);
x_3007 = lean_ctor_get(x_2997, 1);
lean_inc(x_3007);
lean_dec(x_2997);
x_2837 = x_3006;
x_2838 = x_3007;
goto block_2860;
}
}
else
{
lean_object* x_3008; lean_object* x_3009; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2784);
x_3008 = lean_ctor_get(x_2992, 0);
lean_inc(x_3008);
x_3009 = lean_ctor_get(x_2992, 1);
lean_inc(x_3009);
lean_dec(x_2992);
x_2837 = x_3008;
x_2838 = x_3009;
goto block_2860;
}
}
else
{
lean_object* x_3010; lean_object* x_3011; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2795);
lean_dec(x_2784);
x_3010 = lean_ctor_get(x_2989, 0);
lean_inc(x_3010);
x_3011 = lean_ctor_get(x_2989, 1);
lean_inc(x_3011);
lean_dec(x_2989);
x_2837 = x_3010;
x_2838 = x_3011;
goto block_2860;
}
}
else
{
lean_object* x_3012; lean_object* x_3013; lean_object* x_3014; lean_object* x_3015; lean_object* x_3016; lean_object* x_3017; lean_object* x_3018; lean_object* x_3019; lean_object* x_3020; lean_object* x_3021; 
x_3012 = lean_ctor_get(x_2983, 0);
x_3013 = lean_ctor_get(x_2983, 1);
x_3014 = lean_ctor_get(x_2983, 2);
x_3015 = lean_ctor_get(x_2983, 3);
x_3016 = lean_ctor_get(x_2983, 4);
x_3017 = lean_ctor_get(x_2983, 5);
lean_inc(x_3017);
lean_inc(x_3016);
lean_inc(x_3015);
lean_inc(x_3014);
lean_inc(x_3013);
lean_inc(x_3012);
lean_dec(x_2983);
x_3018 = l_Lean_MetavarContext_assignExpr(x_3013, x_2793, x_2984);
x_3019 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_3019, 0, x_3012);
lean_ctor_set(x_3019, 1, x_3018);
lean_ctor_set(x_3019, 2, x_3014);
lean_ctor_set(x_3019, 3, x_3015);
lean_ctor_set(x_3019, 4, x_3016);
lean_ctor_set(x_3019, 5, x_3017);
x_3020 = l_Lean_Expr_mvarId_x21(x_2980);
lean_dec(x_2980);
x_3021 = l_Lean_Meta_clear(x_3020, x_2797, x_2807, x_3019);
if (lean_obj_tag(x_3021) == 0)
{
lean_object* x_3022; lean_object* x_3023; lean_object* x_3024; 
x_3022 = lean_ctor_get(x_3021, 0);
lean_inc(x_3022);
x_3023 = lean_ctor_get(x_3021, 1);
lean_inc(x_3023);
lean_dec(x_3021);
x_3024 = l_Lean_Meta_clear(x_3022, x_2795, x_2807, x_3023);
if (lean_obj_tag(x_3024) == 0)
{
lean_object* x_3025; lean_object* x_3026; lean_object* x_3027; lean_object* x_3028; lean_object* x_3029; 
x_3025 = lean_ctor_get(x_3024, 0);
lean_inc(x_3025);
x_3026 = lean_ctor_get(x_3024, 1);
lean_inc(x_3026);
lean_dec(x_3024);
x_3027 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_3028 = lean_nat_sub(x_3027, x_2755);
lean_dec(x_3027);
x_3029 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_3025, x_3028, x_2786, x_2807, x_3026);
lean_dec(x_2807);
if (lean_obj_tag(x_3029) == 0)
{
lean_object* x_3030; lean_object* x_3031; lean_object* x_3032; lean_object* x_3033; lean_object* x_3034; lean_object* x_3035; 
lean_dec(x_2791);
x_3030 = lean_ctor_get(x_3029, 0);
lean_inc(x_3030);
x_3031 = lean_ctor_get(x_3029, 1);
lean_inc(x_3031);
lean_dec(x_3029);
x_3032 = lean_ctor_get(x_3030, 1);
lean_inc(x_3032);
if (lean_is_exclusive(x_3030)) {
 lean_ctor_release(x_3030, 0);
 lean_ctor_release(x_3030, 1);
 x_3033 = x_3030;
} else {
 lean_dec_ref(x_3030);
 x_3033 = lean_box(0);
}
x_3034 = lean_box(0);
if (lean_is_scalar(x_3033)) {
 x_3035 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3035 = x_3033;
}
lean_ctor_set(x_3035, 0, x_3034);
lean_ctor_set(x_3035, 1, x_3032);
x_2813 = x_3035;
x_2814 = x_3031;
goto block_2836;
}
else
{
lean_object* x_3036; lean_object* x_3037; 
lean_dec(x_2802);
x_3036 = lean_ctor_get(x_3029, 0);
lean_inc(x_3036);
x_3037 = lean_ctor_get(x_3029, 1);
lean_inc(x_3037);
lean_dec(x_3029);
x_2837 = x_3036;
x_2838 = x_3037;
goto block_2860;
}
}
else
{
lean_object* x_3038; lean_object* x_3039; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2784);
x_3038 = lean_ctor_get(x_3024, 0);
lean_inc(x_3038);
x_3039 = lean_ctor_get(x_3024, 1);
lean_inc(x_3039);
lean_dec(x_3024);
x_2837 = x_3038;
x_2838 = x_3039;
goto block_2860;
}
}
else
{
lean_object* x_3040; lean_object* x_3041; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2795);
lean_dec(x_2784);
x_3040 = lean_ctor_get(x_3021, 0);
lean_inc(x_3040);
x_3041 = lean_ctor_get(x_3021, 1);
lean_inc(x_3041);
lean_dec(x_3021);
x_2837 = x_3040;
x_2838 = x_3041;
goto block_2860;
}
}
}
else
{
lean_object* x_3042; lean_object* x_3043; 
lean_dec(x_2980);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
x_3042 = lean_ctor_get(x_2982, 0);
lean_inc(x_3042);
x_3043 = lean_ctor_get(x_2982, 1);
lean_inc(x_3043);
lean_dec(x_2982);
x_2837 = x_3042;
x_2838 = x_3043;
goto block_2860;
}
}
else
{
lean_object* x_3044; lean_object* x_3045; 
lean_dec(x_2973);
lean_dec(x_2965);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3044 = lean_ctor_get(x_2975, 0);
lean_inc(x_3044);
x_3045 = lean_ctor_get(x_2975, 1);
lean_inc(x_3045);
lean_dec(x_2975);
x_2837 = x_3044;
x_2838 = x_3045;
goto block_2860;
}
}
else
{
lean_object* x_3046; lean_object* x_3047; 
lean_dec(x_2965);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3046 = lean_ctor_get(x_2972, 0);
lean_inc(x_3046);
x_3047 = lean_ctor_get(x_2972, 1);
lean_inc(x_3047);
lean_dec(x_2972);
x_2837 = x_3046;
x_2838 = x_3047;
goto block_2860;
}
}
else
{
lean_object* x_3048; lean_object* x_3049; 
lean_dec(x_2965);
lean_dec(x_2963);
lean_dec(x_2865);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3048 = lean_ctor_get(x_2966, 0);
lean_inc(x_3048);
x_3049 = lean_ctor_get(x_2966, 1);
lean_inc(x_3049);
lean_dec(x_2966);
x_2837 = x_3048;
x_2838 = x_3049;
goto block_2860;
}
}
else
{
lean_object* x_3050; lean_object* x_3051; lean_object* x_3052; 
lean_dec(x_2963);
lean_dec(x_2869);
x_3050 = lean_array_push(x_2777, x_2796);
lean_inc(x_2798);
x_3051 = lean_array_push(x_3050, x_2798);
lean_inc(x_2807);
x_3052 = l_Lean_Meta_mkLambda(x_3051, x_2865, x_2807, x_2962);
if (lean_obj_tag(x_3052) == 0)
{
lean_object* x_3053; lean_object* x_3054; uint8_t x_3055; lean_object* x_3056; lean_object* x_3057; lean_object* x_3058; lean_object* x_3059; 
x_3053 = lean_ctor_get(x_3052, 0);
lean_inc(x_3053);
x_3054 = lean_ctor_get(x_3052, 1);
lean_inc(x_3054);
lean_dec(x_3052);
x_3055 = 2;
lean_inc(x_2807);
x_3056 = l_Lean_Meta_mkFreshExprMVar(x_2965, x_2736, x_3055, x_2807, x_3054);
x_3057 = lean_ctor_get(x_3056, 0);
lean_inc(x_3057);
x_3058 = lean_ctor_get(x_3056, 1);
lean_inc(x_3058);
lean_dec(x_3056);
lean_inc(x_2807);
lean_inc(x_3057);
x_3059 = l_Lean_Meta_mkEqRec(x_3053, x_3057, x_2798, x_2807, x_3058);
if (lean_obj_tag(x_3059) == 0)
{
lean_object* x_3060; lean_object* x_3061; uint8_t x_3062; 
x_3060 = lean_ctor_get(x_3059, 1);
lean_inc(x_3060);
x_3061 = lean_ctor_get(x_3059, 0);
lean_inc(x_3061);
lean_dec(x_3059);
x_3062 = !lean_is_exclusive(x_3060);
if (x_3062 == 0)
{
lean_object* x_3063; lean_object* x_3064; lean_object* x_3065; lean_object* x_3066; 
x_3063 = lean_ctor_get(x_3060, 1);
x_3064 = l_Lean_MetavarContext_assignExpr(x_3063, x_2793, x_3061);
lean_ctor_set(x_3060, 1, x_3064);
x_3065 = l_Lean_Expr_mvarId_x21(x_3057);
lean_dec(x_3057);
x_3066 = l_Lean_Meta_clear(x_3065, x_2797, x_2807, x_3060);
if (lean_obj_tag(x_3066) == 0)
{
lean_object* x_3067; lean_object* x_3068; lean_object* x_3069; 
x_3067 = lean_ctor_get(x_3066, 0);
lean_inc(x_3067);
x_3068 = lean_ctor_get(x_3066, 1);
lean_inc(x_3068);
lean_dec(x_3066);
x_3069 = l_Lean_Meta_clear(x_3067, x_2795, x_2807, x_3068);
if (lean_obj_tag(x_3069) == 0)
{
lean_object* x_3070; lean_object* x_3071; lean_object* x_3072; lean_object* x_3073; lean_object* x_3074; 
x_3070 = lean_ctor_get(x_3069, 0);
lean_inc(x_3070);
x_3071 = lean_ctor_get(x_3069, 1);
lean_inc(x_3071);
lean_dec(x_3069);
x_3072 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_3073 = lean_nat_sub(x_3072, x_2755);
lean_dec(x_3072);
x_3074 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_3070, x_3073, x_2786, x_2807, x_3071);
lean_dec(x_2807);
if (lean_obj_tag(x_3074) == 0)
{
lean_object* x_3075; lean_object* x_3076; uint8_t x_3077; 
lean_dec(x_2791);
x_3075 = lean_ctor_get(x_3074, 0);
lean_inc(x_3075);
x_3076 = lean_ctor_get(x_3074, 1);
lean_inc(x_3076);
lean_dec(x_3074);
x_3077 = !lean_is_exclusive(x_3075);
if (x_3077 == 0)
{
lean_object* x_3078; lean_object* x_3079; 
x_3078 = lean_ctor_get(x_3075, 0);
lean_dec(x_3078);
x_3079 = lean_box(0);
lean_ctor_set(x_3075, 0, x_3079);
x_2813 = x_3075;
x_2814 = x_3076;
goto block_2836;
}
else
{
lean_object* x_3080; lean_object* x_3081; lean_object* x_3082; 
x_3080 = lean_ctor_get(x_3075, 1);
lean_inc(x_3080);
lean_dec(x_3075);
x_3081 = lean_box(0);
x_3082 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3082, 0, x_3081);
lean_ctor_set(x_3082, 1, x_3080);
x_2813 = x_3082;
x_2814 = x_3076;
goto block_2836;
}
}
else
{
lean_object* x_3083; lean_object* x_3084; 
lean_dec(x_2802);
x_3083 = lean_ctor_get(x_3074, 0);
lean_inc(x_3083);
x_3084 = lean_ctor_get(x_3074, 1);
lean_inc(x_3084);
lean_dec(x_3074);
x_2837 = x_3083;
x_2838 = x_3084;
goto block_2860;
}
}
else
{
lean_object* x_3085; lean_object* x_3086; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2784);
x_3085 = lean_ctor_get(x_3069, 0);
lean_inc(x_3085);
x_3086 = lean_ctor_get(x_3069, 1);
lean_inc(x_3086);
lean_dec(x_3069);
x_2837 = x_3085;
x_2838 = x_3086;
goto block_2860;
}
}
else
{
lean_object* x_3087; lean_object* x_3088; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2795);
lean_dec(x_2784);
x_3087 = lean_ctor_get(x_3066, 0);
lean_inc(x_3087);
x_3088 = lean_ctor_get(x_3066, 1);
lean_inc(x_3088);
lean_dec(x_3066);
x_2837 = x_3087;
x_2838 = x_3088;
goto block_2860;
}
}
else
{
lean_object* x_3089; lean_object* x_3090; lean_object* x_3091; lean_object* x_3092; lean_object* x_3093; lean_object* x_3094; lean_object* x_3095; lean_object* x_3096; lean_object* x_3097; lean_object* x_3098; 
x_3089 = lean_ctor_get(x_3060, 0);
x_3090 = lean_ctor_get(x_3060, 1);
x_3091 = lean_ctor_get(x_3060, 2);
x_3092 = lean_ctor_get(x_3060, 3);
x_3093 = lean_ctor_get(x_3060, 4);
x_3094 = lean_ctor_get(x_3060, 5);
lean_inc(x_3094);
lean_inc(x_3093);
lean_inc(x_3092);
lean_inc(x_3091);
lean_inc(x_3090);
lean_inc(x_3089);
lean_dec(x_3060);
x_3095 = l_Lean_MetavarContext_assignExpr(x_3090, x_2793, x_3061);
x_3096 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_3096, 0, x_3089);
lean_ctor_set(x_3096, 1, x_3095);
lean_ctor_set(x_3096, 2, x_3091);
lean_ctor_set(x_3096, 3, x_3092);
lean_ctor_set(x_3096, 4, x_3093);
lean_ctor_set(x_3096, 5, x_3094);
x_3097 = l_Lean_Expr_mvarId_x21(x_3057);
lean_dec(x_3057);
x_3098 = l_Lean_Meta_clear(x_3097, x_2797, x_2807, x_3096);
if (lean_obj_tag(x_3098) == 0)
{
lean_object* x_3099; lean_object* x_3100; lean_object* x_3101; 
x_3099 = lean_ctor_get(x_3098, 0);
lean_inc(x_3099);
x_3100 = lean_ctor_get(x_3098, 1);
lean_inc(x_3100);
lean_dec(x_3098);
x_3101 = l_Lean_Meta_clear(x_3099, x_2795, x_2807, x_3100);
if (lean_obj_tag(x_3101) == 0)
{
lean_object* x_3102; lean_object* x_3103; lean_object* x_3104; lean_object* x_3105; lean_object* x_3106; 
x_3102 = lean_ctor_get(x_3101, 0);
lean_inc(x_3102);
x_3103 = lean_ctor_get(x_3101, 1);
lean_inc(x_3103);
lean_dec(x_3101);
x_3104 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_3105 = lean_nat_sub(x_3104, x_2755);
lean_dec(x_3104);
x_3106 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_3102, x_3105, x_2786, x_2807, x_3103);
lean_dec(x_2807);
if (lean_obj_tag(x_3106) == 0)
{
lean_object* x_3107; lean_object* x_3108; lean_object* x_3109; lean_object* x_3110; lean_object* x_3111; lean_object* x_3112; 
lean_dec(x_2791);
x_3107 = lean_ctor_get(x_3106, 0);
lean_inc(x_3107);
x_3108 = lean_ctor_get(x_3106, 1);
lean_inc(x_3108);
lean_dec(x_3106);
x_3109 = lean_ctor_get(x_3107, 1);
lean_inc(x_3109);
if (lean_is_exclusive(x_3107)) {
 lean_ctor_release(x_3107, 0);
 lean_ctor_release(x_3107, 1);
 x_3110 = x_3107;
} else {
 lean_dec_ref(x_3107);
 x_3110 = lean_box(0);
}
x_3111 = lean_box(0);
if (lean_is_scalar(x_3110)) {
 x_3112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3112 = x_3110;
}
lean_ctor_set(x_3112, 0, x_3111);
lean_ctor_set(x_3112, 1, x_3109);
x_2813 = x_3112;
x_2814 = x_3108;
goto block_2836;
}
else
{
lean_object* x_3113; lean_object* x_3114; 
lean_dec(x_2802);
x_3113 = lean_ctor_get(x_3106, 0);
lean_inc(x_3113);
x_3114 = lean_ctor_get(x_3106, 1);
lean_inc(x_3114);
lean_dec(x_3106);
x_2837 = x_3113;
x_2838 = x_3114;
goto block_2860;
}
}
else
{
lean_object* x_3115; lean_object* x_3116; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2784);
x_3115 = lean_ctor_get(x_3101, 0);
lean_inc(x_3115);
x_3116 = lean_ctor_get(x_3101, 1);
lean_inc(x_3116);
lean_dec(x_3101);
x_2837 = x_3115;
x_2838 = x_3116;
goto block_2860;
}
}
else
{
lean_object* x_3117; lean_object* x_3118; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2795);
lean_dec(x_2784);
x_3117 = lean_ctor_get(x_3098, 0);
lean_inc(x_3117);
x_3118 = lean_ctor_get(x_3098, 1);
lean_inc(x_3118);
lean_dec(x_3098);
x_2837 = x_3117;
x_2838 = x_3118;
goto block_2860;
}
}
}
else
{
lean_object* x_3119; lean_object* x_3120; 
lean_dec(x_3057);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
x_3119 = lean_ctor_get(x_3059, 0);
lean_inc(x_3119);
x_3120 = lean_ctor_get(x_3059, 1);
lean_inc(x_3120);
lean_dec(x_3059);
x_2837 = x_3119;
x_2838 = x_3120;
goto block_2860;
}
}
else
{
lean_object* x_3121; lean_object* x_3122; 
lean_dec(x_2965);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3121 = lean_ctor_get(x_3052, 0);
lean_inc(x_3121);
x_3122 = lean_ctor_get(x_3052, 1);
lean_inc(x_3122);
lean_dec(x_3052);
x_2837 = x_3121;
x_2838 = x_3122;
goto block_2860;
}
}
}
else
{
lean_object* x_3123; lean_object* x_3124; 
lean_dec(x_2959);
lean_dec(x_2869);
lean_dec(x_2865);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3123 = lean_ctor_get(x_2960, 0);
lean_inc(x_3123);
x_3124 = lean_ctor_get(x_2960, 1);
lean_inc(x_3124);
lean_dec(x_2960);
x_2837 = x_3123;
x_2838 = x_3124;
goto block_2860;
}
}
}
}
else
{
lean_object* x_3142; lean_object* x_3143; 
lean_dec(x_2865);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3142 = lean_ctor_get(x_2866, 0);
lean_inc(x_3142);
x_3143 = lean_ctor_get(x_2866, 1);
lean_inc(x_3143);
lean_dec(x_2866);
x_2837 = x_3142;
x_2838 = x_3143;
goto block_2860;
}
}
else
{
lean_object* x_3144; lean_object* x_3145; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3144 = lean_ctor_get(x_2862, 0);
lean_inc(x_3144);
x_3145 = lean_ctor_get(x_2862, 1);
lean_inc(x_3145);
lean_dec(x_2862);
x_2837 = x_3144;
x_2838 = x_3145;
goto block_2860;
}
block_2836:
{
uint8_t x_2815; 
x_2815 = !lean_is_exclusive(x_2814);
if (x_2815 == 0)
{
lean_object* x_2816; uint8_t x_2817; 
x_2816 = lean_ctor_get(x_2814, 2);
x_2817 = !lean_is_exclusive(x_2816);
if (x_2817 == 0)
{
lean_object* x_2818; lean_object* x_2819; 
x_2818 = lean_ctor_get(x_2816, 2);
lean_dec(x_2818);
lean_ctor_set(x_2816, 2, x_2812);
if (lean_is_scalar(x_2802)) {
 x_2819 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2819 = x_2802;
}
lean_ctor_set(x_2819, 0, x_2813);
lean_ctor_set(x_2819, 1, x_2814);
return x_2819;
}
else
{
lean_object* x_2820; lean_object* x_2821; lean_object* x_2822; lean_object* x_2823; 
x_2820 = lean_ctor_get(x_2816, 0);
x_2821 = lean_ctor_get(x_2816, 1);
lean_inc(x_2821);
lean_inc(x_2820);
lean_dec(x_2816);
x_2822 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2822, 0, x_2820);
lean_ctor_set(x_2822, 1, x_2821);
lean_ctor_set(x_2822, 2, x_2812);
lean_ctor_set(x_2814, 2, x_2822);
if (lean_is_scalar(x_2802)) {
 x_2823 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2823 = x_2802;
}
lean_ctor_set(x_2823, 0, x_2813);
lean_ctor_set(x_2823, 1, x_2814);
return x_2823;
}
}
else
{
lean_object* x_2824; lean_object* x_2825; lean_object* x_2826; lean_object* x_2827; lean_object* x_2828; lean_object* x_2829; lean_object* x_2830; lean_object* x_2831; lean_object* x_2832; lean_object* x_2833; lean_object* x_2834; lean_object* x_2835; 
x_2824 = lean_ctor_get(x_2814, 2);
x_2825 = lean_ctor_get(x_2814, 0);
x_2826 = lean_ctor_get(x_2814, 1);
x_2827 = lean_ctor_get(x_2814, 3);
x_2828 = lean_ctor_get(x_2814, 4);
x_2829 = lean_ctor_get(x_2814, 5);
lean_inc(x_2829);
lean_inc(x_2828);
lean_inc(x_2827);
lean_inc(x_2824);
lean_inc(x_2826);
lean_inc(x_2825);
lean_dec(x_2814);
x_2830 = lean_ctor_get(x_2824, 0);
lean_inc(x_2830);
x_2831 = lean_ctor_get(x_2824, 1);
lean_inc(x_2831);
if (lean_is_exclusive(x_2824)) {
 lean_ctor_release(x_2824, 0);
 lean_ctor_release(x_2824, 1);
 lean_ctor_release(x_2824, 2);
 x_2832 = x_2824;
} else {
 lean_dec_ref(x_2824);
 x_2832 = lean_box(0);
}
if (lean_is_scalar(x_2832)) {
 x_2833 = lean_alloc_ctor(0, 3, 0);
} else {
 x_2833 = x_2832;
}
lean_ctor_set(x_2833, 0, x_2830);
lean_ctor_set(x_2833, 1, x_2831);
lean_ctor_set(x_2833, 2, x_2812);
x_2834 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2834, 0, x_2825);
lean_ctor_set(x_2834, 1, x_2826);
lean_ctor_set(x_2834, 2, x_2833);
lean_ctor_set(x_2834, 3, x_2827);
lean_ctor_set(x_2834, 4, x_2828);
lean_ctor_set(x_2834, 5, x_2829);
if (lean_is_scalar(x_2802)) {
 x_2835 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2835 = x_2802;
}
lean_ctor_set(x_2835, 0, x_2813);
lean_ctor_set(x_2835, 1, x_2834);
return x_2835;
}
}
block_2860:
{
uint8_t x_2839; 
x_2839 = !lean_is_exclusive(x_2838);
if (x_2839 == 0)
{
lean_object* x_2840; uint8_t x_2841; 
x_2840 = lean_ctor_get(x_2838, 2);
x_2841 = !lean_is_exclusive(x_2840);
if (x_2841 == 0)
{
lean_object* x_2842; lean_object* x_2843; 
x_2842 = lean_ctor_get(x_2840, 2);
lean_dec(x_2842);
lean_ctor_set(x_2840, 2, x_2812);
if (lean_is_scalar(x_2791)) {
 x_2843 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2843 = x_2791;
 lean_ctor_set_tag(x_2843, 1);
}
lean_ctor_set(x_2843, 0, x_2837);
lean_ctor_set(x_2843, 1, x_2838);
return x_2843;
}
else
{
lean_object* x_2844; lean_object* x_2845; lean_object* x_2846; lean_object* x_2847; 
x_2844 = lean_ctor_get(x_2840, 0);
x_2845 = lean_ctor_get(x_2840, 1);
lean_inc(x_2845);
lean_inc(x_2844);
lean_dec(x_2840);
x_2846 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2846, 0, x_2844);
lean_ctor_set(x_2846, 1, x_2845);
lean_ctor_set(x_2846, 2, x_2812);
lean_ctor_set(x_2838, 2, x_2846);
if (lean_is_scalar(x_2791)) {
 x_2847 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2847 = x_2791;
 lean_ctor_set_tag(x_2847, 1);
}
lean_ctor_set(x_2847, 0, x_2837);
lean_ctor_set(x_2847, 1, x_2838);
return x_2847;
}
}
else
{
lean_object* x_2848; lean_object* x_2849; lean_object* x_2850; lean_object* x_2851; lean_object* x_2852; lean_object* x_2853; lean_object* x_2854; lean_object* x_2855; lean_object* x_2856; lean_object* x_2857; lean_object* x_2858; lean_object* x_2859; 
x_2848 = lean_ctor_get(x_2838, 2);
x_2849 = lean_ctor_get(x_2838, 0);
x_2850 = lean_ctor_get(x_2838, 1);
x_2851 = lean_ctor_get(x_2838, 3);
x_2852 = lean_ctor_get(x_2838, 4);
x_2853 = lean_ctor_get(x_2838, 5);
lean_inc(x_2853);
lean_inc(x_2852);
lean_inc(x_2851);
lean_inc(x_2848);
lean_inc(x_2850);
lean_inc(x_2849);
lean_dec(x_2838);
x_2854 = lean_ctor_get(x_2848, 0);
lean_inc(x_2854);
x_2855 = lean_ctor_get(x_2848, 1);
lean_inc(x_2855);
if (lean_is_exclusive(x_2848)) {
 lean_ctor_release(x_2848, 0);
 lean_ctor_release(x_2848, 1);
 lean_ctor_release(x_2848, 2);
 x_2856 = x_2848;
} else {
 lean_dec_ref(x_2848);
 x_2856 = lean_box(0);
}
if (lean_is_scalar(x_2856)) {
 x_2857 = lean_alloc_ctor(0, 3, 0);
} else {
 x_2857 = x_2856;
}
lean_ctor_set(x_2857, 0, x_2854);
lean_ctor_set(x_2857, 1, x_2855);
lean_ctor_set(x_2857, 2, x_2812);
x_2858 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2858, 0, x_2849);
lean_ctor_set(x_2858, 1, x_2850);
lean_ctor_set(x_2858, 2, x_2857);
lean_ctor_set(x_2858, 3, x_2851);
lean_ctor_set(x_2858, 4, x_2852);
lean_ctor_set(x_2858, 5, x_2853);
if (lean_is_scalar(x_2791)) {
 x_2859 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2859 = x_2791;
 lean_ctor_set_tag(x_2859, 1);
}
lean_ctor_set(x_2859, 0, x_2837);
lean_ctor_set(x_2859, 1, x_2858);
return x_2859;
}
}
}
else
{
lean_object* x_3146; lean_object* x_3147; lean_object* x_3148; lean_object* x_3149; lean_object* x_3150; lean_object* x_3165; lean_object* x_3166; lean_object* x_3181; lean_object* x_3182; lean_object* x_3183; 
x_3146 = lean_ctor_get(x_2810, 0);
x_3147 = lean_ctor_get(x_2810, 1);
x_3148 = lean_ctor_get(x_2810, 2);
lean_inc(x_3148);
lean_inc(x_3147);
lean_inc(x_3146);
lean_dec(x_2810);
x_3181 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_3182 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3182, 0, x_3146);
lean_ctor_set(x_3182, 1, x_3147);
lean_ctor_set(x_3182, 2, x_3181);
lean_ctor_set(x_2801, 2, x_3182);
lean_inc(x_2793);
x_3183 = l_Lean_Meta_getMVarDecl(x_2793, x_2807, x_2801);
if (lean_obj_tag(x_3183) == 0)
{
lean_object* x_3184; lean_object* x_3185; lean_object* x_3186; lean_object* x_3187; 
x_3184 = lean_ctor_get(x_3183, 0);
lean_inc(x_3184);
x_3185 = lean_ctor_get(x_3183, 1);
lean_inc(x_3185);
lean_dec(x_3183);
x_3186 = lean_ctor_get(x_3184, 2);
lean_inc(x_3186);
lean_dec(x_3184);
lean_inc(x_2807);
lean_inc(x_2797);
x_3187 = l_Lean_Meta_getLocalDecl(x_2797, x_2807, x_3185);
if (lean_obj_tag(x_3187) == 0)
{
lean_object* x_3188; lean_object* x_3189; lean_object* x_3190; lean_object* x_3369; uint8_t x_3370; 
x_3188 = lean_ctor_get(x_3187, 0);
lean_inc(x_3188);
x_3189 = lean_ctor_get(x_3187, 1);
lean_inc(x_3189);
lean_dec(x_3187);
x_3369 = l_Lean_LocalDecl_type(x_3188);
lean_dec(x_3188);
x_3370 = l_Lean_Expr_isAppOfArity___main(x_3369, x_2745, x_2746);
if (x_3370 == 0)
{
lean_object* x_3371; lean_object* x_3372; lean_object* x_3373; 
lean_dec(x_3369);
lean_dec(x_3186);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3371 = l_Lean_Meta_isClassQuick___main___closed__1;
x_3372 = l_unreachable_x21___rarg(x_3371);
x_3373 = lean_apply_2(x_3372, x_2807, x_3189);
if (lean_obj_tag(x_3373) == 0)
{
lean_object* x_3374; lean_object* x_3375; 
lean_dec(x_2791);
x_3374 = lean_ctor_get(x_3373, 0);
lean_inc(x_3374);
x_3375 = lean_ctor_get(x_3373, 1);
lean_inc(x_3375);
lean_dec(x_3373);
x_3149 = x_3374;
x_3150 = x_3375;
goto block_3164;
}
else
{
lean_object* x_3376; lean_object* x_3377; 
lean_dec(x_2802);
x_3376 = lean_ctor_get(x_3373, 0);
lean_inc(x_3376);
x_3377 = lean_ctor_get(x_3373, 1);
lean_inc(x_3377);
lean_dec(x_3373);
x_3165 = x_3376;
x_3166 = x_3377;
goto block_3180;
}
}
else
{
lean_object* x_3378; 
x_3378 = l_Lean_Expr_getAppNumArgsAux___main(x_3369, x_2731);
if (x_2759 == 0)
{
lean_object* x_3379; lean_object* x_3380; lean_object* x_3381; 
x_3379 = lean_nat_sub(x_3378, x_2755);
lean_dec(x_3378);
x_3380 = lean_nat_sub(x_3379, x_2751);
lean_dec(x_3379);
x_3381 = l_Lean_Expr_getRevArg_x21___main(x_3369, x_3380);
lean_dec(x_3369);
x_3190 = x_3381;
goto block_3368;
}
else
{
lean_object* x_3382; lean_object* x_3383; lean_object* x_3384; 
x_3382 = lean_nat_sub(x_3378, x_2751);
lean_dec(x_3378);
x_3383 = lean_nat_sub(x_3382, x_2751);
lean_dec(x_3382);
x_3384 = l_Lean_Expr_getRevArg_x21___main(x_3369, x_3383);
lean_dec(x_3369);
x_3190 = x_3384;
goto block_3368;
}
}
block_3368:
{
lean_object* x_3191; lean_object* x_3192; uint8_t x_3193; 
x_3191 = lean_ctor_get(x_3189, 1);
lean_inc(x_3191);
lean_inc(x_3186);
x_3192 = l_Lean_MetavarContext_exprDependsOn(x_3191, x_3186, x_2797);
x_3193 = lean_unbox(x_3192);
lean_dec(x_3192);
if (x_3193 == 0)
{
lean_object* x_3194; lean_object* x_3195; lean_object* x_3196; 
x_3194 = l_Lean_mkOptionalNode___closed__2;
x_3195 = lean_array_push(x_3194, x_2796);
lean_inc(x_2807);
lean_inc(x_3186);
lean_inc(x_3195);
x_3196 = l_Lean_Meta_mkLambda(x_3195, x_3186, x_2807, x_3189);
if (lean_obj_tag(x_3196) == 0)
{
lean_object* x_3197; lean_object* x_3198; lean_object* x_3199; lean_object* x_3200; lean_object* x_3201; lean_object* x_3202; 
x_3197 = lean_ctor_get(x_3196, 0);
lean_inc(x_3197);
x_3198 = lean_ctor_get(x_3196, 1);
lean_inc(x_3198);
lean_dec(x_3196);
x_3199 = lean_expr_abstract(x_3186, x_3195);
lean_dec(x_3195);
lean_dec(x_3186);
x_3200 = lean_expr_instantiate1(x_3199, x_3190);
lean_dec(x_3190);
lean_dec(x_3199);
if (x_2759 == 0)
{
lean_object* x_3244; 
lean_inc(x_2807);
x_3244 = l_Lean_Meta_mkEqSymm(x_2798, x_2807, x_3198);
if (lean_obj_tag(x_3244) == 0)
{
lean_object* x_3245; lean_object* x_3246; 
x_3245 = lean_ctor_get(x_3244, 0);
lean_inc(x_3245);
x_3246 = lean_ctor_get(x_3244, 1);
lean_inc(x_3246);
lean_dec(x_3244);
x_3201 = x_3245;
x_3202 = x_3246;
goto block_3243;
}
else
{
lean_object* x_3247; lean_object* x_3248; 
lean_dec(x_3200);
lean_dec(x_3197);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3247 = lean_ctor_get(x_3244, 0);
lean_inc(x_3247);
x_3248 = lean_ctor_get(x_3244, 1);
lean_inc(x_3248);
lean_dec(x_3244);
x_3165 = x_3247;
x_3166 = x_3248;
goto block_3180;
}
}
else
{
x_3201 = x_2798;
x_3202 = x_3198;
goto block_3243;
}
block_3243:
{
uint8_t x_3203; lean_object* x_3204; lean_object* x_3205; lean_object* x_3206; lean_object* x_3207; 
x_3203 = 2;
lean_inc(x_2807);
x_3204 = l_Lean_Meta_mkFreshExprMVar(x_3200, x_2736, x_3203, x_2807, x_3202);
x_3205 = lean_ctor_get(x_3204, 0);
lean_inc(x_3205);
x_3206 = lean_ctor_get(x_3204, 1);
lean_inc(x_3206);
lean_dec(x_3204);
lean_inc(x_2807);
lean_inc(x_3205);
x_3207 = l_Lean_Meta_mkEqNDRec(x_3197, x_3205, x_3201, x_2807, x_3206);
if (lean_obj_tag(x_3207) == 0)
{
lean_object* x_3208; lean_object* x_3209; lean_object* x_3210; lean_object* x_3211; lean_object* x_3212; lean_object* x_3213; lean_object* x_3214; lean_object* x_3215; lean_object* x_3216; lean_object* x_3217; lean_object* x_3218; lean_object* x_3219; lean_object* x_3220; 
x_3208 = lean_ctor_get(x_3207, 1);
lean_inc(x_3208);
x_3209 = lean_ctor_get(x_3207, 0);
lean_inc(x_3209);
lean_dec(x_3207);
x_3210 = lean_ctor_get(x_3208, 0);
lean_inc(x_3210);
x_3211 = lean_ctor_get(x_3208, 1);
lean_inc(x_3211);
x_3212 = lean_ctor_get(x_3208, 2);
lean_inc(x_3212);
x_3213 = lean_ctor_get(x_3208, 3);
lean_inc(x_3213);
x_3214 = lean_ctor_get(x_3208, 4);
lean_inc(x_3214);
x_3215 = lean_ctor_get(x_3208, 5);
lean_inc(x_3215);
if (lean_is_exclusive(x_3208)) {
 lean_ctor_release(x_3208, 0);
 lean_ctor_release(x_3208, 1);
 lean_ctor_release(x_3208, 2);
 lean_ctor_release(x_3208, 3);
 lean_ctor_release(x_3208, 4);
 lean_ctor_release(x_3208, 5);
 x_3216 = x_3208;
} else {
 lean_dec_ref(x_3208);
 x_3216 = lean_box(0);
}
x_3217 = l_Lean_MetavarContext_assignExpr(x_3211, x_2793, x_3209);
if (lean_is_scalar(x_3216)) {
 x_3218 = lean_alloc_ctor(0, 6, 0);
} else {
 x_3218 = x_3216;
}
lean_ctor_set(x_3218, 0, x_3210);
lean_ctor_set(x_3218, 1, x_3217);
lean_ctor_set(x_3218, 2, x_3212);
lean_ctor_set(x_3218, 3, x_3213);
lean_ctor_set(x_3218, 4, x_3214);
lean_ctor_set(x_3218, 5, x_3215);
x_3219 = l_Lean_Expr_mvarId_x21(x_3205);
lean_dec(x_3205);
x_3220 = l_Lean_Meta_clear(x_3219, x_2797, x_2807, x_3218);
if (lean_obj_tag(x_3220) == 0)
{
lean_object* x_3221; lean_object* x_3222; lean_object* x_3223; 
x_3221 = lean_ctor_get(x_3220, 0);
lean_inc(x_3221);
x_3222 = lean_ctor_get(x_3220, 1);
lean_inc(x_3222);
lean_dec(x_3220);
x_3223 = l_Lean_Meta_clear(x_3221, x_2795, x_2807, x_3222);
if (lean_obj_tag(x_3223) == 0)
{
lean_object* x_3224; lean_object* x_3225; lean_object* x_3226; lean_object* x_3227; lean_object* x_3228; 
x_3224 = lean_ctor_get(x_3223, 0);
lean_inc(x_3224);
x_3225 = lean_ctor_get(x_3223, 1);
lean_inc(x_3225);
lean_dec(x_3223);
x_3226 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_3227 = lean_nat_sub(x_3226, x_2755);
lean_dec(x_3226);
x_3228 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_3224, x_3227, x_2786, x_2807, x_3225);
lean_dec(x_2807);
if (lean_obj_tag(x_3228) == 0)
{
lean_object* x_3229; lean_object* x_3230; lean_object* x_3231; lean_object* x_3232; lean_object* x_3233; lean_object* x_3234; 
lean_dec(x_2791);
x_3229 = lean_ctor_get(x_3228, 0);
lean_inc(x_3229);
x_3230 = lean_ctor_get(x_3228, 1);
lean_inc(x_3230);
lean_dec(x_3228);
x_3231 = lean_ctor_get(x_3229, 1);
lean_inc(x_3231);
if (lean_is_exclusive(x_3229)) {
 lean_ctor_release(x_3229, 0);
 lean_ctor_release(x_3229, 1);
 x_3232 = x_3229;
} else {
 lean_dec_ref(x_3229);
 x_3232 = lean_box(0);
}
x_3233 = lean_box(0);
if (lean_is_scalar(x_3232)) {
 x_3234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3234 = x_3232;
}
lean_ctor_set(x_3234, 0, x_3233);
lean_ctor_set(x_3234, 1, x_3231);
x_3149 = x_3234;
x_3150 = x_3230;
goto block_3164;
}
else
{
lean_object* x_3235; lean_object* x_3236; 
lean_dec(x_2802);
x_3235 = lean_ctor_get(x_3228, 0);
lean_inc(x_3235);
x_3236 = lean_ctor_get(x_3228, 1);
lean_inc(x_3236);
lean_dec(x_3228);
x_3165 = x_3235;
x_3166 = x_3236;
goto block_3180;
}
}
else
{
lean_object* x_3237; lean_object* x_3238; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2784);
x_3237 = lean_ctor_get(x_3223, 0);
lean_inc(x_3237);
x_3238 = lean_ctor_get(x_3223, 1);
lean_inc(x_3238);
lean_dec(x_3223);
x_3165 = x_3237;
x_3166 = x_3238;
goto block_3180;
}
}
else
{
lean_object* x_3239; lean_object* x_3240; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2795);
lean_dec(x_2784);
x_3239 = lean_ctor_get(x_3220, 0);
lean_inc(x_3239);
x_3240 = lean_ctor_get(x_3220, 1);
lean_inc(x_3240);
lean_dec(x_3220);
x_3165 = x_3239;
x_3166 = x_3240;
goto block_3180;
}
}
else
{
lean_object* x_3241; lean_object* x_3242; 
lean_dec(x_3205);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
x_3241 = lean_ctor_get(x_3207, 0);
lean_inc(x_3241);
x_3242 = lean_ctor_get(x_3207, 1);
lean_inc(x_3242);
lean_dec(x_3207);
x_3165 = x_3241;
x_3166 = x_3242;
goto block_3180;
}
}
}
else
{
lean_object* x_3249; lean_object* x_3250; 
lean_dec(x_3195);
lean_dec(x_3190);
lean_dec(x_3186);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3249 = lean_ctor_get(x_3196, 0);
lean_inc(x_3249);
x_3250 = lean_ctor_get(x_3196, 1);
lean_inc(x_3250);
lean_dec(x_3196);
x_3165 = x_3249;
x_3166 = x_3250;
goto block_3180;
}
}
else
{
lean_object* x_3251; lean_object* x_3252; lean_object* x_3253; lean_object* x_3254; lean_object* x_3255; 
x_3251 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2796);
x_3252 = lean_array_push(x_3251, x_2796);
x_3253 = lean_expr_abstract(x_3186, x_3252);
lean_dec(x_3252);
x_3254 = lean_expr_instantiate1(x_3253, x_3190);
lean_dec(x_3253);
lean_inc(x_2807);
lean_inc(x_3190);
x_3255 = l_Lean_Meta_mkEqRefl(x_3190, x_2807, x_3189);
if (lean_obj_tag(x_3255) == 0)
{
lean_object* x_3256; lean_object* x_3257; lean_object* x_3258; lean_object* x_3259; lean_object* x_3260; 
x_3256 = lean_ctor_get(x_3255, 0);
lean_inc(x_3256);
x_3257 = lean_ctor_get(x_3255, 1);
lean_inc(x_3257);
lean_dec(x_3255);
lean_inc(x_2798);
x_3258 = lean_array_push(x_3251, x_2798);
x_3259 = lean_expr_abstract(x_3254, x_3258);
lean_dec(x_3254);
x_3260 = lean_expr_instantiate1(x_3259, x_3256);
lean_dec(x_3256);
lean_dec(x_3259);
if (x_2759 == 0)
{
lean_object* x_3261; 
lean_inc(x_2807);
lean_inc(x_2796);
x_3261 = l_Lean_Meta_mkEq(x_3190, x_2796, x_2807, x_3257);
if (lean_obj_tag(x_3261) == 0)
{
lean_object* x_3262; lean_object* x_3263; lean_object* x_3264; lean_object* x_3265; uint8_t x_3266; lean_object* x_3267; 
x_3262 = lean_ctor_get(x_3261, 0);
lean_inc(x_3262);
x_3263 = lean_ctor_get(x_3261, 1);
lean_inc(x_3263);
lean_dec(x_3261);
x_3264 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__1___boxed), 7, 4);
lean_closure_set(x_3264, 0, x_3186);
lean_closure_set(x_3264, 1, x_3258);
lean_closure_set(x_3264, 2, x_2777);
lean_closure_set(x_3264, 3, x_2796);
x_3265 = l_Lean_Meta_substCore___closed__18;
x_3266 = 0;
lean_inc(x_2807);
x_3267 = l_Lean_Meta_withLocalDecl___rarg(x_3265, x_3262, x_3266, x_3264, x_2807, x_3263);
if (lean_obj_tag(x_3267) == 0)
{
lean_object* x_3268; lean_object* x_3269; lean_object* x_3270; 
x_3268 = lean_ctor_get(x_3267, 0);
lean_inc(x_3268);
x_3269 = lean_ctor_get(x_3267, 1);
lean_inc(x_3269);
lean_dec(x_3267);
lean_inc(x_2807);
x_3270 = l_Lean_Meta_mkEqSymm(x_2798, x_2807, x_3269);
if (lean_obj_tag(x_3270) == 0)
{
lean_object* x_3271; lean_object* x_3272; uint8_t x_3273; lean_object* x_3274; lean_object* x_3275; lean_object* x_3276; lean_object* x_3277; 
x_3271 = lean_ctor_get(x_3270, 0);
lean_inc(x_3271);
x_3272 = lean_ctor_get(x_3270, 1);
lean_inc(x_3272);
lean_dec(x_3270);
x_3273 = 2;
lean_inc(x_2807);
x_3274 = l_Lean_Meta_mkFreshExprMVar(x_3260, x_2736, x_3273, x_2807, x_3272);
x_3275 = lean_ctor_get(x_3274, 0);
lean_inc(x_3275);
x_3276 = lean_ctor_get(x_3274, 1);
lean_inc(x_3276);
lean_dec(x_3274);
lean_inc(x_2807);
lean_inc(x_3275);
x_3277 = l_Lean_Meta_mkEqRec(x_3268, x_3275, x_3271, x_2807, x_3276);
if (lean_obj_tag(x_3277) == 0)
{
lean_object* x_3278; lean_object* x_3279; lean_object* x_3280; lean_object* x_3281; lean_object* x_3282; lean_object* x_3283; lean_object* x_3284; lean_object* x_3285; lean_object* x_3286; lean_object* x_3287; lean_object* x_3288; lean_object* x_3289; lean_object* x_3290; 
x_3278 = lean_ctor_get(x_3277, 1);
lean_inc(x_3278);
x_3279 = lean_ctor_get(x_3277, 0);
lean_inc(x_3279);
lean_dec(x_3277);
x_3280 = lean_ctor_get(x_3278, 0);
lean_inc(x_3280);
x_3281 = lean_ctor_get(x_3278, 1);
lean_inc(x_3281);
x_3282 = lean_ctor_get(x_3278, 2);
lean_inc(x_3282);
x_3283 = lean_ctor_get(x_3278, 3);
lean_inc(x_3283);
x_3284 = lean_ctor_get(x_3278, 4);
lean_inc(x_3284);
x_3285 = lean_ctor_get(x_3278, 5);
lean_inc(x_3285);
if (lean_is_exclusive(x_3278)) {
 lean_ctor_release(x_3278, 0);
 lean_ctor_release(x_3278, 1);
 lean_ctor_release(x_3278, 2);
 lean_ctor_release(x_3278, 3);
 lean_ctor_release(x_3278, 4);
 lean_ctor_release(x_3278, 5);
 x_3286 = x_3278;
} else {
 lean_dec_ref(x_3278);
 x_3286 = lean_box(0);
}
x_3287 = l_Lean_MetavarContext_assignExpr(x_3281, x_2793, x_3279);
if (lean_is_scalar(x_3286)) {
 x_3288 = lean_alloc_ctor(0, 6, 0);
} else {
 x_3288 = x_3286;
}
lean_ctor_set(x_3288, 0, x_3280);
lean_ctor_set(x_3288, 1, x_3287);
lean_ctor_set(x_3288, 2, x_3282);
lean_ctor_set(x_3288, 3, x_3283);
lean_ctor_set(x_3288, 4, x_3284);
lean_ctor_set(x_3288, 5, x_3285);
x_3289 = l_Lean_Expr_mvarId_x21(x_3275);
lean_dec(x_3275);
x_3290 = l_Lean_Meta_clear(x_3289, x_2797, x_2807, x_3288);
if (lean_obj_tag(x_3290) == 0)
{
lean_object* x_3291; lean_object* x_3292; lean_object* x_3293; 
x_3291 = lean_ctor_get(x_3290, 0);
lean_inc(x_3291);
x_3292 = lean_ctor_get(x_3290, 1);
lean_inc(x_3292);
lean_dec(x_3290);
x_3293 = l_Lean_Meta_clear(x_3291, x_2795, x_2807, x_3292);
if (lean_obj_tag(x_3293) == 0)
{
lean_object* x_3294; lean_object* x_3295; lean_object* x_3296; lean_object* x_3297; lean_object* x_3298; 
x_3294 = lean_ctor_get(x_3293, 0);
lean_inc(x_3294);
x_3295 = lean_ctor_get(x_3293, 1);
lean_inc(x_3295);
lean_dec(x_3293);
x_3296 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_3297 = lean_nat_sub(x_3296, x_2755);
lean_dec(x_3296);
x_3298 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_3294, x_3297, x_2786, x_2807, x_3295);
lean_dec(x_2807);
if (lean_obj_tag(x_3298) == 0)
{
lean_object* x_3299; lean_object* x_3300; lean_object* x_3301; lean_object* x_3302; lean_object* x_3303; lean_object* x_3304; 
lean_dec(x_2791);
x_3299 = lean_ctor_get(x_3298, 0);
lean_inc(x_3299);
x_3300 = lean_ctor_get(x_3298, 1);
lean_inc(x_3300);
lean_dec(x_3298);
x_3301 = lean_ctor_get(x_3299, 1);
lean_inc(x_3301);
if (lean_is_exclusive(x_3299)) {
 lean_ctor_release(x_3299, 0);
 lean_ctor_release(x_3299, 1);
 x_3302 = x_3299;
} else {
 lean_dec_ref(x_3299);
 x_3302 = lean_box(0);
}
x_3303 = lean_box(0);
if (lean_is_scalar(x_3302)) {
 x_3304 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3304 = x_3302;
}
lean_ctor_set(x_3304, 0, x_3303);
lean_ctor_set(x_3304, 1, x_3301);
x_3149 = x_3304;
x_3150 = x_3300;
goto block_3164;
}
else
{
lean_object* x_3305; lean_object* x_3306; 
lean_dec(x_2802);
x_3305 = lean_ctor_get(x_3298, 0);
lean_inc(x_3305);
x_3306 = lean_ctor_get(x_3298, 1);
lean_inc(x_3306);
lean_dec(x_3298);
x_3165 = x_3305;
x_3166 = x_3306;
goto block_3180;
}
}
else
{
lean_object* x_3307; lean_object* x_3308; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2784);
x_3307 = lean_ctor_get(x_3293, 0);
lean_inc(x_3307);
x_3308 = lean_ctor_get(x_3293, 1);
lean_inc(x_3308);
lean_dec(x_3293);
x_3165 = x_3307;
x_3166 = x_3308;
goto block_3180;
}
}
else
{
lean_object* x_3309; lean_object* x_3310; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2795);
lean_dec(x_2784);
x_3309 = lean_ctor_get(x_3290, 0);
lean_inc(x_3309);
x_3310 = lean_ctor_get(x_3290, 1);
lean_inc(x_3310);
lean_dec(x_3290);
x_3165 = x_3309;
x_3166 = x_3310;
goto block_3180;
}
}
else
{
lean_object* x_3311; lean_object* x_3312; 
lean_dec(x_3275);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
x_3311 = lean_ctor_get(x_3277, 0);
lean_inc(x_3311);
x_3312 = lean_ctor_get(x_3277, 1);
lean_inc(x_3312);
lean_dec(x_3277);
x_3165 = x_3311;
x_3166 = x_3312;
goto block_3180;
}
}
else
{
lean_object* x_3313; lean_object* x_3314; 
lean_dec(x_3268);
lean_dec(x_3260);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3313 = lean_ctor_get(x_3270, 0);
lean_inc(x_3313);
x_3314 = lean_ctor_get(x_3270, 1);
lean_inc(x_3314);
lean_dec(x_3270);
x_3165 = x_3313;
x_3166 = x_3314;
goto block_3180;
}
}
else
{
lean_object* x_3315; lean_object* x_3316; 
lean_dec(x_3260);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3315 = lean_ctor_get(x_3267, 0);
lean_inc(x_3315);
x_3316 = lean_ctor_get(x_3267, 1);
lean_inc(x_3316);
lean_dec(x_3267);
x_3165 = x_3315;
x_3166 = x_3316;
goto block_3180;
}
}
else
{
lean_object* x_3317; lean_object* x_3318; 
lean_dec(x_3260);
lean_dec(x_3258);
lean_dec(x_3186);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3317 = lean_ctor_get(x_3261, 0);
lean_inc(x_3317);
x_3318 = lean_ctor_get(x_3261, 1);
lean_inc(x_3318);
lean_dec(x_3261);
x_3165 = x_3317;
x_3166 = x_3318;
goto block_3180;
}
}
else
{
lean_object* x_3319; lean_object* x_3320; lean_object* x_3321; 
lean_dec(x_3258);
lean_dec(x_3190);
x_3319 = lean_array_push(x_2777, x_2796);
lean_inc(x_2798);
x_3320 = lean_array_push(x_3319, x_2798);
lean_inc(x_2807);
x_3321 = l_Lean_Meta_mkLambda(x_3320, x_3186, x_2807, x_3257);
if (lean_obj_tag(x_3321) == 0)
{
lean_object* x_3322; lean_object* x_3323; uint8_t x_3324; lean_object* x_3325; lean_object* x_3326; lean_object* x_3327; lean_object* x_3328; 
x_3322 = lean_ctor_get(x_3321, 0);
lean_inc(x_3322);
x_3323 = lean_ctor_get(x_3321, 1);
lean_inc(x_3323);
lean_dec(x_3321);
x_3324 = 2;
lean_inc(x_2807);
x_3325 = l_Lean_Meta_mkFreshExprMVar(x_3260, x_2736, x_3324, x_2807, x_3323);
x_3326 = lean_ctor_get(x_3325, 0);
lean_inc(x_3326);
x_3327 = lean_ctor_get(x_3325, 1);
lean_inc(x_3327);
lean_dec(x_3325);
lean_inc(x_2807);
lean_inc(x_3326);
x_3328 = l_Lean_Meta_mkEqRec(x_3322, x_3326, x_2798, x_2807, x_3327);
if (lean_obj_tag(x_3328) == 0)
{
lean_object* x_3329; lean_object* x_3330; lean_object* x_3331; lean_object* x_3332; lean_object* x_3333; lean_object* x_3334; lean_object* x_3335; lean_object* x_3336; lean_object* x_3337; lean_object* x_3338; lean_object* x_3339; lean_object* x_3340; lean_object* x_3341; 
x_3329 = lean_ctor_get(x_3328, 1);
lean_inc(x_3329);
x_3330 = lean_ctor_get(x_3328, 0);
lean_inc(x_3330);
lean_dec(x_3328);
x_3331 = lean_ctor_get(x_3329, 0);
lean_inc(x_3331);
x_3332 = lean_ctor_get(x_3329, 1);
lean_inc(x_3332);
x_3333 = lean_ctor_get(x_3329, 2);
lean_inc(x_3333);
x_3334 = lean_ctor_get(x_3329, 3);
lean_inc(x_3334);
x_3335 = lean_ctor_get(x_3329, 4);
lean_inc(x_3335);
x_3336 = lean_ctor_get(x_3329, 5);
lean_inc(x_3336);
if (lean_is_exclusive(x_3329)) {
 lean_ctor_release(x_3329, 0);
 lean_ctor_release(x_3329, 1);
 lean_ctor_release(x_3329, 2);
 lean_ctor_release(x_3329, 3);
 lean_ctor_release(x_3329, 4);
 lean_ctor_release(x_3329, 5);
 x_3337 = x_3329;
} else {
 lean_dec_ref(x_3329);
 x_3337 = lean_box(0);
}
x_3338 = l_Lean_MetavarContext_assignExpr(x_3332, x_2793, x_3330);
if (lean_is_scalar(x_3337)) {
 x_3339 = lean_alloc_ctor(0, 6, 0);
} else {
 x_3339 = x_3337;
}
lean_ctor_set(x_3339, 0, x_3331);
lean_ctor_set(x_3339, 1, x_3338);
lean_ctor_set(x_3339, 2, x_3333);
lean_ctor_set(x_3339, 3, x_3334);
lean_ctor_set(x_3339, 4, x_3335);
lean_ctor_set(x_3339, 5, x_3336);
x_3340 = l_Lean_Expr_mvarId_x21(x_3326);
lean_dec(x_3326);
x_3341 = l_Lean_Meta_clear(x_3340, x_2797, x_2807, x_3339);
if (lean_obj_tag(x_3341) == 0)
{
lean_object* x_3342; lean_object* x_3343; lean_object* x_3344; 
x_3342 = lean_ctor_get(x_3341, 0);
lean_inc(x_3342);
x_3343 = lean_ctor_get(x_3341, 1);
lean_inc(x_3343);
lean_dec(x_3341);
x_3344 = l_Lean_Meta_clear(x_3342, x_2795, x_2807, x_3343);
if (lean_obj_tag(x_3344) == 0)
{
lean_object* x_3345; lean_object* x_3346; lean_object* x_3347; lean_object* x_3348; lean_object* x_3349; 
x_3345 = lean_ctor_get(x_3344, 0);
lean_inc(x_3345);
x_3346 = lean_ctor_get(x_3344, 1);
lean_inc(x_3346);
lean_dec(x_3344);
x_3347 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_3348 = lean_nat_sub(x_3347, x_2755);
lean_dec(x_3347);
x_3349 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_3345, x_3348, x_2786, x_2807, x_3346);
lean_dec(x_2807);
if (lean_obj_tag(x_3349) == 0)
{
lean_object* x_3350; lean_object* x_3351; lean_object* x_3352; lean_object* x_3353; lean_object* x_3354; lean_object* x_3355; 
lean_dec(x_2791);
x_3350 = lean_ctor_get(x_3349, 0);
lean_inc(x_3350);
x_3351 = lean_ctor_get(x_3349, 1);
lean_inc(x_3351);
lean_dec(x_3349);
x_3352 = lean_ctor_get(x_3350, 1);
lean_inc(x_3352);
if (lean_is_exclusive(x_3350)) {
 lean_ctor_release(x_3350, 0);
 lean_ctor_release(x_3350, 1);
 x_3353 = x_3350;
} else {
 lean_dec_ref(x_3350);
 x_3353 = lean_box(0);
}
x_3354 = lean_box(0);
if (lean_is_scalar(x_3353)) {
 x_3355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3355 = x_3353;
}
lean_ctor_set(x_3355, 0, x_3354);
lean_ctor_set(x_3355, 1, x_3352);
x_3149 = x_3355;
x_3150 = x_3351;
goto block_3164;
}
else
{
lean_object* x_3356; lean_object* x_3357; 
lean_dec(x_2802);
x_3356 = lean_ctor_get(x_3349, 0);
lean_inc(x_3356);
x_3357 = lean_ctor_get(x_3349, 1);
lean_inc(x_3357);
lean_dec(x_3349);
x_3165 = x_3356;
x_3166 = x_3357;
goto block_3180;
}
}
else
{
lean_object* x_3358; lean_object* x_3359; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2784);
x_3358 = lean_ctor_get(x_3344, 0);
lean_inc(x_3358);
x_3359 = lean_ctor_get(x_3344, 1);
lean_inc(x_3359);
lean_dec(x_3344);
x_3165 = x_3358;
x_3166 = x_3359;
goto block_3180;
}
}
else
{
lean_object* x_3360; lean_object* x_3361; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2795);
lean_dec(x_2784);
x_3360 = lean_ctor_get(x_3341, 0);
lean_inc(x_3360);
x_3361 = lean_ctor_get(x_3341, 1);
lean_inc(x_3361);
lean_dec(x_3341);
x_3165 = x_3360;
x_3166 = x_3361;
goto block_3180;
}
}
else
{
lean_object* x_3362; lean_object* x_3363; 
lean_dec(x_3326);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
x_3362 = lean_ctor_get(x_3328, 0);
lean_inc(x_3362);
x_3363 = lean_ctor_get(x_3328, 1);
lean_inc(x_3363);
lean_dec(x_3328);
x_3165 = x_3362;
x_3166 = x_3363;
goto block_3180;
}
}
else
{
lean_object* x_3364; lean_object* x_3365; 
lean_dec(x_3260);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3364 = lean_ctor_get(x_3321, 0);
lean_inc(x_3364);
x_3365 = lean_ctor_get(x_3321, 1);
lean_inc(x_3365);
lean_dec(x_3321);
x_3165 = x_3364;
x_3166 = x_3365;
goto block_3180;
}
}
}
else
{
lean_object* x_3366; lean_object* x_3367; 
lean_dec(x_3254);
lean_dec(x_3190);
lean_dec(x_3186);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3366 = lean_ctor_get(x_3255, 0);
lean_inc(x_3366);
x_3367 = lean_ctor_get(x_3255, 1);
lean_inc(x_3367);
lean_dec(x_3255);
x_3165 = x_3366;
x_3166 = x_3367;
goto block_3180;
}
}
}
}
else
{
lean_object* x_3385; lean_object* x_3386; 
lean_dec(x_3186);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3385 = lean_ctor_get(x_3187, 0);
lean_inc(x_3385);
x_3386 = lean_ctor_get(x_3187, 1);
lean_inc(x_3386);
lean_dec(x_3187);
x_3165 = x_3385;
x_3166 = x_3386;
goto block_3180;
}
}
else
{
lean_object* x_3387; lean_object* x_3388; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3387 = lean_ctor_get(x_3183, 0);
lean_inc(x_3387);
x_3388 = lean_ctor_get(x_3183, 1);
lean_inc(x_3388);
lean_dec(x_3183);
x_3165 = x_3387;
x_3166 = x_3388;
goto block_3180;
}
block_3164:
{
lean_object* x_3151; lean_object* x_3152; lean_object* x_3153; lean_object* x_3154; lean_object* x_3155; lean_object* x_3156; lean_object* x_3157; lean_object* x_3158; lean_object* x_3159; lean_object* x_3160; lean_object* x_3161; lean_object* x_3162; lean_object* x_3163; 
x_3151 = lean_ctor_get(x_3150, 2);
lean_inc(x_3151);
x_3152 = lean_ctor_get(x_3150, 0);
lean_inc(x_3152);
x_3153 = lean_ctor_get(x_3150, 1);
lean_inc(x_3153);
x_3154 = lean_ctor_get(x_3150, 3);
lean_inc(x_3154);
x_3155 = lean_ctor_get(x_3150, 4);
lean_inc(x_3155);
x_3156 = lean_ctor_get(x_3150, 5);
lean_inc(x_3156);
if (lean_is_exclusive(x_3150)) {
 lean_ctor_release(x_3150, 0);
 lean_ctor_release(x_3150, 1);
 lean_ctor_release(x_3150, 2);
 lean_ctor_release(x_3150, 3);
 lean_ctor_release(x_3150, 4);
 lean_ctor_release(x_3150, 5);
 x_3157 = x_3150;
} else {
 lean_dec_ref(x_3150);
 x_3157 = lean_box(0);
}
x_3158 = lean_ctor_get(x_3151, 0);
lean_inc(x_3158);
x_3159 = lean_ctor_get(x_3151, 1);
lean_inc(x_3159);
if (lean_is_exclusive(x_3151)) {
 lean_ctor_release(x_3151, 0);
 lean_ctor_release(x_3151, 1);
 lean_ctor_release(x_3151, 2);
 x_3160 = x_3151;
} else {
 lean_dec_ref(x_3151);
 x_3160 = lean_box(0);
}
if (lean_is_scalar(x_3160)) {
 x_3161 = lean_alloc_ctor(0, 3, 0);
} else {
 x_3161 = x_3160;
}
lean_ctor_set(x_3161, 0, x_3158);
lean_ctor_set(x_3161, 1, x_3159);
lean_ctor_set(x_3161, 2, x_3148);
if (lean_is_scalar(x_3157)) {
 x_3162 = lean_alloc_ctor(0, 6, 0);
} else {
 x_3162 = x_3157;
}
lean_ctor_set(x_3162, 0, x_3152);
lean_ctor_set(x_3162, 1, x_3153);
lean_ctor_set(x_3162, 2, x_3161);
lean_ctor_set(x_3162, 3, x_3154);
lean_ctor_set(x_3162, 4, x_3155);
lean_ctor_set(x_3162, 5, x_3156);
if (lean_is_scalar(x_2802)) {
 x_3163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3163 = x_2802;
}
lean_ctor_set(x_3163, 0, x_3149);
lean_ctor_set(x_3163, 1, x_3162);
return x_3163;
}
block_3180:
{
lean_object* x_3167; lean_object* x_3168; lean_object* x_3169; lean_object* x_3170; lean_object* x_3171; lean_object* x_3172; lean_object* x_3173; lean_object* x_3174; lean_object* x_3175; lean_object* x_3176; lean_object* x_3177; lean_object* x_3178; lean_object* x_3179; 
x_3167 = lean_ctor_get(x_3166, 2);
lean_inc(x_3167);
x_3168 = lean_ctor_get(x_3166, 0);
lean_inc(x_3168);
x_3169 = lean_ctor_get(x_3166, 1);
lean_inc(x_3169);
x_3170 = lean_ctor_get(x_3166, 3);
lean_inc(x_3170);
x_3171 = lean_ctor_get(x_3166, 4);
lean_inc(x_3171);
x_3172 = lean_ctor_get(x_3166, 5);
lean_inc(x_3172);
if (lean_is_exclusive(x_3166)) {
 lean_ctor_release(x_3166, 0);
 lean_ctor_release(x_3166, 1);
 lean_ctor_release(x_3166, 2);
 lean_ctor_release(x_3166, 3);
 lean_ctor_release(x_3166, 4);
 lean_ctor_release(x_3166, 5);
 x_3173 = x_3166;
} else {
 lean_dec_ref(x_3166);
 x_3173 = lean_box(0);
}
x_3174 = lean_ctor_get(x_3167, 0);
lean_inc(x_3174);
x_3175 = lean_ctor_get(x_3167, 1);
lean_inc(x_3175);
if (lean_is_exclusive(x_3167)) {
 lean_ctor_release(x_3167, 0);
 lean_ctor_release(x_3167, 1);
 lean_ctor_release(x_3167, 2);
 x_3176 = x_3167;
} else {
 lean_dec_ref(x_3167);
 x_3176 = lean_box(0);
}
if (lean_is_scalar(x_3176)) {
 x_3177 = lean_alloc_ctor(0, 3, 0);
} else {
 x_3177 = x_3176;
}
lean_ctor_set(x_3177, 0, x_3174);
lean_ctor_set(x_3177, 1, x_3175);
lean_ctor_set(x_3177, 2, x_3148);
if (lean_is_scalar(x_3173)) {
 x_3178 = lean_alloc_ctor(0, 6, 0);
} else {
 x_3178 = x_3173;
}
lean_ctor_set(x_3178, 0, x_3168);
lean_ctor_set(x_3178, 1, x_3169);
lean_ctor_set(x_3178, 2, x_3177);
lean_ctor_set(x_3178, 3, x_3170);
lean_ctor_set(x_3178, 4, x_3171);
lean_ctor_set(x_3178, 5, x_3172);
if (lean_is_scalar(x_2791)) {
 x_3179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3179 = x_2791;
 lean_ctor_set_tag(x_3179, 1);
}
lean_ctor_set(x_3179, 0, x_3165);
lean_ctor_set(x_3179, 1, x_3178);
return x_3179;
}
}
}
else
{
lean_object* x_3389; lean_object* x_3390; lean_object* x_3391; lean_object* x_3392; lean_object* x_3393; lean_object* x_3394; lean_object* x_3395; lean_object* x_3396; lean_object* x_3397; lean_object* x_3398; lean_object* x_3399; lean_object* x_3400; lean_object* x_3415; lean_object* x_3416; lean_object* x_3431; lean_object* x_3432; lean_object* x_3433; lean_object* x_3434; 
x_3389 = lean_ctor_get(x_2801, 2);
x_3390 = lean_ctor_get(x_2801, 0);
x_3391 = lean_ctor_get(x_2801, 1);
x_3392 = lean_ctor_get(x_2801, 3);
x_3393 = lean_ctor_get(x_2801, 4);
x_3394 = lean_ctor_get(x_2801, 5);
lean_inc(x_3394);
lean_inc(x_3393);
lean_inc(x_3392);
lean_inc(x_3389);
lean_inc(x_3391);
lean_inc(x_3390);
lean_dec(x_2801);
x_3395 = lean_ctor_get(x_3389, 0);
lean_inc(x_3395);
x_3396 = lean_ctor_get(x_3389, 1);
lean_inc(x_3396);
x_3397 = lean_ctor_get(x_3389, 2);
lean_inc(x_3397);
if (lean_is_exclusive(x_3389)) {
 lean_ctor_release(x_3389, 0);
 lean_ctor_release(x_3389, 1);
 lean_ctor_release(x_3389, 2);
 x_3398 = x_3389;
} else {
 lean_dec_ref(x_3389);
 x_3398 = lean_box(0);
}
x_3431 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_3398)) {
 x_3432 = lean_alloc_ctor(0, 3, 0);
} else {
 x_3432 = x_3398;
}
lean_ctor_set(x_3432, 0, x_3395);
lean_ctor_set(x_3432, 1, x_3396);
lean_ctor_set(x_3432, 2, x_3431);
x_3433 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_3433, 0, x_3390);
lean_ctor_set(x_3433, 1, x_3391);
lean_ctor_set(x_3433, 2, x_3432);
lean_ctor_set(x_3433, 3, x_3392);
lean_ctor_set(x_3433, 4, x_3393);
lean_ctor_set(x_3433, 5, x_3394);
lean_inc(x_2793);
x_3434 = l_Lean_Meta_getMVarDecl(x_2793, x_2807, x_3433);
if (lean_obj_tag(x_3434) == 0)
{
lean_object* x_3435; lean_object* x_3436; lean_object* x_3437; lean_object* x_3438; 
x_3435 = lean_ctor_get(x_3434, 0);
lean_inc(x_3435);
x_3436 = lean_ctor_get(x_3434, 1);
lean_inc(x_3436);
lean_dec(x_3434);
x_3437 = lean_ctor_get(x_3435, 2);
lean_inc(x_3437);
lean_dec(x_3435);
lean_inc(x_2807);
lean_inc(x_2797);
x_3438 = l_Lean_Meta_getLocalDecl(x_2797, x_2807, x_3436);
if (lean_obj_tag(x_3438) == 0)
{
lean_object* x_3439; lean_object* x_3440; lean_object* x_3441; lean_object* x_3620; uint8_t x_3621; 
x_3439 = lean_ctor_get(x_3438, 0);
lean_inc(x_3439);
x_3440 = lean_ctor_get(x_3438, 1);
lean_inc(x_3440);
lean_dec(x_3438);
x_3620 = l_Lean_LocalDecl_type(x_3439);
lean_dec(x_3439);
x_3621 = l_Lean_Expr_isAppOfArity___main(x_3620, x_2745, x_2746);
if (x_3621 == 0)
{
lean_object* x_3622; lean_object* x_3623; lean_object* x_3624; 
lean_dec(x_3620);
lean_dec(x_3437);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3622 = l_Lean_Meta_isClassQuick___main___closed__1;
x_3623 = l_unreachable_x21___rarg(x_3622);
x_3624 = lean_apply_2(x_3623, x_2807, x_3440);
if (lean_obj_tag(x_3624) == 0)
{
lean_object* x_3625; lean_object* x_3626; 
lean_dec(x_2791);
x_3625 = lean_ctor_get(x_3624, 0);
lean_inc(x_3625);
x_3626 = lean_ctor_get(x_3624, 1);
lean_inc(x_3626);
lean_dec(x_3624);
x_3399 = x_3625;
x_3400 = x_3626;
goto block_3414;
}
else
{
lean_object* x_3627; lean_object* x_3628; 
lean_dec(x_2802);
x_3627 = lean_ctor_get(x_3624, 0);
lean_inc(x_3627);
x_3628 = lean_ctor_get(x_3624, 1);
lean_inc(x_3628);
lean_dec(x_3624);
x_3415 = x_3627;
x_3416 = x_3628;
goto block_3430;
}
}
else
{
lean_object* x_3629; 
x_3629 = l_Lean_Expr_getAppNumArgsAux___main(x_3620, x_2731);
if (x_2759 == 0)
{
lean_object* x_3630; lean_object* x_3631; lean_object* x_3632; 
x_3630 = lean_nat_sub(x_3629, x_2755);
lean_dec(x_3629);
x_3631 = lean_nat_sub(x_3630, x_2751);
lean_dec(x_3630);
x_3632 = l_Lean_Expr_getRevArg_x21___main(x_3620, x_3631);
lean_dec(x_3620);
x_3441 = x_3632;
goto block_3619;
}
else
{
lean_object* x_3633; lean_object* x_3634; lean_object* x_3635; 
x_3633 = lean_nat_sub(x_3629, x_2751);
lean_dec(x_3629);
x_3634 = lean_nat_sub(x_3633, x_2751);
lean_dec(x_3633);
x_3635 = l_Lean_Expr_getRevArg_x21___main(x_3620, x_3634);
lean_dec(x_3620);
x_3441 = x_3635;
goto block_3619;
}
}
block_3619:
{
lean_object* x_3442; lean_object* x_3443; uint8_t x_3444; 
x_3442 = lean_ctor_get(x_3440, 1);
lean_inc(x_3442);
lean_inc(x_3437);
x_3443 = l_Lean_MetavarContext_exprDependsOn(x_3442, x_3437, x_2797);
x_3444 = lean_unbox(x_3443);
lean_dec(x_3443);
if (x_3444 == 0)
{
lean_object* x_3445; lean_object* x_3446; lean_object* x_3447; 
x_3445 = l_Lean_mkOptionalNode___closed__2;
x_3446 = lean_array_push(x_3445, x_2796);
lean_inc(x_2807);
lean_inc(x_3437);
lean_inc(x_3446);
x_3447 = l_Lean_Meta_mkLambda(x_3446, x_3437, x_2807, x_3440);
if (lean_obj_tag(x_3447) == 0)
{
lean_object* x_3448; lean_object* x_3449; lean_object* x_3450; lean_object* x_3451; lean_object* x_3452; lean_object* x_3453; 
x_3448 = lean_ctor_get(x_3447, 0);
lean_inc(x_3448);
x_3449 = lean_ctor_get(x_3447, 1);
lean_inc(x_3449);
lean_dec(x_3447);
x_3450 = lean_expr_abstract(x_3437, x_3446);
lean_dec(x_3446);
lean_dec(x_3437);
x_3451 = lean_expr_instantiate1(x_3450, x_3441);
lean_dec(x_3441);
lean_dec(x_3450);
if (x_2759 == 0)
{
lean_object* x_3495; 
lean_inc(x_2807);
x_3495 = l_Lean_Meta_mkEqSymm(x_2798, x_2807, x_3449);
if (lean_obj_tag(x_3495) == 0)
{
lean_object* x_3496; lean_object* x_3497; 
x_3496 = lean_ctor_get(x_3495, 0);
lean_inc(x_3496);
x_3497 = lean_ctor_get(x_3495, 1);
lean_inc(x_3497);
lean_dec(x_3495);
x_3452 = x_3496;
x_3453 = x_3497;
goto block_3494;
}
else
{
lean_object* x_3498; lean_object* x_3499; 
lean_dec(x_3451);
lean_dec(x_3448);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3498 = lean_ctor_get(x_3495, 0);
lean_inc(x_3498);
x_3499 = lean_ctor_get(x_3495, 1);
lean_inc(x_3499);
lean_dec(x_3495);
x_3415 = x_3498;
x_3416 = x_3499;
goto block_3430;
}
}
else
{
x_3452 = x_2798;
x_3453 = x_3449;
goto block_3494;
}
block_3494:
{
uint8_t x_3454; lean_object* x_3455; lean_object* x_3456; lean_object* x_3457; lean_object* x_3458; 
x_3454 = 2;
lean_inc(x_2807);
x_3455 = l_Lean_Meta_mkFreshExprMVar(x_3451, x_2736, x_3454, x_2807, x_3453);
x_3456 = lean_ctor_get(x_3455, 0);
lean_inc(x_3456);
x_3457 = lean_ctor_get(x_3455, 1);
lean_inc(x_3457);
lean_dec(x_3455);
lean_inc(x_2807);
lean_inc(x_3456);
x_3458 = l_Lean_Meta_mkEqNDRec(x_3448, x_3456, x_3452, x_2807, x_3457);
if (lean_obj_tag(x_3458) == 0)
{
lean_object* x_3459; lean_object* x_3460; lean_object* x_3461; lean_object* x_3462; lean_object* x_3463; lean_object* x_3464; lean_object* x_3465; lean_object* x_3466; lean_object* x_3467; lean_object* x_3468; lean_object* x_3469; lean_object* x_3470; lean_object* x_3471; 
x_3459 = lean_ctor_get(x_3458, 1);
lean_inc(x_3459);
x_3460 = lean_ctor_get(x_3458, 0);
lean_inc(x_3460);
lean_dec(x_3458);
x_3461 = lean_ctor_get(x_3459, 0);
lean_inc(x_3461);
x_3462 = lean_ctor_get(x_3459, 1);
lean_inc(x_3462);
x_3463 = lean_ctor_get(x_3459, 2);
lean_inc(x_3463);
x_3464 = lean_ctor_get(x_3459, 3);
lean_inc(x_3464);
x_3465 = lean_ctor_get(x_3459, 4);
lean_inc(x_3465);
x_3466 = lean_ctor_get(x_3459, 5);
lean_inc(x_3466);
if (lean_is_exclusive(x_3459)) {
 lean_ctor_release(x_3459, 0);
 lean_ctor_release(x_3459, 1);
 lean_ctor_release(x_3459, 2);
 lean_ctor_release(x_3459, 3);
 lean_ctor_release(x_3459, 4);
 lean_ctor_release(x_3459, 5);
 x_3467 = x_3459;
} else {
 lean_dec_ref(x_3459);
 x_3467 = lean_box(0);
}
x_3468 = l_Lean_MetavarContext_assignExpr(x_3462, x_2793, x_3460);
if (lean_is_scalar(x_3467)) {
 x_3469 = lean_alloc_ctor(0, 6, 0);
} else {
 x_3469 = x_3467;
}
lean_ctor_set(x_3469, 0, x_3461);
lean_ctor_set(x_3469, 1, x_3468);
lean_ctor_set(x_3469, 2, x_3463);
lean_ctor_set(x_3469, 3, x_3464);
lean_ctor_set(x_3469, 4, x_3465);
lean_ctor_set(x_3469, 5, x_3466);
x_3470 = l_Lean_Expr_mvarId_x21(x_3456);
lean_dec(x_3456);
x_3471 = l_Lean_Meta_clear(x_3470, x_2797, x_2807, x_3469);
if (lean_obj_tag(x_3471) == 0)
{
lean_object* x_3472; lean_object* x_3473; lean_object* x_3474; 
x_3472 = lean_ctor_get(x_3471, 0);
lean_inc(x_3472);
x_3473 = lean_ctor_get(x_3471, 1);
lean_inc(x_3473);
lean_dec(x_3471);
x_3474 = l_Lean_Meta_clear(x_3472, x_2795, x_2807, x_3473);
if (lean_obj_tag(x_3474) == 0)
{
lean_object* x_3475; lean_object* x_3476; lean_object* x_3477; lean_object* x_3478; lean_object* x_3479; 
x_3475 = lean_ctor_get(x_3474, 0);
lean_inc(x_3475);
x_3476 = lean_ctor_get(x_3474, 1);
lean_inc(x_3476);
lean_dec(x_3474);
x_3477 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_3478 = lean_nat_sub(x_3477, x_2755);
lean_dec(x_3477);
x_3479 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_3475, x_3478, x_2786, x_2807, x_3476);
lean_dec(x_2807);
if (lean_obj_tag(x_3479) == 0)
{
lean_object* x_3480; lean_object* x_3481; lean_object* x_3482; lean_object* x_3483; lean_object* x_3484; lean_object* x_3485; 
lean_dec(x_2791);
x_3480 = lean_ctor_get(x_3479, 0);
lean_inc(x_3480);
x_3481 = lean_ctor_get(x_3479, 1);
lean_inc(x_3481);
lean_dec(x_3479);
x_3482 = lean_ctor_get(x_3480, 1);
lean_inc(x_3482);
if (lean_is_exclusive(x_3480)) {
 lean_ctor_release(x_3480, 0);
 lean_ctor_release(x_3480, 1);
 x_3483 = x_3480;
} else {
 lean_dec_ref(x_3480);
 x_3483 = lean_box(0);
}
x_3484 = lean_box(0);
if (lean_is_scalar(x_3483)) {
 x_3485 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3485 = x_3483;
}
lean_ctor_set(x_3485, 0, x_3484);
lean_ctor_set(x_3485, 1, x_3482);
x_3399 = x_3485;
x_3400 = x_3481;
goto block_3414;
}
else
{
lean_object* x_3486; lean_object* x_3487; 
lean_dec(x_2802);
x_3486 = lean_ctor_get(x_3479, 0);
lean_inc(x_3486);
x_3487 = lean_ctor_get(x_3479, 1);
lean_inc(x_3487);
lean_dec(x_3479);
x_3415 = x_3486;
x_3416 = x_3487;
goto block_3430;
}
}
else
{
lean_object* x_3488; lean_object* x_3489; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2784);
x_3488 = lean_ctor_get(x_3474, 0);
lean_inc(x_3488);
x_3489 = lean_ctor_get(x_3474, 1);
lean_inc(x_3489);
lean_dec(x_3474);
x_3415 = x_3488;
x_3416 = x_3489;
goto block_3430;
}
}
else
{
lean_object* x_3490; lean_object* x_3491; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2795);
lean_dec(x_2784);
x_3490 = lean_ctor_get(x_3471, 0);
lean_inc(x_3490);
x_3491 = lean_ctor_get(x_3471, 1);
lean_inc(x_3491);
lean_dec(x_3471);
x_3415 = x_3490;
x_3416 = x_3491;
goto block_3430;
}
}
else
{
lean_object* x_3492; lean_object* x_3493; 
lean_dec(x_3456);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
x_3492 = lean_ctor_get(x_3458, 0);
lean_inc(x_3492);
x_3493 = lean_ctor_get(x_3458, 1);
lean_inc(x_3493);
lean_dec(x_3458);
x_3415 = x_3492;
x_3416 = x_3493;
goto block_3430;
}
}
}
else
{
lean_object* x_3500; lean_object* x_3501; 
lean_dec(x_3446);
lean_dec(x_3441);
lean_dec(x_3437);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3500 = lean_ctor_get(x_3447, 0);
lean_inc(x_3500);
x_3501 = lean_ctor_get(x_3447, 1);
lean_inc(x_3501);
lean_dec(x_3447);
x_3415 = x_3500;
x_3416 = x_3501;
goto block_3430;
}
}
else
{
lean_object* x_3502; lean_object* x_3503; lean_object* x_3504; lean_object* x_3505; lean_object* x_3506; 
x_3502 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2796);
x_3503 = lean_array_push(x_3502, x_2796);
x_3504 = lean_expr_abstract(x_3437, x_3503);
lean_dec(x_3503);
x_3505 = lean_expr_instantiate1(x_3504, x_3441);
lean_dec(x_3504);
lean_inc(x_2807);
lean_inc(x_3441);
x_3506 = l_Lean_Meta_mkEqRefl(x_3441, x_2807, x_3440);
if (lean_obj_tag(x_3506) == 0)
{
lean_object* x_3507; lean_object* x_3508; lean_object* x_3509; lean_object* x_3510; lean_object* x_3511; 
x_3507 = lean_ctor_get(x_3506, 0);
lean_inc(x_3507);
x_3508 = lean_ctor_get(x_3506, 1);
lean_inc(x_3508);
lean_dec(x_3506);
lean_inc(x_2798);
x_3509 = lean_array_push(x_3502, x_2798);
x_3510 = lean_expr_abstract(x_3505, x_3509);
lean_dec(x_3505);
x_3511 = lean_expr_instantiate1(x_3510, x_3507);
lean_dec(x_3507);
lean_dec(x_3510);
if (x_2759 == 0)
{
lean_object* x_3512; 
lean_inc(x_2807);
lean_inc(x_2796);
x_3512 = l_Lean_Meta_mkEq(x_3441, x_2796, x_2807, x_3508);
if (lean_obj_tag(x_3512) == 0)
{
lean_object* x_3513; lean_object* x_3514; lean_object* x_3515; lean_object* x_3516; uint8_t x_3517; lean_object* x_3518; 
x_3513 = lean_ctor_get(x_3512, 0);
lean_inc(x_3513);
x_3514 = lean_ctor_get(x_3512, 1);
lean_inc(x_3514);
lean_dec(x_3512);
x_3515 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__1___boxed), 7, 4);
lean_closure_set(x_3515, 0, x_3437);
lean_closure_set(x_3515, 1, x_3509);
lean_closure_set(x_3515, 2, x_2777);
lean_closure_set(x_3515, 3, x_2796);
x_3516 = l_Lean_Meta_substCore___closed__18;
x_3517 = 0;
lean_inc(x_2807);
x_3518 = l_Lean_Meta_withLocalDecl___rarg(x_3516, x_3513, x_3517, x_3515, x_2807, x_3514);
if (lean_obj_tag(x_3518) == 0)
{
lean_object* x_3519; lean_object* x_3520; lean_object* x_3521; 
x_3519 = lean_ctor_get(x_3518, 0);
lean_inc(x_3519);
x_3520 = lean_ctor_get(x_3518, 1);
lean_inc(x_3520);
lean_dec(x_3518);
lean_inc(x_2807);
x_3521 = l_Lean_Meta_mkEqSymm(x_2798, x_2807, x_3520);
if (lean_obj_tag(x_3521) == 0)
{
lean_object* x_3522; lean_object* x_3523; uint8_t x_3524; lean_object* x_3525; lean_object* x_3526; lean_object* x_3527; lean_object* x_3528; 
x_3522 = lean_ctor_get(x_3521, 0);
lean_inc(x_3522);
x_3523 = lean_ctor_get(x_3521, 1);
lean_inc(x_3523);
lean_dec(x_3521);
x_3524 = 2;
lean_inc(x_2807);
x_3525 = l_Lean_Meta_mkFreshExprMVar(x_3511, x_2736, x_3524, x_2807, x_3523);
x_3526 = lean_ctor_get(x_3525, 0);
lean_inc(x_3526);
x_3527 = lean_ctor_get(x_3525, 1);
lean_inc(x_3527);
lean_dec(x_3525);
lean_inc(x_2807);
lean_inc(x_3526);
x_3528 = l_Lean_Meta_mkEqRec(x_3519, x_3526, x_3522, x_2807, x_3527);
if (lean_obj_tag(x_3528) == 0)
{
lean_object* x_3529; lean_object* x_3530; lean_object* x_3531; lean_object* x_3532; lean_object* x_3533; lean_object* x_3534; lean_object* x_3535; lean_object* x_3536; lean_object* x_3537; lean_object* x_3538; lean_object* x_3539; lean_object* x_3540; lean_object* x_3541; 
x_3529 = lean_ctor_get(x_3528, 1);
lean_inc(x_3529);
x_3530 = lean_ctor_get(x_3528, 0);
lean_inc(x_3530);
lean_dec(x_3528);
x_3531 = lean_ctor_get(x_3529, 0);
lean_inc(x_3531);
x_3532 = lean_ctor_get(x_3529, 1);
lean_inc(x_3532);
x_3533 = lean_ctor_get(x_3529, 2);
lean_inc(x_3533);
x_3534 = lean_ctor_get(x_3529, 3);
lean_inc(x_3534);
x_3535 = lean_ctor_get(x_3529, 4);
lean_inc(x_3535);
x_3536 = lean_ctor_get(x_3529, 5);
lean_inc(x_3536);
if (lean_is_exclusive(x_3529)) {
 lean_ctor_release(x_3529, 0);
 lean_ctor_release(x_3529, 1);
 lean_ctor_release(x_3529, 2);
 lean_ctor_release(x_3529, 3);
 lean_ctor_release(x_3529, 4);
 lean_ctor_release(x_3529, 5);
 x_3537 = x_3529;
} else {
 lean_dec_ref(x_3529);
 x_3537 = lean_box(0);
}
x_3538 = l_Lean_MetavarContext_assignExpr(x_3532, x_2793, x_3530);
if (lean_is_scalar(x_3537)) {
 x_3539 = lean_alloc_ctor(0, 6, 0);
} else {
 x_3539 = x_3537;
}
lean_ctor_set(x_3539, 0, x_3531);
lean_ctor_set(x_3539, 1, x_3538);
lean_ctor_set(x_3539, 2, x_3533);
lean_ctor_set(x_3539, 3, x_3534);
lean_ctor_set(x_3539, 4, x_3535);
lean_ctor_set(x_3539, 5, x_3536);
x_3540 = l_Lean_Expr_mvarId_x21(x_3526);
lean_dec(x_3526);
x_3541 = l_Lean_Meta_clear(x_3540, x_2797, x_2807, x_3539);
if (lean_obj_tag(x_3541) == 0)
{
lean_object* x_3542; lean_object* x_3543; lean_object* x_3544; 
x_3542 = lean_ctor_get(x_3541, 0);
lean_inc(x_3542);
x_3543 = lean_ctor_get(x_3541, 1);
lean_inc(x_3543);
lean_dec(x_3541);
x_3544 = l_Lean_Meta_clear(x_3542, x_2795, x_2807, x_3543);
if (lean_obj_tag(x_3544) == 0)
{
lean_object* x_3545; lean_object* x_3546; lean_object* x_3547; lean_object* x_3548; lean_object* x_3549; 
x_3545 = lean_ctor_get(x_3544, 0);
lean_inc(x_3545);
x_3546 = lean_ctor_get(x_3544, 1);
lean_inc(x_3546);
lean_dec(x_3544);
x_3547 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_3548 = lean_nat_sub(x_3547, x_2755);
lean_dec(x_3547);
x_3549 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_3545, x_3548, x_2786, x_2807, x_3546);
lean_dec(x_2807);
if (lean_obj_tag(x_3549) == 0)
{
lean_object* x_3550; lean_object* x_3551; lean_object* x_3552; lean_object* x_3553; lean_object* x_3554; lean_object* x_3555; 
lean_dec(x_2791);
x_3550 = lean_ctor_get(x_3549, 0);
lean_inc(x_3550);
x_3551 = lean_ctor_get(x_3549, 1);
lean_inc(x_3551);
lean_dec(x_3549);
x_3552 = lean_ctor_get(x_3550, 1);
lean_inc(x_3552);
if (lean_is_exclusive(x_3550)) {
 lean_ctor_release(x_3550, 0);
 lean_ctor_release(x_3550, 1);
 x_3553 = x_3550;
} else {
 lean_dec_ref(x_3550);
 x_3553 = lean_box(0);
}
x_3554 = lean_box(0);
if (lean_is_scalar(x_3553)) {
 x_3555 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3555 = x_3553;
}
lean_ctor_set(x_3555, 0, x_3554);
lean_ctor_set(x_3555, 1, x_3552);
x_3399 = x_3555;
x_3400 = x_3551;
goto block_3414;
}
else
{
lean_object* x_3556; lean_object* x_3557; 
lean_dec(x_2802);
x_3556 = lean_ctor_get(x_3549, 0);
lean_inc(x_3556);
x_3557 = lean_ctor_get(x_3549, 1);
lean_inc(x_3557);
lean_dec(x_3549);
x_3415 = x_3556;
x_3416 = x_3557;
goto block_3430;
}
}
else
{
lean_object* x_3558; lean_object* x_3559; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2784);
x_3558 = lean_ctor_get(x_3544, 0);
lean_inc(x_3558);
x_3559 = lean_ctor_get(x_3544, 1);
lean_inc(x_3559);
lean_dec(x_3544);
x_3415 = x_3558;
x_3416 = x_3559;
goto block_3430;
}
}
else
{
lean_object* x_3560; lean_object* x_3561; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2795);
lean_dec(x_2784);
x_3560 = lean_ctor_get(x_3541, 0);
lean_inc(x_3560);
x_3561 = lean_ctor_get(x_3541, 1);
lean_inc(x_3561);
lean_dec(x_3541);
x_3415 = x_3560;
x_3416 = x_3561;
goto block_3430;
}
}
else
{
lean_object* x_3562; lean_object* x_3563; 
lean_dec(x_3526);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
x_3562 = lean_ctor_get(x_3528, 0);
lean_inc(x_3562);
x_3563 = lean_ctor_get(x_3528, 1);
lean_inc(x_3563);
lean_dec(x_3528);
x_3415 = x_3562;
x_3416 = x_3563;
goto block_3430;
}
}
else
{
lean_object* x_3564; lean_object* x_3565; 
lean_dec(x_3519);
lean_dec(x_3511);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3564 = lean_ctor_get(x_3521, 0);
lean_inc(x_3564);
x_3565 = lean_ctor_get(x_3521, 1);
lean_inc(x_3565);
lean_dec(x_3521);
x_3415 = x_3564;
x_3416 = x_3565;
goto block_3430;
}
}
else
{
lean_object* x_3566; lean_object* x_3567; 
lean_dec(x_3511);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3566 = lean_ctor_get(x_3518, 0);
lean_inc(x_3566);
x_3567 = lean_ctor_get(x_3518, 1);
lean_inc(x_3567);
lean_dec(x_3518);
x_3415 = x_3566;
x_3416 = x_3567;
goto block_3430;
}
}
else
{
lean_object* x_3568; lean_object* x_3569; 
lean_dec(x_3511);
lean_dec(x_3509);
lean_dec(x_3437);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3568 = lean_ctor_get(x_3512, 0);
lean_inc(x_3568);
x_3569 = lean_ctor_get(x_3512, 1);
lean_inc(x_3569);
lean_dec(x_3512);
x_3415 = x_3568;
x_3416 = x_3569;
goto block_3430;
}
}
else
{
lean_object* x_3570; lean_object* x_3571; lean_object* x_3572; 
lean_dec(x_3509);
lean_dec(x_3441);
x_3570 = lean_array_push(x_2777, x_2796);
lean_inc(x_2798);
x_3571 = lean_array_push(x_3570, x_2798);
lean_inc(x_2807);
x_3572 = l_Lean_Meta_mkLambda(x_3571, x_3437, x_2807, x_3508);
if (lean_obj_tag(x_3572) == 0)
{
lean_object* x_3573; lean_object* x_3574; uint8_t x_3575; lean_object* x_3576; lean_object* x_3577; lean_object* x_3578; lean_object* x_3579; 
x_3573 = lean_ctor_get(x_3572, 0);
lean_inc(x_3573);
x_3574 = lean_ctor_get(x_3572, 1);
lean_inc(x_3574);
lean_dec(x_3572);
x_3575 = 2;
lean_inc(x_2807);
x_3576 = l_Lean_Meta_mkFreshExprMVar(x_3511, x_2736, x_3575, x_2807, x_3574);
x_3577 = lean_ctor_get(x_3576, 0);
lean_inc(x_3577);
x_3578 = lean_ctor_get(x_3576, 1);
lean_inc(x_3578);
lean_dec(x_3576);
lean_inc(x_2807);
lean_inc(x_3577);
x_3579 = l_Lean_Meta_mkEqRec(x_3573, x_3577, x_2798, x_2807, x_3578);
if (lean_obj_tag(x_3579) == 0)
{
lean_object* x_3580; lean_object* x_3581; lean_object* x_3582; lean_object* x_3583; lean_object* x_3584; lean_object* x_3585; lean_object* x_3586; lean_object* x_3587; lean_object* x_3588; lean_object* x_3589; lean_object* x_3590; lean_object* x_3591; lean_object* x_3592; 
x_3580 = lean_ctor_get(x_3579, 1);
lean_inc(x_3580);
x_3581 = lean_ctor_get(x_3579, 0);
lean_inc(x_3581);
lean_dec(x_3579);
x_3582 = lean_ctor_get(x_3580, 0);
lean_inc(x_3582);
x_3583 = lean_ctor_get(x_3580, 1);
lean_inc(x_3583);
x_3584 = lean_ctor_get(x_3580, 2);
lean_inc(x_3584);
x_3585 = lean_ctor_get(x_3580, 3);
lean_inc(x_3585);
x_3586 = lean_ctor_get(x_3580, 4);
lean_inc(x_3586);
x_3587 = lean_ctor_get(x_3580, 5);
lean_inc(x_3587);
if (lean_is_exclusive(x_3580)) {
 lean_ctor_release(x_3580, 0);
 lean_ctor_release(x_3580, 1);
 lean_ctor_release(x_3580, 2);
 lean_ctor_release(x_3580, 3);
 lean_ctor_release(x_3580, 4);
 lean_ctor_release(x_3580, 5);
 x_3588 = x_3580;
} else {
 lean_dec_ref(x_3580);
 x_3588 = lean_box(0);
}
x_3589 = l_Lean_MetavarContext_assignExpr(x_3583, x_2793, x_3581);
if (lean_is_scalar(x_3588)) {
 x_3590 = lean_alloc_ctor(0, 6, 0);
} else {
 x_3590 = x_3588;
}
lean_ctor_set(x_3590, 0, x_3582);
lean_ctor_set(x_3590, 1, x_3589);
lean_ctor_set(x_3590, 2, x_3584);
lean_ctor_set(x_3590, 3, x_3585);
lean_ctor_set(x_3590, 4, x_3586);
lean_ctor_set(x_3590, 5, x_3587);
x_3591 = l_Lean_Expr_mvarId_x21(x_3577);
lean_dec(x_3577);
x_3592 = l_Lean_Meta_clear(x_3591, x_2797, x_2807, x_3590);
if (lean_obj_tag(x_3592) == 0)
{
lean_object* x_3593; lean_object* x_3594; lean_object* x_3595; 
x_3593 = lean_ctor_get(x_3592, 0);
lean_inc(x_3593);
x_3594 = lean_ctor_get(x_3592, 1);
lean_inc(x_3594);
lean_dec(x_3592);
x_3595 = l_Lean_Meta_clear(x_3593, x_2795, x_2807, x_3594);
if (lean_obj_tag(x_3595) == 0)
{
lean_object* x_3596; lean_object* x_3597; lean_object* x_3598; lean_object* x_3599; lean_object* x_3600; 
x_3596 = lean_ctor_get(x_3595, 0);
lean_inc(x_3596);
x_3597 = lean_ctor_get(x_3595, 1);
lean_inc(x_3597);
lean_dec(x_3595);
x_3598 = lean_array_get_size(x_2784);
lean_dec(x_2784);
x_3599 = lean_nat_sub(x_3598, x_2755);
lean_dec(x_3598);
x_3600 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2787, x_3596, x_3599, x_2786, x_2807, x_3597);
lean_dec(x_2807);
if (lean_obj_tag(x_3600) == 0)
{
lean_object* x_3601; lean_object* x_3602; lean_object* x_3603; lean_object* x_3604; lean_object* x_3605; lean_object* x_3606; 
lean_dec(x_2791);
x_3601 = lean_ctor_get(x_3600, 0);
lean_inc(x_3601);
x_3602 = lean_ctor_get(x_3600, 1);
lean_inc(x_3602);
lean_dec(x_3600);
x_3603 = lean_ctor_get(x_3601, 1);
lean_inc(x_3603);
if (lean_is_exclusive(x_3601)) {
 lean_ctor_release(x_3601, 0);
 lean_ctor_release(x_3601, 1);
 x_3604 = x_3601;
} else {
 lean_dec_ref(x_3601);
 x_3604 = lean_box(0);
}
x_3605 = lean_box(0);
if (lean_is_scalar(x_3604)) {
 x_3606 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3606 = x_3604;
}
lean_ctor_set(x_3606, 0, x_3605);
lean_ctor_set(x_3606, 1, x_3603);
x_3399 = x_3606;
x_3400 = x_3602;
goto block_3414;
}
else
{
lean_object* x_3607; lean_object* x_3608; 
lean_dec(x_2802);
x_3607 = lean_ctor_get(x_3600, 0);
lean_inc(x_3607);
x_3608 = lean_ctor_get(x_3600, 1);
lean_inc(x_3608);
lean_dec(x_3600);
x_3415 = x_3607;
x_3416 = x_3608;
goto block_3430;
}
}
else
{
lean_object* x_3609; lean_object* x_3610; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2784);
x_3609 = lean_ctor_get(x_3595, 0);
lean_inc(x_3609);
x_3610 = lean_ctor_get(x_3595, 1);
lean_inc(x_3610);
lean_dec(x_3595);
x_3415 = x_3609;
x_3416 = x_3610;
goto block_3430;
}
}
else
{
lean_object* x_3611; lean_object* x_3612; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2795);
lean_dec(x_2784);
x_3611 = lean_ctor_get(x_3592, 0);
lean_inc(x_3611);
x_3612 = lean_ctor_get(x_3592, 1);
lean_inc(x_3612);
lean_dec(x_3592);
x_3415 = x_3611;
x_3416 = x_3612;
goto block_3430;
}
}
else
{
lean_object* x_3613; lean_object* x_3614; 
lean_dec(x_3577);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
x_3613 = lean_ctor_get(x_3579, 0);
lean_inc(x_3613);
x_3614 = lean_ctor_get(x_3579, 1);
lean_inc(x_3614);
lean_dec(x_3579);
x_3415 = x_3613;
x_3416 = x_3614;
goto block_3430;
}
}
else
{
lean_object* x_3615; lean_object* x_3616; 
lean_dec(x_3511);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3615 = lean_ctor_get(x_3572, 0);
lean_inc(x_3615);
x_3616 = lean_ctor_get(x_3572, 1);
lean_inc(x_3616);
lean_dec(x_3572);
x_3415 = x_3615;
x_3416 = x_3616;
goto block_3430;
}
}
}
else
{
lean_object* x_3617; lean_object* x_3618; 
lean_dec(x_3505);
lean_dec(x_3441);
lean_dec(x_3437);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3617 = lean_ctor_get(x_3506, 0);
lean_inc(x_3617);
x_3618 = lean_ctor_get(x_3506, 1);
lean_inc(x_3618);
lean_dec(x_3506);
x_3415 = x_3617;
x_3416 = x_3618;
goto block_3430;
}
}
}
}
else
{
lean_object* x_3636; lean_object* x_3637; 
lean_dec(x_3437);
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3636 = lean_ctor_get(x_3438, 0);
lean_inc(x_3636);
x_3637 = lean_ctor_get(x_3438, 1);
lean_inc(x_3637);
lean_dec(x_3438);
x_3415 = x_3636;
x_3416 = x_3637;
goto block_3430;
}
}
else
{
lean_object* x_3638; lean_object* x_3639; 
lean_dec(x_2807);
lean_dec(x_2802);
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2784);
lean_dec(x_2736);
x_3638 = lean_ctor_get(x_3434, 0);
lean_inc(x_3638);
x_3639 = lean_ctor_get(x_3434, 1);
lean_inc(x_3639);
lean_dec(x_3434);
x_3415 = x_3638;
x_3416 = x_3639;
goto block_3430;
}
block_3414:
{
lean_object* x_3401; lean_object* x_3402; lean_object* x_3403; lean_object* x_3404; lean_object* x_3405; lean_object* x_3406; lean_object* x_3407; lean_object* x_3408; lean_object* x_3409; lean_object* x_3410; lean_object* x_3411; lean_object* x_3412; lean_object* x_3413; 
x_3401 = lean_ctor_get(x_3400, 2);
lean_inc(x_3401);
x_3402 = lean_ctor_get(x_3400, 0);
lean_inc(x_3402);
x_3403 = lean_ctor_get(x_3400, 1);
lean_inc(x_3403);
x_3404 = lean_ctor_get(x_3400, 3);
lean_inc(x_3404);
x_3405 = lean_ctor_get(x_3400, 4);
lean_inc(x_3405);
x_3406 = lean_ctor_get(x_3400, 5);
lean_inc(x_3406);
if (lean_is_exclusive(x_3400)) {
 lean_ctor_release(x_3400, 0);
 lean_ctor_release(x_3400, 1);
 lean_ctor_release(x_3400, 2);
 lean_ctor_release(x_3400, 3);
 lean_ctor_release(x_3400, 4);
 lean_ctor_release(x_3400, 5);
 x_3407 = x_3400;
} else {
 lean_dec_ref(x_3400);
 x_3407 = lean_box(0);
}
x_3408 = lean_ctor_get(x_3401, 0);
lean_inc(x_3408);
x_3409 = lean_ctor_get(x_3401, 1);
lean_inc(x_3409);
if (lean_is_exclusive(x_3401)) {
 lean_ctor_release(x_3401, 0);
 lean_ctor_release(x_3401, 1);
 lean_ctor_release(x_3401, 2);
 x_3410 = x_3401;
} else {
 lean_dec_ref(x_3401);
 x_3410 = lean_box(0);
}
if (lean_is_scalar(x_3410)) {
 x_3411 = lean_alloc_ctor(0, 3, 0);
} else {
 x_3411 = x_3410;
}
lean_ctor_set(x_3411, 0, x_3408);
lean_ctor_set(x_3411, 1, x_3409);
lean_ctor_set(x_3411, 2, x_3397);
if (lean_is_scalar(x_3407)) {
 x_3412 = lean_alloc_ctor(0, 6, 0);
} else {
 x_3412 = x_3407;
}
lean_ctor_set(x_3412, 0, x_3402);
lean_ctor_set(x_3412, 1, x_3403);
lean_ctor_set(x_3412, 2, x_3411);
lean_ctor_set(x_3412, 3, x_3404);
lean_ctor_set(x_3412, 4, x_3405);
lean_ctor_set(x_3412, 5, x_3406);
if (lean_is_scalar(x_2802)) {
 x_3413 = lean_alloc_ctor(0, 2, 0);
} else {
 x_3413 = x_2802;
}
lean_ctor_set(x_3413, 0, x_3399);
lean_ctor_set(x_3413, 1, x_3412);
return x_3413;
}
block_3430:
{
lean_object* x_3417; lean_object* x_3418; lean_object* x_3419; lean_object* x_3420; lean_object* x_3421; lean_object* x_3422; lean_object* x_3423; lean_object* x_3424; lean_object* x_3425; lean_object* x_3426; lean_object* x_3427; lean_object* x_3428; lean_object* x_3429; 
x_3417 = lean_ctor_get(x_3416, 2);
lean_inc(x_3417);
x_3418 = lean_ctor_get(x_3416, 0);
lean_inc(x_3418);
x_3419 = lean_ctor_get(x_3416, 1);
lean_inc(x_3419);
x_3420 = lean_ctor_get(x_3416, 3);
lean_inc(x_3420);
x_3421 = lean_ctor_get(x_3416, 4);
lean_inc(x_3421);
x_3422 = lean_ctor_get(x_3416, 5);
lean_inc(x_3422);
if (lean_is_exclusive(x_3416)) {
 lean_ctor_release(x_3416, 0);
 lean_ctor_release(x_3416, 1);
 lean_ctor_release(x_3416, 2);
 lean_ctor_release(x_3416, 3);
 lean_ctor_release(x_3416, 4);
 lean_ctor_release(x_3416, 5);
 x_3423 = x_3416;
} else {
 lean_dec_ref(x_3416);
 x_3423 = lean_box(0);
}
x_3424 = lean_ctor_get(x_3417, 0);
lean_inc(x_3424);
x_3425 = lean_ctor_get(x_3417, 1);
lean_inc(x_3425);
if (lean_is_exclusive(x_3417)) {
 lean_ctor_release(x_3417, 0);
 lean_ctor_release(x_3417, 1);
 lean_ctor_release(x_3417, 2);
 x_3426 = x_3417;
} else {
 lean_dec_ref(x_3417);
 x_3426 = lean_box(0);
}
if (lean_is_scalar(x_3426)) {
 x_3427 = lean_alloc_ctor(0, 3, 0);
} else {
 x_3427 = x_3426;
}
lean_ctor_set(x_3427, 0, x_3424);
lean_ctor_set(x_3427, 1, x_3425);
lean_ctor_set(x_3427, 2, x_3397);
if (lean_is_scalar(x_3423)) {
 x_3428 = lean_alloc_ctor(0, 6, 0);
} else {
 x_3428 = x_3423;
}
lean_ctor_set(x_3428, 0, x_3418);
lean_ctor_set(x_3428, 1, x_3419);
lean_ctor_set(x_3428, 2, x_3427);
lean_ctor_set(x_3428, 3, x_3420);
lean_ctor_set(x_3428, 4, x_3421);
lean_ctor_set(x_3428, 5, x_3422);
if (lean_is_scalar(x_2791)) {
 x_3429 = lean_alloc_ctor(1, 2, 0);
} else {
 x_3429 = x_2791;
 lean_ctor_set_tag(x_3429, 1);
}
lean_ctor_set(x_3429, 0, x_3415);
lean_ctor_set(x_3429, 1, x_3428);
return x_3429;
}
}
}
}
else
{
uint8_t x_4011; 
lean_dec(x_2798);
lean_dec(x_2797);
lean_dec(x_2796);
lean_dec(x_2795);
lean_dec(x_2793);
lean_dec(x_2791);
lean_dec(x_2784);
lean_dec(x_2736);
lean_dec(x_2733);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
x_4011 = !lean_is_exclusive(x_2799);
if (x_4011 == 0)
{
return x_2799;
}
else
{
lean_object* x_4012; lean_object* x_4013; lean_object* x_4014; 
x_4012 = lean_ctor_get(x_2799, 0);
x_4013 = lean_ctor_get(x_2799, 1);
lean_inc(x_4013);
lean_inc(x_4012);
lean_dec(x_2799);
x_4014 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4014, 0, x_4012);
lean_ctor_set(x_4014, 1, x_4013);
return x_4014;
}
}
}
else
{
uint8_t x_4015; 
lean_dec(x_2784);
lean_dec(x_2736);
lean_dec(x_2733);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
x_4015 = !lean_is_exclusive(x_2788);
if (x_4015 == 0)
{
return x_2788;
}
else
{
lean_object* x_4016; lean_object* x_4017; lean_object* x_4018; 
x_4016 = lean_ctor_get(x_2788, 0);
x_4017 = lean_ctor_get(x_2788, 1);
lean_inc(x_4017);
lean_inc(x_4016);
lean_dec(x_2788);
x_4018 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4018, 0, x_4016);
lean_ctor_set(x_4018, 1, x_4017);
return x_4018;
}
}
}
else
{
uint8_t x_4019; 
lean_dec(x_2736);
lean_dec(x_2733);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
x_4019 = !lean_is_exclusive(x_2781);
if (x_4019 == 0)
{
return x_2781;
}
else
{
lean_object* x_4020; lean_object* x_4021; lean_object* x_4022; 
x_4020 = lean_ctor_get(x_2781, 0);
x_4021 = lean_ctor_get(x_2781, 1);
lean_inc(x_4021);
lean_inc(x_4020);
lean_dec(x_2781);
x_4022 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4022, 0, x_4020);
lean_ctor_set(x_4022, 1, x_4021);
return x_4022;
}
}
}
else
{
uint8_t x_4023; 
lean_dec(x_2772);
lean_dec(x_2736);
lean_dec(x_2733);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_4023 = !lean_is_exclusive(x_2775);
if (x_4023 == 0)
{
return x_2775;
}
else
{
lean_object* x_4024; lean_object* x_4025; lean_object* x_4026; 
x_4024 = lean_ctor_get(x_2775, 0);
x_4025 = lean_ctor_get(x_2775, 1);
lean_inc(x_4025);
lean_inc(x_4024);
lean_dec(x_2775);
x_4026 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4026, 0, x_4024);
lean_ctor_set(x_4026, 1, x_4025);
return x_4026;
}
}
}
}
else
{
lean_object* x_4043; 
lean_dec(x_2771);
lean_dec(x_2770);
lean_dec(x_2736);
lean_dec(x_2733);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
x_4043 = lean_box(0);
x_2760 = x_4043;
goto block_2769;
}
}
}
}
}
}
else
{
uint8_t x_4049; 
lean_dec(x_2736);
lean_dec(x_2733);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_4049 = !lean_is_exclusive(x_2741);
if (x_4049 == 0)
{
return x_2741;
}
else
{
lean_object* x_4050; lean_object* x_4051; lean_object* x_4052; 
x_4050 = lean_ctor_get(x_2741, 0);
x_4051 = lean_ctor_get(x_2741, 1);
lean_inc(x_4051);
lean_inc(x_4050);
lean_dec(x_2741);
x_4052 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4052, 0, x_4050);
lean_ctor_set(x_4052, 1, x_4051);
return x_4052;
}
}
}
else
{
uint8_t x_4053; 
lean_dec(x_2736);
lean_dec(x_2733);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_4053 = !lean_is_exclusive(x_2739);
if (x_4053 == 0)
{
return x_2739;
}
else
{
lean_object* x_4054; lean_object* x_4055; lean_object* x_4056; 
x_4054 = lean_ctor_get(x_2739, 0);
x_4055 = lean_ctor_get(x_2739, 1);
lean_inc(x_4055);
lean_inc(x_4054);
lean_dec(x_2739);
x_4056 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4056, 0, x_4054);
lean_ctor_set(x_4056, 1, x_4055);
return x_4056;
}
}
}
else
{
uint8_t x_4057; 
lean_dec(x_2733);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_4057 = !lean_is_exclusive(x_2735);
if (x_4057 == 0)
{
return x_2735;
}
else
{
lean_object* x_4058; lean_object* x_4059; lean_object* x_4060; 
x_4058 = lean_ctor_get(x_2735, 0);
x_4059 = lean_ctor_get(x_2735, 1);
lean_inc(x_4059);
lean_inc(x_4058);
lean_dec(x_2735);
x_4060 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4060, 0, x_4058);
lean_ctor_set(x_4060, 1, x_4059);
return x_4060;
}
}
}
}
block_2729:
{
uint8_t x_22; 
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_9, 2);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_50; lean_object* x_51; lean_object* x_74; lean_object* x_80; lean_object* x_81; 
x_25 = lean_ctor_get(x_23, 2);
x_80 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_23, 2, x_80);
lean_inc(x_1);
x_81 = l_Lean_Meta_getMVarTag(x_1, x_20, x_9);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Meta_substCore___closed__2;
lean_inc(x_1);
x_85 = l_Lean_Meta_checkNotAssigned(x_1, x_84, x_20, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
lean_inc(x_20);
lean_inc(x_2);
x_87 = l_Lean_Meta_getLocalDecl(x_2, x_20, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_LocalDecl_type(x_88);
lean_dec(x_88);
x_91 = l_Lean_Expr_eq_x3f___closed__2;
x_92 = lean_unsigned_to_nat(3u);
x_93 = l_Lean_Expr_isAppOfArity___main(x_90, x_91, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_90);
lean_dec(x_82);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_94 = l_Lean_Meta_substCore___closed__5;
x_95 = l_Lean_Meta_throwTacticEx___rarg(x_84, x_1, x_94, x_20, x_89);
lean_dec(x_20);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_50 = x_96;
x_51 = x_97;
goto block_73;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_98 = lean_unsigned_to_nat(0u);
x_99 = l_Lean_Expr_getAppNumArgsAux___main(x_90, x_98);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_sub(x_99, x_100);
x_102 = lean_nat_sub(x_101, x_100);
lean_dec(x_101);
x_103 = l_Lean_Expr_getRevArg_x21___main(x_90, x_102);
x_104 = lean_unsigned_to_nat(2u);
x_105 = lean_nat_sub(x_99, x_104);
lean_dec(x_99);
x_106 = lean_nat_sub(x_105, x_100);
lean_dec(x_105);
x_107 = l_Lean_Expr_getRevArg_x21___main(x_90, x_106);
if (x_3 == 0)
{
uint8_t x_1387; 
x_1387 = 0;
x_108 = x_1387;
goto block_1386;
}
else
{
uint8_t x_1388; 
x_1388 = 1;
x_108 = x_1388;
goto block_1386;
}
block_1386:
{
lean_object* x_109; lean_object* x_123; 
if (x_108 == 0)
{
lean_inc(x_103);
x_123 = x_103;
goto block_1385;
}
else
{
lean_inc(x_107);
x_123 = x_107;
goto block_1385;
}
block_122:
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_109);
x_110 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_110, 0, x_90);
x_111 = l_Lean_indentExpr(x_110);
if (x_108 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = l_Lean_Meta_substCore___closed__12;
x_113 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
x_114 = l_Lean_Meta_throwTacticEx___rarg(x_84, x_1, x_113, x_20, x_89);
lean_dec(x_20);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_50 = x_115;
x_51 = x_116;
goto block_73;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = l_Lean_Meta_substCore___closed__16;
x_118 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_111);
x_119 = l_Lean_Meta_throwTacticEx___rarg(x_84, x_1, x_118, x_20, x_89);
lean_dec(x_20);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_50 = x_120;
x_51 = x_121;
goto block_73;
}
}
block_1385:
{
lean_object* x_124; 
if (x_108 == 0)
{
lean_dec(x_103);
x_124 = x_107;
goto block_1384;
}
else
{
lean_dec(x_107);
x_124 = x_103;
goto block_1384;
}
block_1384:
{
if (lean_obj_tag(x_123) == 1)
{
lean_object* x_125; lean_object* x_126; lean_object* x_1369; lean_object* x_1370; uint8_t x_1371; 
lean_dec(x_90);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
x_1369 = lean_ctor_get(x_89, 1);
lean_inc(x_1369);
lean_inc(x_124);
x_1370 = l_Lean_MetavarContext_exprDependsOn(x_1369, x_124, x_125);
x_1371 = lean_unbox(x_1370);
lean_dec(x_1370);
if (x_1371 == 0)
{
lean_dec(x_124);
lean_dec(x_123);
x_126 = x_89;
goto block_1368;
}
else
{
lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; 
lean_dec(x_125);
lean_dec(x_82);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_1372 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1372, 0, x_123);
x_1373 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_1374 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1374, 0, x_1373);
lean_ctor_set(x_1374, 1, x_1372);
x_1375 = l_Lean_Meta_substCore___closed__21;
x_1376 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1376, 0, x_1374);
lean_ctor_set(x_1376, 1, x_1375);
x_1377 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1377, 0, x_124);
x_1378 = l_Lean_indentExpr(x_1377);
x_1379 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1379, 0, x_1376);
lean_ctor_set(x_1379, 1, x_1378);
x_1380 = l_Lean_Meta_throwTacticEx___rarg(x_84, x_1, x_1379, x_20, x_89);
lean_dec(x_20);
x_1381 = lean_ctor_get(x_1380, 0);
lean_inc(x_1381);
x_1382 = lean_ctor_get(x_1380, 1);
lean_inc(x_1382);
lean_dec(x_1380);
x_50 = x_1381;
x_51 = x_1382;
goto block_73;
}
block_1368:
{
lean_object* x_127; 
lean_inc(x_20);
lean_inc(x_125);
x_127 = l_Lean_Meta_getLocalDecl(x_125, x_20, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = l_Lean_mkAppStx___closed__9;
x_130 = lean_array_push(x_129, x_125);
x_131 = lean_array_push(x_130, x_2);
x_132 = 1;
x_133 = l_Lean_Meta_revert(x_1, x_131, x_132, x_20, x_128);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_box(0);
x_139 = 0;
x_140 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_137, x_104, x_138, x_20, x_135);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_143 = x_140;
} else {
 lean_dec_ref(x_140);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_141, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
lean_dec(x_141);
x_146 = l_Lean_Name_inhabited;
x_147 = lean_array_get(x_146, x_144, x_98);
lean_inc(x_147);
x_148 = l_Lean_mkFVar(x_147);
x_149 = lean_array_get(x_146, x_144, x_100);
lean_dec(x_144);
lean_inc(x_149);
x_150 = l_Lean_mkFVar(x_149);
lean_inc(x_145);
x_151 = l_Lean_Meta_getMVarDecl(x_145, x_20, x_142);
lean_dec(x_20);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_154 = x_151;
} else {
 lean_dec_ref(x_151);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_152, 4);
lean_inc(x_156);
x_157 = lean_array_get_size(x_156);
x_158 = lean_nat_dec_eq(x_18, x_157);
lean_dec(x_157);
lean_dec(x_18);
lean_inc(x_156);
x_159 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_159, 0, x_11);
lean_ctor_set(x_159, 1, x_155);
lean_ctor_set(x_159, 2, x_156);
lean_ctor_set(x_159, 3, x_13);
lean_ctor_set(x_159, 4, x_14);
if (x_158 == 0)
{
lean_object* x_990; 
lean_dec(x_156);
lean_dec(x_152);
lean_dec(x_16);
lean_dec(x_8);
x_990 = lean_box(0);
x_160 = x_990;
goto block_989;
}
else
{
uint8_t x_991; 
x_991 = l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__1(x_8, x_152, lean_box(0), x_16, x_156, x_98);
lean_dec(x_156);
lean_dec(x_16);
lean_dec(x_152);
lean_dec(x_8);
if (x_991 == 0)
{
lean_object* x_992; 
x_992 = lean_box(0);
x_160 = x_992;
goto block_989;
}
else
{
lean_object* x_993; 
lean_dec(x_154);
lean_dec(x_143);
lean_inc(x_145);
x_993 = l_Lean_Meta_getMVarDecl(x_145, x_159, x_153);
if (lean_obj_tag(x_993) == 0)
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; 
x_994 = lean_ctor_get(x_993, 0);
lean_inc(x_994);
x_995 = lean_ctor_get(x_993, 1);
lean_inc(x_995);
lean_dec(x_993);
x_996 = lean_ctor_get(x_994, 2);
lean_inc(x_996);
lean_dec(x_994);
lean_inc(x_159);
lean_inc(x_149);
x_997 = l_Lean_Meta_getLocalDecl(x_149, x_159, x_995);
if (lean_obj_tag(x_997) == 0)
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1340; uint8_t x_1341; 
x_998 = lean_ctor_get(x_997, 0);
lean_inc(x_998);
x_999 = lean_ctor_get(x_997, 1);
lean_inc(x_999);
lean_dec(x_997);
x_1340 = l_Lean_LocalDecl_type(x_998);
lean_dec(x_998);
x_1341 = l_Lean_Expr_isAppOfArity___main(x_1340, x_91, x_92);
if (x_1341 == 0)
{
lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; 
lean_dec(x_1340);
lean_dec(x_996);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_1342 = l_Lean_Meta_isClassQuick___main___closed__1;
x_1343 = l_unreachable_x21___rarg(x_1342);
x_1344 = lean_apply_2(x_1343, x_159, x_999);
x_74 = x_1344;
goto block_79;
}
else
{
lean_object* x_1345; 
x_1345 = l_Lean_Expr_getAppNumArgsAux___main(x_1340, x_98);
if (x_108 == 0)
{
lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; 
x_1346 = lean_nat_sub(x_1345, x_104);
lean_dec(x_1345);
x_1347 = lean_nat_sub(x_1346, x_100);
lean_dec(x_1346);
x_1348 = l_Lean_Expr_getRevArg_x21___main(x_1340, x_1347);
lean_dec(x_1340);
x_1000 = x_1348;
goto block_1339;
}
else
{
lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; 
x_1349 = lean_nat_sub(x_1345, x_100);
lean_dec(x_1345);
x_1350 = lean_nat_sub(x_1349, x_100);
lean_dec(x_1349);
x_1351 = l_Lean_Expr_getRevArg_x21___main(x_1340, x_1350);
lean_dec(x_1340);
x_1000 = x_1351;
goto block_1339;
}
}
block_1339:
{
lean_object* x_1001; lean_object* x_1002; uint8_t x_1003; 
x_1001 = lean_ctor_get(x_999, 1);
lean_inc(x_1001);
lean_inc(x_996);
x_1002 = l_Lean_MetavarContext_exprDependsOn(x_1001, x_996, x_149);
x_1003 = lean_unbox(x_1002);
lean_dec(x_1002);
if (x_1003 == 0)
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
x_1004 = l_Lean_mkOptionalNode___closed__2;
x_1005 = lean_array_push(x_1004, x_148);
lean_inc(x_159);
lean_inc(x_996);
lean_inc(x_1005);
x_1006 = l_Lean_Meta_mkLambda(x_1005, x_996, x_159, x_999);
if (lean_obj_tag(x_1006) == 0)
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1007 = lean_ctor_get(x_1006, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_1006, 1);
lean_inc(x_1008);
lean_dec(x_1006);
x_1009 = lean_expr_abstract(x_996, x_1005);
lean_dec(x_1005);
lean_dec(x_996);
x_1010 = lean_expr_instantiate1(x_1009, x_1000);
lean_dec(x_1000);
lean_dec(x_1009);
if (x_108 == 0)
{
lean_object* x_1103; 
lean_inc(x_159);
x_1103 = l_Lean_Meta_mkEqSymm(x_150, x_159, x_1008);
if (lean_obj_tag(x_1103) == 0)
{
lean_object* x_1104; lean_object* x_1105; 
x_1104 = lean_ctor_get(x_1103, 0);
lean_inc(x_1104);
x_1105 = lean_ctor_get(x_1103, 1);
lean_inc(x_1105);
lean_dec(x_1103);
x_1011 = x_1104;
x_1012 = x_1105;
goto block_1102;
}
else
{
uint8_t x_1106; 
lean_dec(x_1010);
lean_dec(x_1007);
lean_dec(x_159);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_1106 = !lean_is_exclusive(x_1103);
if (x_1106 == 0)
{
x_74 = x_1103;
goto block_79;
}
else
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; 
x_1107 = lean_ctor_get(x_1103, 0);
x_1108 = lean_ctor_get(x_1103, 1);
lean_inc(x_1108);
lean_inc(x_1107);
lean_dec(x_1103);
x_1109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1109, 0, x_1107);
lean_ctor_set(x_1109, 1, x_1108);
x_74 = x_1109;
goto block_79;
}
}
}
else
{
x_1011 = x_150;
x_1012 = x_1008;
goto block_1102;
}
block_1102:
{
uint8_t x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
x_1013 = 2;
lean_inc(x_159);
x_1014 = l_Lean_Meta_mkFreshExprMVar(x_1010, x_82, x_1013, x_159, x_1012);
x_1015 = lean_ctor_get(x_1014, 0);
lean_inc(x_1015);
x_1016 = lean_ctor_get(x_1014, 1);
lean_inc(x_1016);
lean_dec(x_1014);
lean_inc(x_159);
lean_inc(x_1015);
x_1017 = l_Lean_Meta_mkEqNDRec(x_1007, x_1015, x_1011, x_159, x_1016);
if (lean_obj_tag(x_1017) == 0)
{
lean_object* x_1018; lean_object* x_1019; uint8_t x_1020; 
x_1018 = lean_ctor_get(x_1017, 1);
lean_inc(x_1018);
x_1019 = lean_ctor_get(x_1017, 0);
lean_inc(x_1019);
lean_dec(x_1017);
x_1020 = !lean_is_exclusive(x_1018);
if (x_1020 == 0)
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; 
x_1021 = lean_ctor_get(x_1018, 1);
x_1022 = l_Lean_MetavarContext_assignExpr(x_1021, x_145, x_1019);
lean_ctor_set(x_1018, 1, x_1022);
x_1023 = l_Lean_Expr_mvarId_x21(x_1015);
lean_dec(x_1015);
x_1024 = l_Lean_Meta_clear(x_1023, x_149, x_159, x_1018);
if (lean_obj_tag(x_1024) == 0)
{
lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; 
x_1025 = lean_ctor_get(x_1024, 0);
lean_inc(x_1025);
x_1026 = lean_ctor_get(x_1024, 1);
lean_inc(x_1026);
lean_dec(x_1024);
x_1027 = l_Lean_Meta_clear(x_1025, x_147, x_159, x_1026);
if (lean_obj_tag(x_1027) == 0)
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1028 = lean_ctor_get(x_1027, 0);
lean_inc(x_1028);
x_1029 = lean_ctor_get(x_1027, 1);
lean_inc(x_1029);
lean_dec(x_1027);
x_1030 = lean_array_get_size(x_136);
lean_dec(x_136);
x_1031 = lean_nat_sub(x_1030, x_104);
lean_dec(x_1030);
x_1032 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_1028, x_1031, x_138, x_159, x_1029);
lean_dec(x_159);
if (lean_obj_tag(x_1032) == 0)
{
uint8_t x_1033; 
x_1033 = !lean_is_exclusive(x_1032);
if (x_1033 == 0)
{
lean_object* x_1034; uint8_t x_1035; 
x_1034 = lean_ctor_get(x_1032, 0);
x_1035 = !lean_is_exclusive(x_1034);
if (x_1035 == 0)
{
lean_object* x_1036; lean_object* x_1037; 
x_1036 = lean_ctor_get(x_1034, 0);
lean_dec(x_1036);
x_1037 = lean_box(0);
lean_ctor_set(x_1034, 0, x_1037);
x_74 = x_1032;
goto block_79;
}
else
{
lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
x_1038 = lean_ctor_get(x_1034, 1);
lean_inc(x_1038);
lean_dec(x_1034);
x_1039 = lean_box(0);
x_1040 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1040, 0, x_1039);
lean_ctor_set(x_1040, 1, x_1038);
lean_ctor_set(x_1032, 0, x_1040);
x_74 = x_1032;
goto block_79;
}
}
else
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
x_1041 = lean_ctor_get(x_1032, 0);
x_1042 = lean_ctor_get(x_1032, 1);
lean_inc(x_1042);
lean_inc(x_1041);
lean_dec(x_1032);
x_1043 = lean_ctor_get(x_1041, 1);
lean_inc(x_1043);
if (lean_is_exclusive(x_1041)) {
 lean_ctor_release(x_1041, 0);
 lean_ctor_release(x_1041, 1);
 x_1044 = x_1041;
} else {
 lean_dec_ref(x_1041);
 x_1044 = lean_box(0);
}
x_1045 = lean_box(0);
if (lean_is_scalar(x_1044)) {
 x_1046 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1046 = x_1044;
}
lean_ctor_set(x_1046, 0, x_1045);
lean_ctor_set(x_1046, 1, x_1043);
x_1047 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1047, 0, x_1046);
lean_ctor_set(x_1047, 1, x_1042);
x_74 = x_1047;
goto block_79;
}
}
else
{
uint8_t x_1048; 
x_1048 = !lean_is_exclusive(x_1032);
if (x_1048 == 0)
{
x_74 = x_1032;
goto block_79;
}
else
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
x_1049 = lean_ctor_get(x_1032, 0);
x_1050 = lean_ctor_get(x_1032, 1);
lean_inc(x_1050);
lean_inc(x_1049);
lean_dec(x_1032);
x_1051 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1051, 0, x_1049);
lean_ctor_set(x_1051, 1, x_1050);
x_74 = x_1051;
goto block_79;
}
}
}
else
{
uint8_t x_1052; 
lean_dec(x_159);
lean_dec(x_136);
x_1052 = !lean_is_exclusive(x_1027);
if (x_1052 == 0)
{
x_74 = x_1027;
goto block_79;
}
else
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
x_1053 = lean_ctor_get(x_1027, 0);
x_1054 = lean_ctor_get(x_1027, 1);
lean_inc(x_1054);
lean_inc(x_1053);
lean_dec(x_1027);
x_1055 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1055, 0, x_1053);
lean_ctor_set(x_1055, 1, x_1054);
x_74 = x_1055;
goto block_79;
}
}
}
else
{
uint8_t x_1056; 
lean_dec(x_159);
lean_dec(x_147);
lean_dec(x_136);
x_1056 = !lean_is_exclusive(x_1024);
if (x_1056 == 0)
{
x_74 = x_1024;
goto block_79;
}
else
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; 
x_1057 = lean_ctor_get(x_1024, 0);
x_1058 = lean_ctor_get(x_1024, 1);
lean_inc(x_1058);
lean_inc(x_1057);
lean_dec(x_1024);
x_1059 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1059, 0, x_1057);
lean_ctor_set(x_1059, 1, x_1058);
x_74 = x_1059;
goto block_79;
}
}
}
else
{
lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
x_1060 = lean_ctor_get(x_1018, 0);
x_1061 = lean_ctor_get(x_1018, 1);
x_1062 = lean_ctor_get(x_1018, 2);
x_1063 = lean_ctor_get(x_1018, 3);
x_1064 = lean_ctor_get(x_1018, 4);
x_1065 = lean_ctor_get(x_1018, 5);
lean_inc(x_1065);
lean_inc(x_1064);
lean_inc(x_1063);
lean_inc(x_1062);
lean_inc(x_1061);
lean_inc(x_1060);
lean_dec(x_1018);
x_1066 = l_Lean_MetavarContext_assignExpr(x_1061, x_145, x_1019);
x_1067 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1067, 0, x_1060);
lean_ctor_set(x_1067, 1, x_1066);
lean_ctor_set(x_1067, 2, x_1062);
lean_ctor_set(x_1067, 3, x_1063);
lean_ctor_set(x_1067, 4, x_1064);
lean_ctor_set(x_1067, 5, x_1065);
x_1068 = l_Lean_Expr_mvarId_x21(x_1015);
lean_dec(x_1015);
x_1069 = l_Lean_Meta_clear(x_1068, x_149, x_159, x_1067);
if (lean_obj_tag(x_1069) == 0)
{
lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; 
x_1070 = lean_ctor_get(x_1069, 0);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_1069, 1);
lean_inc(x_1071);
lean_dec(x_1069);
x_1072 = l_Lean_Meta_clear(x_1070, x_147, x_159, x_1071);
if (lean_obj_tag(x_1072) == 0)
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; 
x_1073 = lean_ctor_get(x_1072, 0);
lean_inc(x_1073);
x_1074 = lean_ctor_get(x_1072, 1);
lean_inc(x_1074);
lean_dec(x_1072);
x_1075 = lean_array_get_size(x_136);
lean_dec(x_136);
x_1076 = lean_nat_sub(x_1075, x_104);
lean_dec(x_1075);
x_1077 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_1073, x_1076, x_138, x_159, x_1074);
lean_dec(x_159);
if (lean_obj_tag(x_1077) == 0)
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; 
x_1078 = lean_ctor_get(x_1077, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1077, 1);
lean_inc(x_1079);
if (lean_is_exclusive(x_1077)) {
 lean_ctor_release(x_1077, 0);
 lean_ctor_release(x_1077, 1);
 x_1080 = x_1077;
} else {
 lean_dec_ref(x_1077);
 x_1080 = lean_box(0);
}
x_1081 = lean_ctor_get(x_1078, 1);
lean_inc(x_1081);
if (lean_is_exclusive(x_1078)) {
 lean_ctor_release(x_1078, 0);
 lean_ctor_release(x_1078, 1);
 x_1082 = x_1078;
} else {
 lean_dec_ref(x_1078);
 x_1082 = lean_box(0);
}
x_1083 = lean_box(0);
if (lean_is_scalar(x_1082)) {
 x_1084 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1084 = x_1082;
}
lean_ctor_set(x_1084, 0, x_1083);
lean_ctor_set(x_1084, 1, x_1081);
if (lean_is_scalar(x_1080)) {
 x_1085 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1085 = x_1080;
}
lean_ctor_set(x_1085, 0, x_1084);
lean_ctor_set(x_1085, 1, x_1079);
x_74 = x_1085;
goto block_79;
}
else
{
lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; 
x_1086 = lean_ctor_get(x_1077, 0);
lean_inc(x_1086);
x_1087 = lean_ctor_get(x_1077, 1);
lean_inc(x_1087);
if (lean_is_exclusive(x_1077)) {
 lean_ctor_release(x_1077, 0);
 lean_ctor_release(x_1077, 1);
 x_1088 = x_1077;
} else {
 lean_dec_ref(x_1077);
 x_1088 = lean_box(0);
}
if (lean_is_scalar(x_1088)) {
 x_1089 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1089 = x_1088;
}
lean_ctor_set(x_1089, 0, x_1086);
lean_ctor_set(x_1089, 1, x_1087);
x_74 = x_1089;
goto block_79;
}
}
else
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; 
lean_dec(x_159);
lean_dec(x_136);
x_1090 = lean_ctor_get(x_1072, 0);
lean_inc(x_1090);
x_1091 = lean_ctor_get(x_1072, 1);
lean_inc(x_1091);
if (lean_is_exclusive(x_1072)) {
 lean_ctor_release(x_1072, 0);
 lean_ctor_release(x_1072, 1);
 x_1092 = x_1072;
} else {
 lean_dec_ref(x_1072);
 x_1092 = lean_box(0);
}
if (lean_is_scalar(x_1092)) {
 x_1093 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1093 = x_1092;
}
lean_ctor_set(x_1093, 0, x_1090);
lean_ctor_set(x_1093, 1, x_1091);
x_74 = x_1093;
goto block_79;
}
}
else
{
lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; 
lean_dec(x_159);
lean_dec(x_147);
lean_dec(x_136);
x_1094 = lean_ctor_get(x_1069, 0);
lean_inc(x_1094);
x_1095 = lean_ctor_get(x_1069, 1);
lean_inc(x_1095);
if (lean_is_exclusive(x_1069)) {
 lean_ctor_release(x_1069, 0);
 lean_ctor_release(x_1069, 1);
 x_1096 = x_1069;
} else {
 lean_dec_ref(x_1069);
 x_1096 = lean_box(0);
}
if (lean_is_scalar(x_1096)) {
 x_1097 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1097 = x_1096;
}
lean_ctor_set(x_1097, 0, x_1094);
lean_ctor_set(x_1097, 1, x_1095);
x_74 = x_1097;
goto block_79;
}
}
}
else
{
uint8_t x_1098; 
lean_dec(x_1015);
lean_dec(x_159);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
x_1098 = !lean_is_exclusive(x_1017);
if (x_1098 == 0)
{
x_74 = x_1017;
goto block_79;
}
else
{
lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; 
x_1099 = lean_ctor_get(x_1017, 0);
x_1100 = lean_ctor_get(x_1017, 1);
lean_inc(x_1100);
lean_inc(x_1099);
lean_dec(x_1017);
x_1101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1101, 0, x_1099);
lean_ctor_set(x_1101, 1, x_1100);
x_74 = x_1101;
goto block_79;
}
}
}
}
else
{
uint8_t x_1110; 
lean_dec(x_1005);
lean_dec(x_1000);
lean_dec(x_996);
lean_dec(x_159);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_1110 = !lean_is_exclusive(x_1006);
if (x_1110 == 0)
{
x_74 = x_1006;
goto block_79;
}
else
{
lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; 
x_1111 = lean_ctor_get(x_1006, 0);
x_1112 = lean_ctor_get(x_1006, 1);
lean_inc(x_1112);
lean_inc(x_1111);
lean_dec(x_1006);
x_1113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1113, 0, x_1111);
lean_ctor_set(x_1113, 1, x_1112);
x_74 = x_1113;
goto block_79;
}
}
}
else
{
lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1114 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_148);
x_1115 = lean_array_push(x_1114, x_148);
x_1116 = lean_expr_abstract(x_996, x_1115);
lean_dec(x_1115);
x_1117 = lean_expr_instantiate1(x_1116, x_1000);
lean_dec(x_1116);
lean_inc(x_159);
lean_inc(x_1000);
x_1118 = l_Lean_Meta_mkEqRefl(x_1000, x_159, x_999);
if (lean_obj_tag(x_1118) == 0)
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
x_1119 = lean_ctor_get(x_1118, 0);
lean_inc(x_1119);
x_1120 = lean_ctor_get(x_1118, 1);
lean_inc(x_1120);
lean_dec(x_1118);
lean_inc(x_150);
x_1121 = lean_array_push(x_1114, x_150);
x_1122 = lean_expr_abstract(x_1117, x_1121);
lean_dec(x_1117);
x_1123 = lean_expr_instantiate1(x_1122, x_1119);
lean_dec(x_1119);
lean_dec(x_1122);
if (x_108 == 0)
{
lean_object* x_1124; 
lean_inc(x_159);
lean_inc(x_148);
x_1124 = l_Lean_Meta_mkEq(x_1000, x_148, x_159, x_1120);
if (lean_obj_tag(x_1124) == 0)
{
lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; uint8_t x_1129; lean_object* x_1130; 
x_1125 = lean_ctor_get(x_1124, 0);
lean_inc(x_1125);
x_1126 = lean_ctor_get(x_1124, 1);
lean_inc(x_1126);
lean_dec(x_1124);
x_1127 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__1___boxed), 7, 4);
lean_closure_set(x_1127, 0, x_996);
lean_closure_set(x_1127, 1, x_1121);
lean_closure_set(x_1127, 2, x_129);
lean_closure_set(x_1127, 3, x_148);
x_1128 = l_Lean_Meta_substCore___closed__18;
x_1129 = 0;
lean_inc(x_159);
x_1130 = l_Lean_Meta_withLocalDecl___rarg(x_1128, x_1125, x_1129, x_1127, x_159, x_1126);
if (lean_obj_tag(x_1130) == 0)
{
lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; 
x_1131 = lean_ctor_get(x_1130, 0);
lean_inc(x_1131);
x_1132 = lean_ctor_get(x_1130, 1);
lean_inc(x_1132);
lean_dec(x_1130);
lean_inc(x_159);
x_1133 = l_Lean_Meta_mkEqSymm(x_150, x_159, x_1132);
if (lean_obj_tag(x_1133) == 0)
{
lean_object* x_1134; lean_object* x_1135; uint8_t x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
x_1134 = lean_ctor_get(x_1133, 0);
lean_inc(x_1134);
x_1135 = lean_ctor_get(x_1133, 1);
lean_inc(x_1135);
lean_dec(x_1133);
x_1136 = 2;
lean_inc(x_159);
x_1137 = l_Lean_Meta_mkFreshExprMVar(x_1123, x_82, x_1136, x_159, x_1135);
x_1138 = lean_ctor_get(x_1137, 0);
lean_inc(x_1138);
x_1139 = lean_ctor_get(x_1137, 1);
lean_inc(x_1139);
lean_dec(x_1137);
lean_inc(x_159);
lean_inc(x_1138);
x_1140 = l_Lean_Meta_mkEqRec(x_1131, x_1138, x_1134, x_159, x_1139);
if (lean_obj_tag(x_1140) == 0)
{
lean_object* x_1141; lean_object* x_1142; uint8_t x_1143; 
x_1141 = lean_ctor_get(x_1140, 1);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1140, 0);
lean_inc(x_1142);
lean_dec(x_1140);
x_1143 = !lean_is_exclusive(x_1141);
if (x_1143 == 0)
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
x_1144 = lean_ctor_get(x_1141, 1);
x_1145 = l_Lean_MetavarContext_assignExpr(x_1144, x_145, x_1142);
lean_ctor_set(x_1141, 1, x_1145);
x_1146 = l_Lean_Expr_mvarId_x21(x_1138);
lean_dec(x_1138);
x_1147 = l_Lean_Meta_clear(x_1146, x_149, x_159, x_1141);
if (lean_obj_tag(x_1147) == 0)
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
x_1148 = lean_ctor_get(x_1147, 0);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_1147, 1);
lean_inc(x_1149);
lean_dec(x_1147);
x_1150 = l_Lean_Meta_clear(x_1148, x_147, x_159, x_1149);
if (lean_obj_tag(x_1150) == 0)
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
x_1151 = lean_ctor_get(x_1150, 0);
lean_inc(x_1151);
x_1152 = lean_ctor_get(x_1150, 1);
lean_inc(x_1152);
lean_dec(x_1150);
x_1153 = lean_array_get_size(x_136);
lean_dec(x_136);
x_1154 = lean_nat_sub(x_1153, x_104);
lean_dec(x_1153);
x_1155 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_1151, x_1154, x_138, x_159, x_1152);
lean_dec(x_159);
if (lean_obj_tag(x_1155) == 0)
{
uint8_t x_1156; 
x_1156 = !lean_is_exclusive(x_1155);
if (x_1156 == 0)
{
lean_object* x_1157; uint8_t x_1158; 
x_1157 = lean_ctor_get(x_1155, 0);
x_1158 = !lean_is_exclusive(x_1157);
if (x_1158 == 0)
{
lean_object* x_1159; lean_object* x_1160; 
x_1159 = lean_ctor_get(x_1157, 0);
lean_dec(x_1159);
x_1160 = lean_box(0);
lean_ctor_set(x_1157, 0, x_1160);
x_74 = x_1155;
goto block_79;
}
else
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; 
x_1161 = lean_ctor_get(x_1157, 1);
lean_inc(x_1161);
lean_dec(x_1157);
x_1162 = lean_box(0);
x_1163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1163, 0, x_1162);
lean_ctor_set(x_1163, 1, x_1161);
lean_ctor_set(x_1155, 0, x_1163);
x_74 = x_1155;
goto block_79;
}
}
else
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; 
x_1164 = lean_ctor_get(x_1155, 0);
x_1165 = lean_ctor_get(x_1155, 1);
lean_inc(x_1165);
lean_inc(x_1164);
lean_dec(x_1155);
x_1166 = lean_ctor_get(x_1164, 1);
lean_inc(x_1166);
if (lean_is_exclusive(x_1164)) {
 lean_ctor_release(x_1164, 0);
 lean_ctor_release(x_1164, 1);
 x_1167 = x_1164;
} else {
 lean_dec_ref(x_1164);
 x_1167 = lean_box(0);
}
x_1168 = lean_box(0);
if (lean_is_scalar(x_1167)) {
 x_1169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1169 = x_1167;
}
lean_ctor_set(x_1169, 0, x_1168);
lean_ctor_set(x_1169, 1, x_1166);
x_1170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1170, 0, x_1169);
lean_ctor_set(x_1170, 1, x_1165);
x_74 = x_1170;
goto block_79;
}
}
else
{
uint8_t x_1171; 
x_1171 = !lean_is_exclusive(x_1155);
if (x_1171 == 0)
{
x_74 = x_1155;
goto block_79;
}
else
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; 
x_1172 = lean_ctor_get(x_1155, 0);
x_1173 = lean_ctor_get(x_1155, 1);
lean_inc(x_1173);
lean_inc(x_1172);
lean_dec(x_1155);
x_1174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1174, 0, x_1172);
lean_ctor_set(x_1174, 1, x_1173);
x_74 = x_1174;
goto block_79;
}
}
}
else
{
uint8_t x_1175; 
lean_dec(x_159);
lean_dec(x_136);
x_1175 = !lean_is_exclusive(x_1150);
if (x_1175 == 0)
{
x_74 = x_1150;
goto block_79;
}
else
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
x_1176 = lean_ctor_get(x_1150, 0);
x_1177 = lean_ctor_get(x_1150, 1);
lean_inc(x_1177);
lean_inc(x_1176);
lean_dec(x_1150);
x_1178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1178, 0, x_1176);
lean_ctor_set(x_1178, 1, x_1177);
x_74 = x_1178;
goto block_79;
}
}
}
else
{
uint8_t x_1179; 
lean_dec(x_159);
lean_dec(x_147);
lean_dec(x_136);
x_1179 = !lean_is_exclusive(x_1147);
if (x_1179 == 0)
{
x_74 = x_1147;
goto block_79;
}
else
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; 
x_1180 = lean_ctor_get(x_1147, 0);
x_1181 = lean_ctor_get(x_1147, 1);
lean_inc(x_1181);
lean_inc(x_1180);
lean_dec(x_1147);
x_1182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1182, 0, x_1180);
lean_ctor_set(x_1182, 1, x_1181);
x_74 = x_1182;
goto block_79;
}
}
}
else
{
lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; 
x_1183 = lean_ctor_get(x_1141, 0);
x_1184 = lean_ctor_get(x_1141, 1);
x_1185 = lean_ctor_get(x_1141, 2);
x_1186 = lean_ctor_get(x_1141, 3);
x_1187 = lean_ctor_get(x_1141, 4);
x_1188 = lean_ctor_get(x_1141, 5);
lean_inc(x_1188);
lean_inc(x_1187);
lean_inc(x_1186);
lean_inc(x_1185);
lean_inc(x_1184);
lean_inc(x_1183);
lean_dec(x_1141);
x_1189 = l_Lean_MetavarContext_assignExpr(x_1184, x_145, x_1142);
x_1190 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1190, 0, x_1183);
lean_ctor_set(x_1190, 1, x_1189);
lean_ctor_set(x_1190, 2, x_1185);
lean_ctor_set(x_1190, 3, x_1186);
lean_ctor_set(x_1190, 4, x_1187);
lean_ctor_set(x_1190, 5, x_1188);
x_1191 = l_Lean_Expr_mvarId_x21(x_1138);
lean_dec(x_1138);
x_1192 = l_Lean_Meta_clear(x_1191, x_149, x_159, x_1190);
if (lean_obj_tag(x_1192) == 0)
{
lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
x_1193 = lean_ctor_get(x_1192, 0);
lean_inc(x_1193);
x_1194 = lean_ctor_get(x_1192, 1);
lean_inc(x_1194);
lean_dec(x_1192);
x_1195 = l_Lean_Meta_clear(x_1193, x_147, x_159, x_1194);
if (lean_obj_tag(x_1195) == 0)
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; 
x_1196 = lean_ctor_get(x_1195, 0);
lean_inc(x_1196);
x_1197 = lean_ctor_get(x_1195, 1);
lean_inc(x_1197);
lean_dec(x_1195);
x_1198 = lean_array_get_size(x_136);
lean_dec(x_136);
x_1199 = lean_nat_sub(x_1198, x_104);
lean_dec(x_1198);
x_1200 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_1196, x_1199, x_138, x_159, x_1197);
lean_dec(x_159);
if (lean_obj_tag(x_1200) == 0)
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; 
x_1201 = lean_ctor_get(x_1200, 0);
lean_inc(x_1201);
x_1202 = lean_ctor_get(x_1200, 1);
lean_inc(x_1202);
if (lean_is_exclusive(x_1200)) {
 lean_ctor_release(x_1200, 0);
 lean_ctor_release(x_1200, 1);
 x_1203 = x_1200;
} else {
 lean_dec_ref(x_1200);
 x_1203 = lean_box(0);
}
x_1204 = lean_ctor_get(x_1201, 1);
lean_inc(x_1204);
if (lean_is_exclusive(x_1201)) {
 lean_ctor_release(x_1201, 0);
 lean_ctor_release(x_1201, 1);
 x_1205 = x_1201;
} else {
 lean_dec_ref(x_1201);
 x_1205 = lean_box(0);
}
x_1206 = lean_box(0);
if (lean_is_scalar(x_1205)) {
 x_1207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1207 = x_1205;
}
lean_ctor_set(x_1207, 0, x_1206);
lean_ctor_set(x_1207, 1, x_1204);
if (lean_is_scalar(x_1203)) {
 x_1208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1208 = x_1203;
}
lean_ctor_set(x_1208, 0, x_1207);
lean_ctor_set(x_1208, 1, x_1202);
x_74 = x_1208;
goto block_79;
}
else
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; 
x_1209 = lean_ctor_get(x_1200, 0);
lean_inc(x_1209);
x_1210 = lean_ctor_get(x_1200, 1);
lean_inc(x_1210);
if (lean_is_exclusive(x_1200)) {
 lean_ctor_release(x_1200, 0);
 lean_ctor_release(x_1200, 1);
 x_1211 = x_1200;
} else {
 lean_dec_ref(x_1200);
 x_1211 = lean_box(0);
}
if (lean_is_scalar(x_1211)) {
 x_1212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1212 = x_1211;
}
lean_ctor_set(x_1212, 0, x_1209);
lean_ctor_set(x_1212, 1, x_1210);
x_74 = x_1212;
goto block_79;
}
}
else
{
lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
lean_dec(x_159);
lean_dec(x_136);
x_1213 = lean_ctor_get(x_1195, 0);
lean_inc(x_1213);
x_1214 = lean_ctor_get(x_1195, 1);
lean_inc(x_1214);
if (lean_is_exclusive(x_1195)) {
 lean_ctor_release(x_1195, 0);
 lean_ctor_release(x_1195, 1);
 x_1215 = x_1195;
} else {
 lean_dec_ref(x_1195);
 x_1215 = lean_box(0);
}
if (lean_is_scalar(x_1215)) {
 x_1216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1216 = x_1215;
}
lean_ctor_set(x_1216, 0, x_1213);
lean_ctor_set(x_1216, 1, x_1214);
x_74 = x_1216;
goto block_79;
}
}
else
{
lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; 
lean_dec(x_159);
lean_dec(x_147);
lean_dec(x_136);
x_1217 = lean_ctor_get(x_1192, 0);
lean_inc(x_1217);
x_1218 = lean_ctor_get(x_1192, 1);
lean_inc(x_1218);
if (lean_is_exclusive(x_1192)) {
 lean_ctor_release(x_1192, 0);
 lean_ctor_release(x_1192, 1);
 x_1219 = x_1192;
} else {
 lean_dec_ref(x_1192);
 x_1219 = lean_box(0);
}
if (lean_is_scalar(x_1219)) {
 x_1220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1220 = x_1219;
}
lean_ctor_set(x_1220, 0, x_1217);
lean_ctor_set(x_1220, 1, x_1218);
x_74 = x_1220;
goto block_79;
}
}
}
else
{
uint8_t x_1221; 
lean_dec(x_1138);
lean_dec(x_159);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
x_1221 = !lean_is_exclusive(x_1140);
if (x_1221 == 0)
{
x_74 = x_1140;
goto block_79;
}
else
{
lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; 
x_1222 = lean_ctor_get(x_1140, 0);
x_1223 = lean_ctor_get(x_1140, 1);
lean_inc(x_1223);
lean_inc(x_1222);
lean_dec(x_1140);
x_1224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1224, 0, x_1222);
lean_ctor_set(x_1224, 1, x_1223);
x_74 = x_1224;
goto block_79;
}
}
}
else
{
uint8_t x_1225; 
lean_dec(x_1131);
lean_dec(x_1123);
lean_dec(x_159);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_1225 = !lean_is_exclusive(x_1133);
if (x_1225 == 0)
{
x_74 = x_1133;
goto block_79;
}
else
{
lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; 
x_1226 = lean_ctor_get(x_1133, 0);
x_1227 = lean_ctor_get(x_1133, 1);
lean_inc(x_1227);
lean_inc(x_1226);
lean_dec(x_1133);
x_1228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1228, 0, x_1226);
lean_ctor_set(x_1228, 1, x_1227);
x_74 = x_1228;
goto block_79;
}
}
}
else
{
uint8_t x_1229; 
lean_dec(x_1123);
lean_dec(x_159);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_1229 = !lean_is_exclusive(x_1130);
if (x_1229 == 0)
{
x_74 = x_1130;
goto block_79;
}
else
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; 
x_1230 = lean_ctor_get(x_1130, 0);
x_1231 = lean_ctor_get(x_1130, 1);
lean_inc(x_1231);
lean_inc(x_1230);
lean_dec(x_1130);
x_1232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1232, 0, x_1230);
lean_ctor_set(x_1232, 1, x_1231);
x_74 = x_1232;
goto block_79;
}
}
}
else
{
uint8_t x_1233; 
lean_dec(x_1123);
lean_dec(x_1121);
lean_dec(x_996);
lean_dec(x_159);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_1233 = !lean_is_exclusive(x_1124);
if (x_1233 == 0)
{
x_74 = x_1124;
goto block_79;
}
else
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; 
x_1234 = lean_ctor_get(x_1124, 0);
x_1235 = lean_ctor_get(x_1124, 1);
lean_inc(x_1235);
lean_inc(x_1234);
lean_dec(x_1124);
x_1236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1236, 0, x_1234);
lean_ctor_set(x_1236, 1, x_1235);
x_74 = x_1236;
goto block_79;
}
}
}
else
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; 
lean_dec(x_1121);
lean_dec(x_1000);
x_1237 = lean_array_push(x_129, x_148);
lean_inc(x_150);
x_1238 = lean_array_push(x_1237, x_150);
lean_inc(x_159);
x_1239 = l_Lean_Meta_mkLambda(x_1238, x_996, x_159, x_1120);
if (lean_obj_tag(x_1239) == 0)
{
lean_object* x_1240; lean_object* x_1241; uint8_t x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; 
x_1240 = lean_ctor_get(x_1239, 0);
lean_inc(x_1240);
x_1241 = lean_ctor_get(x_1239, 1);
lean_inc(x_1241);
lean_dec(x_1239);
x_1242 = 2;
lean_inc(x_159);
x_1243 = l_Lean_Meta_mkFreshExprMVar(x_1123, x_82, x_1242, x_159, x_1241);
x_1244 = lean_ctor_get(x_1243, 0);
lean_inc(x_1244);
x_1245 = lean_ctor_get(x_1243, 1);
lean_inc(x_1245);
lean_dec(x_1243);
lean_inc(x_159);
lean_inc(x_1244);
x_1246 = l_Lean_Meta_mkEqRec(x_1240, x_1244, x_150, x_159, x_1245);
if (lean_obj_tag(x_1246) == 0)
{
lean_object* x_1247; lean_object* x_1248; uint8_t x_1249; 
x_1247 = lean_ctor_get(x_1246, 1);
lean_inc(x_1247);
x_1248 = lean_ctor_get(x_1246, 0);
lean_inc(x_1248);
lean_dec(x_1246);
x_1249 = !lean_is_exclusive(x_1247);
if (x_1249 == 0)
{
lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; 
x_1250 = lean_ctor_get(x_1247, 1);
x_1251 = l_Lean_MetavarContext_assignExpr(x_1250, x_145, x_1248);
lean_ctor_set(x_1247, 1, x_1251);
x_1252 = l_Lean_Expr_mvarId_x21(x_1244);
lean_dec(x_1244);
x_1253 = l_Lean_Meta_clear(x_1252, x_149, x_159, x_1247);
if (lean_obj_tag(x_1253) == 0)
{
lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; 
x_1254 = lean_ctor_get(x_1253, 0);
lean_inc(x_1254);
x_1255 = lean_ctor_get(x_1253, 1);
lean_inc(x_1255);
lean_dec(x_1253);
x_1256 = l_Lean_Meta_clear(x_1254, x_147, x_159, x_1255);
if (lean_obj_tag(x_1256) == 0)
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; 
x_1257 = lean_ctor_get(x_1256, 0);
lean_inc(x_1257);
x_1258 = lean_ctor_get(x_1256, 1);
lean_inc(x_1258);
lean_dec(x_1256);
x_1259 = lean_array_get_size(x_136);
lean_dec(x_136);
x_1260 = lean_nat_sub(x_1259, x_104);
lean_dec(x_1259);
x_1261 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_1257, x_1260, x_138, x_159, x_1258);
lean_dec(x_159);
if (lean_obj_tag(x_1261) == 0)
{
uint8_t x_1262; 
x_1262 = !lean_is_exclusive(x_1261);
if (x_1262 == 0)
{
lean_object* x_1263; uint8_t x_1264; 
x_1263 = lean_ctor_get(x_1261, 0);
x_1264 = !lean_is_exclusive(x_1263);
if (x_1264 == 0)
{
lean_object* x_1265; lean_object* x_1266; 
x_1265 = lean_ctor_get(x_1263, 0);
lean_dec(x_1265);
x_1266 = lean_box(0);
lean_ctor_set(x_1263, 0, x_1266);
x_74 = x_1261;
goto block_79;
}
else
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
x_1267 = lean_ctor_get(x_1263, 1);
lean_inc(x_1267);
lean_dec(x_1263);
x_1268 = lean_box(0);
x_1269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1269, 0, x_1268);
lean_ctor_set(x_1269, 1, x_1267);
lean_ctor_set(x_1261, 0, x_1269);
x_74 = x_1261;
goto block_79;
}
}
else
{
lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; 
x_1270 = lean_ctor_get(x_1261, 0);
x_1271 = lean_ctor_get(x_1261, 1);
lean_inc(x_1271);
lean_inc(x_1270);
lean_dec(x_1261);
x_1272 = lean_ctor_get(x_1270, 1);
lean_inc(x_1272);
if (lean_is_exclusive(x_1270)) {
 lean_ctor_release(x_1270, 0);
 lean_ctor_release(x_1270, 1);
 x_1273 = x_1270;
} else {
 lean_dec_ref(x_1270);
 x_1273 = lean_box(0);
}
x_1274 = lean_box(0);
if (lean_is_scalar(x_1273)) {
 x_1275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1275 = x_1273;
}
lean_ctor_set(x_1275, 0, x_1274);
lean_ctor_set(x_1275, 1, x_1272);
x_1276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1276, 0, x_1275);
lean_ctor_set(x_1276, 1, x_1271);
x_74 = x_1276;
goto block_79;
}
}
else
{
uint8_t x_1277; 
x_1277 = !lean_is_exclusive(x_1261);
if (x_1277 == 0)
{
x_74 = x_1261;
goto block_79;
}
else
{
lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; 
x_1278 = lean_ctor_get(x_1261, 0);
x_1279 = lean_ctor_get(x_1261, 1);
lean_inc(x_1279);
lean_inc(x_1278);
lean_dec(x_1261);
x_1280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1280, 0, x_1278);
lean_ctor_set(x_1280, 1, x_1279);
x_74 = x_1280;
goto block_79;
}
}
}
else
{
uint8_t x_1281; 
lean_dec(x_159);
lean_dec(x_136);
x_1281 = !lean_is_exclusive(x_1256);
if (x_1281 == 0)
{
x_74 = x_1256;
goto block_79;
}
else
{
lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; 
x_1282 = lean_ctor_get(x_1256, 0);
x_1283 = lean_ctor_get(x_1256, 1);
lean_inc(x_1283);
lean_inc(x_1282);
lean_dec(x_1256);
x_1284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1284, 0, x_1282);
lean_ctor_set(x_1284, 1, x_1283);
x_74 = x_1284;
goto block_79;
}
}
}
else
{
uint8_t x_1285; 
lean_dec(x_159);
lean_dec(x_147);
lean_dec(x_136);
x_1285 = !lean_is_exclusive(x_1253);
if (x_1285 == 0)
{
x_74 = x_1253;
goto block_79;
}
else
{
lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; 
x_1286 = lean_ctor_get(x_1253, 0);
x_1287 = lean_ctor_get(x_1253, 1);
lean_inc(x_1287);
lean_inc(x_1286);
lean_dec(x_1253);
x_1288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1288, 0, x_1286);
lean_ctor_set(x_1288, 1, x_1287);
x_74 = x_1288;
goto block_79;
}
}
}
else
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; 
x_1289 = lean_ctor_get(x_1247, 0);
x_1290 = lean_ctor_get(x_1247, 1);
x_1291 = lean_ctor_get(x_1247, 2);
x_1292 = lean_ctor_get(x_1247, 3);
x_1293 = lean_ctor_get(x_1247, 4);
x_1294 = lean_ctor_get(x_1247, 5);
lean_inc(x_1294);
lean_inc(x_1293);
lean_inc(x_1292);
lean_inc(x_1291);
lean_inc(x_1290);
lean_inc(x_1289);
lean_dec(x_1247);
x_1295 = l_Lean_MetavarContext_assignExpr(x_1290, x_145, x_1248);
x_1296 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_1296, 0, x_1289);
lean_ctor_set(x_1296, 1, x_1295);
lean_ctor_set(x_1296, 2, x_1291);
lean_ctor_set(x_1296, 3, x_1292);
lean_ctor_set(x_1296, 4, x_1293);
lean_ctor_set(x_1296, 5, x_1294);
x_1297 = l_Lean_Expr_mvarId_x21(x_1244);
lean_dec(x_1244);
x_1298 = l_Lean_Meta_clear(x_1297, x_149, x_159, x_1296);
if (lean_obj_tag(x_1298) == 0)
{
lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; 
x_1299 = lean_ctor_get(x_1298, 0);
lean_inc(x_1299);
x_1300 = lean_ctor_get(x_1298, 1);
lean_inc(x_1300);
lean_dec(x_1298);
x_1301 = l_Lean_Meta_clear(x_1299, x_147, x_159, x_1300);
if (lean_obj_tag(x_1301) == 0)
{
lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; 
x_1302 = lean_ctor_get(x_1301, 0);
lean_inc(x_1302);
x_1303 = lean_ctor_get(x_1301, 1);
lean_inc(x_1303);
lean_dec(x_1301);
x_1304 = lean_array_get_size(x_136);
lean_dec(x_136);
x_1305 = lean_nat_sub(x_1304, x_104);
lean_dec(x_1304);
x_1306 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_1302, x_1305, x_138, x_159, x_1303);
lean_dec(x_159);
if (lean_obj_tag(x_1306) == 0)
{
lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; 
x_1307 = lean_ctor_get(x_1306, 0);
lean_inc(x_1307);
x_1308 = lean_ctor_get(x_1306, 1);
lean_inc(x_1308);
if (lean_is_exclusive(x_1306)) {
 lean_ctor_release(x_1306, 0);
 lean_ctor_release(x_1306, 1);
 x_1309 = x_1306;
} else {
 lean_dec_ref(x_1306);
 x_1309 = lean_box(0);
}
x_1310 = lean_ctor_get(x_1307, 1);
lean_inc(x_1310);
if (lean_is_exclusive(x_1307)) {
 lean_ctor_release(x_1307, 0);
 lean_ctor_release(x_1307, 1);
 x_1311 = x_1307;
} else {
 lean_dec_ref(x_1307);
 x_1311 = lean_box(0);
}
x_1312 = lean_box(0);
if (lean_is_scalar(x_1311)) {
 x_1313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1313 = x_1311;
}
lean_ctor_set(x_1313, 0, x_1312);
lean_ctor_set(x_1313, 1, x_1310);
if (lean_is_scalar(x_1309)) {
 x_1314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1314 = x_1309;
}
lean_ctor_set(x_1314, 0, x_1313);
lean_ctor_set(x_1314, 1, x_1308);
x_74 = x_1314;
goto block_79;
}
else
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; 
x_1315 = lean_ctor_get(x_1306, 0);
lean_inc(x_1315);
x_1316 = lean_ctor_get(x_1306, 1);
lean_inc(x_1316);
if (lean_is_exclusive(x_1306)) {
 lean_ctor_release(x_1306, 0);
 lean_ctor_release(x_1306, 1);
 x_1317 = x_1306;
} else {
 lean_dec_ref(x_1306);
 x_1317 = lean_box(0);
}
if (lean_is_scalar(x_1317)) {
 x_1318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1318 = x_1317;
}
lean_ctor_set(x_1318, 0, x_1315);
lean_ctor_set(x_1318, 1, x_1316);
x_74 = x_1318;
goto block_79;
}
}
else
{
lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; 
lean_dec(x_159);
lean_dec(x_136);
x_1319 = lean_ctor_get(x_1301, 0);
lean_inc(x_1319);
x_1320 = lean_ctor_get(x_1301, 1);
lean_inc(x_1320);
if (lean_is_exclusive(x_1301)) {
 lean_ctor_release(x_1301, 0);
 lean_ctor_release(x_1301, 1);
 x_1321 = x_1301;
} else {
 lean_dec_ref(x_1301);
 x_1321 = lean_box(0);
}
if (lean_is_scalar(x_1321)) {
 x_1322 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1322 = x_1321;
}
lean_ctor_set(x_1322, 0, x_1319);
lean_ctor_set(x_1322, 1, x_1320);
x_74 = x_1322;
goto block_79;
}
}
else
{
lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; 
lean_dec(x_159);
lean_dec(x_147);
lean_dec(x_136);
x_1323 = lean_ctor_get(x_1298, 0);
lean_inc(x_1323);
x_1324 = lean_ctor_get(x_1298, 1);
lean_inc(x_1324);
if (lean_is_exclusive(x_1298)) {
 lean_ctor_release(x_1298, 0);
 lean_ctor_release(x_1298, 1);
 x_1325 = x_1298;
} else {
 lean_dec_ref(x_1298);
 x_1325 = lean_box(0);
}
if (lean_is_scalar(x_1325)) {
 x_1326 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1326 = x_1325;
}
lean_ctor_set(x_1326, 0, x_1323);
lean_ctor_set(x_1326, 1, x_1324);
x_74 = x_1326;
goto block_79;
}
}
}
else
{
uint8_t x_1327; 
lean_dec(x_1244);
lean_dec(x_159);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
x_1327 = !lean_is_exclusive(x_1246);
if (x_1327 == 0)
{
x_74 = x_1246;
goto block_79;
}
else
{
lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; 
x_1328 = lean_ctor_get(x_1246, 0);
x_1329 = lean_ctor_get(x_1246, 1);
lean_inc(x_1329);
lean_inc(x_1328);
lean_dec(x_1246);
x_1330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1330, 0, x_1328);
lean_ctor_set(x_1330, 1, x_1329);
x_74 = x_1330;
goto block_79;
}
}
}
else
{
uint8_t x_1331; 
lean_dec(x_1123);
lean_dec(x_159);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_1331 = !lean_is_exclusive(x_1239);
if (x_1331 == 0)
{
x_74 = x_1239;
goto block_79;
}
else
{
lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; 
x_1332 = lean_ctor_get(x_1239, 0);
x_1333 = lean_ctor_get(x_1239, 1);
lean_inc(x_1333);
lean_inc(x_1332);
lean_dec(x_1239);
x_1334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1334, 0, x_1332);
lean_ctor_set(x_1334, 1, x_1333);
x_74 = x_1334;
goto block_79;
}
}
}
}
else
{
uint8_t x_1335; 
lean_dec(x_1117);
lean_dec(x_1000);
lean_dec(x_996);
lean_dec(x_159);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_1335 = !lean_is_exclusive(x_1118);
if (x_1335 == 0)
{
x_74 = x_1118;
goto block_79;
}
else
{
lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; 
x_1336 = lean_ctor_get(x_1118, 0);
x_1337 = lean_ctor_get(x_1118, 1);
lean_inc(x_1337);
lean_inc(x_1336);
lean_dec(x_1118);
x_1338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1338, 0, x_1336);
lean_ctor_set(x_1338, 1, x_1337);
x_74 = x_1338;
goto block_79;
}
}
}
}
}
else
{
uint8_t x_1352; 
lean_dec(x_996);
lean_dec(x_159);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_1352 = !lean_is_exclusive(x_997);
if (x_1352 == 0)
{
x_74 = x_997;
goto block_79;
}
else
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; 
x_1353 = lean_ctor_get(x_997, 0);
x_1354 = lean_ctor_get(x_997, 1);
lean_inc(x_1354);
lean_inc(x_1353);
lean_dec(x_997);
x_1355 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1355, 0, x_1353);
lean_ctor_set(x_1355, 1, x_1354);
x_74 = x_1355;
goto block_79;
}
}
}
else
{
uint8_t x_1356; 
lean_dec(x_159);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_1356 = !lean_is_exclusive(x_993);
if (x_1356 == 0)
{
x_74 = x_993;
goto block_79;
}
else
{
lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; 
x_1357 = lean_ctor_get(x_993, 0);
x_1358 = lean_ctor_get(x_993, 1);
lean_inc(x_1358);
lean_inc(x_1357);
lean_dec(x_993);
x_1359 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1359, 0, x_1357);
lean_ctor_set(x_1359, 1, x_1358);
x_74 = x_1359;
goto block_79;
}
}
}
}
block_989:
{
uint8_t x_161; 
lean_dec(x_160);
x_161 = !lean_is_exclusive(x_153);
if (x_161 == 0)
{
lean_object* x_162; uint8_t x_163; 
x_162 = lean_ctor_get(x_153, 2);
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_189; lean_object* x_190; lean_object* x_213; 
x_164 = lean_ctor_get(x_162, 2);
lean_ctor_set(x_162, 2, x_80);
lean_inc(x_145);
x_213 = l_Lean_Meta_getMVarDecl(x_145, x_159, x_153);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_ctor_get(x_214, 2);
lean_inc(x_216);
lean_dec(x_214);
lean_inc(x_159);
lean_inc(x_149);
x_217 = l_Lean_Meta_getLocalDecl(x_149, x_159, x_215);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_477; uint8_t x_478; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_477 = l_Lean_LocalDecl_type(x_218);
lean_dec(x_218);
x_478 = l_Lean_Expr_isAppOfArity___main(x_477, x_91, x_92);
if (x_478 == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
lean_dec(x_477);
lean_dec(x_216);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_479 = l_Lean_Meta_isClassQuick___main___closed__1;
x_480 = l_unreachable_x21___rarg(x_479);
x_481 = lean_apply_2(x_480, x_159, x_219);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; 
lean_dec(x_143);
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
lean_dec(x_481);
x_165 = x_482;
x_166 = x_483;
goto block_188;
}
else
{
lean_object* x_484; lean_object* x_485; 
lean_dec(x_154);
x_484 = lean_ctor_get(x_481, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_481, 1);
lean_inc(x_485);
lean_dec(x_481);
x_189 = x_484;
x_190 = x_485;
goto block_212;
}
}
else
{
lean_object* x_486; 
x_486 = l_Lean_Expr_getAppNumArgsAux___main(x_477, x_98);
if (x_108 == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_487 = lean_nat_sub(x_486, x_104);
lean_dec(x_486);
x_488 = lean_nat_sub(x_487, x_100);
lean_dec(x_487);
x_489 = l_Lean_Expr_getRevArg_x21___main(x_477, x_488);
lean_dec(x_477);
x_220 = x_489;
goto block_476;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_490 = lean_nat_sub(x_486, x_100);
lean_dec(x_486);
x_491 = lean_nat_sub(x_490, x_100);
lean_dec(x_490);
x_492 = l_Lean_Expr_getRevArg_x21___main(x_477, x_491);
lean_dec(x_477);
x_220 = x_492;
goto block_476;
}
}
block_476:
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_inc(x_216);
x_222 = l_Lean_MetavarContext_exprDependsOn(x_221, x_216, x_149);
x_223 = lean_unbox(x_222);
lean_dec(x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = l_Lean_mkOptionalNode___closed__2;
x_225 = lean_array_push(x_224, x_148);
lean_inc(x_159);
lean_inc(x_216);
lean_inc(x_225);
x_226 = l_Lean_Meta_mkLambda(x_225, x_216, x_159, x_219);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_expr_abstract(x_216, x_225);
lean_dec(x_225);
lean_dec(x_216);
x_230 = lean_expr_instantiate1(x_229, x_220);
lean_dec(x_220);
lean_dec(x_229);
if (x_108 == 0)
{
lean_object* x_300; 
lean_inc(x_159);
x_300 = l_Lean_Meta_mkEqSymm(x_150, x_159, x_228);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_231 = x_301;
x_232 = x_302;
goto block_299;
}
else
{
lean_object* x_303; lean_object* x_304; 
lean_dec(x_230);
lean_dec(x_227);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_303 = lean_ctor_get(x_300, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_300, 1);
lean_inc(x_304);
lean_dec(x_300);
x_189 = x_303;
x_190 = x_304;
goto block_212;
}
}
else
{
x_231 = x_150;
x_232 = x_228;
goto block_299;
}
block_299:
{
uint8_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = 2;
lean_inc(x_159);
x_234 = l_Lean_Meta_mkFreshExprMVar(x_230, x_82, x_233, x_159, x_232);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
lean_inc(x_159);
lean_inc(x_235);
x_237 = l_Lean_Meta_mkEqNDRec(x_227, x_235, x_231, x_159, x_236);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 0);
lean_inc(x_239);
lean_dec(x_237);
x_240 = !lean_is_exclusive(x_238);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_241 = lean_ctor_get(x_238, 1);
x_242 = l_Lean_MetavarContext_assignExpr(x_241, x_145, x_239);
lean_ctor_set(x_238, 1, x_242);
x_243 = l_Lean_Expr_mvarId_x21(x_235);
lean_dec(x_235);
x_244 = l_Lean_Meta_clear(x_243, x_149, x_159, x_238);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = l_Lean_Meta_clear(x_245, x_147, x_159, x_246);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_array_get_size(x_136);
lean_dec(x_136);
x_251 = lean_nat_sub(x_250, x_104);
lean_dec(x_250);
x_252 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_248, x_251, x_138, x_159, x_249);
lean_dec(x_159);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; 
lean_dec(x_143);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = !lean_is_exclusive(x_253);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_253, 0);
lean_dec(x_256);
x_257 = lean_box(0);
lean_ctor_set(x_253, 0, x_257);
x_165 = x_253;
x_166 = x_254;
goto block_188;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_253, 1);
lean_inc(x_258);
lean_dec(x_253);
x_259 = lean_box(0);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_258);
x_165 = x_260;
x_166 = x_254;
goto block_188;
}
}
else
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_154);
x_261 = lean_ctor_get(x_252, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_252, 1);
lean_inc(x_262);
lean_dec(x_252);
x_189 = x_261;
x_190 = x_262;
goto block_212;
}
}
else
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_136);
x_263 = lean_ctor_get(x_247, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_247, 1);
lean_inc(x_264);
lean_dec(x_247);
x_189 = x_263;
x_190 = x_264;
goto block_212;
}
}
else
{
lean_object* x_265; lean_object* x_266; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_147);
lean_dec(x_136);
x_265 = lean_ctor_get(x_244, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_244, 1);
lean_inc(x_266);
lean_dec(x_244);
x_189 = x_265;
x_190 = x_266;
goto block_212;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_267 = lean_ctor_get(x_238, 0);
x_268 = lean_ctor_get(x_238, 1);
x_269 = lean_ctor_get(x_238, 2);
x_270 = lean_ctor_get(x_238, 3);
x_271 = lean_ctor_get(x_238, 4);
x_272 = lean_ctor_get(x_238, 5);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_238);
x_273 = l_Lean_MetavarContext_assignExpr(x_268, x_145, x_239);
x_274 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_274, 0, x_267);
lean_ctor_set(x_274, 1, x_273);
lean_ctor_set(x_274, 2, x_269);
lean_ctor_set(x_274, 3, x_270);
lean_ctor_set(x_274, 4, x_271);
lean_ctor_set(x_274, 5, x_272);
x_275 = l_Lean_Expr_mvarId_x21(x_235);
lean_dec(x_235);
x_276 = l_Lean_Meta_clear(x_275, x_149, x_159, x_274);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = l_Lean_Meta_clear(x_277, x_147, x_159, x_278);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = lean_array_get_size(x_136);
lean_dec(x_136);
x_283 = lean_nat_sub(x_282, x_104);
lean_dec(x_282);
x_284 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_280, x_283, x_138, x_159, x_281);
lean_dec(x_159);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_143);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_288 = x_285;
} else {
 lean_dec_ref(x_285);
 x_288 = lean_box(0);
}
x_289 = lean_box(0);
if (lean_is_scalar(x_288)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_288;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_287);
x_165 = x_290;
x_166 = x_286;
goto block_188;
}
else
{
lean_object* x_291; lean_object* x_292; 
lean_dec(x_154);
x_291 = lean_ctor_get(x_284, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_284, 1);
lean_inc(x_292);
lean_dec(x_284);
x_189 = x_291;
x_190 = x_292;
goto block_212;
}
}
else
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_136);
x_293 = lean_ctor_get(x_279, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_279, 1);
lean_inc(x_294);
lean_dec(x_279);
x_189 = x_293;
x_190 = x_294;
goto block_212;
}
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_147);
lean_dec(x_136);
x_295 = lean_ctor_get(x_276, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_276, 1);
lean_inc(x_296);
lean_dec(x_276);
x_189 = x_295;
x_190 = x_296;
goto block_212;
}
}
}
else
{
lean_object* x_297; lean_object* x_298; 
lean_dec(x_235);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
x_297 = lean_ctor_get(x_237, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_237, 1);
lean_inc(x_298);
lean_dec(x_237);
x_189 = x_297;
x_190 = x_298;
goto block_212;
}
}
}
else
{
lean_object* x_305; lean_object* x_306; 
lean_dec(x_225);
lean_dec(x_220);
lean_dec(x_216);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_305 = lean_ctor_get(x_226, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_226, 1);
lean_inc(x_306);
lean_dec(x_226);
x_189 = x_305;
x_190 = x_306;
goto block_212;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_307 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_148);
x_308 = lean_array_push(x_307, x_148);
x_309 = lean_expr_abstract(x_216, x_308);
lean_dec(x_308);
x_310 = lean_expr_instantiate1(x_309, x_220);
lean_dec(x_309);
lean_inc(x_159);
lean_inc(x_220);
x_311 = l_Lean_Meta_mkEqRefl(x_220, x_159, x_219);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
lean_inc(x_150);
x_314 = lean_array_push(x_307, x_150);
x_315 = lean_expr_abstract(x_310, x_314);
lean_dec(x_310);
x_316 = lean_expr_instantiate1(x_315, x_312);
lean_dec(x_312);
lean_dec(x_315);
if (x_108 == 0)
{
lean_object* x_317; 
lean_inc(x_159);
lean_inc(x_148);
x_317 = l_Lean_Meta_mkEq(x_220, x_148, x_159, x_313);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_320 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__1___boxed), 7, 4);
lean_closure_set(x_320, 0, x_216);
lean_closure_set(x_320, 1, x_314);
lean_closure_set(x_320, 2, x_129);
lean_closure_set(x_320, 3, x_148);
x_321 = l_Lean_Meta_substCore___closed__18;
x_322 = 0;
lean_inc(x_159);
x_323 = l_Lean_Meta_withLocalDecl___rarg(x_321, x_318, x_322, x_320, x_159, x_319);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
lean_inc(x_159);
x_326 = l_Lean_Meta_mkEqSymm(x_150, x_159, x_325);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; uint8_t x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
x_329 = 2;
lean_inc(x_159);
x_330 = l_Lean_Meta_mkFreshExprMVar(x_316, x_82, x_329, x_159, x_328);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
lean_inc(x_159);
lean_inc(x_331);
x_333 = l_Lean_Meta_mkEqRec(x_324, x_331, x_327, x_159, x_332);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; uint8_t x_336; 
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 0);
lean_inc(x_335);
lean_dec(x_333);
x_336 = !lean_is_exclusive(x_334);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_337 = lean_ctor_get(x_334, 1);
x_338 = l_Lean_MetavarContext_assignExpr(x_337, x_145, x_335);
lean_ctor_set(x_334, 1, x_338);
x_339 = l_Lean_Expr_mvarId_x21(x_331);
lean_dec(x_331);
x_340 = l_Lean_Meta_clear(x_339, x_149, x_159, x_334);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
lean_dec(x_340);
x_343 = l_Lean_Meta_clear(x_341, x_147, x_159, x_342);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_346 = lean_array_get_size(x_136);
lean_dec(x_136);
x_347 = lean_nat_sub(x_346, x_104);
lean_dec(x_346);
x_348 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_344, x_347, x_138, x_159, x_345);
lean_dec(x_159);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; uint8_t x_351; 
lean_dec(x_143);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_351 = !lean_is_exclusive(x_349);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; 
x_352 = lean_ctor_get(x_349, 0);
lean_dec(x_352);
x_353 = lean_box(0);
lean_ctor_set(x_349, 0, x_353);
x_165 = x_349;
x_166 = x_350;
goto block_188;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_349, 1);
lean_inc(x_354);
lean_dec(x_349);
x_355 = lean_box(0);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_354);
x_165 = x_356;
x_166 = x_350;
goto block_188;
}
}
else
{
lean_object* x_357; lean_object* x_358; 
lean_dec(x_154);
x_357 = lean_ctor_get(x_348, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_348, 1);
lean_inc(x_358);
lean_dec(x_348);
x_189 = x_357;
x_190 = x_358;
goto block_212;
}
}
else
{
lean_object* x_359; lean_object* x_360; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_136);
x_359 = lean_ctor_get(x_343, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_343, 1);
lean_inc(x_360);
lean_dec(x_343);
x_189 = x_359;
x_190 = x_360;
goto block_212;
}
}
else
{
lean_object* x_361; lean_object* x_362; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_147);
lean_dec(x_136);
x_361 = lean_ctor_get(x_340, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_340, 1);
lean_inc(x_362);
lean_dec(x_340);
x_189 = x_361;
x_190 = x_362;
goto block_212;
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_363 = lean_ctor_get(x_334, 0);
x_364 = lean_ctor_get(x_334, 1);
x_365 = lean_ctor_get(x_334, 2);
x_366 = lean_ctor_get(x_334, 3);
x_367 = lean_ctor_get(x_334, 4);
x_368 = lean_ctor_get(x_334, 5);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_inc(x_364);
lean_inc(x_363);
lean_dec(x_334);
x_369 = l_Lean_MetavarContext_assignExpr(x_364, x_145, x_335);
x_370 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_370, 0, x_363);
lean_ctor_set(x_370, 1, x_369);
lean_ctor_set(x_370, 2, x_365);
lean_ctor_set(x_370, 3, x_366);
lean_ctor_set(x_370, 4, x_367);
lean_ctor_set(x_370, 5, x_368);
x_371 = l_Lean_Expr_mvarId_x21(x_331);
lean_dec(x_331);
x_372 = l_Lean_Meta_clear(x_371, x_149, x_159, x_370);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
lean_dec(x_372);
x_375 = l_Lean_Meta_clear(x_373, x_147, x_159, x_374);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec(x_375);
x_378 = lean_array_get_size(x_136);
lean_dec(x_136);
x_379 = lean_nat_sub(x_378, x_104);
lean_dec(x_378);
x_380 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_376, x_379, x_138, x_159, x_377);
lean_dec(x_159);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_143);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_384 = x_381;
} else {
 lean_dec_ref(x_381);
 x_384 = lean_box(0);
}
x_385 = lean_box(0);
if (lean_is_scalar(x_384)) {
 x_386 = lean_alloc_ctor(0, 2, 0);
} else {
 x_386 = x_384;
}
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_383);
x_165 = x_386;
x_166 = x_382;
goto block_188;
}
else
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_154);
x_387 = lean_ctor_get(x_380, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_380, 1);
lean_inc(x_388);
lean_dec(x_380);
x_189 = x_387;
x_190 = x_388;
goto block_212;
}
}
else
{
lean_object* x_389; lean_object* x_390; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_136);
x_389 = lean_ctor_get(x_375, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_375, 1);
lean_inc(x_390);
lean_dec(x_375);
x_189 = x_389;
x_190 = x_390;
goto block_212;
}
}
else
{
lean_object* x_391; lean_object* x_392; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_147);
lean_dec(x_136);
x_391 = lean_ctor_get(x_372, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_372, 1);
lean_inc(x_392);
lean_dec(x_372);
x_189 = x_391;
x_190 = x_392;
goto block_212;
}
}
}
else
{
lean_object* x_393; lean_object* x_394; 
lean_dec(x_331);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
x_393 = lean_ctor_get(x_333, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_333, 1);
lean_inc(x_394);
lean_dec(x_333);
x_189 = x_393;
x_190 = x_394;
goto block_212;
}
}
else
{
lean_object* x_395; lean_object* x_396; 
lean_dec(x_324);
lean_dec(x_316);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_395 = lean_ctor_get(x_326, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_326, 1);
lean_inc(x_396);
lean_dec(x_326);
x_189 = x_395;
x_190 = x_396;
goto block_212;
}
}
else
{
lean_object* x_397; lean_object* x_398; 
lean_dec(x_316);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_397 = lean_ctor_get(x_323, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_323, 1);
lean_inc(x_398);
lean_dec(x_323);
x_189 = x_397;
x_190 = x_398;
goto block_212;
}
}
else
{
lean_object* x_399; lean_object* x_400; 
lean_dec(x_316);
lean_dec(x_314);
lean_dec(x_216);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_399 = lean_ctor_get(x_317, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_317, 1);
lean_inc(x_400);
lean_dec(x_317);
x_189 = x_399;
x_190 = x_400;
goto block_212;
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_314);
lean_dec(x_220);
x_401 = lean_array_push(x_129, x_148);
lean_inc(x_150);
x_402 = lean_array_push(x_401, x_150);
lean_inc(x_159);
x_403 = l_Lean_Meta_mkLambda(x_402, x_216, x_159, x_313);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
x_406 = 2;
lean_inc(x_159);
x_407 = l_Lean_Meta_mkFreshExprMVar(x_316, x_82, x_406, x_159, x_405);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
lean_inc(x_159);
lean_inc(x_408);
x_410 = l_Lean_Meta_mkEqRec(x_404, x_408, x_150, x_159, x_409);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; uint8_t x_413; 
x_411 = lean_ctor_get(x_410, 1);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 0);
lean_inc(x_412);
lean_dec(x_410);
x_413 = !lean_is_exclusive(x_411);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_414 = lean_ctor_get(x_411, 1);
x_415 = l_Lean_MetavarContext_assignExpr(x_414, x_145, x_412);
lean_ctor_set(x_411, 1, x_415);
x_416 = l_Lean_Expr_mvarId_x21(x_408);
lean_dec(x_408);
x_417 = l_Lean_Meta_clear(x_416, x_149, x_159, x_411);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
x_420 = l_Lean_Meta_clear(x_418, x_147, x_159, x_419);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_array_get_size(x_136);
lean_dec(x_136);
x_424 = lean_nat_sub(x_423, x_104);
lean_dec(x_423);
x_425 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_421, x_424, x_138, x_159, x_422);
lean_dec(x_159);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; uint8_t x_428; 
lean_dec(x_143);
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec(x_425);
x_428 = !lean_is_exclusive(x_426);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; 
x_429 = lean_ctor_get(x_426, 0);
lean_dec(x_429);
x_430 = lean_box(0);
lean_ctor_set(x_426, 0, x_430);
x_165 = x_426;
x_166 = x_427;
goto block_188;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_426, 1);
lean_inc(x_431);
lean_dec(x_426);
x_432 = lean_box(0);
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_431);
x_165 = x_433;
x_166 = x_427;
goto block_188;
}
}
else
{
lean_object* x_434; lean_object* x_435; 
lean_dec(x_154);
x_434 = lean_ctor_get(x_425, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_425, 1);
lean_inc(x_435);
lean_dec(x_425);
x_189 = x_434;
x_190 = x_435;
goto block_212;
}
}
else
{
lean_object* x_436; lean_object* x_437; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_136);
x_436 = lean_ctor_get(x_420, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_420, 1);
lean_inc(x_437);
lean_dec(x_420);
x_189 = x_436;
x_190 = x_437;
goto block_212;
}
}
else
{
lean_object* x_438; lean_object* x_439; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_147);
lean_dec(x_136);
x_438 = lean_ctor_get(x_417, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_417, 1);
lean_inc(x_439);
lean_dec(x_417);
x_189 = x_438;
x_190 = x_439;
goto block_212;
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_440 = lean_ctor_get(x_411, 0);
x_441 = lean_ctor_get(x_411, 1);
x_442 = lean_ctor_get(x_411, 2);
x_443 = lean_ctor_get(x_411, 3);
x_444 = lean_ctor_get(x_411, 4);
x_445 = lean_ctor_get(x_411, 5);
lean_inc(x_445);
lean_inc(x_444);
lean_inc(x_443);
lean_inc(x_442);
lean_inc(x_441);
lean_inc(x_440);
lean_dec(x_411);
x_446 = l_Lean_MetavarContext_assignExpr(x_441, x_145, x_412);
x_447 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_447, 0, x_440);
lean_ctor_set(x_447, 1, x_446);
lean_ctor_set(x_447, 2, x_442);
lean_ctor_set(x_447, 3, x_443);
lean_ctor_set(x_447, 4, x_444);
lean_ctor_set(x_447, 5, x_445);
x_448 = l_Lean_Expr_mvarId_x21(x_408);
lean_dec(x_408);
x_449 = l_Lean_Meta_clear(x_448, x_149, x_159, x_447);
if (lean_obj_tag(x_449) == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_449, 1);
lean_inc(x_451);
lean_dec(x_449);
x_452 = l_Lean_Meta_clear(x_450, x_147, x_159, x_451);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
lean_dec(x_452);
x_455 = lean_array_get_size(x_136);
lean_dec(x_136);
x_456 = lean_nat_sub(x_455, x_104);
lean_dec(x_455);
x_457 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_453, x_456, x_138, x_159, x_454);
lean_dec(x_159);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_143);
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_457, 1);
lean_inc(x_459);
lean_dec(x_457);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_461 = x_458;
} else {
 lean_dec_ref(x_458);
 x_461 = lean_box(0);
}
x_462 = lean_box(0);
if (lean_is_scalar(x_461)) {
 x_463 = lean_alloc_ctor(0, 2, 0);
} else {
 x_463 = x_461;
}
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_460);
x_165 = x_463;
x_166 = x_459;
goto block_188;
}
else
{
lean_object* x_464; lean_object* x_465; 
lean_dec(x_154);
x_464 = lean_ctor_get(x_457, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_457, 1);
lean_inc(x_465);
lean_dec(x_457);
x_189 = x_464;
x_190 = x_465;
goto block_212;
}
}
else
{
lean_object* x_466; lean_object* x_467; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_136);
x_466 = lean_ctor_get(x_452, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_452, 1);
lean_inc(x_467);
lean_dec(x_452);
x_189 = x_466;
x_190 = x_467;
goto block_212;
}
}
else
{
lean_object* x_468; lean_object* x_469; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_147);
lean_dec(x_136);
x_468 = lean_ctor_get(x_449, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_449, 1);
lean_inc(x_469);
lean_dec(x_449);
x_189 = x_468;
x_190 = x_469;
goto block_212;
}
}
}
else
{
lean_object* x_470; lean_object* x_471; 
lean_dec(x_408);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
x_470 = lean_ctor_get(x_410, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_410, 1);
lean_inc(x_471);
lean_dec(x_410);
x_189 = x_470;
x_190 = x_471;
goto block_212;
}
}
else
{
lean_object* x_472; lean_object* x_473; 
lean_dec(x_316);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_472 = lean_ctor_get(x_403, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_403, 1);
lean_inc(x_473);
lean_dec(x_403);
x_189 = x_472;
x_190 = x_473;
goto block_212;
}
}
}
else
{
lean_object* x_474; lean_object* x_475; 
lean_dec(x_310);
lean_dec(x_220);
lean_dec(x_216);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_474 = lean_ctor_get(x_311, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_311, 1);
lean_inc(x_475);
lean_dec(x_311);
x_189 = x_474;
x_190 = x_475;
goto block_212;
}
}
}
}
else
{
lean_object* x_493; lean_object* x_494; 
lean_dec(x_216);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_493 = lean_ctor_get(x_217, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_217, 1);
lean_inc(x_494);
lean_dec(x_217);
x_189 = x_493;
x_190 = x_494;
goto block_212;
}
}
else
{
lean_object* x_495; lean_object* x_496; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_495 = lean_ctor_get(x_213, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_213, 1);
lean_inc(x_496);
lean_dec(x_213);
x_189 = x_495;
x_190 = x_496;
goto block_212;
}
block_188:
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; uint8_t x_169; 
x_168 = lean_ctor_get(x_166, 2);
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_168, 2);
lean_dec(x_170);
lean_ctor_set(x_168, 2, x_164);
if (lean_is_scalar(x_154)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_154;
}
lean_ctor_set(x_171, 0, x_165);
lean_ctor_set(x_171, 1, x_166);
x_74 = x_171;
goto block_79;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_168, 0);
x_173 = lean_ctor_get(x_168, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_168);
x_174 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
lean_ctor_set(x_174, 2, x_164);
lean_ctor_set(x_166, 2, x_174);
if (lean_is_scalar(x_154)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_154;
}
lean_ctor_set(x_175, 0, x_165);
lean_ctor_set(x_175, 1, x_166);
x_74 = x_175;
goto block_79;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_176 = lean_ctor_get(x_166, 2);
x_177 = lean_ctor_get(x_166, 0);
x_178 = lean_ctor_get(x_166, 1);
x_179 = lean_ctor_get(x_166, 3);
x_180 = lean_ctor_get(x_166, 4);
x_181 = lean_ctor_get(x_166, 5);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_176);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_166);
x_182 = lean_ctor_get(x_176, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_176, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 lean_ctor_release(x_176, 2);
 x_184 = x_176;
} else {
 lean_dec_ref(x_176);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(0, 3, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
lean_ctor_set(x_185, 2, x_164);
x_186 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_186, 0, x_177);
lean_ctor_set(x_186, 1, x_178);
lean_ctor_set(x_186, 2, x_185);
lean_ctor_set(x_186, 3, x_179);
lean_ctor_set(x_186, 4, x_180);
lean_ctor_set(x_186, 5, x_181);
if (lean_is_scalar(x_154)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_154;
}
lean_ctor_set(x_187, 0, x_165);
lean_ctor_set(x_187, 1, x_186);
x_74 = x_187;
goto block_79;
}
}
block_212:
{
uint8_t x_191; 
x_191 = !lean_is_exclusive(x_190);
if (x_191 == 0)
{
lean_object* x_192; uint8_t x_193; 
x_192 = lean_ctor_get(x_190, 2);
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_192, 2);
lean_dec(x_194);
lean_ctor_set(x_192, 2, x_164);
if (lean_is_scalar(x_143)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_143;
 lean_ctor_set_tag(x_195, 1);
}
lean_ctor_set(x_195, 0, x_189);
lean_ctor_set(x_195, 1, x_190);
x_74 = x_195;
goto block_79;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_192, 0);
x_197 = lean_ctor_get(x_192, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_192);
x_198 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
lean_ctor_set(x_198, 2, x_164);
lean_ctor_set(x_190, 2, x_198);
if (lean_is_scalar(x_143)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_143;
 lean_ctor_set_tag(x_199, 1);
}
lean_ctor_set(x_199, 0, x_189);
lean_ctor_set(x_199, 1, x_190);
x_74 = x_199;
goto block_79;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_200 = lean_ctor_get(x_190, 2);
x_201 = lean_ctor_get(x_190, 0);
x_202 = lean_ctor_get(x_190, 1);
x_203 = lean_ctor_get(x_190, 3);
x_204 = lean_ctor_get(x_190, 4);
x_205 = lean_ctor_get(x_190, 5);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_200);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_190);
x_206 = lean_ctor_get(x_200, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_200, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 x_208 = x_200;
} else {
 lean_dec_ref(x_200);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(0, 3, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
lean_ctor_set(x_209, 2, x_164);
x_210 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_210, 0, x_201);
lean_ctor_set(x_210, 1, x_202);
lean_ctor_set(x_210, 2, x_209);
lean_ctor_set(x_210, 3, x_203);
lean_ctor_set(x_210, 4, x_204);
lean_ctor_set(x_210, 5, x_205);
if (lean_is_scalar(x_143)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_143;
 lean_ctor_set_tag(x_211, 1);
}
lean_ctor_set(x_211, 0, x_189);
lean_ctor_set(x_211, 1, x_210);
x_74 = x_211;
goto block_79;
}
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_516; lean_object* x_517; lean_object* x_532; lean_object* x_533; 
x_497 = lean_ctor_get(x_162, 0);
x_498 = lean_ctor_get(x_162, 1);
x_499 = lean_ctor_get(x_162, 2);
lean_inc(x_499);
lean_inc(x_498);
lean_inc(x_497);
lean_dec(x_162);
x_532 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_532, 0, x_497);
lean_ctor_set(x_532, 1, x_498);
lean_ctor_set(x_532, 2, x_80);
lean_ctor_set(x_153, 2, x_532);
lean_inc(x_145);
x_533 = l_Lean_Meta_getMVarDecl(x_145, x_159, x_153);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
lean_dec(x_533);
x_536 = lean_ctor_get(x_534, 2);
lean_inc(x_536);
lean_dec(x_534);
lean_inc(x_159);
lean_inc(x_149);
x_537 = l_Lean_Meta_getLocalDecl(x_149, x_159, x_535);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_719; uint8_t x_720; 
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_537, 1);
lean_inc(x_539);
lean_dec(x_537);
x_719 = l_Lean_LocalDecl_type(x_538);
lean_dec(x_538);
x_720 = l_Lean_Expr_isAppOfArity___main(x_719, x_91, x_92);
if (x_720 == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; 
lean_dec(x_719);
lean_dec(x_536);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_721 = l_Lean_Meta_isClassQuick___main___closed__1;
x_722 = l_unreachable_x21___rarg(x_721);
x_723 = lean_apply_2(x_722, x_159, x_539);
if (lean_obj_tag(x_723) == 0)
{
lean_object* x_724; lean_object* x_725; 
lean_dec(x_143);
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
lean_dec(x_723);
x_500 = x_724;
x_501 = x_725;
goto block_515;
}
else
{
lean_object* x_726; lean_object* x_727; 
lean_dec(x_154);
x_726 = lean_ctor_get(x_723, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_723, 1);
lean_inc(x_727);
lean_dec(x_723);
x_516 = x_726;
x_517 = x_727;
goto block_531;
}
}
else
{
lean_object* x_728; 
x_728 = l_Lean_Expr_getAppNumArgsAux___main(x_719, x_98);
if (x_108 == 0)
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_729 = lean_nat_sub(x_728, x_104);
lean_dec(x_728);
x_730 = lean_nat_sub(x_729, x_100);
lean_dec(x_729);
x_731 = l_Lean_Expr_getRevArg_x21___main(x_719, x_730);
lean_dec(x_719);
x_540 = x_731;
goto block_718;
}
else
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_732 = lean_nat_sub(x_728, x_100);
lean_dec(x_728);
x_733 = lean_nat_sub(x_732, x_100);
lean_dec(x_732);
x_734 = l_Lean_Expr_getRevArg_x21___main(x_719, x_733);
lean_dec(x_719);
x_540 = x_734;
goto block_718;
}
}
block_718:
{
lean_object* x_541; lean_object* x_542; uint8_t x_543; 
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
lean_inc(x_536);
x_542 = l_Lean_MetavarContext_exprDependsOn(x_541, x_536, x_149);
x_543 = lean_unbox(x_542);
lean_dec(x_542);
if (x_543 == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_544 = l_Lean_mkOptionalNode___closed__2;
x_545 = lean_array_push(x_544, x_148);
lean_inc(x_159);
lean_inc(x_536);
lean_inc(x_545);
x_546 = l_Lean_Meta_mkLambda(x_545, x_536, x_159, x_539);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
lean_dec(x_546);
x_549 = lean_expr_abstract(x_536, x_545);
lean_dec(x_545);
lean_dec(x_536);
x_550 = lean_expr_instantiate1(x_549, x_540);
lean_dec(x_540);
lean_dec(x_549);
if (x_108 == 0)
{
lean_object* x_594; 
lean_inc(x_159);
x_594 = l_Lean_Meta_mkEqSymm(x_150, x_159, x_548);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; lean_object* x_596; 
x_595 = lean_ctor_get(x_594, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_594, 1);
lean_inc(x_596);
lean_dec(x_594);
x_551 = x_595;
x_552 = x_596;
goto block_593;
}
else
{
lean_object* x_597; lean_object* x_598; 
lean_dec(x_550);
lean_dec(x_547);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_597 = lean_ctor_get(x_594, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_594, 1);
lean_inc(x_598);
lean_dec(x_594);
x_516 = x_597;
x_517 = x_598;
goto block_531;
}
}
else
{
x_551 = x_150;
x_552 = x_548;
goto block_593;
}
block_593:
{
uint8_t x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_553 = 2;
lean_inc(x_159);
x_554 = l_Lean_Meta_mkFreshExprMVar(x_550, x_82, x_553, x_159, x_552);
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
lean_inc(x_159);
lean_inc(x_555);
x_557 = l_Lean_Meta_mkEqNDRec(x_547, x_555, x_551, x_159, x_556);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_558 = lean_ctor_get(x_557, 1);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 0);
lean_inc(x_559);
lean_dec(x_557);
x_560 = lean_ctor_get(x_558, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_558, 1);
lean_inc(x_561);
x_562 = lean_ctor_get(x_558, 2);
lean_inc(x_562);
x_563 = lean_ctor_get(x_558, 3);
lean_inc(x_563);
x_564 = lean_ctor_get(x_558, 4);
lean_inc(x_564);
x_565 = lean_ctor_get(x_558, 5);
lean_inc(x_565);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 lean_ctor_release(x_558, 1);
 lean_ctor_release(x_558, 2);
 lean_ctor_release(x_558, 3);
 lean_ctor_release(x_558, 4);
 lean_ctor_release(x_558, 5);
 x_566 = x_558;
} else {
 lean_dec_ref(x_558);
 x_566 = lean_box(0);
}
x_567 = l_Lean_MetavarContext_assignExpr(x_561, x_145, x_559);
if (lean_is_scalar(x_566)) {
 x_568 = lean_alloc_ctor(0, 6, 0);
} else {
 x_568 = x_566;
}
lean_ctor_set(x_568, 0, x_560);
lean_ctor_set(x_568, 1, x_567);
lean_ctor_set(x_568, 2, x_562);
lean_ctor_set(x_568, 3, x_563);
lean_ctor_set(x_568, 4, x_564);
lean_ctor_set(x_568, 5, x_565);
x_569 = l_Lean_Expr_mvarId_x21(x_555);
lean_dec(x_555);
x_570 = l_Lean_Meta_clear(x_569, x_149, x_159, x_568);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_570, 1);
lean_inc(x_572);
lean_dec(x_570);
x_573 = l_Lean_Meta_clear(x_571, x_147, x_159, x_572);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec(x_573);
x_576 = lean_array_get_size(x_136);
lean_dec(x_136);
x_577 = lean_nat_sub(x_576, x_104);
lean_dec(x_576);
x_578 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_574, x_577, x_138, x_159, x_575);
lean_dec(x_159);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; 
lean_dec(x_143);
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_578, 1);
lean_inc(x_580);
lean_dec(x_578);
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 lean_ctor_release(x_579, 1);
 x_582 = x_579;
} else {
 lean_dec_ref(x_579);
 x_582 = lean_box(0);
}
x_583 = lean_box(0);
if (lean_is_scalar(x_582)) {
 x_584 = lean_alloc_ctor(0, 2, 0);
} else {
 x_584 = x_582;
}
lean_ctor_set(x_584, 0, x_583);
lean_ctor_set(x_584, 1, x_581);
x_500 = x_584;
x_501 = x_580;
goto block_515;
}
else
{
lean_object* x_585; lean_object* x_586; 
lean_dec(x_154);
x_585 = lean_ctor_get(x_578, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_578, 1);
lean_inc(x_586);
lean_dec(x_578);
x_516 = x_585;
x_517 = x_586;
goto block_531;
}
}
else
{
lean_object* x_587; lean_object* x_588; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_136);
x_587 = lean_ctor_get(x_573, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_573, 1);
lean_inc(x_588);
lean_dec(x_573);
x_516 = x_587;
x_517 = x_588;
goto block_531;
}
}
else
{
lean_object* x_589; lean_object* x_590; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_147);
lean_dec(x_136);
x_589 = lean_ctor_get(x_570, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_570, 1);
lean_inc(x_590);
lean_dec(x_570);
x_516 = x_589;
x_517 = x_590;
goto block_531;
}
}
else
{
lean_object* x_591; lean_object* x_592; 
lean_dec(x_555);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
x_591 = lean_ctor_get(x_557, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_557, 1);
lean_inc(x_592);
lean_dec(x_557);
x_516 = x_591;
x_517 = x_592;
goto block_531;
}
}
}
else
{
lean_object* x_599; lean_object* x_600; 
lean_dec(x_545);
lean_dec(x_540);
lean_dec(x_536);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_599 = lean_ctor_get(x_546, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_546, 1);
lean_inc(x_600);
lean_dec(x_546);
x_516 = x_599;
x_517 = x_600;
goto block_531;
}
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_601 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_148);
x_602 = lean_array_push(x_601, x_148);
x_603 = lean_expr_abstract(x_536, x_602);
lean_dec(x_602);
x_604 = lean_expr_instantiate1(x_603, x_540);
lean_dec(x_603);
lean_inc(x_159);
lean_inc(x_540);
x_605 = l_Lean_Meta_mkEqRefl(x_540, x_159, x_539);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_605, 1);
lean_inc(x_607);
lean_dec(x_605);
lean_inc(x_150);
x_608 = lean_array_push(x_601, x_150);
x_609 = lean_expr_abstract(x_604, x_608);
lean_dec(x_604);
x_610 = lean_expr_instantiate1(x_609, x_606);
lean_dec(x_606);
lean_dec(x_609);
if (x_108 == 0)
{
lean_object* x_611; 
lean_inc(x_159);
lean_inc(x_148);
x_611 = l_Lean_Meta_mkEq(x_540, x_148, x_159, x_607);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; uint8_t x_616; lean_object* x_617; 
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_611, 1);
lean_inc(x_613);
lean_dec(x_611);
x_614 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__1___boxed), 7, 4);
lean_closure_set(x_614, 0, x_536);
lean_closure_set(x_614, 1, x_608);
lean_closure_set(x_614, 2, x_129);
lean_closure_set(x_614, 3, x_148);
x_615 = l_Lean_Meta_substCore___closed__18;
x_616 = 0;
lean_inc(x_159);
x_617 = l_Lean_Meta_withLocalDecl___rarg(x_615, x_612, x_616, x_614, x_159, x_613);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_617, 1);
lean_inc(x_619);
lean_dec(x_617);
lean_inc(x_159);
x_620 = l_Lean_Meta_mkEqSymm(x_150, x_159, x_619);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; lean_object* x_622; uint8_t x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 1);
lean_inc(x_622);
lean_dec(x_620);
x_623 = 2;
lean_inc(x_159);
x_624 = l_Lean_Meta_mkFreshExprMVar(x_610, x_82, x_623, x_159, x_622);
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_624, 1);
lean_inc(x_626);
lean_dec(x_624);
lean_inc(x_159);
lean_inc(x_625);
x_627 = l_Lean_Meta_mkEqRec(x_618, x_625, x_621, x_159, x_626);
if (lean_obj_tag(x_627) == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_628 = lean_ctor_get(x_627, 1);
lean_inc(x_628);
x_629 = lean_ctor_get(x_627, 0);
lean_inc(x_629);
lean_dec(x_627);
x_630 = lean_ctor_get(x_628, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_628, 1);
lean_inc(x_631);
x_632 = lean_ctor_get(x_628, 2);
lean_inc(x_632);
x_633 = lean_ctor_get(x_628, 3);
lean_inc(x_633);
x_634 = lean_ctor_get(x_628, 4);
lean_inc(x_634);
x_635 = lean_ctor_get(x_628, 5);
lean_inc(x_635);
if (lean_is_exclusive(x_628)) {
 lean_ctor_release(x_628, 0);
 lean_ctor_release(x_628, 1);
 lean_ctor_release(x_628, 2);
 lean_ctor_release(x_628, 3);
 lean_ctor_release(x_628, 4);
 lean_ctor_release(x_628, 5);
 x_636 = x_628;
} else {
 lean_dec_ref(x_628);
 x_636 = lean_box(0);
}
x_637 = l_Lean_MetavarContext_assignExpr(x_631, x_145, x_629);
if (lean_is_scalar(x_636)) {
 x_638 = lean_alloc_ctor(0, 6, 0);
} else {
 x_638 = x_636;
}
lean_ctor_set(x_638, 0, x_630);
lean_ctor_set(x_638, 1, x_637);
lean_ctor_set(x_638, 2, x_632);
lean_ctor_set(x_638, 3, x_633);
lean_ctor_set(x_638, 4, x_634);
lean_ctor_set(x_638, 5, x_635);
x_639 = l_Lean_Expr_mvarId_x21(x_625);
lean_dec(x_625);
x_640 = l_Lean_Meta_clear(x_639, x_149, x_159, x_638);
if (lean_obj_tag(x_640) == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_641 = lean_ctor_get(x_640, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_640, 1);
lean_inc(x_642);
lean_dec(x_640);
x_643 = l_Lean_Meta_clear(x_641, x_147, x_159, x_642);
if (lean_obj_tag(x_643) == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_643, 1);
lean_inc(x_645);
lean_dec(x_643);
x_646 = lean_array_get_size(x_136);
lean_dec(x_136);
x_647 = lean_nat_sub(x_646, x_104);
lean_dec(x_646);
x_648 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_644, x_647, x_138, x_159, x_645);
lean_dec(x_159);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
lean_dec(x_143);
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_648, 1);
lean_inc(x_650);
lean_dec(x_648);
x_651 = lean_ctor_get(x_649, 1);
lean_inc(x_651);
if (lean_is_exclusive(x_649)) {
 lean_ctor_release(x_649, 0);
 lean_ctor_release(x_649, 1);
 x_652 = x_649;
} else {
 lean_dec_ref(x_649);
 x_652 = lean_box(0);
}
x_653 = lean_box(0);
if (lean_is_scalar(x_652)) {
 x_654 = lean_alloc_ctor(0, 2, 0);
} else {
 x_654 = x_652;
}
lean_ctor_set(x_654, 0, x_653);
lean_ctor_set(x_654, 1, x_651);
x_500 = x_654;
x_501 = x_650;
goto block_515;
}
else
{
lean_object* x_655; lean_object* x_656; 
lean_dec(x_154);
x_655 = lean_ctor_get(x_648, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_648, 1);
lean_inc(x_656);
lean_dec(x_648);
x_516 = x_655;
x_517 = x_656;
goto block_531;
}
}
else
{
lean_object* x_657; lean_object* x_658; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_136);
x_657 = lean_ctor_get(x_643, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_643, 1);
lean_inc(x_658);
lean_dec(x_643);
x_516 = x_657;
x_517 = x_658;
goto block_531;
}
}
else
{
lean_object* x_659; lean_object* x_660; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_147);
lean_dec(x_136);
x_659 = lean_ctor_get(x_640, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_640, 1);
lean_inc(x_660);
lean_dec(x_640);
x_516 = x_659;
x_517 = x_660;
goto block_531;
}
}
else
{
lean_object* x_661; lean_object* x_662; 
lean_dec(x_625);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
x_661 = lean_ctor_get(x_627, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_627, 1);
lean_inc(x_662);
lean_dec(x_627);
x_516 = x_661;
x_517 = x_662;
goto block_531;
}
}
else
{
lean_object* x_663; lean_object* x_664; 
lean_dec(x_618);
lean_dec(x_610);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_663 = lean_ctor_get(x_620, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_620, 1);
lean_inc(x_664);
lean_dec(x_620);
x_516 = x_663;
x_517 = x_664;
goto block_531;
}
}
else
{
lean_object* x_665; lean_object* x_666; 
lean_dec(x_610);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_665 = lean_ctor_get(x_617, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_617, 1);
lean_inc(x_666);
lean_dec(x_617);
x_516 = x_665;
x_517 = x_666;
goto block_531;
}
}
else
{
lean_object* x_667; lean_object* x_668; 
lean_dec(x_610);
lean_dec(x_608);
lean_dec(x_536);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_667 = lean_ctor_get(x_611, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_611, 1);
lean_inc(x_668);
lean_dec(x_611);
x_516 = x_667;
x_517 = x_668;
goto block_531;
}
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; 
lean_dec(x_608);
lean_dec(x_540);
x_669 = lean_array_push(x_129, x_148);
lean_inc(x_150);
x_670 = lean_array_push(x_669, x_150);
lean_inc(x_159);
x_671 = l_Lean_Meta_mkLambda(x_670, x_536, x_159, x_607);
if (lean_obj_tag(x_671) == 0)
{
lean_object* x_672; lean_object* x_673; uint8_t x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_672 = lean_ctor_get(x_671, 0);
lean_inc(x_672);
x_673 = lean_ctor_get(x_671, 1);
lean_inc(x_673);
lean_dec(x_671);
x_674 = 2;
lean_inc(x_159);
x_675 = l_Lean_Meta_mkFreshExprMVar(x_610, x_82, x_674, x_159, x_673);
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_675, 1);
lean_inc(x_677);
lean_dec(x_675);
lean_inc(x_159);
lean_inc(x_676);
x_678 = l_Lean_Meta_mkEqRec(x_672, x_676, x_150, x_159, x_677);
if (lean_obj_tag(x_678) == 0)
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_679 = lean_ctor_get(x_678, 1);
lean_inc(x_679);
x_680 = lean_ctor_get(x_678, 0);
lean_inc(x_680);
lean_dec(x_678);
x_681 = lean_ctor_get(x_679, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_679, 1);
lean_inc(x_682);
x_683 = lean_ctor_get(x_679, 2);
lean_inc(x_683);
x_684 = lean_ctor_get(x_679, 3);
lean_inc(x_684);
x_685 = lean_ctor_get(x_679, 4);
lean_inc(x_685);
x_686 = lean_ctor_get(x_679, 5);
lean_inc(x_686);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 lean_ctor_release(x_679, 2);
 lean_ctor_release(x_679, 3);
 lean_ctor_release(x_679, 4);
 lean_ctor_release(x_679, 5);
 x_687 = x_679;
} else {
 lean_dec_ref(x_679);
 x_687 = lean_box(0);
}
x_688 = l_Lean_MetavarContext_assignExpr(x_682, x_145, x_680);
if (lean_is_scalar(x_687)) {
 x_689 = lean_alloc_ctor(0, 6, 0);
} else {
 x_689 = x_687;
}
lean_ctor_set(x_689, 0, x_681);
lean_ctor_set(x_689, 1, x_688);
lean_ctor_set(x_689, 2, x_683);
lean_ctor_set(x_689, 3, x_684);
lean_ctor_set(x_689, 4, x_685);
lean_ctor_set(x_689, 5, x_686);
x_690 = l_Lean_Expr_mvarId_x21(x_676);
lean_dec(x_676);
x_691 = l_Lean_Meta_clear(x_690, x_149, x_159, x_689);
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; 
x_692 = lean_ctor_get(x_691, 0);
lean_inc(x_692);
x_693 = lean_ctor_get(x_691, 1);
lean_inc(x_693);
lean_dec(x_691);
x_694 = l_Lean_Meta_clear(x_692, x_147, x_159, x_693);
if (lean_obj_tag(x_694) == 0)
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_695 = lean_ctor_get(x_694, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_694, 1);
lean_inc(x_696);
lean_dec(x_694);
x_697 = lean_array_get_size(x_136);
lean_dec(x_136);
x_698 = lean_nat_sub(x_697, x_104);
lean_dec(x_697);
x_699 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_695, x_698, x_138, x_159, x_696);
lean_dec(x_159);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
lean_dec(x_143);
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_699, 1);
lean_inc(x_701);
lean_dec(x_699);
x_702 = lean_ctor_get(x_700, 1);
lean_inc(x_702);
if (lean_is_exclusive(x_700)) {
 lean_ctor_release(x_700, 0);
 lean_ctor_release(x_700, 1);
 x_703 = x_700;
} else {
 lean_dec_ref(x_700);
 x_703 = lean_box(0);
}
x_704 = lean_box(0);
if (lean_is_scalar(x_703)) {
 x_705 = lean_alloc_ctor(0, 2, 0);
} else {
 x_705 = x_703;
}
lean_ctor_set(x_705, 0, x_704);
lean_ctor_set(x_705, 1, x_702);
x_500 = x_705;
x_501 = x_701;
goto block_515;
}
else
{
lean_object* x_706; lean_object* x_707; 
lean_dec(x_154);
x_706 = lean_ctor_get(x_699, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_699, 1);
lean_inc(x_707);
lean_dec(x_699);
x_516 = x_706;
x_517 = x_707;
goto block_531;
}
}
else
{
lean_object* x_708; lean_object* x_709; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_136);
x_708 = lean_ctor_get(x_694, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_694, 1);
lean_inc(x_709);
lean_dec(x_694);
x_516 = x_708;
x_517 = x_709;
goto block_531;
}
}
else
{
lean_object* x_710; lean_object* x_711; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_147);
lean_dec(x_136);
x_710 = lean_ctor_get(x_691, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_691, 1);
lean_inc(x_711);
lean_dec(x_691);
x_516 = x_710;
x_517 = x_711;
goto block_531;
}
}
else
{
lean_object* x_712; lean_object* x_713; 
lean_dec(x_676);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
x_712 = lean_ctor_get(x_678, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_678, 1);
lean_inc(x_713);
lean_dec(x_678);
x_516 = x_712;
x_517 = x_713;
goto block_531;
}
}
else
{
lean_object* x_714; lean_object* x_715; 
lean_dec(x_610);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_714 = lean_ctor_get(x_671, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_671, 1);
lean_inc(x_715);
lean_dec(x_671);
x_516 = x_714;
x_517 = x_715;
goto block_531;
}
}
}
else
{
lean_object* x_716; lean_object* x_717; 
lean_dec(x_604);
lean_dec(x_540);
lean_dec(x_536);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_716 = lean_ctor_get(x_605, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_605, 1);
lean_inc(x_717);
lean_dec(x_605);
x_516 = x_716;
x_517 = x_717;
goto block_531;
}
}
}
}
else
{
lean_object* x_735; lean_object* x_736; 
lean_dec(x_536);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_735 = lean_ctor_get(x_537, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_537, 1);
lean_inc(x_736);
lean_dec(x_537);
x_516 = x_735;
x_517 = x_736;
goto block_531;
}
}
else
{
lean_object* x_737; lean_object* x_738; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_737 = lean_ctor_get(x_533, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_533, 1);
lean_inc(x_738);
lean_dec(x_533);
x_516 = x_737;
x_517 = x_738;
goto block_531;
}
block_515:
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_502 = lean_ctor_get(x_501, 2);
lean_inc(x_502);
x_503 = lean_ctor_get(x_501, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_501, 1);
lean_inc(x_504);
x_505 = lean_ctor_get(x_501, 3);
lean_inc(x_505);
x_506 = lean_ctor_get(x_501, 4);
lean_inc(x_506);
x_507 = lean_ctor_get(x_501, 5);
lean_inc(x_507);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 lean_ctor_release(x_501, 2);
 lean_ctor_release(x_501, 3);
 lean_ctor_release(x_501, 4);
 lean_ctor_release(x_501, 5);
 x_508 = x_501;
} else {
 lean_dec_ref(x_501);
 x_508 = lean_box(0);
}
x_509 = lean_ctor_get(x_502, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_502, 1);
lean_inc(x_510);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 lean_ctor_release(x_502, 2);
 x_511 = x_502;
} else {
 lean_dec_ref(x_502);
 x_511 = lean_box(0);
}
if (lean_is_scalar(x_511)) {
 x_512 = lean_alloc_ctor(0, 3, 0);
} else {
 x_512 = x_511;
}
lean_ctor_set(x_512, 0, x_509);
lean_ctor_set(x_512, 1, x_510);
lean_ctor_set(x_512, 2, x_499);
if (lean_is_scalar(x_508)) {
 x_513 = lean_alloc_ctor(0, 6, 0);
} else {
 x_513 = x_508;
}
lean_ctor_set(x_513, 0, x_503);
lean_ctor_set(x_513, 1, x_504);
lean_ctor_set(x_513, 2, x_512);
lean_ctor_set(x_513, 3, x_505);
lean_ctor_set(x_513, 4, x_506);
lean_ctor_set(x_513, 5, x_507);
if (lean_is_scalar(x_154)) {
 x_514 = lean_alloc_ctor(0, 2, 0);
} else {
 x_514 = x_154;
}
lean_ctor_set(x_514, 0, x_500);
lean_ctor_set(x_514, 1, x_513);
x_74 = x_514;
goto block_79;
}
block_531:
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_518 = lean_ctor_get(x_517, 2);
lean_inc(x_518);
x_519 = lean_ctor_get(x_517, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_517, 1);
lean_inc(x_520);
x_521 = lean_ctor_get(x_517, 3);
lean_inc(x_521);
x_522 = lean_ctor_get(x_517, 4);
lean_inc(x_522);
x_523 = lean_ctor_get(x_517, 5);
lean_inc(x_523);
if (lean_is_exclusive(x_517)) {
 lean_ctor_release(x_517, 0);
 lean_ctor_release(x_517, 1);
 lean_ctor_release(x_517, 2);
 lean_ctor_release(x_517, 3);
 lean_ctor_release(x_517, 4);
 lean_ctor_release(x_517, 5);
 x_524 = x_517;
} else {
 lean_dec_ref(x_517);
 x_524 = lean_box(0);
}
x_525 = lean_ctor_get(x_518, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_518, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 lean_ctor_release(x_518, 2);
 x_527 = x_518;
} else {
 lean_dec_ref(x_518);
 x_527 = lean_box(0);
}
if (lean_is_scalar(x_527)) {
 x_528 = lean_alloc_ctor(0, 3, 0);
} else {
 x_528 = x_527;
}
lean_ctor_set(x_528, 0, x_525);
lean_ctor_set(x_528, 1, x_526);
lean_ctor_set(x_528, 2, x_499);
if (lean_is_scalar(x_524)) {
 x_529 = lean_alloc_ctor(0, 6, 0);
} else {
 x_529 = x_524;
}
lean_ctor_set(x_529, 0, x_519);
lean_ctor_set(x_529, 1, x_520);
lean_ctor_set(x_529, 2, x_528);
lean_ctor_set(x_529, 3, x_521);
lean_ctor_set(x_529, 4, x_522);
lean_ctor_set(x_529, 5, x_523);
if (lean_is_scalar(x_143)) {
 x_530 = lean_alloc_ctor(1, 2, 0);
} else {
 x_530 = x_143;
 lean_ctor_set_tag(x_530, 1);
}
lean_ctor_set(x_530, 0, x_516);
lean_ctor_set(x_530, 1, x_529);
x_74 = x_530;
goto block_79;
}
}
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_765; lean_object* x_766; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
x_739 = lean_ctor_get(x_153, 2);
x_740 = lean_ctor_get(x_153, 0);
x_741 = lean_ctor_get(x_153, 1);
x_742 = lean_ctor_get(x_153, 3);
x_743 = lean_ctor_get(x_153, 4);
x_744 = lean_ctor_get(x_153, 5);
lean_inc(x_744);
lean_inc(x_743);
lean_inc(x_742);
lean_inc(x_739);
lean_inc(x_741);
lean_inc(x_740);
lean_dec(x_153);
x_745 = lean_ctor_get(x_739, 0);
lean_inc(x_745);
x_746 = lean_ctor_get(x_739, 1);
lean_inc(x_746);
x_747 = lean_ctor_get(x_739, 2);
lean_inc(x_747);
if (lean_is_exclusive(x_739)) {
 lean_ctor_release(x_739, 0);
 lean_ctor_release(x_739, 1);
 lean_ctor_release(x_739, 2);
 x_748 = x_739;
} else {
 lean_dec_ref(x_739);
 x_748 = lean_box(0);
}
if (lean_is_scalar(x_748)) {
 x_781 = lean_alloc_ctor(0, 3, 0);
} else {
 x_781 = x_748;
}
lean_ctor_set(x_781, 0, x_745);
lean_ctor_set(x_781, 1, x_746);
lean_ctor_set(x_781, 2, x_80);
x_782 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_782, 0, x_740);
lean_ctor_set(x_782, 1, x_741);
lean_ctor_set(x_782, 2, x_781);
lean_ctor_set(x_782, 3, x_742);
lean_ctor_set(x_782, 4, x_743);
lean_ctor_set(x_782, 5, x_744);
lean_inc(x_145);
x_783 = l_Lean_Meta_getMVarDecl(x_145, x_159, x_782);
if (lean_obj_tag(x_783) == 0)
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_783, 1);
lean_inc(x_785);
lean_dec(x_783);
x_786 = lean_ctor_get(x_784, 2);
lean_inc(x_786);
lean_dec(x_784);
lean_inc(x_159);
lean_inc(x_149);
x_787 = l_Lean_Meta_getLocalDecl(x_149, x_159, x_785);
if (lean_obj_tag(x_787) == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_969; uint8_t x_970; 
x_788 = lean_ctor_get(x_787, 0);
lean_inc(x_788);
x_789 = lean_ctor_get(x_787, 1);
lean_inc(x_789);
lean_dec(x_787);
x_969 = l_Lean_LocalDecl_type(x_788);
lean_dec(x_788);
x_970 = l_Lean_Expr_isAppOfArity___main(x_969, x_91, x_92);
if (x_970 == 0)
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; 
lean_dec(x_969);
lean_dec(x_786);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_971 = l_Lean_Meta_isClassQuick___main___closed__1;
x_972 = l_unreachable_x21___rarg(x_971);
x_973 = lean_apply_2(x_972, x_159, x_789);
if (lean_obj_tag(x_973) == 0)
{
lean_object* x_974; lean_object* x_975; 
lean_dec(x_143);
x_974 = lean_ctor_get(x_973, 0);
lean_inc(x_974);
x_975 = lean_ctor_get(x_973, 1);
lean_inc(x_975);
lean_dec(x_973);
x_749 = x_974;
x_750 = x_975;
goto block_764;
}
else
{
lean_object* x_976; lean_object* x_977; 
lean_dec(x_154);
x_976 = lean_ctor_get(x_973, 0);
lean_inc(x_976);
x_977 = lean_ctor_get(x_973, 1);
lean_inc(x_977);
lean_dec(x_973);
x_765 = x_976;
x_766 = x_977;
goto block_780;
}
}
else
{
lean_object* x_978; 
x_978 = l_Lean_Expr_getAppNumArgsAux___main(x_969, x_98);
if (x_108 == 0)
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; 
x_979 = lean_nat_sub(x_978, x_104);
lean_dec(x_978);
x_980 = lean_nat_sub(x_979, x_100);
lean_dec(x_979);
x_981 = l_Lean_Expr_getRevArg_x21___main(x_969, x_980);
lean_dec(x_969);
x_790 = x_981;
goto block_968;
}
else
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; 
x_982 = lean_nat_sub(x_978, x_100);
lean_dec(x_978);
x_983 = lean_nat_sub(x_982, x_100);
lean_dec(x_982);
x_984 = l_Lean_Expr_getRevArg_x21___main(x_969, x_983);
lean_dec(x_969);
x_790 = x_984;
goto block_968;
}
}
block_968:
{
lean_object* x_791; lean_object* x_792; uint8_t x_793; 
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
lean_inc(x_786);
x_792 = l_Lean_MetavarContext_exprDependsOn(x_791, x_786, x_149);
x_793 = lean_unbox(x_792);
lean_dec(x_792);
if (x_793 == 0)
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; 
x_794 = l_Lean_mkOptionalNode___closed__2;
x_795 = lean_array_push(x_794, x_148);
lean_inc(x_159);
lean_inc(x_786);
lean_inc(x_795);
x_796 = l_Lean_Meta_mkLambda(x_795, x_786, x_159, x_789);
if (lean_obj_tag(x_796) == 0)
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
x_797 = lean_ctor_get(x_796, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_796, 1);
lean_inc(x_798);
lean_dec(x_796);
x_799 = lean_expr_abstract(x_786, x_795);
lean_dec(x_795);
lean_dec(x_786);
x_800 = lean_expr_instantiate1(x_799, x_790);
lean_dec(x_790);
lean_dec(x_799);
if (x_108 == 0)
{
lean_object* x_844; 
lean_inc(x_159);
x_844 = l_Lean_Meta_mkEqSymm(x_150, x_159, x_798);
if (lean_obj_tag(x_844) == 0)
{
lean_object* x_845; lean_object* x_846; 
x_845 = lean_ctor_get(x_844, 0);
lean_inc(x_845);
x_846 = lean_ctor_get(x_844, 1);
lean_inc(x_846);
lean_dec(x_844);
x_801 = x_845;
x_802 = x_846;
goto block_843;
}
else
{
lean_object* x_847; lean_object* x_848; 
lean_dec(x_800);
lean_dec(x_797);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_847 = lean_ctor_get(x_844, 0);
lean_inc(x_847);
x_848 = lean_ctor_get(x_844, 1);
lean_inc(x_848);
lean_dec(x_844);
x_765 = x_847;
x_766 = x_848;
goto block_780;
}
}
else
{
x_801 = x_150;
x_802 = x_798;
goto block_843;
}
block_843:
{
uint8_t x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_803 = 2;
lean_inc(x_159);
x_804 = l_Lean_Meta_mkFreshExprMVar(x_800, x_82, x_803, x_159, x_802);
x_805 = lean_ctor_get(x_804, 0);
lean_inc(x_805);
x_806 = lean_ctor_get(x_804, 1);
lean_inc(x_806);
lean_dec(x_804);
lean_inc(x_159);
lean_inc(x_805);
x_807 = l_Lean_Meta_mkEqNDRec(x_797, x_805, x_801, x_159, x_806);
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_808 = lean_ctor_get(x_807, 1);
lean_inc(x_808);
x_809 = lean_ctor_get(x_807, 0);
lean_inc(x_809);
lean_dec(x_807);
x_810 = lean_ctor_get(x_808, 0);
lean_inc(x_810);
x_811 = lean_ctor_get(x_808, 1);
lean_inc(x_811);
x_812 = lean_ctor_get(x_808, 2);
lean_inc(x_812);
x_813 = lean_ctor_get(x_808, 3);
lean_inc(x_813);
x_814 = lean_ctor_get(x_808, 4);
lean_inc(x_814);
x_815 = lean_ctor_get(x_808, 5);
lean_inc(x_815);
if (lean_is_exclusive(x_808)) {
 lean_ctor_release(x_808, 0);
 lean_ctor_release(x_808, 1);
 lean_ctor_release(x_808, 2);
 lean_ctor_release(x_808, 3);
 lean_ctor_release(x_808, 4);
 lean_ctor_release(x_808, 5);
 x_816 = x_808;
} else {
 lean_dec_ref(x_808);
 x_816 = lean_box(0);
}
x_817 = l_Lean_MetavarContext_assignExpr(x_811, x_145, x_809);
if (lean_is_scalar(x_816)) {
 x_818 = lean_alloc_ctor(0, 6, 0);
} else {
 x_818 = x_816;
}
lean_ctor_set(x_818, 0, x_810);
lean_ctor_set(x_818, 1, x_817);
lean_ctor_set(x_818, 2, x_812);
lean_ctor_set(x_818, 3, x_813);
lean_ctor_set(x_818, 4, x_814);
lean_ctor_set(x_818, 5, x_815);
x_819 = l_Lean_Expr_mvarId_x21(x_805);
lean_dec(x_805);
x_820 = l_Lean_Meta_clear(x_819, x_149, x_159, x_818);
if (lean_obj_tag(x_820) == 0)
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_821 = lean_ctor_get(x_820, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_820, 1);
lean_inc(x_822);
lean_dec(x_820);
x_823 = l_Lean_Meta_clear(x_821, x_147, x_159, x_822);
if (lean_obj_tag(x_823) == 0)
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_824 = lean_ctor_get(x_823, 0);
lean_inc(x_824);
x_825 = lean_ctor_get(x_823, 1);
lean_inc(x_825);
lean_dec(x_823);
x_826 = lean_array_get_size(x_136);
lean_dec(x_136);
x_827 = lean_nat_sub(x_826, x_104);
lean_dec(x_826);
x_828 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_824, x_827, x_138, x_159, x_825);
lean_dec(x_159);
if (lean_obj_tag(x_828) == 0)
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; 
lean_dec(x_143);
x_829 = lean_ctor_get(x_828, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_828, 1);
lean_inc(x_830);
lean_dec(x_828);
x_831 = lean_ctor_get(x_829, 1);
lean_inc(x_831);
if (lean_is_exclusive(x_829)) {
 lean_ctor_release(x_829, 0);
 lean_ctor_release(x_829, 1);
 x_832 = x_829;
} else {
 lean_dec_ref(x_829);
 x_832 = lean_box(0);
}
x_833 = lean_box(0);
if (lean_is_scalar(x_832)) {
 x_834 = lean_alloc_ctor(0, 2, 0);
} else {
 x_834 = x_832;
}
lean_ctor_set(x_834, 0, x_833);
lean_ctor_set(x_834, 1, x_831);
x_749 = x_834;
x_750 = x_830;
goto block_764;
}
else
{
lean_object* x_835; lean_object* x_836; 
lean_dec(x_154);
x_835 = lean_ctor_get(x_828, 0);
lean_inc(x_835);
x_836 = lean_ctor_get(x_828, 1);
lean_inc(x_836);
lean_dec(x_828);
x_765 = x_835;
x_766 = x_836;
goto block_780;
}
}
else
{
lean_object* x_837; lean_object* x_838; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_136);
x_837 = lean_ctor_get(x_823, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_823, 1);
lean_inc(x_838);
lean_dec(x_823);
x_765 = x_837;
x_766 = x_838;
goto block_780;
}
}
else
{
lean_object* x_839; lean_object* x_840; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_147);
lean_dec(x_136);
x_839 = lean_ctor_get(x_820, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_820, 1);
lean_inc(x_840);
lean_dec(x_820);
x_765 = x_839;
x_766 = x_840;
goto block_780;
}
}
else
{
lean_object* x_841; lean_object* x_842; 
lean_dec(x_805);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
x_841 = lean_ctor_get(x_807, 0);
lean_inc(x_841);
x_842 = lean_ctor_get(x_807, 1);
lean_inc(x_842);
lean_dec(x_807);
x_765 = x_841;
x_766 = x_842;
goto block_780;
}
}
}
else
{
lean_object* x_849; lean_object* x_850; 
lean_dec(x_795);
lean_dec(x_790);
lean_dec(x_786);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_849 = lean_ctor_get(x_796, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_796, 1);
lean_inc(x_850);
lean_dec(x_796);
x_765 = x_849;
x_766 = x_850;
goto block_780;
}
}
else
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; 
x_851 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_148);
x_852 = lean_array_push(x_851, x_148);
x_853 = lean_expr_abstract(x_786, x_852);
lean_dec(x_852);
x_854 = lean_expr_instantiate1(x_853, x_790);
lean_dec(x_853);
lean_inc(x_159);
lean_inc(x_790);
x_855 = l_Lean_Meta_mkEqRefl(x_790, x_159, x_789);
if (lean_obj_tag(x_855) == 0)
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; 
x_856 = lean_ctor_get(x_855, 0);
lean_inc(x_856);
x_857 = lean_ctor_get(x_855, 1);
lean_inc(x_857);
lean_dec(x_855);
lean_inc(x_150);
x_858 = lean_array_push(x_851, x_150);
x_859 = lean_expr_abstract(x_854, x_858);
lean_dec(x_854);
x_860 = lean_expr_instantiate1(x_859, x_856);
lean_dec(x_856);
lean_dec(x_859);
if (x_108 == 0)
{
lean_object* x_861; 
lean_inc(x_159);
lean_inc(x_148);
x_861 = l_Lean_Meta_mkEq(x_790, x_148, x_159, x_857);
if (lean_obj_tag(x_861) == 0)
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; uint8_t x_866; lean_object* x_867; 
x_862 = lean_ctor_get(x_861, 0);
lean_inc(x_862);
x_863 = lean_ctor_get(x_861, 1);
lean_inc(x_863);
lean_dec(x_861);
x_864 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__1___boxed), 7, 4);
lean_closure_set(x_864, 0, x_786);
lean_closure_set(x_864, 1, x_858);
lean_closure_set(x_864, 2, x_129);
lean_closure_set(x_864, 3, x_148);
x_865 = l_Lean_Meta_substCore___closed__18;
x_866 = 0;
lean_inc(x_159);
x_867 = l_Lean_Meta_withLocalDecl___rarg(x_865, x_862, x_866, x_864, x_159, x_863);
if (lean_obj_tag(x_867) == 0)
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_868 = lean_ctor_get(x_867, 0);
lean_inc(x_868);
x_869 = lean_ctor_get(x_867, 1);
lean_inc(x_869);
lean_dec(x_867);
lean_inc(x_159);
x_870 = l_Lean_Meta_mkEqSymm(x_150, x_159, x_869);
if (lean_obj_tag(x_870) == 0)
{
lean_object* x_871; lean_object* x_872; uint8_t x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; 
x_871 = lean_ctor_get(x_870, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_870, 1);
lean_inc(x_872);
lean_dec(x_870);
x_873 = 2;
lean_inc(x_159);
x_874 = l_Lean_Meta_mkFreshExprMVar(x_860, x_82, x_873, x_159, x_872);
x_875 = lean_ctor_get(x_874, 0);
lean_inc(x_875);
x_876 = lean_ctor_get(x_874, 1);
lean_inc(x_876);
lean_dec(x_874);
lean_inc(x_159);
lean_inc(x_875);
x_877 = l_Lean_Meta_mkEqRec(x_868, x_875, x_871, x_159, x_876);
if (lean_obj_tag(x_877) == 0)
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
x_878 = lean_ctor_get(x_877, 1);
lean_inc(x_878);
x_879 = lean_ctor_get(x_877, 0);
lean_inc(x_879);
lean_dec(x_877);
x_880 = lean_ctor_get(x_878, 0);
lean_inc(x_880);
x_881 = lean_ctor_get(x_878, 1);
lean_inc(x_881);
x_882 = lean_ctor_get(x_878, 2);
lean_inc(x_882);
x_883 = lean_ctor_get(x_878, 3);
lean_inc(x_883);
x_884 = lean_ctor_get(x_878, 4);
lean_inc(x_884);
x_885 = lean_ctor_get(x_878, 5);
lean_inc(x_885);
if (lean_is_exclusive(x_878)) {
 lean_ctor_release(x_878, 0);
 lean_ctor_release(x_878, 1);
 lean_ctor_release(x_878, 2);
 lean_ctor_release(x_878, 3);
 lean_ctor_release(x_878, 4);
 lean_ctor_release(x_878, 5);
 x_886 = x_878;
} else {
 lean_dec_ref(x_878);
 x_886 = lean_box(0);
}
x_887 = l_Lean_MetavarContext_assignExpr(x_881, x_145, x_879);
if (lean_is_scalar(x_886)) {
 x_888 = lean_alloc_ctor(0, 6, 0);
} else {
 x_888 = x_886;
}
lean_ctor_set(x_888, 0, x_880);
lean_ctor_set(x_888, 1, x_887);
lean_ctor_set(x_888, 2, x_882);
lean_ctor_set(x_888, 3, x_883);
lean_ctor_set(x_888, 4, x_884);
lean_ctor_set(x_888, 5, x_885);
x_889 = l_Lean_Expr_mvarId_x21(x_875);
lean_dec(x_875);
x_890 = l_Lean_Meta_clear(x_889, x_149, x_159, x_888);
if (lean_obj_tag(x_890) == 0)
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; 
x_891 = lean_ctor_get(x_890, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_890, 1);
lean_inc(x_892);
lean_dec(x_890);
x_893 = l_Lean_Meta_clear(x_891, x_147, x_159, x_892);
if (lean_obj_tag(x_893) == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; 
x_894 = lean_ctor_get(x_893, 0);
lean_inc(x_894);
x_895 = lean_ctor_get(x_893, 1);
lean_inc(x_895);
lean_dec(x_893);
x_896 = lean_array_get_size(x_136);
lean_dec(x_136);
x_897 = lean_nat_sub(x_896, x_104);
lean_dec(x_896);
x_898 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_894, x_897, x_138, x_159, x_895);
lean_dec(x_159);
if (lean_obj_tag(x_898) == 0)
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; 
lean_dec(x_143);
x_899 = lean_ctor_get(x_898, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_898, 1);
lean_inc(x_900);
lean_dec(x_898);
x_901 = lean_ctor_get(x_899, 1);
lean_inc(x_901);
if (lean_is_exclusive(x_899)) {
 lean_ctor_release(x_899, 0);
 lean_ctor_release(x_899, 1);
 x_902 = x_899;
} else {
 lean_dec_ref(x_899);
 x_902 = lean_box(0);
}
x_903 = lean_box(0);
if (lean_is_scalar(x_902)) {
 x_904 = lean_alloc_ctor(0, 2, 0);
} else {
 x_904 = x_902;
}
lean_ctor_set(x_904, 0, x_903);
lean_ctor_set(x_904, 1, x_901);
x_749 = x_904;
x_750 = x_900;
goto block_764;
}
else
{
lean_object* x_905; lean_object* x_906; 
lean_dec(x_154);
x_905 = lean_ctor_get(x_898, 0);
lean_inc(x_905);
x_906 = lean_ctor_get(x_898, 1);
lean_inc(x_906);
lean_dec(x_898);
x_765 = x_905;
x_766 = x_906;
goto block_780;
}
}
else
{
lean_object* x_907; lean_object* x_908; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_136);
x_907 = lean_ctor_get(x_893, 0);
lean_inc(x_907);
x_908 = lean_ctor_get(x_893, 1);
lean_inc(x_908);
lean_dec(x_893);
x_765 = x_907;
x_766 = x_908;
goto block_780;
}
}
else
{
lean_object* x_909; lean_object* x_910; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_147);
lean_dec(x_136);
x_909 = lean_ctor_get(x_890, 0);
lean_inc(x_909);
x_910 = lean_ctor_get(x_890, 1);
lean_inc(x_910);
lean_dec(x_890);
x_765 = x_909;
x_766 = x_910;
goto block_780;
}
}
else
{
lean_object* x_911; lean_object* x_912; 
lean_dec(x_875);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
x_911 = lean_ctor_get(x_877, 0);
lean_inc(x_911);
x_912 = lean_ctor_get(x_877, 1);
lean_inc(x_912);
lean_dec(x_877);
x_765 = x_911;
x_766 = x_912;
goto block_780;
}
}
else
{
lean_object* x_913; lean_object* x_914; 
lean_dec(x_868);
lean_dec(x_860);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_913 = lean_ctor_get(x_870, 0);
lean_inc(x_913);
x_914 = lean_ctor_get(x_870, 1);
lean_inc(x_914);
lean_dec(x_870);
x_765 = x_913;
x_766 = x_914;
goto block_780;
}
}
else
{
lean_object* x_915; lean_object* x_916; 
lean_dec(x_860);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_915 = lean_ctor_get(x_867, 0);
lean_inc(x_915);
x_916 = lean_ctor_get(x_867, 1);
lean_inc(x_916);
lean_dec(x_867);
x_765 = x_915;
x_766 = x_916;
goto block_780;
}
}
else
{
lean_object* x_917; lean_object* x_918; 
lean_dec(x_860);
lean_dec(x_858);
lean_dec(x_786);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_917 = lean_ctor_get(x_861, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_861, 1);
lean_inc(x_918);
lean_dec(x_861);
x_765 = x_917;
x_766 = x_918;
goto block_780;
}
}
else
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; 
lean_dec(x_858);
lean_dec(x_790);
x_919 = lean_array_push(x_129, x_148);
lean_inc(x_150);
x_920 = lean_array_push(x_919, x_150);
lean_inc(x_159);
x_921 = l_Lean_Meta_mkLambda(x_920, x_786, x_159, x_857);
if (lean_obj_tag(x_921) == 0)
{
lean_object* x_922; lean_object* x_923; uint8_t x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; 
x_922 = lean_ctor_get(x_921, 0);
lean_inc(x_922);
x_923 = lean_ctor_get(x_921, 1);
lean_inc(x_923);
lean_dec(x_921);
x_924 = 2;
lean_inc(x_159);
x_925 = l_Lean_Meta_mkFreshExprMVar(x_860, x_82, x_924, x_159, x_923);
x_926 = lean_ctor_get(x_925, 0);
lean_inc(x_926);
x_927 = lean_ctor_get(x_925, 1);
lean_inc(x_927);
lean_dec(x_925);
lean_inc(x_159);
lean_inc(x_926);
x_928 = l_Lean_Meta_mkEqRec(x_922, x_926, x_150, x_159, x_927);
if (lean_obj_tag(x_928) == 0)
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; 
x_929 = lean_ctor_get(x_928, 1);
lean_inc(x_929);
x_930 = lean_ctor_get(x_928, 0);
lean_inc(x_930);
lean_dec(x_928);
x_931 = lean_ctor_get(x_929, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_929, 1);
lean_inc(x_932);
x_933 = lean_ctor_get(x_929, 2);
lean_inc(x_933);
x_934 = lean_ctor_get(x_929, 3);
lean_inc(x_934);
x_935 = lean_ctor_get(x_929, 4);
lean_inc(x_935);
x_936 = lean_ctor_get(x_929, 5);
lean_inc(x_936);
if (lean_is_exclusive(x_929)) {
 lean_ctor_release(x_929, 0);
 lean_ctor_release(x_929, 1);
 lean_ctor_release(x_929, 2);
 lean_ctor_release(x_929, 3);
 lean_ctor_release(x_929, 4);
 lean_ctor_release(x_929, 5);
 x_937 = x_929;
} else {
 lean_dec_ref(x_929);
 x_937 = lean_box(0);
}
x_938 = l_Lean_MetavarContext_assignExpr(x_932, x_145, x_930);
if (lean_is_scalar(x_937)) {
 x_939 = lean_alloc_ctor(0, 6, 0);
} else {
 x_939 = x_937;
}
lean_ctor_set(x_939, 0, x_931);
lean_ctor_set(x_939, 1, x_938);
lean_ctor_set(x_939, 2, x_933);
lean_ctor_set(x_939, 3, x_934);
lean_ctor_set(x_939, 4, x_935);
lean_ctor_set(x_939, 5, x_936);
x_940 = l_Lean_Expr_mvarId_x21(x_926);
lean_dec(x_926);
x_941 = l_Lean_Meta_clear(x_940, x_149, x_159, x_939);
if (lean_obj_tag(x_941) == 0)
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; 
x_942 = lean_ctor_get(x_941, 0);
lean_inc(x_942);
x_943 = lean_ctor_get(x_941, 1);
lean_inc(x_943);
lean_dec(x_941);
x_944 = l_Lean_Meta_clear(x_942, x_147, x_159, x_943);
if (lean_obj_tag(x_944) == 0)
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; 
x_945 = lean_ctor_get(x_944, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_944, 1);
lean_inc(x_946);
lean_dec(x_944);
x_947 = lean_array_get_size(x_136);
lean_dec(x_136);
x_948 = lean_nat_sub(x_947, x_104);
lean_dec(x_947);
x_949 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_139, x_945, x_948, x_138, x_159, x_946);
lean_dec(x_159);
if (lean_obj_tag(x_949) == 0)
{
lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; 
lean_dec(x_143);
x_950 = lean_ctor_get(x_949, 0);
lean_inc(x_950);
x_951 = lean_ctor_get(x_949, 1);
lean_inc(x_951);
lean_dec(x_949);
x_952 = lean_ctor_get(x_950, 1);
lean_inc(x_952);
if (lean_is_exclusive(x_950)) {
 lean_ctor_release(x_950, 0);
 lean_ctor_release(x_950, 1);
 x_953 = x_950;
} else {
 lean_dec_ref(x_950);
 x_953 = lean_box(0);
}
x_954 = lean_box(0);
if (lean_is_scalar(x_953)) {
 x_955 = lean_alloc_ctor(0, 2, 0);
} else {
 x_955 = x_953;
}
lean_ctor_set(x_955, 0, x_954);
lean_ctor_set(x_955, 1, x_952);
x_749 = x_955;
x_750 = x_951;
goto block_764;
}
else
{
lean_object* x_956; lean_object* x_957; 
lean_dec(x_154);
x_956 = lean_ctor_get(x_949, 0);
lean_inc(x_956);
x_957 = lean_ctor_get(x_949, 1);
lean_inc(x_957);
lean_dec(x_949);
x_765 = x_956;
x_766 = x_957;
goto block_780;
}
}
else
{
lean_object* x_958; lean_object* x_959; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_136);
x_958 = lean_ctor_get(x_944, 0);
lean_inc(x_958);
x_959 = lean_ctor_get(x_944, 1);
lean_inc(x_959);
lean_dec(x_944);
x_765 = x_958;
x_766 = x_959;
goto block_780;
}
}
else
{
lean_object* x_960; lean_object* x_961; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_147);
lean_dec(x_136);
x_960 = lean_ctor_get(x_941, 0);
lean_inc(x_960);
x_961 = lean_ctor_get(x_941, 1);
lean_inc(x_961);
lean_dec(x_941);
x_765 = x_960;
x_766 = x_961;
goto block_780;
}
}
else
{
lean_object* x_962; lean_object* x_963; 
lean_dec(x_926);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
x_962 = lean_ctor_get(x_928, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_928, 1);
lean_inc(x_963);
lean_dec(x_928);
x_765 = x_962;
x_766 = x_963;
goto block_780;
}
}
else
{
lean_object* x_964; lean_object* x_965; 
lean_dec(x_860);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_964 = lean_ctor_get(x_921, 0);
lean_inc(x_964);
x_965 = lean_ctor_get(x_921, 1);
lean_inc(x_965);
lean_dec(x_921);
x_765 = x_964;
x_766 = x_965;
goto block_780;
}
}
}
else
{
lean_object* x_966; lean_object* x_967; 
lean_dec(x_854);
lean_dec(x_790);
lean_dec(x_786);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_966 = lean_ctor_get(x_855, 0);
lean_inc(x_966);
x_967 = lean_ctor_get(x_855, 1);
lean_inc(x_967);
lean_dec(x_855);
x_765 = x_966;
x_766 = x_967;
goto block_780;
}
}
}
}
else
{
lean_object* x_985; lean_object* x_986; 
lean_dec(x_786);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_985 = lean_ctor_get(x_787, 0);
lean_inc(x_985);
x_986 = lean_ctor_get(x_787, 1);
lean_inc(x_986);
lean_dec(x_787);
x_765 = x_985;
x_766 = x_986;
goto block_780;
}
}
else
{
lean_object* x_987; lean_object* x_988; 
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_136);
lean_dec(x_82);
x_987 = lean_ctor_get(x_783, 0);
lean_inc(x_987);
x_988 = lean_ctor_get(x_783, 1);
lean_inc(x_988);
lean_dec(x_783);
x_765 = x_987;
x_766 = x_988;
goto block_780;
}
block_764:
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; 
x_751 = lean_ctor_get(x_750, 2);
lean_inc(x_751);
x_752 = lean_ctor_get(x_750, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_750, 1);
lean_inc(x_753);
x_754 = lean_ctor_get(x_750, 3);
lean_inc(x_754);
x_755 = lean_ctor_get(x_750, 4);
lean_inc(x_755);
x_756 = lean_ctor_get(x_750, 5);
lean_inc(x_756);
if (lean_is_exclusive(x_750)) {
 lean_ctor_release(x_750, 0);
 lean_ctor_release(x_750, 1);
 lean_ctor_release(x_750, 2);
 lean_ctor_release(x_750, 3);
 lean_ctor_release(x_750, 4);
 lean_ctor_release(x_750, 5);
 x_757 = x_750;
} else {
 lean_dec_ref(x_750);
 x_757 = lean_box(0);
}
x_758 = lean_ctor_get(x_751, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_751, 1);
lean_inc(x_759);
if (lean_is_exclusive(x_751)) {
 lean_ctor_release(x_751, 0);
 lean_ctor_release(x_751, 1);
 lean_ctor_release(x_751, 2);
 x_760 = x_751;
} else {
 lean_dec_ref(x_751);
 x_760 = lean_box(0);
}
if (lean_is_scalar(x_760)) {
 x_761 = lean_alloc_ctor(0, 3, 0);
} else {
 x_761 = x_760;
}
lean_ctor_set(x_761, 0, x_758);
lean_ctor_set(x_761, 1, x_759);
lean_ctor_set(x_761, 2, x_747);
if (lean_is_scalar(x_757)) {
 x_762 = lean_alloc_ctor(0, 6, 0);
} else {
 x_762 = x_757;
}
lean_ctor_set(x_762, 0, x_752);
lean_ctor_set(x_762, 1, x_753);
lean_ctor_set(x_762, 2, x_761);
lean_ctor_set(x_762, 3, x_754);
lean_ctor_set(x_762, 4, x_755);
lean_ctor_set(x_762, 5, x_756);
if (lean_is_scalar(x_154)) {
 x_763 = lean_alloc_ctor(0, 2, 0);
} else {
 x_763 = x_154;
}
lean_ctor_set(x_763, 0, x_749);
lean_ctor_set(x_763, 1, x_762);
x_74 = x_763;
goto block_79;
}
block_780:
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; 
x_767 = lean_ctor_get(x_766, 2);
lean_inc(x_767);
x_768 = lean_ctor_get(x_766, 0);
lean_inc(x_768);
x_769 = lean_ctor_get(x_766, 1);
lean_inc(x_769);
x_770 = lean_ctor_get(x_766, 3);
lean_inc(x_770);
x_771 = lean_ctor_get(x_766, 4);
lean_inc(x_771);
x_772 = lean_ctor_get(x_766, 5);
lean_inc(x_772);
if (lean_is_exclusive(x_766)) {
 lean_ctor_release(x_766, 0);
 lean_ctor_release(x_766, 1);
 lean_ctor_release(x_766, 2);
 lean_ctor_release(x_766, 3);
 lean_ctor_release(x_766, 4);
 lean_ctor_release(x_766, 5);
 x_773 = x_766;
} else {
 lean_dec_ref(x_766);
 x_773 = lean_box(0);
}
x_774 = lean_ctor_get(x_767, 0);
lean_inc(x_774);
x_775 = lean_ctor_get(x_767, 1);
lean_inc(x_775);
if (lean_is_exclusive(x_767)) {
 lean_ctor_release(x_767, 0);
 lean_ctor_release(x_767, 1);
 lean_ctor_release(x_767, 2);
 x_776 = x_767;
} else {
 lean_dec_ref(x_767);
 x_776 = lean_box(0);
}
if (lean_is_scalar(x_776)) {
 x_777 = lean_alloc_ctor(0, 3, 0);
} else {
 x_777 = x_776;
}
lean_ctor_set(x_777, 0, x_774);
lean_ctor_set(x_777, 1, x_775);
lean_ctor_set(x_777, 2, x_747);
if (lean_is_scalar(x_773)) {
 x_778 = lean_alloc_ctor(0, 6, 0);
} else {
 x_778 = x_773;
}
lean_ctor_set(x_778, 0, x_768);
lean_ctor_set(x_778, 1, x_769);
lean_ctor_set(x_778, 2, x_777);
lean_ctor_set(x_778, 3, x_770);
lean_ctor_set(x_778, 4, x_771);
lean_ctor_set(x_778, 5, x_772);
if (lean_is_scalar(x_143)) {
 x_779 = lean_alloc_ctor(1, 2, 0);
} else {
 x_779 = x_143;
 lean_ctor_set_tag(x_779, 1);
}
lean_ctor_set(x_779, 0, x_765);
lean_ctor_set(x_779, 1, x_778);
x_74 = x_779;
goto block_79;
}
}
}
}
else
{
lean_object* x_1360; lean_object* x_1361; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_143);
lean_dec(x_136);
lean_dec(x_82);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_1360 = lean_ctor_get(x_151, 0);
lean_inc(x_1360);
x_1361 = lean_ctor_get(x_151, 1);
lean_inc(x_1361);
lean_dec(x_151);
x_50 = x_1360;
x_51 = x_1361;
goto block_73;
}
}
else
{
lean_object* x_1362; lean_object* x_1363; 
lean_dec(x_136);
lean_dec(x_82);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_1362 = lean_ctor_get(x_140, 0);
lean_inc(x_1362);
x_1363 = lean_ctor_get(x_140, 1);
lean_inc(x_1363);
lean_dec(x_140);
x_50 = x_1362;
x_51 = x_1363;
goto block_73;
}
}
else
{
lean_object* x_1364; lean_object* x_1365; 
lean_dec(x_82);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_1364 = lean_ctor_get(x_133, 0);
lean_inc(x_1364);
x_1365 = lean_ctor_get(x_133, 1);
lean_inc(x_1365);
lean_dec(x_133);
x_50 = x_1364;
x_51 = x_1365;
goto block_73;
}
}
else
{
lean_object* x_1366; lean_object* x_1367; 
lean_dec(x_125);
lean_dec(x_82);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_1366 = lean_ctor_get(x_127, 0);
lean_inc(x_1366);
x_1367 = lean_ctor_get(x_127, 1);
lean_inc(x_1367);
lean_dec(x_127);
x_50 = x_1366;
x_51 = x_1367;
goto block_73;
}
}
}
else
{
lean_object* x_1383; 
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_82);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_1383 = lean_box(0);
x_109 = x_1383;
goto block_122;
}
}
}
}
}
}
else
{
lean_object* x_1389; lean_object* x_1390; 
lean_dec(x_82);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_1389 = lean_ctor_get(x_87, 0);
lean_inc(x_1389);
x_1390 = lean_ctor_get(x_87, 1);
lean_inc(x_1390);
lean_dec(x_87);
x_50 = x_1389;
x_51 = x_1390;
goto block_73;
}
}
else
{
lean_object* x_1391; lean_object* x_1392; 
lean_dec(x_82);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_1391 = lean_ctor_get(x_85, 0);
lean_inc(x_1391);
x_1392 = lean_ctor_get(x_85, 1);
lean_inc(x_1392);
lean_dec(x_85);
x_50 = x_1391;
x_51 = x_1392;
goto block_73;
}
}
else
{
lean_object* x_1393; lean_object* x_1394; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_1393 = lean_ctor_get(x_81, 0);
lean_inc(x_1393);
x_1394 = lean_ctor_get(x_81, 1);
lean_inc(x_1394);
lean_dec(x_81);
x_50 = x_1393;
x_51 = x_1394;
goto block_73;
}
block_49:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 2);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 2);
lean_dec(x_31);
lean_ctor_set(x_29, 2, x_25);
if (lean_is_scalar(x_10)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_10;
}
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_27, 2, x_35);
if (lean_is_scalar(x_10)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_10;
}
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_27);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_37 = lean_ctor_get(x_27, 2);
x_38 = lean_ctor_get(x_27, 0);
x_39 = lean_ctor_get(x_27, 1);
x_40 = lean_ctor_get(x_27, 3);
x_41 = lean_ctor_get(x_27, 4);
x_42 = lean_ctor_get(x_27, 5);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_37);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_27);
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 3, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_25);
x_47 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_39);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_47, 3, x_40);
lean_ctor_set(x_47, 4, x_41);
lean_ctor_set(x_47, 5, x_42);
if (lean_is_scalar(x_10)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_10;
}
lean_ctor_set(x_48, 0, x_26);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
block_73:
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_51, 2);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 2);
lean_dec(x_55);
lean_ctor_set(x_53, 2, x_25);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_53);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_25);
lean_ctor_set(x_51, 2, x_59);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_51);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_61 = lean_ctor_get(x_51, 2);
x_62 = lean_ctor_get(x_51, 0);
x_63 = lean_ctor_get(x_51, 1);
x_64 = lean_ctor_get(x_51, 3);
x_65 = lean_ctor_get(x_51, 4);
x_66 = lean_ctor_get(x_51, 5);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_61);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_51);
x_67 = lean_ctor_get(x_61, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 lean_ctor_release(x_61, 2);
 x_69 = x_61;
} else {
 lean_dec_ref(x_61);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 3, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_70, 2, x_25);
x_71 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set(x_71, 1, x_63);
lean_ctor_set(x_71, 2, x_70);
lean_ctor_set(x_71, 3, x_64);
lean_ctor_set(x_71, 4, x_65);
lean_ctor_set(x_71, 5, x_66);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_50);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
block_79:
{
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_26 = x_75;
x_27 = x_76;
goto block_49;
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_10);
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_50 = x_77;
x_51 = x_78;
goto block_73;
}
}
}
else
{
lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1414; lean_object* x_1415; lean_object* x_1430; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; 
x_1395 = lean_ctor_get(x_23, 0);
x_1396 = lean_ctor_get(x_23, 1);
x_1397 = lean_ctor_get(x_23, 2);
lean_inc(x_1397);
lean_inc(x_1396);
lean_inc(x_1395);
lean_dec(x_23);
x_1436 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_1437 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1437, 0, x_1395);
lean_ctor_set(x_1437, 1, x_1396);
lean_ctor_set(x_1437, 2, x_1436);
lean_ctor_set(x_9, 2, x_1437);
lean_inc(x_1);
x_1438 = l_Lean_Meta_getMVarTag(x_1, x_20, x_9);
if (lean_obj_tag(x_1438) == 0)
{
lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; 
x_1439 = lean_ctor_get(x_1438, 0);
lean_inc(x_1439);
x_1440 = lean_ctor_get(x_1438, 1);
lean_inc(x_1440);
lean_dec(x_1438);
x_1441 = l_Lean_Meta_substCore___closed__2;
lean_inc(x_1);
x_1442 = l_Lean_Meta_checkNotAssigned(x_1, x_1441, x_20, x_1440);
if (lean_obj_tag(x_1442) == 0)
{
lean_object* x_1443; lean_object* x_1444; 
x_1443 = lean_ctor_get(x_1442, 1);
lean_inc(x_1443);
lean_dec(x_1442);
lean_inc(x_20);
lean_inc(x_2);
x_1444 = l_Lean_Meta_getLocalDecl(x_2, x_20, x_1443);
if (lean_obj_tag(x_1444) == 0)
{
lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; uint8_t x_1450; 
x_1445 = lean_ctor_get(x_1444, 0);
lean_inc(x_1445);
x_1446 = lean_ctor_get(x_1444, 1);
lean_inc(x_1446);
lean_dec(x_1444);
x_1447 = l_Lean_LocalDecl_type(x_1445);
lean_dec(x_1445);
x_1448 = l_Lean_Expr_eq_x3f___closed__2;
x_1449 = lean_unsigned_to_nat(3u);
x_1450 = l_Lean_Expr_isAppOfArity___main(x_1447, x_1448, x_1449);
if (x_1450 == 0)
{
lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; 
lean_dec(x_1447);
lean_dec(x_1439);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_1451 = l_Lean_Meta_substCore___closed__5;
x_1452 = l_Lean_Meta_throwTacticEx___rarg(x_1441, x_1, x_1451, x_20, x_1446);
lean_dec(x_20);
x_1453 = lean_ctor_get(x_1452, 0);
lean_inc(x_1453);
x_1454 = lean_ctor_get(x_1452, 1);
lean_inc(x_1454);
lean_dec(x_1452);
x_1414 = x_1453;
x_1415 = x_1454;
goto block_1429;
}
else
{
lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; uint8_t x_1465; 
x_1455 = lean_unsigned_to_nat(0u);
x_1456 = l_Lean_Expr_getAppNumArgsAux___main(x_1447, x_1455);
x_1457 = lean_unsigned_to_nat(1u);
x_1458 = lean_nat_sub(x_1456, x_1457);
x_1459 = lean_nat_sub(x_1458, x_1457);
lean_dec(x_1458);
x_1460 = l_Lean_Expr_getRevArg_x21___main(x_1447, x_1459);
x_1461 = lean_unsigned_to_nat(2u);
x_1462 = lean_nat_sub(x_1456, x_1461);
lean_dec(x_1456);
x_1463 = lean_nat_sub(x_1462, x_1457);
lean_dec(x_1462);
x_1464 = l_Lean_Expr_getRevArg_x21___main(x_1447, x_1463);
if (x_3 == 0)
{
uint8_t x_2050; 
x_2050 = 0;
x_1465 = x_2050;
goto block_2049;
}
else
{
uint8_t x_2051; 
x_2051 = 1;
x_1465 = x_2051;
goto block_2049;
}
block_2049:
{
lean_object* x_1466; lean_object* x_1480; 
if (x_1465 == 0)
{
lean_inc(x_1460);
x_1480 = x_1460;
goto block_2048;
}
else
{
lean_inc(x_1464);
x_1480 = x_1464;
goto block_2048;
}
block_1479:
{
lean_object* x_1467; lean_object* x_1468; 
lean_dec(x_1466);
x_1467 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1467, 0, x_1447);
x_1468 = l_Lean_indentExpr(x_1467);
if (x_1465 == 0)
{
lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; 
x_1469 = l_Lean_Meta_substCore___closed__12;
x_1470 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1470, 0, x_1469);
lean_ctor_set(x_1470, 1, x_1468);
x_1471 = l_Lean_Meta_throwTacticEx___rarg(x_1441, x_1, x_1470, x_20, x_1446);
lean_dec(x_20);
x_1472 = lean_ctor_get(x_1471, 0);
lean_inc(x_1472);
x_1473 = lean_ctor_get(x_1471, 1);
lean_inc(x_1473);
lean_dec(x_1471);
x_1414 = x_1472;
x_1415 = x_1473;
goto block_1429;
}
else
{
lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; 
x_1474 = l_Lean_Meta_substCore___closed__16;
x_1475 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1475, 0, x_1474);
lean_ctor_set(x_1475, 1, x_1468);
x_1476 = l_Lean_Meta_throwTacticEx___rarg(x_1441, x_1, x_1475, x_20, x_1446);
lean_dec(x_20);
x_1477 = lean_ctor_get(x_1476, 0);
lean_inc(x_1477);
x_1478 = lean_ctor_get(x_1476, 1);
lean_inc(x_1478);
lean_dec(x_1476);
x_1414 = x_1477;
x_1415 = x_1478;
goto block_1429;
}
}
block_2048:
{
lean_object* x_1481; 
if (x_1465 == 0)
{
lean_dec(x_1460);
x_1481 = x_1464;
goto block_2047;
}
else
{
lean_dec(x_1464);
x_1481 = x_1460;
goto block_2047;
}
block_2047:
{
if (lean_obj_tag(x_1480) == 1)
{
lean_object* x_1482; lean_object* x_1483; lean_object* x_2032; lean_object* x_2033; uint8_t x_2034; 
lean_dec(x_1447);
x_1482 = lean_ctor_get(x_1480, 0);
lean_inc(x_1482);
x_2032 = lean_ctor_get(x_1446, 1);
lean_inc(x_2032);
lean_inc(x_1481);
x_2033 = l_Lean_MetavarContext_exprDependsOn(x_2032, x_1481, x_1482);
x_2034 = lean_unbox(x_2033);
lean_dec(x_2033);
if (x_2034 == 0)
{
lean_dec(x_1481);
lean_dec(x_1480);
x_1483 = x_1446;
goto block_2031;
}
else
{
lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; lean_object* x_2041; lean_object* x_2042; lean_object* x_2043; lean_object* x_2044; lean_object* x_2045; 
lean_dec(x_1482);
lean_dec(x_1439);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_2035 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2035, 0, x_1480);
x_2036 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_2037 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2037, 0, x_2036);
lean_ctor_set(x_2037, 1, x_2035);
x_2038 = l_Lean_Meta_substCore___closed__21;
x_2039 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2039, 0, x_2037);
lean_ctor_set(x_2039, 1, x_2038);
x_2040 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2040, 0, x_1481);
x_2041 = l_Lean_indentExpr(x_2040);
x_2042 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2042, 0, x_2039);
lean_ctor_set(x_2042, 1, x_2041);
x_2043 = l_Lean_Meta_throwTacticEx___rarg(x_1441, x_1, x_2042, x_20, x_1446);
lean_dec(x_20);
x_2044 = lean_ctor_get(x_2043, 0);
lean_inc(x_2044);
x_2045 = lean_ctor_get(x_2043, 1);
lean_inc(x_2045);
lean_dec(x_2043);
x_1414 = x_2044;
x_1415 = x_2045;
goto block_1429;
}
block_2031:
{
lean_object* x_1484; 
lean_inc(x_20);
lean_inc(x_1482);
x_1484 = l_Lean_Meta_getLocalDecl(x_1482, x_20, x_1483);
if (lean_obj_tag(x_1484) == 0)
{
lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; uint8_t x_1489; lean_object* x_1490; 
x_1485 = lean_ctor_get(x_1484, 1);
lean_inc(x_1485);
lean_dec(x_1484);
x_1486 = l_Lean_mkAppStx___closed__9;
x_1487 = lean_array_push(x_1486, x_1482);
x_1488 = lean_array_push(x_1487, x_2);
x_1489 = 1;
x_1490 = l_Lean_Meta_revert(x_1, x_1488, x_1489, x_20, x_1485);
if (lean_obj_tag(x_1490) == 0)
{
lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; uint8_t x_1496; lean_object* x_1497; 
x_1491 = lean_ctor_get(x_1490, 0);
lean_inc(x_1491);
x_1492 = lean_ctor_get(x_1490, 1);
lean_inc(x_1492);
lean_dec(x_1490);
x_1493 = lean_ctor_get(x_1491, 0);
lean_inc(x_1493);
x_1494 = lean_ctor_get(x_1491, 1);
lean_inc(x_1494);
lean_dec(x_1491);
x_1495 = lean_box(0);
x_1496 = 0;
x_1497 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1496, x_1494, x_1461, x_1495, x_20, x_1492);
if (lean_obj_tag(x_1497) == 0)
{
lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; 
x_1498 = lean_ctor_get(x_1497, 0);
lean_inc(x_1498);
x_1499 = lean_ctor_get(x_1497, 1);
lean_inc(x_1499);
if (lean_is_exclusive(x_1497)) {
 lean_ctor_release(x_1497, 0);
 lean_ctor_release(x_1497, 1);
 x_1500 = x_1497;
} else {
 lean_dec_ref(x_1497);
 x_1500 = lean_box(0);
}
x_1501 = lean_ctor_get(x_1498, 0);
lean_inc(x_1501);
x_1502 = lean_ctor_get(x_1498, 1);
lean_inc(x_1502);
lean_dec(x_1498);
x_1503 = l_Lean_Name_inhabited;
x_1504 = lean_array_get(x_1503, x_1501, x_1455);
lean_inc(x_1504);
x_1505 = l_Lean_mkFVar(x_1504);
x_1506 = lean_array_get(x_1503, x_1501, x_1457);
lean_dec(x_1501);
lean_inc(x_1506);
x_1507 = l_Lean_mkFVar(x_1506);
lean_inc(x_1502);
x_1508 = l_Lean_Meta_getMVarDecl(x_1502, x_20, x_1499);
lean_dec(x_20);
if (lean_obj_tag(x_1508) == 0)
{
lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; uint8_t x_1515; lean_object* x_1516; lean_object* x_1517; 
x_1509 = lean_ctor_get(x_1508, 0);
lean_inc(x_1509);
x_1510 = lean_ctor_get(x_1508, 1);
lean_inc(x_1510);
if (lean_is_exclusive(x_1508)) {
 lean_ctor_release(x_1508, 0);
 lean_ctor_release(x_1508, 1);
 x_1511 = x_1508;
} else {
 lean_dec_ref(x_1508);
 x_1511 = lean_box(0);
}
x_1512 = lean_ctor_get(x_1509, 1);
lean_inc(x_1512);
x_1513 = lean_ctor_get(x_1509, 4);
lean_inc(x_1513);
x_1514 = lean_array_get_size(x_1513);
x_1515 = lean_nat_dec_eq(x_18, x_1514);
lean_dec(x_1514);
lean_dec(x_18);
lean_inc(x_1513);
x_1516 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1516, 0, x_11);
lean_ctor_set(x_1516, 1, x_1512);
lean_ctor_set(x_1516, 2, x_1513);
lean_ctor_set(x_1516, 3, x_13);
lean_ctor_set(x_1516, 4, x_14);
if (x_1515 == 0)
{
lean_object* x_1770; 
lean_dec(x_1513);
lean_dec(x_1509);
lean_dec(x_16);
lean_dec(x_8);
x_1770 = lean_box(0);
x_1517 = x_1770;
goto block_1769;
}
else
{
uint8_t x_1771; 
x_1771 = l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__1(x_8, x_1509, lean_box(0), x_16, x_1513, x_1455);
lean_dec(x_1513);
lean_dec(x_16);
lean_dec(x_1509);
lean_dec(x_8);
if (x_1771 == 0)
{
lean_object* x_1772; 
x_1772 = lean_box(0);
x_1517 = x_1772;
goto block_1769;
}
else
{
lean_object* x_1773; 
lean_dec(x_1511);
lean_dec(x_1500);
lean_inc(x_1502);
x_1773 = l_Lean_Meta_getMVarDecl(x_1502, x_1516, x_1510);
if (lean_obj_tag(x_1773) == 0)
{
lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; 
x_1774 = lean_ctor_get(x_1773, 0);
lean_inc(x_1774);
x_1775 = lean_ctor_get(x_1773, 1);
lean_inc(x_1775);
lean_dec(x_1773);
x_1776 = lean_ctor_get(x_1774, 2);
lean_inc(x_1776);
lean_dec(x_1774);
lean_inc(x_1516);
lean_inc(x_1506);
x_1777 = l_Lean_Meta_getLocalDecl(x_1506, x_1516, x_1775);
if (lean_obj_tag(x_1777) == 0)
{
lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_2003; uint8_t x_2004; 
x_1778 = lean_ctor_get(x_1777, 0);
lean_inc(x_1778);
x_1779 = lean_ctor_get(x_1777, 1);
lean_inc(x_1779);
lean_dec(x_1777);
x_2003 = l_Lean_LocalDecl_type(x_1778);
lean_dec(x_1778);
x_2004 = l_Lean_Expr_isAppOfArity___main(x_2003, x_1448, x_1449);
if (x_2004 == 0)
{
lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; 
lean_dec(x_2003);
lean_dec(x_1776);
lean_dec(x_1507);
lean_dec(x_1506);
lean_dec(x_1505);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_2005 = l_Lean_Meta_isClassQuick___main___closed__1;
x_2006 = l_unreachable_x21___rarg(x_2005);
x_2007 = lean_apply_2(x_2006, x_1516, x_1779);
x_1430 = x_2007;
goto block_1435;
}
else
{
lean_object* x_2008; 
x_2008 = l_Lean_Expr_getAppNumArgsAux___main(x_2003, x_1455);
if (x_1465 == 0)
{
lean_object* x_2009; lean_object* x_2010; lean_object* x_2011; 
x_2009 = lean_nat_sub(x_2008, x_1461);
lean_dec(x_2008);
x_2010 = lean_nat_sub(x_2009, x_1457);
lean_dec(x_2009);
x_2011 = l_Lean_Expr_getRevArg_x21___main(x_2003, x_2010);
lean_dec(x_2003);
x_1780 = x_2011;
goto block_2002;
}
else
{
lean_object* x_2012; lean_object* x_2013; lean_object* x_2014; 
x_2012 = lean_nat_sub(x_2008, x_1457);
lean_dec(x_2008);
x_2013 = lean_nat_sub(x_2012, x_1457);
lean_dec(x_2012);
x_2014 = l_Lean_Expr_getRevArg_x21___main(x_2003, x_2013);
lean_dec(x_2003);
x_1780 = x_2014;
goto block_2002;
}
}
block_2002:
{
lean_object* x_1781; lean_object* x_1782; uint8_t x_1783; 
x_1781 = lean_ctor_get(x_1779, 1);
lean_inc(x_1781);
lean_inc(x_1776);
x_1782 = l_Lean_MetavarContext_exprDependsOn(x_1781, x_1776, x_1506);
x_1783 = lean_unbox(x_1782);
lean_dec(x_1782);
if (x_1783 == 0)
{
lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; 
x_1784 = l_Lean_mkOptionalNode___closed__2;
x_1785 = lean_array_push(x_1784, x_1505);
lean_inc(x_1516);
lean_inc(x_1776);
lean_inc(x_1785);
x_1786 = l_Lean_Meta_mkLambda(x_1785, x_1776, x_1516, x_1779);
if (lean_obj_tag(x_1786) == 0)
{
lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; 
x_1787 = lean_ctor_get(x_1786, 0);
lean_inc(x_1787);
x_1788 = lean_ctor_get(x_1786, 1);
lean_inc(x_1788);
lean_dec(x_1786);
x_1789 = lean_expr_abstract(x_1776, x_1785);
lean_dec(x_1785);
lean_dec(x_1776);
x_1790 = lean_expr_instantiate1(x_1789, x_1780);
lean_dec(x_1780);
lean_dec(x_1789);
if (x_1465 == 0)
{
lean_object* x_1844; 
lean_inc(x_1516);
x_1844 = l_Lean_Meta_mkEqSymm(x_1507, x_1516, x_1788);
if (lean_obj_tag(x_1844) == 0)
{
lean_object* x_1845; lean_object* x_1846; 
x_1845 = lean_ctor_get(x_1844, 0);
lean_inc(x_1845);
x_1846 = lean_ctor_get(x_1844, 1);
lean_inc(x_1846);
lean_dec(x_1844);
x_1791 = x_1845;
x_1792 = x_1846;
goto block_1843;
}
else
{
lean_object* x_1847; lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; 
lean_dec(x_1790);
lean_dec(x_1787);
lean_dec(x_1516);
lean_dec(x_1506);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_1847 = lean_ctor_get(x_1844, 0);
lean_inc(x_1847);
x_1848 = lean_ctor_get(x_1844, 1);
lean_inc(x_1848);
if (lean_is_exclusive(x_1844)) {
 lean_ctor_release(x_1844, 0);
 lean_ctor_release(x_1844, 1);
 x_1849 = x_1844;
} else {
 lean_dec_ref(x_1844);
 x_1849 = lean_box(0);
}
if (lean_is_scalar(x_1849)) {
 x_1850 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1850 = x_1849;
}
lean_ctor_set(x_1850, 0, x_1847);
lean_ctor_set(x_1850, 1, x_1848);
x_1430 = x_1850;
goto block_1435;
}
}
else
{
x_1791 = x_1507;
x_1792 = x_1788;
goto block_1843;
}
block_1843:
{
uint8_t x_1793; lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; 
x_1793 = 2;
lean_inc(x_1516);
x_1794 = l_Lean_Meta_mkFreshExprMVar(x_1790, x_1439, x_1793, x_1516, x_1792);
x_1795 = lean_ctor_get(x_1794, 0);
lean_inc(x_1795);
x_1796 = lean_ctor_get(x_1794, 1);
lean_inc(x_1796);
lean_dec(x_1794);
lean_inc(x_1516);
lean_inc(x_1795);
x_1797 = l_Lean_Meta_mkEqNDRec(x_1787, x_1795, x_1791, x_1516, x_1796);
if (lean_obj_tag(x_1797) == 0)
{
lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; 
x_1798 = lean_ctor_get(x_1797, 1);
lean_inc(x_1798);
x_1799 = lean_ctor_get(x_1797, 0);
lean_inc(x_1799);
lean_dec(x_1797);
x_1800 = lean_ctor_get(x_1798, 0);
lean_inc(x_1800);
x_1801 = lean_ctor_get(x_1798, 1);
lean_inc(x_1801);
x_1802 = lean_ctor_get(x_1798, 2);
lean_inc(x_1802);
x_1803 = lean_ctor_get(x_1798, 3);
lean_inc(x_1803);
x_1804 = lean_ctor_get(x_1798, 4);
lean_inc(x_1804);
x_1805 = lean_ctor_get(x_1798, 5);
lean_inc(x_1805);
if (lean_is_exclusive(x_1798)) {
 lean_ctor_release(x_1798, 0);
 lean_ctor_release(x_1798, 1);
 lean_ctor_release(x_1798, 2);
 lean_ctor_release(x_1798, 3);
 lean_ctor_release(x_1798, 4);
 lean_ctor_release(x_1798, 5);
 x_1806 = x_1798;
} else {
 lean_dec_ref(x_1798);
 x_1806 = lean_box(0);
}
x_1807 = l_Lean_MetavarContext_assignExpr(x_1801, x_1502, x_1799);
if (lean_is_scalar(x_1806)) {
 x_1808 = lean_alloc_ctor(0, 6, 0);
} else {
 x_1808 = x_1806;
}
lean_ctor_set(x_1808, 0, x_1800);
lean_ctor_set(x_1808, 1, x_1807);
lean_ctor_set(x_1808, 2, x_1802);
lean_ctor_set(x_1808, 3, x_1803);
lean_ctor_set(x_1808, 4, x_1804);
lean_ctor_set(x_1808, 5, x_1805);
x_1809 = l_Lean_Expr_mvarId_x21(x_1795);
lean_dec(x_1795);
x_1810 = l_Lean_Meta_clear(x_1809, x_1506, x_1516, x_1808);
if (lean_obj_tag(x_1810) == 0)
{
lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; 
x_1811 = lean_ctor_get(x_1810, 0);
lean_inc(x_1811);
x_1812 = lean_ctor_get(x_1810, 1);
lean_inc(x_1812);
lean_dec(x_1810);
x_1813 = l_Lean_Meta_clear(x_1811, x_1504, x_1516, x_1812);
if (lean_obj_tag(x_1813) == 0)
{
lean_object* x_1814; lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; 
x_1814 = lean_ctor_get(x_1813, 0);
lean_inc(x_1814);
x_1815 = lean_ctor_get(x_1813, 1);
lean_inc(x_1815);
lean_dec(x_1813);
x_1816 = lean_array_get_size(x_1493);
lean_dec(x_1493);
x_1817 = lean_nat_sub(x_1816, x_1461);
lean_dec(x_1816);
x_1818 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1496, x_1814, x_1817, x_1495, x_1516, x_1815);
lean_dec(x_1516);
if (lean_obj_tag(x_1818) == 0)
{
lean_object* x_1819; lean_object* x_1820; lean_object* x_1821; lean_object* x_1822; lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; 
x_1819 = lean_ctor_get(x_1818, 0);
lean_inc(x_1819);
x_1820 = lean_ctor_get(x_1818, 1);
lean_inc(x_1820);
if (lean_is_exclusive(x_1818)) {
 lean_ctor_release(x_1818, 0);
 lean_ctor_release(x_1818, 1);
 x_1821 = x_1818;
} else {
 lean_dec_ref(x_1818);
 x_1821 = lean_box(0);
}
x_1822 = lean_ctor_get(x_1819, 1);
lean_inc(x_1822);
if (lean_is_exclusive(x_1819)) {
 lean_ctor_release(x_1819, 0);
 lean_ctor_release(x_1819, 1);
 x_1823 = x_1819;
} else {
 lean_dec_ref(x_1819);
 x_1823 = lean_box(0);
}
x_1824 = lean_box(0);
if (lean_is_scalar(x_1823)) {
 x_1825 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1825 = x_1823;
}
lean_ctor_set(x_1825, 0, x_1824);
lean_ctor_set(x_1825, 1, x_1822);
if (lean_is_scalar(x_1821)) {
 x_1826 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1826 = x_1821;
}
lean_ctor_set(x_1826, 0, x_1825);
lean_ctor_set(x_1826, 1, x_1820);
x_1430 = x_1826;
goto block_1435;
}
else
{
lean_object* x_1827; lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; 
x_1827 = lean_ctor_get(x_1818, 0);
lean_inc(x_1827);
x_1828 = lean_ctor_get(x_1818, 1);
lean_inc(x_1828);
if (lean_is_exclusive(x_1818)) {
 lean_ctor_release(x_1818, 0);
 lean_ctor_release(x_1818, 1);
 x_1829 = x_1818;
} else {
 lean_dec_ref(x_1818);
 x_1829 = lean_box(0);
}
if (lean_is_scalar(x_1829)) {
 x_1830 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1830 = x_1829;
}
lean_ctor_set(x_1830, 0, x_1827);
lean_ctor_set(x_1830, 1, x_1828);
x_1430 = x_1830;
goto block_1435;
}
}
else
{
lean_object* x_1831; lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; 
lean_dec(x_1516);
lean_dec(x_1493);
x_1831 = lean_ctor_get(x_1813, 0);
lean_inc(x_1831);
x_1832 = lean_ctor_get(x_1813, 1);
lean_inc(x_1832);
if (lean_is_exclusive(x_1813)) {
 lean_ctor_release(x_1813, 0);
 lean_ctor_release(x_1813, 1);
 x_1833 = x_1813;
} else {
 lean_dec_ref(x_1813);
 x_1833 = lean_box(0);
}
if (lean_is_scalar(x_1833)) {
 x_1834 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1834 = x_1833;
}
lean_ctor_set(x_1834, 0, x_1831);
lean_ctor_set(x_1834, 1, x_1832);
x_1430 = x_1834;
goto block_1435;
}
}
else
{
lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; 
lean_dec(x_1516);
lean_dec(x_1504);
lean_dec(x_1493);
x_1835 = lean_ctor_get(x_1810, 0);
lean_inc(x_1835);
x_1836 = lean_ctor_get(x_1810, 1);
lean_inc(x_1836);
if (lean_is_exclusive(x_1810)) {
 lean_ctor_release(x_1810, 0);
 lean_ctor_release(x_1810, 1);
 x_1837 = x_1810;
} else {
 lean_dec_ref(x_1810);
 x_1837 = lean_box(0);
}
if (lean_is_scalar(x_1837)) {
 x_1838 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1838 = x_1837;
}
lean_ctor_set(x_1838, 0, x_1835);
lean_ctor_set(x_1838, 1, x_1836);
x_1430 = x_1838;
goto block_1435;
}
}
else
{
lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; 
lean_dec(x_1795);
lean_dec(x_1516);
lean_dec(x_1506);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
x_1839 = lean_ctor_get(x_1797, 0);
lean_inc(x_1839);
x_1840 = lean_ctor_get(x_1797, 1);
lean_inc(x_1840);
if (lean_is_exclusive(x_1797)) {
 lean_ctor_release(x_1797, 0);
 lean_ctor_release(x_1797, 1);
 x_1841 = x_1797;
} else {
 lean_dec_ref(x_1797);
 x_1841 = lean_box(0);
}
if (lean_is_scalar(x_1841)) {
 x_1842 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1842 = x_1841;
}
lean_ctor_set(x_1842, 0, x_1839);
lean_ctor_set(x_1842, 1, x_1840);
x_1430 = x_1842;
goto block_1435;
}
}
}
else
{
lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; 
lean_dec(x_1785);
lean_dec(x_1780);
lean_dec(x_1776);
lean_dec(x_1516);
lean_dec(x_1507);
lean_dec(x_1506);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_1851 = lean_ctor_get(x_1786, 0);
lean_inc(x_1851);
x_1852 = lean_ctor_get(x_1786, 1);
lean_inc(x_1852);
if (lean_is_exclusive(x_1786)) {
 lean_ctor_release(x_1786, 0);
 lean_ctor_release(x_1786, 1);
 x_1853 = x_1786;
} else {
 lean_dec_ref(x_1786);
 x_1853 = lean_box(0);
}
if (lean_is_scalar(x_1853)) {
 x_1854 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1854 = x_1853;
}
lean_ctor_set(x_1854, 0, x_1851);
lean_ctor_set(x_1854, 1, x_1852);
x_1430 = x_1854;
goto block_1435;
}
}
else
{
lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; 
x_1855 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_1505);
x_1856 = lean_array_push(x_1855, x_1505);
x_1857 = lean_expr_abstract(x_1776, x_1856);
lean_dec(x_1856);
x_1858 = lean_expr_instantiate1(x_1857, x_1780);
lean_dec(x_1857);
lean_inc(x_1516);
lean_inc(x_1780);
x_1859 = l_Lean_Meta_mkEqRefl(x_1780, x_1516, x_1779);
if (lean_obj_tag(x_1859) == 0)
{
lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; lean_object* x_1863; lean_object* x_1864; 
x_1860 = lean_ctor_get(x_1859, 0);
lean_inc(x_1860);
x_1861 = lean_ctor_get(x_1859, 1);
lean_inc(x_1861);
lean_dec(x_1859);
lean_inc(x_1507);
x_1862 = lean_array_push(x_1855, x_1507);
x_1863 = lean_expr_abstract(x_1858, x_1862);
lean_dec(x_1858);
x_1864 = lean_expr_instantiate1(x_1863, x_1860);
lean_dec(x_1860);
lean_dec(x_1863);
if (x_1465 == 0)
{
lean_object* x_1865; 
lean_inc(x_1516);
lean_inc(x_1505);
x_1865 = l_Lean_Meta_mkEq(x_1780, x_1505, x_1516, x_1861);
if (lean_obj_tag(x_1865) == 0)
{
lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; uint8_t x_1870; lean_object* x_1871; 
x_1866 = lean_ctor_get(x_1865, 0);
lean_inc(x_1866);
x_1867 = lean_ctor_get(x_1865, 1);
lean_inc(x_1867);
lean_dec(x_1865);
x_1868 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__1___boxed), 7, 4);
lean_closure_set(x_1868, 0, x_1776);
lean_closure_set(x_1868, 1, x_1862);
lean_closure_set(x_1868, 2, x_1486);
lean_closure_set(x_1868, 3, x_1505);
x_1869 = l_Lean_Meta_substCore___closed__18;
x_1870 = 0;
lean_inc(x_1516);
x_1871 = l_Lean_Meta_withLocalDecl___rarg(x_1869, x_1866, x_1870, x_1868, x_1516, x_1867);
if (lean_obj_tag(x_1871) == 0)
{
lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; 
x_1872 = lean_ctor_get(x_1871, 0);
lean_inc(x_1872);
x_1873 = lean_ctor_get(x_1871, 1);
lean_inc(x_1873);
lean_dec(x_1871);
lean_inc(x_1516);
x_1874 = l_Lean_Meta_mkEqSymm(x_1507, x_1516, x_1873);
if (lean_obj_tag(x_1874) == 0)
{
lean_object* x_1875; lean_object* x_1876; uint8_t x_1877; lean_object* x_1878; lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; 
x_1875 = lean_ctor_get(x_1874, 0);
lean_inc(x_1875);
x_1876 = lean_ctor_get(x_1874, 1);
lean_inc(x_1876);
lean_dec(x_1874);
x_1877 = 2;
lean_inc(x_1516);
x_1878 = l_Lean_Meta_mkFreshExprMVar(x_1864, x_1439, x_1877, x_1516, x_1876);
x_1879 = lean_ctor_get(x_1878, 0);
lean_inc(x_1879);
x_1880 = lean_ctor_get(x_1878, 1);
lean_inc(x_1880);
lean_dec(x_1878);
lean_inc(x_1516);
lean_inc(x_1879);
x_1881 = l_Lean_Meta_mkEqRec(x_1872, x_1879, x_1875, x_1516, x_1880);
if (lean_obj_tag(x_1881) == 0)
{
lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; 
x_1882 = lean_ctor_get(x_1881, 1);
lean_inc(x_1882);
x_1883 = lean_ctor_get(x_1881, 0);
lean_inc(x_1883);
lean_dec(x_1881);
x_1884 = lean_ctor_get(x_1882, 0);
lean_inc(x_1884);
x_1885 = lean_ctor_get(x_1882, 1);
lean_inc(x_1885);
x_1886 = lean_ctor_get(x_1882, 2);
lean_inc(x_1886);
x_1887 = lean_ctor_get(x_1882, 3);
lean_inc(x_1887);
x_1888 = lean_ctor_get(x_1882, 4);
lean_inc(x_1888);
x_1889 = lean_ctor_get(x_1882, 5);
lean_inc(x_1889);
if (lean_is_exclusive(x_1882)) {
 lean_ctor_release(x_1882, 0);
 lean_ctor_release(x_1882, 1);
 lean_ctor_release(x_1882, 2);
 lean_ctor_release(x_1882, 3);
 lean_ctor_release(x_1882, 4);
 lean_ctor_release(x_1882, 5);
 x_1890 = x_1882;
} else {
 lean_dec_ref(x_1882);
 x_1890 = lean_box(0);
}
x_1891 = l_Lean_MetavarContext_assignExpr(x_1885, x_1502, x_1883);
if (lean_is_scalar(x_1890)) {
 x_1892 = lean_alloc_ctor(0, 6, 0);
} else {
 x_1892 = x_1890;
}
lean_ctor_set(x_1892, 0, x_1884);
lean_ctor_set(x_1892, 1, x_1891);
lean_ctor_set(x_1892, 2, x_1886);
lean_ctor_set(x_1892, 3, x_1887);
lean_ctor_set(x_1892, 4, x_1888);
lean_ctor_set(x_1892, 5, x_1889);
x_1893 = l_Lean_Expr_mvarId_x21(x_1879);
lean_dec(x_1879);
x_1894 = l_Lean_Meta_clear(x_1893, x_1506, x_1516, x_1892);
if (lean_obj_tag(x_1894) == 0)
{
lean_object* x_1895; lean_object* x_1896; lean_object* x_1897; 
x_1895 = lean_ctor_get(x_1894, 0);
lean_inc(x_1895);
x_1896 = lean_ctor_get(x_1894, 1);
lean_inc(x_1896);
lean_dec(x_1894);
x_1897 = l_Lean_Meta_clear(x_1895, x_1504, x_1516, x_1896);
if (lean_obj_tag(x_1897) == 0)
{
lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; 
x_1898 = lean_ctor_get(x_1897, 0);
lean_inc(x_1898);
x_1899 = lean_ctor_get(x_1897, 1);
lean_inc(x_1899);
lean_dec(x_1897);
x_1900 = lean_array_get_size(x_1493);
lean_dec(x_1493);
x_1901 = lean_nat_sub(x_1900, x_1461);
lean_dec(x_1900);
x_1902 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1496, x_1898, x_1901, x_1495, x_1516, x_1899);
lean_dec(x_1516);
if (lean_obj_tag(x_1902) == 0)
{
lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; 
x_1903 = lean_ctor_get(x_1902, 0);
lean_inc(x_1903);
x_1904 = lean_ctor_get(x_1902, 1);
lean_inc(x_1904);
if (lean_is_exclusive(x_1902)) {
 lean_ctor_release(x_1902, 0);
 lean_ctor_release(x_1902, 1);
 x_1905 = x_1902;
} else {
 lean_dec_ref(x_1902);
 x_1905 = lean_box(0);
}
x_1906 = lean_ctor_get(x_1903, 1);
lean_inc(x_1906);
if (lean_is_exclusive(x_1903)) {
 lean_ctor_release(x_1903, 0);
 lean_ctor_release(x_1903, 1);
 x_1907 = x_1903;
} else {
 lean_dec_ref(x_1903);
 x_1907 = lean_box(0);
}
x_1908 = lean_box(0);
if (lean_is_scalar(x_1907)) {
 x_1909 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1909 = x_1907;
}
lean_ctor_set(x_1909, 0, x_1908);
lean_ctor_set(x_1909, 1, x_1906);
if (lean_is_scalar(x_1905)) {
 x_1910 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1910 = x_1905;
}
lean_ctor_set(x_1910, 0, x_1909);
lean_ctor_set(x_1910, 1, x_1904);
x_1430 = x_1910;
goto block_1435;
}
else
{
lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; 
x_1911 = lean_ctor_get(x_1902, 0);
lean_inc(x_1911);
x_1912 = lean_ctor_get(x_1902, 1);
lean_inc(x_1912);
if (lean_is_exclusive(x_1902)) {
 lean_ctor_release(x_1902, 0);
 lean_ctor_release(x_1902, 1);
 x_1913 = x_1902;
} else {
 lean_dec_ref(x_1902);
 x_1913 = lean_box(0);
}
if (lean_is_scalar(x_1913)) {
 x_1914 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1914 = x_1913;
}
lean_ctor_set(x_1914, 0, x_1911);
lean_ctor_set(x_1914, 1, x_1912);
x_1430 = x_1914;
goto block_1435;
}
}
else
{
lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; 
lean_dec(x_1516);
lean_dec(x_1493);
x_1915 = lean_ctor_get(x_1897, 0);
lean_inc(x_1915);
x_1916 = lean_ctor_get(x_1897, 1);
lean_inc(x_1916);
if (lean_is_exclusive(x_1897)) {
 lean_ctor_release(x_1897, 0);
 lean_ctor_release(x_1897, 1);
 x_1917 = x_1897;
} else {
 lean_dec_ref(x_1897);
 x_1917 = lean_box(0);
}
if (lean_is_scalar(x_1917)) {
 x_1918 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1918 = x_1917;
}
lean_ctor_set(x_1918, 0, x_1915);
lean_ctor_set(x_1918, 1, x_1916);
x_1430 = x_1918;
goto block_1435;
}
}
else
{
lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; 
lean_dec(x_1516);
lean_dec(x_1504);
lean_dec(x_1493);
x_1919 = lean_ctor_get(x_1894, 0);
lean_inc(x_1919);
x_1920 = lean_ctor_get(x_1894, 1);
lean_inc(x_1920);
if (lean_is_exclusive(x_1894)) {
 lean_ctor_release(x_1894, 0);
 lean_ctor_release(x_1894, 1);
 x_1921 = x_1894;
} else {
 lean_dec_ref(x_1894);
 x_1921 = lean_box(0);
}
if (lean_is_scalar(x_1921)) {
 x_1922 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1922 = x_1921;
}
lean_ctor_set(x_1922, 0, x_1919);
lean_ctor_set(x_1922, 1, x_1920);
x_1430 = x_1922;
goto block_1435;
}
}
else
{
lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; lean_object* x_1926; 
lean_dec(x_1879);
lean_dec(x_1516);
lean_dec(x_1506);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
x_1923 = lean_ctor_get(x_1881, 0);
lean_inc(x_1923);
x_1924 = lean_ctor_get(x_1881, 1);
lean_inc(x_1924);
if (lean_is_exclusive(x_1881)) {
 lean_ctor_release(x_1881, 0);
 lean_ctor_release(x_1881, 1);
 x_1925 = x_1881;
} else {
 lean_dec_ref(x_1881);
 x_1925 = lean_box(0);
}
if (lean_is_scalar(x_1925)) {
 x_1926 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1926 = x_1925;
}
lean_ctor_set(x_1926, 0, x_1923);
lean_ctor_set(x_1926, 1, x_1924);
x_1430 = x_1926;
goto block_1435;
}
}
else
{
lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; 
lean_dec(x_1872);
lean_dec(x_1864);
lean_dec(x_1516);
lean_dec(x_1506);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_1927 = lean_ctor_get(x_1874, 0);
lean_inc(x_1927);
x_1928 = lean_ctor_get(x_1874, 1);
lean_inc(x_1928);
if (lean_is_exclusive(x_1874)) {
 lean_ctor_release(x_1874, 0);
 lean_ctor_release(x_1874, 1);
 x_1929 = x_1874;
} else {
 lean_dec_ref(x_1874);
 x_1929 = lean_box(0);
}
if (lean_is_scalar(x_1929)) {
 x_1930 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1930 = x_1929;
}
lean_ctor_set(x_1930, 0, x_1927);
lean_ctor_set(x_1930, 1, x_1928);
x_1430 = x_1930;
goto block_1435;
}
}
else
{
lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; 
lean_dec(x_1864);
lean_dec(x_1516);
lean_dec(x_1507);
lean_dec(x_1506);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_1931 = lean_ctor_get(x_1871, 0);
lean_inc(x_1931);
x_1932 = lean_ctor_get(x_1871, 1);
lean_inc(x_1932);
if (lean_is_exclusive(x_1871)) {
 lean_ctor_release(x_1871, 0);
 lean_ctor_release(x_1871, 1);
 x_1933 = x_1871;
} else {
 lean_dec_ref(x_1871);
 x_1933 = lean_box(0);
}
if (lean_is_scalar(x_1933)) {
 x_1934 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1934 = x_1933;
}
lean_ctor_set(x_1934, 0, x_1931);
lean_ctor_set(x_1934, 1, x_1932);
x_1430 = x_1934;
goto block_1435;
}
}
else
{
lean_object* x_1935; lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; 
lean_dec(x_1864);
lean_dec(x_1862);
lean_dec(x_1776);
lean_dec(x_1516);
lean_dec(x_1507);
lean_dec(x_1506);
lean_dec(x_1505);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_1935 = lean_ctor_get(x_1865, 0);
lean_inc(x_1935);
x_1936 = lean_ctor_get(x_1865, 1);
lean_inc(x_1936);
if (lean_is_exclusive(x_1865)) {
 lean_ctor_release(x_1865, 0);
 lean_ctor_release(x_1865, 1);
 x_1937 = x_1865;
} else {
 lean_dec_ref(x_1865);
 x_1937 = lean_box(0);
}
if (lean_is_scalar(x_1937)) {
 x_1938 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1938 = x_1937;
}
lean_ctor_set(x_1938, 0, x_1935);
lean_ctor_set(x_1938, 1, x_1936);
x_1430 = x_1938;
goto block_1435;
}
}
else
{
lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; 
lean_dec(x_1862);
lean_dec(x_1780);
x_1939 = lean_array_push(x_1486, x_1505);
lean_inc(x_1507);
x_1940 = lean_array_push(x_1939, x_1507);
lean_inc(x_1516);
x_1941 = l_Lean_Meta_mkLambda(x_1940, x_1776, x_1516, x_1861);
if (lean_obj_tag(x_1941) == 0)
{
lean_object* x_1942; lean_object* x_1943; uint8_t x_1944; lean_object* x_1945; lean_object* x_1946; lean_object* x_1947; lean_object* x_1948; 
x_1942 = lean_ctor_get(x_1941, 0);
lean_inc(x_1942);
x_1943 = lean_ctor_get(x_1941, 1);
lean_inc(x_1943);
lean_dec(x_1941);
x_1944 = 2;
lean_inc(x_1516);
x_1945 = l_Lean_Meta_mkFreshExprMVar(x_1864, x_1439, x_1944, x_1516, x_1943);
x_1946 = lean_ctor_get(x_1945, 0);
lean_inc(x_1946);
x_1947 = lean_ctor_get(x_1945, 1);
lean_inc(x_1947);
lean_dec(x_1945);
lean_inc(x_1516);
lean_inc(x_1946);
x_1948 = l_Lean_Meta_mkEqRec(x_1942, x_1946, x_1507, x_1516, x_1947);
if (lean_obj_tag(x_1948) == 0)
{
lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; lean_object* x_1961; 
x_1949 = lean_ctor_get(x_1948, 1);
lean_inc(x_1949);
x_1950 = lean_ctor_get(x_1948, 0);
lean_inc(x_1950);
lean_dec(x_1948);
x_1951 = lean_ctor_get(x_1949, 0);
lean_inc(x_1951);
x_1952 = lean_ctor_get(x_1949, 1);
lean_inc(x_1952);
x_1953 = lean_ctor_get(x_1949, 2);
lean_inc(x_1953);
x_1954 = lean_ctor_get(x_1949, 3);
lean_inc(x_1954);
x_1955 = lean_ctor_get(x_1949, 4);
lean_inc(x_1955);
x_1956 = lean_ctor_get(x_1949, 5);
lean_inc(x_1956);
if (lean_is_exclusive(x_1949)) {
 lean_ctor_release(x_1949, 0);
 lean_ctor_release(x_1949, 1);
 lean_ctor_release(x_1949, 2);
 lean_ctor_release(x_1949, 3);
 lean_ctor_release(x_1949, 4);
 lean_ctor_release(x_1949, 5);
 x_1957 = x_1949;
} else {
 lean_dec_ref(x_1949);
 x_1957 = lean_box(0);
}
x_1958 = l_Lean_MetavarContext_assignExpr(x_1952, x_1502, x_1950);
if (lean_is_scalar(x_1957)) {
 x_1959 = lean_alloc_ctor(0, 6, 0);
} else {
 x_1959 = x_1957;
}
lean_ctor_set(x_1959, 0, x_1951);
lean_ctor_set(x_1959, 1, x_1958);
lean_ctor_set(x_1959, 2, x_1953);
lean_ctor_set(x_1959, 3, x_1954);
lean_ctor_set(x_1959, 4, x_1955);
lean_ctor_set(x_1959, 5, x_1956);
x_1960 = l_Lean_Expr_mvarId_x21(x_1946);
lean_dec(x_1946);
x_1961 = l_Lean_Meta_clear(x_1960, x_1506, x_1516, x_1959);
if (lean_obj_tag(x_1961) == 0)
{
lean_object* x_1962; lean_object* x_1963; lean_object* x_1964; 
x_1962 = lean_ctor_get(x_1961, 0);
lean_inc(x_1962);
x_1963 = lean_ctor_get(x_1961, 1);
lean_inc(x_1963);
lean_dec(x_1961);
x_1964 = l_Lean_Meta_clear(x_1962, x_1504, x_1516, x_1963);
if (lean_obj_tag(x_1964) == 0)
{
lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; 
x_1965 = lean_ctor_get(x_1964, 0);
lean_inc(x_1965);
x_1966 = lean_ctor_get(x_1964, 1);
lean_inc(x_1966);
lean_dec(x_1964);
x_1967 = lean_array_get_size(x_1493);
lean_dec(x_1493);
x_1968 = lean_nat_sub(x_1967, x_1461);
lean_dec(x_1967);
x_1969 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1496, x_1965, x_1968, x_1495, x_1516, x_1966);
lean_dec(x_1516);
if (lean_obj_tag(x_1969) == 0)
{
lean_object* x_1970; lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; 
x_1970 = lean_ctor_get(x_1969, 0);
lean_inc(x_1970);
x_1971 = lean_ctor_get(x_1969, 1);
lean_inc(x_1971);
if (lean_is_exclusive(x_1969)) {
 lean_ctor_release(x_1969, 0);
 lean_ctor_release(x_1969, 1);
 x_1972 = x_1969;
} else {
 lean_dec_ref(x_1969);
 x_1972 = lean_box(0);
}
x_1973 = lean_ctor_get(x_1970, 1);
lean_inc(x_1973);
if (lean_is_exclusive(x_1970)) {
 lean_ctor_release(x_1970, 0);
 lean_ctor_release(x_1970, 1);
 x_1974 = x_1970;
} else {
 lean_dec_ref(x_1970);
 x_1974 = lean_box(0);
}
x_1975 = lean_box(0);
if (lean_is_scalar(x_1974)) {
 x_1976 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1976 = x_1974;
}
lean_ctor_set(x_1976, 0, x_1975);
lean_ctor_set(x_1976, 1, x_1973);
if (lean_is_scalar(x_1972)) {
 x_1977 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1977 = x_1972;
}
lean_ctor_set(x_1977, 0, x_1976);
lean_ctor_set(x_1977, 1, x_1971);
x_1430 = x_1977;
goto block_1435;
}
else
{
lean_object* x_1978; lean_object* x_1979; lean_object* x_1980; lean_object* x_1981; 
x_1978 = lean_ctor_get(x_1969, 0);
lean_inc(x_1978);
x_1979 = lean_ctor_get(x_1969, 1);
lean_inc(x_1979);
if (lean_is_exclusive(x_1969)) {
 lean_ctor_release(x_1969, 0);
 lean_ctor_release(x_1969, 1);
 x_1980 = x_1969;
} else {
 lean_dec_ref(x_1969);
 x_1980 = lean_box(0);
}
if (lean_is_scalar(x_1980)) {
 x_1981 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1981 = x_1980;
}
lean_ctor_set(x_1981, 0, x_1978);
lean_ctor_set(x_1981, 1, x_1979);
x_1430 = x_1981;
goto block_1435;
}
}
else
{
lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; 
lean_dec(x_1516);
lean_dec(x_1493);
x_1982 = lean_ctor_get(x_1964, 0);
lean_inc(x_1982);
x_1983 = lean_ctor_get(x_1964, 1);
lean_inc(x_1983);
if (lean_is_exclusive(x_1964)) {
 lean_ctor_release(x_1964, 0);
 lean_ctor_release(x_1964, 1);
 x_1984 = x_1964;
} else {
 lean_dec_ref(x_1964);
 x_1984 = lean_box(0);
}
if (lean_is_scalar(x_1984)) {
 x_1985 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1985 = x_1984;
}
lean_ctor_set(x_1985, 0, x_1982);
lean_ctor_set(x_1985, 1, x_1983);
x_1430 = x_1985;
goto block_1435;
}
}
else
{
lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; lean_object* x_1989; 
lean_dec(x_1516);
lean_dec(x_1504);
lean_dec(x_1493);
x_1986 = lean_ctor_get(x_1961, 0);
lean_inc(x_1986);
x_1987 = lean_ctor_get(x_1961, 1);
lean_inc(x_1987);
if (lean_is_exclusive(x_1961)) {
 lean_ctor_release(x_1961, 0);
 lean_ctor_release(x_1961, 1);
 x_1988 = x_1961;
} else {
 lean_dec_ref(x_1961);
 x_1988 = lean_box(0);
}
if (lean_is_scalar(x_1988)) {
 x_1989 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1989 = x_1988;
}
lean_ctor_set(x_1989, 0, x_1986);
lean_ctor_set(x_1989, 1, x_1987);
x_1430 = x_1989;
goto block_1435;
}
}
else
{
lean_object* x_1990; lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; 
lean_dec(x_1946);
lean_dec(x_1516);
lean_dec(x_1506);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
x_1990 = lean_ctor_get(x_1948, 0);
lean_inc(x_1990);
x_1991 = lean_ctor_get(x_1948, 1);
lean_inc(x_1991);
if (lean_is_exclusive(x_1948)) {
 lean_ctor_release(x_1948, 0);
 lean_ctor_release(x_1948, 1);
 x_1992 = x_1948;
} else {
 lean_dec_ref(x_1948);
 x_1992 = lean_box(0);
}
if (lean_is_scalar(x_1992)) {
 x_1993 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1993 = x_1992;
}
lean_ctor_set(x_1993, 0, x_1990);
lean_ctor_set(x_1993, 1, x_1991);
x_1430 = x_1993;
goto block_1435;
}
}
else
{
lean_object* x_1994; lean_object* x_1995; lean_object* x_1996; lean_object* x_1997; 
lean_dec(x_1864);
lean_dec(x_1516);
lean_dec(x_1507);
lean_dec(x_1506);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_1994 = lean_ctor_get(x_1941, 0);
lean_inc(x_1994);
x_1995 = lean_ctor_get(x_1941, 1);
lean_inc(x_1995);
if (lean_is_exclusive(x_1941)) {
 lean_ctor_release(x_1941, 0);
 lean_ctor_release(x_1941, 1);
 x_1996 = x_1941;
} else {
 lean_dec_ref(x_1941);
 x_1996 = lean_box(0);
}
if (lean_is_scalar(x_1996)) {
 x_1997 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1997 = x_1996;
}
lean_ctor_set(x_1997, 0, x_1994);
lean_ctor_set(x_1997, 1, x_1995);
x_1430 = x_1997;
goto block_1435;
}
}
}
else
{
lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; 
lean_dec(x_1858);
lean_dec(x_1780);
lean_dec(x_1776);
lean_dec(x_1516);
lean_dec(x_1507);
lean_dec(x_1506);
lean_dec(x_1505);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_1998 = lean_ctor_get(x_1859, 0);
lean_inc(x_1998);
x_1999 = lean_ctor_get(x_1859, 1);
lean_inc(x_1999);
if (lean_is_exclusive(x_1859)) {
 lean_ctor_release(x_1859, 0);
 lean_ctor_release(x_1859, 1);
 x_2000 = x_1859;
} else {
 lean_dec_ref(x_1859);
 x_2000 = lean_box(0);
}
if (lean_is_scalar(x_2000)) {
 x_2001 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2001 = x_2000;
}
lean_ctor_set(x_2001, 0, x_1998);
lean_ctor_set(x_2001, 1, x_1999);
x_1430 = x_2001;
goto block_1435;
}
}
}
}
else
{
lean_object* x_2015; lean_object* x_2016; lean_object* x_2017; lean_object* x_2018; 
lean_dec(x_1776);
lean_dec(x_1516);
lean_dec(x_1507);
lean_dec(x_1506);
lean_dec(x_1505);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_2015 = lean_ctor_get(x_1777, 0);
lean_inc(x_2015);
x_2016 = lean_ctor_get(x_1777, 1);
lean_inc(x_2016);
if (lean_is_exclusive(x_1777)) {
 lean_ctor_release(x_1777, 0);
 lean_ctor_release(x_1777, 1);
 x_2017 = x_1777;
} else {
 lean_dec_ref(x_1777);
 x_2017 = lean_box(0);
}
if (lean_is_scalar(x_2017)) {
 x_2018 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2018 = x_2017;
}
lean_ctor_set(x_2018, 0, x_2015);
lean_ctor_set(x_2018, 1, x_2016);
x_1430 = x_2018;
goto block_1435;
}
}
else
{
lean_object* x_2019; lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; 
lean_dec(x_1516);
lean_dec(x_1507);
lean_dec(x_1506);
lean_dec(x_1505);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_2019 = lean_ctor_get(x_1773, 0);
lean_inc(x_2019);
x_2020 = lean_ctor_get(x_1773, 1);
lean_inc(x_2020);
if (lean_is_exclusive(x_1773)) {
 lean_ctor_release(x_1773, 0);
 lean_ctor_release(x_1773, 1);
 x_2021 = x_1773;
} else {
 lean_dec_ref(x_1773);
 x_2021 = lean_box(0);
}
if (lean_is_scalar(x_2021)) {
 x_2022 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2022 = x_2021;
}
lean_ctor_set(x_2022, 0, x_2019);
lean_ctor_set(x_2022, 1, x_2020);
x_1430 = x_2022;
goto block_1435;
}
}
}
block_1769:
{
lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1545; lean_object* x_1546; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; 
lean_dec(x_1517);
x_1518 = lean_ctor_get(x_1510, 2);
lean_inc(x_1518);
x_1519 = lean_ctor_get(x_1510, 0);
lean_inc(x_1519);
x_1520 = lean_ctor_get(x_1510, 1);
lean_inc(x_1520);
x_1521 = lean_ctor_get(x_1510, 3);
lean_inc(x_1521);
x_1522 = lean_ctor_get(x_1510, 4);
lean_inc(x_1522);
x_1523 = lean_ctor_get(x_1510, 5);
lean_inc(x_1523);
if (lean_is_exclusive(x_1510)) {
 lean_ctor_release(x_1510, 0);
 lean_ctor_release(x_1510, 1);
 lean_ctor_release(x_1510, 2);
 lean_ctor_release(x_1510, 3);
 lean_ctor_release(x_1510, 4);
 lean_ctor_release(x_1510, 5);
 x_1524 = x_1510;
} else {
 lean_dec_ref(x_1510);
 x_1524 = lean_box(0);
}
x_1525 = lean_ctor_get(x_1518, 0);
lean_inc(x_1525);
x_1526 = lean_ctor_get(x_1518, 1);
lean_inc(x_1526);
x_1527 = lean_ctor_get(x_1518, 2);
lean_inc(x_1527);
if (lean_is_exclusive(x_1518)) {
 lean_ctor_release(x_1518, 0);
 lean_ctor_release(x_1518, 1);
 lean_ctor_release(x_1518, 2);
 x_1528 = x_1518;
} else {
 lean_dec_ref(x_1518);
 x_1528 = lean_box(0);
}
if (lean_is_scalar(x_1528)) {
 x_1561 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1561 = x_1528;
}
lean_ctor_set(x_1561, 0, x_1525);
lean_ctor_set(x_1561, 1, x_1526);
lean_ctor_set(x_1561, 2, x_1436);
if (lean_is_scalar(x_1524)) {
 x_1562 = lean_alloc_ctor(0, 6, 0);
} else {
 x_1562 = x_1524;
}
lean_ctor_set(x_1562, 0, x_1519);
lean_ctor_set(x_1562, 1, x_1520);
lean_ctor_set(x_1562, 2, x_1561);
lean_ctor_set(x_1562, 3, x_1521);
lean_ctor_set(x_1562, 4, x_1522);
lean_ctor_set(x_1562, 5, x_1523);
lean_inc(x_1502);
x_1563 = l_Lean_Meta_getMVarDecl(x_1502, x_1516, x_1562);
if (lean_obj_tag(x_1563) == 0)
{
lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; 
x_1564 = lean_ctor_get(x_1563, 0);
lean_inc(x_1564);
x_1565 = lean_ctor_get(x_1563, 1);
lean_inc(x_1565);
lean_dec(x_1563);
x_1566 = lean_ctor_get(x_1564, 2);
lean_inc(x_1566);
lean_dec(x_1564);
lean_inc(x_1516);
lean_inc(x_1506);
x_1567 = l_Lean_Meta_getLocalDecl(x_1506, x_1516, x_1565);
if (lean_obj_tag(x_1567) == 0)
{
lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1749; uint8_t x_1750; 
x_1568 = lean_ctor_get(x_1567, 0);
lean_inc(x_1568);
x_1569 = lean_ctor_get(x_1567, 1);
lean_inc(x_1569);
lean_dec(x_1567);
x_1749 = l_Lean_LocalDecl_type(x_1568);
lean_dec(x_1568);
x_1750 = l_Lean_Expr_isAppOfArity___main(x_1749, x_1448, x_1449);
if (x_1750 == 0)
{
lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; 
lean_dec(x_1749);
lean_dec(x_1566);
lean_dec(x_1507);
lean_dec(x_1506);
lean_dec(x_1505);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_1751 = l_Lean_Meta_isClassQuick___main___closed__1;
x_1752 = l_unreachable_x21___rarg(x_1751);
x_1753 = lean_apply_2(x_1752, x_1516, x_1569);
if (lean_obj_tag(x_1753) == 0)
{
lean_object* x_1754; lean_object* x_1755; 
lean_dec(x_1500);
x_1754 = lean_ctor_get(x_1753, 0);
lean_inc(x_1754);
x_1755 = lean_ctor_get(x_1753, 1);
lean_inc(x_1755);
lean_dec(x_1753);
x_1529 = x_1754;
x_1530 = x_1755;
goto block_1544;
}
else
{
lean_object* x_1756; lean_object* x_1757; 
lean_dec(x_1511);
x_1756 = lean_ctor_get(x_1753, 0);
lean_inc(x_1756);
x_1757 = lean_ctor_get(x_1753, 1);
lean_inc(x_1757);
lean_dec(x_1753);
x_1545 = x_1756;
x_1546 = x_1757;
goto block_1560;
}
}
else
{
lean_object* x_1758; 
x_1758 = l_Lean_Expr_getAppNumArgsAux___main(x_1749, x_1455);
if (x_1465 == 0)
{
lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; 
x_1759 = lean_nat_sub(x_1758, x_1461);
lean_dec(x_1758);
x_1760 = lean_nat_sub(x_1759, x_1457);
lean_dec(x_1759);
x_1761 = l_Lean_Expr_getRevArg_x21___main(x_1749, x_1760);
lean_dec(x_1749);
x_1570 = x_1761;
goto block_1748;
}
else
{
lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; 
x_1762 = lean_nat_sub(x_1758, x_1457);
lean_dec(x_1758);
x_1763 = lean_nat_sub(x_1762, x_1457);
lean_dec(x_1762);
x_1764 = l_Lean_Expr_getRevArg_x21___main(x_1749, x_1763);
lean_dec(x_1749);
x_1570 = x_1764;
goto block_1748;
}
}
block_1748:
{
lean_object* x_1571; lean_object* x_1572; uint8_t x_1573; 
x_1571 = lean_ctor_get(x_1569, 1);
lean_inc(x_1571);
lean_inc(x_1566);
x_1572 = l_Lean_MetavarContext_exprDependsOn(x_1571, x_1566, x_1506);
x_1573 = lean_unbox(x_1572);
lean_dec(x_1572);
if (x_1573 == 0)
{
lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; 
x_1574 = l_Lean_mkOptionalNode___closed__2;
x_1575 = lean_array_push(x_1574, x_1505);
lean_inc(x_1516);
lean_inc(x_1566);
lean_inc(x_1575);
x_1576 = l_Lean_Meta_mkLambda(x_1575, x_1566, x_1516, x_1569);
if (lean_obj_tag(x_1576) == 0)
{
lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; 
x_1577 = lean_ctor_get(x_1576, 0);
lean_inc(x_1577);
x_1578 = lean_ctor_get(x_1576, 1);
lean_inc(x_1578);
lean_dec(x_1576);
x_1579 = lean_expr_abstract(x_1566, x_1575);
lean_dec(x_1575);
lean_dec(x_1566);
x_1580 = lean_expr_instantiate1(x_1579, x_1570);
lean_dec(x_1570);
lean_dec(x_1579);
if (x_1465 == 0)
{
lean_object* x_1624; 
lean_inc(x_1516);
x_1624 = l_Lean_Meta_mkEqSymm(x_1507, x_1516, x_1578);
if (lean_obj_tag(x_1624) == 0)
{
lean_object* x_1625; lean_object* x_1626; 
x_1625 = lean_ctor_get(x_1624, 0);
lean_inc(x_1625);
x_1626 = lean_ctor_get(x_1624, 1);
lean_inc(x_1626);
lean_dec(x_1624);
x_1581 = x_1625;
x_1582 = x_1626;
goto block_1623;
}
else
{
lean_object* x_1627; lean_object* x_1628; 
lean_dec(x_1580);
lean_dec(x_1577);
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1506);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_1627 = lean_ctor_get(x_1624, 0);
lean_inc(x_1627);
x_1628 = lean_ctor_get(x_1624, 1);
lean_inc(x_1628);
lean_dec(x_1624);
x_1545 = x_1627;
x_1546 = x_1628;
goto block_1560;
}
}
else
{
x_1581 = x_1507;
x_1582 = x_1578;
goto block_1623;
}
block_1623:
{
uint8_t x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; 
x_1583 = 2;
lean_inc(x_1516);
x_1584 = l_Lean_Meta_mkFreshExprMVar(x_1580, x_1439, x_1583, x_1516, x_1582);
x_1585 = lean_ctor_get(x_1584, 0);
lean_inc(x_1585);
x_1586 = lean_ctor_get(x_1584, 1);
lean_inc(x_1586);
lean_dec(x_1584);
lean_inc(x_1516);
lean_inc(x_1585);
x_1587 = l_Lean_Meta_mkEqNDRec(x_1577, x_1585, x_1581, x_1516, x_1586);
if (lean_obj_tag(x_1587) == 0)
{
lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; 
x_1588 = lean_ctor_get(x_1587, 1);
lean_inc(x_1588);
x_1589 = lean_ctor_get(x_1587, 0);
lean_inc(x_1589);
lean_dec(x_1587);
x_1590 = lean_ctor_get(x_1588, 0);
lean_inc(x_1590);
x_1591 = lean_ctor_get(x_1588, 1);
lean_inc(x_1591);
x_1592 = lean_ctor_get(x_1588, 2);
lean_inc(x_1592);
x_1593 = lean_ctor_get(x_1588, 3);
lean_inc(x_1593);
x_1594 = lean_ctor_get(x_1588, 4);
lean_inc(x_1594);
x_1595 = lean_ctor_get(x_1588, 5);
lean_inc(x_1595);
if (lean_is_exclusive(x_1588)) {
 lean_ctor_release(x_1588, 0);
 lean_ctor_release(x_1588, 1);
 lean_ctor_release(x_1588, 2);
 lean_ctor_release(x_1588, 3);
 lean_ctor_release(x_1588, 4);
 lean_ctor_release(x_1588, 5);
 x_1596 = x_1588;
} else {
 lean_dec_ref(x_1588);
 x_1596 = lean_box(0);
}
x_1597 = l_Lean_MetavarContext_assignExpr(x_1591, x_1502, x_1589);
if (lean_is_scalar(x_1596)) {
 x_1598 = lean_alloc_ctor(0, 6, 0);
} else {
 x_1598 = x_1596;
}
lean_ctor_set(x_1598, 0, x_1590);
lean_ctor_set(x_1598, 1, x_1597);
lean_ctor_set(x_1598, 2, x_1592);
lean_ctor_set(x_1598, 3, x_1593);
lean_ctor_set(x_1598, 4, x_1594);
lean_ctor_set(x_1598, 5, x_1595);
x_1599 = l_Lean_Expr_mvarId_x21(x_1585);
lean_dec(x_1585);
x_1600 = l_Lean_Meta_clear(x_1599, x_1506, x_1516, x_1598);
if (lean_obj_tag(x_1600) == 0)
{
lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; 
x_1601 = lean_ctor_get(x_1600, 0);
lean_inc(x_1601);
x_1602 = lean_ctor_get(x_1600, 1);
lean_inc(x_1602);
lean_dec(x_1600);
x_1603 = l_Lean_Meta_clear(x_1601, x_1504, x_1516, x_1602);
if (lean_obj_tag(x_1603) == 0)
{
lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; 
x_1604 = lean_ctor_get(x_1603, 0);
lean_inc(x_1604);
x_1605 = lean_ctor_get(x_1603, 1);
lean_inc(x_1605);
lean_dec(x_1603);
x_1606 = lean_array_get_size(x_1493);
lean_dec(x_1493);
x_1607 = lean_nat_sub(x_1606, x_1461);
lean_dec(x_1606);
x_1608 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1496, x_1604, x_1607, x_1495, x_1516, x_1605);
lean_dec(x_1516);
if (lean_obj_tag(x_1608) == 0)
{
lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; 
lean_dec(x_1500);
x_1609 = lean_ctor_get(x_1608, 0);
lean_inc(x_1609);
x_1610 = lean_ctor_get(x_1608, 1);
lean_inc(x_1610);
lean_dec(x_1608);
x_1611 = lean_ctor_get(x_1609, 1);
lean_inc(x_1611);
if (lean_is_exclusive(x_1609)) {
 lean_ctor_release(x_1609, 0);
 lean_ctor_release(x_1609, 1);
 x_1612 = x_1609;
} else {
 lean_dec_ref(x_1609);
 x_1612 = lean_box(0);
}
x_1613 = lean_box(0);
if (lean_is_scalar(x_1612)) {
 x_1614 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1614 = x_1612;
}
lean_ctor_set(x_1614, 0, x_1613);
lean_ctor_set(x_1614, 1, x_1611);
x_1529 = x_1614;
x_1530 = x_1610;
goto block_1544;
}
else
{
lean_object* x_1615; lean_object* x_1616; 
lean_dec(x_1511);
x_1615 = lean_ctor_get(x_1608, 0);
lean_inc(x_1615);
x_1616 = lean_ctor_get(x_1608, 1);
lean_inc(x_1616);
lean_dec(x_1608);
x_1545 = x_1615;
x_1546 = x_1616;
goto block_1560;
}
}
else
{
lean_object* x_1617; lean_object* x_1618; 
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1493);
x_1617 = lean_ctor_get(x_1603, 0);
lean_inc(x_1617);
x_1618 = lean_ctor_get(x_1603, 1);
lean_inc(x_1618);
lean_dec(x_1603);
x_1545 = x_1617;
x_1546 = x_1618;
goto block_1560;
}
}
else
{
lean_object* x_1619; lean_object* x_1620; 
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1504);
lean_dec(x_1493);
x_1619 = lean_ctor_get(x_1600, 0);
lean_inc(x_1619);
x_1620 = lean_ctor_get(x_1600, 1);
lean_inc(x_1620);
lean_dec(x_1600);
x_1545 = x_1619;
x_1546 = x_1620;
goto block_1560;
}
}
else
{
lean_object* x_1621; lean_object* x_1622; 
lean_dec(x_1585);
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1506);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
x_1621 = lean_ctor_get(x_1587, 0);
lean_inc(x_1621);
x_1622 = lean_ctor_get(x_1587, 1);
lean_inc(x_1622);
lean_dec(x_1587);
x_1545 = x_1621;
x_1546 = x_1622;
goto block_1560;
}
}
}
else
{
lean_object* x_1629; lean_object* x_1630; 
lean_dec(x_1575);
lean_dec(x_1570);
lean_dec(x_1566);
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1507);
lean_dec(x_1506);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_1629 = lean_ctor_get(x_1576, 0);
lean_inc(x_1629);
x_1630 = lean_ctor_get(x_1576, 1);
lean_inc(x_1630);
lean_dec(x_1576);
x_1545 = x_1629;
x_1546 = x_1630;
goto block_1560;
}
}
else
{
lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; 
x_1631 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_1505);
x_1632 = lean_array_push(x_1631, x_1505);
x_1633 = lean_expr_abstract(x_1566, x_1632);
lean_dec(x_1632);
x_1634 = lean_expr_instantiate1(x_1633, x_1570);
lean_dec(x_1633);
lean_inc(x_1516);
lean_inc(x_1570);
x_1635 = l_Lean_Meta_mkEqRefl(x_1570, x_1516, x_1569);
if (lean_obj_tag(x_1635) == 0)
{
lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; 
x_1636 = lean_ctor_get(x_1635, 0);
lean_inc(x_1636);
x_1637 = lean_ctor_get(x_1635, 1);
lean_inc(x_1637);
lean_dec(x_1635);
lean_inc(x_1507);
x_1638 = lean_array_push(x_1631, x_1507);
x_1639 = lean_expr_abstract(x_1634, x_1638);
lean_dec(x_1634);
x_1640 = lean_expr_instantiate1(x_1639, x_1636);
lean_dec(x_1636);
lean_dec(x_1639);
if (x_1465 == 0)
{
lean_object* x_1641; 
lean_inc(x_1516);
lean_inc(x_1505);
x_1641 = l_Lean_Meta_mkEq(x_1570, x_1505, x_1516, x_1637);
if (lean_obj_tag(x_1641) == 0)
{
lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; uint8_t x_1646; lean_object* x_1647; 
x_1642 = lean_ctor_get(x_1641, 0);
lean_inc(x_1642);
x_1643 = lean_ctor_get(x_1641, 1);
lean_inc(x_1643);
lean_dec(x_1641);
x_1644 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__1___boxed), 7, 4);
lean_closure_set(x_1644, 0, x_1566);
lean_closure_set(x_1644, 1, x_1638);
lean_closure_set(x_1644, 2, x_1486);
lean_closure_set(x_1644, 3, x_1505);
x_1645 = l_Lean_Meta_substCore___closed__18;
x_1646 = 0;
lean_inc(x_1516);
x_1647 = l_Lean_Meta_withLocalDecl___rarg(x_1645, x_1642, x_1646, x_1644, x_1516, x_1643);
if (lean_obj_tag(x_1647) == 0)
{
lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; 
x_1648 = lean_ctor_get(x_1647, 0);
lean_inc(x_1648);
x_1649 = lean_ctor_get(x_1647, 1);
lean_inc(x_1649);
lean_dec(x_1647);
lean_inc(x_1516);
x_1650 = l_Lean_Meta_mkEqSymm(x_1507, x_1516, x_1649);
if (lean_obj_tag(x_1650) == 0)
{
lean_object* x_1651; lean_object* x_1652; uint8_t x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; 
x_1651 = lean_ctor_get(x_1650, 0);
lean_inc(x_1651);
x_1652 = lean_ctor_get(x_1650, 1);
lean_inc(x_1652);
lean_dec(x_1650);
x_1653 = 2;
lean_inc(x_1516);
x_1654 = l_Lean_Meta_mkFreshExprMVar(x_1640, x_1439, x_1653, x_1516, x_1652);
x_1655 = lean_ctor_get(x_1654, 0);
lean_inc(x_1655);
x_1656 = lean_ctor_get(x_1654, 1);
lean_inc(x_1656);
lean_dec(x_1654);
lean_inc(x_1516);
lean_inc(x_1655);
x_1657 = l_Lean_Meta_mkEqRec(x_1648, x_1655, x_1651, x_1516, x_1656);
if (lean_obj_tag(x_1657) == 0)
{
lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; 
x_1658 = lean_ctor_get(x_1657, 1);
lean_inc(x_1658);
x_1659 = lean_ctor_get(x_1657, 0);
lean_inc(x_1659);
lean_dec(x_1657);
x_1660 = lean_ctor_get(x_1658, 0);
lean_inc(x_1660);
x_1661 = lean_ctor_get(x_1658, 1);
lean_inc(x_1661);
x_1662 = lean_ctor_get(x_1658, 2);
lean_inc(x_1662);
x_1663 = lean_ctor_get(x_1658, 3);
lean_inc(x_1663);
x_1664 = lean_ctor_get(x_1658, 4);
lean_inc(x_1664);
x_1665 = lean_ctor_get(x_1658, 5);
lean_inc(x_1665);
if (lean_is_exclusive(x_1658)) {
 lean_ctor_release(x_1658, 0);
 lean_ctor_release(x_1658, 1);
 lean_ctor_release(x_1658, 2);
 lean_ctor_release(x_1658, 3);
 lean_ctor_release(x_1658, 4);
 lean_ctor_release(x_1658, 5);
 x_1666 = x_1658;
} else {
 lean_dec_ref(x_1658);
 x_1666 = lean_box(0);
}
x_1667 = l_Lean_MetavarContext_assignExpr(x_1661, x_1502, x_1659);
if (lean_is_scalar(x_1666)) {
 x_1668 = lean_alloc_ctor(0, 6, 0);
} else {
 x_1668 = x_1666;
}
lean_ctor_set(x_1668, 0, x_1660);
lean_ctor_set(x_1668, 1, x_1667);
lean_ctor_set(x_1668, 2, x_1662);
lean_ctor_set(x_1668, 3, x_1663);
lean_ctor_set(x_1668, 4, x_1664);
lean_ctor_set(x_1668, 5, x_1665);
x_1669 = l_Lean_Expr_mvarId_x21(x_1655);
lean_dec(x_1655);
x_1670 = l_Lean_Meta_clear(x_1669, x_1506, x_1516, x_1668);
if (lean_obj_tag(x_1670) == 0)
{
lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; 
x_1671 = lean_ctor_get(x_1670, 0);
lean_inc(x_1671);
x_1672 = lean_ctor_get(x_1670, 1);
lean_inc(x_1672);
lean_dec(x_1670);
x_1673 = l_Lean_Meta_clear(x_1671, x_1504, x_1516, x_1672);
if (lean_obj_tag(x_1673) == 0)
{
lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; 
x_1674 = lean_ctor_get(x_1673, 0);
lean_inc(x_1674);
x_1675 = lean_ctor_get(x_1673, 1);
lean_inc(x_1675);
lean_dec(x_1673);
x_1676 = lean_array_get_size(x_1493);
lean_dec(x_1493);
x_1677 = lean_nat_sub(x_1676, x_1461);
lean_dec(x_1676);
x_1678 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1496, x_1674, x_1677, x_1495, x_1516, x_1675);
lean_dec(x_1516);
if (lean_obj_tag(x_1678) == 0)
{
lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; 
lean_dec(x_1500);
x_1679 = lean_ctor_get(x_1678, 0);
lean_inc(x_1679);
x_1680 = lean_ctor_get(x_1678, 1);
lean_inc(x_1680);
lean_dec(x_1678);
x_1681 = lean_ctor_get(x_1679, 1);
lean_inc(x_1681);
if (lean_is_exclusive(x_1679)) {
 lean_ctor_release(x_1679, 0);
 lean_ctor_release(x_1679, 1);
 x_1682 = x_1679;
} else {
 lean_dec_ref(x_1679);
 x_1682 = lean_box(0);
}
x_1683 = lean_box(0);
if (lean_is_scalar(x_1682)) {
 x_1684 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1684 = x_1682;
}
lean_ctor_set(x_1684, 0, x_1683);
lean_ctor_set(x_1684, 1, x_1681);
x_1529 = x_1684;
x_1530 = x_1680;
goto block_1544;
}
else
{
lean_object* x_1685; lean_object* x_1686; 
lean_dec(x_1511);
x_1685 = lean_ctor_get(x_1678, 0);
lean_inc(x_1685);
x_1686 = lean_ctor_get(x_1678, 1);
lean_inc(x_1686);
lean_dec(x_1678);
x_1545 = x_1685;
x_1546 = x_1686;
goto block_1560;
}
}
else
{
lean_object* x_1687; lean_object* x_1688; 
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1493);
x_1687 = lean_ctor_get(x_1673, 0);
lean_inc(x_1687);
x_1688 = lean_ctor_get(x_1673, 1);
lean_inc(x_1688);
lean_dec(x_1673);
x_1545 = x_1687;
x_1546 = x_1688;
goto block_1560;
}
}
else
{
lean_object* x_1689; lean_object* x_1690; 
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1504);
lean_dec(x_1493);
x_1689 = lean_ctor_get(x_1670, 0);
lean_inc(x_1689);
x_1690 = lean_ctor_get(x_1670, 1);
lean_inc(x_1690);
lean_dec(x_1670);
x_1545 = x_1689;
x_1546 = x_1690;
goto block_1560;
}
}
else
{
lean_object* x_1691; lean_object* x_1692; 
lean_dec(x_1655);
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1506);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
x_1691 = lean_ctor_get(x_1657, 0);
lean_inc(x_1691);
x_1692 = lean_ctor_get(x_1657, 1);
lean_inc(x_1692);
lean_dec(x_1657);
x_1545 = x_1691;
x_1546 = x_1692;
goto block_1560;
}
}
else
{
lean_object* x_1693; lean_object* x_1694; 
lean_dec(x_1648);
lean_dec(x_1640);
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1506);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_1693 = lean_ctor_get(x_1650, 0);
lean_inc(x_1693);
x_1694 = lean_ctor_get(x_1650, 1);
lean_inc(x_1694);
lean_dec(x_1650);
x_1545 = x_1693;
x_1546 = x_1694;
goto block_1560;
}
}
else
{
lean_object* x_1695; lean_object* x_1696; 
lean_dec(x_1640);
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1507);
lean_dec(x_1506);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_1695 = lean_ctor_get(x_1647, 0);
lean_inc(x_1695);
x_1696 = lean_ctor_get(x_1647, 1);
lean_inc(x_1696);
lean_dec(x_1647);
x_1545 = x_1695;
x_1546 = x_1696;
goto block_1560;
}
}
else
{
lean_object* x_1697; lean_object* x_1698; 
lean_dec(x_1640);
lean_dec(x_1638);
lean_dec(x_1566);
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1507);
lean_dec(x_1506);
lean_dec(x_1505);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_1697 = lean_ctor_get(x_1641, 0);
lean_inc(x_1697);
x_1698 = lean_ctor_get(x_1641, 1);
lean_inc(x_1698);
lean_dec(x_1641);
x_1545 = x_1697;
x_1546 = x_1698;
goto block_1560;
}
}
else
{
lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; 
lean_dec(x_1638);
lean_dec(x_1570);
x_1699 = lean_array_push(x_1486, x_1505);
lean_inc(x_1507);
x_1700 = lean_array_push(x_1699, x_1507);
lean_inc(x_1516);
x_1701 = l_Lean_Meta_mkLambda(x_1700, x_1566, x_1516, x_1637);
if (lean_obj_tag(x_1701) == 0)
{
lean_object* x_1702; lean_object* x_1703; uint8_t x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; 
x_1702 = lean_ctor_get(x_1701, 0);
lean_inc(x_1702);
x_1703 = lean_ctor_get(x_1701, 1);
lean_inc(x_1703);
lean_dec(x_1701);
x_1704 = 2;
lean_inc(x_1516);
x_1705 = l_Lean_Meta_mkFreshExprMVar(x_1640, x_1439, x_1704, x_1516, x_1703);
x_1706 = lean_ctor_get(x_1705, 0);
lean_inc(x_1706);
x_1707 = lean_ctor_get(x_1705, 1);
lean_inc(x_1707);
lean_dec(x_1705);
lean_inc(x_1516);
lean_inc(x_1706);
x_1708 = l_Lean_Meta_mkEqRec(x_1702, x_1706, x_1507, x_1516, x_1707);
if (lean_obj_tag(x_1708) == 0)
{
lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; 
x_1709 = lean_ctor_get(x_1708, 1);
lean_inc(x_1709);
x_1710 = lean_ctor_get(x_1708, 0);
lean_inc(x_1710);
lean_dec(x_1708);
x_1711 = lean_ctor_get(x_1709, 0);
lean_inc(x_1711);
x_1712 = lean_ctor_get(x_1709, 1);
lean_inc(x_1712);
x_1713 = lean_ctor_get(x_1709, 2);
lean_inc(x_1713);
x_1714 = lean_ctor_get(x_1709, 3);
lean_inc(x_1714);
x_1715 = lean_ctor_get(x_1709, 4);
lean_inc(x_1715);
x_1716 = lean_ctor_get(x_1709, 5);
lean_inc(x_1716);
if (lean_is_exclusive(x_1709)) {
 lean_ctor_release(x_1709, 0);
 lean_ctor_release(x_1709, 1);
 lean_ctor_release(x_1709, 2);
 lean_ctor_release(x_1709, 3);
 lean_ctor_release(x_1709, 4);
 lean_ctor_release(x_1709, 5);
 x_1717 = x_1709;
} else {
 lean_dec_ref(x_1709);
 x_1717 = lean_box(0);
}
x_1718 = l_Lean_MetavarContext_assignExpr(x_1712, x_1502, x_1710);
if (lean_is_scalar(x_1717)) {
 x_1719 = lean_alloc_ctor(0, 6, 0);
} else {
 x_1719 = x_1717;
}
lean_ctor_set(x_1719, 0, x_1711);
lean_ctor_set(x_1719, 1, x_1718);
lean_ctor_set(x_1719, 2, x_1713);
lean_ctor_set(x_1719, 3, x_1714);
lean_ctor_set(x_1719, 4, x_1715);
lean_ctor_set(x_1719, 5, x_1716);
x_1720 = l_Lean_Expr_mvarId_x21(x_1706);
lean_dec(x_1706);
x_1721 = l_Lean_Meta_clear(x_1720, x_1506, x_1516, x_1719);
if (lean_obj_tag(x_1721) == 0)
{
lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; 
x_1722 = lean_ctor_get(x_1721, 0);
lean_inc(x_1722);
x_1723 = lean_ctor_get(x_1721, 1);
lean_inc(x_1723);
lean_dec(x_1721);
x_1724 = l_Lean_Meta_clear(x_1722, x_1504, x_1516, x_1723);
if (lean_obj_tag(x_1724) == 0)
{
lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; 
x_1725 = lean_ctor_get(x_1724, 0);
lean_inc(x_1725);
x_1726 = lean_ctor_get(x_1724, 1);
lean_inc(x_1726);
lean_dec(x_1724);
x_1727 = lean_array_get_size(x_1493);
lean_dec(x_1493);
x_1728 = lean_nat_sub(x_1727, x_1461);
lean_dec(x_1727);
x_1729 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1496, x_1725, x_1728, x_1495, x_1516, x_1726);
lean_dec(x_1516);
if (lean_obj_tag(x_1729) == 0)
{
lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; 
lean_dec(x_1500);
x_1730 = lean_ctor_get(x_1729, 0);
lean_inc(x_1730);
x_1731 = lean_ctor_get(x_1729, 1);
lean_inc(x_1731);
lean_dec(x_1729);
x_1732 = lean_ctor_get(x_1730, 1);
lean_inc(x_1732);
if (lean_is_exclusive(x_1730)) {
 lean_ctor_release(x_1730, 0);
 lean_ctor_release(x_1730, 1);
 x_1733 = x_1730;
} else {
 lean_dec_ref(x_1730);
 x_1733 = lean_box(0);
}
x_1734 = lean_box(0);
if (lean_is_scalar(x_1733)) {
 x_1735 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1735 = x_1733;
}
lean_ctor_set(x_1735, 0, x_1734);
lean_ctor_set(x_1735, 1, x_1732);
x_1529 = x_1735;
x_1530 = x_1731;
goto block_1544;
}
else
{
lean_object* x_1736; lean_object* x_1737; 
lean_dec(x_1511);
x_1736 = lean_ctor_get(x_1729, 0);
lean_inc(x_1736);
x_1737 = lean_ctor_get(x_1729, 1);
lean_inc(x_1737);
lean_dec(x_1729);
x_1545 = x_1736;
x_1546 = x_1737;
goto block_1560;
}
}
else
{
lean_object* x_1738; lean_object* x_1739; 
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1493);
x_1738 = lean_ctor_get(x_1724, 0);
lean_inc(x_1738);
x_1739 = lean_ctor_get(x_1724, 1);
lean_inc(x_1739);
lean_dec(x_1724);
x_1545 = x_1738;
x_1546 = x_1739;
goto block_1560;
}
}
else
{
lean_object* x_1740; lean_object* x_1741; 
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1504);
lean_dec(x_1493);
x_1740 = lean_ctor_get(x_1721, 0);
lean_inc(x_1740);
x_1741 = lean_ctor_get(x_1721, 1);
lean_inc(x_1741);
lean_dec(x_1721);
x_1545 = x_1740;
x_1546 = x_1741;
goto block_1560;
}
}
else
{
lean_object* x_1742; lean_object* x_1743; 
lean_dec(x_1706);
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1506);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
x_1742 = lean_ctor_get(x_1708, 0);
lean_inc(x_1742);
x_1743 = lean_ctor_get(x_1708, 1);
lean_inc(x_1743);
lean_dec(x_1708);
x_1545 = x_1742;
x_1546 = x_1743;
goto block_1560;
}
}
else
{
lean_object* x_1744; lean_object* x_1745; 
lean_dec(x_1640);
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1507);
lean_dec(x_1506);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_1744 = lean_ctor_get(x_1701, 0);
lean_inc(x_1744);
x_1745 = lean_ctor_get(x_1701, 1);
lean_inc(x_1745);
lean_dec(x_1701);
x_1545 = x_1744;
x_1546 = x_1745;
goto block_1560;
}
}
}
else
{
lean_object* x_1746; lean_object* x_1747; 
lean_dec(x_1634);
lean_dec(x_1570);
lean_dec(x_1566);
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1507);
lean_dec(x_1506);
lean_dec(x_1505);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_1746 = lean_ctor_get(x_1635, 0);
lean_inc(x_1746);
x_1747 = lean_ctor_get(x_1635, 1);
lean_inc(x_1747);
lean_dec(x_1635);
x_1545 = x_1746;
x_1546 = x_1747;
goto block_1560;
}
}
}
}
else
{
lean_object* x_1765; lean_object* x_1766; 
lean_dec(x_1566);
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1507);
lean_dec(x_1506);
lean_dec(x_1505);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_1765 = lean_ctor_get(x_1567, 0);
lean_inc(x_1765);
x_1766 = lean_ctor_get(x_1567, 1);
lean_inc(x_1766);
lean_dec(x_1567);
x_1545 = x_1765;
x_1546 = x_1766;
goto block_1560;
}
}
else
{
lean_object* x_1767; lean_object* x_1768; 
lean_dec(x_1516);
lean_dec(x_1511);
lean_dec(x_1507);
lean_dec(x_1506);
lean_dec(x_1505);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1493);
lean_dec(x_1439);
x_1767 = lean_ctor_get(x_1563, 0);
lean_inc(x_1767);
x_1768 = lean_ctor_get(x_1563, 1);
lean_inc(x_1768);
lean_dec(x_1563);
x_1545 = x_1767;
x_1546 = x_1768;
goto block_1560;
}
block_1544:
{
lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; 
x_1531 = lean_ctor_get(x_1530, 2);
lean_inc(x_1531);
x_1532 = lean_ctor_get(x_1530, 0);
lean_inc(x_1532);
x_1533 = lean_ctor_get(x_1530, 1);
lean_inc(x_1533);
x_1534 = lean_ctor_get(x_1530, 3);
lean_inc(x_1534);
x_1535 = lean_ctor_get(x_1530, 4);
lean_inc(x_1535);
x_1536 = lean_ctor_get(x_1530, 5);
lean_inc(x_1536);
if (lean_is_exclusive(x_1530)) {
 lean_ctor_release(x_1530, 0);
 lean_ctor_release(x_1530, 1);
 lean_ctor_release(x_1530, 2);
 lean_ctor_release(x_1530, 3);
 lean_ctor_release(x_1530, 4);
 lean_ctor_release(x_1530, 5);
 x_1537 = x_1530;
} else {
 lean_dec_ref(x_1530);
 x_1537 = lean_box(0);
}
x_1538 = lean_ctor_get(x_1531, 0);
lean_inc(x_1538);
x_1539 = lean_ctor_get(x_1531, 1);
lean_inc(x_1539);
if (lean_is_exclusive(x_1531)) {
 lean_ctor_release(x_1531, 0);
 lean_ctor_release(x_1531, 1);
 lean_ctor_release(x_1531, 2);
 x_1540 = x_1531;
} else {
 lean_dec_ref(x_1531);
 x_1540 = lean_box(0);
}
if (lean_is_scalar(x_1540)) {
 x_1541 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1541 = x_1540;
}
lean_ctor_set(x_1541, 0, x_1538);
lean_ctor_set(x_1541, 1, x_1539);
lean_ctor_set(x_1541, 2, x_1527);
if (lean_is_scalar(x_1537)) {
 x_1542 = lean_alloc_ctor(0, 6, 0);
} else {
 x_1542 = x_1537;
}
lean_ctor_set(x_1542, 0, x_1532);
lean_ctor_set(x_1542, 1, x_1533);
lean_ctor_set(x_1542, 2, x_1541);
lean_ctor_set(x_1542, 3, x_1534);
lean_ctor_set(x_1542, 4, x_1535);
lean_ctor_set(x_1542, 5, x_1536);
if (lean_is_scalar(x_1511)) {
 x_1543 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1543 = x_1511;
}
lean_ctor_set(x_1543, 0, x_1529);
lean_ctor_set(x_1543, 1, x_1542);
x_1430 = x_1543;
goto block_1435;
}
block_1560:
{
lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; 
x_1547 = lean_ctor_get(x_1546, 2);
lean_inc(x_1547);
x_1548 = lean_ctor_get(x_1546, 0);
lean_inc(x_1548);
x_1549 = lean_ctor_get(x_1546, 1);
lean_inc(x_1549);
x_1550 = lean_ctor_get(x_1546, 3);
lean_inc(x_1550);
x_1551 = lean_ctor_get(x_1546, 4);
lean_inc(x_1551);
x_1552 = lean_ctor_get(x_1546, 5);
lean_inc(x_1552);
if (lean_is_exclusive(x_1546)) {
 lean_ctor_release(x_1546, 0);
 lean_ctor_release(x_1546, 1);
 lean_ctor_release(x_1546, 2);
 lean_ctor_release(x_1546, 3);
 lean_ctor_release(x_1546, 4);
 lean_ctor_release(x_1546, 5);
 x_1553 = x_1546;
} else {
 lean_dec_ref(x_1546);
 x_1553 = lean_box(0);
}
x_1554 = lean_ctor_get(x_1547, 0);
lean_inc(x_1554);
x_1555 = lean_ctor_get(x_1547, 1);
lean_inc(x_1555);
if (lean_is_exclusive(x_1547)) {
 lean_ctor_release(x_1547, 0);
 lean_ctor_release(x_1547, 1);
 lean_ctor_release(x_1547, 2);
 x_1556 = x_1547;
} else {
 lean_dec_ref(x_1547);
 x_1556 = lean_box(0);
}
if (lean_is_scalar(x_1556)) {
 x_1557 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1557 = x_1556;
}
lean_ctor_set(x_1557, 0, x_1554);
lean_ctor_set(x_1557, 1, x_1555);
lean_ctor_set(x_1557, 2, x_1527);
if (lean_is_scalar(x_1553)) {
 x_1558 = lean_alloc_ctor(0, 6, 0);
} else {
 x_1558 = x_1553;
}
lean_ctor_set(x_1558, 0, x_1548);
lean_ctor_set(x_1558, 1, x_1549);
lean_ctor_set(x_1558, 2, x_1557);
lean_ctor_set(x_1558, 3, x_1550);
lean_ctor_set(x_1558, 4, x_1551);
lean_ctor_set(x_1558, 5, x_1552);
if (lean_is_scalar(x_1500)) {
 x_1559 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1559 = x_1500;
 lean_ctor_set_tag(x_1559, 1);
}
lean_ctor_set(x_1559, 0, x_1545);
lean_ctor_set(x_1559, 1, x_1558);
x_1430 = x_1559;
goto block_1435;
}
}
}
else
{
lean_object* x_2023; lean_object* x_2024; 
lean_dec(x_1507);
lean_dec(x_1506);
lean_dec(x_1505);
lean_dec(x_1504);
lean_dec(x_1502);
lean_dec(x_1500);
lean_dec(x_1493);
lean_dec(x_1439);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_2023 = lean_ctor_get(x_1508, 0);
lean_inc(x_2023);
x_2024 = lean_ctor_get(x_1508, 1);
lean_inc(x_2024);
lean_dec(x_1508);
x_1414 = x_2023;
x_1415 = x_2024;
goto block_1429;
}
}
else
{
lean_object* x_2025; lean_object* x_2026; 
lean_dec(x_1493);
lean_dec(x_1439);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_2025 = lean_ctor_get(x_1497, 0);
lean_inc(x_2025);
x_2026 = lean_ctor_get(x_1497, 1);
lean_inc(x_2026);
lean_dec(x_1497);
x_1414 = x_2025;
x_1415 = x_2026;
goto block_1429;
}
}
else
{
lean_object* x_2027; lean_object* x_2028; 
lean_dec(x_1439);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_2027 = lean_ctor_get(x_1490, 0);
lean_inc(x_2027);
x_2028 = lean_ctor_get(x_1490, 1);
lean_inc(x_2028);
lean_dec(x_1490);
x_1414 = x_2027;
x_1415 = x_2028;
goto block_1429;
}
}
else
{
lean_object* x_2029; lean_object* x_2030; 
lean_dec(x_1482);
lean_dec(x_1439);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_2029 = lean_ctor_get(x_1484, 0);
lean_inc(x_2029);
x_2030 = lean_ctor_get(x_1484, 1);
lean_inc(x_2030);
lean_dec(x_1484);
x_1414 = x_2029;
x_1415 = x_2030;
goto block_1429;
}
}
}
else
{
lean_object* x_2046; 
lean_dec(x_1481);
lean_dec(x_1480);
lean_dec(x_1439);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_2046 = lean_box(0);
x_1466 = x_2046;
goto block_1479;
}
}
}
}
}
}
else
{
lean_object* x_2052; lean_object* x_2053; 
lean_dec(x_1439);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_2052 = lean_ctor_get(x_1444, 0);
lean_inc(x_2052);
x_2053 = lean_ctor_get(x_1444, 1);
lean_inc(x_2053);
lean_dec(x_1444);
x_1414 = x_2052;
x_1415 = x_2053;
goto block_1429;
}
}
else
{
lean_object* x_2054; lean_object* x_2055; 
lean_dec(x_1439);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_2054 = lean_ctor_get(x_1442, 0);
lean_inc(x_2054);
x_2055 = lean_ctor_get(x_1442, 1);
lean_inc(x_2055);
lean_dec(x_1442);
x_1414 = x_2054;
x_1415 = x_2055;
goto block_1429;
}
}
else
{
lean_object* x_2056; lean_object* x_2057; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_2056 = lean_ctor_get(x_1438, 0);
lean_inc(x_2056);
x_2057 = lean_ctor_get(x_1438, 1);
lean_inc(x_2057);
lean_dec(x_1438);
x_1414 = x_2056;
x_1415 = x_2057;
goto block_1429;
}
block_1413:
{
lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; 
x_1400 = lean_ctor_get(x_1399, 2);
lean_inc(x_1400);
x_1401 = lean_ctor_get(x_1399, 0);
lean_inc(x_1401);
x_1402 = lean_ctor_get(x_1399, 1);
lean_inc(x_1402);
x_1403 = lean_ctor_get(x_1399, 3);
lean_inc(x_1403);
x_1404 = lean_ctor_get(x_1399, 4);
lean_inc(x_1404);
x_1405 = lean_ctor_get(x_1399, 5);
lean_inc(x_1405);
if (lean_is_exclusive(x_1399)) {
 lean_ctor_release(x_1399, 0);
 lean_ctor_release(x_1399, 1);
 lean_ctor_release(x_1399, 2);
 lean_ctor_release(x_1399, 3);
 lean_ctor_release(x_1399, 4);
 lean_ctor_release(x_1399, 5);
 x_1406 = x_1399;
} else {
 lean_dec_ref(x_1399);
 x_1406 = lean_box(0);
}
x_1407 = lean_ctor_get(x_1400, 0);
lean_inc(x_1407);
x_1408 = lean_ctor_get(x_1400, 1);
lean_inc(x_1408);
if (lean_is_exclusive(x_1400)) {
 lean_ctor_release(x_1400, 0);
 lean_ctor_release(x_1400, 1);
 lean_ctor_release(x_1400, 2);
 x_1409 = x_1400;
} else {
 lean_dec_ref(x_1400);
 x_1409 = lean_box(0);
}
if (lean_is_scalar(x_1409)) {
 x_1410 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1410 = x_1409;
}
lean_ctor_set(x_1410, 0, x_1407);
lean_ctor_set(x_1410, 1, x_1408);
lean_ctor_set(x_1410, 2, x_1397);
if (lean_is_scalar(x_1406)) {
 x_1411 = lean_alloc_ctor(0, 6, 0);
} else {
 x_1411 = x_1406;
}
lean_ctor_set(x_1411, 0, x_1401);
lean_ctor_set(x_1411, 1, x_1402);
lean_ctor_set(x_1411, 2, x_1410);
lean_ctor_set(x_1411, 3, x_1403);
lean_ctor_set(x_1411, 4, x_1404);
lean_ctor_set(x_1411, 5, x_1405);
if (lean_is_scalar(x_10)) {
 x_1412 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1412 = x_10;
}
lean_ctor_set(x_1412, 0, x_1398);
lean_ctor_set(x_1412, 1, x_1411);
return x_1412;
}
block_1429:
{
lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; 
x_1416 = lean_ctor_get(x_1415, 2);
lean_inc(x_1416);
x_1417 = lean_ctor_get(x_1415, 0);
lean_inc(x_1417);
x_1418 = lean_ctor_get(x_1415, 1);
lean_inc(x_1418);
x_1419 = lean_ctor_get(x_1415, 3);
lean_inc(x_1419);
x_1420 = lean_ctor_get(x_1415, 4);
lean_inc(x_1420);
x_1421 = lean_ctor_get(x_1415, 5);
lean_inc(x_1421);
if (lean_is_exclusive(x_1415)) {
 lean_ctor_release(x_1415, 0);
 lean_ctor_release(x_1415, 1);
 lean_ctor_release(x_1415, 2);
 lean_ctor_release(x_1415, 3);
 lean_ctor_release(x_1415, 4);
 lean_ctor_release(x_1415, 5);
 x_1422 = x_1415;
} else {
 lean_dec_ref(x_1415);
 x_1422 = lean_box(0);
}
x_1423 = lean_ctor_get(x_1416, 0);
lean_inc(x_1423);
x_1424 = lean_ctor_get(x_1416, 1);
lean_inc(x_1424);
if (lean_is_exclusive(x_1416)) {
 lean_ctor_release(x_1416, 0);
 lean_ctor_release(x_1416, 1);
 lean_ctor_release(x_1416, 2);
 x_1425 = x_1416;
} else {
 lean_dec_ref(x_1416);
 x_1425 = lean_box(0);
}
if (lean_is_scalar(x_1425)) {
 x_1426 = lean_alloc_ctor(0, 3, 0);
} else {
 x_1426 = x_1425;
}
lean_ctor_set(x_1426, 0, x_1423);
lean_ctor_set(x_1426, 1, x_1424);
lean_ctor_set(x_1426, 2, x_1397);
if (lean_is_scalar(x_1422)) {
 x_1427 = lean_alloc_ctor(0, 6, 0);
} else {
 x_1427 = x_1422;
}
lean_ctor_set(x_1427, 0, x_1417);
lean_ctor_set(x_1427, 1, x_1418);
lean_ctor_set(x_1427, 2, x_1426);
lean_ctor_set(x_1427, 3, x_1419);
lean_ctor_set(x_1427, 4, x_1420);
lean_ctor_set(x_1427, 5, x_1421);
x_1428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1428, 0, x_1414);
lean_ctor_set(x_1428, 1, x_1427);
return x_1428;
}
block_1435:
{
if (lean_obj_tag(x_1430) == 0)
{
lean_object* x_1431; lean_object* x_1432; 
x_1431 = lean_ctor_get(x_1430, 0);
lean_inc(x_1431);
x_1432 = lean_ctor_get(x_1430, 1);
lean_inc(x_1432);
lean_dec(x_1430);
x_1398 = x_1431;
x_1399 = x_1432;
goto block_1413;
}
else
{
lean_object* x_1433; lean_object* x_1434; 
lean_dec(x_10);
x_1433 = lean_ctor_get(x_1430, 0);
lean_inc(x_1433);
x_1434 = lean_ctor_get(x_1430, 1);
lean_inc(x_1434);
lean_dec(x_1430);
x_1414 = x_1433;
x_1415 = x_1434;
goto block_1429;
}
}
}
}
else
{
lean_object* x_2058; lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; lean_object* x_2063; lean_object* x_2064; lean_object* x_2065; lean_object* x_2066; lean_object* x_2067; lean_object* x_2068; lean_object* x_2069; lean_object* x_2084; lean_object* x_2085; lean_object* x_2100; lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; lean_object* x_2109; 
x_2058 = lean_ctor_get(x_9, 2);
x_2059 = lean_ctor_get(x_9, 0);
x_2060 = lean_ctor_get(x_9, 1);
x_2061 = lean_ctor_get(x_9, 3);
x_2062 = lean_ctor_get(x_9, 4);
x_2063 = lean_ctor_get(x_9, 5);
lean_inc(x_2063);
lean_inc(x_2062);
lean_inc(x_2061);
lean_inc(x_2058);
lean_inc(x_2060);
lean_inc(x_2059);
lean_dec(x_9);
x_2064 = lean_ctor_get(x_2058, 0);
lean_inc(x_2064);
x_2065 = lean_ctor_get(x_2058, 1);
lean_inc(x_2065);
x_2066 = lean_ctor_get(x_2058, 2);
lean_inc(x_2066);
if (lean_is_exclusive(x_2058)) {
 lean_ctor_release(x_2058, 0);
 lean_ctor_release(x_2058, 1);
 lean_ctor_release(x_2058, 2);
 x_2067 = x_2058;
} else {
 lean_dec_ref(x_2058);
 x_2067 = lean_box(0);
}
x_2106 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_2067)) {
 x_2107 = lean_alloc_ctor(0, 3, 0);
} else {
 x_2107 = x_2067;
}
lean_ctor_set(x_2107, 0, x_2064);
lean_ctor_set(x_2107, 1, x_2065);
lean_ctor_set(x_2107, 2, x_2106);
x_2108 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2108, 0, x_2059);
lean_ctor_set(x_2108, 1, x_2060);
lean_ctor_set(x_2108, 2, x_2107);
lean_ctor_set(x_2108, 3, x_2061);
lean_ctor_set(x_2108, 4, x_2062);
lean_ctor_set(x_2108, 5, x_2063);
lean_inc(x_1);
x_2109 = l_Lean_Meta_getMVarTag(x_1, x_20, x_2108);
if (lean_obj_tag(x_2109) == 0)
{
lean_object* x_2110; lean_object* x_2111; lean_object* x_2112; lean_object* x_2113; 
x_2110 = lean_ctor_get(x_2109, 0);
lean_inc(x_2110);
x_2111 = lean_ctor_get(x_2109, 1);
lean_inc(x_2111);
lean_dec(x_2109);
x_2112 = l_Lean_Meta_substCore___closed__2;
lean_inc(x_1);
x_2113 = l_Lean_Meta_checkNotAssigned(x_1, x_2112, x_20, x_2111);
if (lean_obj_tag(x_2113) == 0)
{
lean_object* x_2114; lean_object* x_2115; 
x_2114 = lean_ctor_get(x_2113, 1);
lean_inc(x_2114);
lean_dec(x_2113);
lean_inc(x_20);
lean_inc(x_2);
x_2115 = l_Lean_Meta_getLocalDecl(x_2, x_20, x_2114);
if (lean_obj_tag(x_2115) == 0)
{
lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; lean_object* x_2119; lean_object* x_2120; uint8_t x_2121; 
x_2116 = lean_ctor_get(x_2115, 0);
lean_inc(x_2116);
x_2117 = lean_ctor_get(x_2115, 1);
lean_inc(x_2117);
lean_dec(x_2115);
x_2118 = l_Lean_LocalDecl_type(x_2116);
lean_dec(x_2116);
x_2119 = l_Lean_Expr_eq_x3f___closed__2;
x_2120 = lean_unsigned_to_nat(3u);
x_2121 = l_Lean_Expr_isAppOfArity___main(x_2118, x_2119, x_2120);
if (x_2121 == 0)
{
lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; 
lean_dec(x_2118);
lean_dec(x_2110);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_2122 = l_Lean_Meta_substCore___closed__5;
x_2123 = l_Lean_Meta_throwTacticEx___rarg(x_2112, x_1, x_2122, x_20, x_2117);
lean_dec(x_20);
x_2124 = lean_ctor_get(x_2123, 0);
lean_inc(x_2124);
x_2125 = lean_ctor_get(x_2123, 1);
lean_inc(x_2125);
lean_dec(x_2123);
x_2084 = x_2124;
x_2085 = x_2125;
goto block_2099;
}
else
{
lean_object* x_2126; lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; lean_object* x_2133; lean_object* x_2134; lean_object* x_2135; uint8_t x_2136; 
x_2126 = lean_unsigned_to_nat(0u);
x_2127 = l_Lean_Expr_getAppNumArgsAux___main(x_2118, x_2126);
x_2128 = lean_unsigned_to_nat(1u);
x_2129 = lean_nat_sub(x_2127, x_2128);
x_2130 = lean_nat_sub(x_2129, x_2128);
lean_dec(x_2129);
x_2131 = l_Lean_Expr_getRevArg_x21___main(x_2118, x_2130);
x_2132 = lean_unsigned_to_nat(2u);
x_2133 = lean_nat_sub(x_2127, x_2132);
lean_dec(x_2127);
x_2134 = lean_nat_sub(x_2133, x_2128);
lean_dec(x_2133);
x_2135 = l_Lean_Expr_getRevArg_x21___main(x_2118, x_2134);
if (x_3 == 0)
{
uint8_t x_2721; 
x_2721 = 0;
x_2136 = x_2721;
goto block_2720;
}
else
{
uint8_t x_2722; 
x_2722 = 1;
x_2136 = x_2722;
goto block_2720;
}
block_2720:
{
lean_object* x_2137; lean_object* x_2151; 
if (x_2136 == 0)
{
lean_inc(x_2131);
x_2151 = x_2131;
goto block_2719;
}
else
{
lean_inc(x_2135);
x_2151 = x_2135;
goto block_2719;
}
block_2150:
{
lean_object* x_2138; lean_object* x_2139; 
lean_dec(x_2137);
x_2138 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2138, 0, x_2118);
x_2139 = l_Lean_indentExpr(x_2138);
if (x_2136 == 0)
{
lean_object* x_2140; lean_object* x_2141; lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; 
x_2140 = l_Lean_Meta_substCore___closed__12;
x_2141 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2141, 0, x_2140);
lean_ctor_set(x_2141, 1, x_2139);
x_2142 = l_Lean_Meta_throwTacticEx___rarg(x_2112, x_1, x_2141, x_20, x_2117);
lean_dec(x_20);
x_2143 = lean_ctor_get(x_2142, 0);
lean_inc(x_2143);
x_2144 = lean_ctor_get(x_2142, 1);
lean_inc(x_2144);
lean_dec(x_2142);
x_2084 = x_2143;
x_2085 = x_2144;
goto block_2099;
}
else
{
lean_object* x_2145; lean_object* x_2146; lean_object* x_2147; lean_object* x_2148; lean_object* x_2149; 
x_2145 = l_Lean_Meta_substCore___closed__16;
x_2146 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2146, 0, x_2145);
lean_ctor_set(x_2146, 1, x_2139);
x_2147 = l_Lean_Meta_throwTacticEx___rarg(x_2112, x_1, x_2146, x_20, x_2117);
lean_dec(x_20);
x_2148 = lean_ctor_get(x_2147, 0);
lean_inc(x_2148);
x_2149 = lean_ctor_get(x_2147, 1);
lean_inc(x_2149);
lean_dec(x_2147);
x_2084 = x_2148;
x_2085 = x_2149;
goto block_2099;
}
}
block_2719:
{
lean_object* x_2152; 
if (x_2136 == 0)
{
lean_dec(x_2131);
x_2152 = x_2135;
goto block_2718;
}
else
{
lean_dec(x_2135);
x_2152 = x_2131;
goto block_2718;
}
block_2718:
{
if (lean_obj_tag(x_2151) == 1)
{
lean_object* x_2153; lean_object* x_2154; lean_object* x_2703; lean_object* x_2704; uint8_t x_2705; 
lean_dec(x_2118);
x_2153 = lean_ctor_get(x_2151, 0);
lean_inc(x_2153);
x_2703 = lean_ctor_get(x_2117, 1);
lean_inc(x_2703);
lean_inc(x_2152);
x_2704 = l_Lean_MetavarContext_exprDependsOn(x_2703, x_2152, x_2153);
x_2705 = lean_unbox(x_2704);
lean_dec(x_2704);
if (x_2705 == 0)
{
lean_dec(x_2152);
lean_dec(x_2151);
x_2154 = x_2117;
goto block_2702;
}
else
{
lean_object* x_2706; lean_object* x_2707; lean_object* x_2708; lean_object* x_2709; lean_object* x_2710; lean_object* x_2711; lean_object* x_2712; lean_object* x_2713; lean_object* x_2714; lean_object* x_2715; lean_object* x_2716; 
lean_dec(x_2153);
lean_dec(x_2110);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_2706 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2706, 0, x_2151);
x_2707 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_2708 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2708, 0, x_2707);
lean_ctor_set(x_2708, 1, x_2706);
x_2709 = l_Lean_Meta_substCore___closed__21;
x_2710 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2710, 0, x_2708);
lean_ctor_set(x_2710, 1, x_2709);
x_2711 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2711, 0, x_2152);
x_2712 = l_Lean_indentExpr(x_2711);
x_2713 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2713, 0, x_2710);
lean_ctor_set(x_2713, 1, x_2712);
x_2714 = l_Lean_Meta_throwTacticEx___rarg(x_2112, x_1, x_2713, x_20, x_2117);
lean_dec(x_20);
x_2715 = lean_ctor_get(x_2714, 0);
lean_inc(x_2715);
x_2716 = lean_ctor_get(x_2714, 1);
lean_inc(x_2716);
lean_dec(x_2714);
x_2084 = x_2715;
x_2085 = x_2716;
goto block_2099;
}
block_2702:
{
lean_object* x_2155; 
lean_inc(x_20);
lean_inc(x_2153);
x_2155 = l_Lean_Meta_getLocalDecl(x_2153, x_20, x_2154);
if (lean_obj_tag(x_2155) == 0)
{
lean_object* x_2156; lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; uint8_t x_2160; lean_object* x_2161; 
x_2156 = lean_ctor_get(x_2155, 1);
lean_inc(x_2156);
lean_dec(x_2155);
x_2157 = l_Lean_mkAppStx___closed__9;
x_2158 = lean_array_push(x_2157, x_2153);
x_2159 = lean_array_push(x_2158, x_2);
x_2160 = 1;
x_2161 = l_Lean_Meta_revert(x_1, x_2159, x_2160, x_20, x_2156);
if (lean_obj_tag(x_2161) == 0)
{
lean_object* x_2162; lean_object* x_2163; lean_object* x_2164; lean_object* x_2165; lean_object* x_2166; uint8_t x_2167; lean_object* x_2168; 
x_2162 = lean_ctor_get(x_2161, 0);
lean_inc(x_2162);
x_2163 = lean_ctor_get(x_2161, 1);
lean_inc(x_2163);
lean_dec(x_2161);
x_2164 = lean_ctor_get(x_2162, 0);
lean_inc(x_2164);
x_2165 = lean_ctor_get(x_2162, 1);
lean_inc(x_2165);
lean_dec(x_2162);
x_2166 = lean_box(0);
x_2167 = 0;
x_2168 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2167, x_2165, x_2132, x_2166, x_20, x_2163);
if (lean_obj_tag(x_2168) == 0)
{
lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; lean_object* x_2172; lean_object* x_2173; lean_object* x_2174; lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; lean_object* x_2178; lean_object* x_2179; 
x_2169 = lean_ctor_get(x_2168, 0);
lean_inc(x_2169);
x_2170 = lean_ctor_get(x_2168, 1);
lean_inc(x_2170);
if (lean_is_exclusive(x_2168)) {
 lean_ctor_release(x_2168, 0);
 lean_ctor_release(x_2168, 1);
 x_2171 = x_2168;
} else {
 lean_dec_ref(x_2168);
 x_2171 = lean_box(0);
}
x_2172 = lean_ctor_get(x_2169, 0);
lean_inc(x_2172);
x_2173 = lean_ctor_get(x_2169, 1);
lean_inc(x_2173);
lean_dec(x_2169);
x_2174 = l_Lean_Name_inhabited;
x_2175 = lean_array_get(x_2174, x_2172, x_2126);
lean_inc(x_2175);
x_2176 = l_Lean_mkFVar(x_2175);
x_2177 = lean_array_get(x_2174, x_2172, x_2128);
lean_dec(x_2172);
lean_inc(x_2177);
x_2178 = l_Lean_mkFVar(x_2177);
lean_inc(x_2173);
x_2179 = l_Lean_Meta_getMVarDecl(x_2173, x_20, x_2170);
lean_dec(x_20);
if (lean_obj_tag(x_2179) == 0)
{
lean_object* x_2180; lean_object* x_2181; lean_object* x_2182; lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; uint8_t x_2186; lean_object* x_2187; lean_object* x_2188; 
x_2180 = lean_ctor_get(x_2179, 0);
lean_inc(x_2180);
x_2181 = lean_ctor_get(x_2179, 1);
lean_inc(x_2181);
if (lean_is_exclusive(x_2179)) {
 lean_ctor_release(x_2179, 0);
 lean_ctor_release(x_2179, 1);
 x_2182 = x_2179;
} else {
 lean_dec_ref(x_2179);
 x_2182 = lean_box(0);
}
x_2183 = lean_ctor_get(x_2180, 1);
lean_inc(x_2183);
x_2184 = lean_ctor_get(x_2180, 4);
lean_inc(x_2184);
x_2185 = lean_array_get_size(x_2184);
x_2186 = lean_nat_dec_eq(x_18, x_2185);
lean_dec(x_2185);
lean_dec(x_18);
lean_inc(x_2184);
x_2187 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_2187, 0, x_11);
lean_ctor_set(x_2187, 1, x_2183);
lean_ctor_set(x_2187, 2, x_2184);
lean_ctor_set(x_2187, 3, x_13);
lean_ctor_set(x_2187, 4, x_14);
if (x_2186 == 0)
{
lean_object* x_2441; 
lean_dec(x_2184);
lean_dec(x_2180);
lean_dec(x_16);
lean_dec(x_8);
x_2441 = lean_box(0);
x_2188 = x_2441;
goto block_2440;
}
else
{
uint8_t x_2442; 
x_2442 = l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__1(x_8, x_2180, lean_box(0), x_16, x_2184, x_2126);
lean_dec(x_2184);
lean_dec(x_16);
lean_dec(x_2180);
lean_dec(x_8);
if (x_2442 == 0)
{
lean_object* x_2443; 
x_2443 = lean_box(0);
x_2188 = x_2443;
goto block_2440;
}
else
{
lean_object* x_2444; 
lean_dec(x_2182);
lean_dec(x_2171);
lean_inc(x_2173);
x_2444 = l_Lean_Meta_getMVarDecl(x_2173, x_2187, x_2181);
if (lean_obj_tag(x_2444) == 0)
{
lean_object* x_2445; lean_object* x_2446; lean_object* x_2447; lean_object* x_2448; 
x_2445 = lean_ctor_get(x_2444, 0);
lean_inc(x_2445);
x_2446 = lean_ctor_get(x_2444, 1);
lean_inc(x_2446);
lean_dec(x_2444);
x_2447 = lean_ctor_get(x_2445, 2);
lean_inc(x_2447);
lean_dec(x_2445);
lean_inc(x_2187);
lean_inc(x_2177);
x_2448 = l_Lean_Meta_getLocalDecl(x_2177, x_2187, x_2446);
if (lean_obj_tag(x_2448) == 0)
{
lean_object* x_2449; lean_object* x_2450; lean_object* x_2451; lean_object* x_2674; uint8_t x_2675; 
x_2449 = lean_ctor_get(x_2448, 0);
lean_inc(x_2449);
x_2450 = lean_ctor_get(x_2448, 1);
lean_inc(x_2450);
lean_dec(x_2448);
x_2674 = l_Lean_LocalDecl_type(x_2449);
lean_dec(x_2449);
x_2675 = l_Lean_Expr_isAppOfArity___main(x_2674, x_2119, x_2120);
if (x_2675 == 0)
{
lean_object* x_2676; lean_object* x_2677; lean_object* x_2678; 
lean_dec(x_2674);
lean_dec(x_2447);
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2176);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2676 = l_Lean_Meta_isClassQuick___main___closed__1;
x_2677 = l_unreachable_x21___rarg(x_2676);
x_2678 = lean_apply_2(x_2677, x_2187, x_2450);
x_2100 = x_2678;
goto block_2105;
}
else
{
lean_object* x_2679; 
x_2679 = l_Lean_Expr_getAppNumArgsAux___main(x_2674, x_2126);
if (x_2136 == 0)
{
lean_object* x_2680; lean_object* x_2681; lean_object* x_2682; 
x_2680 = lean_nat_sub(x_2679, x_2132);
lean_dec(x_2679);
x_2681 = lean_nat_sub(x_2680, x_2128);
lean_dec(x_2680);
x_2682 = l_Lean_Expr_getRevArg_x21___main(x_2674, x_2681);
lean_dec(x_2674);
x_2451 = x_2682;
goto block_2673;
}
else
{
lean_object* x_2683; lean_object* x_2684; lean_object* x_2685; 
x_2683 = lean_nat_sub(x_2679, x_2128);
lean_dec(x_2679);
x_2684 = lean_nat_sub(x_2683, x_2128);
lean_dec(x_2683);
x_2685 = l_Lean_Expr_getRevArg_x21___main(x_2674, x_2684);
lean_dec(x_2674);
x_2451 = x_2685;
goto block_2673;
}
}
block_2673:
{
lean_object* x_2452; lean_object* x_2453; uint8_t x_2454; 
x_2452 = lean_ctor_get(x_2450, 1);
lean_inc(x_2452);
lean_inc(x_2447);
x_2453 = l_Lean_MetavarContext_exprDependsOn(x_2452, x_2447, x_2177);
x_2454 = lean_unbox(x_2453);
lean_dec(x_2453);
if (x_2454 == 0)
{
lean_object* x_2455; lean_object* x_2456; lean_object* x_2457; 
x_2455 = l_Lean_mkOptionalNode___closed__2;
x_2456 = lean_array_push(x_2455, x_2176);
lean_inc(x_2187);
lean_inc(x_2447);
lean_inc(x_2456);
x_2457 = l_Lean_Meta_mkLambda(x_2456, x_2447, x_2187, x_2450);
if (lean_obj_tag(x_2457) == 0)
{
lean_object* x_2458; lean_object* x_2459; lean_object* x_2460; lean_object* x_2461; lean_object* x_2462; lean_object* x_2463; 
x_2458 = lean_ctor_get(x_2457, 0);
lean_inc(x_2458);
x_2459 = lean_ctor_get(x_2457, 1);
lean_inc(x_2459);
lean_dec(x_2457);
x_2460 = lean_expr_abstract(x_2447, x_2456);
lean_dec(x_2456);
lean_dec(x_2447);
x_2461 = lean_expr_instantiate1(x_2460, x_2451);
lean_dec(x_2451);
lean_dec(x_2460);
if (x_2136 == 0)
{
lean_object* x_2515; 
lean_inc(x_2187);
x_2515 = l_Lean_Meta_mkEqSymm(x_2178, x_2187, x_2459);
if (lean_obj_tag(x_2515) == 0)
{
lean_object* x_2516; lean_object* x_2517; 
x_2516 = lean_ctor_get(x_2515, 0);
lean_inc(x_2516);
x_2517 = lean_ctor_get(x_2515, 1);
lean_inc(x_2517);
lean_dec(x_2515);
x_2462 = x_2516;
x_2463 = x_2517;
goto block_2514;
}
else
{
lean_object* x_2518; lean_object* x_2519; lean_object* x_2520; lean_object* x_2521; 
lean_dec(x_2461);
lean_dec(x_2458);
lean_dec(x_2187);
lean_dec(x_2177);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2518 = lean_ctor_get(x_2515, 0);
lean_inc(x_2518);
x_2519 = lean_ctor_get(x_2515, 1);
lean_inc(x_2519);
if (lean_is_exclusive(x_2515)) {
 lean_ctor_release(x_2515, 0);
 lean_ctor_release(x_2515, 1);
 x_2520 = x_2515;
} else {
 lean_dec_ref(x_2515);
 x_2520 = lean_box(0);
}
if (lean_is_scalar(x_2520)) {
 x_2521 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2521 = x_2520;
}
lean_ctor_set(x_2521, 0, x_2518);
lean_ctor_set(x_2521, 1, x_2519);
x_2100 = x_2521;
goto block_2105;
}
}
else
{
x_2462 = x_2178;
x_2463 = x_2459;
goto block_2514;
}
block_2514:
{
uint8_t x_2464; lean_object* x_2465; lean_object* x_2466; lean_object* x_2467; lean_object* x_2468; 
x_2464 = 2;
lean_inc(x_2187);
x_2465 = l_Lean_Meta_mkFreshExprMVar(x_2461, x_2110, x_2464, x_2187, x_2463);
x_2466 = lean_ctor_get(x_2465, 0);
lean_inc(x_2466);
x_2467 = lean_ctor_get(x_2465, 1);
lean_inc(x_2467);
lean_dec(x_2465);
lean_inc(x_2187);
lean_inc(x_2466);
x_2468 = l_Lean_Meta_mkEqNDRec(x_2458, x_2466, x_2462, x_2187, x_2467);
if (lean_obj_tag(x_2468) == 0)
{
lean_object* x_2469; lean_object* x_2470; lean_object* x_2471; lean_object* x_2472; lean_object* x_2473; lean_object* x_2474; lean_object* x_2475; lean_object* x_2476; lean_object* x_2477; lean_object* x_2478; lean_object* x_2479; lean_object* x_2480; lean_object* x_2481; 
x_2469 = lean_ctor_get(x_2468, 1);
lean_inc(x_2469);
x_2470 = lean_ctor_get(x_2468, 0);
lean_inc(x_2470);
lean_dec(x_2468);
x_2471 = lean_ctor_get(x_2469, 0);
lean_inc(x_2471);
x_2472 = lean_ctor_get(x_2469, 1);
lean_inc(x_2472);
x_2473 = lean_ctor_get(x_2469, 2);
lean_inc(x_2473);
x_2474 = lean_ctor_get(x_2469, 3);
lean_inc(x_2474);
x_2475 = lean_ctor_get(x_2469, 4);
lean_inc(x_2475);
x_2476 = lean_ctor_get(x_2469, 5);
lean_inc(x_2476);
if (lean_is_exclusive(x_2469)) {
 lean_ctor_release(x_2469, 0);
 lean_ctor_release(x_2469, 1);
 lean_ctor_release(x_2469, 2);
 lean_ctor_release(x_2469, 3);
 lean_ctor_release(x_2469, 4);
 lean_ctor_release(x_2469, 5);
 x_2477 = x_2469;
} else {
 lean_dec_ref(x_2469);
 x_2477 = lean_box(0);
}
x_2478 = l_Lean_MetavarContext_assignExpr(x_2472, x_2173, x_2470);
if (lean_is_scalar(x_2477)) {
 x_2479 = lean_alloc_ctor(0, 6, 0);
} else {
 x_2479 = x_2477;
}
lean_ctor_set(x_2479, 0, x_2471);
lean_ctor_set(x_2479, 1, x_2478);
lean_ctor_set(x_2479, 2, x_2473);
lean_ctor_set(x_2479, 3, x_2474);
lean_ctor_set(x_2479, 4, x_2475);
lean_ctor_set(x_2479, 5, x_2476);
x_2480 = l_Lean_Expr_mvarId_x21(x_2466);
lean_dec(x_2466);
x_2481 = l_Lean_Meta_clear(x_2480, x_2177, x_2187, x_2479);
if (lean_obj_tag(x_2481) == 0)
{
lean_object* x_2482; lean_object* x_2483; lean_object* x_2484; 
x_2482 = lean_ctor_get(x_2481, 0);
lean_inc(x_2482);
x_2483 = lean_ctor_get(x_2481, 1);
lean_inc(x_2483);
lean_dec(x_2481);
x_2484 = l_Lean_Meta_clear(x_2482, x_2175, x_2187, x_2483);
if (lean_obj_tag(x_2484) == 0)
{
lean_object* x_2485; lean_object* x_2486; lean_object* x_2487; lean_object* x_2488; lean_object* x_2489; 
x_2485 = lean_ctor_get(x_2484, 0);
lean_inc(x_2485);
x_2486 = lean_ctor_get(x_2484, 1);
lean_inc(x_2486);
lean_dec(x_2484);
x_2487 = lean_array_get_size(x_2164);
lean_dec(x_2164);
x_2488 = lean_nat_sub(x_2487, x_2132);
lean_dec(x_2487);
x_2489 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2167, x_2485, x_2488, x_2166, x_2187, x_2486);
lean_dec(x_2187);
if (lean_obj_tag(x_2489) == 0)
{
lean_object* x_2490; lean_object* x_2491; lean_object* x_2492; lean_object* x_2493; lean_object* x_2494; lean_object* x_2495; lean_object* x_2496; lean_object* x_2497; 
x_2490 = lean_ctor_get(x_2489, 0);
lean_inc(x_2490);
x_2491 = lean_ctor_get(x_2489, 1);
lean_inc(x_2491);
if (lean_is_exclusive(x_2489)) {
 lean_ctor_release(x_2489, 0);
 lean_ctor_release(x_2489, 1);
 x_2492 = x_2489;
} else {
 lean_dec_ref(x_2489);
 x_2492 = lean_box(0);
}
x_2493 = lean_ctor_get(x_2490, 1);
lean_inc(x_2493);
if (lean_is_exclusive(x_2490)) {
 lean_ctor_release(x_2490, 0);
 lean_ctor_release(x_2490, 1);
 x_2494 = x_2490;
} else {
 lean_dec_ref(x_2490);
 x_2494 = lean_box(0);
}
x_2495 = lean_box(0);
if (lean_is_scalar(x_2494)) {
 x_2496 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2496 = x_2494;
}
lean_ctor_set(x_2496, 0, x_2495);
lean_ctor_set(x_2496, 1, x_2493);
if (lean_is_scalar(x_2492)) {
 x_2497 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2497 = x_2492;
}
lean_ctor_set(x_2497, 0, x_2496);
lean_ctor_set(x_2497, 1, x_2491);
x_2100 = x_2497;
goto block_2105;
}
else
{
lean_object* x_2498; lean_object* x_2499; lean_object* x_2500; lean_object* x_2501; 
x_2498 = lean_ctor_get(x_2489, 0);
lean_inc(x_2498);
x_2499 = lean_ctor_get(x_2489, 1);
lean_inc(x_2499);
if (lean_is_exclusive(x_2489)) {
 lean_ctor_release(x_2489, 0);
 lean_ctor_release(x_2489, 1);
 x_2500 = x_2489;
} else {
 lean_dec_ref(x_2489);
 x_2500 = lean_box(0);
}
if (lean_is_scalar(x_2500)) {
 x_2501 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2501 = x_2500;
}
lean_ctor_set(x_2501, 0, x_2498);
lean_ctor_set(x_2501, 1, x_2499);
x_2100 = x_2501;
goto block_2105;
}
}
else
{
lean_object* x_2502; lean_object* x_2503; lean_object* x_2504; lean_object* x_2505; 
lean_dec(x_2187);
lean_dec(x_2164);
x_2502 = lean_ctor_get(x_2484, 0);
lean_inc(x_2502);
x_2503 = lean_ctor_get(x_2484, 1);
lean_inc(x_2503);
if (lean_is_exclusive(x_2484)) {
 lean_ctor_release(x_2484, 0);
 lean_ctor_release(x_2484, 1);
 x_2504 = x_2484;
} else {
 lean_dec_ref(x_2484);
 x_2504 = lean_box(0);
}
if (lean_is_scalar(x_2504)) {
 x_2505 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2505 = x_2504;
}
lean_ctor_set(x_2505, 0, x_2502);
lean_ctor_set(x_2505, 1, x_2503);
x_2100 = x_2505;
goto block_2105;
}
}
else
{
lean_object* x_2506; lean_object* x_2507; lean_object* x_2508; lean_object* x_2509; 
lean_dec(x_2187);
lean_dec(x_2175);
lean_dec(x_2164);
x_2506 = lean_ctor_get(x_2481, 0);
lean_inc(x_2506);
x_2507 = lean_ctor_get(x_2481, 1);
lean_inc(x_2507);
if (lean_is_exclusive(x_2481)) {
 lean_ctor_release(x_2481, 0);
 lean_ctor_release(x_2481, 1);
 x_2508 = x_2481;
} else {
 lean_dec_ref(x_2481);
 x_2508 = lean_box(0);
}
if (lean_is_scalar(x_2508)) {
 x_2509 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2509 = x_2508;
}
lean_ctor_set(x_2509, 0, x_2506);
lean_ctor_set(x_2509, 1, x_2507);
x_2100 = x_2509;
goto block_2105;
}
}
else
{
lean_object* x_2510; lean_object* x_2511; lean_object* x_2512; lean_object* x_2513; 
lean_dec(x_2466);
lean_dec(x_2187);
lean_dec(x_2177);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
x_2510 = lean_ctor_get(x_2468, 0);
lean_inc(x_2510);
x_2511 = lean_ctor_get(x_2468, 1);
lean_inc(x_2511);
if (lean_is_exclusive(x_2468)) {
 lean_ctor_release(x_2468, 0);
 lean_ctor_release(x_2468, 1);
 x_2512 = x_2468;
} else {
 lean_dec_ref(x_2468);
 x_2512 = lean_box(0);
}
if (lean_is_scalar(x_2512)) {
 x_2513 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2513 = x_2512;
}
lean_ctor_set(x_2513, 0, x_2510);
lean_ctor_set(x_2513, 1, x_2511);
x_2100 = x_2513;
goto block_2105;
}
}
}
else
{
lean_object* x_2522; lean_object* x_2523; lean_object* x_2524; lean_object* x_2525; 
lean_dec(x_2456);
lean_dec(x_2451);
lean_dec(x_2447);
lean_dec(x_2187);
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2522 = lean_ctor_get(x_2457, 0);
lean_inc(x_2522);
x_2523 = lean_ctor_get(x_2457, 1);
lean_inc(x_2523);
if (lean_is_exclusive(x_2457)) {
 lean_ctor_release(x_2457, 0);
 lean_ctor_release(x_2457, 1);
 x_2524 = x_2457;
} else {
 lean_dec_ref(x_2457);
 x_2524 = lean_box(0);
}
if (lean_is_scalar(x_2524)) {
 x_2525 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2525 = x_2524;
}
lean_ctor_set(x_2525, 0, x_2522);
lean_ctor_set(x_2525, 1, x_2523);
x_2100 = x_2525;
goto block_2105;
}
}
else
{
lean_object* x_2526; lean_object* x_2527; lean_object* x_2528; lean_object* x_2529; lean_object* x_2530; 
x_2526 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2176);
x_2527 = lean_array_push(x_2526, x_2176);
x_2528 = lean_expr_abstract(x_2447, x_2527);
lean_dec(x_2527);
x_2529 = lean_expr_instantiate1(x_2528, x_2451);
lean_dec(x_2528);
lean_inc(x_2187);
lean_inc(x_2451);
x_2530 = l_Lean_Meta_mkEqRefl(x_2451, x_2187, x_2450);
if (lean_obj_tag(x_2530) == 0)
{
lean_object* x_2531; lean_object* x_2532; lean_object* x_2533; lean_object* x_2534; lean_object* x_2535; 
x_2531 = lean_ctor_get(x_2530, 0);
lean_inc(x_2531);
x_2532 = lean_ctor_get(x_2530, 1);
lean_inc(x_2532);
lean_dec(x_2530);
lean_inc(x_2178);
x_2533 = lean_array_push(x_2526, x_2178);
x_2534 = lean_expr_abstract(x_2529, x_2533);
lean_dec(x_2529);
x_2535 = lean_expr_instantiate1(x_2534, x_2531);
lean_dec(x_2531);
lean_dec(x_2534);
if (x_2136 == 0)
{
lean_object* x_2536; 
lean_inc(x_2187);
lean_inc(x_2176);
x_2536 = l_Lean_Meta_mkEq(x_2451, x_2176, x_2187, x_2532);
if (lean_obj_tag(x_2536) == 0)
{
lean_object* x_2537; lean_object* x_2538; lean_object* x_2539; lean_object* x_2540; uint8_t x_2541; lean_object* x_2542; 
x_2537 = lean_ctor_get(x_2536, 0);
lean_inc(x_2537);
x_2538 = lean_ctor_get(x_2536, 1);
lean_inc(x_2538);
lean_dec(x_2536);
x_2539 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__1___boxed), 7, 4);
lean_closure_set(x_2539, 0, x_2447);
lean_closure_set(x_2539, 1, x_2533);
lean_closure_set(x_2539, 2, x_2157);
lean_closure_set(x_2539, 3, x_2176);
x_2540 = l_Lean_Meta_substCore___closed__18;
x_2541 = 0;
lean_inc(x_2187);
x_2542 = l_Lean_Meta_withLocalDecl___rarg(x_2540, x_2537, x_2541, x_2539, x_2187, x_2538);
if (lean_obj_tag(x_2542) == 0)
{
lean_object* x_2543; lean_object* x_2544; lean_object* x_2545; 
x_2543 = lean_ctor_get(x_2542, 0);
lean_inc(x_2543);
x_2544 = lean_ctor_get(x_2542, 1);
lean_inc(x_2544);
lean_dec(x_2542);
lean_inc(x_2187);
x_2545 = l_Lean_Meta_mkEqSymm(x_2178, x_2187, x_2544);
if (lean_obj_tag(x_2545) == 0)
{
lean_object* x_2546; lean_object* x_2547; uint8_t x_2548; lean_object* x_2549; lean_object* x_2550; lean_object* x_2551; lean_object* x_2552; 
x_2546 = lean_ctor_get(x_2545, 0);
lean_inc(x_2546);
x_2547 = lean_ctor_get(x_2545, 1);
lean_inc(x_2547);
lean_dec(x_2545);
x_2548 = 2;
lean_inc(x_2187);
x_2549 = l_Lean_Meta_mkFreshExprMVar(x_2535, x_2110, x_2548, x_2187, x_2547);
x_2550 = lean_ctor_get(x_2549, 0);
lean_inc(x_2550);
x_2551 = lean_ctor_get(x_2549, 1);
lean_inc(x_2551);
lean_dec(x_2549);
lean_inc(x_2187);
lean_inc(x_2550);
x_2552 = l_Lean_Meta_mkEqRec(x_2543, x_2550, x_2546, x_2187, x_2551);
if (lean_obj_tag(x_2552) == 0)
{
lean_object* x_2553; lean_object* x_2554; lean_object* x_2555; lean_object* x_2556; lean_object* x_2557; lean_object* x_2558; lean_object* x_2559; lean_object* x_2560; lean_object* x_2561; lean_object* x_2562; lean_object* x_2563; lean_object* x_2564; lean_object* x_2565; 
x_2553 = lean_ctor_get(x_2552, 1);
lean_inc(x_2553);
x_2554 = lean_ctor_get(x_2552, 0);
lean_inc(x_2554);
lean_dec(x_2552);
x_2555 = lean_ctor_get(x_2553, 0);
lean_inc(x_2555);
x_2556 = lean_ctor_get(x_2553, 1);
lean_inc(x_2556);
x_2557 = lean_ctor_get(x_2553, 2);
lean_inc(x_2557);
x_2558 = lean_ctor_get(x_2553, 3);
lean_inc(x_2558);
x_2559 = lean_ctor_get(x_2553, 4);
lean_inc(x_2559);
x_2560 = lean_ctor_get(x_2553, 5);
lean_inc(x_2560);
if (lean_is_exclusive(x_2553)) {
 lean_ctor_release(x_2553, 0);
 lean_ctor_release(x_2553, 1);
 lean_ctor_release(x_2553, 2);
 lean_ctor_release(x_2553, 3);
 lean_ctor_release(x_2553, 4);
 lean_ctor_release(x_2553, 5);
 x_2561 = x_2553;
} else {
 lean_dec_ref(x_2553);
 x_2561 = lean_box(0);
}
x_2562 = l_Lean_MetavarContext_assignExpr(x_2556, x_2173, x_2554);
if (lean_is_scalar(x_2561)) {
 x_2563 = lean_alloc_ctor(0, 6, 0);
} else {
 x_2563 = x_2561;
}
lean_ctor_set(x_2563, 0, x_2555);
lean_ctor_set(x_2563, 1, x_2562);
lean_ctor_set(x_2563, 2, x_2557);
lean_ctor_set(x_2563, 3, x_2558);
lean_ctor_set(x_2563, 4, x_2559);
lean_ctor_set(x_2563, 5, x_2560);
x_2564 = l_Lean_Expr_mvarId_x21(x_2550);
lean_dec(x_2550);
x_2565 = l_Lean_Meta_clear(x_2564, x_2177, x_2187, x_2563);
if (lean_obj_tag(x_2565) == 0)
{
lean_object* x_2566; lean_object* x_2567; lean_object* x_2568; 
x_2566 = lean_ctor_get(x_2565, 0);
lean_inc(x_2566);
x_2567 = lean_ctor_get(x_2565, 1);
lean_inc(x_2567);
lean_dec(x_2565);
x_2568 = l_Lean_Meta_clear(x_2566, x_2175, x_2187, x_2567);
if (lean_obj_tag(x_2568) == 0)
{
lean_object* x_2569; lean_object* x_2570; lean_object* x_2571; lean_object* x_2572; lean_object* x_2573; 
x_2569 = lean_ctor_get(x_2568, 0);
lean_inc(x_2569);
x_2570 = lean_ctor_get(x_2568, 1);
lean_inc(x_2570);
lean_dec(x_2568);
x_2571 = lean_array_get_size(x_2164);
lean_dec(x_2164);
x_2572 = lean_nat_sub(x_2571, x_2132);
lean_dec(x_2571);
x_2573 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2167, x_2569, x_2572, x_2166, x_2187, x_2570);
lean_dec(x_2187);
if (lean_obj_tag(x_2573) == 0)
{
lean_object* x_2574; lean_object* x_2575; lean_object* x_2576; lean_object* x_2577; lean_object* x_2578; lean_object* x_2579; lean_object* x_2580; lean_object* x_2581; 
x_2574 = lean_ctor_get(x_2573, 0);
lean_inc(x_2574);
x_2575 = lean_ctor_get(x_2573, 1);
lean_inc(x_2575);
if (lean_is_exclusive(x_2573)) {
 lean_ctor_release(x_2573, 0);
 lean_ctor_release(x_2573, 1);
 x_2576 = x_2573;
} else {
 lean_dec_ref(x_2573);
 x_2576 = lean_box(0);
}
x_2577 = lean_ctor_get(x_2574, 1);
lean_inc(x_2577);
if (lean_is_exclusive(x_2574)) {
 lean_ctor_release(x_2574, 0);
 lean_ctor_release(x_2574, 1);
 x_2578 = x_2574;
} else {
 lean_dec_ref(x_2574);
 x_2578 = lean_box(0);
}
x_2579 = lean_box(0);
if (lean_is_scalar(x_2578)) {
 x_2580 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2580 = x_2578;
}
lean_ctor_set(x_2580, 0, x_2579);
lean_ctor_set(x_2580, 1, x_2577);
if (lean_is_scalar(x_2576)) {
 x_2581 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2581 = x_2576;
}
lean_ctor_set(x_2581, 0, x_2580);
lean_ctor_set(x_2581, 1, x_2575);
x_2100 = x_2581;
goto block_2105;
}
else
{
lean_object* x_2582; lean_object* x_2583; lean_object* x_2584; lean_object* x_2585; 
x_2582 = lean_ctor_get(x_2573, 0);
lean_inc(x_2582);
x_2583 = lean_ctor_get(x_2573, 1);
lean_inc(x_2583);
if (lean_is_exclusive(x_2573)) {
 lean_ctor_release(x_2573, 0);
 lean_ctor_release(x_2573, 1);
 x_2584 = x_2573;
} else {
 lean_dec_ref(x_2573);
 x_2584 = lean_box(0);
}
if (lean_is_scalar(x_2584)) {
 x_2585 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2585 = x_2584;
}
lean_ctor_set(x_2585, 0, x_2582);
lean_ctor_set(x_2585, 1, x_2583);
x_2100 = x_2585;
goto block_2105;
}
}
else
{
lean_object* x_2586; lean_object* x_2587; lean_object* x_2588; lean_object* x_2589; 
lean_dec(x_2187);
lean_dec(x_2164);
x_2586 = lean_ctor_get(x_2568, 0);
lean_inc(x_2586);
x_2587 = lean_ctor_get(x_2568, 1);
lean_inc(x_2587);
if (lean_is_exclusive(x_2568)) {
 lean_ctor_release(x_2568, 0);
 lean_ctor_release(x_2568, 1);
 x_2588 = x_2568;
} else {
 lean_dec_ref(x_2568);
 x_2588 = lean_box(0);
}
if (lean_is_scalar(x_2588)) {
 x_2589 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2589 = x_2588;
}
lean_ctor_set(x_2589, 0, x_2586);
lean_ctor_set(x_2589, 1, x_2587);
x_2100 = x_2589;
goto block_2105;
}
}
else
{
lean_object* x_2590; lean_object* x_2591; lean_object* x_2592; lean_object* x_2593; 
lean_dec(x_2187);
lean_dec(x_2175);
lean_dec(x_2164);
x_2590 = lean_ctor_get(x_2565, 0);
lean_inc(x_2590);
x_2591 = lean_ctor_get(x_2565, 1);
lean_inc(x_2591);
if (lean_is_exclusive(x_2565)) {
 lean_ctor_release(x_2565, 0);
 lean_ctor_release(x_2565, 1);
 x_2592 = x_2565;
} else {
 lean_dec_ref(x_2565);
 x_2592 = lean_box(0);
}
if (lean_is_scalar(x_2592)) {
 x_2593 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2593 = x_2592;
}
lean_ctor_set(x_2593, 0, x_2590);
lean_ctor_set(x_2593, 1, x_2591);
x_2100 = x_2593;
goto block_2105;
}
}
else
{
lean_object* x_2594; lean_object* x_2595; lean_object* x_2596; lean_object* x_2597; 
lean_dec(x_2550);
lean_dec(x_2187);
lean_dec(x_2177);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
x_2594 = lean_ctor_get(x_2552, 0);
lean_inc(x_2594);
x_2595 = lean_ctor_get(x_2552, 1);
lean_inc(x_2595);
if (lean_is_exclusive(x_2552)) {
 lean_ctor_release(x_2552, 0);
 lean_ctor_release(x_2552, 1);
 x_2596 = x_2552;
} else {
 lean_dec_ref(x_2552);
 x_2596 = lean_box(0);
}
if (lean_is_scalar(x_2596)) {
 x_2597 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2597 = x_2596;
}
lean_ctor_set(x_2597, 0, x_2594);
lean_ctor_set(x_2597, 1, x_2595);
x_2100 = x_2597;
goto block_2105;
}
}
else
{
lean_object* x_2598; lean_object* x_2599; lean_object* x_2600; lean_object* x_2601; 
lean_dec(x_2543);
lean_dec(x_2535);
lean_dec(x_2187);
lean_dec(x_2177);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2598 = lean_ctor_get(x_2545, 0);
lean_inc(x_2598);
x_2599 = lean_ctor_get(x_2545, 1);
lean_inc(x_2599);
if (lean_is_exclusive(x_2545)) {
 lean_ctor_release(x_2545, 0);
 lean_ctor_release(x_2545, 1);
 x_2600 = x_2545;
} else {
 lean_dec_ref(x_2545);
 x_2600 = lean_box(0);
}
if (lean_is_scalar(x_2600)) {
 x_2601 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2601 = x_2600;
}
lean_ctor_set(x_2601, 0, x_2598);
lean_ctor_set(x_2601, 1, x_2599);
x_2100 = x_2601;
goto block_2105;
}
}
else
{
lean_object* x_2602; lean_object* x_2603; lean_object* x_2604; lean_object* x_2605; 
lean_dec(x_2535);
lean_dec(x_2187);
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2602 = lean_ctor_get(x_2542, 0);
lean_inc(x_2602);
x_2603 = lean_ctor_get(x_2542, 1);
lean_inc(x_2603);
if (lean_is_exclusive(x_2542)) {
 lean_ctor_release(x_2542, 0);
 lean_ctor_release(x_2542, 1);
 x_2604 = x_2542;
} else {
 lean_dec_ref(x_2542);
 x_2604 = lean_box(0);
}
if (lean_is_scalar(x_2604)) {
 x_2605 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2605 = x_2604;
}
lean_ctor_set(x_2605, 0, x_2602);
lean_ctor_set(x_2605, 1, x_2603);
x_2100 = x_2605;
goto block_2105;
}
}
else
{
lean_object* x_2606; lean_object* x_2607; lean_object* x_2608; lean_object* x_2609; 
lean_dec(x_2535);
lean_dec(x_2533);
lean_dec(x_2447);
lean_dec(x_2187);
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2176);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2606 = lean_ctor_get(x_2536, 0);
lean_inc(x_2606);
x_2607 = lean_ctor_get(x_2536, 1);
lean_inc(x_2607);
if (lean_is_exclusive(x_2536)) {
 lean_ctor_release(x_2536, 0);
 lean_ctor_release(x_2536, 1);
 x_2608 = x_2536;
} else {
 lean_dec_ref(x_2536);
 x_2608 = lean_box(0);
}
if (lean_is_scalar(x_2608)) {
 x_2609 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2609 = x_2608;
}
lean_ctor_set(x_2609, 0, x_2606);
lean_ctor_set(x_2609, 1, x_2607);
x_2100 = x_2609;
goto block_2105;
}
}
else
{
lean_object* x_2610; lean_object* x_2611; lean_object* x_2612; 
lean_dec(x_2533);
lean_dec(x_2451);
x_2610 = lean_array_push(x_2157, x_2176);
lean_inc(x_2178);
x_2611 = lean_array_push(x_2610, x_2178);
lean_inc(x_2187);
x_2612 = l_Lean_Meta_mkLambda(x_2611, x_2447, x_2187, x_2532);
if (lean_obj_tag(x_2612) == 0)
{
lean_object* x_2613; lean_object* x_2614; uint8_t x_2615; lean_object* x_2616; lean_object* x_2617; lean_object* x_2618; lean_object* x_2619; 
x_2613 = lean_ctor_get(x_2612, 0);
lean_inc(x_2613);
x_2614 = lean_ctor_get(x_2612, 1);
lean_inc(x_2614);
lean_dec(x_2612);
x_2615 = 2;
lean_inc(x_2187);
x_2616 = l_Lean_Meta_mkFreshExprMVar(x_2535, x_2110, x_2615, x_2187, x_2614);
x_2617 = lean_ctor_get(x_2616, 0);
lean_inc(x_2617);
x_2618 = lean_ctor_get(x_2616, 1);
lean_inc(x_2618);
lean_dec(x_2616);
lean_inc(x_2187);
lean_inc(x_2617);
x_2619 = l_Lean_Meta_mkEqRec(x_2613, x_2617, x_2178, x_2187, x_2618);
if (lean_obj_tag(x_2619) == 0)
{
lean_object* x_2620; lean_object* x_2621; lean_object* x_2622; lean_object* x_2623; lean_object* x_2624; lean_object* x_2625; lean_object* x_2626; lean_object* x_2627; lean_object* x_2628; lean_object* x_2629; lean_object* x_2630; lean_object* x_2631; lean_object* x_2632; 
x_2620 = lean_ctor_get(x_2619, 1);
lean_inc(x_2620);
x_2621 = lean_ctor_get(x_2619, 0);
lean_inc(x_2621);
lean_dec(x_2619);
x_2622 = lean_ctor_get(x_2620, 0);
lean_inc(x_2622);
x_2623 = lean_ctor_get(x_2620, 1);
lean_inc(x_2623);
x_2624 = lean_ctor_get(x_2620, 2);
lean_inc(x_2624);
x_2625 = lean_ctor_get(x_2620, 3);
lean_inc(x_2625);
x_2626 = lean_ctor_get(x_2620, 4);
lean_inc(x_2626);
x_2627 = lean_ctor_get(x_2620, 5);
lean_inc(x_2627);
if (lean_is_exclusive(x_2620)) {
 lean_ctor_release(x_2620, 0);
 lean_ctor_release(x_2620, 1);
 lean_ctor_release(x_2620, 2);
 lean_ctor_release(x_2620, 3);
 lean_ctor_release(x_2620, 4);
 lean_ctor_release(x_2620, 5);
 x_2628 = x_2620;
} else {
 lean_dec_ref(x_2620);
 x_2628 = lean_box(0);
}
x_2629 = l_Lean_MetavarContext_assignExpr(x_2623, x_2173, x_2621);
if (lean_is_scalar(x_2628)) {
 x_2630 = lean_alloc_ctor(0, 6, 0);
} else {
 x_2630 = x_2628;
}
lean_ctor_set(x_2630, 0, x_2622);
lean_ctor_set(x_2630, 1, x_2629);
lean_ctor_set(x_2630, 2, x_2624);
lean_ctor_set(x_2630, 3, x_2625);
lean_ctor_set(x_2630, 4, x_2626);
lean_ctor_set(x_2630, 5, x_2627);
x_2631 = l_Lean_Expr_mvarId_x21(x_2617);
lean_dec(x_2617);
x_2632 = l_Lean_Meta_clear(x_2631, x_2177, x_2187, x_2630);
if (lean_obj_tag(x_2632) == 0)
{
lean_object* x_2633; lean_object* x_2634; lean_object* x_2635; 
x_2633 = lean_ctor_get(x_2632, 0);
lean_inc(x_2633);
x_2634 = lean_ctor_get(x_2632, 1);
lean_inc(x_2634);
lean_dec(x_2632);
x_2635 = l_Lean_Meta_clear(x_2633, x_2175, x_2187, x_2634);
if (lean_obj_tag(x_2635) == 0)
{
lean_object* x_2636; lean_object* x_2637; lean_object* x_2638; lean_object* x_2639; lean_object* x_2640; 
x_2636 = lean_ctor_get(x_2635, 0);
lean_inc(x_2636);
x_2637 = lean_ctor_get(x_2635, 1);
lean_inc(x_2637);
lean_dec(x_2635);
x_2638 = lean_array_get_size(x_2164);
lean_dec(x_2164);
x_2639 = lean_nat_sub(x_2638, x_2132);
lean_dec(x_2638);
x_2640 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2167, x_2636, x_2639, x_2166, x_2187, x_2637);
lean_dec(x_2187);
if (lean_obj_tag(x_2640) == 0)
{
lean_object* x_2641; lean_object* x_2642; lean_object* x_2643; lean_object* x_2644; lean_object* x_2645; lean_object* x_2646; lean_object* x_2647; lean_object* x_2648; 
x_2641 = lean_ctor_get(x_2640, 0);
lean_inc(x_2641);
x_2642 = lean_ctor_get(x_2640, 1);
lean_inc(x_2642);
if (lean_is_exclusive(x_2640)) {
 lean_ctor_release(x_2640, 0);
 lean_ctor_release(x_2640, 1);
 x_2643 = x_2640;
} else {
 lean_dec_ref(x_2640);
 x_2643 = lean_box(0);
}
x_2644 = lean_ctor_get(x_2641, 1);
lean_inc(x_2644);
if (lean_is_exclusive(x_2641)) {
 lean_ctor_release(x_2641, 0);
 lean_ctor_release(x_2641, 1);
 x_2645 = x_2641;
} else {
 lean_dec_ref(x_2641);
 x_2645 = lean_box(0);
}
x_2646 = lean_box(0);
if (lean_is_scalar(x_2645)) {
 x_2647 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2647 = x_2645;
}
lean_ctor_set(x_2647, 0, x_2646);
lean_ctor_set(x_2647, 1, x_2644);
if (lean_is_scalar(x_2643)) {
 x_2648 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2648 = x_2643;
}
lean_ctor_set(x_2648, 0, x_2647);
lean_ctor_set(x_2648, 1, x_2642);
x_2100 = x_2648;
goto block_2105;
}
else
{
lean_object* x_2649; lean_object* x_2650; lean_object* x_2651; lean_object* x_2652; 
x_2649 = lean_ctor_get(x_2640, 0);
lean_inc(x_2649);
x_2650 = lean_ctor_get(x_2640, 1);
lean_inc(x_2650);
if (lean_is_exclusive(x_2640)) {
 lean_ctor_release(x_2640, 0);
 lean_ctor_release(x_2640, 1);
 x_2651 = x_2640;
} else {
 lean_dec_ref(x_2640);
 x_2651 = lean_box(0);
}
if (lean_is_scalar(x_2651)) {
 x_2652 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2652 = x_2651;
}
lean_ctor_set(x_2652, 0, x_2649);
lean_ctor_set(x_2652, 1, x_2650);
x_2100 = x_2652;
goto block_2105;
}
}
else
{
lean_object* x_2653; lean_object* x_2654; lean_object* x_2655; lean_object* x_2656; 
lean_dec(x_2187);
lean_dec(x_2164);
x_2653 = lean_ctor_get(x_2635, 0);
lean_inc(x_2653);
x_2654 = lean_ctor_get(x_2635, 1);
lean_inc(x_2654);
if (lean_is_exclusive(x_2635)) {
 lean_ctor_release(x_2635, 0);
 lean_ctor_release(x_2635, 1);
 x_2655 = x_2635;
} else {
 lean_dec_ref(x_2635);
 x_2655 = lean_box(0);
}
if (lean_is_scalar(x_2655)) {
 x_2656 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2656 = x_2655;
}
lean_ctor_set(x_2656, 0, x_2653);
lean_ctor_set(x_2656, 1, x_2654);
x_2100 = x_2656;
goto block_2105;
}
}
else
{
lean_object* x_2657; lean_object* x_2658; lean_object* x_2659; lean_object* x_2660; 
lean_dec(x_2187);
lean_dec(x_2175);
lean_dec(x_2164);
x_2657 = lean_ctor_get(x_2632, 0);
lean_inc(x_2657);
x_2658 = lean_ctor_get(x_2632, 1);
lean_inc(x_2658);
if (lean_is_exclusive(x_2632)) {
 lean_ctor_release(x_2632, 0);
 lean_ctor_release(x_2632, 1);
 x_2659 = x_2632;
} else {
 lean_dec_ref(x_2632);
 x_2659 = lean_box(0);
}
if (lean_is_scalar(x_2659)) {
 x_2660 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2660 = x_2659;
}
lean_ctor_set(x_2660, 0, x_2657);
lean_ctor_set(x_2660, 1, x_2658);
x_2100 = x_2660;
goto block_2105;
}
}
else
{
lean_object* x_2661; lean_object* x_2662; lean_object* x_2663; lean_object* x_2664; 
lean_dec(x_2617);
lean_dec(x_2187);
lean_dec(x_2177);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
x_2661 = lean_ctor_get(x_2619, 0);
lean_inc(x_2661);
x_2662 = lean_ctor_get(x_2619, 1);
lean_inc(x_2662);
if (lean_is_exclusive(x_2619)) {
 lean_ctor_release(x_2619, 0);
 lean_ctor_release(x_2619, 1);
 x_2663 = x_2619;
} else {
 lean_dec_ref(x_2619);
 x_2663 = lean_box(0);
}
if (lean_is_scalar(x_2663)) {
 x_2664 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2664 = x_2663;
}
lean_ctor_set(x_2664, 0, x_2661);
lean_ctor_set(x_2664, 1, x_2662);
x_2100 = x_2664;
goto block_2105;
}
}
else
{
lean_object* x_2665; lean_object* x_2666; lean_object* x_2667; lean_object* x_2668; 
lean_dec(x_2535);
lean_dec(x_2187);
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2665 = lean_ctor_get(x_2612, 0);
lean_inc(x_2665);
x_2666 = lean_ctor_get(x_2612, 1);
lean_inc(x_2666);
if (lean_is_exclusive(x_2612)) {
 lean_ctor_release(x_2612, 0);
 lean_ctor_release(x_2612, 1);
 x_2667 = x_2612;
} else {
 lean_dec_ref(x_2612);
 x_2667 = lean_box(0);
}
if (lean_is_scalar(x_2667)) {
 x_2668 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2668 = x_2667;
}
lean_ctor_set(x_2668, 0, x_2665);
lean_ctor_set(x_2668, 1, x_2666);
x_2100 = x_2668;
goto block_2105;
}
}
}
else
{
lean_object* x_2669; lean_object* x_2670; lean_object* x_2671; lean_object* x_2672; 
lean_dec(x_2529);
lean_dec(x_2451);
lean_dec(x_2447);
lean_dec(x_2187);
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2176);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2669 = lean_ctor_get(x_2530, 0);
lean_inc(x_2669);
x_2670 = lean_ctor_get(x_2530, 1);
lean_inc(x_2670);
if (lean_is_exclusive(x_2530)) {
 lean_ctor_release(x_2530, 0);
 lean_ctor_release(x_2530, 1);
 x_2671 = x_2530;
} else {
 lean_dec_ref(x_2530);
 x_2671 = lean_box(0);
}
if (lean_is_scalar(x_2671)) {
 x_2672 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2672 = x_2671;
}
lean_ctor_set(x_2672, 0, x_2669);
lean_ctor_set(x_2672, 1, x_2670);
x_2100 = x_2672;
goto block_2105;
}
}
}
}
else
{
lean_object* x_2686; lean_object* x_2687; lean_object* x_2688; lean_object* x_2689; 
lean_dec(x_2447);
lean_dec(x_2187);
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2176);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2686 = lean_ctor_get(x_2448, 0);
lean_inc(x_2686);
x_2687 = lean_ctor_get(x_2448, 1);
lean_inc(x_2687);
if (lean_is_exclusive(x_2448)) {
 lean_ctor_release(x_2448, 0);
 lean_ctor_release(x_2448, 1);
 x_2688 = x_2448;
} else {
 lean_dec_ref(x_2448);
 x_2688 = lean_box(0);
}
if (lean_is_scalar(x_2688)) {
 x_2689 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2689 = x_2688;
}
lean_ctor_set(x_2689, 0, x_2686);
lean_ctor_set(x_2689, 1, x_2687);
x_2100 = x_2689;
goto block_2105;
}
}
else
{
lean_object* x_2690; lean_object* x_2691; lean_object* x_2692; lean_object* x_2693; 
lean_dec(x_2187);
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2176);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2690 = lean_ctor_get(x_2444, 0);
lean_inc(x_2690);
x_2691 = lean_ctor_get(x_2444, 1);
lean_inc(x_2691);
if (lean_is_exclusive(x_2444)) {
 lean_ctor_release(x_2444, 0);
 lean_ctor_release(x_2444, 1);
 x_2692 = x_2444;
} else {
 lean_dec_ref(x_2444);
 x_2692 = lean_box(0);
}
if (lean_is_scalar(x_2692)) {
 x_2693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2693 = x_2692;
}
lean_ctor_set(x_2693, 0, x_2690);
lean_ctor_set(x_2693, 1, x_2691);
x_2100 = x_2693;
goto block_2105;
}
}
}
block_2440:
{
lean_object* x_2189; lean_object* x_2190; lean_object* x_2191; lean_object* x_2192; lean_object* x_2193; lean_object* x_2194; lean_object* x_2195; lean_object* x_2196; lean_object* x_2197; lean_object* x_2198; lean_object* x_2199; lean_object* x_2200; lean_object* x_2201; lean_object* x_2216; lean_object* x_2217; lean_object* x_2232; lean_object* x_2233; lean_object* x_2234; 
lean_dec(x_2188);
x_2189 = lean_ctor_get(x_2181, 2);
lean_inc(x_2189);
x_2190 = lean_ctor_get(x_2181, 0);
lean_inc(x_2190);
x_2191 = lean_ctor_get(x_2181, 1);
lean_inc(x_2191);
x_2192 = lean_ctor_get(x_2181, 3);
lean_inc(x_2192);
x_2193 = lean_ctor_get(x_2181, 4);
lean_inc(x_2193);
x_2194 = lean_ctor_get(x_2181, 5);
lean_inc(x_2194);
if (lean_is_exclusive(x_2181)) {
 lean_ctor_release(x_2181, 0);
 lean_ctor_release(x_2181, 1);
 lean_ctor_release(x_2181, 2);
 lean_ctor_release(x_2181, 3);
 lean_ctor_release(x_2181, 4);
 lean_ctor_release(x_2181, 5);
 x_2195 = x_2181;
} else {
 lean_dec_ref(x_2181);
 x_2195 = lean_box(0);
}
x_2196 = lean_ctor_get(x_2189, 0);
lean_inc(x_2196);
x_2197 = lean_ctor_get(x_2189, 1);
lean_inc(x_2197);
x_2198 = lean_ctor_get(x_2189, 2);
lean_inc(x_2198);
if (lean_is_exclusive(x_2189)) {
 lean_ctor_release(x_2189, 0);
 lean_ctor_release(x_2189, 1);
 lean_ctor_release(x_2189, 2);
 x_2199 = x_2189;
} else {
 lean_dec_ref(x_2189);
 x_2199 = lean_box(0);
}
if (lean_is_scalar(x_2199)) {
 x_2232 = lean_alloc_ctor(0, 3, 0);
} else {
 x_2232 = x_2199;
}
lean_ctor_set(x_2232, 0, x_2196);
lean_ctor_set(x_2232, 1, x_2197);
lean_ctor_set(x_2232, 2, x_2106);
if (lean_is_scalar(x_2195)) {
 x_2233 = lean_alloc_ctor(0, 6, 0);
} else {
 x_2233 = x_2195;
}
lean_ctor_set(x_2233, 0, x_2190);
lean_ctor_set(x_2233, 1, x_2191);
lean_ctor_set(x_2233, 2, x_2232);
lean_ctor_set(x_2233, 3, x_2192);
lean_ctor_set(x_2233, 4, x_2193);
lean_ctor_set(x_2233, 5, x_2194);
lean_inc(x_2173);
x_2234 = l_Lean_Meta_getMVarDecl(x_2173, x_2187, x_2233);
if (lean_obj_tag(x_2234) == 0)
{
lean_object* x_2235; lean_object* x_2236; lean_object* x_2237; lean_object* x_2238; 
x_2235 = lean_ctor_get(x_2234, 0);
lean_inc(x_2235);
x_2236 = lean_ctor_get(x_2234, 1);
lean_inc(x_2236);
lean_dec(x_2234);
x_2237 = lean_ctor_get(x_2235, 2);
lean_inc(x_2237);
lean_dec(x_2235);
lean_inc(x_2187);
lean_inc(x_2177);
x_2238 = l_Lean_Meta_getLocalDecl(x_2177, x_2187, x_2236);
if (lean_obj_tag(x_2238) == 0)
{
lean_object* x_2239; lean_object* x_2240; lean_object* x_2241; lean_object* x_2420; uint8_t x_2421; 
x_2239 = lean_ctor_get(x_2238, 0);
lean_inc(x_2239);
x_2240 = lean_ctor_get(x_2238, 1);
lean_inc(x_2240);
lean_dec(x_2238);
x_2420 = l_Lean_LocalDecl_type(x_2239);
lean_dec(x_2239);
x_2421 = l_Lean_Expr_isAppOfArity___main(x_2420, x_2119, x_2120);
if (x_2421 == 0)
{
lean_object* x_2422; lean_object* x_2423; lean_object* x_2424; 
lean_dec(x_2420);
lean_dec(x_2237);
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2176);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2422 = l_Lean_Meta_isClassQuick___main___closed__1;
x_2423 = l_unreachable_x21___rarg(x_2422);
x_2424 = lean_apply_2(x_2423, x_2187, x_2240);
if (lean_obj_tag(x_2424) == 0)
{
lean_object* x_2425; lean_object* x_2426; 
lean_dec(x_2171);
x_2425 = lean_ctor_get(x_2424, 0);
lean_inc(x_2425);
x_2426 = lean_ctor_get(x_2424, 1);
lean_inc(x_2426);
lean_dec(x_2424);
x_2200 = x_2425;
x_2201 = x_2426;
goto block_2215;
}
else
{
lean_object* x_2427; lean_object* x_2428; 
lean_dec(x_2182);
x_2427 = lean_ctor_get(x_2424, 0);
lean_inc(x_2427);
x_2428 = lean_ctor_get(x_2424, 1);
lean_inc(x_2428);
lean_dec(x_2424);
x_2216 = x_2427;
x_2217 = x_2428;
goto block_2231;
}
}
else
{
lean_object* x_2429; 
x_2429 = l_Lean_Expr_getAppNumArgsAux___main(x_2420, x_2126);
if (x_2136 == 0)
{
lean_object* x_2430; lean_object* x_2431; lean_object* x_2432; 
x_2430 = lean_nat_sub(x_2429, x_2132);
lean_dec(x_2429);
x_2431 = lean_nat_sub(x_2430, x_2128);
lean_dec(x_2430);
x_2432 = l_Lean_Expr_getRevArg_x21___main(x_2420, x_2431);
lean_dec(x_2420);
x_2241 = x_2432;
goto block_2419;
}
else
{
lean_object* x_2433; lean_object* x_2434; lean_object* x_2435; 
x_2433 = lean_nat_sub(x_2429, x_2128);
lean_dec(x_2429);
x_2434 = lean_nat_sub(x_2433, x_2128);
lean_dec(x_2433);
x_2435 = l_Lean_Expr_getRevArg_x21___main(x_2420, x_2434);
lean_dec(x_2420);
x_2241 = x_2435;
goto block_2419;
}
}
block_2419:
{
lean_object* x_2242; lean_object* x_2243; uint8_t x_2244; 
x_2242 = lean_ctor_get(x_2240, 1);
lean_inc(x_2242);
lean_inc(x_2237);
x_2243 = l_Lean_MetavarContext_exprDependsOn(x_2242, x_2237, x_2177);
x_2244 = lean_unbox(x_2243);
lean_dec(x_2243);
if (x_2244 == 0)
{
lean_object* x_2245; lean_object* x_2246; lean_object* x_2247; 
x_2245 = l_Lean_mkOptionalNode___closed__2;
x_2246 = lean_array_push(x_2245, x_2176);
lean_inc(x_2187);
lean_inc(x_2237);
lean_inc(x_2246);
x_2247 = l_Lean_Meta_mkLambda(x_2246, x_2237, x_2187, x_2240);
if (lean_obj_tag(x_2247) == 0)
{
lean_object* x_2248; lean_object* x_2249; lean_object* x_2250; lean_object* x_2251; lean_object* x_2252; lean_object* x_2253; 
x_2248 = lean_ctor_get(x_2247, 0);
lean_inc(x_2248);
x_2249 = lean_ctor_get(x_2247, 1);
lean_inc(x_2249);
lean_dec(x_2247);
x_2250 = lean_expr_abstract(x_2237, x_2246);
lean_dec(x_2246);
lean_dec(x_2237);
x_2251 = lean_expr_instantiate1(x_2250, x_2241);
lean_dec(x_2241);
lean_dec(x_2250);
if (x_2136 == 0)
{
lean_object* x_2295; 
lean_inc(x_2187);
x_2295 = l_Lean_Meta_mkEqSymm(x_2178, x_2187, x_2249);
if (lean_obj_tag(x_2295) == 0)
{
lean_object* x_2296; lean_object* x_2297; 
x_2296 = lean_ctor_get(x_2295, 0);
lean_inc(x_2296);
x_2297 = lean_ctor_get(x_2295, 1);
lean_inc(x_2297);
lean_dec(x_2295);
x_2252 = x_2296;
x_2253 = x_2297;
goto block_2294;
}
else
{
lean_object* x_2298; lean_object* x_2299; 
lean_dec(x_2251);
lean_dec(x_2248);
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2177);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2298 = lean_ctor_get(x_2295, 0);
lean_inc(x_2298);
x_2299 = lean_ctor_get(x_2295, 1);
lean_inc(x_2299);
lean_dec(x_2295);
x_2216 = x_2298;
x_2217 = x_2299;
goto block_2231;
}
}
else
{
x_2252 = x_2178;
x_2253 = x_2249;
goto block_2294;
}
block_2294:
{
uint8_t x_2254; lean_object* x_2255; lean_object* x_2256; lean_object* x_2257; lean_object* x_2258; 
x_2254 = 2;
lean_inc(x_2187);
x_2255 = l_Lean_Meta_mkFreshExprMVar(x_2251, x_2110, x_2254, x_2187, x_2253);
x_2256 = lean_ctor_get(x_2255, 0);
lean_inc(x_2256);
x_2257 = lean_ctor_get(x_2255, 1);
lean_inc(x_2257);
lean_dec(x_2255);
lean_inc(x_2187);
lean_inc(x_2256);
x_2258 = l_Lean_Meta_mkEqNDRec(x_2248, x_2256, x_2252, x_2187, x_2257);
if (lean_obj_tag(x_2258) == 0)
{
lean_object* x_2259; lean_object* x_2260; lean_object* x_2261; lean_object* x_2262; lean_object* x_2263; lean_object* x_2264; lean_object* x_2265; lean_object* x_2266; lean_object* x_2267; lean_object* x_2268; lean_object* x_2269; lean_object* x_2270; lean_object* x_2271; 
x_2259 = lean_ctor_get(x_2258, 1);
lean_inc(x_2259);
x_2260 = lean_ctor_get(x_2258, 0);
lean_inc(x_2260);
lean_dec(x_2258);
x_2261 = lean_ctor_get(x_2259, 0);
lean_inc(x_2261);
x_2262 = lean_ctor_get(x_2259, 1);
lean_inc(x_2262);
x_2263 = lean_ctor_get(x_2259, 2);
lean_inc(x_2263);
x_2264 = lean_ctor_get(x_2259, 3);
lean_inc(x_2264);
x_2265 = lean_ctor_get(x_2259, 4);
lean_inc(x_2265);
x_2266 = lean_ctor_get(x_2259, 5);
lean_inc(x_2266);
if (lean_is_exclusive(x_2259)) {
 lean_ctor_release(x_2259, 0);
 lean_ctor_release(x_2259, 1);
 lean_ctor_release(x_2259, 2);
 lean_ctor_release(x_2259, 3);
 lean_ctor_release(x_2259, 4);
 lean_ctor_release(x_2259, 5);
 x_2267 = x_2259;
} else {
 lean_dec_ref(x_2259);
 x_2267 = lean_box(0);
}
x_2268 = l_Lean_MetavarContext_assignExpr(x_2262, x_2173, x_2260);
if (lean_is_scalar(x_2267)) {
 x_2269 = lean_alloc_ctor(0, 6, 0);
} else {
 x_2269 = x_2267;
}
lean_ctor_set(x_2269, 0, x_2261);
lean_ctor_set(x_2269, 1, x_2268);
lean_ctor_set(x_2269, 2, x_2263);
lean_ctor_set(x_2269, 3, x_2264);
lean_ctor_set(x_2269, 4, x_2265);
lean_ctor_set(x_2269, 5, x_2266);
x_2270 = l_Lean_Expr_mvarId_x21(x_2256);
lean_dec(x_2256);
x_2271 = l_Lean_Meta_clear(x_2270, x_2177, x_2187, x_2269);
if (lean_obj_tag(x_2271) == 0)
{
lean_object* x_2272; lean_object* x_2273; lean_object* x_2274; 
x_2272 = lean_ctor_get(x_2271, 0);
lean_inc(x_2272);
x_2273 = lean_ctor_get(x_2271, 1);
lean_inc(x_2273);
lean_dec(x_2271);
x_2274 = l_Lean_Meta_clear(x_2272, x_2175, x_2187, x_2273);
if (lean_obj_tag(x_2274) == 0)
{
lean_object* x_2275; lean_object* x_2276; lean_object* x_2277; lean_object* x_2278; lean_object* x_2279; 
x_2275 = lean_ctor_get(x_2274, 0);
lean_inc(x_2275);
x_2276 = lean_ctor_get(x_2274, 1);
lean_inc(x_2276);
lean_dec(x_2274);
x_2277 = lean_array_get_size(x_2164);
lean_dec(x_2164);
x_2278 = lean_nat_sub(x_2277, x_2132);
lean_dec(x_2277);
x_2279 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2167, x_2275, x_2278, x_2166, x_2187, x_2276);
lean_dec(x_2187);
if (lean_obj_tag(x_2279) == 0)
{
lean_object* x_2280; lean_object* x_2281; lean_object* x_2282; lean_object* x_2283; lean_object* x_2284; lean_object* x_2285; 
lean_dec(x_2171);
x_2280 = lean_ctor_get(x_2279, 0);
lean_inc(x_2280);
x_2281 = lean_ctor_get(x_2279, 1);
lean_inc(x_2281);
lean_dec(x_2279);
x_2282 = lean_ctor_get(x_2280, 1);
lean_inc(x_2282);
if (lean_is_exclusive(x_2280)) {
 lean_ctor_release(x_2280, 0);
 lean_ctor_release(x_2280, 1);
 x_2283 = x_2280;
} else {
 lean_dec_ref(x_2280);
 x_2283 = lean_box(0);
}
x_2284 = lean_box(0);
if (lean_is_scalar(x_2283)) {
 x_2285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2285 = x_2283;
}
lean_ctor_set(x_2285, 0, x_2284);
lean_ctor_set(x_2285, 1, x_2282);
x_2200 = x_2285;
x_2201 = x_2281;
goto block_2215;
}
else
{
lean_object* x_2286; lean_object* x_2287; 
lean_dec(x_2182);
x_2286 = lean_ctor_get(x_2279, 0);
lean_inc(x_2286);
x_2287 = lean_ctor_get(x_2279, 1);
lean_inc(x_2287);
lean_dec(x_2279);
x_2216 = x_2286;
x_2217 = x_2287;
goto block_2231;
}
}
else
{
lean_object* x_2288; lean_object* x_2289; 
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2164);
x_2288 = lean_ctor_get(x_2274, 0);
lean_inc(x_2288);
x_2289 = lean_ctor_get(x_2274, 1);
lean_inc(x_2289);
lean_dec(x_2274);
x_2216 = x_2288;
x_2217 = x_2289;
goto block_2231;
}
}
else
{
lean_object* x_2290; lean_object* x_2291; 
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2175);
lean_dec(x_2164);
x_2290 = lean_ctor_get(x_2271, 0);
lean_inc(x_2290);
x_2291 = lean_ctor_get(x_2271, 1);
lean_inc(x_2291);
lean_dec(x_2271);
x_2216 = x_2290;
x_2217 = x_2291;
goto block_2231;
}
}
else
{
lean_object* x_2292; lean_object* x_2293; 
lean_dec(x_2256);
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2177);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
x_2292 = lean_ctor_get(x_2258, 0);
lean_inc(x_2292);
x_2293 = lean_ctor_get(x_2258, 1);
lean_inc(x_2293);
lean_dec(x_2258);
x_2216 = x_2292;
x_2217 = x_2293;
goto block_2231;
}
}
}
else
{
lean_object* x_2300; lean_object* x_2301; 
lean_dec(x_2246);
lean_dec(x_2241);
lean_dec(x_2237);
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2300 = lean_ctor_get(x_2247, 0);
lean_inc(x_2300);
x_2301 = lean_ctor_get(x_2247, 1);
lean_inc(x_2301);
lean_dec(x_2247);
x_2216 = x_2300;
x_2217 = x_2301;
goto block_2231;
}
}
else
{
lean_object* x_2302; lean_object* x_2303; lean_object* x_2304; lean_object* x_2305; lean_object* x_2306; 
x_2302 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2176);
x_2303 = lean_array_push(x_2302, x_2176);
x_2304 = lean_expr_abstract(x_2237, x_2303);
lean_dec(x_2303);
x_2305 = lean_expr_instantiate1(x_2304, x_2241);
lean_dec(x_2304);
lean_inc(x_2187);
lean_inc(x_2241);
x_2306 = l_Lean_Meta_mkEqRefl(x_2241, x_2187, x_2240);
if (lean_obj_tag(x_2306) == 0)
{
lean_object* x_2307; lean_object* x_2308; lean_object* x_2309; lean_object* x_2310; lean_object* x_2311; 
x_2307 = lean_ctor_get(x_2306, 0);
lean_inc(x_2307);
x_2308 = lean_ctor_get(x_2306, 1);
lean_inc(x_2308);
lean_dec(x_2306);
lean_inc(x_2178);
x_2309 = lean_array_push(x_2302, x_2178);
x_2310 = lean_expr_abstract(x_2305, x_2309);
lean_dec(x_2305);
x_2311 = lean_expr_instantiate1(x_2310, x_2307);
lean_dec(x_2307);
lean_dec(x_2310);
if (x_2136 == 0)
{
lean_object* x_2312; 
lean_inc(x_2187);
lean_inc(x_2176);
x_2312 = l_Lean_Meta_mkEq(x_2241, x_2176, x_2187, x_2308);
if (lean_obj_tag(x_2312) == 0)
{
lean_object* x_2313; lean_object* x_2314; lean_object* x_2315; lean_object* x_2316; uint8_t x_2317; lean_object* x_2318; 
x_2313 = lean_ctor_get(x_2312, 0);
lean_inc(x_2313);
x_2314 = lean_ctor_get(x_2312, 1);
lean_inc(x_2314);
lean_dec(x_2312);
x_2315 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__1___boxed), 7, 4);
lean_closure_set(x_2315, 0, x_2237);
lean_closure_set(x_2315, 1, x_2309);
lean_closure_set(x_2315, 2, x_2157);
lean_closure_set(x_2315, 3, x_2176);
x_2316 = l_Lean_Meta_substCore___closed__18;
x_2317 = 0;
lean_inc(x_2187);
x_2318 = l_Lean_Meta_withLocalDecl___rarg(x_2316, x_2313, x_2317, x_2315, x_2187, x_2314);
if (lean_obj_tag(x_2318) == 0)
{
lean_object* x_2319; lean_object* x_2320; lean_object* x_2321; 
x_2319 = lean_ctor_get(x_2318, 0);
lean_inc(x_2319);
x_2320 = lean_ctor_get(x_2318, 1);
lean_inc(x_2320);
lean_dec(x_2318);
lean_inc(x_2187);
x_2321 = l_Lean_Meta_mkEqSymm(x_2178, x_2187, x_2320);
if (lean_obj_tag(x_2321) == 0)
{
lean_object* x_2322; lean_object* x_2323; uint8_t x_2324; lean_object* x_2325; lean_object* x_2326; lean_object* x_2327; lean_object* x_2328; 
x_2322 = lean_ctor_get(x_2321, 0);
lean_inc(x_2322);
x_2323 = lean_ctor_get(x_2321, 1);
lean_inc(x_2323);
lean_dec(x_2321);
x_2324 = 2;
lean_inc(x_2187);
x_2325 = l_Lean_Meta_mkFreshExprMVar(x_2311, x_2110, x_2324, x_2187, x_2323);
x_2326 = lean_ctor_get(x_2325, 0);
lean_inc(x_2326);
x_2327 = lean_ctor_get(x_2325, 1);
lean_inc(x_2327);
lean_dec(x_2325);
lean_inc(x_2187);
lean_inc(x_2326);
x_2328 = l_Lean_Meta_mkEqRec(x_2319, x_2326, x_2322, x_2187, x_2327);
if (lean_obj_tag(x_2328) == 0)
{
lean_object* x_2329; lean_object* x_2330; lean_object* x_2331; lean_object* x_2332; lean_object* x_2333; lean_object* x_2334; lean_object* x_2335; lean_object* x_2336; lean_object* x_2337; lean_object* x_2338; lean_object* x_2339; lean_object* x_2340; lean_object* x_2341; 
x_2329 = lean_ctor_get(x_2328, 1);
lean_inc(x_2329);
x_2330 = lean_ctor_get(x_2328, 0);
lean_inc(x_2330);
lean_dec(x_2328);
x_2331 = lean_ctor_get(x_2329, 0);
lean_inc(x_2331);
x_2332 = lean_ctor_get(x_2329, 1);
lean_inc(x_2332);
x_2333 = lean_ctor_get(x_2329, 2);
lean_inc(x_2333);
x_2334 = lean_ctor_get(x_2329, 3);
lean_inc(x_2334);
x_2335 = lean_ctor_get(x_2329, 4);
lean_inc(x_2335);
x_2336 = lean_ctor_get(x_2329, 5);
lean_inc(x_2336);
if (lean_is_exclusive(x_2329)) {
 lean_ctor_release(x_2329, 0);
 lean_ctor_release(x_2329, 1);
 lean_ctor_release(x_2329, 2);
 lean_ctor_release(x_2329, 3);
 lean_ctor_release(x_2329, 4);
 lean_ctor_release(x_2329, 5);
 x_2337 = x_2329;
} else {
 lean_dec_ref(x_2329);
 x_2337 = lean_box(0);
}
x_2338 = l_Lean_MetavarContext_assignExpr(x_2332, x_2173, x_2330);
if (lean_is_scalar(x_2337)) {
 x_2339 = lean_alloc_ctor(0, 6, 0);
} else {
 x_2339 = x_2337;
}
lean_ctor_set(x_2339, 0, x_2331);
lean_ctor_set(x_2339, 1, x_2338);
lean_ctor_set(x_2339, 2, x_2333);
lean_ctor_set(x_2339, 3, x_2334);
lean_ctor_set(x_2339, 4, x_2335);
lean_ctor_set(x_2339, 5, x_2336);
x_2340 = l_Lean_Expr_mvarId_x21(x_2326);
lean_dec(x_2326);
x_2341 = l_Lean_Meta_clear(x_2340, x_2177, x_2187, x_2339);
if (lean_obj_tag(x_2341) == 0)
{
lean_object* x_2342; lean_object* x_2343; lean_object* x_2344; 
x_2342 = lean_ctor_get(x_2341, 0);
lean_inc(x_2342);
x_2343 = lean_ctor_get(x_2341, 1);
lean_inc(x_2343);
lean_dec(x_2341);
x_2344 = l_Lean_Meta_clear(x_2342, x_2175, x_2187, x_2343);
if (lean_obj_tag(x_2344) == 0)
{
lean_object* x_2345; lean_object* x_2346; lean_object* x_2347; lean_object* x_2348; lean_object* x_2349; 
x_2345 = lean_ctor_get(x_2344, 0);
lean_inc(x_2345);
x_2346 = lean_ctor_get(x_2344, 1);
lean_inc(x_2346);
lean_dec(x_2344);
x_2347 = lean_array_get_size(x_2164);
lean_dec(x_2164);
x_2348 = lean_nat_sub(x_2347, x_2132);
lean_dec(x_2347);
x_2349 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2167, x_2345, x_2348, x_2166, x_2187, x_2346);
lean_dec(x_2187);
if (lean_obj_tag(x_2349) == 0)
{
lean_object* x_2350; lean_object* x_2351; lean_object* x_2352; lean_object* x_2353; lean_object* x_2354; lean_object* x_2355; 
lean_dec(x_2171);
x_2350 = lean_ctor_get(x_2349, 0);
lean_inc(x_2350);
x_2351 = lean_ctor_get(x_2349, 1);
lean_inc(x_2351);
lean_dec(x_2349);
x_2352 = lean_ctor_get(x_2350, 1);
lean_inc(x_2352);
if (lean_is_exclusive(x_2350)) {
 lean_ctor_release(x_2350, 0);
 lean_ctor_release(x_2350, 1);
 x_2353 = x_2350;
} else {
 lean_dec_ref(x_2350);
 x_2353 = lean_box(0);
}
x_2354 = lean_box(0);
if (lean_is_scalar(x_2353)) {
 x_2355 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2355 = x_2353;
}
lean_ctor_set(x_2355, 0, x_2354);
lean_ctor_set(x_2355, 1, x_2352);
x_2200 = x_2355;
x_2201 = x_2351;
goto block_2215;
}
else
{
lean_object* x_2356; lean_object* x_2357; 
lean_dec(x_2182);
x_2356 = lean_ctor_get(x_2349, 0);
lean_inc(x_2356);
x_2357 = lean_ctor_get(x_2349, 1);
lean_inc(x_2357);
lean_dec(x_2349);
x_2216 = x_2356;
x_2217 = x_2357;
goto block_2231;
}
}
else
{
lean_object* x_2358; lean_object* x_2359; 
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2164);
x_2358 = lean_ctor_get(x_2344, 0);
lean_inc(x_2358);
x_2359 = lean_ctor_get(x_2344, 1);
lean_inc(x_2359);
lean_dec(x_2344);
x_2216 = x_2358;
x_2217 = x_2359;
goto block_2231;
}
}
else
{
lean_object* x_2360; lean_object* x_2361; 
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2175);
lean_dec(x_2164);
x_2360 = lean_ctor_get(x_2341, 0);
lean_inc(x_2360);
x_2361 = lean_ctor_get(x_2341, 1);
lean_inc(x_2361);
lean_dec(x_2341);
x_2216 = x_2360;
x_2217 = x_2361;
goto block_2231;
}
}
else
{
lean_object* x_2362; lean_object* x_2363; 
lean_dec(x_2326);
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2177);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
x_2362 = lean_ctor_get(x_2328, 0);
lean_inc(x_2362);
x_2363 = lean_ctor_get(x_2328, 1);
lean_inc(x_2363);
lean_dec(x_2328);
x_2216 = x_2362;
x_2217 = x_2363;
goto block_2231;
}
}
else
{
lean_object* x_2364; lean_object* x_2365; 
lean_dec(x_2319);
lean_dec(x_2311);
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2177);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2364 = lean_ctor_get(x_2321, 0);
lean_inc(x_2364);
x_2365 = lean_ctor_get(x_2321, 1);
lean_inc(x_2365);
lean_dec(x_2321);
x_2216 = x_2364;
x_2217 = x_2365;
goto block_2231;
}
}
else
{
lean_object* x_2366; lean_object* x_2367; 
lean_dec(x_2311);
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2366 = lean_ctor_get(x_2318, 0);
lean_inc(x_2366);
x_2367 = lean_ctor_get(x_2318, 1);
lean_inc(x_2367);
lean_dec(x_2318);
x_2216 = x_2366;
x_2217 = x_2367;
goto block_2231;
}
}
else
{
lean_object* x_2368; lean_object* x_2369; 
lean_dec(x_2311);
lean_dec(x_2309);
lean_dec(x_2237);
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2176);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2368 = lean_ctor_get(x_2312, 0);
lean_inc(x_2368);
x_2369 = lean_ctor_get(x_2312, 1);
lean_inc(x_2369);
lean_dec(x_2312);
x_2216 = x_2368;
x_2217 = x_2369;
goto block_2231;
}
}
else
{
lean_object* x_2370; lean_object* x_2371; lean_object* x_2372; 
lean_dec(x_2309);
lean_dec(x_2241);
x_2370 = lean_array_push(x_2157, x_2176);
lean_inc(x_2178);
x_2371 = lean_array_push(x_2370, x_2178);
lean_inc(x_2187);
x_2372 = l_Lean_Meta_mkLambda(x_2371, x_2237, x_2187, x_2308);
if (lean_obj_tag(x_2372) == 0)
{
lean_object* x_2373; lean_object* x_2374; uint8_t x_2375; lean_object* x_2376; lean_object* x_2377; lean_object* x_2378; lean_object* x_2379; 
x_2373 = lean_ctor_get(x_2372, 0);
lean_inc(x_2373);
x_2374 = lean_ctor_get(x_2372, 1);
lean_inc(x_2374);
lean_dec(x_2372);
x_2375 = 2;
lean_inc(x_2187);
x_2376 = l_Lean_Meta_mkFreshExprMVar(x_2311, x_2110, x_2375, x_2187, x_2374);
x_2377 = lean_ctor_get(x_2376, 0);
lean_inc(x_2377);
x_2378 = lean_ctor_get(x_2376, 1);
lean_inc(x_2378);
lean_dec(x_2376);
lean_inc(x_2187);
lean_inc(x_2377);
x_2379 = l_Lean_Meta_mkEqRec(x_2373, x_2377, x_2178, x_2187, x_2378);
if (lean_obj_tag(x_2379) == 0)
{
lean_object* x_2380; lean_object* x_2381; lean_object* x_2382; lean_object* x_2383; lean_object* x_2384; lean_object* x_2385; lean_object* x_2386; lean_object* x_2387; lean_object* x_2388; lean_object* x_2389; lean_object* x_2390; lean_object* x_2391; lean_object* x_2392; 
x_2380 = lean_ctor_get(x_2379, 1);
lean_inc(x_2380);
x_2381 = lean_ctor_get(x_2379, 0);
lean_inc(x_2381);
lean_dec(x_2379);
x_2382 = lean_ctor_get(x_2380, 0);
lean_inc(x_2382);
x_2383 = lean_ctor_get(x_2380, 1);
lean_inc(x_2383);
x_2384 = lean_ctor_get(x_2380, 2);
lean_inc(x_2384);
x_2385 = lean_ctor_get(x_2380, 3);
lean_inc(x_2385);
x_2386 = lean_ctor_get(x_2380, 4);
lean_inc(x_2386);
x_2387 = lean_ctor_get(x_2380, 5);
lean_inc(x_2387);
if (lean_is_exclusive(x_2380)) {
 lean_ctor_release(x_2380, 0);
 lean_ctor_release(x_2380, 1);
 lean_ctor_release(x_2380, 2);
 lean_ctor_release(x_2380, 3);
 lean_ctor_release(x_2380, 4);
 lean_ctor_release(x_2380, 5);
 x_2388 = x_2380;
} else {
 lean_dec_ref(x_2380);
 x_2388 = lean_box(0);
}
x_2389 = l_Lean_MetavarContext_assignExpr(x_2383, x_2173, x_2381);
if (lean_is_scalar(x_2388)) {
 x_2390 = lean_alloc_ctor(0, 6, 0);
} else {
 x_2390 = x_2388;
}
lean_ctor_set(x_2390, 0, x_2382);
lean_ctor_set(x_2390, 1, x_2389);
lean_ctor_set(x_2390, 2, x_2384);
lean_ctor_set(x_2390, 3, x_2385);
lean_ctor_set(x_2390, 4, x_2386);
lean_ctor_set(x_2390, 5, x_2387);
x_2391 = l_Lean_Expr_mvarId_x21(x_2377);
lean_dec(x_2377);
x_2392 = l_Lean_Meta_clear(x_2391, x_2177, x_2187, x_2390);
if (lean_obj_tag(x_2392) == 0)
{
lean_object* x_2393; lean_object* x_2394; lean_object* x_2395; 
x_2393 = lean_ctor_get(x_2392, 0);
lean_inc(x_2393);
x_2394 = lean_ctor_get(x_2392, 1);
lean_inc(x_2394);
lean_dec(x_2392);
x_2395 = l_Lean_Meta_clear(x_2393, x_2175, x_2187, x_2394);
if (lean_obj_tag(x_2395) == 0)
{
lean_object* x_2396; lean_object* x_2397; lean_object* x_2398; lean_object* x_2399; lean_object* x_2400; 
x_2396 = lean_ctor_get(x_2395, 0);
lean_inc(x_2396);
x_2397 = lean_ctor_get(x_2395, 1);
lean_inc(x_2397);
lean_dec(x_2395);
x_2398 = lean_array_get_size(x_2164);
lean_dec(x_2164);
x_2399 = lean_nat_sub(x_2398, x_2132);
lean_dec(x_2398);
x_2400 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_2167, x_2396, x_2399, x_2166, x_2187, x_2397);
lean_dec(x_2187);
if (lean_obj_tag(x_2400) == 0)
{
lean_object* x_2401; lean_object* x_2402; lean_object* x_2403; lean_object* x_2404; lean_object* x_2405; lean_object* x_2406; 
lean_dec(x_2171);
x_2401 = lean_ctor_get(x_2400, 0);
lean_inc(x_2401);
x_2402 = lean_ctor_get(x_2400, 1);
lean_inc(x_2402);
lean_dec(x_2400);
x_2403 = lean_ctor_get(x_2401, 1);
lean_inc(x_2403);
if (lean_is_exclusive(x_2401)) {
 lean_ctor_release(x_2401, 0);
 lean_ctor_release(x_2401, 1);
 x_2404 = x_2401;
} else {
 lean_dec_ref(x_2401);
 x_2404 = lean_box(0);
}
x_2405 = lean_box(0);
if (lean_is_scalar(x_2404)) {
 x_2406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2406 = x_2404;
}
lean_ctor_set(x_2406, 0, x_2405);
lean_ctor_set(x_2406, 1, x_2403);
x_2200 = x_2406;
x_2201 = x_2402;
goto block_2215;
}
else
{
lean_object* x_2407; lean_object* x_2408; 
lean_dec(x_2182);
x_2407 = lean_ctor_get(x_2400, 0);
lean_inc(x_2407);
x_2408 = lean_ctor_get(x_2400, 1);
lean_inc(x_2408);
lean_dec(x_2400);
x_2216 = x_2407;
x_2217 = x_2408;
goto block_2231;
}
}
else
{
lean_object* x_2409; lean_object* x_2410; 
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2164);
x_2409 = lean_ctor_get(x_2395, 0);
lean_inc(x_2409);
x_2410 = lean_ctor_get(x_2395, 1);
lean_inc(x_2410);
lean_dec(x_2395);
x_2216 = x_2409;
x_2217 = x_2410;
goto block_2231;
}
}
else
{
lean_object* x_2411; lean_object* x_2412; 
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2175);
lean_dec(x_2164);
x_2411 = lean_ctor_get(x_2392, 0);
lean_inc(x_2411);
x_2412 = lean_ctor_get(x_2392, 1);
lean_inc(x_2412);
lean_dec(x_2392);
x_2216 = x_2411;
x_2217 = x_2412;
goto block_2231;
}
}
else
{
lean_object* x_2413; lean_object* x_2414; 
lean_dec(x_2377);
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2177);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
x_2413 = lean_ctor_get(x_2379, 0);
lean_inc(x_2413);
x_2414 = lean_ctor_get(x_2379, 1);
lean_inc(x_2414);
lean_dec(x_2379);
x_2216 = x_2413;
x_2217 = x_2414;
goto block_2231;
}
}
else
{
lean_object* x_2415; lean_object* x_2416; 
lean_dec(x_2311);
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2415 = lean_ctor_get(x_2372, 0);
lean_inc(x_2415);
x_2416 = lean_ctor_get(x_2372, 1);
lean_inc(x_2416);
lean_dec(x_2372);
x_2216 = x_2415;
x_2217 = x_2416;
goto block_2231;
}
}
}
else
{
lean_object* x_2417; lean_object* x_2418; 
lean_dec(x_2305);
lean_dec(x_2241);
lean_dec(x_2237);
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2176);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2417 = lean_ctor_get(x_2306, 0);
lean_inc(x_2417);
x_2418 = lean_ctor_get(x_2306, 1);
lean_inc(x_2418);
lean_dec(x_2306);
x_2216 = x_2417;
x_2217 = x_2418;
goto block_2231;
}
}
}
}
else
{
lean_object* x_2436; lean_object* x_2437; 
lean_dec(x_2237);
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2176);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2436 = lean_ctor_get(x_2238, 0);
lean_inc(x_2436);
x_2437 = lean_ctor_get(x_2238, 1);
lean_inc(x_2437);
lean_dec(x_2238);
x_2216 = x_2436;
x_2217 = x_2437;
goto block_2231;
}
}
else
{
lean_object* x_2438; lean_object* x_2439; 
lean_dec(x_2187);
lean_dec(x_2182);
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2176);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2164);
lean_dec(x_2110);
x_2438 = lean_ctor_get(x_2234, 0);
lean_inc(x_2438);
x_2439 = lean_ctor_get(x_2234, 1);
lean_inc(x_2439);
lean_dec(x_2234);
x_2216 = x_2438;
x_2217 = x_2439;
goto block_2231;
}
block_2215:
{
lean_object* x_2202; lean_object* x_2203; lean_object* x_2204; lean_object* x_2205; lean_object* x_2206; lean_object* x_2207; lean_object* x_2208; lean_object* x_2209; lean_object* x_2210; lean_object* x_2211; lean_object* x_2212; lean_object* x_2213; lean_object* x_2214; 
x_2202 = lean_ctor_get(x_2201, 2);
lean_inc(x_2202);
x_2203 = lean_ctor_get(x_2201, 0);
lean_inc(x_2203);
x_2204 = lean_ctor_get(x_2201, 1);
lean_inc(x_2204);
x_2205 = lean_ctor_get(x_2201, 3);
lean_inc(x_2205);
x_2206 = lean_ctor_get(x_2201, 4);
lean_inc(x_2206);
x_2207 = lean_ctor_get(x_2201, 5);
lean_inc(x_2207);
if (lean_is_exclusive(x_2201)) {
 lean_ctor_release(x_2201, 0);
 lean_ctor_release(x_2201, 1);
 lean_ctor_release(x_2201, 2);
 lean_ctor_release(x_2201, 3);
 lean_ctor_release(x_2201, 4);
 lean_ctor_release(x_2201, 5);
 x_2208 = x_2201;
} else {
 lean_dec_ref(x_2201);
 x_2208 = lean_box(0);
}
x_2209 = lean_ctor_get(x_2202, 0);
lean_inc(x_2209);
x_2210 = lean_ctor_get(x_2202, 1);
lean_inc(x_2210);
if (lean_is_exclusive(x_2202)) {
 lean_ctor_release(x_2202, 0);
 lean_ctor_release(x_2202, 1);
 lean_ctor_release(x_2202, 2);
 x_2211 = x_2202;
} else {
 lean_dec_ref(x_2202);
 x_2211 = lean_box(0);
}
if (lean_is_scalar(x_2211)) {
 x_2212 = lean_alloc_ctor(0, 3, 0);
} else {
 x_2212 = x_2211;
}
lean_ctor_set(x_2212, 0, x_2209);
lean_ctor_set(x_2212, 1, x_2210);
lean_ctor_set(x_2212, 2, x_2198);
if (lean_is_scalar(x_2208)) {
 x_2213 = lean_alloc_ctor(0, 6, 0);
} else {
 x_2213 = x_2208;
}
lean_ctor_set(x_2213, 0, x_2203);
lean_ctor_set(x_2213, 1, x_2204);
lean_ctor_set(x_2213, 2, x_2212);
lean_ctor_set(x_2213, 3, x_2205);
lean_ctor_set(x_2213, 4, x_2206);
lean_ctor_set(x_2213, 5, x_2207);
if (lean_is_scalar(x_2182)) {
 x_2214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2214 = x_2182;
}
lean_ctor_set(x_2214, 0, x_2200);
lean_ctor_set(x_2214, 1, x_2213);
x_2100 = x_2214;
goto block_2105;
}
block_2231:
{
lean_object* x_2218; lean_object* x_2219; lean_object* x_2220; lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; lean_object* x_2224; lean_object* x_2225; lean_object* x_2226; lean_object* x_2227; lean_object* x_2228; lean_object* x_2229; lean_object* x_2230; 
x_2218 = lean_ctor_get(x_2217, 2);
lean_inc(x_2218);
x_2219 = lean_ctor_get(x_2217, 0);
lean_inc(x_2219);
x_2220 = lean_ctor_get(x_2217, 1);
lean_inc(x_2220);
x_2221 = lean_ctor_get(x_2217, 3);
lean_inc(x_2221);
x_2222 = lean_ctor_get(x_2217, 4);
lean_inc(x_2222);
x_2223 = lean_ctor_get(x_2217, 5);
lean_inc(x_2223);
if (lean_is_exclusive(x_2217)) {
 lean_ctor_release(x_2217, 0);
 lean_ctor_release(x_2217, 1);
 lean_ctor_release(x_2217, 2);
 lean_ctor_release(x_2217, 3);
 lean_ctor_release(x_2217, 4);
 lean_ctor_release(x_2217, 5);
 x_2224 = x_2217;
} else {
 lean_dec_ref(x_2217);
 x_2224 = lean_box(0);
}
x_2225 = lean_ctor_get(x_2218, 0);
lean_inc(x_2225);
x_2226 = lean_ctor_get(x_2218, 1);
lean_inc(x_2226);
if (lean_is_exclusive(x_2218)) {
 lean_ctor_release(x_2218, 0);
 lean_ctor_release(x_2218, 1);
 lean_ctor_release(x_2218, 2);
 x_2227 = x_2218;
} else {
 lean_dec_ref(x_2218);
 x_2227 = lean_box(0);
}
if (lean_is_scalar(x_2227)) {
 x_2228 = lean_alloc_ctor(0, 3, 0);
} else {
 x_2228 = x_2227;
}
lean_ctor_set(x_2228, 0, x_2225);
lean_ctor_set(x_2228, 1, x_2226);
lean_ctor_set(x_2228, 2, x_2198);
if (lean_is_scalar(x_2224)) {
 x_2229 = lean_alloc_ctor(0, 6, 0);
} else {
 x_2229 = x_2224;
}
lean_ctor_set(x_2229, 0, x_2219);
lean_ctor_set(x_2229, 1, x_2220);
lean_ctor_set(x_2229, 2, x_2228);
lean_ctor_set(x_2229, 3, x_2221);
lean_ctor_set(x_2229, 4, x_2222);
lean_ctor_set(x_2229, 5, x_2223);
if (lean_is_scalar(x_2171)) {
 x_2230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2230 = x_2171;
 lean_ctor_set_tag(x_2230, 1);
}
lean_ctor_set(x_2230, 0, x_2216);
lean_ctor_set(x_2230, 1, x_2229);
x_2100 = x_2230;
goto block_2105;
}
}
}
else
{
lean_object* x_2694; lean_object* x_2695; 
lean_dec(x_2178);
lean_dec(x_2177);
lean_dec(x_2176);
lean_dec(x_2175);
lean_dec(x_2173);
lean_dec(x_2171);
lean_dec(x_2164);
lean_dec(x_2110);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_2694 = lean_ctor_get(x_2179, 0);
lean_inc(x_2694);
x_2695 = lean_ctor_get(x_2179, 1);
lean_inc(x_2695);
lean_dec(x_2179);
x_2084 = x_2694;
x_2085 = x_2695;
goto block_2099;
}
}
else
{
lean_object* x_2696; lean_object* x_2697; 
lean_dec(x_2164);
lean_dec(x_2110);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_2696 = lean_ctor_get(x_2168, 0);
lean_inc(x_2696);
x_2697 = lean_ctor_get(x_2168, 1);
lean_inc(x_2697);
lean_dec(x_2168);
x_2084 = x_2696;
x_2085 = x_2697;
goto block_2099;
}
}
else
{
lean_object* x_2698; lean_object* x_2699; 
lean_dec(x_2110);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_2698 = lean_ctor_get(x_2161, 0);
lean_inc(x_2698);
x_2699 = lean_ctor_get(x_2161, 1);
lean_inc(x_2699);
lean_dec(x_2161);
x_2084 = x_2698;
x_2085 = x_2699;
goto block_2099;
}
}
else
{
lean_object* x_2700; lean_object* x_2701; 
lean_dec(x_2153);
lean_dec(x_2110);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_2700 = lean_ctor_get(x_2155, 0);
lean_inc(x_2700);
x_2701 = lean_ctor_get(x_2155, 1);
lean_inc(x_2701);
lean_dec(x_2155);
x_2084 = x_2700;
x_2085 = x_2701;
goto block_2099;
}
}
}
else
{
lean_object* x_2717; 
lean_dec(x_2152);
lean_dec(x_2151);
lean_dec(x_2110);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_2717 = lean_box(0);
x_2137 = x_2717;
goto block_2150;
}
}
}
}
}
}
else
{
lean_object* x_2723; lean_object* x_2724; 
lean_dec(x_2110);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_2723 = lean_ctor_get(x_2115, 0);
lean_inc(x_2723);
x_2724 = lean_ctor_get(x_2115, 1);
lean_inc(x_2724);
lean_dec(x_2115);
x_2084 = x_2723;
x_2085 = x_2724;
goto block_2099;
}
}
else
{
lean_object* x_2725; lean_object* x_2726; 
lean_dec(x_2110);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_2725 = lean_ctor_get(x_2113, 0);
lean_inc(x_2725);
x_2726 = lean_ctor_get(x_2113, 1);
lean_inc(x_2726);
lean_dec(x_2113);
x_2084 = x_2725;
x_2085 = x_2726;
goto block_2099;
}
}
else
{
lean_object* x_2727; lean_object* x_2728; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_2727 = lean_ctor_get(x_2109, 0);
lean_inc(x_2727);
x_2728 = lean_ctor_get(x_2109, 1);
lean_inc(x_2728);
lean_dec(x_2109);
x_2084 = x_2727;
x_2085 = x_2728;
goto block_2099;
}
block_2083:
{
lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; 
x_2070 = lean_ctor_get(x_2069, 2);
lean_inc(x_2070);
x_2071 = lean_ctor_get(x_2069, 0);
lean_inc(x_2071);
x_2072 = lean_ctor_get(x_2069, 1);
lean_inc(x_2072);
x_2073 = lean_ctor_get(x_2069, 3);
lean_inc(x_2073);
x_2074 = lean_ctor_get(x_2069, 4);
lean_inc(x_2074);
x_2075 = lean_ctor_get(x_2069, 5);
lean_inc(x_2075);
if (lean_is_exclusive(x_2069)) {
 lean_ctor_release(x_2069, 0);
 lean_ctor_release(x_2069, 1);
 lean_ctor_release(x_2069, 2);
 lean_ctor_release(x_2069, 3);
 lean_ctor_release(x_2069, 4);
 lean_ctor_release(x_2069, 5);
 x_2076 = x_2069;
} else {
 lean_dec_ref(x_2069);
 x_2076 = lean_box(0);
}
x_2077 = lean_ctor_get(x_2070, 0);
lean_inc(x_2077);
x_2078 = lean_ctor_get(x_2070, 1);
lean_inc(x_2078);
if (lean_is_exclusive(x_2070)) {
 lean_ctor_release(x_2070, 0);
 lean_ctor_release(x_2070, 1);
 lean_ctor_release(x_2070, 2);
 x_2079 = x_2070;
} else {
 lean_dec_ref(x_2070);
 x_2079 = lean_box(0);
}
if (lean_is_scalar(x_2079)) {
 x_2080 = lean_alloc_ctor(0, 3, 0);
} else {
 x_2080 = x_2079;
}
lean_ctor_set(x_2080, 0, x_2077);
lean_ctor_set(x_2080, 1, x_2078);
lean_ctor_set(x_2080, 2, x_2066);
if (lean_is_scalar(x_2076)) {
 x_2081 = lean_alloc_ctor(0, 6, 0);
} else {
 x_2081 = x_2076;
}
lean_ctor_set(x_2081, 0, x_2071);
lean_ctor_set(x_2081, 1, x_2072);
lean_ctor_set(x_2081, 2, x_2080);
lean_ctor_set(x_2081, 3, x_2073);
lean_ctor_set(x_2081, 4, x_2074);
lean_ctor_set(x_2081, 5, x_2075);
if (lean_is_scalar(x_10)) {
 x_2082 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2082 = x_10;
}
lean_ctor_set(x_2082, 0, x_2068);
lean_ctor_set(x_2082, 1, x_2081);
return x_2082;
}
block_2099:
{
lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; lean_object* x_2097; lean_object* x_2098; 
x_2086 = lean_ctor_get(x_2085, 2);
lean_inc(x_2086);
x_2087 = lean_ctor_get(x_2085, 0);
lean_inc(x_2087);
x_2088 = lean_ctor_get(x_2085, 1);
lean_inc(x_2088);
x_2089 = lean_ctor_get(x_2085, 3);
lean_inc(x_2089);
x_2090 = lean_ctor_get(x_2085, 4);
lean_inc(x_2090);
x_2091 = lean_ctor_get(x_2085, 5);
lean_inc(x_2091);
if (lean_is_exclusive(x_2085)) {
 lean_ctor_release(x_2085, 0);
 lean_ctor_release(x_2085, 1);
 lean_ctor_release(x_2085, 2);
 lean_ctor_release(x_2085, 3);
 lean_ctor_release(x_2085, 4);
 lean_ctor_release(x_2085, 5);
 x_2092 = x_2085;
} else {
 lean_dec_ref(x_2085);
 x_2092 = lean_box(0);
}
x_2093 = lean_ctor_get(x_2086, 0);
lean_inc(x_2093);
x_2094 = lean_ctor_get(x_2086, 1);
lean_inc(x_2094);
if (lean_is_exclusive(x_2086)) {
 lean_ctor_release(x_2086, 0);
 lean_ctor_release(x_2086, 1);
 lean_ctor_release(x_2086, 2);
 x_2095 = x_2086;
} else {
 lean_dec_ref(x_2086);
 x_2095 = lean_box(0);
}
if (lean_is_scalar(x_2095)) {
 x_2096 = lean_alloc_ctor(0, 3, 0);
} else {
 x_2096 = x_2095;
}
lean_ctor_set(x_2096, 0, x_2093);
lean_ctor_set(x_2096, 1, x_2094);
lean_ctor_set(x_2096, 2, x_2066);
if (lean_is_scalar(x_2092)) {
 x_2097 = lean_alloc_ctor(0, 6, 0);
} else {
 x_2097 = x_2092;
}
lean_ctor_set(x_2097, 0, x_2087);
lean_ctor_set(x_2097, 1, x_2088);
lean_ctor_set(x_2097, 2, x_2096);
lean_ctor_set(x_2097, 3, x_2089);
lean_ctor_set(x_2097, 4, x_2090);
lean_ctor_set(x_2097, 5, x_2091);
x_2098 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2098, 0, x_2084);
lean_ctor_set(x_2098, 1, x_2097);
return x_2098;
}
block_2105:
{
if (lean_obj_tag(x_2100) == 0)
{
lean_object* x_2101; lean_object* x_2102; 
x_2101 = lean_ctor_get(x_2100, 0);
lean_inc(x_2101);
x_2102 = lean_ctor_get(x_2100, 1);
lean_inc(x_2102);
lean_dec(x_2100);
x_2068 = x_2101;
x_2069 = x_2102;
goto block_2083;
}
else
{
lean_object* x_2103; lean_object* x_2104; 
lean_dec(x_10);
x_2103 = lean_ctor_get(x_2100, 0);
lean_inc(x_2103);
x_2104 = lean_ctor_get(x_2100, 1);
lean_inc(x_2104);
lean_dec(x_2100);
x_2084 = x_2103;
x_2085 = x_2104;
goto block_2099;
}
}
}
}
}
else
{
uint8_t x_4061; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_4061 = !lean_is_exclusive(x_7);
if (x_4061 == 0)
{
return x_7;
}
else
{
lean_object* x_4062; lean_object* x_4063; lean_object* x_4064; 
x_4062 = lean_ctor_get(x_7, 0);
x_4063 = lean_ctor_get(x_7, 1);
lean_inc(x_4063);
lean_inc(x_4062);
lean_dec(x_7);
x_4064 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4064, 0, x_4062);
lean_ctor_set(x_4064, 1, x_4063);
return x_4064;
}
}
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_Meta_substCore___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_substCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_substCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Meta_substCore(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_fget(x_4, x_5);
lean_inc(x_3);
x_13 = l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(x_1, x_2, x_3, x_12, x_6, x_7);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_5, x_16);
lean_dec(x_5);
x_5 = x_17;
x_7 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_array_fget(x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_18 = l_Lean_LocalDecl_type(x_16);
x_19 = lean_unsigned_to_nat(3u);
x_20 = l_Lean_Expr_isAppOfArity___main(x_18, x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
lean_dec(x_5);
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_53; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Expr_getAppNumArgsAux___main(x_18, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_25, x_26);
x_28 = lean_nat_sub(x_27, x_26);
lean_dec(x_27);
x_29 = l_Lean_Expr_getRevArg_x21___main(x_18, x_28);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_sub(x_25, x_30);
lean_dec(x_25);
x_32 = lean_nat_sub(x_31, x_26);
lean_dec(x_31);
x_33 = l_Lean_Expr_getRevArg_x21___main(x_18, x_32);
lean_dec(x_18);
x_53 = l_Lean_Expr_isFVar(x_33);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
x_34 = x_54;
goto block_52;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Lean_Expr_fvarId_x21(x_33);
x_56 = lean_name_eq(x_55, x_1);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_box(0);
x_34 = x_57;
goto block_52;
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_inc(x_29);
lean_inc(x_3);
x_58 = l_Lean_MetavarContext_exprDependsOn(x_3, x_29, x_1);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_3);
x_60 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_61 = 1;
x_62 = lean_box(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_7);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_box(0);
x_34 = x_66;
goto block_52;
}
}
}
block_52:
{
uint8_t x_35; 
lean_dec(x_34);
x_35 = l_Lean_Expr_isFVar(x_29);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_16);
x_36 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_36;
goto _start;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Expr_fvarId_x21(x_29);
lean_dec(x_29);
x_39 = lean_name_eq(x_38, x_1);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_16);
x_40 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_40;
goto _start;
}
else
{
lean_object* x_42; uint8_t x_43; 
lean_inc(x_3);
x_42 = l_Lean_MetavarContext_exprDependsOn(x_3, x_33, x_1);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_5);
lean_dec(x_3);
x_44 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_45 = 0;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
if (lean_is_scalar(x_17)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_17;
}
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_7);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_17);
lean_dec(x_16);
x_50 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_50;
goto _start;
}
}
}
}
}
}
}
}
}
lean_object* l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(x_1, x_2, x_3, x_7, x_8, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(x_1, x_2, x_3, x_10, x_11, x_5, x_6);
return x_12;
}
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_array_fget(x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_18 = l_Lean_LocalDecl_type(x_16);
x_19 = lean_unsigned_to_nat(3u);
x_20 = l_Lean_Expr_isAppOfArity___main(x_18, x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
lean_dec(x_5);
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_53; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Expr_getAppNumArgsAux___main(x_18, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_25, x_26);
x_28 = lean_nat_sub(x_27, x_26);
lean_dec(x_27);
x_29 = l_Lean_Expr_getRevArg_x21___main(x_18, x_28);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_sub(x_25, x_30);
lean_dec(x_25);
x_32 = lean_nat_sub(x_31, x_26);
lean_dec(x_31);
x_33 = l_Lean_Expr_getRevArg_x21___main(x_18, x_32);
lean_dec(x_18);
x_53 = l_Lean_Expr_isFVar(x_33);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
x_34 = x_54;
goto block_52;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Lean_Expr_fvarId_x21(x_33);
x_56 = lean_name_eq(x_55, x_1);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_box(0);
x_34 = x_57;
goto block_52;
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_inc(x_29);
lean_inc(x_3);
x_58 = l_Lean_MetavarContext_exprDependsOn(x_3, x_29, x_1);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_3);
x_60 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_61 = 1;
x_62 = lean_box(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_7);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_box(0);
x_34 = x_66;
goto block_52;
}
}
}
block_52:
{
uint8_t x_35; 
lean_dec(x_34);
x_35 = l_Lean_Expr_isFVar(x_29);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_16);
x_36 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_36;
goto _start;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Expr_fvarId_x21(x_29);
lean_dec(x_29);
x_39 = lean_name_eq(x_38, x_1);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_16);
x_40 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_40;
goto _start;
}
else
{
lean_object* x_42; uint8_t x_43; 
lean_inc(x_3);
x_42 = l_Lean_MetavarContext_exprDependsOn(x_3, x_33, x_1);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_5);
lean_dec(x_3);
x_44 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_45 = 0;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
if (lean_is_scalar(x_17)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_17;
}
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_7);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_17);
lean_dec(x_16);
x_50 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_50;
goto _start;
}
}
}
}
}
}
}
}
}
lean_object* l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_3);
x_8 = l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(x_1, x_2, x_3, x_7, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(x_1, x_2, x_3, x_11, x_12, x_5, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_8, 0);
lean_dec(x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_subst___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_LocalInstance_beq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_fget(x_4, x_5);
lean_inc(x_3);
x_13 = l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__10(x_1, x_2, x_3, x_12, x_6, x_7);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_5, x_16);
lean_dec(x_5);
x_5 = x_17;
x_7 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_array_fget(x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_18 = l_Lean_LocalDecl_type(x_16);
x_19 = lean_unsigned_to_nat(3u);
x_20 = l_Lean_Expr_isAppOfArity___main(x_18, x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
lean_dec(x_5);
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_53; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Expr_getAppNumArgsAux___main(x_18, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_25, x_26);
x_28 = lean_nat_sub(x_27, x_26);
lean_dec(x_27);
x_29 = l_Lean_Expr_getRevArg_x21___main(x_18, x_28);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_sub(x_25, x_30);
lean_dec(x_25);
x_32 = lean_nat_sub(x_31, x_26);
lean_dec(x_31);
x_33 = l_Lean_Expr_getRevArg_x21___main(x_18, x_32);
lean_dec(x_18);
x_53 = l_Lean_Expr_isFVar(x_33);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
x_34 = x_54;
goto block_52;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Lean_Expr_fvarId_x21(x_33);
x_56 = lean_name_eq(x_55, x_1);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_box(0);
x_34 = x_57;
goto block_52;
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_inc(x_29);
lean_inc(x_3);
x_58 = l_Lean_MetavarContext_exprDependsOn(x_3, x_29, x_1);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_3);
x_60 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_61 = 1;
x_62 = lean_box(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_7);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_box(0);
x_34 = x_66;
goto block_52;
}
}
}
block_52:
{
uint8_t x_35; 
lean_dec(x_34);
x_35 = l_Lean_Expr_isFVar(x_29);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_16);
x_36 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_36;
goto _start;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Expr_fvarId_x21(x_29);
lean_dec(x_29);
x_39 = lean_name_eq(x_38, x_1);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_16);
x_40 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_40;
goto _start;
}
else
{
lean_object* x_42; uint8_t x_43; 
lean_inc(x_3);
x_42 = l_Lean_MetavarContext_exprDependsOn(x_3, x_33, x_1);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_5);
lean_dec(x_3);
x_44 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_45 = 0;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
if (lean_is_scalar(x_17)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_17;
}
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_7);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_17);
lean_dec(x_16);
x_50 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_50;
goto _start;
}
}
}
}
}
}
}
}
}
lean_object* l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__11(x_1, x_2, x_3, x_7, x_8, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__12(x_1, x_2, x_3, x_10, x_11, x_5, x_6);
return x_12;
}
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_array_fget(x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_18 = l_Lean_LocalDecl_type(x_16);
x_19 = lean_unsigned_to_nat(3u);
x_20 = l_Lean_Expr_isAppOfArity___main(x_18, x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
lean_dec(x_5);
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_53; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Expr_getAppNumArgsAux___main(x_18, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_25, x_26);
x_28 = lean_nat_sub(x_27, x_26);
lean_dec(x_27);
x_29 = l_Lean_Expr_getRevArg_x21___main(x_18, x_28);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_sub(x_25, x_30);
lean_dec(x_25);
x_32 = lean_nat_sub(x_31, x_26);
lean_dec(x_31);
x_33 = l_Lean_Expr_getRevArg_x21___main(x_18, x_32);
lean_dec(x_18);
x_53 = l_Lean_Expr_isFVar(x_33);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
x_34 = x_54;
goto block_52;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Lean_Expr_fvarId_x21(x_33);
x_56 = lean_name_eq(x_55, x_1);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_box(0);
x_34 = x_57;
goto block_52;
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_inc(x_29);
lean_inc(x_3);
x_58 = l_Lean_MetavarContext_exprDependsOn(x_3, x_29, x_1);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_3);
x_60 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_61 = 1;
x_62 = lean_box(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_7);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_box(0);
x_34 = x_66;
goto block_52;
}
}
}
block_52:
{
uint8_t x_35; 
lean_dec(x_34);
x_35 = l_Lean_Expr_isFVar(x_29);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_16);
x_36 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_36;
goto _start;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Expr_fvarId_x21(x_29);
lean_dec(x_29);
x_39 = lean_name_eq(x_38, x_1);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_16);
x_40 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_40;
goto _start;
}
else
{
lean_object* x_42; uint8_t x_43; 
lean_inc(x_3);
x_42 = l_Lean_MetavarContext_exprDependsOn(x_3, x_33, x_1);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_5);
lean_dec(x_3);
x_44 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_45 = 0;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
if (lean_is_scalar(x_17)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_17;
}
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_7);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_17);
lean_dec(x_16);
x_50 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_50;
goto _start;
}
}
}
}
}
}
}
}
}
lean_object* l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_3);
x_8 = l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__10(x_1, x_2, x_3, x_7, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__13(x_1, x_2, x_3, x_11, x_12, x_5, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_8, 0);
lean_dec(x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__9(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_Meta_subst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("did not find equation for eliminating '");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_subst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_subst___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_subst___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid equality proof, it is not of the form (x = t) or (t = x)");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_subst___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_subst___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_subst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_Meta_getMVarDecl(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_ctor_get(x_3, 3);
x_12 = lean_ctor_get(x_3, 4);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 4);
lean_inc(x_14);
x_15 = lean_array_get_size(x_10);
x_16 = lean_array_get_size(x_14);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_9);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_11);
lean_ctor_set(x_18, 4, x_12);
if (x_17 == 0)
{
lean_object* x_366; 
lean_dec(x_14);
lean_dec(x_6);
x_366 = lean_box(0);
x_19 = x_366;
goto block_365;
}
else
{
lean_object* x_367; uint8_t x_368; 
x_367 = lean_unsigned_to_nat(0u);
x_368 = l_Array_isEqvAux___main___at_Lean_Meta_subst___spec__7(x_3, x_6, lean_box(0), x_10, x_14, x_367);
lean_dec(x_14);
lean_dec(x_6);
if (x_368 == 0)
{
lean_object* x_369; 
x_369 = lean_box(0);
x_19 = x_369;
goto block_365;
}
else
{
lean_object* x_370; 
lean_dec(x_8);
lean_inc(x_18);
lean_inc(x_2);
x_370 = l_Lean_Meta_getLocalDecl(x_2, x_18, x_7);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_373 = l_Lean_LocalDecl_type(x_371);
lean_dec(x_371);
x_374 = l_Lean_Expr_eq_x3f___closed__2;
x_375 = lean_unsigned_to_nat(3u);
x_376 = l_Lean_Expr_isAppOfArity___main(x_373, x_374, x_375);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_373);
x_377 = lean_ctor_get(x_372, 1);
lean_inc(x_377);
x_378 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__8(x_2, x_374, x_377, x_13, x_18, x_372);
lean_dec(x_13);
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_381 = l_Lean_mkFVar(x_2);
x_382 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_382, 0, x_381);
x_383 = l_Lean_Meta_subst___closed__3;
x_384 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_382);
x_385 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_386 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set(x_386, 1, x_385);
x_387 = l_Lean_Meta_substCore___closed__2;
x_388 = l_Lean_Meta_throwTacticEx___rarg(x_387, x_1, x_386, x_18, x_380);
lean_dec(x_18);
return x_388;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; uint8_t x_394; lean_object* x_395; 
lean_dec(x_2);
x_389 = lean_ctor_get(x_379, 0);
lean_inc(x_389);
lean_dec(x_379);
x_390 = lean_ctor_get(x_378, 1);
lean_inc(x_390);
lean_dec(x_378);
x_391 = lean_ctor_get(x_389, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_389, 1);
lean_inc(x_392);
lean_dec(x_389);
x_393 = 0;
x_394 = lean_unbox(x_392);
lean_dec(x_392);
x_395 = l_Lean_Meta_substCore(x_1, x_391, x_394, x_393, x_18, x_390);
if (lean_obj_tag(x_395) == 0)
{
uint8_t x_396; 
x_396 = !lean_is_exclusive(x_395);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; 
x_397 = lean_ctor_get(x_395, 0);
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
lean_dec(x_397);
lean_ctor_set(x_395, 0, x_398);
return x_395;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_399 = lean_ctor_get(x_395, 0);
x_400 = lean_ctor_get(x_395, 1);
lean_inc(x_400);
lean_inc(x_399);
lean_dec(x_395);
x_401 = lean_ctor_get(x_399, 1);
lean_inc(x_401);
lean_dec(x_399);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_400);
return x_402;
}
}
else
{
uint8_t x_403; 
x_403 = !lean_is_exclusive(x_395);
if (x_403 == 0)
{
return x_395;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_395, 0);
x_405 = lean_ctor_get(x_395, 1);
lean_inc(x_405);
lean_inc(x_404);
lean_dec(x_395);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
return x_406;
}
}
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; 
lean_dec(x_13);
x_407 = l_Lean_Expr_getAppNumArgsAux___main(x_373, x_367);
x_408 = lean_unsigned_to_nat(1u);
x_409 = lean_nat_sub(x_407, x_408);
x_410 = lean_nat_sub(x_409, x_408);
lean_dec(x_409);
x_411 = l_Lean_Expr_getRevArg_x21___main(x_373, x_410);
x_412 = lean_unsigned_to_nat(2u);
x_413 = lean_nat_sub(x_407, x_412);
lean_dec(x_407);
x_414 = lean_nat_sub(x_413, x_408);
lean_dec(x_413);
x_415 = l_Lean_Expr_getRevArg_x21___main(x_373, x_414);
x_416 = l_Lean_Expr_isFVar(x_415);
lean_dec(x_415);
if (x_416 == 0)
{
uint8_t x_417; 
x_417 = l_Lean_Expr_isFVar(x_411);
lean_dec(x_411);
if (x_417 == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_2);
x_418 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_418, 0, x_373);
x_419 = l_Lean_indentExpr(x_418);
x_420 = l_Lean_Meta_subst___closed__6;
x_421 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_419);
x_422 = l_Lean_Meta_substCore___closed__2;
x_423 = l_Lean_Meta_throwTacticEx___rarg(x_422, x_1, x_421, x_18, x_372);
lean_dec(x_18);
return x_423;
}
else
{
uint8_t x_424; lean_object* x_425; 
lean_dec(x_373);
x_424 = 0;
x_425 = l_Lean_Meta_substCore(x_1, x_2, x_424, x_424, x_18, x_372);
if (lean_obj_tag(x_425) == 0)
{
uint8_t x_426; 
x_426 = !lean_is_exclusive(x_425);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; 
x_427 = lean_ctor_get(x_425, 0);
x_428 = lean_ctor_get(x_427, 1);
lean_inc(x_428);
lean_dec(x_427);
lean_ctor_set(x_425, 0, x_428);
return x_425;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_429 = lean_ctor_get(x_425, 0);
x_430 = lean_ctor_get(x_425, 1);
lean_inc(x_430);
lean_inc(x_429);
lean_dec(x_425);
x_431 = lean_ctor_get(x_429, 1);
lean_inc(x_431);
lean_dec(x_429);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_430);
return x_432;
}
}
else
{
uint8_t x_433; 
x_433 = !lean_is_exclusive(x_425);
if (x_433 == 0)
{
return x_425;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_ctor_get(x_425, 0);
x_435 = lean_ctor_get(x_425, 1);
lean_inc(x_435);
lean_inc(x_434);
lean_dec(x_425);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
return x_436;
}
}
}
}
else
{
uint8_t x_437; uint8_t x_438; lean_object* x_439; 
lean_dec(x_411);
lean_dec(x_373);
x_437 = 1;
x_438 = 0;
x_439 = l_Lean_Meta_substCore(x_1, x_2, x_437, x_438, x_18, x_372);
if (lean_obj_tag(x_439) == 0)
{
uint8_t x_440; 
x_440 = !lean_is_exclusive(x_439);
if (x_440 == 0)
{
lean_object* x_441; lean_object* x_442; 
x_441 = lean_ctor_get(x_439, 0);
x_442 = lean_ctor_get(x_441, 1);
lean_inc(x_442);
lean_dec(x_441);
lean_ctor_set(x_439, 0, x_442);
return x_439;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_443 = lean_ctor_get(x_439, 0);
x_444 = lean_ctor_get(x_439, 1);
lean_inc(x_444);
lean_inc(x_443);
lean_dec(x_439);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec(x_443);
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_444);
return x_446;
}
}
else
{
uint8_t x_447; 
x_447 = !lean_is_exclusive(x_439);
if (x_447 == 0)
{
return x_439;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_439, 0);
x_449 = lean_ctor_get(x_439, 1);
lean_inc(x_449);
lean_inc(x_448);
lean_dec(x_439);
x_450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
return x_450;
}
}
}
}
}
else
{
uint8_t x_451; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_451 = !lean_is_exclusive(x_370);
if (x_451 == 0)
{
return x_370;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_452 = lean_ctor_get(x_370, 0);
x_453 = lean_ctor_get(x_370, 1);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_370);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
return x_454;
}
}
}
}
block_365:
{
uint8_t x_20; 
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_7, 2);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_48; lean_object* x_49; lean_object* x_72; lean_object* x_73; 
x_23 = lean_ctor_get(x_21, 2);
x_72 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_21, 2, x_72);
lean_inc(x_18);
lean_inc(x_2);
x_73 = l_Lean_Meta_getLocalDecl(x_2, x_18, x_7);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_LocalDecl_type(x_74);
lean_dec(x_74);
x_77 = l_Lean_Expr_eq_x3f___closed__2;
x_78 = lean_unsigned_to_nat(3u);
x_79 = l_Lean_Expr_isAppOfArity___main(x_76, x_77, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_76);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
x_81 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(x_2, x_77, x_80, x_13, x_18, x_75);
lean_dec(x_13);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_8);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_mkFVar(x_2);
x_85 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = l_Lean_Meta_subst___closed__3;
x_87 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_89 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Meta_substCore___closed__2;
x_91 = l_Lean_Meta_throwTacticEx___rarg(x_90, x_1, x_89, x_18, x_83);
lean_dec(x_18);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_48 = x_92;
x_49 = x_93;
goto block_71;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_99; lean_object* x_100; 
lean_dec(x_2);
x_94 = lean_ctor_get(x_82, 0);
lean_inc(x_94);
lean_dec(x_82);
x_95 = lean_ctor_get(x_81, 1);
lean_inc(x_95);
lean_dec(x_81);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = 0;
x_99 = lean_unbox(x_97);
lean_dec(x_97);
x_100 = l_Lean_Meta_substCore(x_1, x_96, x_99, x_98, x_18, x_95);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_24 = x_103;
x_25 = x_102;
goto block_47;
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_8);
x_104 = lean_ctor_get(x_100, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_100, 1);
lean_inc(x_105);
lean_dec(x_100);
x_48 = x_104;
x_49 = x_105;
goto block_71;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_13);
x_106 = lean_unsigned_to_nat(0u);
x_107 = l_Lean_Expr_getAppNumArgsAux___main(x_76, x_106);
x_108 = lean_unsigned_to_nat(1u);
x_109 = lean_nat_sub(x_107, x_108);
x_110 = lean_nat_sub(x_109, x_108);
lean_dec(x_109);
x_111 = l_Lean_Expr_getRevArg_x21___main(x_76, x_110);
x_112 = lean_unsigned_to_nat(2u);
x_113 = lean_nat_sub(x_107, x_112);
lean_dec(x_107);
x_114 = lean_nat_sub(x_113, x_108);
lean_dec(x_113);
x_115 = l_Lean_Expr_getRevArg_x21___main(x_76, x_114);
x_116 = l_Lean_Expr_isFVar(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
uint8_t x_117; 
x_117 = l_Lean_Expr_isFVar(x_111);
lean_dec(x_111);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_8);
lean_dec(x_2);
x_118 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_118, 0, x_76);
x_119 = l_Lean_indentExpr(x_118);
x_120 = l_Lean_Meta_subst___closed__6;
x_121 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = l_Lean_Meta_substCore___closed__2;
x_123 = l_Lean_Meta_throwTacticEx___rarg(x_122, x_1, x_121, x_18, x_75);
lean_dec(x_18);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_48 = x_124;
x_49 = x_125;
goto block_71;
}
else
{
uint8_t x_126; lean_object* x_127; 
lean_dec(x_76);
x_126 = 0;
x_127 = l_Lean_Meta_substCore(x_1, x_2, x_126, x_126, x_18, x_75);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_24 = x_130;
x_25 = x_129;
goto block_47;
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_8);
x_131 = lean_ctor_get(x_127, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_dec(x_127);
x_48 = x_131;
x_49 = x_132;
goto block_71;
}
}
}
else
{
uint8_t x_133; uint8_t x_134; lean_object* x_135; 
lean_dec(x_111);
lean_dec(x_76);
x_133 = 1;
x_134 = 0;
x_135 = l_Lean_Meta_substCore(x_1, x_2, x_133, x_134, x_18, x_75);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_24 = x_138;
x_25 = x_137;
goto block_47;
}
else
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_8);
x_139 = lean_ctor_get(x_135, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_135, 1);
lean_inc(x_140);
lean_dec(x_135);
x_48 = x_139;
x_49 = x_140;
goto block_71;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_141 = lean_ctor_get(x_73, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_73, 1);
lean_inc(x_142);
lean_dec(x_73);
x_48 = x_141;
x_49 = x_142;
goto block_71;
}
block_47:
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 2);
lean_dec(x_29);
lean_ctor_set(x_27, 2, x_23);
if (lean_is_scalar(x_8)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_8;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_23);
lean_ctor_set(x_25, 2, x_33);
if (lean_is_scalar(x_8)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_8;
}
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_ctor_get(x_25, 2);
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
x_38 = lean_ctor_get(x_25, 3);
x_39 = lean_ctor_get(x_25, 4);
x_40 = lean_ctor_get(x_25, 5);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_35);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 x_43 = x_35;
} else {
 lean_dec_ref(x_35);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 3, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_23);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_38);
lean_ctor_set(x_45, 4, x_39);
lean_ctor_set(x_45, 5, x_40);
if (lean_is_scalar(x_8)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_8;
}
lean_ctor_set(x_46, 0, x_24);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
block_71:
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_49, 2);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 2);
lean_dec(x_53);
lean_ctor_set(x_51, 2, x_23);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_23);
lean_ctor_set(x_49, 2, x_57);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_49);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_59 = lean_ctor_get(x_49, 2);
x_60 = lean_ctor_get(x_49, 0);
x_61 = lean_ctor_get(x_49, 1);
x_62 = lean_ctor_get(x_49, 3);
x_63 = lean_ctor_get(x_49, 4);
x_64 = lean_ctor_get(x_49, 5);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_59);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_49);
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 x_67 = x_59;
} else {
 lean_dec_ref(x_59);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 3, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_68, 2, x_23);
x_69 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_61);
lean_ctor_set(x_69, 2, x_68);
lean_ctor_set(x_69, 3, x_62);
lean_ctor_set(x_69, 4, x_63);
lean_ctor_set(x_69, 5, x_64);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_48);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_162; lean_object* x_163; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_143 = lean_ctor_get(x_21, 0);
x_144 = lean_ctor_get(x_21, 1);
x_145 = lean_ctor_get(x_21, 2);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_21);
x_178 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_179 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_179, 0, x_143);
lean_ctor_set(x_179, 1, x_144);
lean_ctor_set(x_179, 2, x_178);
lean_ctor_set(x_7, 2, x_179);
lean_inc(x_18);
lean_inc(x_2);
x_180 = l_Lean_Meta_getLocalDecl(x_2, x_18, x_7);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = l_Lean_LocalDecl_type(x_181);
lean_dec(x_181);
x_184 = l_Lean_Expr_eq_x3f___closed__2;
x_185 = lean_unsigned_to_nat(3u);
x_186 = l_Lean_Expr_isAppOfArity___main(x_183, x_184, x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_183);
x_187 = lean_ctor_get(x_182, 1);
lean_inc(x_187);
x_188 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(x_2, x_184, x_187, x_13, x_18, x_182);
lean_dec(x_13);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_8);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_mkFVar(x_2);
x_192 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_193 = l_Lean_Meta_subst___closed__3;
x_194 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_196 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_197 = l_Lean_Meta_substCore___closed__2;
x_198 = l_Lean_Meta_throwTacticEx___rarg(x_197, x_1, x_196, x_18, x_190);
lean_dec(x_18);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_162 = x_199;
x_163 = x_200;
goto block_177;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; uint8_t x_206; lean_object* x_207; 
lean_dec(x_2);
x_201 = lean_ctor_get(x_189, 0);
lean_inc(x_201);
lean_dec(x_189);
x_202 = lean_ctor_get(x_188, 1);
lean_inc(x_202);
lean_dec(x_188);
x_203 = lean_ctor_get(x_201, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
lean_dec(x_201);
x_205 = 0;
x_206 = lean_unbox(x_204);
lean_dec(x_204);
x_207 = l_Lean_Meta_substCore(x_1, x_203, x_206, x_205, x_18, x_202);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_146 = x_210;
x_147 = x_209;
goto block_161;
}
else
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_8);
x_211 = lean_ctor_get(x_207, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_207, 1);
lean_inc(x_212);
lean_dec(x_207);
x_162 = x_211;
x_163 = x_212;
goto block_177;
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
lean_dec(x_13);
x_213 = lean_unsigned_to_nat(0u);
x_214 = l_Lean_Expr_getAppNumArgsAux___main(x_183, x_213);
x_215 = lean_unsigned_to_nat(1u);
x_216 = lean_nat_sub(x_214, x_215);
x_217 = lean_nat_sub(x_216, x_215);
lean_dec(x_216);
x_218 = l_Lean_Expr_getRevArg_x21___main(x_183, x_217);
x_219 = lean_unsigned_to_nat(2u);
x_220 = lean_nat_sub(x_214, x_219);
lean_dec(x_214);
x_221 = lean_nat_sub(x_220, x_215);
lean_dec(x_220);
x_222 = l_Lean_Expr_getRevArg_x21___main(x_183, x_221);
x_223 = l_Lean_Expr_isFVar(x_222);
lean_dec(x_222);
if (x_223 == 0)
{
uint8_t x_224; 
x_224 = l_Lean_Expr_isFVar(x_218);
lean_dec(x_218);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_8);
lean_dec(x_2);
x_225 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_225, 0, x_183);
x_226 = l_Lean_indentExpr(x_225);
x_227 = l_Lean_Meta_subst___closed__6;
x_228 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_226);
x_229 = l_Lean_Meta_substCore___closed__2;
x_230 = l_Lean_Meta_throwTacticEx___rarg(x_229, x_1, x_228, x_18, x_182);
lean_dec(x_18);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_162 = x_231;
x_163 = x_232;
goto block_177;
}
else
{
uint8_t x_233; lean_object* x_234; 
lean_dec(x_183);
x_233 = 0;
x_234 = l_Lean_Meta_substCore(x_1, x_2, x_233, x_233, x_18, x_182);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_146 = x_237;
x_147 = x_236;
goto block_161;
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_8);
x_238 = lean_ctor_get(x_234, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_234, 1);
lean_inc(x_239);
lean_dec(x_234);
x_162 = x_238;
x_163 = x_239;
goto block_177;
}
}
}
else
{
uint8_t x_240; uint8_t x_241; lean_object* x_242; 
lean_dec(x_218);
lean_dec(x_183);
x_240 = 1;
x_241 = 0;
x_242 = l_Lean_Meta_substCore(x_1, x_2, x_240, x_241, x_18, x_182);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_146 = x_245;
x_147 = x_244;
goto block_161;
}
else
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_8);
x_246 = lean_ctor_get(x_242, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_242, 1);
lean_inc(x_247);
lean_dec(x_242);
x_162 = x_246;
x_163 = x_247;
goto block_177;
}
}
}
}
else
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_248 = lean_ctor_get(x_180, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_180, 1);
lean_inc(x_249);
lean_dec(x_180);
x_162 = x_248;
x_163 = x_249;
goto block_177;
}
block_161:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_148 = lean_ctor_get(x_147, 2);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_147, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_147, 4);
lean_inc(x_152);
x_153 = lean_ctor_get(x_147, 5);
lean_inc(x_153);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 lean_ctor_release(x_147, 2);
 lean_ctor_release(x_147, 3);
 lean_ctor_release(x_147, 4);
 lean_ctor_release(x_147, 5);
 x_154 = x_147;
} else {
 lean_dec_ref(x_147);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_148, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_148, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 lean_ctor_release(x_148, 2);
 x_157 = x_148;
} else {
 lean_dec_ref(x_148);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 3, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
lean_ctor_set(x_158, 2, x_145);
if (lean_is_scalar(x_154)) {
 x_159 = lean_alloc_ctor(0, 6, 0);
} else {
 x_159 = x_154;
}
lean_ctor_set(x_159, 0, x_149);
lean_ctor_set(x_159, 1, x_150);
lean_ctor_set(x_159, 2, x_158);
lean_ctor_set(x_159, 3, x_151);
lean_ctor_set(x_159, 4, x_152);
lean_ctor_set(x_159, 5, x_153);
if (lean_is_scalar(x_8)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_8;
}
lean_ctor_set(x_160, 0, x_146);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
block_177:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_164 = lean_ctor_get(x_163, 2);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_163, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_163, 4);
lean_inc(x_168);
x_169 = lean_ctor_get(x_163, 5);
lean_inc(x_169);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 lean_ctor_release(x_163, 2);
 lean_ctor_release(x_163, 3);
 lean_ctor_release(x_163, 4);
 lean_ctor_release(x_163, 5);
 x_170 = x_163;
} else {
 lean_dec_ref(x_163);
 x_170 = lean_box(0);
}
x_171 = lean_ctor_get(x_164, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_164, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 lean_ctor_release(x_164, 2);
 x_173 = x_164;
} else {
 lean_dec_ref(x_164);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(0, 3, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
lean_ctor_set(x_174, 2, x_145);
if (lean_is_scalar(x_170)) {
 x_175 = lean_alloc_ctor(0, 6, 0);
} else {
 x_175 = x_170;
}
lean_ctor_set(x_175, 0, x_165);
lean_ctor_set(x_175, 1, x_166);
lean_ctor_set(x_175, 2, x_174);
lean_ctor_set(x_175, 3, x_167);
lean_ctor_set(x_175, 4, x_168);
lean_ctor_set(x_175, 5, x_169);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_162);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_276; lean_object* x_277; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_250 = lean_ctor_get(x_7, 2);
x_251 = lean_ctor_get(x_7, 0);
x_252 = lean_ctor_get(x_7, 1);
x_253 = lean_ctor_get(x_7, 3);
x_254 = lean_ctor_get(x_7, 4);
x_255 = lean_ctor_get(x_7, 5);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_250);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_7);
x_256 = lean_ctor_get(x_250, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_250, 1);
lean_inc(x_257);
x_258 = lean_ctor_get(x_250, 2);
lean_inc(x_258);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 lean_ctor_release(x_250, 2);
 x_259 = x_250;
} else {
 lean_dec_ref(x_250);
 x_259 = lean_box(0);
}
x_292 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_259)) {
 x_293 = lean_alloc_ctor(0, 3, 0);
} else {
 x_293 = x_259;
}
lean_ctor_set(x_293, 0, x_256);
lean_ctor_set(x_293, 1, x_257);
lean_ctor_set(x_293, 2, x_292);
x_294 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_294, 0, x_251);
lean_ctor_set(x_294, 1, x_252);
lean_ctor_set(x_294, 2, x_293);
lean_ctor_set(x_294, 3, x_253);
lean_ctor_set(x_294, 4, x_254);
lean_ctor_set(x_294, 5, x_255);
lean_inc(x_18);
lean_inc(x_2);
x_295 = l_Lean_Meta_getLocalDecl(x_2, x_18, x_294);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = l_Lean_LocalDecl_type(x_296);
lean_dec(x_296);
x_299 = l_Lean_Expr_eq_x3f___closed__2;
x_300 = lean_unsigned_to_nat(3u);
x_301 = l_Lean_Expr_isAppOfArity___main(x_298, x_299, x_300);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_298);
x_302 = lean_ctor_get(x_297, 1);
lean_inc(x_302);
x_303 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(x_2, x_299, x_302, x_13, x_18, x_297);
lean_dec(x_13);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_8);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = l_Lean_mkFVar(x_2);
x_307 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_307, 0, x_306);
x_308 = l_Lean_Meta_subst___closed__3;
x_309 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_307);
x_310 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_311 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
x_312 = l_Lean_Meta_substCore___closed__2;
x_313 = l_Lean_Meta_throwTacticEx___rarg(x_312, x_1, x_311, x_18, x_305);
lean_dec(x_18);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_276 = x_314;
x_277 = x_315;
goto block_291;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; uint8_t x_321; lean_object* x_322; 
lean_dec(x_2);
x_316 = lean_ctor_get(x_304, 0);
lean_inc(x_316);
lean_dec(x_304);
x_317 = lean_ctor_get(x_303, 1);
lean_inc(x_317);
lean_dec(x_303);
x_318 = lean_ctor_get(x_316, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_316, 1);
lean_inc(x_319);
lean_dec(x_316);
x_320 = 0;
x_321 = lean_unbox(x_319);
lean_dec(x_319);
x_322 = l_Lean_Meta_substCore(x_1, x_318, x_321, x_320, x_18, x_317);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_260 = x_325;
x_261 = x_324;
goto block_275;
}
else
{
lean_object* x_326; lean_object* x_327; 
lean_dec(x_8);
x_326 = lean_ctor_get(x_322, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_322, 1);
lean_inc(x_327);
lean_dec(x_322);
x_276 = x_326;
x_277 = x_327;
goto block_291;
}
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; 
lean_dec(x_13);
x_328 = lean_unsigned_to_nat(0u);
x_329 = l_Lean_Expr_getAppNumArgsAux___main(x_298, x_328);
x_330 = lean_unsigned_to_nat(1u);
x_331 = lean_nat_sub(x_329, x_330);
x_332 = lean_nat_sub(x_331, x_330);
lean_dec(x_331);
x_333 = l_Lean_Expr_getRevArg_x21___main(x_298, x_332);
x_334 = lean_unsigned_to_nat(2u);
x_335 = lean_nat_sub(x_329, x_334);
lean_dec(x_329);
x_336 = lean_nat_sub(x_335, x_330);
lean_dec(x_335);
x_337 = l_Lean_Expr_getRevArg_x21___main(x_298, x_336);
x_338 = l_Lean_Expr_isFVar(x_337);
lean_dec(x_337);
if (x_338 == 0)
{
uint8_t x_339; 
x_339 = l_Lean_Expr_isFVar(x_333);
lean_dec(x_333);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_8);
lean_dec(x_2);
x_340 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_340, 0, x_298);
x_341 = l_Lean_indentExpr(x_340);
x_342 = l_Lean_Meta_subst___closed__6;
x_343 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_341);
x_344 = l_Lean_Meta_substCore___closed__2;
x_345 = l_Lean_Meta_throwTacticEx___rarg(x_344, x_1, x_343, x_18, x_297);
lean_dec(x_18);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_276 = x_346;
x_277 = x_347;
goto block_291;
}
else
{
uint8_t x_348; lean_object* x_349; 
lean_dec(x_298);
x_348 = 0;
x_349 = l_Lean_Meta_substCore(x_1, x_2, x_348, x_348, x_18, x_297);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_260 = x_352;
x_261 = x_351;
goto block_275;
}
else
{
lean_object* x_353; lean_object* x_354; 
lean_dec(x_8);
x_353 = lean_ctor_get(x_349, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_349, 1);
lean_inc(x_354);
lean_dec(x_349);
x_276 = x_353;
x_277 = x_354;
goto block_291;
}
}
}
else
{
uint8_t x_355; uint8_t x_356; lean_object* x_357; 
lean_dec(x_333);
lean_dec(x_298);
x_355 = 1;
x_356 = 0;
x_357 = l_Lean_Meta_substCore(x_1, x_2, x_355, x_356, x_18, x_297);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
x_260 = x_360;
x_261 = x_359;
goto block_275;
}
else
{
lean_object* x_361; lean_object* x_362; 
lean_dec(x_8);
x_361 = lean_ctor_get(x_357, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_357, 1);
lean_inc(x_362);
lean_dec(x_357);
x_276 = x_361;
x_277 = x_362;
goto block_291;
}
}
}
}
else
{
lean_object* x_363; lean_object* x_364; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_363 = lean_ctor_get(x_295, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_295, 1);
lean_inc(x_364);
lean_dec(x_295);
x_276 = x_363;
x_277 = x_364;
goto block_291;
}
block_275:
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_262 = lean_ctor_get(x_261, 2);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_261, 3);
lean_inc(x_265);
x_266 = lean_ctor_get(x_261, 4);
lean_inc(x_266);
x_267 = lean_ctor_get(x_261, 5);
lean_inc(x_267);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 lean_ctor_release(x_261, 3);
 lean_ctor_release(x_261, 4);
 lean_ctor_release(x_261, 5);
 x_268 = x_261;
} else {
 lean_dec_ref(x_261);
 x_268 = lean_box(0);
}
x_269 = lean_ctor_get(x_262, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_262, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 lean_ctor_release(x_262, 2);
 x_271 = x_262;
} else {
 lean_dec_ref(x_262);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 3, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_270);
lean_ctor_set(x_272, 2, x_258);
if (lean_is_scalar(x_268)) {
 x_273 = lean_alloc_ctor(0, 6, 0);
} else {
 x_273 = x_268;
}
lean_ctor_set(x_273, 0, x_263);
lean_ctor_set(x_273, 1, x_264);
lean_ctor_set(x_273, 2, x_272);
lean_ctor_set(x_273, 3, x_265);
lean_ctor_set(x_273, 4, x_266);
lean_ctor_set(x_273, 5, x_267);
if (lean_is_scalar(x_8)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_8;
}
lean_ctor_set(x_274, 0, x_260);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
block_291:
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_278 = lean_ctor_get(x_277, 2);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_277, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_277, 3);
lean_inc(x_281);
x_282 = lean_ctor_get(x_277, 4);
lean_inc(x_282);
x_283 = lean_ctor_get(x_277, 5);
lean_inc(x_283);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 lean_ctor_release(x_277, 2);
 lean_ctor_release(x_277, 3);
 lean_ctor_release(x_277, 4);
 lean_ctor_release(x_277, 5);
 x_284 = x_277;
} else {
 lean_dec_ref(x_277);
 x_284 = lean_box(0);
}
x_285 = lean_ctor_get(x_278, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_278, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 lean_ctor_release(x_278, 2);
 x_287 = x_278;
} else {
 lean_dec_ref(x_278);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(0, 3, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
lean_ctor_set(x_288, 2, x_258);
if (lean_is_scalar(x_284)) {
 x_289 = lean_alloc_ctor(0, 6, 0);
} else {
 x_289 = x_284;
}
lean_ctor_set(x_289, 0, x_279);
lean_ctor_set(x_289, 1, x_280);
lean_ctor_set(x_289, 2, x_288);
lean_ctor_set(x_289, 3, x_281);
lean_ctor_set(x_289, 4, x_282);
lean_ctor_set(x_289, 5, x_283);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_276);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
}
}
else
{
uint8_t x_455; 
lean_dec(x_2);
lean_dec(x_1);
x_455 = !lean_is_exclusive(x_5);
if (x_455 == 0)
{
return x_5;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_ctor_get(x_5, 0);
x_457 = lean_ctor_get(x_5, 1);
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_5);
x_458 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_457);
return x_458;
}
}
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_subst___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_Meta_subst___spec__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__10(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__8(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_subst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_subst(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_substCore___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init_Lean_Meta_AppBuilder(lean_object*);
lean_object* initialize_Init_Lean_Meta_Message(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Util(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Revert(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Intro(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Clear(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_FVarSubst(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_Tactic_Subst(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta_AppBuilder(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Message(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Revert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Intro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Clear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_FVarSubst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_substCore___closed__1 = _init_l_Lean_Meta_substCore___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___closed__1);
l_Lean_Meta_substCore___closed__2 = _init_l_Lean_Meta_substCore___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___closed__2);
l_Lean_Meta_substCore___closed__3 = _init_l_Lean_Meta_substCore___closed__3();
lean_mark_persistent(l_Lean_Meta_substCore___closed__3);
l_Lean_Meta_substCore___closed__4 = _init_l_Lean_Meta_substCore___closed__4();
lean_mark_persistent(l_Lean_Meta_substCore___closed__4);
l_Lean_Meta_substCore___closed__5 = _init_l_Lean_Meta_substCore___closed__5();
lean_mark_persistent(l_Lean_Meta_substCore___closed__5);
l_Lean_Meta_substCore___closed__6 = _init_l_Lean_Meta_substCore___closed__6();
lean_mark_persistent(l_Lean_Meta_substCore___closed__6);
l_Lean_Meta_substCore___closed__7 = _init_l_Lean_Meta_substCore___closed__7();
lean_mark_persistent(l_Lean_Meta_substCore___closed__7);
l_Lean_Meta_substCore___closed__8 = _init_l_Lean_Meta_substCore___closed__8();
lean_mark_persistent(l_Lean_Meta_substCore___closed__8);
l_Lean_Meta_substCore___closed__9 = _init_l_Lean_Meta_substCore___closed__9();
lean_mark_persistent(l_Lean_Meta_substCore___closed__9);
l_Lean_Meta_substCore___closed__10 = _init_l_Lean_Meta_substCore___closed__10();
lean_mark_persistent(l_Lean_Meta_substCore___closed__10);
l_Lean_Meta_substCore___closed__11 = _init_l_Lean_Meta_substCore___closed__11();
lean_mark_persistent(l_Lean_Meta_substCore___closed__11);
l_Lean_Meta_substCore___closed__12 = _init_l_Lean_Meta_substCore___closed__12();
lean_mark_persistent(l_Lean_Meta_substCore___closed__12);
l_Lean_Meta_substCore___closed__13 = _init_l_Lean_Meta_substCore___closed__13();
lean_mark_persistent(l_Lean_Meta_substCore___closed__13);
l_Lean_Meta_substCore___closed__14 = _init_l_Lean_Meta_substCore___closed__14();
lean_mark_persistent(l_Lean_Meta_substCore___closed__14);
l_Lean_Meta_substCore___closed__15 = _init_l_Lean_Meta_substCore___closed__15();
lean_mark_persistent(l_Lean_Meta_substCore___closed__15);
l_Lean_Meta_substCore___closed__16 = _init_l_Lean_Meta_substCore___closed__16();
lean_mark_persistent(l_Lean_Meta_substCore___closed__16);
l_Lean_Meta_substCore___closed__17 = _init_l_Lean_Meta_substCore___closed__17();
lean_mark_persistent(l_Lean_Meta_substCore___closed__17);
l_Lean_Meta_substCore___closed__18 = _init_l_Lean_Meta_substCore___closed__18();
lean_mark_persistent(l_Lean_Meta_substCore___closed__18);
l_Lean_Meta_substCore___closed__19 = _init_l_Lean_Meta_substCore___closed__19();
lean_mark_persistent(l_Lean_Meta_substCore___closed__19);
l_Lean_Meta_substCore___closed__20 = _init_l_Lean_Meta_substCore___closed__20();
lean_mark_persistent(l_Lean_Meta_substCore___closed__20);
l_Lean_Meta_substCore___closed__21 = _init_l_Lean_Meta_substCore___closed__21();
lean_mark_persistent(l_Lean_Meta_substCore___closed__21);
l_Lean_Meta_subst___closed__1 = _init_l_Lean_Meta_subst___closed__1();
lean_mark_persistent(l_Lean_Meta_subst___closed__1);
l_Lean_Meta_subst___closed__2 = _init_l_Lean_Meta_subst___closed__2();
lean_mark_persistent(l_Lean_Meta_subst___closed__2);
l_Lean_Meta_subst___closed__3 = _init_l_Lean_Meta_subst___closed__3();
lean_mark_persistent(l_Lean_Meta_subst___closed__3);
l_Lean_Meta_subst___closed__4 = _init_l_Lean_Meta_subst___closed__4();
lean_mark_persistent(l_Lean_Meta_subst___closed__4);
l_Lean_Meta_subst___closed__5 = _init_l_Lean_Meta_subst___closed__5();
lean_mark_persistent(l_Lean_Meta_subst___closed__5);
l_Lean_Meta_subst___closed__6 = _init_l_Lean_Meta_subst___closed__6();
lean_mark_persistent(l_Lean_Meta_subst___closed__6);
l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1 = _init_l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1);
res = l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
