// Lean compiler output
// Module: Init.Lean.Meta.Tactic.Induction
// Imports: Init.Lean.Meta.RecursorInfo Init.Lean.Meta.SynthInstance Init.Lean.Meta.Tactic.Util Init.Lean.Meta.Tactic.Revert Init.Lean.Meta.Tactic.Intro Init.Lean.Meta.Tactic.Clear Init.Lean.Meta.Tactic.FVarSubst
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
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7;
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_1__getTargetArity(lean_object*);
lean_object* l_Lean_Meta_induction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfUntil___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_Meta_induction___spec__2(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_Lean_Level_Inhabited;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__7;
extern lean_object* l___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3;
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___boxed(lean_object**);
extern lean_object* l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___boxed(lean_object**);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__3;
lean_object* l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__2;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__2;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__1;
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_5__finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_elem___main___at_Lean_Meta_induction___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__9;
lean_object* l_Lean_Meta_getMVarType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__9;
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__8;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__4;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__8;
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_localDeclDependsOn(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8;
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Meta_InductionSubgoal_inhabited___closed__1;
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_1__getTargetArity___main(lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__6;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__2;
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__4;
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_5__finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_3__getTypeBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_3__getTypeBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___boxed(lean_object**);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__6;
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__3;
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6;
uint8_t l_Lean_Level_isZero(lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__5;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__5;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
extern lean_object* l_Lean_Meta_isClassQuick___main___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__4;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__1;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__2;
lean_object* l_Lean_Meta_InductionSubgoal_inhabited;
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__2;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__1;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__7;
lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_1__getTargetArity___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l___private_Init_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
return x_11;
}
case 10:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_1 = x_12;
goto _start;
}
default: 
{
lean_object* x_14; 
x_14 = lean_box(0);
x_2 = x_14;
goto block_7;
}
}
block_7:
{
uint8_t x_3; 
lean_dec(x_2);
x_3 = l_Lean_Expr_isHeadBetaTarget(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Expr_headBeta(x_1);
x_1 = x_5;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_1__getTargetArity(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("induction");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed recursor");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to generate type class instance parameter");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_Meta_inferType(x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
x_13 = l_Lean_Meta_whnfForall(x_11, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 7)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_5);
x_17 = l_Lean_Meta_synthInstance(x_16, x_5, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_mkApp(x_4, x_18);
x_3 = x_9;
x_4 = x_20;
x_6 = x_19;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_4);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_24 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8;
x_25 = l_Lean_Meta_throwTacticEx___rarg(x_23, x_1, x_24, x_5, x_22);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_14);
lean_dec(x_4);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_dec(x_13);
x_31 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_32 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_33 = l_Lean_Meta_throwTacticEx___rarg(x_31, x_1, x_32, x_5, x_30);
lean_dec(x_5);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
return x_13;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_10);
if (x_38 == 0)
{
return x_10;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_10, 0);
x_40 = lean_ctor_get(x_10, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_10);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_3, 1);
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_array_get_size(x_2);
x_45 = lean_nat_dec_lt(x_43, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_4);
x_46 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_47 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_48 = l_Lean_Meta_throwTacticEx___rarg(x_46, x_1, x_47, x_5, x_6);
lean_dec(x_5);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_array_fget(x_2, x_43);
x_50 = l_Lean_mkApp(x_4, x_49);
x_3 = x_42;
x_4 = x_50;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* _init_l_Lean_Meta_InductionSubgoal_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_InductionSubgoal_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_InductionSubgoal_inhabited___closed__1;
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_3__getTypeBody(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l_Lean_Meta_whnfForall(x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 7)
{
uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_expr_instantiate1(x_10, x_3);
lean_dec(x_10);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_ctor_get(x_7, 2);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_expr_instantiate1(x_13, x_3);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_18 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_19 = l_Lean_Meta_throwTacticEx___rarg(x_17, x_1, x_18, x_4, x_16);
lean_dec(x_4);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
return x_6;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_3__getTypeBody___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
x_12 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
x_13 = lean_nat_add(x_3, x_10);
x_14 = lean_nat_dec_le(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = l_Lean_Name_inhabited;
x_16 = lean_array_get(x_15, x_1, x_12);
x_17 = lean_nat_sub(x_12, x_3);
lean_dec(x_12);
x_18 = lean_nat_sub(x_17, x_10);
lean_dec(x_17);
x_19 = lean_array_get(x_15, x_4, x_18);
lean_dec(x_18);
x_20 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_16, x_19);
x_6 = x_11;
x_7 = x_20;
goto _start;
}
else
{
lean_dec(x_12);
x_6 = x_11;
goto _start;
}
}
else
{
lean_dec(x_6);
return x_7;
}
}
}
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
x_12 = lean_nat_sub(x_5, x_6);
lean_dec(x_6);
x_13 = lean_nat_add(x_3, x_10);
x_14 = lean_nat_dec_le(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = l_Lean_Name_inhabited;
x_16 = lean_array_get(x_15, x_1, x_12);
x_17 = lean_nat_sub(x_12, x_3);
lean_dec(x_12);
x_18 = lean_nat_sub(x_17, x_10);
lean_dec(x_17);
x_19 = lean_array_get(x_15, x_4, x_18);
lean_dec(x_18);
x_20 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_16, x_19);
x_6 = x_11;
x_7 = x_20;
goto _start;
}
else
{
lean_dec(x_12);
x_6 = x_11;
goto _start;
}
}
else
{
lean_dec(x_6);
return x_7;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_17 = l_Lean_mkApp(x_15, x_11);
lean_inc(x_6);
lean_inc(x_1);
x_18 = l___private_Init_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_16, x_11, x_6, x_7);
lean_dec(x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_5, 1, x_19);
lean_ctor_set(x_5, 0, x_17);
x_4 = x_13;
x_7 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_17);
lean_free_object(x_5);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_5, 0);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
lean_inc(x_11);
x_28 = l_Lean_mkApp(x_26, x_11);
lean_inc(x_6);
lean_inc(x_1);
x_29 = l___private_Init_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_27, x_11, x_6, x_7);
lean_dec(x_11);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_30);
x_4 = x_13;
x_5 = x_32;
x_7 = x_31;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_28);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_1);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
lean_inc(x_16);
x_18 = l_Lean_Meta_whnfForall(x_13, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_isForall(x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
if (x_14 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_12);
x_22 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_23 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_24 = l_Lean_Meta_throwTacticEx___rarg(x_22, x_1, x_23, x_16, x_20);
lean_dec(x_16);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; 
x_29 = l_Lean_Meta_assignExprMVar(x_1, x_12, x_16, x_20);
lean_dec(x_16);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_15);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_15);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_3, 3);
x_39 = lean_nat_dec_lt(x_10, x_38);
if (x_39 == 0)
{
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
if (x_14 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_15);
lean_dec(x_12);
x_40 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_41 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_42 = l_Lean_Meta_throwTacticEx___rarg(x_40, x_1, x_41, x_16, x_20);
lean_dec(x_16);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; 
x_47 = l_Lean_Meta_assignExprMVar(x_1, x_12, x_16, x_20);
lean_dec(x_16);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_15);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_15);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_15);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_47);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_Meta_RecursorInfo_firstIndexPos(x_3);
x_57 = lean_nat_dec_eq(x_10, x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_inc(x_1);
x_58 = l_Lean_Meta_getMVarTag(x_1, x_16, x_20);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_194; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_194 = lean_nat_dec_le(x_8, x_11);
if (x_194 == 0)
{
x_61 = x_60;
goto block_193;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
lean_dec(x_59);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_195 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_196 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_197 = l_Lean_Meta_throwTacticEx___rarg(x_195, x_1, x_196, x_16, x_60);
lean_dec(x_16);
x_198 = !lean_is_exclusive(x_197);
if (x_198 == 0)
{
return x_197;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_197, 0);
x_200 = lean_ctor_get(x_197, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_197);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
block_193:
{
if (lean_obj_tag(x_19) == 7)
{
lean_object* x_62; lean_object* x_63; uint64_t x_64; lean_object* x_65; lean_object* x_66; uint8_t x_142; uint8_t x_143; 
x_62 = lean_ctor_get(x_19, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_19, 1);
lean_inc(x_63);
x_64 = lean_ctor_get_uint64(x_19, sizeof(void*)*3);
x_65 = l_Lean_Expr_headBeta(x_63);
x_142 = (uint8_t)((x_64 << 24) >> 61);
x_143 = l_Lean_BinderInfo_isInstImplicit(x_142);
if (x_143 == 0)
{
lean_object* x_144; 
x_144 = lean_box(0);
x_66 = x_144;
goto block_141;
}
else
{
uint8_t x_145; 
x_145 = l_Array_isEmpty___rarg(x_2);
if (x_145 == 0)
{
lean_object* x_146; 
x_146 = lean_box(0);
x_66 = x_146;
goto block_141;
}
else
{
lean_object* x_147; 
lean_inc(x_16);
lean_inc(x_65);
x_147 = l_Lean_Meta_synthInstance_x3f(x_65, x_16, x_61);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Lean_Name_append___main(x_59, x_62);
lean_dec(x_59);
x_151 = 2;
lean_inc(x_16);
x_152 = l_Lean_Meta_mkFreshExprMVar(x_65, x_150, x_151, x_16, x_149);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
lean_inc(x_153);
x_155 = l_Lean_mkApp(x_12, x_153);
lean_inc(x_16);
lean_inc(x_1);
x_156 = l___private_Init_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_19, x_153, x_16, x_154);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_unsigned_to_nat(1u);
x_160 = lean_nat_add(x_10, x_159);
lean_dec(x_10);
x_161 = lean_nat_add(x_11, x_159);
lean_dec(x_11);
x_162 = l_Lean_Expr_mvarId_x21(x_153);
lean_dec(x_153);
x_163 = lean_box(0);
x_164 = l_Array_empty___closed__1;
x_165 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_165, 2, x_163);
x_166 = lean_array_push(x_15, x_165);
x_10 = x_160;
x_11 = x_161;
x_12 = x_155;
x_13 = x_157;
x_15 = x_166;
x_17 = x_158;
goto _start;
}
else
{
uint8_t x_168; 
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_168 = !lean_is_exclusive(x_156);
if (x_168 == 0)
{
return x_156;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_156, 0);
x_170 = lean_ctor_get(x_156, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_156);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_59);
x_172 = lean_ctor_get(x_147, 1);
lean_inc(x_172);
lean_dec(x_147);
x_173 = lean_ctor_get(x_148, 0);
lean_inc(x_173);
lean_dec(x_148);
lean_inc(x_173);
x_174 = l_Lean_mkApp(x_12, x_173);
lean_inc(x_16);
lean_inc(x_1);
x_175 = l___private_Init_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_19, x_173, x_16, x_172);
lean_dec(x_173);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_unsigned_to_nat(1u);
x_179 = lean_nat_add(x_10, x_178);
lean_dec(x_10);
x_180 = lean_nat_add(x_11, x_178);
lean_dec(x_11);
x_10 = x_179;
x_11 = x_180;
x_12 = x_174;
x_13 = x_176;
x_17 = x_177;
goto _start;
}
else
{
uint8_t x_182; 
lean_dec(x_174);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_175);
if (x_182 == 0)
{
return x_175;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_175, 0);
x_184 = lean_ctor_get(x_175, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_175);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_147);
if (x_186 == 0)
{
return x_147;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_147, 0);
x_188 = lean_ctor_get(x_147, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_147);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
}
block_141:
{
lean_object* x_67; uint8_t x_68; 
lean_dec(x_66);
lean_inc(x_65);
x_67 = l___private_Init_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_65);
x_68 = lean_nat_dec_lt(x_67, x_6);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_123; uint8_t x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; 
x_69 = lean_nat_sub(x_67, x_6);
lean_dec(x_67);
x_70 = lean_array_get_size(x_4);
x_71 = lean_array_get_size(x_7);
x_72 = lean_nat_sub(x_70, x_71);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_sub(x_72, x_73);
lean_dec(x_72);
x_123 = lean_array_get_size(x_2);
x_124 = lean_nat_dec_lt(x_11, x_123);
lean_dec(x_123);
x_125 = l_Lean_Name_append___main(x_59, x_62);
lean_dec(x_59);
x_126 = 2;
lean_inc(x_16);
x_127 = l_Lean_Meta_mkFreshExprMVar(x_65, x_125, x_126, x_16, x_61);
if (x_124 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_box(0);
x_75 = x_130;
x_76 = x_128;
x_77 = x_129;
goto block_122;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_127, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_dec(x_127);
x_133 = lean_array_fget(x_2, x_11);
x_75 = x_133;
x_76 = x_131;
x_77 = x_132;
goto block_122;
}
block_122:
{
lean_object* x_78; lean_object* x_79; 
lean_inc(x_76);
x_78 = l_Lean_mkApp(x_12, x_76);
lean_inc(x_16);
lean_inc(x_1);
x_79 = l___private_Init_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_19, x_76, x_16, x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Expr_mvarId_x21(x_76);
lean_dec(x_76);
x_83 = l_Lean_Expr_fvarId_x21(x_5);
x_84 = l_Lean_Meta_tryClear(x_82, x_83, x_16, x_81);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = 1;
x_88 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_87, x_85, x_69, x_75, x_16, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_box(0);
x_94 = 0;
x_95 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_94, x_92, x_74, x_93, x_16, x_90);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
lean_inc(x_9);
lean_inc(x_70);
x_100 = l_Nat_foldAux___main___at___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(x_4, x_7, x_71, x_98, x_70, x_70, x_9);
lean_dec(x_70);
lean_dec(x_98);
lean_dec(x_71);
x_101 = lean_nat_add(x_10, x_73);
lean_dec(x_10);
x_102 = lean_nat_add(x_11, x_73);
lean_dec(x_11);
x_103 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_91);
lean_ctor_set(x_103, 2, x_100);
x_104 = lean_array_push(x_15, x_103);
x_10 = x_101;
x_11 = x_102;
x_12 = x_78;
x_13 = x_80;
x_15 = x_104;
x_17 = x_97;
goto _start;
}
else
{
uint8_t x_106; 
lean_dec(x_91);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_95);
if (x_106 == 0)
{
return x_95;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_95, 0);
x_108 = lean_ctor_get(x_95, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_95);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_88);
if (x_110 == 0)
{
return x_88;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_88, 0);
x_112 = lean_ctor_get(x_88, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_88);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_84);
if (x_114 == 0)
{
return x_84;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_84, 0);
x_116 = lean_ctor_get(x_84, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_84);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_79);
if (x_118 == 0)
{
return x_79;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_79, 0);
x_120 = lean_ctor_get(x_79, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_79);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
lean_dec(x_67);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_134 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_135 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_136 = l_Lean_Meta_throwTacticEx___rarg(x_134, x_1, x_135, x_16, x_61);
lean_dec(x_16);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
return x_136;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_136);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_59);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_190 = l_Lean_Meta_isClassQuick___main___closed__1;
x_191 = l_unreachable_x21___rarg(x_190);
x_192 = lean_apply_2(x_191, x_16, x_61);
return x_192;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_202 = !lean_is_exclusive(x_58);
if (x_202 == 0)
{
return x_58;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_58, 0);
x_204 = lean_ctor_get(x_58, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_58);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_12);
lean_ctor_set(x_206, 1, x_19);
x_207 = lean_unsigned_to_nat(0u);
lean_inc(x_16);
lean_inc(x_1);
x_208 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(x_1, x_7, x_7, x_207, x_206, x_16, x_20);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_ctor_get(x_209, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_dec(x_209);
lean_inc(x_5);
x_213 = l_Lean_mkApp(x_211, x_5);
lean_inc(x_16);
lean_inc(x_1);
x_214 = l___private_Init_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_212, x_5, x_16, x_210);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_unsigned_to_nat(1u);
x_218 = lean_nat_add(x_10, x_217);
lean_dec(x_10);
x_219 = lean_array_get_size(x_7);
x_220 = lean_nat_add(x_218, x_219);
lean_dec(x_219);
lean_dec(x_218);
x_221 = 1;
x_10 = x_220;
x_12 = x_213;
x_13 = x_215;
x_14 = x_221;
x_17 = x_216;
goto _start;
}
else
{
uint8_t x_223; 
lean_dec(x_213);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_223 = !lean_is_exclusive(x_214);
if (x_223 == 0)
{
return x_214;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_214, 0);
x_225 = lean_ctor_get(x_214, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_214);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
}
else
{
uint8_t x_227; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_227 = !lean_is_exclusive(x_208);
if (x_227 == 0)
{
return x_208;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_208, 0);
x_229 = lean_ctor_get(x_208, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_208);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
}
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_231 = !lean_is_exclusive(x_18);
if (x_231 == 0)
{
return x_18;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_18, 0);
x_233 = lean_ctor_get(x_18, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_18);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
}
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldAux___main___at___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Nat_foldAux___main___at___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldAux___main___at___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_14);
lean_dec(x_14);
x_19 = l___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_18, x_15, x_16, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_14);
lean_dec(x_14);
x_19 = l___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_18, x_15, x_16, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_5__finalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_Meta_getMVarType(x_1, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Init_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_12);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l_Lean_Meta_inferType(x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_3, 7);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_List_lengthAux___main___rarg(x_18, x_19);
x_21 = lean_ctor_get(x_3, 5);
x_22 = l_List_lengthAux___main___rarg(x_21, x_19);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_22, x_23);
lean_dec(x_22);
x_25 = 0;
x_26 = l_Array_empty___closed__1;
x_27 = l___private_Init_Lean_Meta_Tactic_Induction_4__finalizeAux___main(x_1, x_2, x_3, x_4, x_5, x_14, x_6, x_20, x_7, x_24, x_19, x_8, x_16, x_25, x_26, x_9, x_17);
lean_dec(x_20);
lean_dec(x_14);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Induction_5__finalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_Meta_Tactic_Induction_5__finalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* _init_l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise type is ill-formed");
return x_1;
}
}
lean_object* _init_l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_5, 1);
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_le(x_15, x_14);
lean_dec(x_15);
if (x_16 == 0)
{
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_3);
x_19 = l_Lean_indentExpr(x_18);
x_20 = l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__3;
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_21, x_6, x_7);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
}
uint8_t l_List_elem___main___at_Lean_Meta_induction___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_nat_dec_eq(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is an index in major premise, but it depends on index occurring at position #");
return x_1;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is an index in major premise, but it occurs in previous arguments");
return x_1;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is an index in major premise, but it occurs more than once");
return x_1;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_10, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_56; uint8_t x_75; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_10, x_15);
lean_dec(x_10);
x_17 = lean_nat_sub(x_9, x_16);
x_18 = lean_nat_sub(x_17, x_15);
lean_dec(x_17);
x_19 = l_Lean_Expr_Inhabited;
x_20 = lean_array_get(x_19, x_4, x_18);
x_75 = lean_nat_dec_eq(x_18, x_7);
if (x_75 == 0)
{
uint8_t x_76; 
x_76 = lean_expr_eqv(x_20, x_8);
if (x_76 == 0)
{
x_56 = x_12;
goto block_74;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_5);
x_77 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_77, 0, x_8);
x_78 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_79 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__9;
x_81 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_3);
x_83 = l_Lean_indentExpr(x_82);
x_84 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_84, x_11, x_12);
lean_dec(x_11);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
return x_85;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_85);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
x_56 = x_12;
goto block_74;
}
block_55:
{
uint8_t x_22; 
x_22 = lean_nat_dec_lt(x_7, x_18);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_18);
x_10 = x_16;
x_12 = x_21;
goto _start;
}
else
{
uint8_t x_24; 
x_24 = l_List_elem___main___at_Lean_Meta_induction___spec__2(x_18, x_6);
if (x_24 == 0)
{
lean_dec(x_20);
lean_dec(x_18);
x_10 = x_16;
x_12 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
x_26 = l_Lean_Expr_isFVar(x_20);
if (x_26 == 0)
{
lean_dec(x_20);
lean_dec(x_18);
x_10 = x_16;
x_12 = x_21;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_Expr_fvarId_x21(x_8);
lean_inc(x_11);
x_29 = l_Lean_Meta_getLocalDecl(x_28, x_11, x_21);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Expr_fvarId_x21(x_20);
lean_dec(x_20);
lean_inc(x_5);
x_33 = l_Lean_MetavarContext_localDeclDependsOn(x_5, x_30, x_32);
lean_dec(x_32);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_dec(x_18);
x_10 = x_16;
x_12 = x_31;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_3);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_8);
x_37 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__3;
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_nat_add(x_18, x_15);
lean_dec(x_18);
x_42 = l_Nat_repr(x_41);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_45, x_11, x_31);
lean_dec(x_11);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
return x_46;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_46);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_29);
if (x_51 == 0)
{
return x_29;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_29, 0);
x_53 = lean_ctor_get(x_29, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_29);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
block_74:
{
uint8_t x_57; 
x_57 = lean_nat_dec_lt(x_18, x_7);
if (x_57 == 0)
{
x_21 = x_56;
goto block_55;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l_Lean_Expr_fvarId_x21(x_8);
lean_inc(x_20);
lean_inc(x_5);
x_59 = l_Lean_MetavarContext_exprDependsOn(x_5, x_20, x_58);
lean_dec(x_58);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
x_21 = x_56;
goto block_55;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_5);
x_61 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_61, 0, x_8);
x_62 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_63 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__6;
x_65 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_3);
x_67 = l_Lean_indentExpr(x_66);
x_68 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_68, x_11, x_56);
lean_dec(x_11);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
return x_69;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_69);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_12);
return x_91;
}
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise type index ");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" is not variable ");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_8);
x_12 = lean_nat_dec_lt(x_7, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_50; 
x_14 = lean_array_fget(x_8, x_7);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fset(x_8, x_7, x_15);
x_17 = x_14;
x_18 = lean_array_get_size(x_4);
x_50 = lean_nat_dec_le(x_18, x_17);
if (x_50 == 0)
{
x_19 = x_10;
goto block_49;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_5);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_3);
x_52 = l_Lean_indentExpr(x_51);
x_53 = l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__3;
x_54 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_54, x_9, x_10);
lean_dec(x_9);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_55);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
block_49:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_35; 
x_20 = l_Lean_Expr_Inhabited;
x_21 = lean_array_get(x_20, x_4, x_17);
x_35 = l_Lean_Expr_isFVar(x_21);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_5);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_21);
x_37 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__3;
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__6;
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_3);
x_42 = l_Lean_indentExpr(x_41);
x_43 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_43, x_9, x_19);
lean_dec(x_9);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
x_22 = x_19;
goto block_34;
}
block_34:
{
lean_object* x_23; 
lean_inc(x_9);
lean_inc(x_18);
lean_inc(x_21);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_21, x_18, x_18, x_9, x_22);
lean_dec(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_7, x_25);
x_27 = x_21;
x_28 = lean_array_fset(x_16, x_7, x_27);
lean_dec(x_7);
x_7 = x_26;
x_8 = x_28;
x_10 = x_24;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_10 = l_Lean_Name_inhabited;
x_11 = lean_array_get(x_10, x_2, x_4);
x_12 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_5, x_9, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_4 = x_14;
x_5 = x_12;
goto _start;
}
}
}
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_6, 1);
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_dec(x_14);
lean_inc(x_3);
x_15 = lean_array_push(x_13, x_3);
x_16 = 1;
x_17 = lean_box(x_16);
lean_ctor_set(x_5, 1, x_17);
lean_ctor_set(x_5, 0, x_15);
x_6 = x_12;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
lean_dec(x_5);
lean_inc(x_3);
x_21 = lean_array_push(x_20, x_3);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_5 = x_24;
x_6 = x_19;
goto _start;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_6, 1);
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_array_get_size(x_4);
x_32 = lean_nat_dec_le(x_31, x_30);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lean_Level_Inhabited;
x_34 = lean_array_get(x_33, x_4, x_30);
x_35 = lean_array_push(x_28, x_34);
lean_ctor_set(x_5, 0, x_35);
x_6 = x_27;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_free_object(x_5);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_3);
x_37 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_38 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_37, x_7, x_8);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_6, 1);
x_44 = lean_ctor_get(x_5, 0);
x_45 = lean_ctor_get(x_5, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_5);
x_46 = lean_ctor_get(x_10, 0);
x_47 = lean_array_get_size(x_4);
x_48 = lean_nat_dec_le(x_47, x_46);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = l_Lean_Level_Inhabited;
x_50 = lean_array_get(x_49, x_4, x_46);
x_51 = lean_array_push(x_44, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
x_5 = x_52;
x_6 = x_43;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_3);
x_54 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_55 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_54, x_7, x_8);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise is not of the form (C ...)");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("recursor '");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' can only eliminate into Prop");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
switch (lean_obj_tag(x_14)) {
case 4:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_List_redLength___main___rarg(x_19);
x_21 = lean_mk_empty_array_with_capacity(x_20);
lean_dec(x_20);
x_22 = l_List_toArrayAux___main___rarg(x_19, x_21);
x_23 = lean_ctor_get(x_4, 2);
x_24 = l___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_inc(x_13);
lean_inc(x_8);
lean_inc(x_3);
x_25 = l_List_foldlM___main___at_Lean_Meta_induction___spec__6(x_3, x_8, x_13, x_22, x_24, x_23, x_17, x_18);
lean_dec(x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_31 = l_Lean_Level_isZero(x_13);
lean_dec(x_13);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_32 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_32, 0, x_1);
x_33 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__9;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_36, x_17, x_29);
lean_dec(x_17);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_3);
x_42 = l_Array_toList___rarg(x_30);
lean_dec(x_30);
x_43 = l_Lean_mkConst(x_1, x_42);
lean_inc(x_17);
lean_inc(x_8);
x_44 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_8, x_15, x_5, x_43, x_17, x_29);
lean_dec(x_15);
if (lean_obj_tag(x_44) == 0)
{
if (x_6 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_17);
lean_inc(x_10);
x_47 = l_Lean_Meta_mkLambda(x_10, x_12, x_17, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_mkApp(x_45, x_48);
x_51 = l___private_Init_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_50, x_17, x_49);
lean_dec(x_10);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_45);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_47);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_44, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_44, 1);
lean_inc(x_57);
lean_dec(x_44);
x_58 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_11);
x_59 = lean_array_push(x_58, x_11);
lean_inc(x_17);
x_60 = l_Lean_Meta_mkLambda(x_59, x_12, x_17, x_57);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_17);
lean_inc(x_10);
x_63 = l_Lean_Meta_mkLambda(x_10, x_61, x_17, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_mkApp(x_56, x_64);
x_67 = l___private_Init_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_66, x_17, x_65);
lean_dec(x_10);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_56);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
return x_63;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_63, 0);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_63);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_56);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_72 = !lean_is_exclusive(x_60);
if (x_72 == 0)
{
return x_60;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_60, 0);
x_74 = lean_ctor_get(x_60, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_60);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_76 = !lean_is_exclusive(x_44);
if (x_76 == 0)
{
return x_44;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_44, 0);
x_78 = lean_ctor_get(x_44, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_44);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_13);
lean_dec(x_3);
x_80 = lean_ctor_get(x_25, 1);
lean_inc(x_80);
lean_dec(x_25);
x_81 = lean_ctor_get(x_26, 0);
lean_inc(x_81);
lean_dec(x_26);
x_82 = l_Array_toList___rarg(x_81);
lean_dec(x_81);
x_83 = l_Lean_mkConst(x_1, x_82);
lean_inc(x_17);
lean_inc(x_8);
x_84 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_8, x_15, x_5, x_83, x_17, x_80);
lean_dec(x_15);
if (lean_obj_tag(x_84) == 0)
{
if (x_6 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_17);
lean_inc(x_10);
x_87 = l_Lean_Meta_mkLambda(x_10, x_12, x_17, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_mkApp(x_85, x_88);
x_91 = l___private_Init_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_90, x_17, x_89);
lean_dec(x_10);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec(x_85);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
return x_87;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_87, 0);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_87);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_84, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_84, 1);
lean_inc(x_97);
lean_dec(x_84);
x_98 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_11);
x_99 = lean_array_push(x_98, x_11);
lean_inc(x_17);
x_100 = l_Lean_Meta_mkLambda(x_99, x_12, x_17, x_97);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_17);
lean_inc(x_10);
x_103 = l_Lean_Meta_mkLambda(x_10, x_101, x_17, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_mkApp(x_96, x_104);
x_107 = l___private_Init_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_106, x_17, x_105);
lean_dec(x_10);
return x_107;
}
else
{
uint8_t x_108; 
lean_dec(x_96);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_108 = !lean_is_exclusive(x_103);
if (x_108 == 0)
{
return x_103;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_103, 0);
x_110 = lean_ctor_get(x_103, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_103);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_96);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_112 = !lean_is_exclusive(x_100);
if (x_112 == 0)
{
return x_100;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_100, 0);
x_114 = lean_ctor_get(x_100, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_100);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_116 = !lean_is_exclusive(x_84);
if (x_116 == 0)
{
return x_84;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_84, 0);
x_118 = lean_ctor_get(x_84, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_84);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_25);
if (x_120 == 0)
{
return x_25;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_25, 0);
x_122 = lean_ctor_get(x_25, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_25);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
case 5:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_14, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_14, 1);
lean_inc(x_125);
lean_dec(x_14);
x_126 = lean_array_set(x_15, x_16, x_125);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_nat_sub(x_16, x_127);
lean_dec(x_16);
x_14 = x_124;
x_15 = x_126;
x_16 = x_128;
goto _start;
}
default: 
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_130 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__3;
x_131 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_130, x_17, x_18);
lean_dec(x_17);
return x_131;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
x_17 = l_Lean_Meta_getLevel(x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_15);
x_20 = l_Lean_Meta_getLocalDecl(x_1, x_15, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_LocalDecl_type(x_21);
lean_dec(x_21);
lean_inc(x_15);
x_24 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfUntil___spec__2(x_2, x_23, x_15, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Expr_getAppNumArgsAux___main(x_25, x_27);
x_29 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_28);
x_30 = lean_mk_array(x_28, x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_sub(x_28, x_31);
lean_dec(x_28);
x_33 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_18, x_25, x_30, x_32, x_15, x_26);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_24);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_20);
if (x_38 == 0)
{
return x_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_20, 0);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_20);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_17);
if (x_42 == 0)
{
return x_17;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_17, 0);
x_44 = lean_ctor_get(x_17, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_17);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not support dependent elimination, but conclusion depends on major premise");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_9);
x_14 = lean_ctor_get(x_6, 5);
lean_inc(x_14);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_15 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_14, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 6);
lean_inc(x_18);
x_19 = l_List_redLength___main___rarg(x_18);
x_20 = lean_mk_empty_array_with_capacity(x_19);
lean_dec(x_19);
lean_inc(x_18);
x_21 = l_List_toArrayAux___main___rarg(x_18, x_20);
x_22 = x_21;
x_23 = lean_unsigned_to_nat(0u);
lean_inc(x_17);
lean_inc(x_5);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_5);
lean_closure_set(x_24, 2, x_8);
lean_closure_set(x_24, 3, x_10);
lean_closure_set(x_24, 4, x_17);
lean_closure_set(x_24, 5, x_18);
lean_closure_set(x_24, 6, x_23);
lean_closure_set(x_24, 7, x_22);
x_25 = x_24;
lean_inc(x_12);
x_26 = lean_apply_2(x_25, x_12, x_16);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_1);
x_29 = l_Lean_Meta_getMVarType(x_1, x_12, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_32 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = l_Lean_MetavarContext_exprDependsOn(x_17, x_30, x_2);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
x_33 = x_31;
goto block_89;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_92 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_92, 0, x_3);
x_93 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_94 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_96 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_96, x_12, x_31);
lean_dec(x_12);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
return x_97;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_97);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_dec(x_30);
lean_dec(x_17);
x_33 = x_31;
goto block_89;
}
block_89:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
lean_inc(x_27);
x_34 = x_27;
x_35 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_23, x_34);
x_36 = x_35;
x_37 = lean_array_push(x_36, x_2);
x_38 = 1;
x_39 = l_Lean_Meta_revert(x_1, x_37, x_38, x_12, x_33);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_array_get_size(x_27);
x_45 = lean_box(0);
x_46 = 0;
x_47 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_46, x_43, x_44, x_45, x_12, x_41);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l_Lean_Meta_intro1(x_51, x_46, x_12, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_box(0);
x_58 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_27, x_50, x_27, x_23, x_57);
lean_dec(x_27);
x_59 = x_50;
x_60 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_23, x_59);
x_61 = x_60;
lean_inc(x_55);
x_62 = l_Lean_mkFVar(x_55);
lean_inc(x_56);
x_63 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_63, 0, x_56);
x_64 = lean_box(x_32);
lean_inc(x_56);
x_65 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_65, 0, x_55);
lean_closure_set(x_65, 1, x_7);
lean_closure_set(x_65, 2, x_3);
lean_closure_set(x_65, 3, x_4);
lean_closure_set(x_65, 4, x_5);
lean_closure_set(x_65, 5, x_6);
lean_closure_set(x_65, 6, x_14);
lean_closure_set(x_65, 7, x_64);
lean_closure_set(x_65, 8, x_42);
lean_closure_set(x_65, 9, x_56);
lean_closure_set(x_65, 10, x_58);
lean_closure_set(x_65, 11, x_61);
lean_closure_set(x_65, 12, x_62);
x_66 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_66, 0, x_63);
lean_closure_set(x_66, 1, x_65);
x_67 = l_Lean_Meta_getMVarDecl(x_56, x_12, x_54);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 4);
lean_inc(x_71);
lean_dec(x_68);
x_72 = l_Lean_Meta_withLocalContext___rarg(x_70, x_71, x_66, x_12, x_69);
lean_dec(x_12);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_66);
lean_dec(x_12);
x_73 = !lean_is_exclusive(x_67);
if (x_73 == 0)
{
return x_67;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_67, 0);
x_75 = lean_ctor_get(x_67, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_67);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_50);
lean_dec(x_42);
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_52);
if (x_77 == 0)
{
return x_52;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_52, 0);
x_79 = lean_ctor_get(x_52, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_52);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_42);
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_47);
if (x_81 == 0)
{
return x_47;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_47, 0);
x_83 = lean_ctor_get(x_47, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_47);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_39);
if (x_85 == 0)
{
return x_39;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_39, 0);
x_87 = lean_ctor_get(x_39, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_39);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_29);
if (x_102 == 0)
{
return x_29;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_29, 0);
x_104 = lean_ctor_get(x_29, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_29);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_26);
if (x_106 == 0)
{
return x_26;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_26, 0);
x_108 = lean_ctor_get(x_26, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_26);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_15);
if (x_110 == 0)
{
return x_15;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_15, 0);
x_112 = lean_ctor_get(x_15, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_15);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
case 1:
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_11);
lean_dec(x_9);
x_114 = lean_ctor_get(x_6, 5);
lean_inc(x_114);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_115 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_114, x_12, x_13);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_6, 6);
lean_inc(x_118);
x_119 = l_List_redLength___main___rarg(x_118);
x_120 = lean_mk_empty_array_with_capacity(x_119);
lean_dec(x_119);
lean_inc(x_118);
x_121 = l_List_toArrayAux___main___rarg(x_118, x_120);
x_122 = x_121;
x_123 = lean_unsigned_to_nat(0u);
lean_inc(x_117);
lean_inc(x_5);
lean_inc(x_1);
x_124 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_124, 0, x_1);
lean_closure_set(x_124, 1, x_5);
lean_closure_set(x_124, 2, x_8);
lean_closure_set(x_124, 3, x_10);
lean_closure_set(x_124, 4, x_117);
lean_closure_set(x_124, 5, x_118);
lean_closure_set(x_124, 6, x_123);
lean_closure_set(x_124, 7, x_122);
x_125 = x_124;
lean_inc(x_12);
x_126 = lean_apply_2(x_125, x_12, x_116);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
lean_inc(x_1);
x_129 = l_Lean_Meta_getMVarType(x_1, x_12, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_132 == 0)
{
lean_object* x_190; uint8_t x_191; 
x_190 = l_Lean_MetavarContext_exprDependsOn(x_117, x_130, x_2);
x_191 = lean_unbox(x_190);
lean_dec(x_190);
if (x_191 == 0)
{
x_133 = x_131;
goto block_189;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
lean_dec(x_127);
lean_dec(x_114);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_192 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_192, 0, x_3);
x_193 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_194 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_196 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_197 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_196, x_12, x_131);
lean_dec(x_12);
x_198 = !lean_is_exclusive(x_197);
if (x_198 == 0)
{
return x_197;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_197, 0);
x_200 = lean_ctor_get(x_197, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_197);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
lean_dec(x_130);
lean_dec(x_117);
x_133 = x_131;
goto block_189;
}
block_189:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; 
lean_inc(x_127);
x_134 = x_127;
x_135 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_123, x_134);
x_136 = x_135;
x_137 = lean_array_push(x_136, x_2);
x_138 = 1;
x_139 = l_Lean_Meta_revert(x_1, x_137, x_138, x_12, x_133);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_array_get_size(x_127);
x_145 = lean_box(0);
x_146 = 0;
x_147 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_146, x_143, x_144, x_145, x_12, x_141);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_ctor_get(x_148, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
lean_dec(x_148);
x_152 = l_Lean_Meta_intro1(x_151, x_146, x_12, x_149);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
x_157 = lean_box(0);
x_158 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_127, x_150, x_127, x_123, x_157);
lean_dec(x_127);
x_159 = x_150;
x_160 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_123, x_159);
x_161 = x_160;
lean_inc(x_155);
x_162 = l_Lean_mkFVar(x_155);
lean_inc(x_156);
x_163 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_163, 0, x_156);
x_164 = lean_box(x_132);
lean_inc(x_156);
x_165 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_165, 0, x_155);
lean_closure_set(x_165, 1, x_7);
lean_closure_set(x_165, 2, x_3);
lean_closure_set(x_165, 3, x_4);
lean_closure_set(x_165, 4, x_5);
lean_closure_set(x_165, 5, x_6);
lean_closure_set(x_165, 6, x_114);
lean_closure_set(x_165, 7, x_164);
lean_closure_set(x_165, 8, x_142);
lean_closure_set(x_165, 9, x_156);
lean_closure_set(x_165, 10, x_158);
lean_closure_set(x_165, 11, x_161);
lean_closure_set(x_165, 12, x_162);
x_166 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_166, 0, x_163);
lean_closure_set(x_166, 1, x_165);
x_167 = l_Lean_Meta_getMVarDecl(x_156, x_12, x_154);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 4);
lean_inc(x_171);
lean_dec(x_168);
x_172 = l_Lean_Meta_withLocalContext___rarg(x_170, x_171, x_166, x_12, x_169);
lean_dec(x_12);
return x_172;
}
else
{
uint8_t x_173; 
lean_dec(x_166);
lean_dec(x_12);
x_173 = !lean_is_exclusive(x_167);
if (x_173 == 0)
{
return x_167;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_167, 0);
x_175 = lean_ctor_get(x_167, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_167);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_150);
lean_dec(x_142);
lean_dec(x_127);
lean_dec(x_114);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_177 = !lean_is_exclusive(x_152);
if (x_177 == 0)
{
return x_152;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_152, 0);
x_179 = lean_ctor_get(x_152, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_152);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_142);
lean_dec(x_127);
lean_dec(x_114);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_181 = !lean_is_exclusive(x_147);
if (x_181 == 0)
{
return x_147;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_147, 0);
x_183 = lean_ctor_get(x_147, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_147);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_127);
lean_dec(x_114);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_185 = !lean_is_exclusive(x_139);
if (x_185 == 0)
{
return x_139;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_139, 0);
x_187 = lean_ctor_get(x_139, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_139);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_127);
lean_dec(x_117);
lean_dec(x_114);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_202 = !lean_is_exclusive(x_129);
if (x_202 == 0)
{
return x_129;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_129, 0);
x_204 = lean_ctor_get(x_129, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_129);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
uint8_t x_206; 
lean_dec(x_117);
lean_dec(x_114);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_206 = !lean_is_exclusive(x_126);
if (x_206 == 0)
{
return x_126;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_126, 0);
x_208 = lean_ctor_get(x_126, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_126);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_114);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_210 = !lean_is_exclusive(x_115);
if (x_210 == 0)
{
return x_115;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_115, 0);
x_212 = lean_ctor_get(x_115, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_115);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
case 2:
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_11);
lean_dec(x_9);
x_214 = lean_ctor_get(x_6, 5);
lean_inc(x_214);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_215 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_214, x_12, x_13);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_6, 6);
lean_inc(x_218);
x_219 = l_List_redLength___main___rarg(x_218);
x_220 = lean_mk_empty_array_with_capacity(x_219);
lean_dec(x_219);
lean_inc(x_218);
x_221 = l_List_toArrayAux___main___rarg(x_218, x_220);
x_222 = x_221;
x_223 = lean_unsigned_to_nat(0u);
lean_inc(x_217);
lean_inc(x_5);
lean_inc(x_1);
x_224 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_224, 0, x_1);
lean_closure_set(x_224, 1, x_5);
lean_closure_set(x_224, 2, x_8);
lean_closure_set(x_224, 3, x_10);
lean_closure_set(x_224, 4, x_217);
lean_closure_set(x_224, 5, x_218);
lean_closure_set(x_224, 6, x_223);
lean_closure_set(x_224, 7, x_222);
x_225 = x_224;
lean_inc(x_12);
x_226 = lean_apply_2(x_225, x_12, x_216);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
lean_inc(x_1);
x_229 = l_Lean_Meta_getMVarType(x_1, x_12, x_228);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_232 == 0)
{
lean_object* x_290; uint8_t x_291; 
x_290 = l_Lean_MetavarContext_exprDependsOn(x_217, x_230, x_2);
x_291 = lean_unbox(x_290);
lean_dec(x_290);
if (x_291 == 0)
{
x_233 = x_231;
goto block_289;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
lean_dec(x_227);
lean_dec(x_214);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_292 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_292, 0, x_3);
x_293 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_294 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_292);
x_295 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_296 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
x_297 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_296, x_12, x_231);
lean_dec(x_12);
x_298 = !lean_is_exclusive(x_297);
if (x_298 == 0)
{
return x_297;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_297, 0);
x_300 = lean_ctor_get(x_297, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_297);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
else
{
lean_dec(x_230);
lean_dec(x_217);
x_233 = x_231;
goto block_289;
}
block_289:
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; 
lean_inc(x_227);
x_234 = x_227;
x_235 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_223, x_234);
x_236 = x_235;
x_237 = lean_array_push(x_236, x_2);
x_238 = 1;
x_239 = l_Lean_Meta_revert(x_1, x_237, x_238, x_12, x_233);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_ctor_get(x_240, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_240, 1);
lean_inc(x_243);
lean_dec(x_240);
x_244 = lean_array_get_size(x_227);
x_245 = lean_box(0);
x_246 = 0;
x_247 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_246, x_243, x_244, x_245, x_12, x_241);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_ctor_get(x_248, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_248, 1);
lean_inc(x_251);
lean_dec(x_248);
x_252 = l_Lean_Meta_intro1(x_251, x_246, x_12, x_249);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = lean_ctor_get(x_253, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_253, 1);
lean_inc(x_256);
lean_dec(x_253);
x_257 = lean_box(0);
x_258 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_227, x_250, x_227, x_223, x_257);
lean_dec(x_227);
x_259 = x_250;
x_260 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_223, x_259);
x_261 = x_260;
lean_inc(x_255);
x_262 = l_Lean_mkFVar(x_255);
lean_inc(x_256);
x_263 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_263, 0, x_256);
x_264 = lean_box(x_232);
lean_inc(x_256);
x_265 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_265, 0, x_255);
lean_closure_set(x_265, 1, x_7);
lean_closure_set(x_265, 2, x_3);
lean_closure_set(x_265, 3, x_4);
lean_closure_set(x_265, 4, x_5);
lean_closure_set(x_265, 5, x_6);
lean_closure_set(x_265, 6, x_214);
lean_closure_set(x_265, 7, x_264);
lean_closure_set(x_265, 8, x_242);
lean_closure_set(x_265, 9, x_256);
lean_closure_set(x_265, 10, x_258);
lean_closure_set(x_265, 11, x_261);
lean_closure_set(x_265, 12, x_262);
x_266 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_266, 0, x_263);
lean_closure_set(x_266, 1, x_265);
x_267 = l_Lean_Meta_getMVarDecl(x_256, x_12, x_254);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_268, 4);
lean_inc(x_271);
lean_dec(x_268);
x_272 = l_Lean_Meta_withLocalContext___rarg(x_270, x_271, x_266, x_12, x_269);
lean_dec(x_12);
return x_272;
}
else
{
uint8_t x_273; 
lean_dec(x_266);
lean_dec(x_12);
x_273 = !lean_is_exclusive(x_267);
if (x_273 == 0)
{
return x_267;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_267, 0);
x_275 = lean_ctor_get(x_267, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_267);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
else
{
uint8_t x_277; 
lean_dec(x_250);
lean_dec(x_242);
lean_dec(x_227);
lean_dec(x_214);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_277 = !lean_is_exclusive(x_252);
if (x_277 == 0)
{
return x_252;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_252, 0);
x_279 = lean_ctor_get(x_252, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_252);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
return x_280;
}
}
}
else
{
uint8_t x_281; 
lean_dec(x_242);
lean_dec(x_227);
lean_dec(x_214);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_281 = !lean_is_exclusive(x_247);
if (x_281 == 0)
{
return x_247;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_247, 0);
x_283 = lean_ctor_get(x_247, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_247);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
else
{
uint8_t x_285; 
lean_dec(x_227);
lean_dec(x_214);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_285 = !lean_is_exclusive(x_239);
if (x_285 == 0)
{
return x_239;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_239, 0);
x_287 = lean_ctor_get(x_239, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_239);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
}
}
else
{
uint8_t x_302; 
lean_dec(x_227);
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_302 = !lean_is_exclusive(x_229);
if (x_302 == 0)
{
return x_229;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_229, 0);
x_304 = lean_ctor_get(x_229, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_229);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_217);
lean_dec(x_214);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_306 = !lean_is_exclusive(x_226);
if (x_306 == 0)
{
return x_226;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_226, 0);
x_308 = lean_ctor_get(x_226, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_226);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
else
{
uint8_t x_310; 
lean_dec(x_214);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_310 = !lean_is_exclusive(x_215);
if (x_310 == 0)
{
return x_215;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_215, 0);
x_312 = lean_ctor_get(x_215, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_215);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
case 3:
{
lean_object* x_314; lean_object* x_315; 
lean_dec(x_11);
lean_dec(x_9);
x_314 = lean_ctor_get(x_6, 5);
lean_inc(x_314);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_315 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_314, x_12, x_13);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
lean_dec(x_315);
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
x_318 = lean_ctor_get(x_6, 6);
lean_inc(x_318);
x_319 = l_List_redLength___main___rarg(x_318);
x_320 = lean_mk_empty_array_with_capacity(x_319);
lean_dec(x_319);
lean_inc(x_318);
x_321 = l_List_toArrayAux___main___rarg(x_318, x_320);
x_322 = x_321;
x_323 = lean_unsigned_to_nat(0u);
lean_inc(x_317);
lean_inc(x_5);
lean_inc(x_1);
x_324 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_324, 0, x_1);
lean_closure_set(x_324, 1, x_5);
lean_closure_set(x_324, 2, x_8);
lean_closure_set(x_324, 3, x_10);
lean_closure_set(x_324, 4, x_317);
lean_closure_set(x_324, 5, x_318);
lean_closure_set(x_324, 6, x_323);
lean_closure_set(x_324, 7, x_322);
x_325 = x_324;
lean_inc(x_12);
x_326 = lean_apply_2(x_325, x_12, x_316);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
lean_inc(x_1);
x_329 = l_Lean_Meta_getMVarType(x_1, x_12, x_328);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec(x_329);
x_332 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_332 == 0)
{
lean_object* x_390; uint8_t x_391; 
x_390 = l_Lean_MetavarContext_exprDependsOn(x_317, x_330, x_2);
x_391 = lean_unbox(x_390);
lean_dec(x_390);
if (x_391 == 0)
{
x_333 = x_331;
goto block_389;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
lean_dec(x_327);
lean_dec(x_314);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_392 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_392, 0, x_3);
x_393 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_394 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_392);
x_395 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_396 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
x_397 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_396, x_12, x_331);
lean_dec(x_12);
x_398 = !lean_is_exclusive(x_397);
if (x_398 == 0)
{
return x_397;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_397, 0);
x_400 = lean_ctor_get(x_397, 1);
lean_inc(x_400);
lean_inc(x_399);
lean_dec(x_397);
x_401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_400);
return x_401;
}
}
}
else
{
lean_dec(x_330);
lean_dec(x_317);
x_333 = x_331;
goto block_389;
}
block_389:
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; lean_object* x_339; 
lean_inc(x_327);
x_334 = x_327;
x_335 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_323, x_334);
x_336 = x_335;
x_337 = lean_array_push(x_336, x_2);
x_338 = 1;
x_339 = l_Lean_Meta_revert(x_1, x_337, x_338, x_12, x_333);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec(x_339);
x_342 = lean_ctor_get(x_340, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_340, 1);
lean_inc(x_343);
lean_dec(x_340);
x_344 = lean_array_get_size(x_327);
x_345 = lean_box(0);
x_346 = 0;
x_347 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_346, x_343, x_344, x_345, x_12, x_341);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_347, 1);
lean_inc(x_349);
lean_dec(x_347);
x_350 = lean_ctor_get(x_348, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_348, 1);
lean_inc(x_351);
lean_dec(x_348);
x_352 = l_Lean_Meta_intro1(x_351, x_346, x_12, x_349);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_355 = lean_ctor_get(x_353, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_353, 1);
lean_inc(x_356);
lean_dec(x_353);
x_357 = lean_box(0);
x_358 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_327, x_350, x_327, x_323, x_357);
lean_dec(x_327);
x_359 = x_350;
x_360 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_323, x_359);
x_361 = x_360;
lean_inc(x_355);
x_362 = l_Lean_mkFVar(x_355);
lean_inc(x_356);
x_363 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_363, 0, x_356);
x_364 = lean_box(x_332);
lean_inc(x_356);
x_365 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_365, 0, x_355);
lean_closure_set(x_365, 1, x_7);
lean_closure_set(x_365, 2, x_3);
lean_closure_set(x_365, 3, x_4);
lean_closure_set(x_365, 4, x_5);
lean_closure_set(x_365, 5, x_6);
lean_closure_set(x_365, 6, x_314);
lean_closure_set(x_365, 7, x_364);
lean_closure_set(x_365, 8, x_342);
lean_closure_set(x_365, 9, x_356);
lean_closure_set(x_365, 10, x_358);
lean_closure_set(x_365, 11, x_361);
lean_closure_set(x_365, 12, x_362);
x_366 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_366, 0, x_363);
lean_closure_set(x_366, 1, x_365);
x_367 = l_Lean_Meta_getMVarDecl(x_356, x_12, x_354);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
x_370 = lean_ctor_get(x_368, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_368, 4);
lean_inc(x_371);
lean_dec(x_368);
x_372 = l_Lean_Meta_withLocalContext___rarg(x_370, x_371, x_366, x_12, x_369);
lean_dec(x_12);
return x_372;
}
else
{
uint8_t x_373; 
lean_dec(x_366);
lean_dec(x_12);
x_373 = !lean_is_exclusive(x_367);
if (x_373 == 0)
{
return x_367;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_367, 0);
x_375 = lean_ctor_get(x_367, 1);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_367);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_375);
return x_376;
}
}
}
else
{
uint8_t x_377; 
lean_dec(x_350);
lean_dec(x_342);
lean_dec(x_327);
lean_dec(x_314);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_377 = !lean_is_exclusive(x_352);
if (x_377 == 0)
{
return x_352;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_352, 0);
x_379 = lean_ctor_get(x_352, 1);
lean_inc(x_379);
lean_inc(x_378);
lean_dec(x_352);
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
return x_380;
}
}
}
else
{
uint8_t x_381; 
lean_dec(x_342);
lean_dec(x_327);
lean_dec(x_314);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_381 = !lean_is_exclusive(x_347);
if (x_381 == 0)
{
return x_347;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_347, 0);
x_383 = lean_ctor_get(x_347, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_347);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
else
{
uint8_t x_385; 
lean_dec(x_327);
lean_dec(x_314);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_385 = !lean_is_exclusive(x_339);
if (x_385 == 0)
{
return x_339;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_339, 0);
x_387 = lean_ctor_get(x_339, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_339);
x_388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
return x_388;
}
}
}
}
else
{
uint8_t x_402; 
lean_dec(x_327);
lean_dec(x_317);
lean_dec(x_314);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_402 = !lean_is_exclusive(x_329);
if (x_402 == 0)
{
return x_329;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_403 = lean_ctor_get(x_329, 0);
x_404 = lean_ctor_get(x_329, 1);
lean_inc(x_404);
lean_inc(x_403);
lean_dec(x_329);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_403);
lean_ctor_set(x_405, 1, x_404);
return x_405;
}
}
}
else
{
uint8_t x_406; 
lean_dec(x_317);
lean_dec(x_314);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_406 = !lean_is_exclusive(x_326);
if (x_406 == 0)
{
return x_326;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_326, 0);
x_408 = lean_ctor_get(x_326, 1);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_326);
x_409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
return x_409;
}
}
}
else
{
uint8_t x_410; 
lean_dec(x_314);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_410 = !lean_is_exclusive(x_315);
if (x_410 == 0)
{
return x_315;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_411 = lean_ctor_get(x_315, 0);
x_412 = lean_ctor_get(x_315, 1);
lean_inc(x_412);
lean_inc(x_411);
lean_dec(x_315);
x_413 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
return x_413;
}
}
}
case 4:
{
lean_object* x_414; lean_object* x_415; 
lean_dec(x_11);
lean_dec(x_9);
x_414 = lean_ctor_get(x_6, 5);
lean_inc(x_414);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_415 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_414, x_12, x_13);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_416 = lean_ctor_get(x_415, 1);
lean_inc(x_416);
lean_dec(x_415);
x_417 = lean_ctor_get(x_416, 1);
lean_inc(x_417);
x_418 = lean_ctor_get(x_6, 6);
lean_inc(x_418);
x_419 = l_List_redLength___main___rarg(x_418);
x_420 = lean_mk_empty_array_with_capacity(x_419);
lean_dec(x_419);
lean_inc(x_418);
x_421 = l_List_toArrayAux___main___rarg(x_418, x_420);
x_422 = x_421;
x_423 = lean_unsigned_to_nat(0u);
lean_inc(x_417);
lean_inc(x_5);
lean_inc(x_1);
x_424 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_424, 0, x_1);
lean_closure_set(x_424, 1, x_5);
lean_closure_set(x_424, 2, x_8);
lean_closure_set(x_424, 3, x_10);
lean_closure_set(x_424, 4, x_417);
lean_closure_set(x_424, 5, x_418);
lean_closure_set(x_424, 6, x_423);
lean_closure_set(x_424, 7, x_422);
x_425 = x_424;
lean_inc(x_12);
x_426 = lean_apply_2(x_425, x_12, x_416);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
lean_inc(x_1);
x_429 = l_Lean_Meta_getMVarType(x_1, x_12, x_428);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; 
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_429, 1);
lean_inc(x_431);
lean_dec(x_429);
x_432 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_432 == 0)
{
lean_object* x_490; uint8_t x_491; 
x_490 = l_Lean_MetavarContext_exprDependsOn(x_417, x_430, x_2);
x_491 = lean_unbox(x_490);
lean_dec(x_490);
if (x_491 == 0)
{
x_433 = x_431;
goto block_489;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; uint8_t x_498; 
lean_dec(x_427);
lean_dec(x_414);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_492 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_492, 0, x_3);
x_493 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_494 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_492);
x_495 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_496 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set(x_496, 1, x_495);
x_497 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_496, x_12, x_431);
lean_dec(x_12);
x_498 = !lean_is_exclusive(x_497);
if (x_498 == 0)
{
return x_497;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_499 = lean_ctor_get(x_497, 0);
x_500 = lean_ctor_get(x_497, 1);
lean_inc(x_500);
lean_inc(x_499);
lean_dec(x_497);
x_501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_500);
return x_501;
}
}
}
else
{
lean_dec(x_430);
lean_dec(x_417);
x_433 = x_431;
goto block_489;
}
block_489:
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; 
lean_inc(x_427);
x_434 = x_427;
x_435 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_423, x_434);
x_436 = x_435;
x_437 = lean_array_push(x_436, x_2);
x_438 = 1;
x_439 = l_Lean_Meta_revert(x_1, x_437, x_438, x_12, x_433);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
x_442 = lean_ctor_get(x_440, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_440, 1);
lean_inc(x_443);
lean_dec(x_440);
x_444 = lean_array_get_size(x_427);
x_445 = lean_box(0);
x_446 = 0;
x_447 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_446, x_443, x_444, x_445, x_12, x_441);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
lean_dec(x_447);
x_450 = lean_ctor_get(x_448, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_448, 1);
lean_inc(x_451);
lean_dec(x_448);
x_452 = l_Lean_Meta_intro1(x_451, x_446, x_12, x_449);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
lean_dec(x_452);
x_455 = lean_ctor_get(x_453, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_453, 1);
lean_inc(x_456);
lean_dec(x_453);
x_457 = lean_box(0);
x_458 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_427, x_450, x_427, x_423, x_457);
lean_dec(x_427);
x_459 = x_450;
x_460 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_423, x_459);
x_461 = x_460;
lean_inc(x_455);
x_462 = l_Lean_mkFVar(x_455);
lean_inc(x_456);
x_463 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_463, 0, x_456);
x_464 = lean_box(x_432);
lean_inc(x_456);
x_465 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_465, 0, x_455);
lean_closure_set(x_465, 1, x_7);
lean_closure_set(x_465, 2, x_3);
lean_closure_set(x_465, 3, x_4);
lean_closure_set(x_465, 4, x_5);
lean_closure_set(x_465, 5, x_6);
lean_closure_set(x_465, 6, x_414);
lean_closure_set(x_465, 7, x_464);
lean_closure_set(x_465, 8, x_442);
lean_closure_set(x_465, 9, x_456);
lean_closure_set(x_465, 10, x_458);
lean_closure_set(x_465, 11, x_461);
lean_closure_set(x_465, 12, x_462);
x_466 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_466, 0, x_463);
lean_closure_set(x_466, 1, x_465);
x_467 = l_Lean_Meta_getMVarDecl(x_456, x_12, x_454);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec(x_467);
x_470 = lean_ctor_get(x_468, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_468, 4);
lean_inc(x_471);
lean_dec(x_468);
x_472 = l_Lean_Meta_withLocalContext___rarg(x_470, x_471, x_466, x_12, x_469);
lean_dec(x_12);
return x_472;
}
else
{
uint8_t x_473; 
lean_dec(x_466);
lean_dec(x_12);
x_473 = !lean_is_exclusive(x_467);
if (x_473 == 0)
{
return x_467;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_474 = lean_ctor_get(x_467, 0);
x_475 = lean_ctor_get(x_467, 1);
lean_inc(x_475);
lean_inc(x_474);
lean_dec(x_467);
x_476 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_476, 0, x_474);
lean_ctor_set(x_476, 1, x_475);
return x_476;
}
}
}
else
{
uint8_t x_477; 
lean_dec(x_450);
lean_dec(x_442);
lean_dec(x_427);
lean_dec(x_414);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_477 = !lean_is_exclusive(x_452);
if (x_477 == 0)
{
return x_452;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_478 = lean_ctor_get(x_452, 0);
x_479 = lean_ctor_get(x_452, 1);
lean_inc(x_479);
lean_inc(x_478);
lean_dec(x_452);
x_480 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_480, 0, x_478);
lean_ctor_set(x_480, 1, x_479);
return x_480;
}
}
}
else
{
uint8_t x_481; 
lean_dec(x_442);
lean_dec(x_427);
lean_dec(x_414);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_481 = !lean_is_exclusive(x_447);
if (x_481 == 0)
{
return x_447;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_447, 0);
x_483 = lean_ctor_get(x_447, 1);
lean_inc(x_483);
lean_inc(x_482);
lean_dec(x_447);
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_483);
return x_484;
}
}
}
else
{
uint8_t x_485; 
lean_dec(x_427);
lean_dec(x_414);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_485 = !lean_is_exclusive(x_439);
if (x_485 == 0)
{
return x_439;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_486 = lean_ctor_get(x_439, 0);
x_487 = lean_ctor_get(x_439, 1);
lean_inc(x_487);
lean_inc(x_486);
lean_dec(x_439);
x_488 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
return x_488;
}
}
}
}
else
{
uint8_t x_502; 
lean_dec(x_427);
lean_dec(x_417);
lean_dec(x_414);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_502 = !lean_is_exclusive(x_429);
if (x_502 == 0)
{
return x_429;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_429, 0);
x_504 = lean_ctor_get(x_429, 1);
lean_inc(x_504);
lean_inc(x_503);
lean_dec(x_429);
x_505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_504);
return x_505;
}
}
}
else
{
uint8_t x_506; 
lean_dec(x_417);
lean_dec(x_414);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_506 = !lean_is_exclusive(x_426);
if (x_506 == 0)
{
return x_426;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_426, 0);
x_508 = lean_ctor_get(x_426, 1);
lean_inc(x_508);
lean_inc(x_507);
lean_dec(x_426);
x_509 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_509, 0, x_507);
lean_ctor_set(x_509, 1, x_508);
return x_509;
}
}
}
else
{
uint8_t x_510; 
lean_dec(x_414);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_510 = !lean_is_exclusive(x_415);
if (x_510 == 0)
{
return x_415;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_511 = lean_ctor_get(x_415, 0);
x_512 = lean_ctor_get(x_415, 1);
lean_inc(x_512);
lean_inc(x_511);
lean_dec(x_415);
x_513 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_513, 0, x_511);
lean_ctor_set(x_513, 1, x_512);
return x_513;
}
}
}
case 5:
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_514 = lean_ctor_get(x_9, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_9, 1);
lean_inc(x_515);
lean_dec(x_9);
x_516 = lean_array_set(x_10, x_11, x_515);
x_517 = lean_unsigned_to_nat(1u);
x_518 = lean_nat_sub(x_11, x_517);
lean_dec(x_11);
x_9 = x_514;
x_10 = x_516;
x_11 = x_518;
goto _start;
}
case 6:
{
lean_object* x_520; lean_object* x_521; 
lean_dec(x_11);
lean_dec(x_9);
x_520 = lean_ctor_get(x_6, 5);
lean_inc(x_520);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_521 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_520, x_12, x_13);
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_522 = lean_ctor_get(x_521, 1);
lean_inc(x_522);
lean_dec(x_521);
x_523 = lean_ctor_get(x_522, 1);
lean_inc(x_523);
x_524 = lean_ctor_get(x_6, 6);
lean_inc(x_524);
x_525 = l_List_redLength___main___rarg(x_524);
x_526 = lean_mk_empty_array_with_capacity(x_525);
lean_dec(x_525);
lean_inc(x_524);
x_527 = l_List_toArrayAux___main___rarg(x_524, x_526);
x_528 = x_527;
x_529 = lean_unsigned_to_nat(0u);
lean_inc(x_523);
lean_inc(x_5);
lean_inc(x_1);
x_530 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_530, 0, x_1);
lean_closure_set(x_530, 1, x_5);
lean_closure_set(x_530, 2, x_8);
lean_closure_set(x_530, 3, x_10);
lean_closure_set(x_530, 4, x_523);
lean_closure_set(x_530, 5, x_524);
lean_closure_set(x_530, 6, x_529);
lean_closure_set(x_530, 7, x_528);
x_531 = x_530;
lean_inc(x_12);
x_532 = lean_apply_2(x_531, x_12, x_522);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_532, 1);
lean_inc(x_534);
lean_dec(x_532);
lean_inc(x_1);
x_535 = l_Lean_Meta_getMVarType(x_1, x_12, x_534);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; uint8_t x_538; lean_object* x_539; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
lean_dec(x_535);
x_538 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_538 == 0)
{
lean_object* x_596; uint8_t x_597; 
x_596 = l_Lean_MetavarContext_exprDependsOn(x_523, x_536, x_2);
x_597 = lean_unbox(x_596);
lean_dec(x_596);
if (x_597 == 0)
{
x_539 = x_537;
goto block_595;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; 
lean_dec(x_533);
lean_dec(x_520);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_598 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_598, 0, x_3);
x_599 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_600 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_600, 0, x_599);
lean_ctor_set(x_600, 1, x_598);
x_601 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_602 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_602, 0, x_600);
lean_ctor_set(x_602, 1, x_601);
x_603 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_602, x_12, x_537);
lean_dec(x_12);
x_604 = !lean_is_exclusive(x_603);
if (x_604 == 0)
{
return x_603;
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_605 = lean_ctor_get(x_603, 0);
x_606 = lean_ctor_get(x_603, 1);
lean_inc(x_606);
lean_inc(x_605);
lean_dec(x_603);
x_607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_607, 0, x_605);
lean_ctor_set(x_607, 1, x_606);
return x_607;
}
}
}
else
{
lean_dec(x_536);
lean_dec(x_523);
x_539 = x_537;
goto block_595;
}
block_595:
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; uint8_t x_544; lean_object* x_545; 
lean_inc(x_533);
x_540 = x_533;
x_541 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_529, x_540);
x_542 = x_541;
x_543 = lean_array_push(x_542, x_2);
x_544 = 1;
x_545 = l_Lean_Meta_revert(x_1, x_543, x_544, x_12, x_539);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; uint8_t x_552; lean_object* x_553; 
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_545, 1);
lean_inc(x_547);
lean_dec(x_545);
x_548 = lean_ctor_get(x_546, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_546, 1);
lean_inc(x_549);
lean_dec(x_546);
x_550 = lean_array_get_size(x_533);
x_551 = lean_box(0);
x_552 = 0;
x_553 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_552, x_549, x_550, x_551, x_12, x_547);
if (lean_obj_tag(x_553) == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_554 = lean_ctor_get(x_553, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_553, 1);
lean_inc(x_555);
lean_dec(x_553);
x_556 = lean_ctor_get(x_554, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_554, 1);
lean_inc(x_557);
lean_dec(x_554);
x_558 = l_Lean_Meta_intro1(x_557, x_552, x_12, x_555);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_558, 1);
lean_inc(x_560);
lean_dec(x_558);
x_561 = lean_ctor_get(x_559, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_559, 1);
lean_inc(x_562);
lean_dec(x_559);
x_563 = lean_box(0);
x_564 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_533, x_556, x_533, x_529, x_563);
lean_dec(x_533);
x_565 = x_556;
x_566 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_529, x_565);
x_567 = x_566;
lean_inc(x_561);
x_568 = l_Lean_mkFVar(x_561);
lean_inc(x_562);
x_569 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_569, 0, x_562);
x_570 = lean_box(x_538);
lean_inc(x_562);
x_571 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_571, 0, x_561);
lean_closure_set(x_571, 1, x_7);
lean_closure_set(x_571, 2, x_3);
lean_closure_set(x_571, 3, x_4);
lean_closure_set(x_571, 4, x_5);
lean_closure_set(x_571, 5, x_6);
lean_closure_set(x_571, 6, x_520);
lean_closure_set(x_571, 7, x_570);
lean_closure_set(x_571, 8, x_548);
lean_closure_set(x_571, 9, x_562);
lean_closure_set(x_571, 10, x_564);
lean_closure_set(x_571, 11, x_567);
lean_closure_set(x_571, 12, x_568);
x_572 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_572, 0, x_569);
lean_closure_set(x_572, 1, x_571);
x_573 = l_Lean_Meta_getMVarDecl(x_562, x_12, x_560);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec(x_573);
x_576 = lean_ctor_get(x_574, 1);
lean_inc(x_576);
x_577 = lean_ctor_get(x_574, 4);
lean_inc(x_577);
lean_dec(x_574);
x_578 = l_Lean_Meta_withLocalContext___rarg(x_576, x_577, x_572, x_12, x_575);
lean_dec(x_12);
return x_578;
}
else
{
uint8_t x_579; 
lean_dec(x_572);
lean_dec(x_12);
x_579 = !lean_is_exclusive(x_573);
if (x_579 == 0)
{
return x_573;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_580 = lean_ctor_get(x_573, 0);
x_581 = lean_ctor_get(x_573, 1);
lean_inc(x_581);
lean_inc(x_580);
lean_dec(x_573);
x_582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_582, 0, x_580);
lean_ctor_set(x_582, 1, x_581);
return x_582;
}
}
}
else
{
uint8_t x_583; 
lean_dec(x_556);
lean_dec(x_548);
lean_dec(x_533);
lean_dec(x_520);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_583 = !lean_is_exclusive(x_558);
if (x_583 == 0)
{
return x_558;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_558, 0);
x_585 = lean_ctor_get(x_558, 1);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_558);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_584);
lean_ctor_set(x_586, 1, x_585);
return x_586;
}
}
}
else
{
uint8_t x_587; 
lean_dec(x_548);
lean_dec(x_533);
lean_dec(x_520);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_587 = !lean_is_exclusive(x_553);
if (x_587 == 0)
{
return x_553;
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_588 = lean_ctor_get(x_553, 0);
x_589 = lean_ctor_get(x_553, 1);
lean_inc(x_589);
lean_inc(x_588);
lean_dec(x_553);
x_590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_590, 0, x_588);
lean_ctor_set(x_590, 1, x_589);
return x_590;
}
}
}
else
{
uint8_t x_591; 
lean_dec(x_533);
lean_dec(x_520);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_591 = !lean_is_exclusive(x_545);
if (x_591 == 0)
{
return x_545;
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_592 = lean_ctor_get(x_545, 0);
x_593 = lean_ctor_get(x_545, 1);
lean_inc(x_593);
lean_inc(x_592);
lean_dec(x_545);
x_594 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_594, 0, x_592);
lean_ctor_set(x_594, 1, x_593);
return x_594;
}
}
}
}
else
{
uint8_t x_608; 
lean_dec(x_533);
lean_dec(x_523);
lean_dec(x_520);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_608 = !lean_is_exclusive(x_535);
if (x_608 == 0)
{
return x_535;
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_609 = lean_ctor_get(x_535, 0);
x_610 = lean_ctor_get(x_535, 1);
lean_inc(x_610);
lean_inc(x_609);
lean_dec(x_535);
x_611 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_611, 0, x_609);
lean_ctor_set(x_611, 1, x_610);
return x_611;
}
}
}
else
{
uint8_t x_612; 
lean_dec(x_523);
lean_dec(x_520);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_612 = !lean_is_exclusive(x_532);
if (x_612 == 0)
{
return x_532;
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = lean_ctor_get(x_532, 0);
x_614 = lean_ctor_get(x_532, 1);
lean_inc(x_614);
lean_inc(x_613);
lean_dec(x_532);
x_615 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_615, 0, x_613);
lean_ctor_set(x_615, 1, x_614);
return x_615;
}
}
}
else
{
uint8_t x_616; 
lean_dec(x_520);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_616 = !lean_is_exclusive(x_521);
if (x_616 == 0)
{
return x_521;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_617 = lean_ctor_get(x_521, 0);
x_618 = lean_ctor_get(x_521, 1);
lean_inc(x_618);
lean_inc(x_617);
lean_dec(x_521);
x_619 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_619, 0, x_617);
lean_ctor_set(x_619, 1, x_618);
return x_619;
}
}
}
case 7:
{
lean_object* x_620; lean_object* x_621; 
lean_dec(x_11);
lean_dec(x_9);
x_620 = lean_ctor_get(x_6, 5);
lean_inc(x_620);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_621 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_620, x_12, x_13);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_622 = lean_ctor_get(x_621, 1);
lean_inc(x_622);
lean_dec(x_621);
x_623 = lean_ctor_get(x_622, 1);
lean_inc(x_623);
x_624 = lean_ctor_get(x_6, 6);
lean_inc(x_624);
x_625 = l_List_redLength___main___rarg(x_624);
x_626 = lean_mk_empty_array_with_capacity(x_625);
lean_dec(x_625);
lean_inc(x_624);
x_627 = l_List_toArrayAux___main___rarg(x_624, x_626);
x_628 = x_627;
x_629 = lean_unsigned_to_nat(0u);
lean_inc(x_623);
lean_inc(x_5);
lean_inc(x_1);
x_630 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_630, 0, x_1);
lean_closure_set(x_630, 1, x_5);
lean_closure_set(x_630, 2, x_8);
lean_closure_set(x_630, 3, x_10);
lean_closure_set(x_630, 4, x_623);
lean_closure_set(x_630, 5, x_624);
lean_closure_set(x_630, 6, x_629);
lean_closure_set(x_630, 7, x_628);
x_631 = x_630;
lean_inc(x_12);
x_632 = lean_apply_2(x_631, x_12, x_622);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
lean_dec(x_632);
lean_inc(x_1);
x_635 = l_Lean_Meta_getMVarType(x_1, x_12, x_634);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; lean_object* x_637; uint8_t x_638; lean_object* x_639; 
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_635, 1);
lean_inc(x_637);
lean_dec(x_635);
x_638 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_638 == 0)
{
lean_object* x_696; uint8_t x_697; 
x_696 = l_Lean_MetavarContext_exprDependsOn(x_623, x_636, x_2);
x_697 = lean_unbox(x_696);
lean_dec(x_696);
if (x_697 == 0)
{
x_639 = x_637;
goto block_695;
}
else
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; uint8_t x_704; 
lean_dec(x_633);
lean_dec(x_620);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_698 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_698, 0, x_3);
x_699 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_700 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_698);
x_701 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_702 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_702, 0, x_700);
lean_ctor_set(x_702, 1, x_701);
x_703 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_702, x_12, x_637);
lean_dec(x_12);
x_704 = !lean_is_exclusive(x_703);
if (x_704 == 0)
{
return x_703;
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_705 = lean_ctor_get(x_703, 0);
x_706 = lean_ctor_get(x_703, 1);
lean_inc(x_706);
lean_inc(x_705);
lean_dec(x_703);
x_707 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_707, 0, x_705);
lean_ctor_set(x_707, 1, x_706);
return x_707;
}
}
}
else
{
lean_dec(x_636);
lean_dec(x_623);
x_639 = x_637;
goto block_695;
}
block_695:
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; uint8_t x_644; lean_object* x_645; 
lean_inc(x_633);
x_640 = x_633;
x_641 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_629, x_640);
x_642 = x_641;
x_643 = lean_array_push(x_642, x_2);
x_644 = 1;
x_645 = l_Lean_Meta_revert(x_1, x_643, x_644, x_12, x_639);
if (lean_obj_tag(x_645) == 0)
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; uint8_t x_652; lean_object* x_653; 
x_646 = lean_ctor_get(x_645, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_645, 1);
lean_inc(x_647);
lean_dec(x_645);
x_648 = lean_ctor_get(x_646, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_646, 1);
lean_inc(x_649);
lean_dec(x_646);
x_650 = lean_array_get_size(x_633);
x_651 = lean_box(0);
x_652 = 0;
x_653 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_652, x_649, x_650, x_651, x_12, x_647);
if (lean_obj_tag(x_653) == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_654 = lean_ctor_get(x_653, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_653, 1);
lean_inc(x_655);
lean_dec(x_653);
x_656 = lean_ctor_get(x_654, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_654, 1);
lean_inc(x_657);
lean_dec(x_654);
x_658 = l_Lean_Meta_intro1(x_657, x_652, x_12, x_655);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_659 = lean_ctor_get(x_658, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_658, 1);
lean_inc(x_660);
lean_dec(x_658);
x_661 = lean_ctor_get(x_659, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_659, 1);
lean_inc(x_662);
lean_dec(x_659);
x_663 = lean_box(0);
x_664 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_633, x_656, x_633, x_629, x_663);
lean_dec(x_633);
x_665 = x_656;
x_666 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_629, x_665);
x_667 = x_666;
lean_inc(x_661);
x_668 = l_Lean_mkFVar(x_661);
lean_inc(x_662);
x_669 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_669, 0, x_662);
x_670 = lean_box(x_638);
lean_inc(x_662);
x_671 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_671, 0, x_661);
lean_closure_set(x_671, 1, x_7);
lean_closure_set(x_671, 2, x_3);
lean_closure_set(x_671, 3, x_4);
lean_closure_set(x_671, 4, x_5);
lean_closure_set(x_671, 5, x_6);
lean_closure_set(x_671, 6, x_620);
lean_closure_set(x_671, 7, x_670);
lean_closure_set(x_671, 8, x_648);
lean_closure_set(x_671, 9, x_662);
lean_closure_set(x_671, 10, x_664);
lean_closure_set(x_671, 11, x_667);
lean_closure_set(x_671, 12, x_668);
x_672 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_672, 0, x_669);
lean_closure_set(x_672, 1, x_671);
x_673 = l_Lean_Meta_getMVarDecl(x_662, x_12, x_660);
if (lean_obj_tag(x_673) == 0)
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_674 = lean_ctor_get(x_673, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_673, 1);
lean_inc(x_675);
lean_dec(x_673);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
x_677 = lean_ctor_get(x_674, 4);
lean_inc(x_677);
lean_dec(x_674);
x_678 = l_Lean_Meta_withLocalContext___rarg(x_676, x_677, x_672, x_12, x_675);
lean_dec(x_12);
return x_678;
}
else
{
uint8_t x_679; 
lean_dec(x_672);
lean_dec(x_12);
x_679 = !lean_is_exclusive(x_673);
if (x_679 == 0)
{
return x_673;
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_680 = lean_ctor_get(x_673, 0);
x_681 = lean_ctor_get(x_673, 1);
lean_inc(x_681);
lean_inc(x_680);
lean_dec(x_673);
x_682 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_682, 0, x_680);
lean_ctor_set(x_682, 1, x_681);
return x_682;
}
}
}
else
{
uint8_t x_683; 
lean_dec(x_656);
lean_dec(x_648);
lean_dec(x_633);
lean_dec(x_620);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_683 = !lean_is_exclusive(x_658);
if (x_683 == 0)
{
return x_658;
}
else
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_684 = lean_ctor_get(x_658, 0);
x_685 = lean_ctor_get(x_658, 1);
lean_inc(x_685);
lean_inc(x_684);
lean_dec(x_658);
x_686 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_686, 0, x_684);
lean_ctor_set(x_686, 1, x_685);
return x_686;
}
}
}
else
{
uint8_t x_687; 
lean_dec(x_648);
lean_dec(x_633);
lean_dec(x_620);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_687 = !lean_is_exclusive(x_653);
if (x_687 == 0)
{
return x_653;
}
else
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_688 = lean_ctor_get(x_653, 0);
x_689 = lean_ctor_get(x_653, 1);
lean_inc(x_689);
lean_inc(x_688);
lean_dec(x_653);
x_690 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_690, 0, x_688);
lean_ctor_set(x_690, 1, x_689);
return x_690;
}
}
}
else
{
uint8_t x_691; 
lean_dec(x_633);
lean_dec(x_620);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_691 = !lean_is_exclusive(x_645);
if (x_691 == 0)
{
return x_645;
}
else
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; 
x_692 = lean_ctor_get(x_645, 0);
x_693 = lean_ctor_get(x_645, 1);
lean_inc(x_693);
lean_inc(x_692);
lean_dec(x_645);
x_694 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_694, 0, x_692);
lean_ctor_set(x_694, 1, x_693);
return x_694;
}
}
}
}
else
{
uint8_t x_708; 
lean_dec(x_633);
lean_dec(x_623);
lean_dec(x_620);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_708 = !lean_is_exclusive(x_635);
if (x_708 == 0)
{
return x_635;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = lean_ctor_get(x_635, 0);
x_710 = lean_ctor_get(x_635, 1);
lean_inc(x_710);
lean_inc(x_709);
lean_dec(x_635);
x_711 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_711, 0, x_709);
lean_ctor_set(x_711, 1, x_710);
return x_711;
}
}
}
else
{
uint8_t x_712; 
lean_dec(x_623);
lean_dec(x_620);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_712 = !lean_is_exclusive(x_632);
if (x_712 == 0)
{
return x_632;
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_713 = lean_ctor_get(x_632, 0);
x_714 = lean_ctor_get(x_632, 1);
lean_inc(x_714);
lean_inc(x_713);
lean_dec(x_632);
x_715 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_715, 0, x_713);
lean_ctor_set(x_715, 1, x_714);
return x_715;
}
}
}
else
{
uint8_t x_716; 
lean_dec(x_620);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_716 = !lean_is_exclusive(x_621);
if (x_716 == 0)
{
return x_621;
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_717 = lean_ctor_get(x_621, 0);
x_718 = lean_ctor_get(x_621, 1);
lean_inc(x_718);
lean_inc(x_717);
lean_dec(x_621);
x_719 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_719, 0, x_717);
lean_ctor_set(x_719, 1, x_718);
return x_719;
}
}
}
case 8:
{
lean_object* x_720; lean_object* x_721; 
lean_dec(x_11);
lean_dec(x_9);
x_720 = lean_ctor_get(x_6, 5);
lean_inc(x_720);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_721 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_720, x_12, x_13);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_722 = lean_ctor_get(x_721, 1);
lean_inc(x_722);
lean_dec(x_721);
x_723 = lean_ctor_get(x_722, 1);
lean_inc(x_723);
x_724 = lean_ctor_get(x_6, 6);
lean_inc(x_724);
x_725 = l_List_redLength___main___rarg(x_724);
x_726 = lean_mk_empty_array_with_capacity(x_725);
lean_dec(x_725);
lean_inc(x_724);
x_727 = l_List_toArrayAux___main___rarg(x_724, x_726);
x_728 = x_727;
x_729 = lean_unsigned_to_nat(0u);
lean_inc(x_723);
lean_inc(x_5);
lean_inc(x_1);
x_730 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_730, 0, x_1);
lean_closure_set(x_730, 1, x_5);
lean_closure_set(x_730, 2, x_8);
lean_closure_set(x_730, 3, x_10);
lean_closure_set(x_730, 4, x_723);
lean_closure_set(x_730, 5, x_724);
lean_closure_set(x_730, 6, x_729);
lean_closure_set(x_730, 7, x_728);
x_731 = x_730;
lean_inc(x_12);
x_732 = lean_apply_2(x_731, x_12, x_722);
if (lean_obj_tag(x_732) == 0)
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; 
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_732, 1);
lean_inc(x_734);
lean_dec(x_732);
lean_inc(x_1);
x_735 = l_Lean_Meta_getMVarType(x_1, x_12, x_734);
if (lean_obj_tag(x_735) == 0)
{
lean_object* x_736; lean_object* x_737; uint8_t x_738; lean_object* x_739; 
x_736 = lean_ctor_get(x_735, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_735, 1);
lean_inc(x_737);
lean_dec(x_735);
x_738 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_738 == 0)
{
lean_object* x_796; uint8_t x_797; 
x_796 = l_Lean_MetavarContext_exprDependsOn(x_723, x_736, x_2);
x_797 = lean_unbox(x_796);
lean_dec(x_796);
if (x_797 == 0)
{
x_739 = x_737;
goto block_795;
}
else
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; uint8_t x_804; 
lean_dec(x_733);
lean_dec(x_720);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_798 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_798, 0, x_3);
x_799 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_800 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_800, 0, x_799);
lean_ctor_set(x_800, 1, x_798);
x_801 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_802 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_802, 0, x_800);
lean_ctor_set(x_802, 1, x_801);
x_803 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_802, x_12, x_737);
lean_dec(x_12);
x_804 = !lean_is_exclusive(x_803);
if (x_804 == 0)
{
return x_803;
}
else
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_805 = lean_ctor_get(x_803, 0);
x_806 = lean_ctor_get(x_803, 1);
lean_inc(x_806);
lean_inc(x_805);
lean_dec(x_803);
x_807 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_807, 0, x_805);
lean_ctor_set(x_807, 1, x_806);
return x_807;
}
}
}
else
{
lean_dec(x_736);
lean_dec(x_723);
x_739 = x_737;
goto block_795;
}
block_795:
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; uint8_t x_744; lean_object* x_745; 
lean_inc(x_733);
x_740 = x_733;
x_741 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_729, x_740);
x_742 = x_741;
x_743 = lean_array_push(x_742, x_2);
x_744 = 1;
x_745 = l_Lean_Meta_revert(x_1, x_743, x_744, x_12, x_739);
if (lean_obj_tag(x_745) == 0)
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; uint8_t x_752; lean_object* x_753; 
x_746 = lean_ctor_get(x_745, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_745, 1);
lean_inc(x_747);
lean_dec(x_745);
x_748 = lean_ctor_get(x_746, 0);
lean_inc(x_748);
x_749 = lean_ctor_get(x_746, 1);
lean_inc(x_749);
lean_dec(x_746);
x_750 = lean_array_get_size(x_733);
x_751 = lean_box(0);
x_752 = 0;
x_753 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_752, x_749, x_750, x_751, x_12, x_747);
if (lean_obj_tag(x_753) == 0)
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_754 = lean_ctor_get(x_753, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_753, 1);
lean_inc(x_755);
lean_dec(x_753);
x_756 = lean_ctor_get(x_754, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_754, 1);
lean_inc(x_757);
lean_dec(x_754);
x_758 = l_Lean_Meta_intro1(x_757, x_752, x_12, x_755);
if (lean_obj_tag(x_758) == 0)
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
lean_dec(x_758);
x_761 = lean_ctor_get(x_759, 0);
lean_inc(x_761);
x_762 = lean_ctor_get(x_759, 1);
lean_inc(x_762);
lean_dec(x_759);
x_763 = lean_box(0);
x_764 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_733, x_756, x_733, x_729, x_763);
lean_dec(x_733);
x_765 = x_756;
x_766 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_729, x_765);
x_767 = x_766;
lean_inc(x_761);
x_768 = l_Lean_mkFVar(x_761);
lean_inc(x_762);
x_769 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_769, 0, x_762);
x_770 = lean_box(x_738);
lean_inc(x_762);
x_771 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_771, 0, x_761);
lean_closure_set(x_771, 1, x_7);
lean_closure_set(x_771, 2, x_3);
lean_closure_set(x_771, 3, x_4);
lean_closure_set(x_771, 4, x_5);
lean_closure_set(x_771, 5, x_6);
lean_closure_set(x_771, 6, x_720);
lean_closure_set(x_771, 7, x_770);
lean_closure_set(x_771, 8, x_748);
lean_closure_set(x_771, 9, x_762);
lean_closure_set(x_771, 10, x_764);
lean_closure_set(x_771, 11, x_767);
lean_closure_set(x_771, 12, x_768);
x_772 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_772, 0, x_769);
lean_closure_set(x_772, 1, x_771);
x_773 = l_Lean_Meta_getMVarDecl(x_762, x_12, x_760);
if (lean_obj_tag(x_773) == 0)
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_774 = lean_ctor_get(x_773, 0);
lean_inc(x_774);
x_775 = lean_ctor_get(x_773, 1);
lean_inc(x_775);
lean_dec(x_773);
x_776 = lean_ctor_get(x_774, 1);
lean_inc(x_776);
x_777 = lean_ctor_get(x_774, 4);
lean_inc(x_777);
lean_dec(x_774);
x_778 = l_Lean_Meta_withLocalContext___rarg(x_776, x_777, x_772, x_12, x_775);
lean_dec(x_12);
return x_778;
}
else
{
uint8_t x_779; 
lean_dec(x_772);
lean_dec(x_12);
x_779 = !lean_is_exclusive(x_773);
if (x_779 == 0)
{
return x_773;
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_780 = lean_ctor_get(x_773, 0);
x_781 = lean_ctor_get(x_773, 1);
lean_inc(x_781);
lean_inc(x_780);
lean_dec(x_773);
x_782 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_782, 0, x_780);
lean_ctor_set(x_782, 1, x_781);
return x_782;
}
}
}
else
{
uint8_t x_783; 
lean_dec(x_756);
lean_dec(x_748);
lean_dec(x_733);
lean_dec(x_720);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_783 = !lean_is_exclusive(x_758);
if (x_783 == 0)
{
return x_758;
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; 
x_784 = lean_ctor_get(x_758, 0);
x_785 = lean_ctor_get(x_758, 1);
lean_inc(x_785);
lean_inc(x_784);
lean_dec(x_758);
x_786 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_786, 0, x_784);
lean_ctor_set(x_786, 1, x_785);
return x_786;
}
}
}
else
{
uint8_t x_787; 
lean_dec(x_748);
lean_dec(x_733);
lean_dec(x_720);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_787 = !lean_is_exclusive(x_753);
if (x_787 == 0)
{
return x_753;
}
else
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_788 = lean_ctor_get(x_753, 0);
x_789 = lean_ctor_get(x_753, 1);
lean_inc(x_789);
lean_inc(x_788);
lean_dec(x_753);
x_790 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_790, 0, x_788);
lean_ctor_set(x_790, 1, x_789);
return x_790;
}
}
}
else
{
uint8_t x_791; 
lean_dec(x_733);
lean_dec(x_720);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_791 = !lean_is_exclusive(x_745);
if (x_791 == 0)
{
return x_745;
}
else
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_792 = lean_ctor_get(x_745, 0);
x_793 = lean_ctor_get(x_745, 1);
lean_inc(x_793);
lean_inc(x_792);
lean_dec(x_745);
x_794 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_794, 0, x_792);
lean_ctor_set(x_794, 1, x_793);
return x_794;
}
}
}
}
else
{
uint8_t x_808; 
lean_dec(x_733);
lean_dec(x_723);
lean_dec(x_720);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_808 = !lean_is_exclusive(x_735);
if (x_808 == 0)
{
return x_735;
}
else
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_809 = lean_ctor_get(x_735, 0);
x_810 = lean_ctor_get(x_735, 1);
lean_inc(x_810);
lean_inc(x_809);
lean_dec(x_735);
x_811 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_811, 0, x_809);
lean_ctor_set(x_811, 1, x_810);
return x_811;
}
}
}
else
{
uint8_t x_812; 
lean_dec(x_723);
lean_dec(x_720);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_812 = !lean_is_exclusive(x_732);
if (x_812 == 0)
{
return x_732;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_813 = lean_ctor_get(x_732, 0);
x_814 = lean_ctor_get(x_732, 1);
lean_inc(x_814);
lean_inc(x_813);
lean_dec(x_732);
x_815 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_815, 0, x_813);
lean_ctor_set(x_815, 1, x_814);
return x_815;
}
}
}
else
{
uint8_t x_816; 
lean_dec(x_720);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_816 = !lean_is_exclusive(x_721);
if (x_816 == 0)
{
return x_721;
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_817 = lean_ctor_get(x_721, 0);
x_818 = lean_ctor_get(x_721, 1);
lean_inc(x_818);
lean_inc(x_817);
lean_dec(x_721);
x_819 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_819, 0, x_817);
lean_ctor_set(x_819, 1, x_818);
return x_819;
}
}
}
case 9:
{
lean_object* x_820; lean_object* x_821; 
lean_dec(x_11);
lean_dec(x_9);
x_820 = lean_ctor_get(x_6, 5);
lean_inc(x_820);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_821 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_820, x_12, x_13);
if (lean_obj_tag(x_821) == 0)
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
x_822 = lean_ctor_get(x_821, 1);
lean_inc(x_822);
lean_dec(x_821);
x_823 = lean_ctor_get(x_822, 1);
lean_inc(x_823);
x_824 = lean_ctor_get(x_6, 6);
lean_inc(x_824);
x_825 = l_List_redLength___main___rarg(x_824);
x_826 = lean_mk_empty_array_with_capacity(x_825);
lean_dec(x_825);
lean_inc(x_824);
x_827 = l_List_toArrayAux___main___rarg(x_824, x_826);
x_828 = x_827;
x_829 = lean_unsigned_to_nat(0u);
lean_inc(x_823);
lean_inc(x_5);
lean_inc(x_1);
x_830 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_830, 0, x_1);
lean_closure_set(x_830, 1, x_5);
lean_closure_set(x_830, 2, x_8);
lean_closure_set(x_830, 3, x_10);
lean_closure_set(x_830, 4, x_823);
lean_closure_set(x_830, 5, x_824);
lean_closure_set(x_830, 6, x_829);
lean_closure_set(x_830, 7, x_828);
x_831 = x_830;
lean_inc(x_12);
x_832 = lean_apply_2(x_831, x_12, x_822);
if (lean_obj_tag(x_832) == 0)
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; 
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_832, 1);
lean_inc(x_834);
lean_dec(x_832);
lean_inc(x_1);
x_835 = l_Lean_Meta_getMVarType(x_1, x_12, x_834);
if (lean_obj_tag(x_835) == 0)
{
lean_object* x_836; lean_object* x_837; uint8_t x_838; lean_object* x_839; 
x_836 = lean_ctor_get(x_835, 0);
lean_inc(x_836);
x_837 = lean_ctor_get(x_835, 1);
lean_inc(x_837);
lean_dec(x_835);
x_838 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_838 == 0)
{
lean_object* x_896; uint8_t x_897; 
x_896 = l_Lean_MetavarContext_exprDependsOn(x_823, x_836, x_2);
x_897 = lean_unbox(x_896);
lean_dec(x_896);
if (x_897 == 0)
{
x_839 = x_837;
goto block_895;
}
else
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; uint8_t x_904; 
lean_dec(x_833);
lean_dec(x_820);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_898 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_898, 0, x_3);
x_899 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_900 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_900, 0, x_899);
lean_ctor_set(x_900, 1, x_898);
x_901 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_902 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_902, 0, x_900);
lean_ctor_set(x_902, 1, x_901);
x_903 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_902, x_12, x_837);
lean_dec(x_12);
x_904 = !lean_is_exclusive(x_903);
if (x_904 == 0)
{
return x_903;
}
else
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; 
x_905 = lean_ctor_get(x_903, 0);
x_906 = lean_ctor_get(x_903, 1);
lean_inc(x_906);
lean_inc(x_905);
lean_dec(x_903);
x_907 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_907, 0, x_905);
lean_ctor_set(x_907, 1, x_906);
return x_907;
}
}
}
else
{
lean_dec(x_836);
lean_dec(x_823);
x_839 = x_837;
goto block_895;
}
block_895:
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; uint8_t x_844; lean_object* x_845; 
lean_inc(x_833);
x_840 = x_833;
x_841 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_829, x_840);
x_842 = x_841;
x_843 = lean_array_push(x_842, x_2);
x_844 = 1;
x_845 = l_Lean_Meta_revert(x_1, x_843, x_844, x_12, x_839);
if (lean_obj_tag(x_845) == 0)
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; uint8_t x_852; lean_object* x_853; 
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_845, 1);
lean_inc(x_847);
lean_dec(x_845);
x_848 = lean_ctor_get(x_846, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_846, 1);
lean_inc(x_849);
lean_dec(x_846);
x_850 = lean_array_get_size(x_833);
x_851 = lean_box(0);
x_852 = 0;
x_853 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_852, x_849, x_850, x_851, x_12, x_847);
if (lean_obj_tag(x_853) == 0)
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; 
x_854 = lean_ctor_get(x_853, 0);
lean_inc(x_854);
x_855 = lean_ctor_get(x_853, 1);
lean_inc(x_855);
lean_dec(x_853);
x_856 = lean_ctor_get(x_854, 0);
lean_inc(x_856);
x_857 = lean_ctor_get(x_854, 1);
lean_inc(x_857);
lean_dec(x_854);
x_858 = l_Lean_Meta_intro1(x_857, x_852, x_12, x_855);
if (lean_obj_tag(x_858) == 0)
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; 
x_859 = lean_ctor_get(x_858, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_858, 1);
lean_inc(x_860);
lean_dec(x_858);
x_861 = lean_ctor_get(x_859, 0);
lean_inc(x_861);
x_862 = lean_ctor_get(x_859, 1);
lean_inc(x_862);
lean_dec(x_859);
x_863 = lean_box(0);
x_864 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_833, x_856, x_833, x_829, x_863);
lean_dec(x_833);
x_865 = x_856;
x_866 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_829, x_865);
x_867 = x_866;
lean_inc(x_861);
x_868 = l_Lean_mkFVar(x_861);
lean_inc(x_862);
x_869 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_869, 0, x_862);
x_870 = lean_box(x_838);
lean_inc(x_862);
x_871 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_871, 0, x_861);
lean_closure_set(x_871, 1, x_7);
lean_closure_set(x_871, 2, x_3);
lean_closure_set(x_871, 3, x_4);
lean_closure_set(x_871, 4, x_5);
lean_closure_set(x_871, 5, x_6);
lean_closure_set(x_871, 6, x_820);
lean_closure_set(x_871, 7, x_870);
lean_closure_set(x_871, 8, x_848);
lean_closure_set(x_871, 9, x_862);
lean_closure_set(x_871, 10, x_864);
lean_closure_set(x_871, 11, x_867);
lean_closure_set(x_871, 12, x_868);
x_872 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_872, 0, x_869);
lean_closure_set(x_872, 1, x_871);
x_873 = l_Lean_Meta_getMVarDecl(x_862, x_12, x_860);
if (lean_obj_tag(x_873) == 0)
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; 
x_874 = lean_ctor_get(x_873, 0);
lean_inc(x_874);
x_875 = lean_ctor_get(x_873, 1);
lean_inc(x_875);
lean_dec(x_873);
x_876 = lean_ctor_get(x_874, 1);
lean_inc(x_876);
x_877 = lean_ctor_get(x_874, 4);
lean_inc(x_877);
lean_dec(x_874);
x_878 = l_Lean_Meta_withLocalContext___rarg(x_876, x_877, x_872, x_12, x_875);
lean_dec(x_12);
return x_878;
}
else
{
uint8_t x_879; 
lean_dec(x_872);
lean_dec(x_12);
x_879 = !lean_is_exclusive(x_873);
if (x_879 == 0)
{
return x_873;
}
else
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; 
x_880 = lean_ctor_get(x_873, 0);
x_881 = lean_ctor_get(x_873, 1);
lean_inc(x_881);
lean_inc(x_880);
lean_dec(x_873);
x_882 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_882, 0, x_880);
lean_ctor_set(x_882, 1, x_881);
return x_882;
}
}
}
else
{
uint8_t x_883; 
lean_dec(x_856);
lean_dec(x_848);
lean_dec(x_833);
lean_dec(x_820);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_883 = !lean_is_exclusive(x_858);
if (x_883 == 0)
{
return x_858;
}
else
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; 
x_884 = lean_ctor_get(x_858, 0);
x_885 = lean_ctor_get(x_858, 1);
lean_inc(x_885);
lean_inc(x_884);
lean_dec(x_858);
x_886 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_886, 0, x_884);
lean_ctor_set(x_886, 1, x_885);
return x_886;
}
}
}
else
{
uint8_t x_887; 
lean_dec(x_848);
lean_dec(x_833);
lean_dec(x_820);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_887 = !lean_is_exclusive(x_853);
if (x_887 == 0)
{
return x_853;
}
else
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; 
x_888 = lean_ctor_get(x_853, 0);
x_889 = lean_ctor_get(x_853, 1);
lean_inc(x_889);
lean_inc(x_888);
lean_dec(x_853);
x_890 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_890, 0, x_888);
lean_ctor_set(x_890, 1, x_889);
return x_890;
}
}
}
else
{
uint8_t x_891; 
lean_dec(x_833);
lean_dec(x_820);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_891 = !lean_is_exclusive(x_845);
if (x_891 == 0)
{
return x_845;
}
else
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_892 = lean_ctor_get(x_845, 0);
x_893 = lean_ctor_get(x_845, 1);
lean_inc(x_893);
lean_inc(x_892);
lean_dec(x_845);
x_894 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_894, 0, x_892);
lean_ctor_set(x_894, 1, x_893);
return x_894;
}
}
}
}
else
{
uint8_t x_908; 
lean_dec(x_833);
lean_dec(x_823);
lean_dec(x_820);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_908 = !lean_is_exclusive(x_835);
if (x_908 == 0)
{
return x_835;
}
else
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; 
x_909 = lean_ctor_get(x_835, 0);
x_910 = lean_ctor_get(x_835, 1);
lean_inc(x_910);
lean_inc(x_909);
lean_dec(x_835);
x_911 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_911, 0, x_909);
lean_ctor_set(x_911, 1, x_910);
return x_911;
}
}
}
else
{
uint8_t x_912; 
lean_dec(x_823);
lean_dec(x_820);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_912 = !lean_is_exclusive(x_832);
if (x_912 == 0)
{
return x_832;
}
else
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; 
x_913 = lean_ctor_get(x_832, 0);
x_914 = lean_ctor_get(x_832, 1);
lean_inc(x_914);
lean_inc(x_913);
lean_dec(x_832);
x_915 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_915, 0, x_913);
lean_ctor_set(x_915, 1, x_914);
return x_915;
}
}
}
else
{
uint8_t x_916; 
lean_dec(x_820);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_916 = !lean_is_exclusive(x_821);
if (x_916 == 0)
{
return x_821;
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; 
x_917 = lean_ctor_get(x_821, 0);
x_918 = lean_ctor_get(x_821, 1);
lean_inc(x_918);
lean_inc(x_917);
lean_dec(x_821);
x_919 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_919, 0, x_917);
lean_ctor_set(x_919, 1, x_918);
return x_919;
}
}
}
case 10:
{
lean_object* x_920; lean_object* x_921; 
lean_dec(x_11);
lean_dec(x_9);
x_920 = lean_ctor_get(x_6, 5);
lean_inc(x_920);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_921 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_920, x_12, x_13);
if (lean_obj_tag(x_921) == 0)
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; 
x_922 = lean_ctor_get(x_921, 1);
lean_inc(x_922);
lean_dec(x_921);
x_923 = lean_ctor_get(x_922, 1);
lean_inc(x_923);
x_924 = lean_ctor_get(x_6, 6);
lean_inc(x_924);
x_925 = l_List_redLength___main___rarg(x_924);
x_926 = lean_mk_empty_array_with_capacity(x_925);
lean_dec(x_925);
lean_inc(x_924);
x_927 = l_List_toArrayAux___main___rarg(x_924, x_926);
x_928 = x_927;
x_929 = lean_unsigned_to_nat(0u);
lean_inc(x_923);
lean_inc(x_5);
lean_inc(x_1);
x_930 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_930, 0, x_1);
lean_closure_set(x_930, 1, x_5);
lean_closure_set(x_930, 2, x_8);
lean_closure_set(x_930, 3, x_10);
lean_closure_set(x_930, 4, x_923);
lean_closure_set(x_930, 5, x_924);
lean_closure_set(x_930, 6, x_929);
lean_closure_set(x_930, 7, x_928);
x_931 = x_930;
lean_inc(x_12);
x_932 = lean_apply_2(x_931, x_12, x_922);
if (lean_obj_tag(x_932) == 0)
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_933 = lean_ctor_get(x_932, 0);
lean_inc(x_933);
x_934 = lean_ctor_get(x_932, 1);
lean_inc(x_934);
lean_dec(x_932);
lean_inc(x_1);
x_935 = l_Lean_Meta_getMVarType(x_1, x_12, x_934);
if (lean_obj_tag(x_935) == 0)
{
lean_object* x_936; lean_object* x_937; uint8_t x_938; lean_object* x_939; 
x_936 = lean_ctor_get(x_935, 0);
lean_inc(x_936);
x_937 = lean_ctor_get(x_935, 1);
lean_inc(x_937);
lean_dec(x_935);
x_938 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_938 == 0)
{
lean_object* x_996; uint8_t x_997; 
x_996 = l_Lean_MetavarContext_exprDependsOn(x_923, x_936, x_2);
x_997 = lean_unbox(x_996);
lean_dec(x_996);
if (x_997 == 0)
{
x_939 = x_937;
goto block_995;
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; uint8_t x_1004; 
lean_dec(x_933);
lean_dec(x_920);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_998 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_998, 0, x_3);
x_999 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1000 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1000, 0, x_999);
lean_ctor_set(x_1000, 1, x_998);
x_1001 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_1002 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1002, 0, x_1000);
lean_ctor_set(x_1002, 1, x_1001);
x_1003 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_1002, x_12, x_937);
lean_dec(x_12);
x_1004 = !lean_is_exclusive(x_1003);
if (x_1004 == 0)
{
return x_1003;
}
else
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; 
x_1005 = lean_ctor_get(x_1003, 0);
x_1006 = lean_ctor_get(x_1003, 1);
lean_inc(x_1006);
lean_inc(x_1005);
lean_dec(x_1003);
x_1007 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1007, 0, x_1005);
lean_ctor_set(x_1007, 1, x_1006);
return x_1007;
}
}
}
else
{
lean_dec(x_936);
lean_dec(x_923);
x_939 = x_937;
goto block_995;
}
block_995:
{
lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; uint8_t x_944; lean_object* x_945; 
lean_inc(x_933);
x_940 = x_933;
x_941 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_929, x_940);
x_942 = x_941;
x_943 = lean_array_push(x_942, x_2);
x_944 = 1;
x_945 = l_Lean_Meta_revert(x_1, x_943, x_944, x_12, x_939);
if (lean_obj_tag(x_945) == 0)
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; uint8_t x_952; lean_object* x_953; 
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_945, 1);
lean_inc(x_947);
lean_dec(x_945);
x_948 = lean_ctor_get(x_946, 0);
lean_inc(x_948);
x_949 = lean_ctor_get(x_946, 1);
lean_inc(x_949);
lean_dec(x_946);
x_950 = lean_array_get_size(x_933);
x_951 = lean_box(0);
x_952 = 0;
x_953 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_952, x_949, x_950, x_951, x_12, x_947);
if (lean_obj_tag(x_953) == 0)
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; 
x_954 = lean_ctor_get(x_953, 0);
lean_inc(x_954);
x_955 = lean_ctor_get(x_953, 1);
lean_inc(x_955);
lean_dec(x_953);
x_956 = lean_ctor_get(x_954, 0);
lean_inc(x_956);
x_957 = lean_ctor_get(x_954, 1);
lean_inc(x_957);
lean_dec(x_954);
x_958 = l_Lean_Meta_intro1(x_957, x_952, x_12, x_955);
if (lean_obj_tag(x_958) == 0)
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; 
x_959 = lean_ctor_get(x_958, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_958, 1);
lean_inc(x_960);
lean_dec(x_958);
x_961 = lean_ctor_get(x_959, 0);
lean_inc(x_961);
x_962 = lean_ctor_get(x_959, 1);
lean_inc(x_962);
lean_dec(x_959);
x_963 = lean_box(0);
x_964 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_933, x_956, x_933, x_929, x_963);
lean_dec(x_933);
x_965 = x_956;
x_966 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_929, x_965);
x_967 = x_966;
lean_inc(x_961);
x_968 = l_Lean_mkFVar(x_961);
lean_inc(x_962);
x_969 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_969, 0, x_962);
x_970 = lean_box(x_938);
lean_inc(x_962);
x_971 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_971, 0, x_961);
lean_closure_set(x_971, 1, x_7);
lean_closure_set(x_971, 2, x_3);
lean_closure_set(x_971, 3, x_4);
lean_closure_set(x_971, 4, x_5);
lean_closure_set(x_971, 5, x_6);
lean_closure_set(x_971, 6, x_920);
lean_closure_set(x_971, 7, x_970);
lean_closure_set(x_971, 8, x_948);
lean_closure_set(x_971, 9, x_962);
lean_closure_set(x_971, 10, x_964);
lean_closure_set(x_971, 11, x_967);
lean_closure_set(x_971, 12, x_968);
x_972 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_972, 0, x_969);
lean_closure_set(x_972, 1, x_971);
x_973 = l_Lean_Meta_getMVarDecl(x_962, x_12, x_960);
if (lean_obj_tag(x_973) == 0)
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; 
x_974 = lean_ctor_get(x_973, 0);
lean_inc(x_974);
x_975 = lean_ctor_get(x_973, 1);
lean_inc(x_975);
lean_dec(x_973);
x_976 = lean_ctor_get(x_974, 1);
lean_inc(x_976);
x_977 = lean_ctor_get(x_974, 4);
lean_inc(x_977);
lean_dec(x_974);
x_978 = l_Lean_Meta_withLocalContext___rarg(x_976, x_977, x_972, x_12, x_975);
lean_dec(x_12);
return x_978;
}
else
{
uint8_t x_979; 
lean_dec(x_972);
lean_dec(x_12);
x_979 = !lean_is_exclusive(x_973);
if (x_979 == 0)
{
return x_973;
}
else
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; 
x_980 = lean_ctor_get(x_973, 0);
x_981 = lean_ctor_get(x_973, 1);
lean_inc(x_981);
lean_inc(x_980);
lean_dec(x_973);
x_982 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_982, 0, x_980);
lean_ctor_set(x_982, 1, x_981);
return x_982;
}
}
}
else
{
uint8_t x_983; 
lean_dec(x_956);
lean_dec(x_948);
lean_dec(x_933);
lean_dec(x_920);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_983 = !lean_is_exclusive(x_958);
if (x_983 == 0)
{
return x_958;
}
else
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; 
x_984 = lean_ctor_get(x_958, 0);
x_985 = lean_ctor_get(x_958, 1);
lean_inc(x_985);
lean_inc(x_984);
lean_dec(x_958);
x_986 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_986, 0, x_984);
lean_ctor_set(x_986, 1, x_985);
return x_986;
}
}
}
else
{
uint8_t x_987; 
lean_dec(x_948);
lean_dec(x_933);
lean_dec(x_920);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_987 = !lean_is_exclusive(x_953);
if (x_987 == 0)
{
return x_953;
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; 
x_988 = lean_ctor_get(x_953, 0);
x_989 = lean_ctor_get(x_953, 1);
lean_inc(x_989);
lean_inc(x_988);
lean_dec(x_953);
x_990 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_990, 0, x_988);
lean_ctor_set(x_990, 1, x_989);
return x_990;
}
}
}
else
{
uint8_t x_991; 
lean_dec(x_933);
lean_dec(x_920);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_991 = !lean_is_exclusive(x_945);
if (x_991 == 0)
{
return x_945;
}
else
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; 
x_992 = lean_ctor_get(x_945, 0);
x_993 = lean_ctor_get(x_945, 1);
lean_inc(x_993);
lean_inc(x_992);
lean_dec(x_945);
x_994 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_994, 0, x_992);
lean_ctor_set(x_994, 1, x_993);
return x_994;
}
}
}
}
else
{
uint8_t x_1008; 
lean_dec(x_933);
lean_dec(x_923);
lean_dec(x_920);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1008 = !lean_is_exclusive(x_935);
if (x_1008 == 0)
{
return x_935;
}
else
{
lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
x_1009 = lean_ctor_get(x_935, 0);
x_1010 = lean_ctor_get(x_935, 1);
lean_inc(x_1010);
lean_inc(x_1009);
lean_dec(x_935);
x_1011 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1011, 0, x_1009);
lean_ctor_set(x_1011, 1, x_1010);
return x_1011;
}
}
}
else
{
uint8_t x_1012; 
lean_dec(x_923);
lean_dec(x_920);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1012 = !lean_is_exclusive(x_932);
if (x_1012 == 0)
{
return x_932;
}
else
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; 
x_1013 = lean_ctor_get(x_932, 0);
x_1014 = lean_ctor_get(x_932, 1);
lean_inc(x_1014);
lean_inc(x_1013);
lean_dec(x_932);
x_1015 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1015, 0, x_1013);
lean_ctor_set(x_1015, 1, x_1014);
return x_1015;
}
}
}
else
{
uint8_t x_1016; 
lean_dec(x_920);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1016 = !lean_is_exclusive(x_921);
if (x_1016 == 0)
{
return x_921;
}
else
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1017 = lean_ctor_get(x_921, 0);
x_1018 = lean_ctor_get(x_921, 1);
lean_inc(x_1018);
lean_inc(x_1017);
lean_dec(x_921);
x_1019 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1019, 0, x_1017);
lean_ctor_set(x_1019, 1, x_1018);
return x_1019;
}
}
}
case 11:
{
lean_object* x_1020; lean_object* x_1021; 
lean_dec(x_11);
lean_dec(x_9);
x_1020 = lean_ctor_get(x_6, 5);
lean_inc(x_1020);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_1021 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_1020, x_12, x_13);
if (lean_obj_tag(x_1021) == 0)
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1022 = lean_ctor_get(x_1021, 1);
lean_inc(x_1022);
lean_dec(x_1021);
x_1023 = lean_ctor_get(x_1022, 1);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_6, 6);
lean_inc(x_1024);
x_1025 = l_List_redLength___main___rarg(x_1024);
x_1026 = lean_mk_empty_array_with_capacity(x_1025);
lean_dec(x_1025);
lean_inc(x_1024);
x_1027 = l_List_toArrayAux___main___rarg(x_1024, x_1026);
x_1028 = x_1027;
x_1029 = lean_unsigned_to_nat(0u);
lean_inc(x_1023);
lean_inc(x_5);
lean_inc(x_1);
x_1030 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_1030, 0, x_1);
lean_closure_set(x_1030, 1, x_5);
lean_closure_set(x_1030, 2, x_8);
lean_closure_set(x_1030, 3, x_10);
lean_closure_set(x_1030, 4, x_1023);
lean_closure_set(x_1030, 5, x_1024);
lean_closure_set(x_1030, 6, x_1029);
lean_closure_set(x_1030, 7, x_1028);
x_1031 = x_1030;
lean_inc(x_12);
x_1032 = lean_apply_2(x_1031, x_12, x_1022);
if (lean_obj_tag(x_1032) == 0)
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; 
x_1033 = lean_ctor_get(x_1032, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_1032, 1);
lean_inc(x_1034);
lean_dec(x_1032);
lean_inc(x_1);
x_1035 = l_Lean_Meta_getMVarType(x_1, x_12, x_1034);
if (lean_obj_tag(x_1035) == 0)
{
lean_object* x_1036; lean_object* x_1037; uint8_t x_1038; lean_object* x_1039; 
x_1036 = lean_ctor_get(x_1035, 0);
lean_inc(x_1036);
x_1037 = lean_ctor_get(x_1035, 1);
lean_inc(x_1037);
lean_dec(x_1035);
x_1038 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_1038 == 0)
{
lean_object* x_1096; uint8_t x_1097; 
x_1096 = l_Lean_MetavarContext_exprDependsOn(x_1023, x_1036, x_2);
x_1097 = lean_unbox(x_1096);
lean_dec(x_1096);
if (x_1097 == 0)
{
x_1039 = x_1037;
goto block_1095;
}
else
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; uint8_t x_1104; 
lean_dec(x_1033);
lean_dec(x_1020);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1098 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1098, 0, x_3);
x_1099 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1100 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1100, 0, x_1099);
lean_ctor_set(x_1100, 1, x_1098);
x_1101 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_1102 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1102, 0, x_1100);
lean_ctor_set(x_1102, 1, x_1101);
x_1103 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_1102, x_12, x_1037);
lean_dec(x_12);
x_1104 = !lean_is_exclusive(x_1103);
if (x_1104 == 0)
{
return x_1103;
}
else
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; 
x_1105 = lean_ctor_get(x_1103, 0);
x_1106 = lean_ctor_get(x_1103, 1);
lean_inc(x_1106);
lean_inc(x_1105);
lean_dec(x_1103);
x_1107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1107, 0, x_1105);
lean_ctor_set(x_1107, 1, x_1106);
return x_1107;
}
}
}
else
{
lean_dec(x_1036);
lean_dec(x_1023);
x_1039 = x_1037;
goto block_1095;
}
block_1095:
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; uint8_t x_1044; lean_object* x_1045; 
lean_inc(x_1033);
x_1040 = x_1033;
x_1041 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1029, x_1040);
x_1042 = x_1041;
x_1043 = lean_array_push(x_1042, x_2);
x_1044 = 1;
x_1045 = l_Lean_Meta_revert(x_1, x_1043, x_1044, x_12, x_1039);
if (lean_obj_tag(x_1045) == 0)
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; uint8_t x_1052; lean_object* x_1053; 
x_1046 = lean_ctor_get(x_1045, 0);
lean_inc(x_1046);
x_1047 = lean_ctor_get(x_1045, 1);
lean_inc(x_1047);
lean_dec(x_1045);
x_1048 = lean_ctor_get(x_1046, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1046, 1);
lean_inc(x_1049);
lean_dec(x_1046);
x_1050 = lean_array_get_size(x_1033);
x_1051 = lean_box(0);
x_1052 = 0;
x_1053 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1052, x_1049, x_1050, x_1051, x_12, x_1047);
if (lean_obj_tag(x_1053) == 0)
{
lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; 
x_1054 = lean_ctor_get(x_1053, 0);
lean_inc(x_1054);
x_1055 = lean_ctor_get(x_1053, 1);
lean_inc(x_1055);
lean_dec(x_1053);
x_1056 = lean_ctor_get(x_1054, 0);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_1054, 1);
lean_inc(x_1057);
lean_dec(x_1054);
x_1058 = l_Lean_Meta_intro1(x_1057, x_1052, x_12, x_1055);
if (lean_obj_tag(x_1058) == 0)
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; 
x_1059 = lean_ctor_get(x_1058, 0);
lean_inc(x_1059);
x_1060 = lean_ctor_get(x_1058, 1);
lean_inc(x_1060);
lean_dec(x_1058);
x_1061 = lean_ctor_get(x_1059, 0);
lean_inc(x_1061);
x_1062 = lean_ctor_get(x_1059, 1);
lean_inc(x_1062);
lean_dec(x_1059);
x_1063 = lean_box(0);
x_1064 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_1033, x_1056, x_1033, x_1029, x_1063);
lean_dec(x_1033);
x_1065 = x_1056;
x_1066 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_1029, x_1065);
x_1067 = x_1066;
lean_inc(x_1061);
x_1068 = l_Lean_mkFVar(x_1061);
lean_inc(x_1062);
x_1069 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_1069, 0, x_1062);
x_1070 = lean_box(x_1038);
lean_inc(x_1062);
x_1071 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_1071, 0, x_1061);
lean_closure_set(x_1071, 1, x_7);
lean_closure_set(x_1071, 2, x_3);
lean_closure_set(x_1071, 3, x_4);
lean_closure_set(x_1071, 4, x_5);
lean_closure_set(x_1071, 5, x_6);
lean_closure_set(x_1071, 6, x_1020);
lean_closure_set(x_1071, 7, x_1070);
lean_closure_set(x_1071, 8, x_1048);
lean_closure_set(x_1071, 9, x_1062);
lean_closure_set(x_1071, 10, x_1064);
lean_closure_set(x_1071, 11, x_1067);
lean_closure_set(x_1071, 12, x_1068);
x_1072 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_1072, 0, x_1069);
lean_closure_set(x_1072, 1, x_1071);
x_1073 = l_Lean_Meta_getMVarDecl(x_1062, x_12, x_1060);
if (lean_obj_tag(x_1073) == 0)
{
lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; 
x_1074 = lean_ctor_get(x_1073, 0);
lean_inc(x_1074);
x_1075 = lean_ctor_get(x_1073, 1);
lean_inc(x_1075);
lean_dec(x_1073);
x_1076 = lean_ctor_get(x_1074, 1);
lean_inc(x_1076);
x_1077 = lean_ctor_get(x_1074, 4);
lean_inc(x_1077);
lean_dec(x_1074);
x_1078 = l_Lean_Meta_withLocalContext___rarg(x_1076, x_1077, x_1072, x_12, x_1075);
lean_dec(x_12);
return x_1078;
}
else
{
uint8_t x_1079; 
lean_dec(x_1072);
lean_dec(x_12);
x_1079 = !lean_is_exclusive(x_1073);
if (x_1079 == 0)
{
return x_1073;
}
else
{
lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; 
x_1080 = lean_ctor_get(x_1073, 0);
x_1081 = lean_ctor_get(x_1073, 1);
lean_inc(x_1081);
lean_inc(x_1080);
lean_dec(x_1073);
x_1082 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1082, 0, x_1080);
lean_ctor_set(x_1082, 1, x_1081);
return x_1082;
}
}
}
else
{
uint8_t x_1083; 
lean_dec(x_1056);
lean_dec(x_1048);
lean_dec(x_1033);
lean_dec(x_1020);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1083 = !lean_is_exclusive(x_1058);
if (x_1083 == 0)
{
return x_1058;
}
else
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; 
x_1084 = lean_ctor_get(x_1058, 0);
x_1085 = lean_ctor_get(x_1058, 1);
lean_inc(x_1085);
lean_inc(x_1084);
lean_dec(x_1058);
x_1086 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1086, 0, x_1084);
lean_ctor_set(x_1086, 1, x_1085);
return x_1086;
}
}
}
else
{
uint8_t x_1087; 
lean_dec(x_1048);
lean_dec(x_1033);
lean_dec(x_1020);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1087 = !lean_is_exclusive(x_1053);
if (x_1087 == 0)
{
return x_1053;
}
else
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; 
x_1088 = lean_ctor_get(x_1053, 0);
x_1089 = lean_ctor_get(x_1053, 1);
lean_inc(x_1089);
lean_inc(x_1088);
lean_dec(x_1053);
x_1090 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1090, 0, x_1088);
lean_ctor_set(x_1090, 1, x_1089);
return x_1090;
}
}
}
else
{
uint8_t x_1091; 
lean_dec(x_1033);
lean_dec(x_1020);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1091 = !lean_is_exclusive(x_1045);
if (x_1091 == 0)
{
return x_1045;
}
else
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; 
x_1092 = lean_ctor_get(x_1045, 0);
x_1093 = lean_ctor_get(x_1045, 1);
lean_inc(x_1093);
lean_inc(x_1092);
lean_dec(x_1045);
x_1094 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1094, 0, x_1092);
lean_ctor_set(x_1094, 1, x_1093);
return x_1094;
}
}
}
}
else
{
uint8_t x_1108; 
lean_dec(x_1033);
lean_dec(x_1023);
lean_dec(x_1020);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1108 = !lean_is_exclusive(x_1035);
if (x_1108 == 0)
{
return x_1035;
}
else
{
lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; 
x_1109 = lean_ctor_get(x_1035, 0);
x_1110 = lean_ctor_get(x_1035, 1);
lean_inc(x_1110);
lean_inc(x_1109);
lean_dec(x_1035);
x_1111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1111, 0, x_1109);
lean_ctor_set(x_1111, 1, x_1110);
return x_1111;
}
}
}
else
{
uint8_t x_1112; 
lean_dec(x_1023);
lean_dec(x_1020);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1112 = !lean_is_exclusive(x_1032);
if (x_1112 == 0)
{
return x_1032;
}
else
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
x_1113 = lean_ctor_get(x_1032, 0);
x_1114 = lean_ctor_get(x_1032, 1);
lean_inc(x_1114);
lean_inc(x_1113);
lean_dec(x_1032);
x_1115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1115, 0, x_1113);
lean_ctor_set(x_1115, 1, x_1114);
return x_1115;
}
}
}
else
{
uint8_t x_1116; 
lean_dec(x_1020);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1116 = !lean_is_exclusive(x_1021);
if (x_1116 == 0)
{
return x_1021;
}
else
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; 
x_1117 = lean_ctor_get(x_1021, 0);
x_1118 = lean_ctor_get(x_1021, 1);
lean_inc(x_1118);
lean_inc(x_1117);
lean_dec(x_1021);
x_1119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1119, 0, x_1117);
lean_ctor_set(x_1119, 1, x_1118);
return x_1119;
}
}
}
default: 
{
lean_object* x_1120; lean_object* x_1121; 
lean_dec(x_11);
lean_dec(x_9);
x_1120 = lean_ctor_get(x_6, 5);
lean_inc(x_1120);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_1121 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_1120, x_12, x_13);
if (lean_obj_tag(x_1121) == 0)
{
lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
x_1122 = lean_ctor_get(x_1121, 1);
lean_inc(x_1122);
lean_dec(x_1121);
x_1123 = lean_ctor_get(x_1122, 1);
lean_inc(x_1123);
x_1124 = lean_ctor_get(x_6, 6);
lean_inc(x_1124);
x_1125 = l_List_redLength___main___rarg(x_1124);
x_1126 = lean_mk_empty_array_with_capacity(x_1125);
lean_dec(x_1125);
lean_inc(x_1124);
x_1127 = l_List_toArrayAux___main___rarg(x_1124, x_1126);
x_1128 = x_1127;
x_1129 = lean_unsigned_to_nat(0u);
lean_inc(x_1123);
lean_inc(x_5);
lean_inc(x_1);
x_1130 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_1130, 0, x_1);
lean_closure_set(x_1130, 1, x_5);
lean_closure_set(x_1130, 2, x_8);
lean_closure_set(x_1130, 3, x_10);
lean_closure_set(x_1130, 4, x_1123);
lean_closure_set(x_1130, 5, x_1124);
lean_closure_set(x_1130, 6, x_1129);
lean_closure_set(x_1130, 7, x_1128);
x_1131 = x_1130;
lean_inc(x_12);
x_1132 = lean_apply_2(x_1131, x_12, x_1122);
if (lean_obj_tag(x_1132) == 0)
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; 
x_1133 = lean_ctor_get(x_1132, 0);
lean_inc(x_1133);
x_1134 = lean_ctor_get(x_1132, 1);
lean_inc(x_1134);
lean_dec(x_1132);
lean_inc(x_1);
x_1135 = l_Lean_Meta_getMVarType(x_1, x_12, x_1134);
if (lean_obj_tag(x_1135) == 0)
{
lean_object* x_1136; lean_object* x_1137; uint8_t x_1138; lean_object* x_1139; 
x_1136 = lean_ctor_get(x_1135, 0);
lean_inc(x_1136);
x_1137 = lean_ctor_get(x_1135, 1);
lean_inc(x_1137);
lean_dec(x_1135);
x_1138 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_1138 == 0)
{
lean_object* x_1196; uint8_t x_1197; 
x_1196 = l_Lean_MetavarContext_exprDependsOn(x_1123, x_1136, x_2);
x_1197 = lean_unbox(x_1196);
lean_dec(x_1196);
if (x_1197 == 0)
{
x_1139 = x_1137;
goto block_1195;
}
else
{
lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; uint8_t x_1204; 
lean_dec(x_1133);
lean_dec(x_1120);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1198 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1198, 0, x_3);
x_1199 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1200 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1200, 0, x_1199);
lean_ctor_set(x_1200, 1, x_1198);
x_1201 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_1202 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1202, 0, x_1200);
lean_ctor_set(x_1202, 1, x_1201);
x_1203 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_1202, x_12, x_1137);
lean_dec(x_12);
x_1204 = !lean_is_exclusive(x_1203);
if (x_1204 == 0)
{
return x_1203;
}
else
{
lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; 
x_1205 = lean_ctor_get(x_1203, 0);
x_1206 = lean_ctor_get(x_1203, 1);
lean_inc(x_1206);
lean_inc(x_1205);
lean_dec(x_1203);
x_1207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1207, 0, x_1205);
lean_ctor_set(x_1207, 1, x_1206);
return x_1207;
}
}
}
else
{
lean_dec(x_1136);
lean_dec(x_1123);
x_1139 = x_1137;
goto block_1195;
}
block_1195:
{
lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; uint8_t x_1144; lean_object* x_1145; 
lean_inc(x_1133);
x_1140 = x_1133;
x_1141 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1129, x_1140);
x_1142 = x_1141;
x_1143 = lean_array_push(x_1142, x_2);
x_1144 = 1;
x_1145 = l_Lean_Meta_revert(x_1, x_1143, x_1144, x_12, x_1139);
if (lean_obj_tag(x_1145) == 0)
{
lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; uint8_t x_1152; lean_object* x_1153; 
x_1146 = lean_ctor_get(x_1145, 0);
lean_inc(x_1146);
x_1147 = lean_ctor_get(x_1145, 1);
lean_inc(x_1147);
lean_dec(x_1145);
x_1148 = lean_ctor_get(x_1146, 0);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_1146, 1);
lean_inc(x_1149);
lean_dec(x_1146);
x_1150 = lean_array_get_size(x_1133);
x_1151 = lean_box(0);
x_1152 = 0;
x_1153 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1152, x_1149, x_1150, x_1151, x_12, x_1147);
if (lean_obj_tag(x_1153) == 0)
{
lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; 
x_1154 = lean_ctor_get(x_1153, 0);
lean_inc(x_1154);
x_1155 = lean_ctor_get(x_1153, 1);
lean_inc(x_1155);
lean_dec(x_1153);
x_1156 = lean_ctor_get(x_1154, 0);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1154, 1);
lean_inc(x_1157);
lean_dec(x_1154);
x_1158 = l_Lean_Meta_intro1(x_1157, x_1152, x_12, x_1155);
if (lean_obj_tag(x_1158) == 0)
{
lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; 
x_1159 = lean_ctor_get(x_1158, 0);
lean_inc(x_1159);
x_1160 = lean_ctor_get(x_1158, 1);
lean_inc(x_1160);
lean_dec(x_1158);
x_1161 = lean_ctor_get(x_1159, 0);
lean_inc(x_1161);
x_1162 = lean_ctor_get(x_1159, 1);
lean_inc(x_1162);
lean_dec(x_1159);
x_1163 = lean_box(0);
x_1164 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_1133, x_1156, x_1133, x_1129, x_1163);
lean_dec(x_1133);
x_1165 = x_1156;
x_1166 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_1129, x_1165);
x_1167 = x_1166;
lean_inc(x_1161);
x_1168 = l_Lean_mkFVar(x_1161);
lean_inc(x_1162);
x_1169 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_1169, 0, x_1162);
x_1170 = lean_box(x_1138);
lean_inc(x_1162);
x_1171 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_1171, 0, x_1161);
lean_closure_set(x_1171, 1, x_7);
lean_closure_set(x_1171, 2, x_3);
lean_closure_set(x_1171, 3, x_4);
lean_closure_set(x_1171, 4, x_5);
lean_closure_set(x_1171, 5, x_6);
lean_closure_set(x_1171, 6, x_1120);
lean_closure_set(x_1171, 7, x_1170);
lean_closure_set(x_1171, 8, x_1148);
lean_closure_set(x_1171, 9, x_1162);
lean_closure_set(x_1171, 10, x_1164);
lean_closure_set(x_1171, 11, x_1167);
lean_closure_set(x_1171, 12, x_1168);
x_1172 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_1172, 0, x_1169);
lean_closure_set(x_1172, 1, x_1171);
x_1173 = l_Lean_Meta_getMVarDecl(x_1162, x_12, x_1160);
if (lean_obj_tag(x_1173) == 0)
{
lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
x_1174 = lean_ctor_get(x_1173, 0);
lean_inc(x_1174);
x_1175 = lean_ctor_get(x_1173, 1);
lean_inc(x_1175);
lean_dec(x_1173);
x_1176 = lean_ctor_get(x_1174, 1);
lean_inc(x_1176);
x_1177 = lean_ctor_get(x_1174, 4);
lean_inc(x_1177);
lean_dec(x_1174);
x_1178 = l_Lean_Meta_withLocalContext___rarg(x_1176, x_1177, x_1172, x_12, x_1175);
lean_dec(x_12);
return x_1178;
}
else
{
uint8_t x_1179; 
lean_dec(x_1172);
lean_dec(x_12);
x_1179 = !lean_is_exclusive(x_1173);
if (x_1179 == 0)
{
return x_1173;
}
else
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; 
x_1180 = lean_ctor_get(x_1173, 0);
x_1181 = lean_ctor_get(x_1173, 1);
lean_inc(x_1181);
lean_inc(x_1180);
lean_dec(x_1173);
x_1182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1182, 0, x_1180);
lean_ctor_set(x_1182, 1, x_1181);
return x_1182;
}
}
}
else
{
uint8_t x_1183; 
lean_dec(x_1156);
lean_dec(x_1148);
lean_dec(x_1133);
lean_dec(x_1120);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1183 = !lean_is_exclusive(x_1158);
if (x_1183 == 0)
{
return x_1158;
}
else
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1184 = lean_ctor_get(x_1158, 0);
x_1185 = lean_ctor_get(x_1158, 1);
lean_inc(x_1185);
lean_inc(x_1184);
lean_dec(x_1158);
x_1186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1186, 0, x_1184);
lean_ctor_set(x_1186, 1, x_1185);
return x_1186;
}
}
}
else
{
uint8_t x_1187; 
lean_dec(x_1148);
lean_dec(x_1133);
lean_dec(x_1120);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1187 = !lean_is_exclusive(x_1153);
if (x_1187 == 0)
{
return x_1153;
}
else
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; 
x_1188 = lean_ctor_get(x_1153, 0);
x_1189 = lean_ctor_get(x_1153, 1);
lean_inc(x_1189);
lean_inc(x_1188);
lean_dec(x_1153);
x_1190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1190, 0, x_1188);
lean_ctor_set(x_1190, 1, x_1189);
return x_1190;
}
}
}
else
{
uint8_t x_1191; 
lean_dec(x_1133);
lean_dec(x_1120);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1191 = !lean_is_exclusive(x_1145);
if (x_1191 == 0)
{
return x_1145;
}
else
{
lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; 
x_1192 = lean_ctor_get(x_1145, 0);
x_1193 = lean_ctor_get(x_1145, 1);
lean_inc(x_1193);
lean_inc(x_1192);
lean_dec(x_1145);
x_1194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1194, 0, x_1192);
lean_ctor_set(x_1194, 1, x_1193);
return x_1194;
}
}
}
}
else
{
uint8_t x_1208; 
lean_dec(x_1133);
lean_dec(x_1123);
lean_dec(x_1120);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1208 = !lean_is_exclusive(x_1135);
if (x_1208 == 0)
{
return x_1135;
}
else
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; 
x_1209 = lean_ctor_get(x_1135, 0);
x_1210 = lean_ctor_get(x_1135, 1);
lean_inc(x_1210);
lean_inc(x_1209);
lean_dec(x_1135);
x_1211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1211, 0, x_1209);
lean_ctor_set(x_1211, 1, x_1210);
return x_1211;
}
}
}
else
{
uint8_t x_1212; 
lean_dec(x_1123);
lean_dec(x_1120);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1212 = !lean_is_exclusive(x_1132);
if (x_1212 == 0)
{
return x_1132;
}
else
{
lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; 
x_1213 = lean_ctor_get(x_1132, 0);
x_1214 = lean_ctor_get(x_1132, 1);
lean_inc(x_1214);
lean_inc(x_1213);
lean_dec(x_1132);
x_1215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1215, 0, x_1213);
lean_ctor_set(x_1215, 1, x_1214);
return x_1215;
}
}
}
else
{
uint8_t x_1216; 
lean_dec(x_1120);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1216 = !lean_is_exclusive(x_1121);
if (x_1216 == 0)
{
return x_1121;
}
else
{
lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; 
x_1217 = lean_ctor_get(x_1121, 0);
x_1218 = lean_ctor_get(x_1121, 1);
lean_inc(x_1218);
lean_inc(x_1217);
lean_dec(x_1121);
x_1219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1219, 0, x_1217);
lean_ctor_set(x_1219, 1, x_1218);
return x_1219;
}
}
}
}
}
}
lean_object* l_Lean_Meta_induction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_1);
x_9 = l_Lean_Meta_getLocalDecl(x_1, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
lean_inc(x_7);
lean_inc(x_2);
x_13 = l_Lean_Meta_mkRecursorInfo(x_2, x_12, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_LocalDecl_type(x_10);
lean_dec(x_10);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_7);
x_18 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfUntil___spec__2(x_17, x_16, x_7, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Expr_getAppNumArgsAux___main(x_19, x_21);
x_23 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_22);
x_24 = lean_mk_array(x_22, x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_22, x_25);
lean_dec(x_22);
lean_inc(x_19);
x_27 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(x_3, x_1, x_2, x_4, x_5, x_14, x_17, x_19, x_19, x_24, x_26, x_7, x_20);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_9);
if (x_36 == 0)
{
return x_9;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_9, 0);
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_9);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* l_Lean_Meta_induction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 4, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_induction___lambda__1___boxed), 8, 5);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_1);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_8);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_getMVarDecl(x_1, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 4);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Meta_withLocalContext___rarg(x_15, x_16, x_11, x_6, x_14);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
lean_object* l_List_elem___main___at_Lean_Meta_induction___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___main___at_Lean_Meta_induction___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_13;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___main___at_Lean_Meta_induction___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_6);
lean_dec(x_6);
x_20 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7(x_1, x_2, x_3, x_4, x_5, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_20;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_8);
lean_dec(x_8);
x_18 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_18;
}
}
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_induction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_9;
}
}
lean_object* l_Lean_Meta_induction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_Meta_induction(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_6);
return x_9;
}
}
lean_object* initialize_Init_Lean_Meta_RecursorInfo(lean_object*);
lean_object* initialize_Init_Lean_Meta_SynthInstance(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Util(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Revert(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Intro(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Clear(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_FVarSubst(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_Tactic_Induction(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta_RecursorInfo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_SynthInstance(lean_io_mk_world());
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
l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1 = _init_l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1);
l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2 = _init_l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2);
l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3 = _init_l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3);
l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4 = _init_l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4);
l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5 = _init_l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5);
l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6 = _init_l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6);
l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7 = _init_l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7);
l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8 = _init_l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8);
l_Lean_Meta_InductionSubgoal_inhabited___closed__1 = _init_l_Lean_Meta_InductionSubgoal_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_InductionSubgoal_inhabited___closed__1);
l_Lean_Meta_InductionSubgoal_inhabited = _init_l_Lean_Meta_InductionSubgoal_inhabited();
lean_mark_persistent(l_Lean_Meta_InductionSubgoal_inhabited);
l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__1 = _init_l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__1();
lean_mark_persistent(l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__1);
l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__2 = _init_l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__2();
lean_mark_persistent(l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__2);
l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__3 = _init_l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__3();
lean_mark_persistent(l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__3);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__1 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__1();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__1);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__2 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__2();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__2);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__3 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__3();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__3);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__4 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__4();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__4);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__5 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__5();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__5);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__6 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__6();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__6);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__7 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__7();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__7);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__8 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__8();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__8);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__9 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__9();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__9);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__1 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__1);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__2 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__2);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__3 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__3);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__4 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__4();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__4);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__5 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__5();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__5);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__6 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__6();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__6);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__1 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__1);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__2 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__2);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__3 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__3);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__4 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__4);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__5 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__5);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__7 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__7();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__7);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__8 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__8();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__8);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__9 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__9();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__9);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__2 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__2);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
