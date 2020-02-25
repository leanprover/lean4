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
uint8_t l_Lean_Expr_isHeadBetaTarget___main(lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__4;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
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
x_3 = l_Lean_Expr_isHeadBetaTarget___main(x_1);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = l_Lean_Name_inhabited;
x_16 = lean_array_get(x_15, x_1, x_12);
x_17 = lean_nat_sub(x_12, x_3);
lean_dec(x_12);
x_18 = lean_nat_sub(x_17, x_10);
lean_dec(x_17);
x_19 = lean_array_get(x_15, x_4, x_18);
lean_dec(x_18);
x_20 = l_Lean_mkFVar(x_19);
x_21 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_16, x_20);
x_6 = x_11;
x_7 = x_21;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = l_Lean_Name_inhabited;
x_16 = lean_array_get(x_15, x_1, x_12);
x_17 = lean_nat_sub(x_12, x_3);
lean_dec(x_12);
x_18 = lean_nat_sub(x_17, x_10);
lean_dec(x_17);
x_19 = lean_array_get(x_15, x_4, x_18);
lean_dec(x_18);
x_20 = l_Lean_mkFVar(x_19);
x_21 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_7, x_16, x_20);
x_6 = x_11;
x_7 = x_21;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Array_empty___closed__1;
x_14 = x_8;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_52; 
x_16 = lean_array_fget(x_8, x_7);
x_17 = lean_box(0);
x_18 = x_17;
x_19 = lean_array_fset(x_8, x_7, x_18);
x_20 = lean_array_get_size(x_4);
x_52 = lean_nat_dec_le(x_20, x_16);
if (x_52 == 0)
{
x_21 = x_10;
goto block_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_5);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_3);
x_54 = l_Lean_indentExpr(x_53);
x_55 = l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__3;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_56, x_9, x_10);
lean_dec(x_9);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
block_51:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_37; 
x_22 = l_Lean_Expr_Inhabited;
x_23 = lean_array_get(x_22, x_4, x_16);
x_37 = l_Lean_Expr_isFVar(x_23);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_5);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_23);
x_39 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__3;
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__6;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_3);
x_44 = l_Lean_indentExpr(x_43);
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_45, x_9, x_21);
lean_dec(x_9);
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
else
{
x_24 = x_21;
goto block_36;
}
block_36:
{
lean_object* x_25; 
lean_inc(x_9);
lean_inc(x_20);
lean_inc(x_23);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_25 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_23, x_20, x_20, x_9, x_24);
lean_dec(x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_7, x_27);
x_29 = x_23;
lean_dec(x_16);
x_30 = lean_array_fset(x_19, x_7, x_29);
lean_dec(x_7);
x_7 = x_28;
x_8 = x_30;
x_10 = x_26;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_10 = l_Lean_Name_inhabited;
x_11 = lean_array_get(x_10, x_2, x_4);
x_12 = l_Lean_mkFVar(x_11);
x_13 = l_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_5, x_9, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_4 = x_15;
x_5 = x_13;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
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
x_22 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_17);
lean_inc(x_5);
lean_inc(x_1);
x_23 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_17, x_18, x_22, x_21, x_12, x_16);
lean_dec(x_18);
lean_dec(x_10);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_1);
x_26 = l_Lean_Meta_getMVarType(x_1, x_12, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 6);
if (x_29 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = l_Lean_MetavarContext_exprDependsOn(x_17, x_27, x_2);
x_84 = lean_unbox(x_83);
lean_dec(x_83);
if (x_84 == 0)
{
x_30 = x_28;
goto block_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_85 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_85, 0, x_3);
x_86 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_87 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_89 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_89, x_12, x_28);
lean_dec(x_12);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
return x_90;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_90);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_dec(x_27);
lean_dec(x_17);
x_30 = x_28;
goto block_82;
}
block_82:
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
lean_inc(x_24);
x_31 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_22, x_24);
x_32 = lean_array_push(x_31, x_2);
x_33 = 1;
x_34 = l_Lean_Meta_revert(x_1, x_32, x_33, x_12, x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_array_get_size(x_24);
x_40 = lean_box(0);
x_41 = 0;
x_42 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_41, x_38, x_39, x_40, x_12, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l_Lean_Meta_intro1(x_46, x_41, x_12, x_44);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
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
x_52 = lean_box(0);
x_53 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_24, x_45, x_24, x_22, x_52);
lean_dec(x_24);
x_54 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_22, x_45);
lean_inc(x_50);
x_55 = l_Lean_mkFVar(x_50);
lean_inc(x_51);
x_56 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_56, 0, x_51);
x_57 = lean_box(x_29);
lean_inc(x_51);
x_58 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_58, 0, x_50);
lean_closure_set(x_58, 1, x_7);
lean_closure_set(x_58, 2, x_3);
lean_closure_set(x_58, 3, x_4);
lean_closure_set(x_58, 4, x_5);
lean_closure_set(x_58, 5, x_6);
lean_closure_set(x_58, 6, x_14);
lean_closure_set(x_58, 7, x_57);
lean_closure_set(x_58, 8, x_37);
lean_closure_set(x_58, 9, x_51);
lean_closure_set(x_58, 10, x_53);
lean_closure_set(x_58, 11, x_54);
lean_closure_set(x_58, 12, x_55);
x_59 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_59, 0, x_56);
lean_closure_set(x_59, 1, x_58);
x_60 = l_Lean_Meta_getMVarDecl(x_51, x_12, x_49);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 4);
lean_inc(x_64);
lean_dec(x_61);
x_65 = l_Lean_Meta_withLocalContext___rarg(x_63, x_64, x_59, x_12, x_62);
lean_dec(x_12);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_59);
lean_dec(x_12);
x_66 = !lean_is_exclusive(x_60);
if (x_66 == 0)
{
return x_60;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_60, 0);
x_68 = lean_ctor_get(x_60, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_60);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_45);
lean_dec(x_37);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_47);
if (x_70 == 0)
{
return x_47;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_47, 0);
x_72 = lean_ctor_get(x_47, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_47);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_37);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_42);
if (x_74 == 0)
{
return x_42;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_42, 0);
x_76 = lean_ctor_get(x_42, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_42);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_34);
if (x_78 == 0)
{
return x_34;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_34, 0);
x_80 = lean_ctor_get(x_34, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_24);
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
x_95 = !lean_is_exclusive(x_26);
if (x_95 == 0)
{
return x_26;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_26, 0);
x_97 = lean_ctor_get(x_26, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_26);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
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
x_99 = !lean_is_exclusive(x_23);
if (x_99 == 0)
{
return x_23;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_23, 0);
x_101 = lean_ctor_get(x_23, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_23);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
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
x_103 = !lean_is_exclusive(x_15);
if (x_103 == 0)
{
return x_15;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_15, 0);
x_105 = lean_ctor_get(x_15, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_15);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
case 1:
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_11);
lean_dec(x_9);
x_107 = lean_ctor_get(x_6, 5);
lean_inc(x_107);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_108 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_107, x_12, x_13);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_6, 6);
lean_inc(x_111);
x_112 = l_List_redLength___main___rarg(x_111);
x_113 = lean_mk_empty_array_with_capacity(x_112);
lean_dec(x_112);
lean_inc(x_111);
x_114 = l_List_toArrayAux___main___rarg(x_111, x_113);
x_115 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_110);
lean_inc(x_5);
lean_inc(x_1);
x_116 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_110, x_111, x_115, x_114, x_12, x_109);
lean_dec(x_111);
lean_dec(x_10);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_1);
x_119 = l_Lean_Meta_getMVarType(x_1, x_12, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 6);
if (x_122 == 0)
{
lean_object* x_176; uint8_t x_177; 
x_176 = l_Lean_MetavarContext_exprDependsOn(x_110, x_120, x_2);
x_177 = lean_unbox(x_176);
lean_dec(x_176);
if (x_177 == 0)
{
x_123 = x_121;
goto block_175;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_dec(x_117);
lean_dec(x_107);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_178 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_178, 0, x_3);
x_179 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_180 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
x_181 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_182 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_183 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_182, x_12, x_121);
lean_dec(x_12);
x_184 = !lean_is_exclusive(x_183);
if (x_184 == 0)
{
return x_183;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_183, 0);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_183);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
lean_dec(x_120);
lean_dec(x_110);
x_123 = x_121;
goto block_175;
}
block_175:
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; 
lean_inc(x_117);
x_124 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_115, x_117);
x_125 = lean_array_push(x_124, x_2);
x_126 = 1;
x_127 = l_Lean_Meta_revert(x_1, x_125, x_126, x_12, x_123);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_array_get_size(x_117);
x_133 = lean_box(0);
x_134 = 0;
x_135 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_134, x_131, x_132, x_133, x_12, x_129);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_140 = l_Lean_Meta_intro1(x_139, x_134, x_12, x_137);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec(x_141);
x_145 = lean_box(0);
x_146 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_117, x_138, x_117, x_115, x_145);
lean_dec(x_117);
x_147 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_115, x_138);
lean_inc(x_143);
x_148 = l_Lean_mkFVar(x_143);
lean_inc(x_144);
x_149 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_149, 0, x_144);
x_150 = lean_box(x_122);
lean_inc(x_144);
x_151 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_151, 0, x_143);
lean_closure_set(x_151, 1, x_7);
lean_closure_set(x_151, 2, x_3);
lean_closure_set(x_151, 3, x_4);
lean_closure_set(x_151, 4, x_5);
lean_closure_set(x_151, 5, x_6);
lean_closure_set(x_151, 6, x_107);
lean_closure_set(x_151, 7, x_150);
lean_closure_set(x_151, 8, x_130);
lean_closure_set(x_151, 9, x_144);
lean_closure_set(x_151, 10, x_146);
lean_closure_set(x_151, 11, x_147);
lean_closure_set(x_151, 12, x_148);
x_152 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_152, 0, x_149);
lean_closure_set(x_152, 1, x_151);
x_153 = l_Lean_Meta_getMVarDecl(x_144, x_12, x_142);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 4);
lean_inc(x_157);
lean_dec(x_154);
x_158 = l_Lean_Meta_withLocalContext___rarg(x_156, x_157, x_152, x_12, x_155);
lean_dec(x_12);
return x_158;
}
else
{
uint8_t x_159; 
lean_dec(x_152);
lean_dec(x_12);
x_159 = !lean_is_exclusive(x_153);
if (x_159 == 0)
{
return x_153;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_153, 0);
x_161 = lean_ctor_get(x_153, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_153);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_138);
lean_dec(x_130);
lean_dec(x_117);
lean_dec(x_107);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_163 = !lean_is_exclusive(x_140);
if (x_163 == 0)
{
return x_140;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_140, 0);
x_165 = lean_ctor_get(x_140, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_140);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_130);
lean_dec(x_117);
lean_dec(x_107);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_167 = !lean_is_exclusive(x_135);
if (x_167 == 0)
{
return x_135;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_135, 0);
x_169 = lean_ctor_get(x_135, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_135);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_117);
lean_dec(x_107);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_171 = !lean_is_exclusive(x_127);
if (x_171 == 0)
{
return x_127;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_127, 0);
x_173 = lean_ctor_get(x_127, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_127);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_117);
lean_dec(x_110);
lean_dec(x_107);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_119);
if (x_188 == 0)
{
return x_119;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_119, 0);
x_190 = lean_ctor_get(x_119, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_119);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_110);
lean_dec(x_107);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_192 = !lean_is_exclusive(x_116);
if (x_192 == 0)
{
return x_116;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_116, 0);
x_194 = lean_ctor_get(x_116, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_116);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_107);
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
x_196 = !lean_is_exclusive(x_108);
if (x_196 == 0)
{
return x_108;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_108, 0);
x_198 = lean_ctor_get(x_108, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_108);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
case 2:
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_11);
lean_dec(x_9);
x_200 = lean_ctor_get(x_6, 5);
lean_inc(x_200);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_201 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_200, x_12, x_13);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec(x_201);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_6, 6);
lean_inc(x_204);
x_205 = l_List_redLength___main___rarg(x_204);
x_206 = lean_mk_empty_array_with_capacity(x_205);
lean_dec(x_205);
lean_inc(x_204);
x_207 = l_List_toArrayAux___main___rarg(x_204, x_206);
x_208 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_203);
lean_inc(x_5);
lean_inc(x_1);
x_209 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_203, x_204, x_208, x_207, x_12, x_202);
lean_dec(x_204);
lean_dec(x_10);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
lean_inc(x_1);
x_212 = l_Lean_Meta_getMVarType(x_1, x_12, x_211);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 6);
if (x_215 == 0)
{
lean_object* x_269; uint8_t x_270; 
x_269 = l_Lean_MetavarContext_exprDependsOn(x_203, x_213, x_2);
x_270 = lean_unbox(x_269);
lean_dec(x_269);
if (x_270 == 0)
{
x_216 = x_214;
goto block_268;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
lean_dec(x_210);
lean_dec(x_200);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_271 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_271, 0, x_3);
x_272 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_273 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_271);
x_274 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_275 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
x_276 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_275, x_12, x_214);
lean_dec(x_12);
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
return x_276;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_276, 0);
x_279 = lean_ctor_get(x_276, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_276);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
return x_280;
}
}
}
else
{
lean_dec(x_213);
lean_dec(x_203);
x_216 = x_214;
goto block_268;
}
block_268:
{
lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; 
lean_inc(x_210);
x_217 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_208, x_210);
x_218 = lean_array_push(x_217, x_2);
x_219 = 1;
x_220 = l_Lean_Meta_revert(x_1, x_218, x_219, x_12, x_216);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; lean_object* x_228; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_ctor_get(x_221, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_dec(x_221);
x_225 = lean_array_get_size(x_210);
x_226 = lean_box(0);
x_227 = 0;
x_228 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_227, x_224, x_225, x_226, x_12, x_222);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_ctor_get(x_229, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
lean_dec(x_229);
x_233 = l_Lean_Meta_intro1(x_232, x_227, x_12, x_230);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_ctor_get(x_234, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
lean_dec(x_234);
x_238 = lean_box(0);
x_239 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_210, x_231, x_210, x_208, x_238);
lean_dec(x_210);
x_240 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_208, x_231);
lean_inc(x_236);
x_241 = l_Lean_mkFVar(x_236);
lean_inc(x_237);
x_242 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_242, 0, x_237);
x_243 = lean_box(x_215);
lean_inc(x_237);
x_244 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_244, 0, x_236);
lean_closure_set(x_244, 1, x_7);
lean_closure_set(x_244, 2, x_3);
lean_closure_set(x_244, 3, x_4);
lean_closure_set(x_244, 4, x_5);
lean_closure_set(x_244, 5, x_6);
lean_closure_set(x_244, 6, x_200);
lean_closure_set(x_244, 7, x_243);
lean_closure_set(x_244, 8, x_223);
lean_closure_set(x_244, 9, x_237);
lean_closure_set(x_244, 10, x_239);
lean_closure_set(x_244, 11, x_240);
lean_closure_set(x_244, 12, x_241);
x_245 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_245, 0, x_242);
lean_closure_set(x_245, 1, x_244);
x_246 = l_Lean_Meta_getMVarDecl(x_237, x_12, x_235);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
x_250 = lean_ctor_get(x_247, 4);
lean_inc(x_250);
lean_dec(x_247);
x_251 = l_Lean_Meta_withLocalContext___rarg(x_249, x_250, x_245, x_12, x_248);
lean_dec(x_12);
return x_251;
}
else
{
uint8_t x_252; 
lean_dec(x_245);
lean_dec(x_12);
x_252 = !lean_is_exclusive(x_246);
if (x_252 == 0)
{
return x_246;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_246, 0);
x_254 = lean_ctor_get(x_246, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_246);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
else
{
uint8_t x_256; 
lean_dec(x_231);
lean_dec(x_223);
lean_dec(x_210);
lean_dec(x_200);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_256 = !lean_is_exclusive(x_233);
if (x_256 == 0)
{
return x_233;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_233, 0);
x_258 = lean_ctor_get(x_233, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_233);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
else
{
uint8_t x_260; 
lean_dec(x_223);
lean_dec(x_210);
lean_dec(x_200);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_260 = !lean_is_exclusive(x_228);
if (x_260 == 0)
{
return x_228;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_228, 0);
x_262 = lean_ctor_get(x_228, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_228);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
else
{
uint8_t x_264; 
lean_dec(x_210);
lean_dec(x_200);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_264 = !lean_is_exclusive(x_220);
if (x_264 == 0)
{
return x_220;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_220, 0);
x_266 = lean_ctor_get(x_220, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_220);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
}
}
else
{
uint8_t x_281; 
lean_dec(x_210);
lean_dec(x_203);
lean_dec(x_200);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_281 = !lean_is_exclusive(x_212);
if (x_281 == 0)
{
return x_212;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_212, 0);
x_283 = lean_ctor_get(x_212, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_212);
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
lean_dec(x_203);
lean_dec(x_200);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_285 = !lean_is_exclusive(x_209);
if (x_285 == 0)
{
return x_209;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_209, 0);
x_287 = lean_ctor_get(x_209, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_209);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
}
else
{
uint8_t x_289; 
lean_dec(x_200);
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
x_289 = !lean_is_exclusive(x_201);
if (x_289 == 0)
{
return x_201;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_201, 0);
x_291 = lean_ctor_get(x_201, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_201);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
case 3:
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_11);
lean_dec(x_9);
x_293 = lean_ctor_get(x_6, 5);
lean_inc(x_293);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_294 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_293, x_12, x_13);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_6, 6);
lean_inc(x_297);
x_298 = l_List_redLength___main___rarg(x_297);
x_299 = lean_mk_empty_array_with_capacity(x_298);
lean_dec(x_298);
lean_inc(x_297);
x_300 = l_List_toArrayAux___main___rarg(x_297, x_299);
x_301 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_296);
lean_inc(x_5);
lean_inc(x_1);
x_302 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_296, x_297, x_301, x_300, x_12, x_295);
lean_dec(x_297);
lean_dec(x_10);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
lean_inc(x_1);
x_305 = l_Lean_Meta_getMVarType(x_1, x_12, x_304);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; uint8_t x_308; lean_object* x_309; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
x_308 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 6);
if (x_308 == 0)
{
lean_object* x_362; uint8_t x_363; 
x_362 = l_Lean_MetavarContext_exprDependsOn(x_296, x_306, x_2);
x_363 = lean_unbox(x_362);
lean_dec(x_362);
if (x_363 == 0)
{
x_309 = x_307;
goto block_361;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; 
lean_dec(x_303);
lean_dec(x_293);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_364 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_364, 0, x_3);
x_365 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_366 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_364);
x_367 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_368 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
x_369 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_368, x_12, x_307);
lean_dec(x_12);
x_370 = !lean_is_exclusive(x_369);
if (x_370 == 0)
{
return x_369;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_369, 0);
x_372 = lean_ctor_get(x_369, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_369);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
return x_373;
}
}
}
else
{
lean_dec(x_306);
lean_dec(x_296);
x_309 = x_307;
goto block_361;
}
block_361:
{
lean_object* x_310; lean_object* x_311; uint8_t x_312; lean_object* x_313; 
lean_inc(x_303);
x_310 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_301, x_303);
x_311 = lean_array_push(x_310, x_2);
x_312 = 1;
x_313 = l_Lean_Meta_revert(x_1, x_311, x_312, x_12, x_309);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = lean_ctor_get(x_314, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_314, 1);
lean_inc(x_317);
lean_dec(x_314);
x_318 = lean_array_get_size(x_303);
x_319 = lean_box(0);
x_320 = 0;
x_321 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_320, x_317, x_318, x_319, x_12, x_315);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
x_324 = lean_ctor_get(x_322, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_322, 1);
lean_inc(x_325);
lean_dec(x_322);
x_326 = l_Lean_Meta_intro1(x_325, x_320, x_12, x_323);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
x_329 = lean_ctor_get(x_327, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_327, 1);
lean_inc(x_330);
lean_dec(x_327);
x_331 = lean_box(0);
x_332 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_303, x_324, x_303, x_301, x_331);
lean_dec(x_303);
x_333 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_301, x_324);
lean_inc(x_329);
x_334 = l_Lean_mkFVar(x_329);
lean_inc(x_330);
x_335 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_335, 0, x_330);
x_336 = lean_box(x_308);
lean_inc(x_330);
x_337 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_337, 0, x_329);
lean_closure_set(x_337, 1, x_7);
lean_closure_set(x_337, 2, x_3);
lean_closure_set(x_337, 3, x_4);
lean_closure_set(x_337, 4, x_5);
lean_closure_set(x_337, 5, x_6);
lean_closure_set(x_337, 6, x_293);
lean_closure_set(x_337, 7, x_336);
lean_closure_set(x_337, 8, x_316);
lean_closure_set(x_337, 9, x_330);
lean_closure_set(x_337, 10, x_332);
lean_closure_set(x_337, 11, x_333);
lean_closure_set(x_337, 12, x_334);
x_338 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_338, 0, x_335);
lean_closure_set(x_338, 1, x_337);
x_339 = l_Lean_Meta_getMVarDecl(x_330, x_12, x_328);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec(x_339);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
x_343 = lean_ctor_get(x_340, 4);
lean_inc(x_343);
lean_dec(x_340);
x_344 = l_Lean_Meta_withLocalContext___rarg(x_342, x_343, x_338, x_12, x_341);
lean_dec(x_12);
return x_344;
}
else
{
uint8_t x_345; 
lean_dec(x_338);
lean_dec(x_12);
x_345 = !lean_is_exclusive(x_339);
if (x_345 == 0)
{
return x_339;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_339, 0);
x_347 = lean_ctor_get(x_339, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_339);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
}
else
{
uint8_t x_349; 
lean_dec(x_324);
lean_dec(x_316);
lean_dec(x_303);
lean_dec(x_293);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_349 = !lean_is_exclusive(x_326);
if (x_349 == 0)
{
return x_326;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_326, 0);
x_351 = lean_ctor_get(x_326, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_326);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
return x_352;
}
}
}
else
{
uint8_t x_353; 
lean_dec(x_316);
lean_dec(x_303);
lean_dec(x_293);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_353 = !lean_is_exclusive(x_321);
if (x_353 == 0)
{
return x_321;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_321, 0);
x_355 = lean_ctor_get(x_321, 1);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_321);
x_356 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
return x_356;
}
}
}
else
{
uint8_t x_357; 
lean_dec(x_303);
lean_dec(x_293);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_357 = !lean_is_exclusive(x_313);
if (x_357 == 0)
{
return x_313;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_313, 0);
x_359 = lean_ctor_get(x_313, 1);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_313);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_359);
return x_360;
}
}
}
}
else
{
uint8_t x_374; 
lean_dec(x_303);
lean_dec(x_296);
lean_dec(x_293);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_374 = !lean_is_exclusive(x_305);
if (x_374 == 0)
{
return x_305;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_305, 0);
x_376 = lean_ctor_get(x_305, 1);
lean_inc(x_376);
lean_inc(x_375);
lean_dec(x_305);
x_377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
return x_377;
}
}
}
else
{
uint8_t x_378; 
lean_dec(x_296);
lean_dec(x_293);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_378 = !lean_is_exclusive(x_302);
if (x_378 == 0)
{
return x_302;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_302, 0);
x_380 = lean_ctor_get(x_302, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_302);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
return x_381;
}
}
}
else
{
uint8_t x_382; 
lean_dec(x_293);
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
x_382 = !lean_is_exclusive(x_294);
if (x_382 == 0)
{
return x_294;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_294, 0);
x_384 = lean_ctor_get(x_294, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_294);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
return x_385;
}
}
}
case 4:
{
lean_object* x_386; lean_object* x_387; 
lean_dec(x_11);
lean_dec(x_9);
x_386 = lean_ctor_get(x_6, 5);
lean_inc(x_386);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_387 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_386, x_12, x_13);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
lean_dec(x_387);
x_389 = lean_ctor_get(x_388, 1);
lean_inc(x_389);
x_390 = lean_ctor_get(x_6, 6);
lean_inc(x_390);
x_391 = l_List_redLength___main___rarg(x_390);
x_392 = lean_mk_empty_array_with_capacity(x_391);
lean_dec(x_391);
lean_inc(x_390);
x_393 = l_List_toArrayAux___main___rarg(x_390, x_392);
x_394 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_389);
lean_inc(x_5);
lean_inc(x_1);
x_395 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_389, x_390, x_394, x_393, x_12, x_388);
lean_dec(x_390);
lean_dec(x_10);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
lean_inc(x_1);
x_398 = l_Lean_Meta_getMVarType(x_1, x_12, x_397);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_402; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 6);
if (x_401 == 0)
{
lean_object* x_455; uint8_t x_456; 
x_455 = l_Lean_MetavarContext_exprDependsOn(x_389, x_399, x_2);
x_456 = lean_unbox(x_455);
lean_dec(x_455);
if (x_456 == 0)
{
x_402 = x_400;
goto block_454;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; 
lean_dec(x_396);
lean_dec(x_386);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_457 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_457, 0, x_3);
x_458 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_459 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_457);
x_460 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_461 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
x_462 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_461, x_12, x_400);
lean_dec(x_12);
x_463 = !lean_is_exclusive(x_462);
if (x_463 == 0)
{
return x_462;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_462, 0);
x_465 = lean_ctor_get(x_462, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_462);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
}
}
else
{
lean_dec(x_399);
lean_dec(x_389);
x_402 = x_400;
goto block_454;
}
block_454:
{
lean_object* x_403; lean_object* x_404; uint8_t x_405; lean_object* x_406; 
lean_inc(x_396);
x_403 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_394, x_396);
x_404 = lean_array_push(x_403, x_2);
x_405 = 1;
x_406 = l_Lean_Meta_revert(x_1, x_404, x_405, x_12, x_402);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; lean_object* x_414; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
lean_dec(x_406);
x_409 = lean_ctor_get(x_407, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_407, 1);
lean_inc(x_410);
lean_dec(x_407);
x_411 = lean_array_get_size(x_396);
x_412 = lean_box(0);
x_413 = 0;
x_414 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_413, x_410, x_411, x_412, x_12, x_408);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_417 = lean_ctor_get(x_415, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_415, 1);
lean_inc(x_418);
lean_dec(x_415);
x_419 = l_Lean_Meta_intro1(x_418, x_413, x_12, x_416);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
x_422 = lean_ctor_get(x_420, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_420, 1);
lean_inc(x_423);
lean_dec(x_420);
x_424 = lean_box(0);
x_425 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_396, x_417, x_396, x_394, x_424);
lean_dec(x_396);
x_426 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_394, x_417);
lean_inc(x_422);
x_427 = l_Lean_mkFVar(x_422);
lean_inc(x_423);
x_428 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_428, 0, x_423);
x_429 = lean_box(x_401);
lean_inc(x_423);
x_430 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_430, 0, x_422);
lean_closure_set(x_430, 1, x_7);
lean_closure_set(x_430, 2, x_3);
lean_closure_set(x_430, 3, x_4);
lean_closure_set(x_430, 4, x_5);
lean_closure_set(x_430, 5, x_6);
lean_closure_set(x_430, 6, x_386);
lean_closure_set(x_430, 7, x_429);
lean_closure_set(x_430, 8, x_409);
lean_closure_set(x_430, 9, x_423);
lean_closure_set(x_430, 10, x_425);
lean_closure_set(x_430, 11, x_426);
lean_closure_set(x_430, 12, x_427);
x_431 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_431, 0, x_428);
lean_closure_set(x_431, 1, x_430);
x_432 = l_Lean_Meta_getMVarDecl(x_423, x_12, x_421);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
lean_dec(x_432);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_433, 4);
lean_inc(x_436);
lean_dec(x_433);
x_437 = l_Lean_Meta_withLocalContext___rarg(x_435, x_436, x_431, x_12, x_434);
lean_dec(x_12);
return x_437;
}
else
{
uint8_t x_438; 
lean_dec(x_431);
lean_dec(x_12);
x_438 = !lean_is_exclusive(x_432);
if (x_438 == 0)
{
return x_432;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_439 = lean_ctor_get(x_432, 0);
x_440 = lean_ctor_get(x_432, 1);
lean_inc(x_440);
lean_inc(x_439);
lean_dec(x_432);
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
return x_441;
}
}
}
else
{
uint8_t x_442; 
lean_dec(x_417);
lean_dec(x_409);
lean_dec(x_396);
lean_dec(x_386);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_442 = !lean_is_exclusive(x_419);
if (x_442 == 0)
{
return x_419;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_419, 0);
x_444 = lean_ctor_get(x_419, 1);
lean_inc(x_444);
lean_inc(x_443);
lean_dec(x_419);
x_445 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
return x_445;
}
}
}
else
{
uint8_t x_446; 
lean_dec(x_409);
lean_dec(x_396);
lean_dec(x_386);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_446 = !lean_is_exclusive(x_414);
if (x_446 == 0)
{
return x_414;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_ctor_get(x_414, 0);
x_448 = lean_ctor_get(x_414, 1);
lean_inc(x_448);
lean_inc(x_447);
lean_dec(x_414);
x_449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_449, 0, x_447);
lean_ctor_set(x_449, 1, x_448);
return x_449;
}
}
}
else
{
uint8_t x_450; 
lean_dec(x_396);
lean_dec(x_386);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_450 = !lean_is_exclusive(x_406);
if (x_450 == 0)
{
return x_406;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_451 = lean_ctor_get(x_406, 0);
x_452 = lean_ctor_get(x_406, 1);
lean_inc(x_452);
lean_inc(x_451);
lean_dec(x_406);
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_451);
lean_ctor_set(x_453, 1, x_452);
return x_453;
}
}
}
}
else
{
uint8_t x_467; 
lean_dec(x_396);
lean_dec(x_389);
lean_dec(x_386);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_467 = !lean_is_exclusive(x_398);
if (x_467 == 0)
{
return x_398;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_468 = lean_ctor_get(x_398, 0);
x_469 = lean_ctor_get(x_398, 1);
lean_inc(x_469);
lean_inc(x_468);
lean_dec(x_398);
x_470 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_470, 0, x_468);
lean_ctor_set(x_470, 1, x_469);
return x_470;
}
}
}
else
{
uint8_t x_471; 
lean_dec(x_389);
lean_dec(x_386);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_471 = !lean_is_exclusive(x_395);
if (x_471 == 0)
{
return x_395;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_395, 0);
x_473 = lean_ctor_get(x_395, 1);
lean_inc(x_473);
lean_inc(x_472);
lean_dec(x_395);
x_474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set(x_474, 1, x_473);
return x_474;
}
}
}
else
{
uint8_t x_475; 
lean_dec(x_386);
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
x_475 = !lean_is_exclusive(x_387);
if (x_475 == 0)
{
return x_387;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_387, 0);
x_477 = lean_ctor_get(x_387, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_387);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
}
}
case 5:
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_479 = lean_ctor_get(x_9, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_9, 1);
lean_inc(x_480);
lean_dec(x_9);
x_481 = lean_array_set(x_10, x_11, x_480);
x_482 = lean_unsigned_to_nat(1u);
x_483 = lean_nat_sub(x_11, x_482);
lean_dec(x_11);
x_9 = x_479;
x_10 = x_481;
x_11 = x_483;
goto _start;
}
case 6:
{
lean_object* x_485; lean_object* x_486; 
lean_dec(x_11);
lean_dec(x_9);
x_485 = lean_ctor_get(x_6, 5);
lean_inc(x_485);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_486 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_485, x_12, x_13);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_487 = lean_ctor_get(x_486, 1);
lean_inc(x_487);
lean_dec(x_486);
x_488 = lean_ctor_get(x_487, 1);
lean_inc(x_488);
x_489 = lean_ctor_get(x_6, 6);
lean_inc(x_489);
x_490 = l_List_redLength___main___rarg(x_489);
x_491 = lean_mk_empty_array_with_capacity(x_490);
lean_dec(x_490);
lean_inc(x_489);
x_492 = l_List_toArrayAux___main___rarg(x_489, x_491);
x_493 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_488);
lean_inc(x_5);
lean_inc(x_1);
x_494 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_488, x_489, x_493, x_492, x_12, x_487);
lean_dec(x_489);
lean_dec(x_10);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
lean_inc(x_1);
x_497 = l_Lean_Meta_getMVarType(x_1, x_12, x_496);
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_498; lean_object* x_499; uint8_t x_500; lean_object* x_501; 
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
lean_dec(x_497);
x_500 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 6);
if (x_500 == 0)
{
lean_object* x_554; uint8_t x_555; 
x_554 = l_Lean_MetavarContext_exprDependsOn(x_488, x_498, x_2);
x_555 = lean_unbox(x_554);
lean_dec(x_554);
if (x_555 == 0)
{
x_501 = x_499;
goto block_553;
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; uint8_t x_562; 
lean_dec(x_495);
lean_dec(x_485);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_556 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_556, 0, x_3);
x_557 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_558 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_558, 0, x_557);
lean_ctor_set(x_558, 1, x_556);
x_559 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_560 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_560, 0, x_558);
lean_ctor_set(x_560, 1, x_559);
x_561 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_560, x_12, x_499);
lean_dec(x_12);
x_562 = !lean_is_exclusive(x_561);
if (x_562 == 0)
{
return x_561;
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_563 = lean_ctor_get(x_561, 0);
x_564 = lean_ctor_get(x_561, 1);
lean_inc(x_564);
lean_inc(x_563);
lean_dec(x_561);
x_565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_565, 0, x_563);
lean_ctor_set(x_565, 1, x_564);
return x_565;
}
}
}
else
{
lean_dec(x_498);
lean_dec(x_488);
x_501 = x_499;
goto block_553;
}
block_553:
{
lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; 
lean_inc(x_495);
x_502 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_493, x_495);
x_503 = lean_array_push(x_502, x_2);
x_504 = 1;
x_505 = l_Lean_Meta_revert(x_1, x_503, x_504, x_12, x_501);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; uint8_t x_512; lean_object* x_513; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
x_508 = lean_ctor_get(x_506, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_506, 1);
lean_inc(x_509);
lean_dec(x_506);
x_510 = lean_array_get_size(x_495);
x_511 = lean_box(0);
x_512 = 0;
x_513 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_512, x_509, x_510, x_511, x_12, x_507);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
x_516 = lean_ctor_get(x_514, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_514, 1);
lean_inc(x_517);
lean_dec(x_514);
x_518 = l_Lean_Meta_intro1(x_517, x_512, x_12, x_515);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_518, 1);
lean_inc(x_520);
lean_dec(x_518);
x_521 = lean_ctor_get(x_519, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_519, 1);
lean_inc(x_522);
lean_dec(x_519);
x_523 = lean_box(0);
x_524 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_495, x_516, x_495, x_493, x_523);
lean_dec(x_495);
x_525 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_493, x_516);
lean_inc(x_521);
x_526 = l_Lean_mkFVar(x_521);
lean_inc(x_522);
x_527 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_527, 0, x_522);
x_528 = lean_box(x_500);
lean_inc(x_522);
x_529 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_529, 0, x_521);
lean_closure_set(x_529, 1, x_7);
lean_closure_set(x_529, 2, x_3);
lean_closure_set(x_529, 3, x_4);
lean_closure_set(x_529, 4, x_5);
lean_closure_set(x_529, 5, x_6);
lean_closure_set(x_529, 6, x_485);
lean_closure_set(x_529, 7, x_528);
lean_closure_set(x_529, 8, x_508);
lean_closure_set(x_529, 9, x_522);
lean_closure_set(x_529, 10, x_524);
lean_closure_set(x_529, 11, x_525);
lean_closure_set(x_529, 12, x_526);
x_530 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_530, 0, x_527);
lean_closure_set(x_530, 1, x_529);
x_531 = l_Lean_Meta_getMVarDecl(x_522, x_12, x_520);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
lean_dec(x_531);
x_534 = lean_ctor_get(x_532, 1);
lean_inc(x_534);
x_535 = lean_ctor_get(x_532, 4);
lean_inc(x_535);
lean_dec(x_532);
x_536 = l_Lean_Meta_withLocalContext___rarg(x_534, x_535, x_530, x_12, x_533);
lean_dec(x_12);
return x_536;
}
else
{
uint8_t x_537; 
lean_dec(x_530);
lean_dec(x_12);
x_537 = !lean_is_exclusive(x_531);
if (x_537 == 0)
{
return x_531;
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_538 = lean_ctor_get(x_531, 0);
x_539 = lean_ctor_get(x_531, 1);
lean_inc(x_539);
lean_inc(x_538);
lean_dec(x_531);
x_540 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_540, 0, x_538);
lean_ctor_set(x_540, 1, x_539);
return x_540;
}
}
}
else
{
uint8_t x_541; 
lean_dec(x_516);
lean_dec(x_508);
lean_dec(x_495);
lean_dec(x_485);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_541 = !lean_is_exclusive(x_518);
if (x_541 == 0)
{
return x_518;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_ctor_get(x_518, 0);
x_543 = lean_ctor_get(x_518, 1);
lean_inc(x_543);
lean_inc(x_542);
lean_dec(x_518);
x_544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_543);
return x_544;
}
}
}
else
{
uint8_t x_545; 
lean_dec(x_508);
lean_dec(x_495);
lean_dec(x_485);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_545 = !lean_is_exclusive(x_513);
if (x_545 == 0)
{
return x_513;
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_546 = lean_ctor_get(x_513, 0);
x_547 = lean_ctor_get(x_513, 1);
lean_inc(x_547);
lean_inc(x_546);
lean_dec(x_513);
x_548 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_548, 0, x_546);
lean_ctor_set(x_548, 1, x_547);
return x_548;
}
}
}
else
{
uint8_t x_549; 
lean_dec(x_495);
lean_dec(x_485);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_549 = !lean_is_exclusive(x_505);
if (x_549 == 0)
{
return x_505;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_505, 0);
x_551 = lean_ctor_get(x_505, 1);
lean_inc(x_551);
lean_inc(x_550);
lean_dec(x_505);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
return x_552;
}
}
}
}
else
{
uint8_t x_566; 
lean_dec(x_495);
lean_dec(x_488);
lean_dec(x_485);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_566 = !lean_is_exclusive(x_497);
if (x_566 == 0)
{
return x_497;
}
else
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_567 = lean_ctor_get(x_497, 0);
x_568 = lean_ctor_get(x_497, 1);
lean_inc(x_568);
lean_inc(x_567);
lean_dec(x_497);
x_569 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_569, 0, x_567);
lean_ctor_set(x_569, 1, x_568);
return x_569;
}
}
}
else
{
uint8_t x_570; 
lean_dec(x_488);
lean_dec(x_485);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_570 = !lean_is_exclusive(x_494);
if (x_570 == 0)
{
return x_494;
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_571 = lean_ctor_get(x_494, 0);
x_572 = lean_ctor_get(x_494, 1);
lean_inc(x_572);
lean_inc(x_571);
lean_dec(x_494);
x_573 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_573, 0, x_571);
lean_ctor_set(x_573, 1, x_572);
return x_573;
}
}
}
else
{
uint8_t x_574; 
lean_dec(x_485);
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
x_574 = !lean_is_exclusive(x_486);
if (x_574 == 0)
{
return x_486;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_575 = lean_ctor_get(x_486, 0);
x_576 = lean_ctor_get(x_486, 1);
lean_inc(x_576);
lean_inc(x_575);
lean_dec(x_486);
x_577 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_577, 0, x_575);
lean_ctor_set(x_577, 1, x_576);
return x_577;
}
}
}
case 7:
{
lean_object* x_578; lean_object* x_579; 
lean_dec(x_11);
lean_dec(x_9);
x_578 = lean_ctor_get(x_6, 5);
lean_inc(x_578);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_579 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_578, x_12, x_13);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_580 = lean_ctor_get(x_579, 1);
lean_inc(x_580);
lean_dec(x_579);
x_581 = lean_ctor_get(x_580, 1);
lean_inc(x_581);
x_582 = lean_ctor_get(x_6, 6);
lean_inc(x_582);
x_583 = l_List_redLength___main___rarg(x_582);
x_584 = lean_mk_empty_array_with_capacity(x_583);
lean_dec(x_583);
lean_inc(x_582);
x_585 = l_List_toArrayAux___main___rarg(x_582, x_584);
x_586 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_581);
lean_inc(x_5);
lean_inc(x_1);
x_587 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_581, x_582, x_586, x_585, x_12, x_580);
lean_dec(x_582);
lean_dec(x_10);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
lean_dec(x_587);
lean_inc(x_1);
x_590 = l_Lean_Meta_getMVarType(x_1, x_12, x_589);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; uint8_t x_593; lean_object* x_594; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_590, 1);
lean_inc(x_592);
lean_dec(x_590);
x_593 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 6);
if (x_593 == 0)
{
lean_object* x_647; uint8_t x_648; 
x_647 = l_Lean_MetavarContext_exprDependsOn(x_581, x_591, x_2);
x_648 = lean_unbox(x_647);
lean_dec(x_647);
if (x_648 == 0)
{
x_594 = x_592;
goto block_646;
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; uint8_t x_655; 
lean_dec(x_588);
lean_dec(x_578);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_649 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_649, 0, x_3);
x_650 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_651 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_651, 0, x_650);
lean_ctor_set(x_651, 1, x_649);
x_652 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_653 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_653, 0, x_651);
lean_ctor_set(x_653, 1, x_652);
x_654 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_653, x_12, x_592);
lean_dec(x_12);
x_655 = !lean_is_exclusive(x_654);
if (x_655 == 0)
{
return x_654;
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_656 = lean_ctor_get(x_654, 0);
x_657 = lean_ctor_get(x_654, 1);
lean_inc(x_657);
lean_inc(x_656);
lean_dec(x_654);
x_658 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_658, 0, x_656);
lean_ctor_set(x_658, 1, x_657);
return x_658;
}
}
}
else
{
lean_dec(x_591);
lean_dec(x_581);
x_594 = x_592;
goto block_646;
}
block_646:
{
lean_object* x_595; lean_object* x_596; uint8_t x_597; lean_object* x_598; 
lean_inc(x_588);
x_595 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_586, x_588);
x_596 = lean_array_push(x_595, x_2);
x_597 = 1;
x_598 = l_Lean_Meta_revert(x_1, x_596, x_597, x_12, x_594);
if (lean_obj_tag(x_598) == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; uint8_t x_605; lean_object* x_606; 
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
lean_dec(x_598);
x_601 = lean_ctor_get(x_599, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_599, 1);
lean_inc(x_602);
lean_dec(x_599);
x_603 = lean_array_get_size(x_588);
x_604 = lean_box(0);
x_605 = 0;
x_606 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_605, x_602, x_603, x_604, x_12, x_600);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
lean_dec(x_606);
x_609 = lean_ctor_get(x_607, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_607, 1);
lean_inc(x_610);
lean_dec(x_607);
x_611 = l_Lean_Meta_intro1(x_610, x_605, x_12, x_608);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_611, 1);
lean_inc(x_613);
lean_dec(x_611);
x_614 = lean_ctor_get(x_612, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_612, 1);
lean_inc(x_615);
lean_dec(x_612);
x_616 = lean_box(0);
x_617 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_588, x_609, x_588, x_586, x_616);
lean_dec(x_588);
x_618 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_586, x_609);
lean_inc(x_614);
x_619 = l_Lean_mkFVar(x_614);
lean_inc(x_615);
x_620 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_620, 0, x_615);
x_621 = lean_box(x_593);
lean_inc(x_615);
x_622 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_622, 0, x_614);
lean_closure_set(x_622, 1, x_7);
lean_closure_set(x_622, 2, x_3);
lean_closure_set(x_622, 3, x_4);
lean_closure_set(x_622, 4, x_5);
lean_closure_set(x_622, 5, x_6);
lean_closure_set(x_622, 6, x_578);
lean_closure_set(x_622, 7, x_621);
lean_closure_set(x_622, 8, x_601);
lean_closure_set(x_622, 9, x_615);
lean_closure_set(x_622, 10, x_617);
lean_closure_set(x_622, 11, x_618);
lean_closure_set(x_622, 12, x_619);
x_623 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_623, 0, x_620);
lean_closure_set(x_623, 1, x_622);
x_624 = l_Lean_Meta_getMVarDecl(x_615, x_12, x_613);
if (lean_obj_tag(x_624) == 0)
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_624, 1);
lean_inc(x_626);
lean_dec(x_624);
x_627 = lean_ctor_get(x_625, 1);
lean_inc(x_627);
x_628 = lean_ctor_get(x_625, 4);
lean_inc(x_628);
lean_dec(x_625);
x_629 = l_Lean_Meta_withLocalContext___rarg(x_627, x_628, x_623, x_12, x_626);
lean_dec(x_12);
return x_629;
}
else
{
uint8_t x_630; 
lean_dec(x_623);
lean_dec(x_12);
x_630 = !lean_is_exclusive(x_624);
if (x_630 == 0)
{
return x_624;
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_631 = lean_ctor_get(x_624, 0);
x_632 = lean_ctor_get(x_624, 1);
lean_inc(x_632);
lean_inc(x_631);
lean_dec(x_624);
x_633 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_633, 0, x_631);
lean_ctor_set(x_633, 1, x_632);
return x_633;
}
}
}
else
{
uint8_t x_634; 
lean_dec(x_609);
lean_dec(x_601);
lean_dec(x_588);
lean_dec(x_578);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_634 = !lean_is_exclusive(x_611);
if (x_634 == 0)
{
return x_611;
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_635 = lean_ctor_get(x_611, 0);
x_636 = lean_ctor_get(x_611, 1);
lean_inc(x_636);
lean_inc(x_635);
lean_dec(x_611);
x_637 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_637, 0, x_635);
lean_ctor_set(x_637, 1, x_636);
return x_637;
}
}
}
else
{
uint8_t x_638; 
lean_dec(x_601);
lean_dec(x_588);
lean_dec(x_578);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_638 = !lean_is_exclusive(x_606);
if (x_638 == 0)
{
return x_606;
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_639 = lean_ctor_get(x_606, 0);
x_640 = lean_ctor_get(x_606, 1);
lean_inc(x_640);
lean_inc(x_639);
lean_dec(x_606);
x_641 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_641, 0, x_639);
lean_ctor_set(x_641, 1, x_640);
return x_641;
}
}
}
else
{
uint8_t x_642; 
lean_dec(x_588);
lean_dec(x_578);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_642 = !lean_is_exclusive(x_598);
if (x_642 == 0)
{
return x_598;
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_643 = lean_ctor_get(x_598, 0);
x_644 = lean_ctor_get(x_598, 1);
lean_inc(x_644);
lean_inc(x_643);
lean_dec(x_598);
x_645 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_645, 0, x_643);
lean_ctor_set(x_645, 1, x_644);
return x_645;
}
}
}
}
else
{
uint8_t x_659; 
lean_dec(x_588);
lean_dec(x_581);
lean_dec(x_578);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_659 = !lean_is_exclusive(x_590);
if (x_659 == 0)
{
return x_590;
}
else
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; 
x_660 = lean_ctor_get(x_590, 0);
x_661 = lean_ctor_get(x_590, 1);
lean_inc(x_661);
lean_inc(x_660);
lean_dec(x_590);
x_662 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_662, 0, x_660);
lean_ctor_set(x_662, 1, x_661);
return x_662;
}
}
}
else
{
uint8_t x_663; 
lean_dec(x_581);
lean_dec(x_578);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_663 = !lean_is_exclusive(x_587);
if (x_663 == 0)
{
return x_587;
}
else
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_664 = lean_ctor_get(x_587, 0);
x_665 = lean_ctor_get(x_587, 1);
lean_inc(x_665);
lean_inc(x_664);
lean_dec(x_587);
x_666 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_666, 0, x_664);
lean_ctor_set(x_666, 1, x_665);
return x_666;
}
}
}
else
{
uint8_t x_667; 
lean_dec(x_578);
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
x_667 = !lean_is_exclusive(x_579);
if (x_667 == 0)
{
return x_579;
}
else
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; 
x_668 = lean_ctor_get(x_579, 0);
x_669 = lean_ctor_get(x_579, 1);
lean_inc(x_669);
lean_inc(x_668);
lean_dec(x_579);
x_670 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_670, 0, x_668);
lean_ctor_set(x_670, 1, x_669);
return x_670;
}
}
}
case 8:
{
lean_object* x_671; lean_object* x_672; 
lean_dec(x_11);
lean_dec(x_9);
x_671 = lean_ctor_get(x_6, 5);
lean_inc(x_671);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_672 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_671, x_12, x_13);
if (lean_obj_tag(x_672) == 0)
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_673 = lean_ctor_get(x_672, 1);
lean_inc(x_673);
lean_dec(x_672);
x_674 = lean_ctor_get(x_673, 1);
lean_inc(x_674);
x_675 = lean_ctor_get(x_6, 6);
lean_inc(x_675);
x_676 = l_List_redLength___main___rarg(x_675);
x_677 = lean_mk_empty_array_with_capacity(x_676);
lean_dec(x_676);
lean_inc(x_675);
x_678 = l_List_toArrayAux___main___rarg(x_675, x_677);
x_679 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_674);
lean_inc(x_5);
lean_inc(x_1);
x_680 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_674, x_675, x_679, x_678, x_12, x_673);
lean_dec(x_675);
lean_dec(x_10);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
lean_dec(x_680);
lean_inc(x_1);
x_683 = l_Lean_Meta_getMVarType(x_1, x_12, x_682);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; lean_object* x_685; uint8_t x_686; lean_object* x_687; 
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_683, 1);
lean_inc(x_685);
lean_dec(x_683);
x_686 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 6);
if (x_686 == 0)
{
lean_object* x_740; uint8_t x_741; 
x_740 = l_Lean_MetavarContext_exprDependsOn(x_674, x_684, x_2);
x_741 = lean_unbox(x_740);
lean_dec(x_740);
if (x_741 == 0)
{
x_687 = x_685;
goto block_739;
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; uint8_t x_748; 
lean_dec(x_681);
lean_dec(x_671);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_742 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_742, 0, x_3);
x_743 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_744 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_744, 0, x_743);
lean_ctor_set(x_744, 1, x_742);
x_745 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_746 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_746, 0, x_744);
lean_ctor_set(x_746, 1, x_745);
x_747 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_746, x_12, x_685);
lean_dec(x_12);
x_748 = !lean_is_exclusive(x_747);
if (x_748 == 0)
{
return x_747;
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; 
x_749 = lean_ctor_get(x_747, 0);
x_750 = lean_ctor_get(x_747, 1);
lean_inc(x_750);
lean_inc(x_749);
lean_dec(x_747);
x_751 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_751, 0, x_749);
lean_ctor_set(x_751, 1, x_750);
return x_751;
}
}
}
else
{
lean_dec(x_684);
lean_dec(x_674);
x_687 = x_685;
goto block_739;
}
block_739:
{
lean_object* x_688; lean_object* x_689; uint8_t x_690; lean_object* x_691; 
lean_inc(x_681);
x_688 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_679, x_681);
x_689 = lean_array_push(x_688, x_2);
x_690 = 1;
x_691 = l_Lean_Meta_revert(x_1, x_689, x_690, x_12, x_687);
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; uint8_t x_698; lean_object* x_699; 
x_692 = lean_ctor_get(x_691, 0);
lean_inc(x_692);
x_693 = lean_ctor_get(x_691, 1);
lean_inc(x_693);
lean_dec(x_691);
x_694 = lean_ctor_get(x_692, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_692, 1);
lean_inc(x_695);
lean_dec(x_692);
x_696 = lean_array_get_size(x_681);
x_697 = lean_box(0);
x_698 = 0;
x_699 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_698, x_695, x_696, x_697, x_12, x_693);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_699, 1);
lean_inc(x_701);
lean_dec(x_699);
x_702 = lean_ctor_get(x_700, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_700, 1);
lean_inc(x_703);
lean_dec(x_700);
x_704 = l_Lean_Meta_intro1(x_703, x_698, x_12, x_701);
if (lean_obj_tag(x_704) == 0)
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_705 = lean_ctor_get(x_704, 0);
lean_inc(x_705);
x_706 = lean_ctor_get(x_704, 1);
lean_inc(x_706);
lean_dec(x_704);
x_707 = lean_ctor_get(x_705, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_705, 1);
lean_inc(x_708);
lean_dec(x_705);
x_709 = lean_box(0);
x_710 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_681, x_702, x_681, x_679, x_709);
lean_dec(x_681);
x_711 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_679, x_702);
lean_inc(x_707);
x_712 = l_Lean_mkFVar(x_707);
lean_inc(x_708);
x_713 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_713, 0, x_708);
x_714 = lean_box(x_686);
lean_inc(x_708);
x_715 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_715, 0, x_707);
lean_closure_set(x_715, 1, x_7);
lean_closure_set(x_715, 2, x_3);
lean_closure_set(x_715, 3, x_4);
lean_closure_set(x_715, 4, x_5);
lean_closure_set(x_715, 5, x_6);
lean_closure_set(x_715, 6, x_671);
lean_closure_set(x_715, 7, x_714);
lean_closure_set(x_715, 8, x_694);
lean_closure_set(x_715, 9, x_708);
lean_closure_set(x_715, 10, x_710);
lean_closure_set(x_715, 11, x_711);
lean_closure_set(x_715, 12, x_712);
x_716 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_716, 0, x_713);
lean_closure_set(x_716, 1, x_715);
x_717 = l_Lean_Meta_getMVarDecl(x_708, x_12, x_706);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_717, 1);
lean_inc(x_719);
lean_dec(x_717);
x_720 = lean_ctor_get(x_718, 1);
lean_inc(x_720);
x_721 = lean_ctor_get(x_718, 4);
lean_inc(x_721);
lean_dec(x_718);
x_722 = l_Lean_Meta_withLocalContext___rarg(x_720, x_721, x_716, x_12, x_719);
lean_dec(x_12);
return x_722;
}
else
{
uint8_t x_723; 
lean_dec(x_716);
lean_dec(x_12);
x_723 = !lean_is_exclusive(x_717);
if (x_723 == 0)
{
return x_717;
}
else
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_724 = lean_ctor_get(x_717, 0);
x_725 = lean_ctor_get(x_717, 1);
lean_inc(x_725);
lean_inc(x_724);
lean_dec(x_717);
x_726 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_726, 0, x_724);
lean_ctor_set(x_726, 1, x_725);
return x_726;
}
}
}
else
{
uint8_t x_727; 
lean_dec(x_702);
lean_dec(x_694);
lean_dec(x_681);
lean_dec(x_671);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_727 = !lean_is_exclusive(x_704);
if (x_727 == 0)
{
return x_704;
}
else
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_728 = lean_ctor_get(x_704, 0);
x_729 = lean_ctor_get(x_704, 1);
lean_inc(x_729);
lean_inc(x_728);
lean_dec(x_704);
x_730 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_730, 0, x_728);
lean_ctor_set(x_730, 1, x_729);
return x_730;
}
}
}
else
{
uint8_t x_731; 
lean_dec(x_694);
lean_dec(x_681);
lean_dec(x_671);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_731 = !lean_is_exclusive(x_699);
if (x_731 == 0)
{
return x_699;
}
else
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_732 = lean_ctor_get(x_699, 0);
x_733 = lean_ctor_get(x_699, 1);
lean_inc(x_733);
lean_inc(x_732);
lean_dec(x_699);
x_734 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_734, 0, x_732);
lean_ctor_set(x_734, 1, x_733);
return x_734;
}
}
}
else
{
uint8_t x_735; 
lean_dec(x_681);
lean_dec(x_671);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_735 = !lean_is_exclusive(x_691);
if (x_735 == 0)
{
return x_691;
}
else
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_736 = lean_ctor_get(x_691, 0);
x_737 = lean_ctor_get(x_691, 1);
lean_inc(x_737);
lean_inc(x_736);
lean_dec(x_691);
x_738 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_738, 0, x_736);
lean_ctor_set(x_738, 1, x_737);
return x_738;
}
}
}
}
else
{
uint8_t x_752; 
lean_dec(x_681);
lean_dec(x_674);
lean_dec(x_671);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_752 = !lean_is_exclusive(x_683);
if (x_752 == 0)
{
return x_683;
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_753 = lean_ctor_get(x_683, 0);
x_754 = lean_ctor_get(x_683, 1);
lean_inc(x_754);
lean_inc(x_753);
lean_dec(x_683);
x_755 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_755, 0, x_753);
lean_ctor_set(x_755, 1, x_754);
return x_755;
}
}
}
else
{
uint8_t x_756; 
lean_dec(x_674);
lean_dec(x_671);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_756 = !lean_is_exclusive(x_680);
if (x_756 == 0)
{
return x_680;
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; 
x_757 = lean_ctor_get(x_680, 0);
x_758 = lean_ctor_get(x_680, 1);
lean_inc(x_758);
lean_inc(x_757);
lean_dec(x_680);
x_759 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_759, 0, x_757);
lean_ctor_set(x_759, 1, x_758);
return x_759;
}
}
}
else
{
uint8_t x_760; 
lean_dec(x_671);
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
x_760 = !lean_is_exclusive(x_672);
if (x_760 == 0)
{
return x_672;
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; 
x_761 = lean_ctor_get(x_672, 0);
x_762 = lean_ctor_get(x_672, 1);
lean_inc(x_762);
lean_inc(x_761);
lean_dec(x_672);
x_763 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_763, 0, x_761);
lean_ctor_set(x_763, 1, x_762);
return x_763;
}
}
}
case 9:
{
lean_object* x_764; lean_object* x_765; 
lean_dec(x_11);
lean_dec(x_9);
x_764 = lean_ctor_get(x_6, 5);
lean_inc(x_764);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_765 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_764, x_12, x_13);
if (lean_obj_tag(x_765) == 0)
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_766 = lean_ctor_get(x_765, 1);
lean_inc(x_766);
lean_dec(x_765);
x_767 = lean_ctor_get(x_766, 1);
lean_inc(x_767);
x_768 = lean_ctor_get(x_6, 6);
lean_inc(x_768);
x_769 = l_List_redLength___main___rarg(x_768);
x_770 = lean_mk_empty_array_with_capacity(x_769);
lean_dec(x_769);
lean_inc(x_768);
x_771 = l_List_toArrayAux___main___rarg(x_768, x_770);
x_772 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_767);
lean_inc(x_5);
lean_inc(x_1);
x_773 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_767, x_768, x_772, x_771, x_12, x_766);
lean_dec(x_768);
lean_dec(x_10);
if (lean_obj_tag(x_773) == 0)
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_774 = lean_ctor_get(x_773, 0);
lean_inc(x_774);
x_775 = lean_ctor_get(x_773, 1);
lean_inc(x_775);
lean_dec(x_773);
lean_inc(x_1);
x_776 = l_Lean_Meta_getMVarType(x_1, x_12, x_775);
if (lean_obj_tag(x_776) == 0)
{
lean_object* x_777; lean_object* x_778; uint8_t x_779; lean_object* x_780; 
x_777 = lean_ctor_get(x_776, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_776, 1);
lean_inc(x_778);
lean_dec(x_776);
x_779 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 6);
if (x_779 == 0)
{
lean_object* x_833; uint8_t x_834; 
x_833 = l_Lean_MetavarContext_exprDependsOn(x_767, x_777, x_2);
x_834 = lean_unbox(x_833);
lean_dec(x_833);
if (x_834 == 0)
{
x_780 = x_778;
goto block_832;
}
else
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; uint8_t x_841; 
lean_dec(x_774);
lean_dec(x_764);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_835 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_835, 0, x_3);
x_836 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_837 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_837, 0, x_836);
lean_ctor_set(x_837, 1, x_835);
x_838 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_839 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_839, 0, x_837);
lean_ctor_set(x_839, 1, x_838);
x_840 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_839, x_12, x_778);
lean_dec(x_12);
x_841 = !lean_is_exclusive(x_840);
if (x_841 == 0)
{
return x_840;
}
else
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; 
x_842 = lean_ctor_get(x_840, 0);
x_843 = lean_ctor_get(x_840, 1);
lean_inc(x_843);
lean_inc(x_842);
lean_dec(x_840);
x_844 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_844, 0, x_842);
lean_ctor_set(x_844, 1, x_843);
return x_844;
}
}
}
else
{
lean_dec(x_777);
lean_dec(x_767);
x_780 = x_778;
goto block_832;
}
block_832:
{
lean_object* x_781; lean_object* x_782; uint8_t x_783; lean_object* x_784; 
lean_inc(x_774);
x_781 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_772, x_774);
x_782 = lean_array_push(x_781, x_2);
x_783 = 1;
x_784 = l_Lean_Meta_revert(x_1, x_782, x_783, x_12, x_780);
if (lean_obj_tag(x_784) == 0)
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; lean_object* x_792; 
x_785 = lean_ctor_get(x_784, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_784, 1);
lean_inc(x_786);
lean_dec(x_784);
x_787 = lean_ctor_get(x_785, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_785, 1);
lean_inc(x_788);
lean_dec(x_785);
x_789 = lean_array_get_size(x_774);
x_790 = lean_box(0);
x_791 = 0;
x_792 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_791, x_788, x_789, x_790, x_12, x_786);
if (lean_obj_tag(x_792) == 0)
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_792, 1);
lean_inc(x_794);
lean_dec(x_792);
x_795 = lean_ctor_get(x_793, 0);
lean_inc(x_795);
x_796 = lean_ctor_get(x_793, 1);
lean_inc(x_796);
lean_dec(x_793);
x_797 = l_Lean_Meta_intro1(x_796, x_791, x_12, x_794);
if (lean_obj_tag(x_797) == 0)
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_798 = lean_ctor_get(x_797, 0);
lean_inc(x_798);
x_799 = lean_ctor_get(x_797, 1);
lean_inc(x_799);
lean_dec(x_797);
x_800 = lean_ctor_get(x_798, 0);
lean_inc(x_800);
x_801 = lean_ctor_get(x_798, 1);
lean_inc(x_801);
lean_dec(x_798);
x_802 = lean_box(0);
x_803 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_774, x_795, x_774, x_772, x_802);
lean_dec(x_774);
x_804 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_772, x_795);
lean_inc(x_800);
x_805 = l_Lean_mkFVar(x_800);
lean_inc(x_801);
x_806 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_806, 0, x_801);
x_807 = lean_box(x_779);
lean_inc(x_801);
x_808 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_808, 0, x_800);
lean_closure_set(x_808, 1, x_7);
lean_closure_set(x_808, 2, x_3);
lean_closure_set(x_808, 3, x_4);
lean_closure_set(x_808, 4, x_5);
lean_closure_set(x_808, 5, x_6);
lean_closure_set(x_808, 6, x_764);
lean_closure_set(x_808, 7, x_807);
lean_closure_set(x_808, 8, x_787);
lean_closure_set(x_808, 9, x_801);
lean_closure_set(x_808, 10, x_803);
lean_closure_set(x_808, 11, x_804);
lean_closure_set(x_808, 12, x_805);
x_809 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_809, 0, x_806);
lean_closure_set(x_809, 1, x_808);
x_810 = l_Lean_Meta_getMVarDecl(x_801, x_12, x_799);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_811 = lean_ctor_get(x_810, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_810, 1);
lean_inc(x_812);
lean_dec(x_810);
x_813 = lean_ctor_get(x_811, 1);
lean_inc(x_813);
x_814 = lean_ctor_get(x_811, 4);
lean_inc(x_814);
lean_dec(x_811);
x_815 = l_Lean_Meta_withLocalContext___rarg(x_813, x_814, x_809, x_12, x_812);
lean_dec(x_12);
return x_815;
}
else
{
uint8_t x_816; 
lean_dec(x_809);
lean_dec(x_12);
x_816 = !lean_is_exclusive(x_810);
if (x_816 == 0)
{
return x_810;
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_817 = lean_ctor_get(x_810, 0);
x_818 = lean_ctor_get(x_810, 1);
lean_inc(x_818);
lean_inc(x_817);
lean_dec(x_810);
x_819 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_819, 0, x_817);
lean_ctor_set(x_819, 1, x_818);
return x_819;
}
}
}
else
{
uint8_t x_820; 
lean_dec(x_795);
lean_dec(x_787);
lean_dec(x_774);
lean_dec(x_764);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_820 = !lean_is_exclusive(x_797);
if (x_820 == 0)
{
return x_797;
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_821 = lean_ctor_get(x_797, 0);
x_822 = lean_ctor_get(x_797, 1);
lean_inc(x_822);
lean_inc(x_821);
lean_dec(x_797);
x_823 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_823, 0, x_821);
lean_ctor_set(x_823, 1, x_822);
return x_823;
}
}
}
else
{
uint8_t x_824; 
lean_dec(x_787);
lean_dec(x_774);
lean_dec(x_764);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_824 = !lean_is_exclusive(x_792);
if (x_824 == 0)
{
return x_792;
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_825 = lean_ctor_get(x_792, 0);
x_826 = lean_ctor_get(x_792, 1);
lean_inc(x_826);
lean_inc(x_825);
lean_dec(x_792);
x_827 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_827, 0, x_825);
lean_ctor_set(x_827, 1, x_826);
return x_827;
}
}
}
else
{
uint8_t x_828; 
lean_dec(x_774);
lean_dec(x_764);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_828 = !lean_is_exclusive(x_784);
if (x_828 == 0)
{
return x_784;
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; 
x_829 = lean_ctor_get(x_784, 0);
x_830 = lean_ctor_get(x_784, 1);
lean_inc(x_830);
lean_inc(x_829);
lean_dec(x_784);
x_831 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_831, 0, x_829);
lean_ctor_set(x_831, 1, x_830);
return x_831;
}
}
}
}
else
{
uint8_t x_845; 
lean_dec(x_774);
lean_dec(x_767);
lean_dec(x_764);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_845 = !lean_is_exclusive(x_776);
if (x_845 == 0)
{
return x_776;
}
else
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_846 = lean_ctor_get(x_776, 0);
x_847 = lean_ctor_get(x_776, 1);
lean_inc(x_847);
lean_inc(x_846);
lean_dec(x_776);
x_848 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_848, 0, x_846);
lean_ctor_set(x_848, 1, x_847);
return x_848;
}
}
}
else
{
uint8_t x_849; 
lean_dec(x_767);
lean_dec(x_764);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_849 = !lean_is_exclusive(x_773);
if (x_849 == 0)
{
return x_773;
}
else
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; 
x_850 = lean_ctor_get(x_773, 0);
x_851 = lean_ctor_get(x_773, 1);
lean_inc(x_851);
lean_inc(x_850);
lean_dec(x_773);
x_852 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_852, 0, x_850);
lean_ctor_set(x_852, 1, x_851);
return x_852;
}
}
}
else
{
uint8_t x_853; 
lean_dec(x_764);
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
x_853 = !lean_is_exclusive(x_765);
if (x_853 == 0)
{
return x_765;
}
else
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; 
x_854 = lean_ctor_get(x_765, 0);
x_855 = lean_ctor_get(x_765, 1);
lean_inc(x_855);
lean_inc(x_854);
lean_dec(x_765);
x_856 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_856, 0, x_854);
lean_ctor_set(x_856, 1, x_855);
return x_856;
}
}
}
case 10:
{
lean_object* x_857; lean_object* x_858; 
lean_dec(x_11);
lean_dec(x_9);
x_857 = lean_ctor_get(x_6, 5);
lean_inc(x_857);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_858 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_857, x_12, x_13);
if (lean_obj_tag(x_858) == 0)
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; 
x_859 = lean_ctor_get(x_858, 1);
lean_inc(x_859);
lean_dec(x_858);
x_860 = lean_ctor_get(x_859, 1);
lean_inc(x_860);
x_861 = lean_ctor_get(x_6, 6);
lean_inc(x_861);
x_862 = l_List_redLength___main___rarg(x_861);
x_863 = lean_mk_empty_array_with_capacity(x_862);
lean_dec(x_862);
lean_inc(x_861);
x_864 = l_List_toArrayAux___main___rarg(x_861, x_863);
x_865 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_860);
lean_inc(x_5);
lean_inc(x_1);
x_866 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_860, x_861, x_865, x_864, x_12, x_859);
lean_dec(x_861);
lean_dec(x_10);
if (lean_obj_tag(x_866) == 0)
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; 
x_867 = lean_ctor_get(x_866, 0);
lean_inc(x_867);
x_868 = lean_ctor_get(x_866, 1);
lean_inc(x_868);
lean_dec(x_866);
lean_inc(x_1);
x_869 = l_Lean_Meta_getMVarType(x_1, x_12, x_868);
if (lean_obj_tag(x_869) == 0)
{
lean_object* x_870; lean_object* x_871; uint8_t x_872; lean_object* x_873; 
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
lean_dec(x_869);
x_872 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 6);
if (x_872 == 0)
{
lean_object* x_926; uint8_t x_927; 
x_926 = l_Lean_MetavarContext_exprDependsOn(x_860, x_870, x_2);
x_927 = lean_unbox(x_926);
lean_dec(x_926);
if (x_927 == 0)
{
x_873 = x_871;
goto block_925;
}
else
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; uint8_t x_934; 
lean_dec(x_867);
lean_dec(x_857);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_928 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_928, 0, x_3);
x_929 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_930 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_930, 0, x_929);
lean_ctor_set(x_930, 1, x_928);
x_931 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_932 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_932, 0, x_930);
lean_ctor_set(x_932, 1, x_931);
x_933 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_932, x_12, x_871);
lean_dec(x_12);
x_934 = !lean_is_exclusive(x_933);
if (x_934 == 0)
{
return x_933;
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; 
x_935 = lean_ctor_get(x_933, 0);
x_936 = lean_ctor_get(x_933, 1);
lean_inc(x_936);
lean_inc(x_935);
lean_dec(x_933);
x_937 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_937, 0, x_935);
lean_ctor_set(x_937, 1, x_936);
return x_937;
}
}
}
else
{
lean_dec(x_870);
lean_dec(x_860);
x_873 = x_871;
goto block_925;
}
block_925:
{
lean_object* x_874; lean_object* x_875; uint8_t x_876; lean_object* x_877; 
lean_inc(x_867);
x_874 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_865, x_867);
x_875 = lean_array_push(x_874, x_2);
x_876 = 1;
x_877 = l_Lean_Meta_revert(x_1, x_875, x_876, x_12, x_873);
if (lean_obj_tag(x_877) == 0)
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; uint8_t x_884; lean_object* x_885; 
x_878 = lean_ctor_get(x_877, 0);
lean_inc(x_878);
x_879 = lean_ctor_get(x_877, 1);
lean_inc(x_879);
lean_dec(x_877);
x_880 = lean_ctor_get(x_878, 0);
lean_inc(x_880);
x_881 = lean_ctor_get(x_878, 1);
lean_inc(x_881);
lean_dec(x_878);
x_882 = lean_array_get_size(x_867);
x_883 = lean_box(0);
x_884 = 0;
x_885 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_884, x_881, x_882, x_883, x_12, x_879);
if (lean_obj_tag(x_885) == 0)
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
x_886 = lean_ctor_get(x_885, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_885, 1);
lean_inc(x_887);
lean_dec(x_885);
x_888 = lean_ctor_get(x_886, 0);
lean_inc(x_888);
x_889 = lean_ctor_get(x_886, 1);
lean_inc(x_889);
lean_dec(x_886);
x_890 = l_Lean_Meta_intro1(x_889, x_884, x_12, x_887);
if (lean_obj_tag(x_890) == 0)
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; 
x_891 = lean_ctor_get(x_890, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_890, 1);
lean_inc(x_892);
lean_dec(x_890);
x_893 = lean_ctor_get(x_891, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_891, 1);
lean_inc(x_894);
lean_dec(x_891);
x_895 = lean_box(0);
x_896 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_867, x_888, x_867, x_865, x_895);
lean_dec(x_867);
x_897 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_865, x_888);
lean_inc(x_893);
x_898 = l_Lean_mkFVar(x_893);
lean_inc(x_894);
x_899 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_899, 0, x_894);
x_900 = lean_box(x_872);
lean_inc(x_894);
x_901 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_901, 0, x_893);
lean_closure_set(x_901, 1, x_7);
lean_closure_set(x_901, 2, x_3);
lean_closure_set(x_901, 3, x_4);
lean_closure_set(x_901, 4, x_5);
lean_closure_set(x_901, 5, x_6);
lean_closure_set(x_901, 6, x_857);
lean_closure_set(x_901, 7, x_900);
lean_closure_set(x_901, 8, x_880);
lean_closure_set(x_901, 9, x_894);
lean_closure_set(x_901, 10, x_896);
lean_closure_set(x_901, 11, x_897);
lean_closure_set(x_901, 12, x_898);
x_902 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_902, 0, x_899);
lean_closure_set(x_902, 1, x_901);
x_903 = l_Lean_Meta_getMVarDecl(x_894, x_12, x_892);
if (lean_obj_tag(x_903) == 0)
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; 
x_904 = lean_ctor_get(x_903, 0);
lean_inc(x_904);
x_905 = lean_ctor_get(x_903, 1);
lean_inc(x_905);
lean_dec(x_903);
x_906 = lean_ctor_get(x_904, 1);
lean_inc(x_906);
x_907 = lean_ctor_get(x_904, 4);
lean_inc(x_907);
lean_dec(x_904);
x_908 = l_Lean_Meta_withLocalContext___rarg(x_906, x_907, x_902, x_12, x_905);
lean_dec(x_12);
return x_908;
}
else
{
uint8_t x_909; 
lean_dec(x_902);
lean_dec(x_12);
x_909 = !lean_is_exclusive(x_903);
if (x_909 == 0)
{
return x_903;
}
else
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; 
x_910 = lean_ctor_get(x_903, 0);
x_911 = lean_ctor_get(x_903, 1);
lean_inc(x_911);
lean_inc(x_910);
lean_dec(x_903);
x_912 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_912, 0, x_910);
lean_ctor_set(x_912, 1, x_911);
return x_912;
}
}
}
else
{
uint8_t x_913; 
lean_dec(x_888);
lean_dec(x_880);
lean_dec(x_867);
lean_dec(x_857);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_913 = !lean_is_exclusive(x_890);
if (x_913 == 0)
{
return x_890;
}
else
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; 
x_914 = lean_ctor_get(x_890, 0);
x_915 = lean_ctor_get(x_890, 1);
lean_inc(x_915);
lean_inc(x_914);
lean_dec(x_890);
x_916 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_916, 0, x_914);
lean_ctor_set(x_916, 1, x_915);
return x_916;
}
}
}
else
{
uint8_t x_917; 
lean_dec(x_880);
lean_dec(x_867);
lean_dec(x_857);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_917 = !lean_is_exclusive(x_885);
if (x_917 == 0)
{
return x_885;
}
else
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; 
x_918 = lean_ctor_get(x_885, 0);
x_919 = lean_ctor_get(x_885, 1);
lean_inc(x_919);
lean_inc(x_918);
lean_dec(x_885);
x_920 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_920, 0, x_918);
lean_ctor_set(x_920, 1, x_919);
return x_920;
}
}
}
else
{
uint8_t x_921; 
lean_dec(x_867);
lean_dec(x_857);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_921 = !lean_is_exclusive(x_877);
if (x_921 == 0)
{
return x_877;
}
else
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; 
x_922 = lean_ctor_get(x_877, 0);
x_923 = lean_ctor_get(x_877, 1);
lean_inc(x_923);
lean_inc(x_922);
lean_dec(x_877);
x_924 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_924, 0, x_922);
lean_ctor_set(x_924, 1, x_923);
return x_924;
}
}
}
}
else
{
uint8_t x_938; 
lean_dec(x_867);
lean_dec(x_860);
lean_dec(x_857);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_938 = !lean_is_exclusive(x_869);
if (x_938 == 0)
{
return x_869;
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; 
x_939 = lean_ctor_get(x_869, 0);
x_940 = lean_ctor_get(x_869, 1);
lean_inc(x_940);
lean_inc(x_939);
lean_dec(x_869);
x_941 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_941, 0, x_939);
lean_ctor_set(x_941, 1, x_940);
return x_941;
}
}
}
else
{
uint8_t x_942; 
lean_dec(x_860);
lean_dec(x_857);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_942 = !lean_is_exclusive(x_866);
if (x_942 == 0)
{
return x_866;
}
else
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; 
x_943 = lean_ctor_get(x_866, 0);
x_944 = lean_ctor_get(x_866, 1);
lean_inc(x_944);
lean_inc(x_943);
lean_dec(x_866);
x_945 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_945, 0, x_943);
lean_ctor_set(x_945, 1, x_944);
return x_945;
}
}
}
else
{
uint8_t x_946; 
lean_dec(x_857);
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
x_946 = !lean_is_exclusive(x_858);
if (x_946 == 0)
{
return x_858;
}
else
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; 
x_947 = lean_ctor_get(x_858, 0);
x_948 = lean_ctor_get(x_858, 1);
lean_inc(x_948);
lean_inc(x_947);
lean_dec(x_858);
x_949 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_949, 0, x_947);
lean_ctor_set(x_949, 1, x_948);
return x_949;
}
}
}
case 11:
{
lean_object* x_950; lean_object* x_951; 
lean_dec(x_11);
lean_dec(x_9);
x_950 = lean_ctor_get(x_6, 5);
lean_inc(x_950);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_951 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_950, x_12, x_13);
if (lean_obj_tag(x_951) == 0)
{
lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; 
x_952 = lean_ctor_get(x_951, 1);
lean_inc(x_952);
lean_dec(x_951);
x_953 = lean_ctor_get(x_952, 1);
lean_inc(x_953);
x_954 = lean_ctor_get(x_6, 6);
lean_inc(x_954);
x_955 = l_List_redLength___main___rarg(x_954);
x_956 = lean_mk_empty_array_with_capacity(x_955);
lean_dec(x_955);
lean_inc(x_954);
x_957 = l_List_toArrayAux___main___rarg(x_954, x_956);
x_958 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_953);
lean_inc(x_5);
lean_inc(x_1);
x_959 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_953, x_954, x_958, x_957, x_12, x_952);
lean_dec(x_954);
lean_dec(x_10);
if (lean_obj_tag(x_959) == 0)
{
lean_object* x_960; lean_object* x_961; lean_object* x_962; 
x_960 = lean_ctor_get(x_959, 0);
lean_inc(x_960);
x_961 = lean_ctor_get(x_959, 1);
lean_inc(x_961);
lean_dec(x_959);
lean_inc(x_1);
x_962 = l_Lean_Meta_getMVarType(x_1, x_12, x_961);
if (lean_obj_tag(x_962) == 0)
{
lean_object* x_963; lean_object* x_964; uint8_t x_965; lean_object* x_966; 
x_963 = lean_ctor_get(x_962, 0);
lean_inc(x_963);
x_964 = lean_ctor_get(x_962, 1);
lean_inc(x_964);
lean_dec(x_962);
x_965 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 6);
if (x_965 == 0)
{
lean_object* x_1019; uint8_t x_1020; 
x_1019 = l_Lean_MetavarContext_exprDependsOn(x_953, x_963, x_2);
x_1020 = lean_unbox(x_1019);
lean_dec(x_1019);
if (x_1020 == 0)
{
x_966 = x_964;
goto block_1018;
}
else
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; uint8_t x_1027; 
lean_dec(x_960);
lean_dec(x_950);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1021 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1021, 0, x_3);
x_1022 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1023 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1023, 0, x_1022);
lean_ctor_set(x_1023, 1, x_1021);
x_1024 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_1025 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1025, 0, x_1023);
lean_ctor_set(x_1025, 1, x_1024);
x_1026 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_1025, x_12, x_964);
lean_dec(x_12);
x_1027 = !lean_is_exclusive(x_1026);
if (x_1027 == 0)
{
return x_1026;
}
else
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; 
x_1028 = lean_ctor_get(x_1026, 0);
x_1029 = lean_ctor_get(x_1026, 1);
lean_inc(x_1029);
lean_inc(x_1028);
lean_dec(x_1026);
x_1030 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1030, 0, x_1028);
lean_ctor_set(x_1030, 1, x_1029);
return x_1030;
}
}
}
else
{
lean_dec(x_963);
lean_dec(x_953);
x_966 = x_964;
goto block_1018;
}
block_1018:
{
lean_object* x_967; lean_object* x_968; uint8_t x_969; lean_object* x_970; 
lean_inc(x_960);
x_967 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_958, x_960);
x_968 = lean_array_push(x_967, x_2);
x_969 = 1;
x_970 = l_Lean_Meta_revert(x_1, x_968, x_969, x_12, x_966);
if (lean_obj_tag(x_970) == 0)
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; uint8_t x_977; lean_object* x_978; 
x_971 = lean_ctor_get(x_970, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_970, 1);
lean_inc(x_972);
lean_dec(x_970);
x_973 = lean_ctor_get(x_971, 0);
lean_inc(x_973);
x_974 = lean_ctor_get(x_971, 1);
lean_inc(x_974);
lean_dec(x_971);
x_975 = lean_array_get_size(x_960);
x_976 = lean_box(0);
x_977 = 0;
x_978 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_977, x_974, x_975, x_976, x_12, x_972);
if (lean_obj_tag(x_978) == 0)
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; 
x_979 = lean_ctor_get(x_978, 0);
lean_inc(x_979);
x_980 = lean_ctor_get(x_978, 1);
lean_inc(x_980);
lean_dec(x_978);
x_981 = lean_ctor_get(x_979, 0);
lean_inc(x_981);
x_982 = lean_ctor_get(x_979, 1);
lean_inc(x_982);
lean_dec(x_979);
x_983 = l_Lean_Meta_intro1(x_982, x_977, x_12, x_980);
if (lean_obj_tag(x_983) == 0)
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; 
x_984 = lean_ctor_get(x_983, 0);
lean_inc(x_984);
x_985 = lean_ctor_get(x_983, 1);
lean_inc(x_985);
lean_dec(x_983);
x_986 = lean_ctor_get(x_984, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_984, 1);
lean_inc(x_987);
lean_dec(x_984);
x_988 = lean_box(0);
x_989 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_960, x_981, x_960, x_958, x_988);
lean_dec(x_960);
x_990 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_958, x_981);
lean_inc(x_986);
x_991 = l_Lean_mkFVar(x_986);
lean_inc(x_987);
x_992 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_992, 0, x_987);
x_993 = lean_box(x_965);
lean_inc(x_987);
x_994 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_994, 0, x_986);
lean_closure_set(x_994, 1, x_7);
lean_closure_set(x_994, 2, x_3);
lean_closure_set(x_994, 3, x_4);
lean_closure_set(x_994, 4, x_5);
lean_closure_set(x_994, 5, x_6);
lean_closure_set(x_994, 6, x_950);
lean_closure_set(x_994, 7, x_993);
lean_closure_set(x_994, 8, x_973);
lean_closure_set(x_994, 9, x_987);
lean_closure_set(x_994, 10, x_989);
lean_closure_set(x_994, 11, x_990);
lean_closure_set(x_994, 12, x_991);
x_995 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_995, 0, x_992);
lean_closure_set(x_995, 1, x_994);
x_996 = l_Lean_Meta_getMVarDecl(x_987, x_12, x_985);
if (lean_obj_tag(x_996) == 0)
{
lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
x_997 = lean_ctor_get(x_996, 0);
lean_inc(x_997);
x_998 = lean_ctor_get(x_996, 1);
lean_inc(x_998);
lean_dec(x_996);
x_999 = lean_ctor_get(x_997, 1);
lean_inc(x_999);
x_1000 = lean_ctor_get(x_997, 4);
lean_inc(x_1000);
lean_dec(x_997);
x_1001 = l_Lean_Meta_withLocalContext___rarg(x_999, x_1000, x_995, x_12, x_998);
lean_dec(x_12);
return x_1001;
}
else
{
uint8_t x_1002; 
lean_dec(x_995);
lean_dec(x_12);
x_1002 = !lean_is_exclusive(x_996);
if (x_1002 == 0)
{
return x_996;
}
else
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; 
x_1003 = lean_ctor_get(x_996, 0);
x_1004 = lean_ctor_get(x_996, 1);
lean_inc(x_1004);
lean_inc(x_1003);
lean_dec(x_996);
x_1005 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1005, 0, x_1003);
lean_ctor_set(x_1005, 1, x_1004);
return x_1005;
}
}
}
else
{
uint8_t x_1006; 
lean_dec(x_981);
lean_dec(x_973);
lean_dec(x_960);
lean_dec(x_950);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1006 = !lean_is_exclusive(x_983);
if (x_1006 == 0)
{
return x_983;
}
else
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; 
x_1007 = lean_ctor_get(x_983, 0);
x_1008 = lean_ctor_get(x_983, 1);
lean_inc(x_1008);
lean_inc(x_1007);
lean_dec(x_983);
x_1009 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1009, 0, x_1007);
lean_ctor_set(x_1009, 1, x_1008);
return x_1009;
}
}
}
else
{
uint8_t x_1010; 
lean_dec(x_973);
lean_dec(x_960);
lean_dec(x_950);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1010 = !lean_is_exclusive(x_978);
if (x_1010 == 0)
{
return x_978;
}
else
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
x_1011 = lean_ctor_get(x_978, 0);
x_1012 = lean_ctor_get(x_978, 1);
lean_inc(x_1012);
lean_inc(x_1011);
lean_dec(x_978);
x_1013 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1013, 0, x_1011);
lean_ctor_set(x_1013, 1, x_1012);
return x_1013;
}
}
}
else
{
uint8_t x_1014; 
lean_dec(x_960);
lean_dec(x_950);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1014 = !lean_is_exclusive(x_970);
if (x_1014 == 0)
{
return x_970;
}
else
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
x_1015 = lean_ctor_get(x_970, 0);
x_1016 = lean_ctor_get(x_970, 1);
lean_inc(x_1016);
lean_inc(x_1015);
lean_dec(x_970);
x_1017 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1017, 0, x_1015);
lean_ctor_set(x_1017, 1, x_1016);
return x_1017;
}
}
}
}
else
{
uint8_t x_1031; 
lean_dec(x_960);
lean_dec(x_953);
lean_dec(x_950);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1031 = !lean_is_exclusive(x_962);
if (x_1031 == 0)
{
return x_962;
}
else
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
x_1032 = lean_ctor_get(x_962, 0);
x_1033 = lean_ctor_get(x_962, 1);
lean_inc(x_1033);
lean_inc(x_1032);
lean_dec(x_962);
x_1034 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1034, 0, x_1032);
lean_ctor_set(x_1034, 1, x_1033);
return x_1034;
}
}
}
else
{
uint8_t x_1035; 
lean_dec(x_953);
lean_dec(x_950);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1035 = !lean_is_exclusive(x_959);
if (x_1035 == 0)
{
return x_959;
}
else
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1036 = lean_ctor_get(x_959, 0);
x_1037 = lean_ctor_get(x_959, 1);
lean_inc(x_1037);
lean_inc(x_1036);
lean_dec(x_959);
x_1038 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1038, 0, x_1036);
lean_ctor_set(x_1038, 1, x_1037);
return x_1038;
}
}
}
else
{
uint8_t x_1039; 
lean_dec(x_950);
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
x_1039 = !lean_is_exclusive(x_951);
if (x_1039 == 0)
{
return x_951;
}
else
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
x_1040 = lean_ctor_get(x_951, 0);
x_1041 = lean_ctor_get(x_951, 1);
lean_inc(x_1041);
lean_inc(x_1040);
lean_dec(x_951);
x_1042 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1042, 0, x_1040);
lean_ctor_set(x_1042, 1, x_1041);
return x_1042;
}
}
}
default: 
{
lean_object* x_1043; lean_object* x_1044; 
lean_dec(x_11);
lean_dec(x_9);
x_1043 = lean_ctor_get(x_6, 5);
lean_inc(x_1043);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_1044 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_5, x_8, x_10, x_1043, x_12, x_13);
if (lean_obj_tag(x_1044) == 0)
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
x_1045 = lean_ctor_get(x_1044, 1);
lean_inc(x_1045);
lean_dec(x_1044);
x_1046 = lean_ctor_get(x_1045, 1);
lean_inc(x_1046);
x_1047 = lean_ctor_get(x_6, 6);
lean_inc(x_1047);
x_1048 = l_List_redLength___main___rarg(x_1047);
x_1049 = lean_mk_empty_array_with_capacity(x_1048);
lean_dec(x_1048);
lean_inc(x_1047);
x_1050 = l_List_toArrayAux___main___rarg(x_1047, x_1049);
x_1051 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
lean_inc(x_1046);
lean_inc(x_5);
lean_inc(x_1);
x_1052 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_1046, x_1047, x_1051, x_1050, x_12, x_1045);
lean_dec(x_1047);
lean_dec(x_10);
if (lean_obj_tag(x_1052) == 0)
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
x_1053 = lean_ctor_get(x_1052, 0);
lean_inc(x_1053);
x_1054 = lean_ctor_get(x_1052, 1);
lean_inc(x_1054);
lean_dec(x_1052);
lean_inc(x_1);
x_1055 = l_Lean_Meta_getMVarType(x_1, x_12, x_1054);
if (lean_obj_tag(x_1055) == 0)
{
lean_object* x_1056; lean_object* x_1057; uint8_t x_1058; lean_object* x_1059; 
x_1056 = lean_ctor_get(x_1055, 0);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_1055, 1);
lean_inc(x_1057);
lean_dec(x_1055);
x_1058 = lean_ctor_get_uint8(x_6, sizeof(void*)*8 + 6);
if (x_1058 == 0)
{
lean_object* x_1112; uint8_t x_1113; 
x_1112 = l_Lean_MetavarContext_exprDependsOn(x_1046, x_1056, x_2);
x_1113 = lean_unbox(x_1112);
lean_dec(x_1112);
if (x_1113 == 0)
{
x_1059 = x_1057;
goto block_1111;
}
else
{
lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; uint8_t x_1120; 
lean_dec(x_1053);
lean_dec(x_1043);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1114 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1114, 0, x_3);
x_1115 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1116 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1116, 0, x_1115);
lean_ctor_set(x_1116, 1, x_1114);
x_1117 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_1118 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1118, 0, x_1116);
lean_ctor_set(x_1118, 1, x_1117);
x_1119 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_1118, x_12, x_1057);
lean_dec(x_12);
x_1120 = !lean_is_exclusive(x_1119);
if (x_1120 == 0)
{
return x_1119;
}
else
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
x_1121 = lean_ctor_get(x_1119, 0);
x_1122 = lean_ctor_get(x_1119, 1);
lean_inc(x_1122);
lean_inc(x_1121);
lean_dec(x_1119);
x_1123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1123, 0, x_1121);
lean_ctor_set(x_1123, 1, x_1122);
return x_1123;
}
}
}
else
{
lean_dec(x_1056);
lean_dec(x_1046);
x_1059 = x_1057;
goto block_1111;
}
block_1111:
{
lean_object* x_1060; lean_object* x_1061; uint8_t x_1062; lean_object* x_1063; 
lean_inc(x_1053);
x_1060 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1051, x_1053);
x_1061 = lean_array_push(x_1060, x_2);
x_1062 = 1;
x_1063 = l_Lean_Meta_revert(x_1, x_1061, x_1062, x_12, x_1059);
if (lean_obj_tag(x_1063) == 0)
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; uint8_t x_1070; lean_object* x_1071; 
x_1064 = lean_ctor_get(x_1063, 0);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_1063, 1);
lean_inc(x_1065);
lean_dec(x_1063);
x_1066 = lean_ctor_get(x_1064, 0);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_1064, 1);
lean_inc(x_1067);
lean_dec(x_1064);
x_1068 = lean_array_get_size(x_1053);
x_1069 = lean_box(0);
x_1070 = 0;
x_1071 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1070, x_1067, x_1068, x_1069, x_12, x_1065);
if (lean_obj_tag(x_1071) == 0)
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
x_1072 = lean_ctor_get(x_1071, 0);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_1071, 1);
lean_inc(x_1073);
lean_dec(x_1071);
x_1074 = lean_ctor_get(x_1072, 0);
lean_inc(x_1074);
x_1075 = lean_ctor_get(x_1072, 1);
lean_inc(x_1075);
lean_dec(x_1072);
x_1076 = l_Lean_Meta_intro1(x_1075, x_1070, x_12, x_1073);
if (lean_obj_tag(x_1076) == 0)
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; 
x_1077 = lean_ctor_get(x_1076, 0);
lean_inc(x_1077);
x_1078 = lean_ctor_get(x_1076, 1);
lean_inc(x_1078);
lean_dec(x_1076);
x_1079 = lean_ctor_get(x_1077, 0);
lean_inc(x_1079);
x_1080 = lean_ctor_get(x_1077, 1);
lean_inc(x_1080);
lean_dec(x_1077);
x_1081 = lean_box(0);
x_1082 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_1053, x_1074, x_1053, x_1051, x_1081);
lean_dec(x_1053);
x_1083 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_1051, x_1074);
lean_inc(x_1079);
x_1084 = l_Lean_mkFVar(x_1079);
lean_inc(x_1080);
x_1085 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_1085, 0, x_1080);
x_1086 = lean_box(x_1058);
lean_inc(x_1080);
x_1087 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_1087, 0, x_1079);
lean_closure_set(x_1087, 1, x_7);
lean_closure_set(x_1087, 2, x_3);
lean_closure_set(x_1087, 3, x_4);
lean_closure_set(x_1087, 4, x_5);
lean_closure_set(x_1087, 5, x_6);
lean_closure_set(x_1087, 6, x_1043);
lean_closure_set(x_1087, 7, x_1086);
lean_closure_set(x_1087, 8, x_1066);
lean_closure_set(x_1087, 9, x_1080);
lean_closure_set(x_1087, 10, x_1082);
lean_closure_set(x_1087, 11, x_1083);
lean_closure_set(x_1087, 12, x_1084);
x_1088 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_1088, 0, x_1085);
lean_closure_set(x_1088, 1, x_1087);
x_1089 = l_Lean_Meta_getMVarDecl(x_1080, x_12, x_1078);
if (lean_obj_tag(x_1089) == 0)
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; 
x_1090 = lean_ctor_get(x_1089, 0);
lean_inc(x_1090);
x_1091 = lean_ctor_get(x_1089, 1);
lean_inc(x_1091);
lean_dec(x_1089);
x_1092 = lean_ctor_get(x_1090, 1);
lean_inc(x_1092);
x_1093 = lean_ctor_get(x_1090, 4);
lean_inc(x_1093);
lean_dec(x_1090);
x_1094 = l_Lean_Meta_withLocalContext___rarg(x_1092, x_1093, x_1088, x_12, x_1091);
lean_dec(x_12);
return x_1094;
}
else
{
uint8_t x_1095; 
lean_dec(x_1088);
lean_dec(x_12);
x_1095 = !lean_is_exclusive(x_1089);
if (x_1095 == 0)
{
return x_1089;
}
else
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; 
x_1096 = lean_ctor_get(x_1089, 0);
x_1097 = lean_ctor_get(x_1089, 1);
lean_inc(x_1097);
lean_inc(x_1096);
lean_dec(x_1089);
x_1098 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1098, 0, x_1096);
lean_ctor_set(x_1098, 1, x_1097);
return x_1098;
}
}
}
else
{
uint8_t x_1099; 
lean_dec(x_1074);
lean_dec(x_1066);
lean_dec(x_1053);
lean_dec(x_1043);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1099 = !lean_is_exclusive(x_1076);
if (x_1099 == 0)
{
return x_1076;
}
else
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; 
x_1100 = lean_ctor_get(x_1076, 0);
x_1101 = lean_ctor_get(x_1076, 1);
lean_inc(x_1101);
lean_inc(x_1100);
lean_dec(x_1076);
x_1102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1102, 0, x_1100);
lean_ctor_set(x_1102, 1, x_1101);
return x_1102;
}
}
}
else
{
uint8_t x_1103; 
lean_dec(x_1066);
lean_dec(x_1053);
lean_dec(x_1043);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1103 = !lean_is_exclusive(x_1071);
if (x_1103 == 0)
{
return x_1071;
}
else
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; 
x_1104 = lean_ctor_get(x_1071, 0);
x_1105 = lean_ctor_get(x_1071, 1);
lean_inc(x_1105);
lean_inc(x_1104);
lean_dec(x_1071);
x_1106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1106, 0, x_1104);
lean_ctor_set(x_1106, 1, x_1105);
return x_1106;
}
}
}
else
{
uint8_t x_1107; 
lean_dec(x_1053);
lean_dec(x_1043);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1107 = !lean_is_exclusive(x_1063);
if (x_1107 == 0)
{
return x_1063;
}
else
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; 
x_1108 = lean_ctor_get(x_1063, 0);
x_1109 = lean_ctor_get(x_1063, 1);
lean_inc(x_1109);
lean_inc(x_1108);
lean_dec(x_1063);
x_1110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1110, 0, x_1108);
lean_ctor_set(x_1110, 1, x_1109);
return x_1110;
}
}
}
}
else
{
uint8_t x_1124; 
lean_dec(x_1053);
lean_dec(x_1046);
lean_dec(x_1043);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1124 = !lean_is_exclusive(x_1055);
if (x_1124 == 0)
{
return x_1055;
}
else
{
lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; 
x_1125 = lean_ctor_get(x_1055, 0);
x_1126 = lean_ctor_get(x_1055, 1);
lean_inc(x_1126);
lean_inc(x_1125);
lean_dec(x_1055);
x_1127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1127, 0, x_1125);
lean_ctor_set(x_1127, 1, x_1126);
return x_1127;
}
}
}
else
{
uint8_t x_1128; 
lean_dec(x_1046);
lean_dec(x_1043);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1128 = !lean_is_exclusive(x_1052);
if (x_1128 == 0)
{
return x_1052;
}
else
{
lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
x_1129 = lean_ctor_get(x_1052, 0);
x_1130 = lean_ctor_get(x_1052, 1);
lean_inc(x_1130);
lean_inc(x_1129);
lean_dec(x_1052);
x_1131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1131, 0, x_1129);
lean_ctor_set(x_1131, 1, x_1130);
return x_1131;
}
}
}
else
{
uint8_t x_1132; 
lean_dec(x_1043);
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
x_1132 = !lean_is_exclusive(x_1044);
if (x_1132 == 0)
{
return x_1044;
}
else
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; 
x_1133 = lean_ctor_get(x_1044, 0);
x_1134 = lean_ctor_get(x_1044, 1);
lean_inc(x_1134);
lean_inc(x_1133);
lean_dec(x_1044);
x_1135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1135, 0, x_1133);
lean_ctor_set(x_1135, 1, x_1134);
return x_1135;
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
