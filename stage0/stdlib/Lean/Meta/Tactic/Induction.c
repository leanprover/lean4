// Lean compiler output
// Module: Lean.Meta.Tactic.Induction
// Imports: Init Lean.Meta.RecursorInfo Lean.Meta.SynthInstance Lean.Meta.Tactic.Util Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Clear Lean.Meta.Tactic.FVarSubst
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
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity(lean_object*);
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_Meta_induction___spec__2(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_Lean_Level_Inhabited;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__7;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__4;
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___boxed(lean_object**);
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___boxed(lean_object**);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_3__forallTelescopeReducingAuxAux___main___rarg___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___boxed(lean_object**);
extern lean_object* l_Lean_Meta_isClassQuick_x3f___main___closed__1;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__3;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__2;
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__2;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_List_elem___main___at_Lean_Meta_induction___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7;
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__9;
lean_object* l_Lean_Meta_getMVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__9;
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__8;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__4;
extern lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__8;
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
lean_object* l_Lean_MetavarContext_localDeclDependsOn(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__7;
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InductionSubgoal_inhabited___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__2;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__4;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___boxed(lean_object**);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed(lean_object**);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__6;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__3;
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__5;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__5;
extern lean_object* l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__4;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__1;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__2;
lean_object* l_Lean_Meta_InductionSubgoal_inhabited;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Core_getTraceState___rarg(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__2;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__1;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfUntil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__7;
lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(lean_object* x_1) {
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
x_9 = l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_8);
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
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("induction");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed recursor");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to generate type class instance parameter");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Meta_inferType(x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Meta_whnfForall(x_14, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 7)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Meta_synthInstance(x_19, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_mkApp(x_4, x_21);
x_3 = x_12;
x_4 = x_23;
x_9 = x_22;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_4);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_27 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8;
x_28 = lean_box(0);
x_29 = l_Lean_Meta_throwTacticEx___rarg(x_26, x_1, x_27, x_28, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_17);
lean_dec(x_4);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_dec(x_16);
x_35 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_36 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_37 = lean_box(0);
x_38 = l_Lean_Meta_throwTacticEx___rarg(x_35, x_1, x_36, x_37, x_5, x_6, x_7, x_8, x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
return x_16;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_16);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_13);
if (x_43 == 0)
{
return x_13;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_13, 0);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_3, 1);
x_48 = lean_ctor_get(x_11, 0);
x_49 = lean_array_get_size(x_2);
x_50 = lean_nat_dec_lt(x_48, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_4);
x_51 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_52 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_53 = lean_box(0);
x_54 = l_Lean_Meta_throwTacticEx___rarg(x_51, x_1, x_52, x_53, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_array_fget(x_2, x_48);
x_56 = l_Lean_mkApp(x_4, x_55);
x_3 = x_47;
x_4 = x_56;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
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
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_whnfForall(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 7)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_expr_instantiate1(x_13, x_3);
lean_dec(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_ctor_get(x_10, 2);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_expr_instantiate1(x_16, x_3);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_21 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_22 = lean_box(0);
x_23 = l_Lean_Meta_throwTacticEx___rarg(x_20, x_1, x_21, x_22, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
return x_9;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_14 = lean_nat_dec_lt(x_12, x_13);
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
x_21 = l_Lean_Meta_FVarSubst_insert(x_7, x_16, x_20);
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
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_14 = lean_nat_dec_lt(x_12, x_13);
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
x_21 = l_Lean_Meta_FVarSubst_insert(x_7, x_16, x_20);
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_3);
x_12 = lean_nat_dec_lt(x_4, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_array_fget(x_3, x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
x_20 = l_Lean_mkApp(x_18, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_21 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_19, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_5, 1, x_22);
lean_ctor_set(x_5, 0, x_20);
x_4 = x_16;
x_10 = x_23;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_20);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
lean_inc(x_14);
x_31 = l_Lean_mkApp(x_29, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_32 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_30, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_33);
x_4 = x_16;
x_5 = x_35;
x_10 = x_34;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_39 = x_32;
} else {
 lean_dec_ref(x_32);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_21 = l_Lean_Meta_whnfForall(x_13, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Expr_isForall(x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
if (x_14 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_12);
x_25 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_26 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_27 = lean_box(0);
x_28 = l_Lean_Meta_throwTacticEx___rarg(x_25, x_1, x_26, x_27, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Meta_assignExprMVar(x_1, x_12, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_15);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_15);
lean_ctor_set(x_37, 1, x_36);
return x_37;
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
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
if (x_14 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_15);
lean_dec(x_12);
x_40 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_41 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_42 = lean_box(0);
x_43 = l_Lean_Meta_throwTacticEx___rarg(x_40, x_1, x_41, x_42, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_Meta_assignExprMVar(x_1, x_12, x_16, x_17, x_18, x_19, x_23);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_15);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_15);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = l_Lean_Meta_RecursorInfo_firstIndexPos(x_3);
x_54 = lean_nat_dec_eq(x_10, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_inc(x_1);
x_55 = l_Lean_Meta_getMVarTag(x_1, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_196; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_196 = lean_nat_dec_le(x_8, x_11);
if (x_196 == 0)
{
x_58 = x_57;
goto block_195;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
lean_dec(x_56);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_197 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_198 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_199 = lean_box(0);
x_200 = l_Lean_Meta_throwTacticEx___rarg(x_197, x_1, x_198, x_199, x_16, x_17, x_18, x_19, x_57);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
return x_200;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_200, 0);
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_200);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
block_195:
{
if (lean_obj_tag(x_22) == 7)
{
lean_object* x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; lean_object* x_63; uint8_t x_144; uint8_t x_145; 
x_59 = lean_ctor_get(x_22, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_22, 1);
lean_inc(x_60);
x_61 = lean_ctor_get_uint64(x_22, sizeof(void*)*3);
x_62 = l_Lean_Expr_headBeta(x_60);
x_144 = (uint8_t)((x_61 << 24) >> 61);
x_145 = l_Lean_BinderInfo_isInstImplicit(x_144);
if (x_145 == 0)
{
lean_object* x_146; 
x_146 = lean_box(0);
x_63 = x_146;
goto block_143;
}
else
{
uint8_t x_147; 
x_147 = l_Array_isEmpty___rarg(x_2);
if (x_147 == 0)
{
lean_object* x_148; 
x_148 = lean_box(0);
x_63 = x_148;
goto block_143;
}
else
{
lean_object* x_149; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_62);
x_149 = l_Lean_Meta_synthInstance_x3f(x_62, x_16, x_17, x_18, x_19, x_58);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = l_Lean_Name_append___main(x_56, x_59);
lean_dec(x_56);
x_153 = 2;
lean_inc(x_16);
x_154 = l_Lean_Meta_mkFreshExprMVar(x_62, x_152, x_153, x_16, x_17, x_18, x_19, x_151);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
lean_inc(x_155);
x_157 = l_Lean_mkApp(x_12, x_155);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_158 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_22, x_155, x_16, x_17, x_18, x_19, x_156);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_unsigned_to_nat(1u);
x_162 = lean_nat_add(x_10, x_161);
lean_dec(x_10);
x_163 = lean_nat_add(x_11, x_161);
lean_dec(x_11);
x_164 = l_Lean_Expr_mvarId_x21(x_155);
lean_dec(x_155);
x_165 = lean_box(0);
x_166 = l_Array_empty___closed__1;
x_167 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_166);
lean_ctor_set(x_167, 2, x_165);
x_168 = lean_array_push(x_15, x_167);
x_10 = x_162;
x_11 = x_163;
x_12 = x_157;
x_13 = x_159;
x_15 = x_168;
x_20 = x_160;
goto _start;
}
else
{
uint8_t x_170; 
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_170 = !lean_is_exclusive(x_158);
if (x_170 == 0)
{
return x_158;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_158, 0);
x_172 = lean_ctor_get(x_158, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_158);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_56);
x_174 = lean_ctor_get(x_149, 1);
lean_inc(x_174);
lean_dec(x_149);
x_175 = lean_ctor_get(x_150, 0);
lean_inc(x_175);
lean_dec(x_150);
lean_inc(x_175);
x_176 = l_Lean_mkApp(x_12, x_175);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_177 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_22, x_175, x_16, x_17, x_18, x_19, x_174);
lean_dec(x_175);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_unsigned_to_nat(1u);
x_181 = lean_nat_add(x_10, x_180);
lean_dec(x_10);
x_182 = lean_nat_add(x_11, x_180);
lean_dec(x_11);
x_10 = x_181;
x_11 = x_182;
x_12 = x_176;
x_13 = x_178;
x_20 = x_179;
goto _start;
}
else
{
uint8_t x_184; 
lean_dec(x_176);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_177);
if (x_184 == 0)
{
return x_177;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_177, 0);
x_186 = lean_ctor_get(x_177, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_177);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_149);
if (x_188 == 0)
{
return x_149;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_149, 0);
x_190 = lean_ctor_get(x_149, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_149);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
}
block_143:
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_63);
lean_inc(x_62);
x_64 = l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_62);
x_65 = lean_nat_dec_lt(x_64, x_6);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_124; uint8_t x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; 
x_66 = lean_nat_sub(x_64, x_6);
lean_dec(x_64);
x_67 = lean_array_get_size(x_4);
x_68 = lean_array_get_size(x_7);
x_69 = lean_nat_sub(x_67, x_68);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_69, x_70);
lean_dec(x_69);
x_124 = lean_array_get_size(x_2);
x_125 = lean_nat_dec_lt(x_11, x_124);
lean_dec(x_124);
x_126 = l_Lean_Name_append___main(x_56, x_59);
lean_dec(x_56);
x_127 = 2;
lean_inc(x_16);
x_128 = l_Lean_Meta_mkFreshExprMVar(x_62, x_126, x_127, x_16, x_17, x_18, x_19, x_58);
if (x_125 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_box(0);
x_72 = x_131;
x_73 = x_129;
x_74 = x_130;
goto block_123;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_128, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_128, 1);
lean_inc(x_133);
lean_dec(x_128);
x_134 = lean_array_fget(x_2, x_11);
x_72 = x_134;
x_73 = x_132;
x_74 = x_133;
goto block_123;
}
block_123:
{
lean_object* x_75; lean_object* x_76; 
lean_inc(x_73);
x_75 = l_Lean_mkApp(x_12, x_73);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_76 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_22, x_73, x_16, x_17, x_18, x_19, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Expr_mvarId_x21(x_73);
lean_dec(x_73);
x_80 = l_Lean_Expr_fvarId_x21(x_5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_81 = l_Lean_Meta_tryClear(x_79, x_80, x_16, x_17, x_18, x_19, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_85 = l_Lean_Meta_introN(x_82, x_66, x_72, x_84, x_16, x_17, x_18, x_19, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_box(0);
x_91 = 0;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_92 = l_Lean_Meta_introN(x_89, x_71, x_90, x_91, x_16, x_17, x_18, x_19, x_87);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
lean_inc(x_9);
lean_inc(x_67);
x_97 = l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(x_4, x_7, x_68, x_95, x_67, x_67, x_9);
lean_dec(x_67);
lean_dec(x_95);
lean_dec(x_68);
x_98 = x_88;
x_99 = lean_unsigned_to_nat(0u);
x_100 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_99, x_98);
x_101 = x_100;
x_102 = lean_nat_add(x_10, x_70);
lean_dec(x_10);
x_103 = lean_nat_add(x_11, x_70);
lean_dec(x_11);
x_104 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_104, 0, x_96);
lean_ctor_set(x_104, 1, x_101);
lean_ctor_set(x_104, 2, x_97);
x_105 = lean_array_push(x_15, x_104);
x_10 = x_102;
x_11 = x_103;
x_12 = x_75;
x_13 = x_77;
x_15 = x_105;
x_20 = x_94;
goto _start;
}
else
{
uint8_t x_107; 
lean_dec(x_88);
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_92);
if (x_107 == 0)
{
return x_92;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_92, 0);
x_109 = lean_ctor_get(x_92, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_92);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_85);
if (x_111 == 0)
{
return x_85;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_85, 0);
x_113 = lean_ctor_get(x_85, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_85);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_81);
if (x_115 == 0)
{
return x_81;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_81, 0);
x_117 = lean_ctor_get(x_81, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_81);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_76);
if (x_119 == 0)
{
return x_76;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_76, 0);
x_121 = lean_ctor_get(x_76, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_76);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_135 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_136 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_137 = lean_box(0);
x_138 = l_Lean_Meta_throwTacticEx___rarg(x_135, x_1, x_136, x_137, x_16, x_17, x_18, x_19, x_58);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
return x_138;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_138);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_56);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_192 = l_Lean_Meta_isClassQuick_x3f___main___closed__1;
x_193 = l_unreachable_x21___rarg(x_192);
x_194 = lean_apply_5(x_193, x_16, x_17, x_18, x_19, x_58);
return x_194;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_205 = !lean_is_exclusive(x_55);
if (x_205 == 0)
{
return x_55;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_55, 0);
x_207 = lean_ctor_get(x_55, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_55);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_12);
lean_ctor_set(x_209, 1, x_22);
x_210 = lean_unsigned_to_nat(0u);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_211 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(x_1, x_7, x_7, x_210, x_209, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_ctor_get(x_212, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_212, 1);
lean_inc(x_215);
lean_dec(x_212);
lean_inc(x_5);
x_216 = l_Lean_mkApp(x_214, x_5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_217 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_215, x_5, x_16, x_17, x_18, x_19, x_213);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_unsigned_to_nat(1u);
x_221 = lean_nat_add(x_10, x_220);
lean_dec(x_10);
x_222 = lean_array_get_size(x_7);
x_223 = lean_nat_add(x_221, x_222);
lean_dec(x_222);
lean_dec(x_221);
x_224 = 1;
x_10 = x_223;
x_12 = x_216;
x_13 = x_218;
x_14 = x_224;
x_20 = x_219;
goto _start;
}
else
{
uint8_t x_226; 
lean_dec(x_216);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_226 = !lean_is_exclusive(x_217);
if (x_226 == 0)
{
return x_217;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_217, 0);
x_228 = lean_ctor_get(x_217, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_217);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
else
{
uint8_t x_230; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_230 = !lean_is_exclusive(x_211);
if (x_230 == 0)
{
return x_211;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_211, 0);
x_232 = lean_ctor_get(x_211, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_211);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_234 = !lean_is_exclusive(x_21);
if (x_234 == 0)
{
return x_21;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_21, 0);
x_236 = lean_ctor_get(x_21, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_21);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
}
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___boxed(lean_object** _args) {
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
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_14);
lean_dec(x_14);
x_22 = l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_21, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
x_21 = l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_21;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___boxed(lean_object** _args) {
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
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_14);
lean_dec(x_14);
x_22 = l___private_Lean_Meta_Tactic_Induction_4__finalizeAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_21, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_1);
x_14 = l_Lean_Meta_getMVarType(x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_inferType(x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_3, 7);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_List_lengthAux___main___rarg(x_21, x_22);
x_24 = lean_ctor_get(x_3, 5);
x_25 = l_List_lengthAux___main___rarg(x_24, x_22);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_25, x_26);
lean_dec(x_25);
x_28 = 0;
x_29 = l_Array_empty___closed__1;
x_30 = l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(x_1, x_2, x_3, x_4, x_5, x_17, x_6, x_23, x_7, x_27, x_22, x_8, x_19, x_28, x_29, x_9, x_10, x_11, x_12, x_20);
lean_dec(x_23);
lean_dec(x_17);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected major premise type ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = l_Lean_indentExpr(x_8);
x_10 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_13 = lean_box(0);
x_14 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_11, x_13, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
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
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_5, 1);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_array_get_size(x_4);
x_19 = lean_nat_dec_le(x_18, x_17);
lean_dec(x_18);
if (x_19 == 0)
{
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_3);
x_22 = l_Lean_indentExpr(x_21);
x_23 = l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__3;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_box(0);
x_26 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_24, x_25, x_6, x_7, x_8, x_9, x_10);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
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
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_10, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_60; uint8_t x_80; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_10, x_18);
lean_dec(x_10);
x_20 = lean_nat_sub(x_9, x_19);
x_21 = lean_nat_sub(x_20, x_18);
lean_dec(x_20);
x_22 = l_Lean_Expr_Inhabited;
x_23 = lean_array_get(x_22, x_4, x_21);
x_80 = lean_nat_dec_eq(x_21, x_7);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = lean_expr_eqv(x_23, x_8);
if (x_81 == 0)
{
x_60 = x_15;
goto block_79;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_5);
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_8);
x_83 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_84 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__9;
x_86 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_87, 0, x_3);
x_88 = l_Lean_indentExpr(x_87);
x_89 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_box(0);
x_91 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_89, x_90, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_11);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
return x_91;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_91);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
x_60 = x_15;
goto block_79;
}
block_59:
{
uint8_t x_25; 
x_25 = lean_nat_dec_lt(x_7, x_21);
if (x_25 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
x_10 = x_19;
x_15 = x_24;
goto _start;
}
else
{
uint8_t x_27; 
x_27 = l_List_elem___main___at_Lean_Meta_induction___spec__2(x_21, x_6);
if (x_27 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
x_10 = x_19;
x_15 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
x_29 = l_Lean_Expr_isFVar(x_23);
if (x_29 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
x_10 = x_19;
x_15 = x_24;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_Expr_fvarId_x21(x_8);
lean_inc(x_11);
x_32 = l_Lean_Meta_getLocalDecl(x_31, x_11, x_12, x_13, x_14, x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Expr_fvarId_x21(x_23);
lean_dec(x_23);
lean_inc(x_5);
x_36 = l_Lean_MetavarContext_localDeclDependsOn(x_5, x_33, x_35);
lean_dec(x_35);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_dec(x_21);
x_10 = x_19;
x_15 = x_34;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_3);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_8);
x_40 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__3;
x_43 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_nat_add(x_21, x_18);
lean_dec(x_21);
x_45 = l_Nat_repr(x_44);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_box(0);
x_50 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_48, x_49, x_11, x_12, x_13, x_14, x_34);
lean_dec(x_11);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_32);
if (x_55 == 0)
{
return x_32;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_32, 0);
x_57 = lean_ctor_get(x_32, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_32);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
}
block_79:
{
uint8_t x_61; 
x_61 = lean_nat_dec_lt(x_21, x_7);
if (x_61 == 0)
{
x_24 = x_60;
goto block_59;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = l_Lean_Expr_fvarId_x21(x_8);
lean_inc(x_23);
lean_inc(x_5);
x_63 = l_Lean_MetavarContext_exprDependsOn(x_5, x_23, x_62);
lean_dec(x_62);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
x_24 = x_60;
goto block_59;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_5);
x_65 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_65, 0, x_8);
x_66 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_67 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__6;
x_69 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_3);
x_71 = l_Lean_indentExpr(x_70);
x_72 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_box(0);
x_74 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_72, x_73, x_11, x_12, x_13, x_14, x_60);
lean_dec(x_11);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
return x_74;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_74);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_15);
return x_97;
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
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_8);
x_15 = lean_nat_dec_lt(x_7, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = x_8;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_55; 
x_18 = lean_array_fget(x_8, x_7);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_fset(x_8, x_7, x_19);
x_21 = x_18;
x_22 = lean_array_get_size(x_4);
x_55 = lean_nat_dec_le(x_22, x_21);
if (x_55 == 0)
{
x_23 = x_13;
goto block_54;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_3);
x_57 = l_Lean_indentExpr(x_56);
x_58 = l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__3;
x_59 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_box(0);
x_61 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_59, x_60, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
return x_61;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_61);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
block_54:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_39; 
x_24 = l_Lean_Expr_Inhabited;
x_25 = lean_array_get(x_24, x_4, x_21);
x_39 = l_Lean_Expr_isFVar(x_25);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_25);
x_41 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__3;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__6;
x_44 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_3);
x_46 = l_Lean_indentExpr(x_45);
x_47 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_box(0);
x_49 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_47, x_48, x_9, x_10, x_11, x_12, x_23);
lean_dec(x_9);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
return x_49;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
x_26 = x_23;
goto block_38;
}
block_38:
{
lean_object* x_27; 
lean_inc(x_9);
lean_inc(x_22);
lean_inc(x_25);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_21, x_25, x_22, x_22, x_9, x_10, x_11, x_12, x_26);
lean_dec(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_7, x_29);
x_31 = x_25;
x_32 = lean_array_fset(x_20, x_7, x_31);
lean_dec(x_7);
x_7 = x_30;
x_8 = x_32;
x_13 = x_28;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_25);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
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
x_13 = l_Lean_Meta_FVarSubst_insert(x_5, x_9, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_4 = x_15;
x_5 = x_13;
goto _start;
}
}
}
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_dec(x_17);
lean_inc(x_3);
x_18 = lean_array_push(x_16, x_3);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_5, 1, x_20);
lean_ctor_set(x_5, 0, x_18);
x_6 = x_15;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_dec(x_5);
lean_inc(x_3);
x_24 = lean_array_push(x_23, x_3);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_5 = x_27;
x_6 = x_22;
goto _start;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_6, 1);
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_array_get_size(x_4);
x_35 = lean_nat_dec_le(x_34, x_33);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = l_Lean_Level_Inhabited;
x_37 = lean_array_get(x_36, x_4, x_33);
x_38 = lean_array_push(x_31, x_37);
lean_ctor_set(x_5, 0, x_38);
x_6 = x_30;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_free_object(x_5);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_3);
x_40 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_41 = lean_box(0);
x_42 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_40, x_41, x_7, x_8, x_9, x_10, x_11);
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
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_ctor_get(x_6, 1);
x_48 = lean_ctor_get(x_5, 0);
x_49 = lean_ctor_get(x_5, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_5);
x_50 = lean_ctor_get(x_13, 0);
x_51 = lean_array_get_size(x_4);
x_52 = lean_nat_dec_le(x_51, x_50);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = l_Lean_Level_Inhabited;
x_54 = lean_array_get(x_53, x_4, x_50);
x_55 = lean_array_push(x_48, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_49);
x_5 = x_56;
x_6 = x_47;
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_3);
x_58 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_59 = lean_box(0);
x_60 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_58, x_59, x_7, x_8, x_9, x_10, x_11);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
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
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
switch (lean_obj_tag(x_14)) {
case 4:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_List_redLength___main___rarg(x_22);
x_24 = lean_mk_empty_array_with_capacity(x_23);
lean_dec(x_23);
x_25 = l_List_toArrayAux___main___rarg(x_22, x_24);
x_26 = lean_ctor_get(x_4, 2);
x_27 = l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_inc(x_13);
lean_inc(x_8);
lean_inc(x_3);
x_28 = l_List_foldlM___main___at_Lean_Meta_induction___spec__6(x_3, x_8, x_13, x_25, x_27, x_26, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = l_Lean_Level_isZero(x_13);
lean_dec(x_13);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_33);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_35 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_35, 0, x_1);
x_36 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__9;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_box(0);
x_41 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_39, x_40, x_17, x_18, x_19, x_20, x_32);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_3);
x_46 = l_Array_toList___rarg(x_33);
lean_dec(x_33);
x_47 = l_Lean_mkConst(x_1, x_46);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_8);
x_48 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_8, x_15, x_5, x_47, x_17, x_18, x_19, x_20, x_32);
lean_dec(x_15);
if (lean_obj_tag(x_48) == 0)
{
if (x_6 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_17);
lean_inc(x_10);
x_51 = l_Lean_Meta_mkLambda(x_10, x_12, x_17, x_18, x_19, x_20, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_mkApp(x_49, x_52);
x_55 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_54, x_17, x_18, x_19, x_20, x_53);
lean_dec(x_10);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_49);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_56 = !lean_is_exclusive(x_51);
if (x_56 == 0)
{
return x_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_51, 0);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_51);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_48, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
lean_dec(x_48);
x_62 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_11);
x_63 = lean_array_push(x_62, x_11);
lean_inc(x_17);
x_64 = l_Lean_Meta_mkLambda(x_63, x_12, x_17, x_18, x_19, x_20, x_61);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_17);
lean_inc(x_10);
x_67 = l_Lean_Meta_mkLambda(x_10, x_65, x_17, x_18, x_19, x_20, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_mkApp(x_60, x_68);
x_71 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_70, x_17, x_18, x_19, x_20, x_69);
lean_dec(x_10);
return x_71;
}
else
{
uint8_t x_72; 
lean_dec(x_60);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_72 = !lean_is_exclusive(x_67);
if (x_72 == 0)
{
return x_67;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_67, 0);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_67);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_60);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_76 = !lean_is_exclusive(x_64);
if (x_76 == 0)
{
return x_64;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_64, 0);
x_78 = lean_ctor_get(x_64, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_64);
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
uint8_t x_80; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_80 = !lean_is_exclusive(x_48);
if (x_80 == 0)
{
return x_48;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_48, 0);
x_82 = lean_ctor_get(x_48, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_48);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_13);
lean_dec(x_3);
x_84 = lean_ctor_get(x_28, 1);
lean_inc(x_84);
lean_dec(x_28);
x_85 = lean_ctor_get(x_29, 0);
lean_inc(x_85);
lean_dec(x_29);
x_86 = l_Array_toList___rarg(x_85);
lean_dec(x_85);
x_87 = l_Lean_mkConst(x_1, x_86);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_8);
x_88 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_8, x_15, x_5, x_87, x_17, x_18, x_19, x_20, x_84);
lean_dec(x_15);
if (lean_obj_tag(x_88) == 0)
{
if (x_6 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_17);
lean_inc(x_10);
x_91 = l_Lean_Meta_mkLambda(x_10, x_12, x_17, x_18, x_19, x_20, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_mkApp(x_89, x_92);
x_95 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_94, x_17, x_18, x_19, x_20, x_93);
lean_dec(x_10);
return x_95;
}
else
{
uint8_t x_96; 
lean_dec(x_89);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_96 = !lean_is_exclusive(x_91);
if (x_96 == 0)
{
return x_91;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_91, 0);
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_91);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_88, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_88, 1);
lean_inc(x_101);
lean_dec(x_88);
x_102 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_11);
x_103 = lean_array_push(x_102, x_11);
lean_inc(x_17);
x_104 = l_Lean_Meta_mkLambda(x_103, x_12, x_17, x_18, x_19, x_20, x_101);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_17);
lean_inc(x_10);
x_107 = l_Lean_Meta_mkLambda(x_10, x_105, x_17, x_18, x_19, x_20, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_mkApp(x_100, x_108);
x_111 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_110, x_17, x_18, x_19, x_20, x_109);
lean_dec(x_10);
return x_111;
}
else
{
uint8_t x_112; 
lean_dec(x_100);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_112 = !lean_is_exclusive(x_107);
if (x_112 == 0)
{
return x_107;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_107, 0);
x_114 = lean_ctor_get(x_107, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_107);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_100);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_116 = !lean_is_exclusive(x_104);
if (x_116 == 0)
{
return x_104;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_104, 0);
x_118 = lean_ctor_get(x_104, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_104);
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
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_120 = !lean_is_exclusive(x_88);
if (x_120 == 0)
{
return x_88;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_88, 0);
x_122 = lean_ctor_get(x_88, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_88);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
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
x_124 = !lean_is_exclusive(x_28);
if (x_124 == 0)
{
return x_28;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_28, 0);
x_126 = lean_ctor_get(x_28, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_28);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
case 5:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_14, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_14, 1);
lean_inc(x_129);
lean_dec(x_14);
x_130 = lean_array_set(x_15, x_16, x_129);
x_131 = lean_unsigned_to_nat(1u);
x_132 = lean_nat_sub(x_16, x_131);
lean_dec(x_16);
x_14 = x_128;
x_15 = x_130;
x_16 = x_132;
goto _start;
}
default: 
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_134 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__3;
x_135 = lean_box(0);
x_136 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_134, x_135, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
return x_136;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_20 = l_Lean_Meta_getLevel(x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_15);
x_23 = l_Lean_Meta_getLocalDecl(x_1, x_15, x_16, x_17, x_18, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_LocalDecl_type(x_24);
lean_dec(x_24);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_26);
x_27 = l_Lean_Meta_whnfUntil(x_26, x_2, x_15, x_16, x_17, x_18, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(x_3, x_26, x_15, x_16, x_17, x_18, x_29);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_26);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Expr_getAppNumArgsAux___main(x_32, x_33);
x_35 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_34);
x_36 = lean_mk_array(x_34, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_34, x_37);
lean_dec(x_34);
x_39 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_13, x_14, x_21, x_32, x_36, x_38, x_15, x_16, x_17, x_18, x_31);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_27);
if (x_40 == 0)
{
return x_27;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_27, 0);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_27);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
return x_23;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_23, 0);
x_46 = lean_ctor_get(x_23, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_23);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_20);
if (x_48 == 0)
{
return x_20;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_20, 0);
x_50 = lean_ctor_get(x_20, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_20);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after revert&intro");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__4;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not support dependent elimination, but conclusion depends on major premise");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_10);
x_18 = lean_ctor_get(x_7, 5);
lean_inc(x_18);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_19 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_18, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_14, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_7, 6);
lean_inc(x_25);
x_26 = l_List_redLength___main___rarg(x_25);
x_27 = lean_mk_empty_array_with_capacity(x_26);
lean_dec(x_26);
lean_inc(x_25);
x_28 = l_List_toArrayAux___main___rarg(x_25, x_27);
x_29 = x_28;
x_30 = lean_unsigned_to_nat(0u);
lean_inc(x_24);
lean_inc(x_6);
lean_inc(x_1);
x_31 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_6);
lean_closure_set(x_31, 2, x_9);
lean_closure_set(x_31, 3, x_11);
lean_closure_set(x_31, 4, x_24);
lean_closure_set(x_31, 5, x_25);
lean_closure_set(x_31, 6, x_30);
lean_closure_set(x_31, 7, x_29);
x_32 = x_31;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_33 = lean_apply_5(x_32, x_13, x_14, x_15, x_16, x_23);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_1);
x_36 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_39 == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = l_Lean_MetavarContext_exprDependsOn(x_24, x_37, x_2);
x_119 = lean_unbox(x_118);
lean_dec(x_118);
if (x_119 == 0)
{
x_40 = x_38;
goto block_117;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_120 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_120, 0, x_3);
x_121 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_122 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_124 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_box(0);
x_126 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_124, x_125, x_13, x_14, x_15, x_16, x_38);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
return x_126;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_126, 0);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_126);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_24);
x_40 = x_38;
goto block_117;
}
block_117:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
lean_inc(x_34);
x_41 = x_34;
x_42 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_30, x_41);
x_43 = x_42;
x_44 = lean_array_push(x_43, x_2);
x_45 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_46 = l_Lean_Meta_revert(x_1, x_44, x_45, x_13, x_14, x_15, x_16, x_40);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_array_get_size(x_34);
x_52 = lean_box(0);
x_53 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_54 = l_Lean_Meta_introN(x_50, x_51, x_52, x_53, x_13, x_14, x_15, x_16, x_48);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_59 = l_Lean_Meta_intro1(x_58, x_53, x_13, x_14, x_15, x_16, x_56);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_86; lean_object* x_87; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_box(0);
x_65 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_34, x_57, x_34, x_30, x_64);
lean_dec(x_34);
x_95 = l_Lean_Core_getTraceState___rarg(x_16, x_61);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_96, sizeof(void*)*1);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_86 = x_53;
x_87 = x_98;
goto block_94;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
lean_dec(x_95);
x_100 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_101 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_100, x_15, x_16, x_99);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_unbox(x_102);
lean_dec(x_102);
x_86 = x_104;
x_87 = x_103;
goto block_94;
}
block_85:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = x_57;
x_68 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_30, x_67);
x_69 = x_68;
lean_inc(x_62);
x_70 = l_Lean_mkFVar(x_62);
lean_inc(x_63);
x_71 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_71, 0, x_63);
x_72 = lean_box(x_39);
lean_inc(x_63);
x_73 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_73, 0, x_62);
lean_closure_set(x_73, 1, x_8);
lean_closure_set(x_73, 2, x_63);
lean_closure_set(x_73, 3, x_3);
lean_closure_set(x_73, 4, x_4);
lean_closure_set(x_73, 5, x_6);
lean_closure_set(x_73, 6, x_7);
lean_closure_set(x_73, 7, x_18);
lean_closure_set(x_73, 8, x_72);
lean_closure_set(x_73, 9, x_49);
lean_closure_set(x_73, 10, x_65);
lean_closure_set(x_73, 11, x_69);
lean_closure_set(x_73, 12, x_70);
x_74 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_74, 0, x_71);
lean_closure_set(x_74, 1, x_73);
x_75 = l_Lean_Meta_getMVarDecl(x_63, x_13, x_14, x_15, x_16, x_66);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 4);
lean_inc(x_79);
lean_dec(x_76);
x_80 = l_Lean_Meta_withLocalContext___rarg(x_78, x_79, x_74, x_13, x_14, x_15, x_16, x_77);
lean_dec(x_13);
return x_80;
}
else
{
uint8_t x_81; 
lean_dec(x_74);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_81 = !lean_is_exclusive(x_75);
if (x_81 == 0)
{
return x_75;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_75, 0);
x_83 = lean_ctor_get(x_75, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_75);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
block_94:
{
if (x_86 == 0)
{
x_66 = x_87;
goto block_85;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_inc(x_63);
x_88 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_88, 0, x_63);
x_89 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_90 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_92 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_91, x_90, x_13, x_14, x_15, x_16, x_87);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_66 = x_93;
goto block_85;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_57);
lean_dec(x_49);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_105 = !lean_is_exclusive(x_59);
if (x_105 == 0)
{
return x_59;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_59, 0);
x_107 = lean_ctor_get(x_59, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_59);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_49);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_109 = !lean_is_exclusive(x_54);
if (x_109 == 0)
{
return x_54;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_54, 0);
x_111 = lean_ctor_get(x_54, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_54);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_113 = !lean_is_exclusive(x_46);
if (x_113 == 0)
{
return x_46;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_46, 0);
x_115 = lean_ctor_get(x_46, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_46);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_34);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_36);
if (x_131 == 0)
{
return x_36;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_36, 0);
x_133 = lean_ctor_get(x_36, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_36);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_33);
if (x_135 == 0)
{
return x_33;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_33, 0);
x_137 = lean_ctor_get(x_33, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_33);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_19);
if (x_139 == 0)
{
return x_19;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_19, 0);
x_141 = lean_ctor_get(x_19, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_19);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
case 1:
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_12);
lean_dec(x_10);
x_143 = lean_ctor_get(x_7, 5);
lean_inc(x_143);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_144 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_143, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_st_ref_get(x_14, x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_ctor_get(x_7, 6);
lean_inc(x_150);
x_151 = l_List_redLength___main___rarg(x_150);
x_152 = lean_mk_empty_array_with_capacity(x_151);
lean_dec(x_151);
lean_inc(x_150);
x_153 = l_List_toArrayAux___main___rarg(x_150, x_152);
x_154 = x_153;
x_155 = lean_unsigned_to_nat(0u);
lean_inc(x_149);
lean_inc(x_6);
lean_inc(x_1);
x_156 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_156, 0, x_1);
lean_closure_set(x_156, 1, x_6);
lean_closure_set(x_156, 2, x_9);
lean_closure_set(x_156, 3, x_11);
lean_closure_set(x_156, 4, x_149);
lean_closure_set(x_156, 5, x_150);
lean_closure_set(x_156, 6, x_155);
lean_closure_set(x_156, 7, x_154);
x_157 = x_156;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_158 = lean_apply_5(x_157, x_13, x_14, x_15, x_16, x_148);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_1);
x_161 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_164 == 0)
{
lean_object* x_243; uint8_t x_244; 
x_243 = l_Lean_MetavarContext_exprDependsOn(x_149, x_162, x_2);
x_244 = lean_unbox(x_243);
lean_dec(x_243);
if (x_244 == 0)
{
x_165 = x_163;
goto block_242;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
lean_dec(x_159);
lean_dec(x_143);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_245 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_245, 0, x_3);
x_246 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_247 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_245);
x_248 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_249 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_box(0);
x_251 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_249, x_250, x_13, x_14, x_15, x_16, x_163);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_252 = !lean_is_exclusive(x_251);
if (x_252 == 0)
{
return x_251;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_251, 0);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_251);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
else
{
lean_dec(x_162);
lean_dec(x_149);
x_165 = x_163;
goto block_242;
}
block_242:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; 
lean_inc(x_159);
x_166 = x_159;
x_167 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_155, x_166);
x_168 = x_167;
x_169 = lean_array_push(x_168, x_2);
x_170 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_171 = l_Lean_Meta_revert(x_1, x_169, x_170, x_13, x_14, x_15, x_16, x_165);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
x_176 = lean_array_get_size(x_159);
x_177 = lean_box(0);
x_178 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_179 = l_Lean_Meta_introN(x_175, x_176, x_177, x_178, x_13, x_14, x_15, x_16, x_173);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_dec(x_180);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_184 = l_Lean_Meta_intro1(x_183, x_178, x_13, x_14, x_15, x_16, x_181);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_211; lean_object* x_212; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_ctor_get(x_185, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
lean_dec(x_185);
x_189 = lean_box(0);
x_190 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_159, x_182, x_159, x_155, x_189);
lean_dec(x_159);
x_220 = l_Lean_Core_getTraceState___rarg(x_16, x_186);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get_uint8(x_221, sizeof(void*)*1);
lean_dec(x_221);
if (x_222 == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
lean_dec(x_220);
x_211 = x_178;
x_212 = x_223;
goto block_219;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_224 = lean_ctor_get(x_220, 1);
lean_inc(x_224);
lean_dec(x_220);
x_225 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_226 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_225, x_15, x_16, x_224);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_unbox(x_227);
lean_dec(x_227);
x_211 = x_229;
x_212 = x_228;
goto block_219;
}
block_210:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_192 = x_182;
x_193 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_155, x_192);
x_194 = x_193;
lean_inc(x_187);
x_195 = l_Lean_mkFVar(x_187);
lean_inc(x_188);
x_196 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_196, 0, x_188);
x_197 = lean_box(x_164);
lean_inc(x_188);
x_198 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_198, 0, x_187);
lean_closure_set(x_198, 1, x_8);
lean_closure_set(x_198, 2, x_188);
lean_closure_set(x_198, 3, x_3);
lean_closure_set(x_198, 4, x_4);
lean_closure_set(x_198, 5, x_6);
lean_closure_set(x_198, 6, x_7);
lean_closure_set(x_198, 7, x_143);
lean_closure_set(x_198, 8, x_197);
lean_closure_set(x_198, 9, x_174);
lean_closure_set(x_198, 10, x_190);
lean_closure_set(x_198, 11, x_194);
lean_closure_set(x_198, 12, x_195);
x_199 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_199, 0, x_196);
lean_closure_set(x_199, 1, x_198);
x_200 = l_Lean_Meta_getMVarDecl(x_188, x_13, x_14, x_15, x_16, x_191);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_201, 4);
lean_inc(x_204);
lean_dec(x_201);
x_205 = l_Lean_Meta_withLocalContext___rarg(x_203, x_204, x_199, x_13, x_14, x_15, x_16, x_202);
lean_dec(x_13);
return x_205;
}
else
{
uint8_t x_206; 
lean_dec(x_199);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_206 = !lean_is_exclusive(x_200);
if (x_206 == 0)
{
return x_200;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_200, 0);
x_208 = lean_ctor_get(x_200, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_200);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
block_219:
{
if (x_211 == 0)
{
x_191 = x_212;
goto block_210;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_inc(x_188);
x_213 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_213, 0, x_188);
x_214 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_215 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_213);
x_216 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_217 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_216, x_215, x_13, x_14, x_15, x_16, x_212);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
x_191 = x_218;
goto block_210;
}
}
}
else
{
uint8_t x_230; 
lean_dec(x_182);
lean_dec(x_174);
lean_dec(x_159);
lean_dec(x_143);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_230 = !lean_is_exclusive(x_184);
if (x_230 == 0)
{
return x_184;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_184, 0);
x_232 = lean_ctor_get(x_184, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_184);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_174);
lean_dec(x_159);
lean_dec(x_143);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_234 = !lean_is_exclusive(x_179);
if (x_234 == 0)
{
return x_179;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_179, 0);
x_236 = lean_ctor_get(x_179, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_179);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_159);
lean_dec(x_143);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_238 = !lean_is_exclusive(x_171);
if (x_238 == 0)
{
return x_171;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_171, 0);
x_240 = lean_ctor_get(x_171, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_171);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
}
else
{
uint8_t x_256; 
lean_dec(x_159);
lean_dec(x_149);
lean_dec(x_143);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_256 = !lean_is_exclusive(x_161);
if (x_256 == 0)
{
return x_161;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_161, 0);
x_258 = lean_ctor_get(x_161, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_161);
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
lean_dec(x_149);
lean_dec(x_143);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_260 = !lean_is_exclusive(x_158);
if (x_260 == 0)
{
return x_158;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_158, 0);
x_262 = lean_ctor_get(x_158, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_158);
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
lean_dec(x_143);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_264 = !lean_is_exclusive(x_144);
if (x_264 == 0)
{
return x_144;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_144, 0);
x_266 = lean_ctor_get(x_144, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_144);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
}
case 2:
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_12);
lean_dec(x_10);
x_268 = lean_ctor_get(x_7, 5);
lean_inc(x_268);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_269 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_268, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_271 = lean_st_ref_get(x_14, x_270);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
lean_dec(x_272);
x_275 = lean_ctor_get(x_7, 6);
lean_inc(x_275);
x_276 = l_List_redLength___main___rarg(x_275);
x_277 = lean_mk_empty_array_with_capacity(x_276);
lean_dec(x_276);
lean_inc(x_275);
x_278 = l_List_toArrayAux___main___rarg(x_275, x_277);
x_279 = x_278;
x_280 = lean_unsigned_to_nat(0u);
lean_inc(x_274);
lean_inc(x_6);
lean_inc(x_1);
x_281 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_281, 0, x_1);
lean_closure_set(x_281, 1, x_6);
lean_closure_set(x_281, 2, x_9);
lean_closure_set(x_281, 3, x_11);
lean_closure_set(x_281, 4, x_274);
lean_closure_set(x_281, 5, x_275);
lean_closure_set(x_281, 6, x_280);
lean_closure_set(x_281, 7, x_279);
x_282 = x_281;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_283 = lean_apply_5(x_282, x_13, x_14, x_15, x_16, x_273);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
lean_inc(x_1);
x_286 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_285);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_289 == 0)
{
lean_object* x_368; uint8_t x_369; 
x_368 = l_Lean_MetavarContext_exprDependsOn(x_274, x_287, x_2);
x_369 = lean_unbox(x_368);
lean_dec(x_368);
if (x_369 == 0)
{
x_290 = x_288;
goto block_367;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; 
lean_dec(x_284);
lean_dec(x_268);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_370 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_370, 0, x_3);
x_371 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_372 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_370);
x_373 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_374 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
x_375 = lean_box(0);
x_376 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_374, x_375, x_13, x_14, x_15, x_16, x_288);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_377 = !lean_is_exclusive(x_376);
if (x_377 == 0)
{
return x_376;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_376, 0);
x_379 = lean_ctor_get(x_376, 1);
lean_inc(x_379);
lean_inc(x_378);
lean_dec(x_376);
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
return x_380;
}
}
}
else
{
lean_dec(x_287);
lean_dec(x_274);
x_290 = x_288;
goto block_367;
}
block_367:
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; 
lean_inc(x_284);
x_291 = x_284;
x_292 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_280, x_291);
x_293 = x_292;
x_294 = lean_array_push(x_293, x_2);
x_295 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_296 = l_Lean_Meta_revert(x_1, x_294, x_295, x_13, x_14, x_15, x_16, x_290);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_297, 1);
lean_inc(x_300);
lean_dec(x_297);
x_301 = lean_array_get_size(x_284);
x_302 = lean_box(0);
x_303 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_304 = l_Lean_Meta_introN(x_300, x_301, x_302, x_303, x_13, x_14, x_15, x_16, x_298);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_ctor_get(x_305, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_305, 1);
lean_inc(x_308);
lean_dec(x_305);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_309 = l_Lean_Meta_intro1(x_308, x_303, x_13, x_14, x_15, x_16, x_306);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_336; lean_object* x_337; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
x_312 = lean_ctor_get(x_310, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_310, 1);
lean_inc(x_313);
lean_dec(x_310);
x_314 = lean_box(0);
x_315 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_284, x_307, x_284, x_280, x_314);
lean_dec(x_284);
x_345 = l_Lean_Core_getTraceState___rarg(x_16, x_311);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get_uint8(x_346, sizeof(void*)*1);
lean_dec(x_346);
if (x_347 == 0)
{
lean_object* x_348; 
x_348 = lean_ctor_get(x_345, 1);
lean_inc(x_348);
lean_dec(x_345);
x_336 = x_303;
x_337 = x_348;
goto block_344;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_349 = lean_ctor_get(x_345, 1);
lean_inc(x_349);
lean_dec(x_345);
x_350 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_351 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_350, x_15, x_16, x_349);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = lean_unbox(x_352);
lean_dec(x_352);
x_336 = x_354;
x_337 = x_353;
goto block_344;
}
block_335:
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_317 = x_307;
x_318 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_280, x_317);
x_319 = x_318;
lean_inc(x_312);
x_320 = l_Lean_mkFVar(x_312);
lean_inc(x_313);
x_321 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_321, 0, x_313);
x_322 = lean_box(x_289);
lean_inc(x_313);
x_323 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_323, 0, x_312);
lean_closure_set(x_323, 1, x_8);
lean_closure_set(x_323, 2, x_313);
lean_closure_set(x_323, 3, x_3);
lean_closure_set(x_323, 4, x_4);
lean_closure_set(x_323, 5, x_6);
lean_closure_set(x_323, 6, x_7);
lean_closure_set(x_323, 7, x_268);
lean_closure_set(x_323, 8, x_322);
lean_closure_set(x_323, 9, x_299);
lean_closure_set(x_323, 10, x_315);
lean_closure_set(x_323, 11, x_319);
lean_closure_set(x_323, 12, x_320);
x_324 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_324, 0, x_321);
lean_closure_set(x_324, 1, x_323);
x_325 = l_Lean_Meta_getMVarDecl(x_313, x_13, x_14, x_15, x_16, x_316);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
lean_dec(x_325);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_326, 4);
lean_inc(x_329);
lean_dec(x_326);
x_330 = l_Lean_Meta_withLocalContext___rarg(x_328, x_329, x_324, x_13, x_14, x_15, x_16, x_327);
lean_dec(x_13);
return x_330;
}
else
{
uint8_t x_331; 
lean_dec(x_324);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_331 = !lean_is_exclusive(x_325);
if (x_331 == 0)
{
return x_325;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_325, 0);
x_333 = lean_ctor_get(x_325, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_325);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
}
block_344:
{
if (x_336 == 0)
{
x_316 = x_337;
goto block_335;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_inc(x_313);
x_338 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_338, 0, x_313);
x_339 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_340 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_338);
x_341 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_342 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_341, x_340, x_13, x_14, x_15, x_16, x_337);
x_343 = lean_ctor_get(x_342, 1);
lean_inc(x_343);
lean_dec(x_342);
x_316 = x_343;
goto block_335;
}
}
}
else
{
uint8_t x_355; 
lean_dec(x_307);
lean_dec(x_299);
lean_dec(x_284);
lean_dec(x_268);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_355 = !lean_is_exclusive(x_309);
if (x_355 == 0)
{
return x_309;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_309, 0);
x_357 = lean_ctor_get(x_309, 1);
lean_inc(x_357);
lean_inc(x_356);
lean_dec(x_309);
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
return x_358;
}
}
}
else
{
uint8_t x_359; 
lean_dec(x_299);
lean_dec(x_284);
lean_dec(x_268);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_359 = !lean_is_exclusive(x_304);
if (x_359 == 0)
{
return x_304;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_304, 0);
x_361 = lean_ctor_get(x_304, 1);
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_304);
x_362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_361);
return x_362;
}
}
}
else
{
uint8_t x_363; 
lean_dec(x_284);
lean_dec(x_268);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_363 = !lean_is_exclusive(x_296);
if (x_363 == 0)
{
return x_296;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_364 = lean_ctor_get(x_296, 0);
x_365 = lean_ctor_get(x_296, 1);
lean_inc(x_365);
lean_inc(x_364);
lean_dec(x_296);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
return x_366;
}
}
}
}
else
{
uint8_t x_381; 
lean_dec(x_284);
lean_dec(x_274);
lean_dec(x_268);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_381 = !lean_is_exclusive(x_286);
if (x_381 == 0)
{
return x_286;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_286, 0);
x_383 = lean_ctor_get(x_286, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_286);
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
lean_dec(x_274);
lean_dec(x_268);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_385 = !lean_is_exclusive(x_283);
if (x_385 == 0)
{
return x_283;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_283, 0);
x_387 = lean_ctor_get(x_283, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_283);
x_388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
return x_388;
}
}
}
else
{
uint8_t x_389; 
lean_dec(x_268);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_389 = !lean_is_exclusive(x_269);
if (x_389 == 0)
{
return x_269;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_269, 0);
x_391 = lean_ctor_get(x_269, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_269);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
case 3:
{
lean_object* x_393; lean_object* x_394; 
lean_dec(x_12);
lean_dec(x_10);
x_393 = lean_ctor_get(x_7, 5);
lean_inc(x_393);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_394 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_393, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_395 = lean_ctor_get(x_394, 1);
lean_inc(x_395);
lean_dec(x_394);
x_396 = lean_st_ref_get(x_14, x_395);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_399 = lean_ctor_get(x_397, 0);
lean_inc(x_399);
lean_dec(x_397);
x_400 = lean_ctor_get(x_7, 6);
lean_inc(x_400);
x_401 = l_List_redLength___main___rarg(x_400);
x_402 = lean_mk_empty_array_with_capacity(x_401);
lean_dec(x_401);
lean_inc(x_400);
x_403 = l_List_toArrayAux___main___rarg(x_400, x_402);
x_404 = x_403;
x_405 = lean_unsigned_to_nat(0u);
lean_inc(x_399);
lean_inc(x_6);
lean_inc(x_1);
x_406 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_406, 0, x_1);
lean_closure_set(x_406, 1, x_6);
lean_closure_set(x_406, 2, x_9);
lean_closure_set(x_406, 3, x_11);
lean_closure_set(x_406, 4, x_399);
lean_closure_set(x_406, 5, x_400);
lean_closure_set(x_406, 6, x_405);
lean_closure_set(x_406, 7, x_404);
x_407 = x_406;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_408 = lean_apply_5(x_407, x_13, x_14, x_15, x_16, x_398);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
lean_inc(x_1);
x_411 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_410);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; uint8_t x_414; lean_object* x_415; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_414 == 0)
{
lean_object* x_493; uint8_t x_494; 
x_493 = l_Lean_MetavarContext_exprDependsOn(x_399, x_412, x_2);
x_494 = lean_unbox(x_493);
lean_dec(x_493);
if (x_494 == 0)
{
x_415 = x_413;
goto block_492;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; 
lean_dec(x_409);
lean_dec(x_393);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_495 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_495, 0, x_3);
x_496 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_497 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_497, 0, x_496);
lean_ctor_set(x_497, 1, x_495);
x_498 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_499 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_499, 0, x_497);
lean_ctor_set(x_499, 1, x_498);
x_500 = lean_box(0);
x_501 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_499, x_500, x_13, x_14, x_15, x_16, x_413);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_502 = !lean_is_exclusive(x_501);
if (x_502 == 0)
{
return x_501;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_501, 0);
x_504 = lean_ctor_get(x_501, 1);
lean_inc(x_504);
lean_inc(x_503);
lean_dec(x_501);
x_505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_504);
return x_505;
}
}
}
else
{
lean_dec(x_412);
lean_dec(x_399);
x_415 = x_413;
goto block_492;
}
block_492:
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; lean_object* x_421; 
lean_inc(x_409);
x_416 = x_409;
x_417 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_405, x_416);
x_418 = x_417;
x_419 = lean_array_push(x_418, x_2);
x_420 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_421 = l_Lean_Meta_revert(x_1, x_419, x_420, x_13, x_14, x_15, x_16, x_415);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; lean_object* x_429; 
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_421, 1);
lean_inc(x_423);
lean_dec(x_421);
x_424 = lean_ctor_get(x_422, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_422, 1);
lean_inc(x_425);
lean_dec(x_422);
x_426 = lean_array_get_size(x_409);
x_427 = lean_box(0);
x_428 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_429 = l_Lean_Meta_introN(x_425, x_426, x_427, x_428, x_13, x_14, x_15, x_16, x_423);
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_430 = lean_ctor_get(x_429, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_429, 1);
lean_inc(x_431);
lean_dec(x_429);
x_432 = lean_ctor_get(x_430, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_430, 1);
lean_inc(x_433);
lean_dec(x_430);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_434 = l_Lean_Meta_intro1(x_433, x_428, x_13, x_14, x_15, x_16, x_431);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_461; lean_object* x_462; lean_object* x_470; lean_object* x_471; uint8_t x_472; 
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_434, 1);
lean_inc(x_436);
lean_dec(x_434);
x_437 = lean_ctor_get(x_435, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_435, 1);
lean_inc(x_438);
lean_dec(x_435);
x_439 = lean_box(0);
x_440 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_409, x_432, x_409, x_405, x_439);
lean_dec(x_409);
x_470 = l_Lean_Core_getTraceState___rarg(x_16, x_436);
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get_uint8(x_471, sizeof(void*)*1);
lean_dec(x_471);
if (x_472 == 0)
{
lean_object* x_473; 
x_473 = lean_ctor_get(x_470, 1);
lean_inc(x_473);
lean_dec(x_470);
x_461 = x_428;
x_462 = x_473;
goto block_469;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; 
x_474 = lean_ctor_get(x_470, 1);
lean_inc(x_474);
lean_dec(x_470);
x_475 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_476 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_475, x_15, x_16, x_474);
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
lean_dec(x_476);
x_479 = lean_unbox(x_477);
lean_dec(x_477);
x_461 = x_479;
x_462 = x_478;
goto block_469;
}
block_460:
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_442 = x_432;
x_443 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_405, x_442);
x_444 = x_443;
lean_inc(x_437);
x_445 = l_Lean_mkFVar(x_437);
lean_inc(x_438);
x_446 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_446, 0, x_438);
x_447 = lean_box(x_414);
lean_inc(x_438);
x_448 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_448, 0, x_437);
lean_closure_set(x_448, 1, x_8);
lean_closure_set(x_448, 2, x_438);
lean_closure_set(x_448, 3, x_3);
lean_closure_set(x_448, 4, x_4);
lean_closure_set(x_448, 5, x_6);
lean_closure_set(x_448, 6, x_7);
lean_closure_set(x_448, 7, x_393);
lean_closure_set(x_448, 8, x_447);
lean_closure_set(x_448, 9, x_424);
lean_closure_set(x_448, 10, x_440);
lean_closure_set(x_448, 11, x_444);
lean_closure_set(x_448, 12, x_445);
x_449 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_449, 0, x_446);
lean_closure_set(x_449, 1, x_448);
x_450 = l_Lean_Meta_getMVarDecl(x_438, x_13, x_14, x_15, x_16, x_441);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
lean_dec(x_450);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
x_454 = lean_ctor_get(x_451, 4);
lean_inc(x_454);
lean_dec(x_451);
x_455 = l_Lean_Meta_withLocalContext___rarg(x_453, x_454, x_449, x_13, x_14, x_15, x_16, x_452);
lean_dec(x_13);
return x_455;
}
else
{
uint8_t x_456; 
lean_dec(x_449);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_456 = !lean_is_exclusive(x_450);
if (x_456 == 0)
{
return x_450;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_450, 0);
x_458 = lean_ctor_get(x_450, 1);
lean_inc(x_458);
lean_inc(x_457);
lean_dec(x_450);
x_459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set(x_459, 1, x_458);
return x_459;
}
}
}
block_469:
{
if (x_461 == 0)
{
x_441 = x_462;
goto block_460;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
lean_inc(x_438);
x_463 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_463, 0, x_438);
x_464 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_465 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_463);
x_466 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_467 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_466, x_465, x_13, x_14, x_15, x_16, x_462);
x_468 = lean_ctor_get(x_467, 1);
lean_inc(x_468);
lean_dec(x_467);
x_441 = x_468;
goto block_460;
}
}
}
else
{
uint8_t x_480; 
lean_dec(x_432);
lean_dec(x_424);
lean_dec(x_409);
lean_dec(x_393);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_480 = !lean_is_exclusive(x_434);
if (x_480 == 0)
{
return x_434;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_434, 0);
x_482 = lean_ctor_get(x_434, 1);
lean_inc(x_482);
lean_inc(x_481);
lean_dec(x_434);
x_483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_483, 0, x_481);
lean_ctor_set(x_483, 1, x_482);
return x_483;
}
}
}
else
{
uint8_t x_484; 
lean_dec(x_424);
lean_dec(x_409);
lean_dec(x_393);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_484 = !lean_is_exclusive(x_429);
if (x_484 == 0)
{
return x_429;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_485 = lean_ctor_get(x_429, 0);
x_486 = lean_ctor_get(x_429, 1);
lean_inc(x_486);
lean_inc(x_485);
lean_dec(x_429);
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_485);
lean_ctor_set(x_487, 1, x_486);
return x_487;
}
}
}
else
{
uint8_t x_488; 
lean_dec(x_409);
lean_dec(x_393);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_488 = !lean_is_exclusive(x_421);
if (x_488 == 0)
{
return x_421;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_489 = lean_ctor_get(x_421, 0);
x_490 = lean_ctor_get(x_421, 1);
lean_inc(x_490);
lean_inc(x_489);
lean_dec(x_421);
x_491 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_491, 0, x_489);
lean_ctor_set(x_491, 1, x_490);
return x_491;
}
}
}
}
else
{
uint8_t x_506; 
lean_dec(x_409);
lean_dec(x_399);
lean_dec(x_393);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_506 = !lean_is_exclusive(x_411);
if (x_506 == 0)
{
return x_411;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_411, 0);
x_508 = lean_ctor_get(x_411, 1);
lean_inc(x_508);
lean_inc(x_507);
lean_dec(x_411);
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
lean_dec(x_399);
lean_dec(x_393);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_510 = !lean_is_exclusive(x_408);
if (x_510 == 0)
{
return x_408;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_511 = lean_ctor_get(x_408, 0);
x_512 = lean_ctor_get(x_408, 1);
lean_inc(x_512);
lean_inc(x_511);
lean_dec(x_408);
x_513 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_513, 0, x_511);
lean_ctor_set(x_513, 1, x_512);
return x_513;
}
}
}
else
{
uint8_t x_514; 
lean_dec(x_393);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_514 = !lean_is_exclusive(x_394);
if (x_514 == 0)
{
return x_394;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_515 = lean_ctor_get(x_394, 0);
x_516 = lean_ctor_get(x_394, 1);
lean_inc(x_516);
lean_inc(x_515);
lean_dec(x_394);
x_517 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_517, 0, x_515);
lean_ctor_set(x_517, 1, x_516);
return x_517;
}
}
}
case 4:
{
lean_object* x_518; lean_object* x_519; 
lean_dec(x_12);
lean_dec(x_10);
x_518 = lean_ctor_get(x_7, 5);
lean_inc(x_518);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_519 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_518, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_520 = lean_ctor_get(x_519, 1);
lean_inc(x_520);
lean_dec(x_519);
x_521 = lean_st_ref_get(x_14, x_520);
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 1);
lean_inc(x_523);
lean_dec(x_521);
x_524 = lean_ctor_get(x_522, 0);
lean_inc(x_524);
lean_dec(x_522);
x_525 = lean_ctor_get(x_7, 6);
lean_inc(x_525);
x_526 = l_List_redLength___main___rarg(x_525);
x_527 = lean_mk_empty_array_with_capacity(x_526);
lean_dec(x_526);
lean_inc(x_525);
x_528 = l_List_toArrayAux___main___rarg(x_525, x_527);
x_529 = x_528;
x_530 = lean_unsigned_to_nat(0u);
lean_inc(x_524);
lean_inc(x_6);
lean_inc(x_1);
x_531 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_531, 0, x_1);
lean_closure_set(x_531, 1, x_6);
lean_closure_set(x_531, 2, x_9);
lean_closure_set(x_531, 3, x_11);
lean_closure_set(x_531, 4, x_524);
lean_closure_set(x_531, 5, x_525);
lean_closure_set(x_531, 6, x_530);
lean_closure_set(x_531, 7, x_529);
x_532 = x_531;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_533 = lean_apply_5(x_532, x_13, x_14, x_15, x_16, x_523);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
lean_dec(x_533);
lean_inc(x_1);
x_536 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_535);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; 
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
lean_dec(x_536);
x_539 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_539 == 0)
{
lean_object* x_618; uint8_t x_619; 
x_618 = l_Lean_MetavarContext_exprDependsOn(x_524, x_537, x_2);
x_619 = lean_unbox(x_618);
lean_dec(x_618);
if (x_619 == 0)
{
x_540 = x_538;
goto block_617;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; 
lean_dec(x_534);
lean_dec(x_518);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_620 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_620, 0, x_3);
x_621 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_622 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_620);
x_623 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_624 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_624, 0, x_622);
lean_ctor_set(x_624, 1, x_623);
x_625 = lean_box(0);
x_626 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_624, x_625, x_13, x_14, x_15, x_16, x_538);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_627 = !lean_is_exclusive(x_626);
if (x_627 == 0)
{
return x_626;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_626, 0);
x_629 = lean_ctor_get(x_626, 1);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_626);
x_630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
return x_630;
}
}
}
else
{
lean_dec(x_537);
lean_dec(x_524);
x_540 = x_538;
goto block_617;
}
block_617:
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; uint8_t x_545; lean_object* x_546; 
lean_inc(x_534);
x_541 = x_534;
x_542 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_530, x_541);
x_543 = x_542;
x_544 = lean_array_push(x_543, x_2);
x_545 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_546 = l_Lean_Meta_revert(x_1, x_544, x_545, x_13, x_14, x_15, x_16, x_540);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; uint8_t x_553; lean_object* x_554; 
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_546, 1);
lean_inc(x_548);
lean_dec(x_546);
x_549 = lean_ctor_get(x_547, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_547, 1);
lean_inc(x_550);
lean_dec(x_547);
x_551 = lean_array_get_size(x_534);
x_552 = lean_box(0);
x_553 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_554 = l_Lean_Meta_introN(x_550, x_551, x_552, x_553, x_13, x_14, x_15, x_16, x_548);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
x_557 = lean_ctor_get(x_555, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_555, 1);
lean_inc(x_558);
lean_dec(x_555);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_559 = l_Lean_Meta_intro1(x_558, x_553, x_13, x_14, x_15, x_16, x_556);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; uint8_t x_586; lean_object* x_587; lean_object* x_595; lean_object* x_596; uint8_t x_597; 
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
lean_dec(x_559);
x_562 = lean_ctor_get(x_560, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_560, 1);
lean_inc(x_563);
lean_dec(x_560);
x_564 = lean_box(0);
x_565 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_534, x_557, x_534, x_530, x_564);
lean_dec(x_534);
x_595 = l_Lean_Core_getTraceState___rarg(x_16, x_561);
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
x_597 = lean_ctor_get_uint8(x_596, sizeof(void*)*1);
lean_dec(x_596);
if (x_597 == 0)
{
lean_object* x_598; 
x_598 = lean_ctor_get(x_595, 1);
lean_inc(x_598);
lean_dec(x_595);
x_586 = x_553;
x_587 = x_598;
goto block_594;
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; 
x_599 = lean_ctor_get(x_595, 1);
lean_inc(x_599);
lean_dec(x_595);
x_600 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_601 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_600, x_15, x_16, x_599);
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
lean_dec(x_601);
x_604 = lean_unbox(x_602);
lean_dec(x_602);
x_586 = x_604;
x_587 = x_603;
goto block_594;
}
block_585:
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_567 = x_557;
x_568 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_530, x_567);
x_569 = x_568;
lean_inc(x_562);
x_570 = l_Lean_mkFVar(x_562);
lean_inc(x_563);
x_571 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_571, 0, x_563);
x_572 = lean_box(x_539);
lean_inc(x_563);
x_573 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_573, 0, x_562);
lean_closure_set(x_573, 1, x_8);
lean_closure_set(x_573, 2, x_563);
lean_closure_set(x_573, 3, x_3);
lean_closure_set(x_573, 4, x_4);
lean_closure_set(x_573, 5, x_6);
lean_closure_set(x_573, 6, x_7);
lean_closure_set(x_573, 7, x_518);
lean_closure_set(x_573, 8, x_572);
lean_closure_set(x_573, 9, x_549);
lean_closure_set(x_573, 10, x_565);
lean_closure_set(x_573, 11, x_569);
lean_closure_set(x_573, 12, x_570);
x_574 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_574, 0, x_571);
lean_closure_set(x_574, 1, x_573);
x_575 = l_Lean_Meta_getMVarDecl(x_563, x_13, x_14, x_15, x_16, x_566);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_576 = lean_ctor_get(x_575, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_575, 1);
lean_inc(x_577);
lean_dec(x_575);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
x_579 = lean_ctor_get(x_576, 4);
lean_inc(x_579);
lean_dec(x_576);
x_580 = l_Lean_Meta_withLocalContext___rarg(x_578, x_579, x_574, x_13, x_14, x_15, x_16, x_577);
lean_dec(x_13);
return x_580;
}
else
{
uint8_t x_581; 
lean_dec(x_574);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_581 = !lean_is_exclusive(x_575);
if (x_581 == 0)
{
return x_575;
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_582 = lean_ctor_get(x_575, 0);
x_583 = lean_ctor_get(x_575, 1);
lean_inc(x_583);
lean_inc(x_582);
lean_dec(x_575);
x_584 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_584, 0, x_582);
lean_ctor_set(x_584, 1, x_583);
return x_584;
}
}
}
block_594:
{
if (x_586 == 0)
{
x_566 = x_587;
goto block_585;
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
lean_inc(x_563);
x_588 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_588, 0, x_563);
x_589 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_590 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_588);
x_591 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_592 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_591, x_590, x_13, x_14, x_15, x_16, x_587);
x_593 = lean_ctor_get(x_592, 1);
lean_inc(x_593);
lean_dec(x_592);
x_566 = x_593;
goto block_585;
}
}
}
else
{
uint8_t x_605; 
lean_dec(x_557);
lean_dec(x_549);
lean_dec(x_534);
lean_dec(x_518);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_605 = !lean_is_exclusive(x_559);
if (x_605 == 0)
{
return x_559;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_606 = lean_ctor_get(x_559, 0);
x_607 = lean_ctor_get(x_559, 1);
lean_inc(x_607);
lean_inc(x_606);
lean_dec(x_559);
x_608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_608, 0, x_606);
lean_ctor_set(x_608, 1, x_607);
return x_608;
}
}
}
else
{
uint8_t x_609; 
lean_dec(x_549);
lean_dec(x_534);
lean_dec(x_518);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_609 = !lean_is_exclusive(x_554);
if (x_609 == 0)
{
return x_554;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_610 = lean_ctor_get(x_554, 0);
x_611 = lean_ctor_get(x_554, 1);
lean_inc(x_611);
lean_inc(x_610);
lean_dec(x_554);
x_612 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_612, 0, x_610);
lean_ctor_set(x_612, 1, x_611);
return x_612;
}
}
}
else
{
uint8_t x_613; 
lean_dec(x_534);
lean_dec(x_518);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_613 = !lean_is_exclusive(x_546);
if (x_613 == 0)
{
return x_546;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = lean_ctor_get(x_546, 0);
x_615 = lean_ctor_get(x_546, 1);
lean_inc(x_615);
lean_inc(x_614);
lean_dec(x_546);
x_616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_616, 0, x_614);
lean_ctor_set(x_616, 1, x_615);
return x_616;
}
}
}
}
else
{
uint8_t x_631; 
lean_dec(x_534);
lean_dec(x_524);
lean_dec(x_518);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_631 = !lean_is_exclusive(x_536);
if (x_631 == 0)
{
return x_536;
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_632 = lean_ctor_get(x_536, 0);
x_633 = lean_ctor_get(x_536, 1);
lean_inc(x_633);
lean_inc(x_632);
lean_dec(x_536);
x_634 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_634, 0, x_632);
lean_ctor_set(x_634, 1, x_633);
return x_634;
}
}
}
else
{
uint8_t x_635; 
lean_dec(x_524);
lean_dec(x_518);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_635 = !lean_is_exclusive(x_533);
if (x_635 == 0)
{
return x_533;
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_636 = lean_ctor_get(x_533, 0);
x_637 = lean_ctor_get(x_533, 1);
lean_inc(x_637);
lean_inc(x_636);
lean_dec(x_533);
x_638 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_638, 0, x_636);
lean_ctor_set(x_638, 1, x_637);
return x_638;
}
}
}
else
{
uint8_t x_639; 
lean_dec(x_518);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_639 = !lean_is_exclusive(x_519);
if (x_639 == 0)
{
return x_519;
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_640 = lean_ctor_get(x_519, 0);
x_641 = lean_ctor_get(x_519, 1);
lean_inc(x_641);
lean_inc(x_640);
lean_dec(x_519);
x_642 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_642, 0, x_640);
lean_ctor_set(x_642, 1, x_641);
return x_642;
}
}
}
case 5:
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_643 = lean_ctor_get(x_10, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_10, 1);
lean_inc(x_644);
lean_dec(x_10);
x_645 = lean_array_set(x_11, x_12, x_644);
x_646 = lean_unsigned_to_nat(1u);
x_647 = lean_nat_sub(x_12, x_646);
lean_dec(x_12);
x_10 = x_643;
x_11 = x_645;
x_12 = x_647;
goto _start;
}
case 6:
{
lean_object* x_649; lean_object* x_650; 
lean_dec(x_12);
lean_dec(x_10);
x_649 = lean_ctor_get(x_7, 5);
lean_inc(x_649);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_650 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_649, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_650) == 0)
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_651 = lean_ctor_get(x_650, 1);
lean_inc(x_651);
lean_dec(x_650);
x_652 = lean_st_ref_get(x_14, x_651);
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_652, 1);
lean_inc(x_654);
lean_dec(x_652);
x_655 = lean_ctor_get(x_653, 0);
lean_inc(x_655);
lean_dec(x_653);
x_656 = lean_ctor_get(x_7, 6);
lean_inc(x_656);
x_657 = l_List_redLength___main___rarg(x_656);
x_658 = lean_mk_empty_array_with_capacity(x_657);
lean_dec(x_657);
lean_inc(x_656);
x_659 = l_List_toArrayAux___main___rarg(x_656, x_658);
x_660 = x_659;
x_661 = lean_unsigned_to_nat(0u);
lean_inc(x_655);
lean_inc(x_6);
lean_inc(x_1);
x_662 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_662, 0, x_1);
lean_closure_set(x_662, 1, x_6);
lean_closure_set(x_662, 2, x_9);
lean_closure_set(x_662, 3, x_11);
lean_closure_set(x_662, 4, x_655);
lean_closure_set(x_662, 5, x_656);
lean_closure_set(x_662, 6, x_661);
lean_closure_set(x_662, 7, x_660);
x_663 = x_662;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_664 = lean_apply_5(x_663, x_13, x_14, x_15, x_16, x_654);
if (lean_obj_tag(x_664) == 0)
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_664, 1);
lean_inc(x_666);
lean_dec(x_664);
lean_inc(x_1);
x_667 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_666);
if (lean_obj_tag(x_667) == 0)
{
lean_object* x_668; lean_object* x_669; uint8_t x_670; lean_object* x_671; 
x_668 = lean_ctor_get(x_667, 0);
lean_inc(x_668);
x_669 = lean_ctor_get(x_667, 1);
lean_inc(x_669);
lean_dec(x_667);
x_670 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_670 == 0)
{
lean_object* x_749; uint8_t x_750; 
x_749 = l_Lean_MetavarContext_exprDependsOn(x_655, x_668, x_2);
x_750 = lean_unbox(x_749);
lean_dec(x_749);
if (x_750 == 0)
{
x_671 = x_669;
goto block_748;
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; uint8_t x_758; 
lean_dec(x_665);
lean_dec(x_649);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_751 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_751, 0, x_3);
x_752 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_753 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_753, 0, x_752);
lean_ctor_set(x_753, 1, x_751);
x_754 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_755 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_755, 0, x_753);
lean_ctor_set(x_755, 1, x_754);
x_756 = lean_box(0);
x_757 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_755, x_756, x_13, x_14, x_15, x_16, x_669);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_758 = !lean_is_exclusive(x_757);
if (x_758 == 0)
{
return x_757;
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_759 = lean_ctor_get(x_757, 0);
x_760 = lean_ctor_get(x_757, 1);
lean_inc(x_760);
lean_inc(x_759);
lean_dec(x_757);
x_761 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_761, 0, x_759);
lean_ctor_set(x_761, 1, x_760);
return x_761;
}
}
}
else
{
lean_dec(x_668);
lean_dec(x_655);
x_671 = x_669;
goto block_748;
}
block_748:
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; lean_object* x_677; 
lean_inc(x_665);
x_672 = x_665;
x_673 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_661, x_672);
x_674 = x_673;
x_675 = lean_array_push(x_674, x_2);
x_676 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_677 = l_Lean_Meta_revert(x_1, x_675, x_676, x_13, x_14, x_15, x_16, x_671);
if (lean_obj_tag(x_677) == 0)
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; uint8_t x_684; lean_object* x_685; 
x_678 = lean_ctor_get(x_677, 0);
lean_inc(x_678);
x_679 = lean_ctor_get(x_677, 1);
lean_inc(x_679);
lean_dec(x_677);
x_680 = lean_ctor_get(x_678, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_678, 1);
lean_inc(x_681);
lean_dec(x_678);
x_682 = lean_array_get_size(x_665);
x_683 = lean_box(0);
x_684 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_685 = l_Lean_Meta_introN(x_681, x_682, x_683, x_684, x_13, x_14, x_15, x_16, x_679);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_685, 1);
lean_inc(x_687);
lean_dec(x_685);
x_688 = lean_ctor_get(x_686, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_686, 1);
lean_inc(x_689);
lean_dec(x_686);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_690 = l_Lean_Meta_intro1(x_689, x_684, x_13, x_14, x_15, x_16, x_687);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; uint8_t x_717; lean_object* x_718; lean_object* x_726; lean_object* x_727; uint8_t x_728; 
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_690, 1);
lean_inc(x_692);
lean_dec(x_690);
x_693 = lean_ctor_get(x_691, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_691, 1);
lean_inc(x_694);
lean_dec(x_691);
x_695 = lean_box(0);
x_696 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_665, x_688, x_665, x_661, x_695);
lean_dec(x_665);
x_726 = l_Lean_Core_getTraceState___rarg(x_16, x_692);
x_727 = lean_ctor_get(x_726, 0);
lean_inc(x_727);
x_728 = lean_ctor_get_uint8(x_727, sizeof(void*)*1);
lean_dec(x_727);
if (x_728 == 0)
{
lean_object* x_729; 
x_729 = lean_ctor_get(x_726, 1);
lean_inc(x_729);
lean_dec(x_726);
x_717 = x_684;
x_718 = x_729;
goto block_725;
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; uint8_t x_735; 
x_730 = lean_ctor_get(x_726, 1);
lean_inc(x_730);
lean_dec(x_726);
x_731 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_732 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_731, x_15, x_16, x_730);
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_732, 1);
lean_inc(x_734);
lean_dec(x_732);
x_735 = lean_unbox(x_733);
lean_dec(x_733);
x_717 = x_735;
x_718 = x_734;
goto block_725;
}
block_716:
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_698 = x_688;
x_699 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_661, x_698);
x_700 = x_699;
lean_inc(x_693);
x_701 = l_Lean_mkFVar(x_693);
lean_inc(x_694);
x_702 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_702, 0, x_694);
x_703 = lean_box(x_670);
lean_inc(x_694);
x_704 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_704, 0, x_693);
lean_closure_set(x_704, 1, x_8);
lean_closure_set(x_704, 2, x_694);
lean_closure_set(x_704, 3, x_3);
lean_closure_set(x_704, 4, x_4);
lean_closure_set(x_704, 5, x_6);
lean_closure_set(x_704, 6, x_7);
lean_closure_set(x_704, 7, x_649);
lean_closure_set(x_704, 8, x_703);
lean_closure_set(x_704, 9, x_680);
lean_closure_set(x_704, 10, x_696);
lean_closure_set(x_704, 11, x_700);
lean_closure_set(x_704, 12, x_701);
x_705 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_705, 0, x_702);
lean_closure_set(x_705, 1, x_704);
x_706 = l_Lean_Meta_getMVarDecl(x_694, x_13, x_14, x_15, x_16, x_697);
if (lean_obj_tag(x_706) == 0)
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_707 = lean_ctor_get(x_706, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_706, 1);
lean_inc(x_708);
lean_dec(x_706);
x_709 = lean_ctor_get(x_707, 1);
lean_inc(x_709);
x_710 = lean_ctor_get(x_707, 4);
lean_inc(x_710);
lean_dec(x_707);
x_711 = l_Lean_Meta_withLocalContext___rarg(x_709, x_710, x_705, x_13, x_14, x_15, x_16, x_708);
lean_dec(x_13);
return x_711;
}
else
{
uint8_t x_712; 
lean_dec(x_705);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_712 = !lean_is_exclusive(x_706);
if (x_712 == 0)
{
return x_706;
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_713 = lean_ctor_get(x_706, 0);
x_714 = lean_ctor_get(x_706, 1);
lean_inc(x_714);
lean_inc(x_713);
lean_dec(x_706);
x_715 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_715, 0, x_713);
lean_ctor_set(x_715, 1, x_714);
return x_715;
}
}
}
block_725:
{
if (x_717 == 0)
{
x_697 = x_718;
goto block_716;
}
else
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
lean_inc(x_694);
x_719 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_719, 0, x_694);
x_720 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_721 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_721, 0, x_720);
lean_ctor_set(x_721, 1, x_719);
x_722 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_723 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_722, x_721, x_13, x_14, x_15, x_16, x_718);
x_724 = lean_ctor_get(x_723, 1);
lean_inc(x_724);
lean_dec(x_723);
x_697 = x_724;
goto block_716;
}
}
}
else
{
uint8_t x_736; 
lean_dec(x_688);
lean_dec(x_680);
lean_dec(x_665);
lean_dec(x_649);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_736 = !lean_is_exclusive(x_690);
if (x_736 == 0)
{
return x_690;
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_737 = lean_ctor_get(x_690, 0);
x_738 = lean_ctor_get(x_690, 1);
lean_inc(x_738);
lean_inc(x_737);
lean_dec(x_690);
x_739 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_739, 0, x_737);
lean_ctor_set(x_739, 1, x_738);
return x_739;
}
}
}
else
{
uint8_t x_740; 
lean_dec(x_680);
lean_dec(x_665);
lean_dec(x_649);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_740 = !lean_is_exclusive(x_685);
if (x_740 == 0)
{
return x_685;
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_741 = lean_ctor_get(x_685, 0);
x_742 = lean_ctor_get(x_685, 1);
lean_inc(x_742);
lean_inc(x_741);
lean_dec(x_685);
x_743 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_743, 0, x_741);
lean_ctor_set(x_743, 1, x_742);
return x_743;
}
}
}
else
{
uint8_t x_744; 
lean_dec(x_665);
lean_dec(x_649);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_744 = !lean_is_exclusive(x_677);
if (x_744 == 0)
{
return x_677;
}
else
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_745 = lean_ctor_get(x_677, 0);
x_746 = lean_ctor_get(x_677, 1);
lean_inc(x_746);
lean_inc(x_745);
lean_dec(x_677);
x_747 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_747, 0, x_745);
lean_ctor_set(x_747, 1, x_746);
return x_747;
}
}
}
}
else
{
uint8_t x_762; 
lean_dec(x_665);
lean_dec(x_655);
lean_dec(x_649);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_762 = !lean_is_exclusive(x_667);
if (x_762 == 0)
{
return x_667;
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; 
x_763 = lean_ctor_get(x_667, 0);
x_764 = lean_ctor_get(x_667, 1);
lean_inc(x_764);
lean_inc(x_763);
lean_dec(x_667);
x_765 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_765, 0, x_763);
lean_ctor_set(x_765, 1, x_764);
return x_765;
}
}
}
else
{
uint8_t x_766; 
lean_dec(x_655);
lean_dec(x_649);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_766 = !lean_is_exclusive(x_664);
if (x_766 == 0)
{
return x_664;
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_767 = lean_ctor_get(x_664, 0);
x_768 = lean_ctor_get(x_664, 1);
lean_inc(x_768);
lean_inc(x_767);
lean_dec(x_664);
x_769 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_769, 0, x_767);
lean_ctor_set(x_769, 1, x_768);
return x_769;
}
}
}
else
{
uint8_t x_770; 
lean_dec(x_649);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_770 = !lean_is_exclusive(x_650);
if (x_770 == 0)
{
return x_650;
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_771 = lean_ctor_get(x_650, 0);
x_772 = lean_ctor_get(x_650, 1);
lean_inc(x_772);
lean_inc(x_771);
lean_dec(x_650);
x_773 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_773, 0, x_771);
lean_ctor_set(x_773, 1, x_772);
return x_773;
}
}
}
case 7:
{
lean_object* x_774; lean_object* x_775; 
lean_dec(x_12);
lean_dec(x_10);
x_774 = lean_ctor_get(x_7, 5);
lean_inc(x_774);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_775 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_774, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_775) == 0)
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_776 = lean_ctor_get(x_775, 1);
lean_inc(x_776);
lean_dec(x_775);
x_777 = lean_st_ref_get(x_14, x_776);
x_778 = lean_ctor_get(x_777, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_777, 1);
lean_inc(x_779);
lean_dec(x_777);
x_780 = lean_ctor_get(x_778, 0);
lean_inc(x_780);
lean_dec(x_778);
x_781 = lean_ctor_get(x_7, 6);
lean_inc(x_781);
x_782 = l_List_redLength___main___rarg(x_781);
x_783 = lean_mk_empty_array_with_capacity(x_782);
lean_dec(x_782);
lean_inc(x_781);
x_784 = l_List_toArrayAux___main___rarg(x_781, x_783);
x_785 = x_784;
x_786 = lean_unsigned_to_nat(0u);
lean_inc(x_780);
lean_inc(x_6);
lean_inc(x_1);
x_787 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_787, 0, x_1);
lean_closure_set(x_787, 1, x_6);
lean_closure_set(x_787, 2, x_9);
lean_closure_set(x_787, 3, x_11);
lean_closure_set(x_787, 4, x_780);
lean_closure_set(x_787, 5, x_781);
lean_closure_set(x_787, 6, x_786);
lean_closure_set(x_787, 7, x_785);
x_788 = x_787;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_789 = lean_apply_5(x_788, x_13, x_14, x_15, x_16, x_779);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
lean_dec(x_789);
lean_inc(x_1);
x_792 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_791);
if (lean_obj_tag(x_792) == 0)
{
lean_object* x_793; lean_object* x_794; uint8_t x_795; lean_object* x_796; 
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_792, 1);
lean_inc(x_794);
lean_dec(x_792);
x_795 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_795 == 0)
{
lean_object* x_874; uint8_t x_875; 
x_874 = l_Lean_MetavarContext_exprDependsOn(x_780, x_793, x_2);
x_875 = lean_unbox(x_874);
lean_dec(x_874);
if (x_875 == 0)
{
x_796 = x_794;
goto block_873;
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; uint8_t x_883; 
lean_dec(x_790);
lean_dec(x_774);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_876 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_876, 0, x_3);
x_877 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_878 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_878, 0, x_877);
lean_ctor_set(x_878, 1, x_876);
x_879 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_880 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_880, 0, x_878);
lean_ctor_set(x_880, 1, x_879);
x_881 = lean_box(0);
x_882 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_880, x_881, x_13, x_14, x_15, x_16, x_794);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_883 = !lean_is_exclusive(x_882);
if (x_883 == 0)
{
return x_882;
}
else
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; 
x_884 = lean_ctor_get(x_882, 0);
x_885 = lean_ctor_get(x_882, 1);
lean_inc(x_885);
lean_inc(x_884);
lean_dec(x_882);
x_886 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_886, 0, x_884);
lean_ctor_set(x_886, 1, x_885);
return x_886;
}
}
}
else
{
lean_dec(x_793);
lean_dec(x_780);
x_796 = x_794;
goto block_873;
}
block_873:
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; uint8_t x_801; lean_object* x_802; 
lean_inc(x_790);
x_797 = x_790;
x_798 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_786, x_797);
x_799 = x_798;
x_800 = lean_array_push(x_799, x_2);
x_801 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_802 = l_Lean_Meta_revert(x_1, x_800, x_801, x_13, x_14, x_15, x_16, x_796);
if (lean_obj_tag(x_802) == 0)
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; uint8_t x_809; lean_object* x_810; 
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
x_804 = lean_ctor_get(x_802, 1);
lean_inc(x_804);
lean_dec(x_802);
x_805 = lean_ctor_get(x_803, 0);
lean_inc(x_805);
x_806 = lean_ctor_get(x_803, 1);
lean_inc(x_806);
lean_dec(x_803);
x_807 = lean_array_get_size(x_790);
x_808 = lean_box(0);
x_809 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_810 = l_Lean_Meta_introN(x_806, x_807, x_808, x_809, x_13, x_14, x_15, x_16, x_804);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_811 = lean_ctor_get(x_810, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_810, 1);
lean_inc(x_812);
lean_dec(x_810);
x_813 = lean_ctor_get(x_811, 0);
lean_inc(x_813);
x_814 = lean_ctor_get(x_811, 1);
lean_inc(x_814);
lean_dec(x_811);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_815 = l_Lean_Meta_intro1(x_814, x_809, x_13, x_14, x_15, x_16, x_812);
if (lean_obj_tag(x_815) == 0)
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; uint8_t x_842; lean_object* x_843; lean_object* x_851; lean_object* x_852; uint8_t x_853; 
x_816 = lean_ctor_get(x_815, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_815, 1);
lean_inc(x_817);
lean_dec(x_815);
x_818 = lean_ctor_get(x_816, 0);
lean_inc(x_818);
x_819 = lean_ctor_get(x_816, 1);
lean_inc(x_819);
lean_dec(x_816);
x_820 = lean_box(0);
x_821 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_790, x_813, x_790, x_786, x_820);
lean_dec(x_790);
x_851 = l_Lean_Core_getTraceState___rarg(x_16, x_817);
x_852 = lean_ctor_get(x_851, 0);
lean_inc(x_852);
x_853 = lean_ctor_get_uint8(x_852, sizeof(void*)*1);
lean_dec(x_852);
if (x_853 == 0)
{
lean_object* x_854; 
x_854 = lean_ctor_get(x_851, 1);
lean_inc(x_854);
lean_dec(x_851);
x_842 = x_809;
x_843 = x_854;
goto block_850;
}
else
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; uint8_t x_860; 
x_855 = lean_ctor_get(x_851, 1);
lean_inc(x_855);
lean_dec(x_851);
x_856 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_857 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_856, x_15, x_16, x_855);
x_858 = lean_ctor_get(x_857, 0);
lean_inc(x_858);
x_859 = lean_ctor_get(x_857, 1);
lean_inc(x_859);
lean_dec(x_857);
x_860 = lean_unbox(x_858);
lean_dec(x_858);
x_842 = x_860;
x_843 = x_859;
goto block_850;
}
block_841:
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; 
x_823 = x_813;
x_824 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_786, x_823);
x_825 = x_824;
lean_inc(x_818);
x_826 = l_Lean_mkFVar(x_818);
lean_inc(x_819);
x_827 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_827, 0, x_819);
x_828 = lean_box(x_795);
lean_inc(x_819);
x_829 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_829, 0, x_818);
lean_closure_set(x_829, 1, x_8);
lean_closure_set(x_829, 2, x_819);
lean_closure_set(x_829, 3, x_3);
lean_closure_set(x_829, 4, x_4);
lean_closure_set(x_829, 5, x_6);
lean_closure_set(x_829, 6, x_7);
lean_closure_set(x_829, 7, x_774);
lean_closure_set(x_829, 8, x_828);
lean_closure_set(x_829, 9, x_805);
lean_closure_set(x_829, 10, x_821);
lean_closure_set(x_829, 11, x_825);
lean_closure_set(x_829, 12, x_826);
x_830 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_830, 0, x_827);
lean_closure_set(x_830, 1, x_829);
x_831 = l_Lean_Meta_getMVarDecl(x_819, x_13, x_14, x_15, x_16, x_822);
if (lean_obj_tag(x_831) == 0)
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
x_832 = lean_ctor_get(x_831, 0);
lean_inc(x_832);
x_833 = lean_ctor_get(x_831, 1);
lean_inc(x_833);
lean_dec(x_831);
x_834 = lean_ctor_get(x_832, 1);
lean_inc(x_834);
x_835 = lean_ctor_get(x_832, 4);
lean_inc(x_835);
lean_dec(x_832);
x_836 = l_Lean_Meta_withLocalContext___rarg(x_834, x_835, x_830, x_13, x_14, x_15, x_16, x_833);
lean_dec(x_13);
return x_836;
}
else
{
uint8_t x_837; 
lean_dec(x_830);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_837 = !lean_is_exclusive(x_831);
if (x_837 == 0)
{
return x_831;
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; 
x_838 = lean_ctor_get(x_831, 0);
x_839 = lean_ctor_get(x_831, 1);
lean_inc(x_839);
lean_inc(x_838);
lean_dec(x_831);
x_840 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_840, 0, x_838);
lean_ctor_set(x_840, 1, x_839);
return x_840;
}
}
}
block_850:
{
if (x_842 == 0)
{
x_822 = x_843;
goto block_841;
}
else
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; 
lean_inc(x_819);
x_844 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_844, 0, x_819);
x_845 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_846 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_846, 0, x_845);
lean_ctor_set(x_846, 1, x_844);
x_847 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_848 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_847, x_846, x_13, x_14, x_15, x_16, x_843);
x_849 = lean_ctor_get(x_848, 1);
lean_inc(x_849);
lean_dec(x_848);
x_822 = x_849;
goto block_841;
}
}
}
else
{
uint8_t x_861; 
lean_dec(x_813);
lean_dec(x_805);
lean_dec(x_790);
lean_dec(x_774);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_861 = !lean_is_exclusive(x_815);
if (x_861 == 0)
{
return x_815;
}
else
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; 
x_862 = lean_ctor_get(x_815, 0);
x_863 = lean_ctor_get(x_815, 1);
lean_inc(x_863);
lean_inc(x_862);
lean_dec(x_815);
x_864 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_864, 0, x_862);
lean_ctor_set(x_864, 1, x_863);
return x_864;
}
}
}
else
{
uint8_t x_865; 
lean_dec(x_805);
lean_dec(x_790);
lean_dec(x_774);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_865 = !lean_is_exclusive(x_810);
if (x_865 == 0)
{
return x_810;
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; 
x_866 = lean_ctor_get(x_810, 0);
x_867 = lean_ctor_get(x_810, 1);
lean_inc(x_867);
lean_inc(x_866);
lean_dec(x_810);
x_868 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_868, 0, x_866);
lean_ctor_set(x_868, 1, x_867);
return x_868;
}
}
}
else
{
uint8_t x_869; 
lean_dec(x_790);
lean_dec(x_774);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_869 = !lean_is_exclusive(x_802);
if (x_869 == 0)
{
return x_802;
}
else
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_870 = lean_ctor_get(x_802, 0);
x_871 = lean_ctor_get(x_802, 1);
lean_inc(x_871);
lean_inc(x_870);
lean_dec(x_802);
x_872 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_872, 0, x_870);
lean_ctor_set(x_872, 1, x_871);
return x_872;
}
}
}
}
else
{
uint8_t x_887; 
lean_dec(x_790);
lean_dec(x_780);
lean_dec(x_774);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_887 = !lean_is_exclusive(x_792);
if (x_887 == 0)
{
return x_792;
}
else
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; 
x_888 = lean_ctor_get(x_792, 0);
x_889 = lean_ctor_get(x_792, 1);
lean_inc(x_889);
lean_inc(x_888);
lean_dec(x_792);
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
lean_dec(x_780);
lean_dec(x_774);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_891 = !lean_is_exclusive(x_789);
if (x_891 == 0)
{
return x_789;
}
else
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_892 = lean_ctor_get(x_789, 0);
x_893 = lean_ctor_get(x_789, 1);
lean_inc(x_893);
lean_inc(x_892);
lean_dec(x_789);
x_894 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_894, 0, x_892);
lean_ctor_set(x_894, 1, x_893);
return x_894;
}
}
}
else
{
uint8_t x_895; 
lean_dec(x_774);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_895 = !lean_is_exclusive(x_775);
if (x_895 == 0)
{
return x_775;
}
else
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; 
x_896 = lean_ctor_get(x_775, 0);
x_897 = lean_ctor_get(x_775, 1);
lean_inc(x_897);
lean_inc(x_896);
lean_dec(x_775);
x_898 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_898, 0, x_896);
lean_ctor_set(x_898, 1, x_897);
return x_898;
}
}
}
case 8:
{
lean_object* x_899; lean_object* x_900; 
lean_dec(x_12);
lean_dec(x_10);
x_899 = lean_ctor_get(x_7, 5);
lean_inc(x_899);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_900 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_899, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_900) == 0)
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; 
x_901 = lean_ctor_get(x_900, 1);
lean_inc(x_901);
lean_dec(x_900);
x_902 = lean_st_ref_get(x_14, x_901);
x_903 = lean_ctor_get(x_902, 0);
lean_inc(x_903);
x_904 = lean_ctor_get(x_902, 1);
lean_inc(x_904);
lean_dec(x_902);
x_905 = lean_ctor_get(x_903, 0);
lean_inc(x_905);
lean_dec(x_903);
x_906 = lean_ctor_get(x_7, 6);
lean_inc(x_906);
x_907 = l_List_redLength___main___rarg(x_906);
x_908 = lean_mk_empty_array_with_capacity(x_907);
lean_dec(x_907);
lean_inc(x_906);
x_909 = l_List_toArrayAux___main___rarg(x_906, x_908);
x_910 = x_909;
x_911 = lean_unsigned_to_nat(0u);
lean_inc(x_905);
lean_inc(x_6);
lean_inc(x_1);
x_912 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_912, 0, x_1);
lean_closure_set(x_912, 1, x_6);
lean_closure_set(x_912, 2, x_9);
lean_closure_set(x_912, 3, x_11);
lean_closure_set(x_912, 4, x_905);
lean_closure_set(x_912, 5, x_906);
lean_closure_set(x_912, 6, x_911);
lean_closure_set(x_912, 7, x_910);
x_913 = x_912;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_914 = lean_apply_5(x_913, x_13, x_14, x_15, x_16, x_904);
if (lean_obj_tag(x_914) == 0)
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; 
x_915 = lean_ctor_get(x_914, 0);
lean_inc(x_915);
x_916 = lean_ctor_get(x_914, 1);
lean_inc(x_916);
lean_dec(x_914);
lean_inc(x_1);
x_917 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_916);
if (lean_obj_tag(x_917) == 0)
{
lean_object* x_918; lean_object* x_919; uint8_t x_920; lean_object* x_921; 
x_918 = lean_ctor_get(x_917, 0);
lean_inc(x_918);
x_919 = lean_ctor_get(x_917, 1);
lean_inc(x_919);
lean_dec(x_917);
x_920 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_920 == 0)
{
lean_object* x_999; uint8_t x_1000; 
x_999 = l_Lean_MetavarContext_exprDependsOn(x_905, x_918, x_2);
x_1000 = lean_unbox(x_999);
lean_dec(x_999);
if (x_1000 == 0)
{
x_921 = x_919;
goto block_998;
}
else
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; uint8_t x_1008; 
lean_dec(x_915);
lean_dec(x_899);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_1001 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1001, 0, x_3);
x_1002 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1003 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1003, 0, x_1002);
lean_ctor_set(x_1003, 1, x_1001);
x_1004 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_1005 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1005, 0, x_1003);
lean_ctor_set(x_1005, 1, x_1004);
x_1006 = lean_box(0);
x_1007 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1005, x_1006, x_13, x_14, x_15, x_16, x_919);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1008 = !lean_is_exclusive(x_1007);
if (x_1008 == 0)
{
return x_1007;
}
else
{
lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
x_1009 = lean_ctor_get(x_1007, 0);
x_1010 = lean_ctor_get(x_1007, 1);
lean_inc(x_1010);
lean_inc(x_1009);
lean_dec(x_1007);
x_1011 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1011, 0, x_1009);
lean_ctor_set(x_1011, 1, x_1010);
return x_1011;
}
}
}
else
{
lean_dec(x_918);
lean_dec(x_905);
x_921 = x_919;
goto block_998;
}
block_998:
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; uint8_t x_926; lean_object* x_927; 
lean_inc(x_915);
x_922 = x_915;
x_923 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_911, x_922);
x_924 = x_923;
x_925 = lean_array_push(x_924, x_2);
x_926 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_927 = l_Lean_Meta_revert(x_1, x_925, x_926, x_13, x_14, x_15, x_16, x_921);
if (lean_obj_tag(x_927) == 0)
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; uint8_t x_934; lean_object* x_935; 
x_928 = lean_ctor_get(x_927, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_927, 1);
lean_inc(x_929);
lean_dec(x_927);
x_930 = lean_ctor_get(x_928, 0);
lean_inc(x_930);
x_931 = lean_ctor_get(x_928, 1);
lean_inc(x_931);
lean_dec(x_928);
x_932 = lean_array_get_size(x_915);
x_933 = lean_box(0);
x_934 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_935 = l_Lean_Meta_introN(x_931, x_932, x_933, x_934, x_13, x_14, x_15, x_16, x_929);
if (lean_obj_tag(x_935) == 0)
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_936 = lean_ctor_get(x_935, 0);
lean_inc(x_936);
x_937 = lean_ctor_get(x_935, 1);
lean_inc(x_937);
lean_dec(x_935);
x_938 = lean_ctor_get(x_936, 0);
lean_inc(x_938);
x_939 = lean_ctor_get(x_936, 1);
lean_inc(x_939);
lean_dec(x_936);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_940 = l_Lean_Meta_intro1(x_939, x_934, x_13, x_14, x_15, x_16, x_937);
if (lean_obj_tag(x_940) == 0)
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; uint8_t x_967; lean_object* x_968; lean_object* x_976; lean_object* x_977; uint8_t x_978; 
x_941 = lean_ctor_get(x_940, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_940, 1);
lean_inc(x_942);
lean_dec(x_940);
x_943 = lean_ctor_get(x_941, 0);
lean_inc(x_943);
x_944 = lean_ctor_get(x_941, 1);
lean_inc(x_944);
lean_dec(x_941);
x_945 = lean_box(0);
x_946 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_915, x_938, x_915, x_911, x_945);
lean_dec(x_915);
x_976 = l_Lean_Core_getTraceState___rarg(x_16, x_942);
x_977 = lean_ctor_get(x_976, 0);
lean_inc(x_977);
x_978 = lean_ctor_get_uint8(x_977, sizeof(void*)*1);
lean_dec(x_977);
if (x_978 == 0)
{
lean_object* x_979; 
x_979 = lean_ctor_get(x_976, 1);
lean_inc(x_979);
lean_dec(x_976);
x_967 = x_934;
x_968 = x_979;
goto block_975;
}
else
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; uint8_t x_985; 
x_980 = lean_ctor_get(x_976, 1);
lean_inc(x_980);
lean_dec(x_976);
x_981 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_982 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_981, x_15, x_16, x_980);
x_983 = lean_ctor_get(x_982, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_982, 1);
lean_inc(x_984);
lean_dec(x_982);
x_985 = lean_unbox(x_983);
lean_dec(x_983);
x_967 = x_985;
x_968 = x_984;
goto block_975;
}
block_966:
{
lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; 
x_948 = x_938;
x_949 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_911, x_948);
x_950 = x_949;
lean_inc(x_943);
x_951 = l_Lean_mkFVar(x_943);
lean_inc(x_944);
x_952 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_952, 0, x_944);
x_953 = lean_box(x_920);
lean_inc(x_944);
x_954 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_954, 0, x_943);
lean_closure_set(x_954, 1, x_8);
lean_closure_set(x_954, 2, x_944);
lean_closure_set(x_954, 3, x_3);
lean_closure_set(x_954, 4, x_4);
lean_closure_set(x_954, 5, x_6);
lean_closure_set(x_954, 6, x_7);
lean_closure_set(x_954, 7, x_899);
lean_closure_set(x_954, 8, x_953);
lean_closure_set(x_954, 9, x_930);
lean_closure_set(x_954, 10, x_946);
lean_closure_set(x_954, 11, x_950);
lean_closure_set(x_954, 12, x_951);
x_955 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_955, 0, x_952);
lean_closure_set(x_955, 1, x_954);
x_956 = l_Lean_Meta_getMVarDecl(x_944, x_13, x_14, x_15, x_16, x_947);
if (lean_obj_tag(x_956) == 0)
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; 
x_957 = lean_ctor_get(x_956, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_956, 1);
lean_inc(x_958);
lean_dec(x_956);
x_959 = lean_ctor_get(x_957, 1);
lean_inc(x_959);
x_960 = lean_ctor_get(x_957, 4);
lean_inc(x_960);
lean_dec(x_957);
x_961 = l_Lean_Meta_withLocalContext___rarg(x_959, x_960, x_955, x_13, x_14, x_15, x_16, x_958);
lean_dec(x_13);
return x_961;
}
else
{
uint8_t x_962; 
lean_dec(x_955);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_962 = !lean_is_exclusive(x_956);
if (x_962 == 0)
{
return x_956;
}
else
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; 
x_963 = lean_ctor_get(x_956, 0);
x_964 = lean_ctor_get(x_956, 1);
lean_inc(x_964);
lean_inc(x_963);
lean_dec(x_956);
x_965 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_965, 0, x_963);
lean_ctor_set(x_965, 1, x_964);
return x_965;
}
}
}
block_975:
{
if (x_967 == 0)
{
x_947 = x_968;
goto block_966;
}
else
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
lean_inc(x_944);
x_969 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_969, 0, x_944);
x_970 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_971 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_971, 0, x_970);
lean_ctor_set(x_971, 1, x_969);
x_972 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_973 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_972, x_971, x_13, x_14, x_15, x_16, x_968);
x_974 = lean_ctor_get(x_973, 1);
lean_inc(x_974);
lean_dec(x_973);
x_947 = x_974;
goto block_966;
}
}
}
else
{
uint8_t x_986; 
lean_dec(x_938);
lean_dec(x_930);
lean_dec(x_915);
lean_dec(x_899);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_986 = !lean_is_exclusive(x_940);
if (x_986 == 0)
{
return x_940;
}
else
{
lean_object* x_987; lean_object* x_988; lean_object* x_989; 
x_987 = lean_ctor_get(x_940, 0);
x_988 = lean_ctor_get(x_940, 1);
lean_inc(x_988);
lean_inc(x_987);
lean_dec(x_940);
x_989 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_989, 0, x_987);
lean_ctor_set(x_989, 1, x_988);
return x_989;
}
}
}
else
{
uint8_t x_990; 
lean_dec(x_930);
lean_dec(x_915);
lean_dec(x_899);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_990 = !lean_is_exclusive(x_935);
if (x_990 == 0)
{
return x_935;
}
else
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; 
x_991 = lean_ctor_get(x_935, 0);
x_992 = lean_ctor_get(x_935, 1);
lean_inc(x_992);
lean_inc(x_991);
lean_dec(x_935);
x_993 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_993, 0, x_991);
lean_ctor_set(x_993, 1, x_992);
return x_993;
}
}
}
else
{
uint8_t x_994; 
lean_dec(x_915);
lean_dec(x_899);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_994 = !lean_is_exclusive(x_927);
if (x_994 == 0)
{
return x_927;
}
else
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; 
x_995 = lean_ctor_get(x_927, 0);
x_996 = lean_ctor_get(x_927, 1);
lean_inc(x_996);
lean_inc(x_995);
lean_dec(x_927);
x_997 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_997, 0, x_995);
lean_ctor_set(x_997, 1, x_996);
return x_997;
}
}
}
}
else
{
uint8_t x_1012; 
lean_dec(x_915);
lean_dec(x_905);
lean_dec(x_899);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1012 = !lean_is_exclusive(x_917);
if (x_1012 == 0)
{
return x_917;
}
else
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; 
x_1013 = lean_ctor_get(x_917, 0);
x_1014 = lean_ctor_get(x_917, 1);
lean_inc(x_1014);
lean_inc(x_1013);
lean_dec(x_917);
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
lean_dec(x_905);
lean_dec(x_899);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1016 = !lean_is_exclusive(x_914);
if (x_1016 == 0)
{
return x_914;
}
else
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1017 = lean_ctor_get(x_914, 0);
x_1018 = lean_ctor_get(x_914, 1);
lean_inc(x_1018);
lean_inc(x_1017);
lean_dec(x_914);
x_1019 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1019, 0, x_1017);
lean_ctor_set(x_1019, 1, x_1018);
return x_1019;
}
}
}
else
{
uint8_t x_1020; 
lean_dec(x_899);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1020 = !lean_is_exclusive(x_900);
if (x_1020 == 0)
{
return x_900;
}
else
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
x_1021 = lean_ctor_get(x_900, 0);
x_1022 = lean_ctor_get(x_900, 1);
lean_inc(x_1022);
lean_inc(x_1021);
lean_dec(x_900);
x_1023 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1023, 0, x_1021);
lean_ctor_set(x_1023, 1, x_1022);
return x_1023;
}
}
}
case 9:
{
lean_object* x_1024; lean_object* x_1025; 
lean_dec(x_12);
lean_dec(x_10);
x_1024 = lean_ctor_get(x_7, 5);
lean_inc(x_1024);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1025 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_1024, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_1025) == 0)
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; 
x_1026 = lean_ctor_get(x_1025, 1);
lean_inc(x_1026);
lean_dec(x_1025);
x_1027 = lean_st_ref_get(x_14, x_1026);
x_1028 = lean_ctor_get(x_1027, 0);
lean_inc(x_1028);
x_1029 = lean_ctor_get(x_1027, 1);
lean_inc(x_1029);
lean_dec(x_1027);
x_1030 = lean_ctor_get(x_1028, 0);
lean_inc(x_1030);
lean_dec(x_1028);
x_1031 = lean_ctor_get(x_7, 6);
lean_inc(x_1031);
x_1032 = l_List_redLength___main___rarg(x_1031);
x_1033 = lean_mk_empty_array_with_capacity(x_1032);
lean_dec(x_1032);
lean_inc(x_1031);
x_1034 = l_List_toArrayAux___main___rarg(x_1031, x_1033);
x_1035 = x_1034;
x_1036 = lean_unsigned_to_nat(0u);
lean_inc(x_1030);
lean_inc(x_6);
lean_inc(x_1);
x_1037 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_1037, 0, x_1);
lean_closure_set(x_1037, 1, x_6);
lean_closure_set(x_1037, 2, x_9);
lean_closure_set(x_1037, 3, x_11);
lean_closure_set(x_1037, 4, x_1030);
lean_closure_set(x_1037, 5, x_1031);
lean_closure_set(x_1037, 6, x_1036);
lean_closure_set(x_1037, 7, x_1035);
x_1038 = x_1037;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_1039 = lean_apply_5(x_1038, x_13, x_14, x_15, x_16, x_1029);
if (lean_obj_tag(x_1039) == 0)
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
x_1040 = lean_ctor_get(x_1039, 0);
lean_inc(x_1040);
x_1041 = lean_ctor_get(x_1039, 1);
lean_inc(x_1041);
lean_dec(x_1039);
lean_inc(x_1);
x_1042 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_1041);
if (lean_obj_tag(x_1042) == 0)
{
lean_object* x_1043; lean_object* x_1044; uint8_t x_1045; lean_object* x_1046; 
x_1043 = lean_ctor_get(x_1042, 0);
lean_inc(x_1043);
x_1044 = lean_ctor_get(x_1042, 1);
lean_inc(x_1044);
lean_dec(x_1042);
x_1045 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_1045 == 0)
{
lean_object* x_1124; uint8_t x_1125; 
x_1124 = l_Lean_MetavarContext_exprDependsOn(x_1030, x_1043, x_2);
x_1125 = lean_unbox(x_1124);
lean_dec(x_1124);
if (x_1125 == 0)
{
x_1046 = x_1044;
goto block_1123;
}
else
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; uint8_t x_1133; 
lean_dec(x_1040);
lean_dec(x_1024);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_1126 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1126, 0, x_3);
x_1127 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1128 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1128, 0, x_1127);
lean_ctor_set(x_1128, 1, x_1126);
x_1129 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_1130 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1130, 0, x_1128);
lean_ctor_set(x_1130, 1, x_1129);
x_1131 = lean_box(0);
x_1132 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1130, x_1131, x_13, x_14, x_15, x_16, x_1044);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1133 = !lean_is_exclusive(x_1132);
if (x_1133 == 0)
{
return x_1132;
}
else
{
lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; 
x_1134 = lean_ctor_get(x_1132, 0);
x_1135 = lean_ctor_get(x_1132, 1);
lean_inc(x_1135);
lean_inc(x_1134);
lean_dec(x_1132);
x_1136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1136, 0, x_1134);
lean_ctor_set(x_1136, 1, x_1135);
return x_1136;
}
}
}
else
{
lean_dec(x_1043);
lean_dec(x_1030);
x_1046 = x_1044;
goto block_1123;
}
block_1123:
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; uint8_t x_1051; lean_object* x_1052; 
lean_inc(x_1040);
x_1047 = x_1040;
x_1048 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1036, x_1047);
x_1049 = x_1048;
x_1050 = lean_array_push(x_1049, x_2);
x_1051 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1052 = l_Lean_Meta_revert(x_1, x_1050, x_1051, x_13, x_14, x_15, x_16, x_1046);
if (lean_obj_tag(x_1052) == 0)
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; uint8_t x_1059; lean_object* x_1060; 
x_1053 = lean_ctor_get(x_1052, 0);
lean_inc(x_1053);
x_1054 = lean_ctor_get(x_1052, 1);
lean_inc(x_1054);
lean_dec(x_1052);
x_1055 = lean_ctor_get(x_1053, 0);
lean_inc(x_1055);
x_1056 = lean_ctor_get(x_1053, 1);
lean_inc(x_1056);
lean_dec(x_1053);
x_1057 = lean_array_get_size(x_1040);
x_1058 = lean_box(0);
x_1059 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1060 = l_Lean_Meta_introN(x_1056, x_1057, x_1058, x_1059, x_13, x_14, x_15, x_16, x_1054);
if (lean_obj_tag(x_1060) == 0)
{
lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
x_1061 = lean_ctor_get(x_1060, 0);
lean_inc(x_1061);
x_1062 = lean_ctor_get(x_1060, 1);
lean_inc(x_1062);
lean_dec(x_1060);
x_1063 = lean_ctor_get(x_1061, 0);
lean_inc(x_1063);
x_1064 = lean_ctor_get(x_1061, 1);
lean_inc(x_1064);
lean_dec(x_1061);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1065 = l_Lean_Meta_intro1(x_1064, x_1059, x_13, x_14, x_15, x_16, x_1062);
if (lean_obj_tag(x_1065) == 0)
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; uint8_t x_1092; lean_object* x_1093; lean_object* x_1101; lean_object* x_1102; uint8_t x_1103; 
x_1066 = lean_ctor_get(x_1065, 0);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_1065, 1);
lean_inc(x_1067);
lean_dec(x_1065);
x_1068 = lean_ctor_get(x_1066, 0);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_1066, 1);
lean_inc(x_1069);
lean_dec(x_1066);
x_1070 = lean_box(0);
x_1071 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_1040, x_1063, x_1040, x_1036, x_1070);
lean_dec(x_1040);
x_1101 = l_Lean_Core_getTraceState___rarg(x_16, x_1067);
x_1102 = lean_ctor_get(x_1101, 0);
lean_inc(x_1102);
x_1103 = lean_ctor_get_uint8(x_1102, sizeof(void*)*1);
lean_dec(x_1102);
if (x_1103 == 0)
{
lean_object* x_1104; 
x_1104 = lean_ctor_get(x_1101, 1);
lean_inc(x_1104);
lean_dec(x_1101);
x_1092 = x_1059;
x_1093 = x_1104;
goto block_1100;
}
else
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; uint8_t x_1110; 
x_1105 = lean_ctor_get(x_1101, 1);
lean_inc(x_1105);
lean_dec(x_1101);
x_1106 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1107 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1106, x_15, x_16, x_1105);
x_1108 = lean_ctor_get(x_1107, 0);
lean_inc(x_1108);
x_1109 = lean_ctor_get(x_1107, 1);
lean_inc(x_1109);
lean_dec(x_1107);
x_1110 = lean_unbox(x_1108);
lean_dec(x_1108);
x_1092 = x_1110;
x_1093 = x_1109;
goto block_1100;
}
block_1091:
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; 
x_1073 = x_1063;
x_1074 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1036, x_1073);
x_1075 = x_1074;
lean_inc(x_1068);
x_1076 = l_Lean_mkFVar(x_1068);
lean_inc(x_1069);
x_1077 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1077, 0, x_1069);
x_1078 = lean_box(x_1045);
lean_inc(x_1069);
x_1079 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_1079, 0, x_1068);
lean_closure_set(x_1079, 1, x_8);
lean_closure_set(x_1079, 2, x_1069);
lean_closure_set(x_1079, 3, x_3);
lean_closure_set(x_1079, 4, x_4);
lean_closure_set(x_1079, 5, x_6);
lean_closure_set(x_1079, 6, x_7);
lean_closure_set(x_1079, 7, x_1024);
lean_closure_set(x_1079, 8, x_1078);
lean_closure_set(x_1079, 9, x_1055);
lean_closure_set(x_1079, 10, x_1071);
lean_closure_set(x_1079, 11, x_1075);
lean_closure_set(x_1079, 12, x_1076);
x_1080 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_1080, 0, x_1077);
lean_closure_set(x_1080, 1, x_1079);
x_1081 = l_Lean_Meta_getMVarDecl(x_1069, x_13, x_14, x_15, x_16, x_1072);
if (lean_obj_tag(x_1081) == 0)
{
lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; 
x_1082 = lean_ctor_get(x_1081, 0);
lean_inc(x_1082);
x_1083 = lean_ctor_get(x_1081, 1);
lean_inc(x_1083);
lean_dec(x_1081);
x_1084 = lean_ctor_get(x_1082, 1);
lean_inc(x_1084);
x_1085 = lean_ctor_get(x_1082, 4);
lean_inc(x_1085);
lean_dec(x_1082);
x_1086 = l_Lean_Meta_withLocalContext___rarg(x_1084, x_1085, x_1080, x_13, x_14, x_15, x_16, x_1083);
lean_dec(x_13);
return x_1086;
}
else
{
uint8_t x_1087; 
lean_dec(x_1080);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1087 = !lean_is_exclusive(x_1081);
if (x_1087 == 0)
{
return x_1081;
}
else
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; 
x_1088 = lean_ctor_get(x_1081, 0);
x_1089 = lean_ctor_get(x_1081, 1);
lean_inc(x_1089);
lean_inc(x_1088);
lean_dec(x_1081);
x_1090 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1090, 0, x_1088);
lean_ctor_set(x_1090, 1, x_1089);
return x_1090;
}
}
}
block_1100:
{
if (x_1092 == 0)
{
x_1072 = x_1093;
goto block_1091;
}
else
{
lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; 
lean_inc(x_1069);
x_1094 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1094, 0, x_1069);
x_1095 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_1096 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1096, 0, x_1095);
lean_ctor_set(x_1096, 1, x_1094);
x_1097 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1098 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1097, x_1096, x_13, x_14, x_15, x_16, x_1093);
x_1099 = lean_ctor_get(x_1098, 1);
lean_inc(x_1099);
lean_dec(x_1098);
x_1072 = x_1099;
goto block_1091;
}
}
}
else
{
uint8_t x_1111; 
lean_dec(x_1063);
lean_dec(x_1055);
lean_dec(x_1040);
lean_dec(x_1024);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1111 = !lean_is_exclusive(x_1065);
if (x_1111 == 0)
{
return x_1065;
}
else
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; 
x_1112 = lean_ctor_get(x_1065, 0);
x_1113 = lean_ctor_get(x_1065, 1);
lean_inc(x_1113);
lean_inc(x_1112);
lean_dec(x_1065);
x_1114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1114, 0, x_1112);
lean_ctor_set(x_1114, 1, x_1113);
return x_1114;
}
}
}
else
{
uint8_t x_1115; 
lean_dec(x_1055);
lean_dec(x_1040);
lean_dec(x_1024);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1115 = !lean_is_exclusive(x_1060);
if (x_1115 == 0)
{
return x_1060;
}
else
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1116 = lean_ctor_get(x_1060, 0);
x_1117 = lean_ctor_get(x_1060, 1);
lean_inc(x_1117);
lean_inc(x_1116);
lean_dec(x_1060);
x_1118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1118, 0, x_1116);
lean_ctor_set(x_1118, 1, x_1117);
return x_1118;
}
}
}
else
{
uint8_t x_1119; 
lean_dec(x_1040);
lean_dec(x_1024);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1119 = !lean_is_exclusive(x_1052);
if (x_1119 == 0)
{
return x_1052;
}
else
{
lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; 
x_1120 = lean_ctor_get(x_1052, 0);
x_1121 = lean_ctor_get(x_1052, 1);
lean_inc(x_1121);
lean_inc(x_1120);
lean_dec(x_1052);
x_1122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1122, 0, x_1120);
lean_ctor_set(x_1122, 1, x_1121);
return x_1122;
}
}
}
}
else
{
uint8_t x_1137; 
lean_dec(x_1040);
lean_dec(x_1030);
lean_dec(x_1024);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1137 = !lean_is_exclusive(x_1042);
if (x_1137 == 0)
{
return x_1042;
}
else
{
lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
x_1138 = lean_ctor_get(x_1042, 0);
x_1139 = lean_ctor_get(x_1042, 1);
lean_inc(x_1139);
lean_inc(x_1138);
lean_dec(x_1042);
x_1140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1140, 0, x_1138);
lean_ctor_set(x_1140, 1, x_1139);
return x_1140;
}
}
}
else
{
uint8_t x_1141; 
lean_dec(x_1030);
lean_dec(x_1024);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1141 = !lean_is_exclusive(x_1039);
if (x_1141 == 0)
{
return x_1039;
}
else
{
lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
x_1142 = lean_ctor_get(x_1039, 0);
x_1143 = lean_ctor_get(x_1039, 1);
lean_inc(x_1143);
lean_inc(x_1142);
lean_dec(x_1039);
x_1144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1144, 0, x_1142);
lean_ctor_set(x_1144, 1, x_1143);
return x_1144;
}
}
}
else
{
uint8_t x_1145; 
lean_dec(x_1024);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1145 = !lean_is_exclusive(x_1025);
if (x_1145 == 0)
{
return x_1025;
}
else
{
lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; 
x_1146 = lean_ctor_get(x_1025, 0);
x_1147 = lean_ctor_get(x_1025, 1);
lean_inc(x_1147);
lean_inc(x_1146);
lean_dec(x_1025);
x_1148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1148, 0, x_1146);
lean_ctor_set(x_1148, 1, x_1147);
return x_1148;
}
}
}
case 10:
{
lean_object* x_1149; lean_object* x_1150; 
lean_dec(x_12);
lean_dec(x_10);
x_1149 = lean_ctor_get(x_7, 5);
lean_inc(x_1149);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1150 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_1149, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_1150) == 0)
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
x_1151 = lean_ctor_get(x_1150, 1);
lean_inc(x_1151);
lean_dec(x_1150);
x_1152 = lean_st_ref_get(x_14, x_1151);
x_1153 = lean_ctor_get(x_1152, 0);
lean_inc(x_1153);
x_1154 = lean_ctor_get(x_1152, 1);
lean_inc(x_1154);
lean_dec(x_1152);
x_1155 = lean_ctor_get(x_1153, 0);
lean_inc(x_1155);
lean_dec(x_1153);
x_1156 = lean_ctor_get(x_7, 6);
lean_inc(x_1156);
x_1157 = l_List_redLength___main___rarg(x_1156);
x_1158 = lean_mk_empty_array_with_capacity(x_1157);
lean_dec(x_1157);
lean_inc(x_1156);
x_1159 = l_List_toArrayAux___main___rarg(x_1156, x_1158);
x_1160 = x_1159;
x_1161 = lean_unsigned_to_nat(0u);
lean_inc(x_1155);
lean_inc(x_6);
lean_inc(x_1);
x_1162 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_1162, 0, x_1);
lean_closure_set(x_1162, 1, x_6);
lean_closure_set(x_1162, 2, x_9);
lean_closure_set(x_1162, 3, x_11);
lean_closure_set(x_1162, 4, x_1155);
lean_closure_set(x_1162, 5, x_1156);
lean_closure_set(x_1162, 6, x_1161);
lean_closure_set(x_1162, 7, x_1160);
x_1163 = x_1162;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_1164 = lean_apply_5(x_1163, x_13, x_14, x_15, x_16, x_1154);
if (lean_obj_tag(x_1164) == 0)
{
lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
x_1165 = lean_ctor_get(x_1164, 0);
lean_inc(x_1165);
x_1166 = lean_ctor_get(x_1164, 1);
lean_inc(x_1166);
lean_dec(x_1164);
lean_inc(x_1);
x_1167 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_1166);
if (lean_obj_tag(x_1167) == 0)
{
lean_object* x_1168; lean_object* x_1169; uint8_t x_1170; lean_object* x_1171; 
x_1168 = lean_ctor_get(x_1167, 0);
lean_inc(x_1168);
x_1169 = lean_ctor_get(x_1167, 1);
lean_inc(x_1169);
lean_dec(x_1167);
x_1170 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_1170 == 0)
{
lean_object* x_1249; uint8_t x_1250; 
x_1249 = l_Lean_MetavarContext_exprDependsOn(x_1155, x_1168, x_2);
x_1250 = lean_unbox(x_1249);
lean_dec(x_1249);
if (x_1250 == 0)
{
x_1171 = x_1169;
goto block_1248;
}
else
{
lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; uint8_t x_1258; 
lean_dec(x_1165);
lean_dec(x_1149);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_1251 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1251, 0, x_3);
x_1252 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1253 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1253, 0, x_1252);
lean_ctor_set(x_1253, 1, x_1251);
x_1254 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_1255 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1255, 0, x_1253);
lean_ctor_set(x_1255, 1, x_1254);
x_1256 = lean_box(0);
x_1257 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1255, x_1256, x_13, x_14, x_15, x_16, x_1169);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1258 = !lean_is_exclusive(x_1257);
if (x_1258 == 0)
{
return x_1257;
}
else
{
lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; 
x_1259 = lean_ctor_get(x_1257, 0);
x_1260 = lean_ctor_get(x_1257, 1);
lean_inc(x_1260);
lean_inc(x_1259);
lean_dec(x_1257);
x_1261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1261, 0, x_1259);
lean_ctor_set(x_1261, 1, x_1260);
return x_1261;
}
}
}
else
{
lean_dec(x_1168);
lean_dec(x_1155);
x_1171 = x_1169;
goto block_1248;
}
block_1248:
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; uint8_t x_1176; lean_object* x_1177; 
lean_inc(x_1165);
x_1172 = x_1165;
x_1173 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1161, x_1172);
x_1174 = x_1173;
x_1175 = lean_array_push(x_1174, x_2);
x_1176 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1177 = l_Lean_Meta_revert(x_1, x_1175, x_1176, x_13, x_14, x_15, x_16, x_1171);
if (lean_obj_tag(x_1177) == 0)
{
lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; uint8_t x_1184; lean_object* x_1185; 
x_1178 = lean_ctor_get(x_1177, 0);
lean_inc(x_1178);
x_1179 = lean_ctor_get(x_1177, 1);
lean_inc(x_1179);
lean_dec(x_1177);
x_1180 = lean_ctor_get(x_1178, 0);
lean_inc(x_1180);
x_1181 = lean_ctor_get(x_1178, 1);
lean_inc(x_1181);
lean_dec(x_1178);
x_1182 = lean_array_get_size(x_1165);
x_1183 = lean_box(0);
x_1184 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1185 = l_Lean_Meta_introN(x_1181, x_1182, x_1183, x_1184, x_13, x_14, x_15, x_16, x_1179);
if (lean_obj_tag(x_1185) == 0)
{
lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; 
x_1186 = lean_ctor_get(x_1185, 0);
lean_inc(x_1186);
x_1187 = lean_ctor_get(x_1185, 1);
lean_inc(x_1187);
lean_dec(x_1185);
x_1188 = lean_ctor_get(x_1186, 0);
lean_inc(x_1188);
x_1189 = lean_ctor_get(x_1186, 1);
lean_inc(x_1189);
lean_dec(x_1186);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1190 = l_Lean_Meta_intro1(x_1189, x_1184, x_13, x_14, x_15, x_16, x_1187);
if (lean_obj_tag(x_1190) == 0)
{
lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; uint8_t x_1217; lean_object* x_1218; lean_object* x_1226; lean_object* x_1227; uint8_t x_1228; 
x_1191 = lean_ctor_get(x_1190, 0);
lean_inc(x_1191);
x_1192 = lean_ctor_get(x_1190, 1);
lean_inc(x_1192);
lean_dec(x_1190);
x_1193 = lean_ctor_get(x_1191, 0);
lean_inc(x_1193);
x_1194 = lean_ctor_get(x_1191, 1);
lean_inc(x_1194);
lean_dec(x_1191);
x_1195 = lean_box(0);
x_1196 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_1165, x_1188, x_1165, x_1161, x_1195);
lean_dec(x_1165);
x_1226 = l_Lean_Core_getTraceState___rarg(x_16, x_1192);
x_1227 = lean_ctor_get(x_1226, 0);
lean_inc(x_1227);
x_1228 = lean_ctor_get_uint8(x_1227, sizeof(void*)*1);
lean_dec(x_1227);
if (x_1228 == 0)
{
lean_object* x_1229; 
x_1229 = lean_ctor_get(x_1226, 1);
lean_inc(x_1229);
lean_dec(x_1226);
x_1217 = x_1184;
x_1218 = x_1229;
goto block_1225;
}
else
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; uint8_t x_1235; 
x_1230 = lean_ctor_get(x_1226, 1);
lean_inc(x_1230);
lean_dec(x_1226);
x_1231 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1232 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1231, x_15, x_16, x_1230);
x_1233 = lean_ctor_get(x_1232, 0);
lean_inc(x_1233);
x_1234 = lean_ctor_get(x_1232, 1);
lean_inc(x_1234);
lean_dec(x_1232);
x_1235 = lean_unbox(x_1233);
lean_dec(x_1233);
x_1217 = x_1235;
x_1218 = x_1234;
goto block_1225;
}
block_1216:
{
lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; 
x_1198 = x_1188;
x_1199 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1161, x_1198);
x_1200 = x_1199;
lean_inc(x_1193);
x_1201 = l_Lean_mkFVar(x_1193);
lean_inc(x_1194);
x_1202 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1202, 0, x_1194);
x_1203 = lean_box(x_1170);
lean_inc(x_1194);
x_1204 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_1204, 0, x_1193);
lean_closure_set(x_1204, 1, x_8);
lean_closure_set(x_1204, 2, x_1194);
lean_closure_set(x_1204, 3, x_3);
lean_closure_set(x_1204, 4, x_4);
lean_closure_set(x_1204, 5, x_6);
lean_closure_set(x_1204, 6, x_7);
lean_closure_set(x_1204, 7, x_1149);
lean_closure_set(x_1204, 8, x_1203);
lean_closure_set(x_1204, 9, x_1180);
lean_closure_set(x_1204, 10, x_1196);
lean_closure_set(x_1204, 11, x_1200);
lean_closure_set(x_1204, 12, x_1201);
x_1205 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_1205, 0, x_1202);
lean_closure_set(x_1205, 1, x_1204);
x_1206 = l_Lean_Meta_getMVarDecl(x_1194, x_13, x_14, x_15, x_16, x_1197);
if (lean_obj_tag(x_1206) == 0)
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; 
x_1207 = lean_ctor_get(x_1206, 0);
lean_inc(x_1207);
x_1208 = lean_ctor_get(x_1206, 1);
lean_inc(x_1208);
lean_dec(x_1206);
x_1209 = lean_ctor_get(x_1207, 1);
lean_inc(x_1209);
x_1210 = lean_ctor_get(x_1207, 4);
lean_inc(x_1210);
lean_dec(x_1207);
x_1211 = l_Lean_Meta_withLocalContext___rarg(x_1209, x_1210, x_1205, x_13, x_14, x_15, x_16, x_1208);
lean_dec(x_13);
return x_1211;
}
else
{
uint8_t x_1212; 
lean_dec(x_1205);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1212 = !lean_is_exclusive(x_1206);
if (x_1212 == 0)
{
return x_1206;
}
else
{
lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; 
x_1213 = lean_ctor_get(x_1206, 0);
x_1214 = lean_ctor_get(x_1206, 1);
lean_inc(x_1214);
lean_inc(x_1213);
lean_dec(x_1206);
x_1215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1215, 0, x_1213);
lean_ctor_set(x_1215, 1, x_1214);
return x_1215;
}
}
}
block_1225:
{
if (x_1217 == 0)
{
x_1197 = x_1218;
goto block_1216;
}
else
{
lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; 
lean_inc(x_1194);
x_1219 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1219, 0, x_1194);
x_1220 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_1221 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1221, 0, x_1220);
lean_ctor_set(x_1221, 1, x_1219);
x_1222 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1223 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1222, x_1221, x_13, x_14, x_15, x_16, x_1218);
x_1224 = lean_ctor_get(x_1223, 1);
lean_inc(x_1224);
lean_dec(x_1223);
x_1197 = x_1224;
goto block_1216;
}
}
}
else
{
uint8_t x_1236; 
lean_dec(x_1188);
lean_dec(x_1180);
lean_dec(x_1165);
lean_dec(x_1149);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1236 = !lean_is_exclusive(x_1190);
if (x_1236 == 0)
{
return x_1190;
}
else
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; 
x_1237 = lean_ctor_get(x_1190, 0);
x_1238 = lean_ctor_get(x_1190, 1);
lean_inc(x_1238);
lean_inc(x_1237);
lean_dec(x_1190);
x_1239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1239, 0, x_1237);
lean_ctor_set(x_1239, 1, x_1238);
return x_1239;
}
}
}
else
{
uint8_t x_1240; 
lean_dec(x_1180);
lean_dec(x_1165);
lean_dec(x_1149);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1240 = !lean_is_exclusive(x_1185);
if (x_1240 == 0)
{
return x_1185;
}
else
{
lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; 
x_1241 = lean_ctor_get(x_1185, 0);
x_1242 = lean_ctor_get(x_1185, 1);
lean_inc(x_1242);
lean_inc(x_1241);
lean_dec(x_1185);
x_1243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1243, 0, x_1241);
lean_ctor_set(x_1243, 1, x_1242);
return x_1243;
}
}
}
else
{
uint8_t x_1244; 
lean_dec(x_1165);
lean_dec(x_1149);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1244 = !lean_is_exclusive(x_1177);
if (x_1244 == 0)
{
return x_1177;
}
else
{
lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; 
x_1245 = lean_ctor_get(x_1177, 0);
x_1246 = lean_ctor_get(x_1177, 1);
lean_inc(x_1246);
lean_inc(x_1245);
lean_dec(x_1177);
x_1247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1247, 0, x_1245);
lean_ctor_set(x_1247, 1, x_1246);
return x_1247;
}
}
}
}
else
{
uint8_t x_1262; 
lean_dec(x_1165);
lean_dec(x_1155);
lean_dec(x_1149);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1262 = !lean_is_exclusive(x_1167);
if (x_1262 == 0)
{
return x_1167;
}
else
{
lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; 
x_1263 = lean_ctor_get(x_1167, 0);
x_1264 = lean_ctor_get(x_1167, 1);
lean_inc(x_1264);
lean_inc(x_1263);
lean_dec(x_1167);
x_1265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1265, 0, x_1263);
lean_ctor_set(x_1265, 1, x_1264);
return x_1265;
}
}
}
else
{
uint8_t x_1266; 
lean_dec(x_1155);
lean_dec(x_1149);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1266 = !lean_is_exclusive(x_1164);
if (x_1266 == 0)
{
return x_1164;
}
else
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
x_1267 = lean_ctor_get(x_1164, 0);
x_1268 = lean_ctor_get(x_1164, 1);
lean_inc(x_1268);
lean_inc(x_1267);
lean_dec(x_1164);
x_1269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1269, 0, x_1267);
lean_ctor_set(x_1269, 1, x_1268);
return x_1269;
}
}
}
else
{
uint8_t x_1270; 
lean_dec(x_1149);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1270 = !lean_is_exclusive(x_1150);
if (x_1270 == 0)
{
return x_1150;
}
else
{
lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; 
x_1271 = lean_ctor_get(x_1150, 0);
x_1272 = lean_ctor_get(x_1150, 1);
lean_inc(x_1272);
lean_inc(x_1271);
lean_dec(x_1150);
x_1273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1273, 0, x_1271);
lean_ctor_set(x_1273, 1, x_1272);
return x_1273;
}
}
}
case 11:
{
lean_object* x_1274; lean_object* x_1275; 
lean_dec(x_12);
lean_dec(x_10);
x_1274 = lean_ctor_get(x_7, 5);
lean_inc(x_1274);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1275 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_1274, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_1275) == 0)
{
lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; 
x_1276 = lean_ctor_get(x_1275, 1);
lean_inc(x_1276);
lean_dec(x_1275);
x_1277 = lean_st_ref_get(x_14, x_1276);
x_1278 = lean_ctor_get(x_1277, 0);
lean_inc(x_1278);
x_1279 = lean_ctor_get(x_1277, 1);
lean_inc(x_1279);
lean_dec(x_1277);
x_1280 = lean_ctor_get(x_1278, 0);
lean_inc(x_1280);
lean_dec(x_1278);
x_1281 = lean_ctor_get(x_7, 6);
lean_inc(x_1281);
x_1282 = l_List_redLength___main___rarg(x_1281);
x_1283 = lean_mk_empty_array_with_capacity(x_1282);
lean_dec(x_1282);
lean_inc(x_1281);
x_1284 = l_List_toArrayAux___main___rarg(x_1281, x_1283);
x_1285 = x_1284;
x_1286 = lean_unsigned_to_nat(0u);
lean_inc(x_1280);
lean_inc(x_6);
lean_inc(x_1);
x_1287 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_1287, 0, x_1);
lean_closure_set(x_1287, 1, x_6);
lean_closure_set(x_1287, 2, x_9);
lean_closure_set(x_1287, 3, x_11);
lean_closure_set(x_1287, 4, x_1280);
lean_closure_set(x_1287, 5, x_1281);
lean_closure_set(x_1287, 6, x_1286);
lean_closure_set(x_1287, 7, x_1285);
x_1288 = x_1287;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_1289 = lean_apply_5(x_1288, x_13, x_14, x_15, x_16, x_1279);
if (lean_obj_tag(x_1289) == 0)
{
lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; 
x_1290 = lean_ctor_get(x_1289, 0);
lean_inc(x_1290);
x_1291 = lean_ctor_get(x_1289, 1);
lean_inc(x_1291);
lean_dec(x_1289);
lean_inc(x_1);
x_1292 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_1291);
if (lean_obj_tag(x_1292) == 0)
{
lean_object* x_1293; lean_object* x_1294; uint8_t x_1295; lean_object* x_1296; 
x_1293 = lean_ctor_get(x_1292, 0);
lean_inc(x_1293);
x_1294 = lean_ctor_get(x_1292, 1);
lean_inc(x_1294);
lean_dec(x_1292);
x_1295 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_1295 == 0)
{
lean_object* x_1374; uint8_t x_1375; 
x_1374 = l_Lean_MetavarContext_exprDependsOn(x_1280, x_1293, x_2);
x_1375 = lean_unbox(x_1374);
lean_dec(x_1374);
if (x_1375 == 0)
{
x_1296 = x_1294;
goto block_1373;
}
else
{
lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; uint8_t x_1383; 
lean_dec(x_1290);
lean_dec(x_1274);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_1376 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1376, 0, x_3);
x_1377 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1378 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1378, 0, x_1377);
lean_ctor_set(x_1378, 1, x_1376);
x_1379 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_1380 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1380, 0, x_1378);
lean_ctor_set(x_1380, 1, x_1379);
x_1381 = lean_box(0);
x_1382 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1380, x_1381, x_13, x_14, x_15, x_16, x_1294);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1383 = !lean_is_exclusive(x_1382);
if (x_1383 == 0)
{
return x_1382;
}
else
{
lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; 
x_1384 = lean_ctor_get(x_1382, 0);
x_1385 = lean_ctor_get(x_1382, 1);
lean_inc(x_1385);
lean_inc(x_1384);
lean_dec(x_1382);
x_1386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1386, 0, x_1384);
lean_ctor_set(x_1386, 1, x_1385);
return x_1386;
}
}
}
else
{
lean_dec(x_1293);
lean_dec(x_1280);
x_1296 = x_1294;
goto block_1373;
}
block_1373:
{
lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; uint8_t x_1301; lean_object* x_1302; 
lean_inc(x_1290);
x_1297 = x_1290;
x_1298 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1286, x_1297);
x_1299 = x_1298;
x_1300 = lean_array_push(x_1299, x_2);
x_1301 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1302 = l_Lean_Meta_revert(x_1, x_1300, x_1301, x_13, x_14, x_15, x_16, x_1296);
if (lean_obj_tag(x_1302) == 0)
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; uint8_t x_1309; lean_object* x_1310; 
x_1303 = lean_ctor_get(x_1302, 0);
lean_inc(x_1303);
x_1304 = lean_ctor_get(x_1302, 1);
lean_inc(x_1304);
lean_dec(x_1302);
x_1305 = lean_ctor_get(x_1303, 0);
lean_inc(x_1305);
x_1306 = lean_ctor_get(x_1303, 1);
lean_inc(x_1306);
lean_dec(x_1303);
x_1307 = lean_array_get_size(x_1290);
x_1308 = lean_box(0);
x_1309 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1310 = l_Lean_Meta_introN(x_1306, x_1307, x_1308, x_1309, x_13, x_14, x_15, x_16, x_1304);
if (lean_obj_tag(x_1310) == 0)
{
lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; 
x_1311 = lean_ctor_get(x_1310, 0);
lean_inc(x_1311);
x_1312 = lean_ctor_get(x_1310, 1);
lean_inc(x_1312);
lean_dec(x_1310);
x_1313 = lean_ctor_get(x_1311, 0);
lean_inc(x_1313);
x_1314 = lean_ctor_get(x_1311, 1);
lean_inc(x_1314);
lean_dec(x_1311);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1315 = l_Lean_Meta_intro1(x_1314, x_1309, x_13, x_14, x_15, x_16, x_1312);
if (lean_obj_tag(x_1315) == 0)
{
lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; uint8_t x_1342; lean_object* x_1343; lean_object* x_1351; lean_object* x_1352; uint8_t x_1353; 
x_1316 = lean_ctor_get(x_1315, 0);
lean_inc(x_1316);
x_1317 = lean_ctor_get(x_1315, 1);
lean_inc(x_1317);
lean_dec(x_1315);
x_1318 = lean_ctor_get(x_1316, 0);
lean_inc(x_1318);
x_1319 = lean_ctor_get(x_1316, 1);
lean_inc(x_1319);
lean_dec(x_1316);
x_1320 = lean_box(0);
x_1321 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_1290, x_1313, x_1290, x_1286, x_1320);
lean_dec(x_1290);
x_1351 = l_Lean_Core_getTraceState___rarg(x_16, x_1317);
x_1352 = lean_ctor_get(x_1351, 0);
lean_inc(x_1352);
x_1353 = lean_ctor_get_uint8(x_1352, sizeof(void*)*1);
lean_dec(x_1352);
if (x_1353 == 0)
{
lean_object* x_1354; 
x_1354 = lean_ctor_get(x_1351, 1);
lean_inc(x_1354);
lean_dec(x_1351);
x_1342 = x_1309;
x_1343 = x_1354;
goto block_1350;
}
else
{
lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; uint8_t x_1360; 
x_1355 = lean_ctor_get(x_1351, 1);
lean_inc(x_1355);
lean_dec(x_1351);
x_1356 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1357 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1356, x_15, x_16, x_1355);
x_1358 = lean_ctor_get(x_1357, 0);
lean_inc(x_1358);
x_1359 = lean_ctor_get(x_1357, 1);
lean_inc(x_1359);
lean_dec(x_1357);
x_1360 = lean_unbox(x_1358);
lean_dec(x_1358);
x_1342 = x_1360;
x_1343 = x_1359;
goto block_1350;
}
block_1341:
{
lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; 
x_1323 = x_1313;
x_1324 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1286, x_1323);
x_1325 = x_1324;
lean_inc(x_1318);
x_1326 = l_Lean_mkFVar(x_1318);
lean_inc(x_1319);
x_1327 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1327, 0, x_1319);
x_1328 = lean_box(x_1295);
lean_inc(x_1319);
x_1329 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_1329, 0, x_1318);
lean_closure_set(x_1329, 1, x_8);
lean_closure_set(x_1329, 2, x_1319);
lean_closure_set(x_1329, 3, x_3);
lean_closure_set(x_1329, 4, x_4);
lean_closure_set(x_1329, 5, x_6);
lean_closure_set(x_1329, 6, x_7);
lean_closure_set(x_1329, 7, x_1274);
lean_closure_set(x_1329, 8, x_1328);
lean_closure_set(x_1329, 9, x_1305);
lean_closure_set(x_1329, 10, x_1321);
lean_closure_set(x_1329, 11, x_1325);
lean_closure_set(x_1329, 12, x_1326);
x_1330 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_1330, 0, x_1327);
lean_closure_set(x_1330, 1, x_1329);
x_1331 = l_Lean_Meta_getMVarDecl(x_1319, x_13, x_14, x_15, x_16, x_1322);
if (lean_obj_tag(x_1331) == 0)
{
lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; 
x_1332 = lean_ctor_get(x_1331, 0);
lean_inc(x_1332);
x_1333 = lean_ctor_get(x_1331, 1);
lean_inc(x_1333);
lean_dec(x_1331);
x_1334 = lean_ctor_get(x_1332, 1);
lean_inc(x_1334);
x_1335 = lean_ctor_get(x_1332, 4);
lean_inc(x_1335);
lean_dec(x_1332);
x_1336 = l_Lean_Meta_withLocalContext___rarg(x_1334, x_1335, x_1330, x_13, x_14, x_15, x_16, x_1333);
lean_dec(x_13);
return x_1336;
}
else
{
uint8_t x_1337; 
lean_dec(x_1330);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1337 = !lean_is_exclusive(x_1331);
if (x_1337 == 0)
{
return x_1331;
}
else
{
lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; 
x_1338 = lean_ctor_get(x_1331, 0);
x_1339 = lean_ctor_get(x_1331, 1);
lean_inc(x_1339);
lean_inc(x_1338);
lean_dec(x_1331);
x_1340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1340, 0, x_1338);
lean_ctor_set(x_1340, 1, x_1339);
return x_1340;
}
}
}
block_1350:
{
if (x_1342 == 0)
{
x_1322 = x_1343;
goto block_1341;
}
else
{
lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; 
lean_inc(x_1319);
x_1344 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1344, 0, x_1319);
x_1345 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_1346 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1346, 0, x_1345);
lean_ctor_set(x_1346, 1, x_1344);
x_1347 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1348 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1347, x_1346, x_13, x_14, x_15, x_16, x_1343);
x_1349 = lean_ctor_get(x_1348, 1);
lean_inc(x_1349);
lean_dec(x_1348);
x_1322 = x_1349;
goto block_1341;
}
}
}
else
{
uint8_t x_1361; 
lean_dec(x_1313);
lean_dec(x_1305);
lean_dec(x_1290);
lean_dec(x_1274);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1361 = !lean_is_exclusive(x_1315);
if (x_1361 == 0)
{
return x_1315;
}
else
{
lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; 
x_1362 = lean_ctor_get(x_1315, 0);
x_1363 = lean_ctor_get(x_1315, 1);
lean_inc(x_1363);
lean_inc(x_1362);
lean_dec(x_1315);
x_1364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1364, 0, x_1362);
lean_ctor_set(x_1364, 1, x_1363);
return x_1364;
}
}
}
else
{
uint8_t x_1365; 
lean_dec(x_1305);
lean_dec(x_1290);
lean_dec(x_1274);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1365 = !lean_is_exclusive(x_1310);
if (x_1365 == 0)
{
return x_1310;
}
else
{
lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; 
x_1366 = lean_ctor_get(x_1310, 0);
x_1367 = lean_ctor_get(x_1310, 1);
lean_inc(x_1367);
lean_inc(x_1366);
lean_dec(x_1310);
x_1368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1368, 0, x_1366);
lean_ctor_set(x_1368, 1, x_1367);
return x_1368;
}
}
}
else
{
uint8_t x_1369; 
lean_dec(x_1290);
lean_dec(x_1274);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1369 = !lean_is_exclusive(x_1302);
if (x_1369 == 0)
{
return x_1302;
}
else
{
lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; 
x_1370 = lean_ctor_get(x_1302, 0);
x_1371 = lean_ctor_get(x_1302, 1);
lean_inc(x_1371);
lean_inc(x_1370);
lean_dec(x_1302);
x_1372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1372, 0, x_1370);
lean_ctor_set(x_1372, 1, x_1371);
return x_1372;
}
}
}
}
else
{
uint8_t x_1387; 
lean_dec(x_1290);
lean_dec(x_1280);
lean_dec(x_1274);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1387 = !lean_is_exclusive(x_1292);
if (x_1387 == 0)
{
return x_1292;
}
else
{
lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; 
x_1388 = lean_ctor_get(x_1292, 0);
x_1389 = lean_ctor_get(x_1292, 1);
lean_inc(x_1389);
lean_inc(x_1388);
lean_dec(x_1292);
x_1390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1390, 0, x_1388);
lean_ctor_set(x_1390, 1, x_1389);
return x_1390;
}
}
}
else
{
uint8_t x_1391; 
lean_dec(x_1280);
lean_dec(x_1274);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1391 = !lean_is_exclusive(x_1289);
if (x_1391 == 0)
{
return x_1289;
}
else
{
lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; 
x_1392 = lean_ctor_get(x_1289, 0);
x_1393 = lean_ctor_get(x_1289, 1);
lean_inc(x_1393);
lean_inc(x_1392);
lean_dec(x_1289);
x_1394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1394, 0, x_1392);
lean_ctor_set(x_1394, 1, x_1393);
return x_1394;
}
}
}
else
{
uint8_t x_1395; 
lean_dec(x_1274);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1395 = !lean_is_exclusive(x_1275);
if (x_1395 == 0)
{
return x_1275;
}
else
{
lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; 
x_1396 = lean_ctor_get(x_1275, 0);
x_1397 = lean_ctor_get(x_1275, 1);
lean_inc(x_1397);
lean_inc(x_1396);
lean_dec(x_1275);
x_1398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1398, 0, x_1396);
lean_ctor_set(x_1398, 1, x_1397);
return x_1398;
}
}
}
default: 
{
lean_object* x_1399; lean_object* x_1400; 
lean_dec(x_12);
lean_dec(x_10);
x_1399 = lean_ctor_get(x_7, 5);
lean_inc(x_1399);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1400 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_1399, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_1400) == 0)
{
lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; 
x_1401 = lean_ctor_get(x_1400, 1);
lean_inc(x_1401);
lean_dec(x_1400);
x_1402 = lean_st_ref_get(x_14, x_1401);
x_1403 = lean_ctor_get(x_1402, 0);
lean_inc(x_1403);
x_1404 = lean_ctor_get(x_1402, 1);
lean_inc(x_1404);
lean_dec(x_1402);
x_1405 = lean_ctor_get(x_1403, 0);
lean_inc(x_1405);
lean_dec(x_1403);
x_1406 = lean_ctor_get(x_7, 6);
lean_inc(x_1406);
x_1407 = l_List_redLength___main___rarg(x_1406);
x_1408 = lean_mk_empty_array_with_capacity(x_1407);
lean_dec(x_1407);
lean_inc(x_1406);
x_1409 = l_List_toArrayAux___main___rarg(x_1406, x_1408);
x_1410 = x_1409;
x_1411 = lean_unsigned_to_nat(0u);
lean_inc(x_1405);
lean_inc(x_6);
lean_inc(x_1);
x_1412 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_1412, 0, x_1);
lean_closure_set(x_1412, 1, x_6);
lean_closure_set(x_1412, 2, x_9);
lean_closure_set(x_1412, 3, x_11);
lean_closure_set(x_1412, 4, x_1405);
lean_closure_set(x_1412, 5, x_1406);
lean_closure_set(x_1412, 6, x_1411);
lean_closure_set(x_1412, 7, x_1410);
x_1413 = x_1412;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_1414 = lean_apply_5(x_1413, x_13, x_14, x_15, x_16, x_1404);
if (lean_obj_tag(x_1414) == 0)
{
lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; 
x_1415 = lean_ctor_get(x_1414, 0);
lean_inc(x_1415);
x_1416 = lean_ctor_get(x_1414, 1);
lean_inc(x_1416);
lean_dec(x_1414);
lean_inc(x_1);
x_1417 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_1416);
if (lean_obj_tag(x_1417) == 0)
{
lean_object* x_1418; lean_object* x_1419; uint8_t x_1420; lean_object* x_1421; 
x_1418 = lean_ctor_get(x_1417, 0);
lean_inc(x_1418);
x_1419 = lean_ctor_get(x_1417, 1);
lean_inc(x_1419);
lean_dec(x_1417);
x_1420 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_1420 == 0)
{
lean_object* x_1499; uint8_t x_1500; 
x_1499 = l_Lean_MetavarContext_exprDependsOn(x_1405, x_1418, x_2);
x_1500 = lean_unbox(x_1499);
lean_dec(x_1499);
if (x_1500 == 0)
{
x_1421 = x_1419;
goto block_1498;
}
else
{
lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; uint8_t x_1508; 
lean_dec(x_1415);
lean_dec(x_1399);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_1501 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1501, 0, x_3);
x_1502 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1503 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1503, 0, x_1502);
lean_ctor_set(x_1503, 1, x_1501);
x_1504 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_1505 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1505, 0, x_1503);
lean_ctor_set(x_1505, 1, x_1504);
x_1506 = lean_box(0);
x_1507 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1505, x_1506, x_13, x_14, x_15, x_16, x_1419);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1508 = !lean_is_exclusive(x_1507);
if (x_1508 == 0)
{
return x_1507;
}
else
{
lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; 
x_1509 = lean_ctor_get(x_1507, 0);
x_1510 = lean_ctor_get(x_1507, 1);
lean_inc(x_1510);
lean_inc(x_1509);
lean_dec(x_1507);
x_1511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1511, 0, x_1509);
lean_ctor_set(x_1511, 1, x_1510);
return x_1511;
}
}
}
else
{
lean_dec(x_1418);
lean_dec(x_1405);
x_1421 = x_1419;
goto block_1498;
}
block_1498:
{
lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; uint8_t x_1426; lean_object* x_1427; 
lean_inc(x_1415);
x_1422 = x_1415;
x_1423 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1411, x_1422);
x_1424 = x_1423;
x_1425 = lean_array_push(x_1424, x_2);
x_1426 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1427 = l_Lean_Meta_revert(x_1, x_1425, x_1426, x_13, x_14, x_15, x_16, x_1421);
if (lean_obj_tag(x_1427) == 0)
{
lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; uint8_t x_1434; lean_object* x_1435; 
x_1428 = lean_ctor_get(x_1427, 0);
lean_inc(x_1428);
x_1429 = lean_ctor_get(x_1427, 1);
lean_inc(x_1429);
lean_dec(x_1427);
x_1430 = lean_ctor_get(x_1428, 0);
lean_inc(x_1430);
x_1431 = lean_ctor_get(x_1428, 1);
lean_inc(x_1431);
lean_dec(x_1428);
x_1432 = lean_array_get_size(x_1415);
x_1433 = lean_box(0);
x_1434 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1435 = l_Lean_Meta_introN(x_1431, x_1432, x_1433, x_1434, x_13, x_14, x_15, x_16, x_1429);
if (lean_obj_tag(x_1435) == 0)
{
lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; 
x_1436 = lean_ctor_get(x_1435, 0);
lean_inc(x_1436);
x_1437 = lean_ctor_get(x_1435, 1);
lean_inc(x_1437);
lean_dec(x_1435);
x_1438 = lean_ctor_get(x_1436, 0);
lean_inc(x_1438);
x_1439 = lean_ctor_get(x_1436, 1);
lean_inc(x_1439);
lean_dec(x_1436);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1440 = l_Lean_Meta_intro1(x_1439, x_1434, x_13, x_14, x_15, x_16, x_1437);
if (lean_obj_tag(x_1440) == 0)
{
lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; uint8_t x_1467; lean_object* x_1468; lean_object* x_1476; lean_object* x_1477; uint8_t x_1478; 
x_1441 = lean_ctor_get(x_1440, 0);
lean_inc(x_1441);
x_1442 = lean_ctor_get(x_1440, 1);
lean_inc(x_1442);
lean_dec(x_1440);
x_1443 = lean_ctor_get(x_1441, 0);
lean_inc(x_1443);
x_1444 = lean_ctor_get(x_1441, 1);
lean_inc(x_1444);
lean_dec(x_1441);
x_1445 = lean_box(0);
x_1446 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_1415, x_1438, x_1415, x_1411, x_1445);
lean_dec(x_1415);
x_1476 = l_Lean_Core_getTraceState___rarg(x_16, x_1442);
x_1477 = lean_ctor_get(x_1476, 0);
lean_inc(x_1477);
x_1478 = lean_ctor_get_uint8(x_1477, sizeof(void*)*1);
lean_dec(x_1477);
if (x_1478 == 0)
{
lean_object* x_1479; 
x_1479 = lean_ctor_get(x_1476, 1);
lean_inc(x_1479);
lean_dec(x_1476);
x_1467 = x_1434;
x_1468 = x_1479;
goto block_1475;
}
else
{
lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; uint8_t x_1485; 
x_1480 = lean_ctor_get(x_1476, 1);
lean_inc(x_1480);
lean_dec(x_1476);
x_1481 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1482 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1481, x_15, x_16, x_1480);
x_1483 = lean_ctor_get(x_1482, 0);
lean_inc(x_1483);
x_1484 = lean_ctor_get(x_1482, 1);
lean_inc(x_1484);
lean_dec(x_1482);
x_1485 = lean_unbox(x_1483);
lean_dec(x_1483);
x_1467 = x_1485;
x_1468 = x_1484;
goto block_1475;
}
block_1466:
{
lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; 
x_1448 = x_1438;
x_1449 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1411, x_1448);
x_1450 = x_1449;
lean_inc(x_1443);
x_1451 = l_Lean_mkFVar(x_1443);
lean_inc(x_1444);
x_1452 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1452, 0, x_1444);
x_1453 = lean_box(x_1420);
lean_inc(x_1444);
x_1454 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_1454, 0, x_1443);
lean_closure_set(x_1454, 1, x_8);
lean_closure_set(x_1454, 2, x_1444);
lean_closure_set(x_1454, 3, x_3);
lean_closure_set(x_1454, 4, x_4);
lean_closure_set(x_1454, 5, x_6);
lean_closure_set(x_1454, 6, x_7);
lean_closure_set(x_1454, 7, x_1399);
lean_closure_set(x_1454, 8, x_1453);
lean_closure_set(x_1454, 9, x_1430);
lean_closure_set(x_1454, 10, x_1446);
lean_closure_set(x_1454, 11, x_1450);
lean_closure_set(x_1454, 12, x_1451);
x_1455 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_1455, 0, x_1452);
lean_closure_set(x_1455, 1, x_1454);
x_1456 = l_Lean_Meta_getMVarDecl(x_1444, x_13, x_14, x_15, x_16, x_1447);
if (lean_obj_tag(x_1456) == 0)
{
lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; 
x_1457 = lean_ctor_get(x_1456, 0);
lean_inc(x_1457);
x_1458 = lean_ctor_get(x_1456, 1);
lean_inc(x_1458);
lean_dec(x_1456);
x_1459 = lean_ctor_get(x_1457, 1);
lean_inc(x_1459);
x_1460 = lean_ctor_get(x_1457, 4);
lean_inc(x_1460);
lean_dec(x_1457);
x_1461 = l_Lean_Meta_withLocalContext___rarg(x_1459, x_1460, x_1455, x_13, x_14, x_15, x_16, x_1458);
lean_dec(x_13);
return x_1461;
}
else
{
uint8_t x_1462; 
lean_dec(x_1455);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1462 = !lean_is_exclusive(x_1456);
if (x_1462 == 0)
{
return x_1456;
}
else
{
lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; 
x_1463 = lean_ctor_get(x_1456, 0);
x_1464 = lean_ctor_get(x_1456, 1);
lean_inc(x_1464);
lean_inc(x_1463);
lean_dec(x_1456);
x_1465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1465, 0, x_1463);
lean_ctor_set(x_1465, 1, x_1464);
return x_1465;
}
}
}
block_1475:
{
if (x_1467 == 0)
{
x_1447 = x_1468;
goto block_1466;
}
else
{
lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; 
lean_inc(x_1444);
x_1469 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1469, 0, x_1444);
x_1470 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_1471 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1471, 0, x_1470);
lean_ctor_set(x_1471, 1, x_1469);
x_1472 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1473 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1472, x_1471, x_13, x_14, x_15, x_16, x_1468);
x_1474 = lean_ctor_get(x_1473, 1);
lean_inc(x_1474);
lean_dec(x_1473);
x_1447 = x_1474;
goto block_1466;
}
}
}
else
{
uint8_t x_1486; 
lean_dec(x_1438);
lean_dec(x_1430);
lean_dec(x_1415);
lean_dec(x_1399);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1486 = !lean_is_exclusive(x_1440);
if (x_1486 == 0)
{
return x_1440;
}
else
{
lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; 
x_1487 = lean_ctor_get(x_1440, 0);
x_1488 = lean_ctor_get(x_1440, 1);
lean_inc(x_1488);
lean_inc(x_1487);
lean_dec(x_1440);
x_1489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1489, 0, x_1487);
lean_ctor_set(x_1489, 1, x_1488);
return x_1489;
}
}
}
else
{
uint8_t x_1490; 
lean_dec(x_1430);
lean_dec(x_1415);
lean_dec(x_1399);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1490 = !lean_is_exclusive(x_1435);
if (x_1490 == 0)
{
return x_1435;
}
else
{
lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; 
x_1491 = lean_ctor_get(x_1435, 0);
x_1492 = lean_ctor_get(x_1435, 1);
lean_inc(x_1492);
lean_inc(x_1491);
lean_dec(x_1435);
x_1493 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1493, 0, x_1491);
lean_ctor_set(x_1493, 1, x_1492);
return x_1493;
}
}
}
else
{
uint8_t x_1494; 
lean_dec(x_1415);
lean_dec(x_1399);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1494 = !lean_is_exclusive(x_1427);
if (x_1494 == 0)
{
return x_1427;
}
else
{
lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; 
x_1495 = lean_ctor_get(x_1427, 0);
x_1496 = lean_ctor_get(x_1427, 1);
lean_inc(x_1496);
lean_inc(x_1495);
lean_dec(x_1427);
x_1497 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1497, 0, x_1495);
lean_ctor_set(x_1497, 1, x_1496);
return x_1497;
}
}
}
}
else
{
uint8_t x_1512; 
lean_dec(x_1415);
lean_dec(x_1405);
lean_dec(x_1399);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1512 = !lean_is_exclusive(x_1417);
if (x_1512 == 0)
{
return x_1417;
}
else
{
lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; 
x_1513 = lean_ctor_get(x_1417, 0);
x_1514 = lean_ctor_get(x_1417, 1);
lean_inc(x_1514);
lean_inc(x_1513);
lean_dec(x_1417);
x_1515 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1515, 0, x_1513);
lean_ctor_set(x_1515, 1, x_1514);
return x_1515;
}
}
}
else
{
uint8_t x_1516; 
lean_dec(x_1405);
lean_dec(x_1399);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1516 = !lean_is_exclusive(x_1414);
if (x_1516 == 0)
{
return x_1414;
}
else
{
lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; 
x_1517 = lean_ctor_get(x_1414, 0);
x_1518 = lean_ctor_get(x_1414, 1);
lean_inc(x_1518);
lean_inc(x_1517);
lean_dec(x_1414);
x_1519 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1519, 0, x_1517);
lean_ctor_set(x_1519, 1, x_1518);
return x_1519;
}
}
}
else
{
uint8_t x_1520; 
lean_dec(x_1399);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1520 = !lean_is_exclusive(x_1400);
if (x_1520 == 0)
{
return x_1400;
}
else
{
lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; 
x_1521 = lean_ctor_get(x_1400, 0);
x_1522 = lean_ctor_get(x_1400, 1);
lean_inc(x_1522);
lean_inc(x_1521);
lean_dec(x_1400);
x_1523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1523, 0, x_1521);
lean_ctor_set(x_1523, 1, x_1522);
return x_1523;
}
}
}
}
}
}
lean_object* l_Lean_Meta_induction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_8);
lean_inc(x_1);
x_13 = l_Lean_Meta_getLocalDecl(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_17 = l_Lean_Meta_mkRecursorInfo(x_2, x_16, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_LocalDecl_type(x_14);
lean_dec(x_14);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_20);
x_22 = l_Lean_Meta_whnfUntil(x_20, x_21, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(x_3, x_20, x_8, x_9, x_10, x_11, x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_20);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_Expr_getAppNumArgsAux___main(x_27, x_28);
x_30 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_29);
x_31 = lean_mk_array(x_29, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_29, x_32);
lean_dec(x_29);
lean_inc(x_27);
x_34 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(x_3, x_1, x_2, x_4, x_5, x_6, x_18, x_21, x_27, x_27, x_31, x_33, x_8, x_9, x_10, x_11, x_26);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_17, 0);
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_17);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_13);
if (x_43 == 0)
{
return x_13;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_13, 0);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l_Lean_Meta_induction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = l___private_Lean_Meta_Basic_3__forallTelescopeReducingAuxAux___main___rarg___closed__1;
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_induction___lambda__1___boxed), 12, 6);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_13);
lean_closure_set(x_14, 5, x_11);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_getMVarDecl(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 4);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_Meta_withLocalContext___rarg(x_19, x_20, x_15, x_6, x_7, x_8, x_9, x_18);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
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
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_16;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
return x_14;
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
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_foldlM___main___at_Lean_Meta_induction___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_12;
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
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_unbox(x_6);
lean_dec(x_6);
x_23 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7(x_1, x_2, x_3, x_4, x_5, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_23;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed(lean_object** _args) {
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
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_9);
lean_dec(x_9);
x_21 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_21;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_5);
return x_18;
}
}
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_induction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_5);
return x_13;
}
}
lean_object* l_Lean_Meta_induction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_induction(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_12;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_RecursorInfo(lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Revert(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Induction(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_RecursorInfo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FVarSubst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7);
l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8 = _init_l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8);
l_Lean_Meta_InductionSubgoal_inhabited___closed__1 = _init_l_Lean_Meta_InductionSubgoal_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_InductionSubgoal_inhabited___closed__1);
l_Lean_Meta_InductionSubgoal_inhabited = _init_l_Lean_Meta_InductionSubgoal_inhabited();
lean_mark_persistent(l_Lean_Meta_InductionSubgoal_inhabited);
l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1 = _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1);
l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2 = _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2);
l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3 = _init_l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3);
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
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__4 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__4);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__7 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__7();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__7);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8);
res = l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
