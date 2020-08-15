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
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity(lean_object*);
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___boxed(lean_object**);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__3;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__2;
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__2;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_List_elem___main___at_Lean_Meta_induction___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7;
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__9;
lean_object* l_Lean_Meta_getMVarType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__9;
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__8;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__4;
extern lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__8;
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
lean_object* l_Lean_MetavarContext_localDeclDependsOn(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__7;
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InductionSubgoal_inhabited___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__2;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__4;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___boxed(lean_object**);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__6;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__3;
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__5;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__5;
extern lean_object* l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
extern lean_object* l_Lean_Meta_isClassQuick___main___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__4;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__1;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__2;
lean_object* l_Lean_Meta_InductionSubgoal_inhabited;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__2;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__1;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
lean_object* l_Lean_Meta_whnfUntil(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__7;
lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_4);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_24 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8;
x_25 = lean_box(0);
x_26 = l_Lean_Meta_throwTacticEx___rarg(x_23, x_1, x_24, x_25, x_5, x_22);
lean_dec(x_5);
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
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_14);
lean_dec(x_4);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_dec(x_13);
x_32 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_33 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_34 = lean_box(0);
x_35 = l_Lean_Meta_throwTacticEx___rarg(x_32, x_1, x_33, x_34, x_5, x_31);
lean_dec(x_5);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_3, 1);
x_45 = lean_ctor_get(x_8, 0);
x_46 = lean_array_get_size(x_2);
x_47 = lean_nat_dec_lt(x_45, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_4);
x_48 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_49 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_50 = lean_box(0);
x_51 = l_Lean_Meta_throwTacticEx___rarg(x_48, x_1, x_49, x_50, x_5, x_6);
lean_dec(x_5);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_array_fget(x_2, x_45);
x_53 = l_Lean_mkApp(x_4, x_52);
x_3 = x_44;
x_4 = x_53;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_18 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_19 = lean_box(0);
x_20 = l_Lean_Meta_throwTacticEx___rarg(x_17, x_1, x_18, x_19, x_4, x_16);
lean_dec(x_4);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_4);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_18 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_16, x_11, x_6, x_7);
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
x_29 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_27, x_11, x_6, x_7);
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
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_12);
x_22 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_23 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_24 = lean_box(0);
x_25 = l_Lean_Meta_throwTacticEx___rarg(x_22, x_1, x_23, x_24, x_16, x_20);
lean_dec(x_16);
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
else
{
lean_object* x_30; 
x_30 = l_Lean_Meta_assignExprMVar(x_1, x_12, x_16, x_20);
lean_dec(x_16);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_15);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_15);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_3, 3);
x_40 = lean_nat_dec_lt(x_10, x_39);
if (x_40 == 0)
{
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
if (x_14 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_15);
lean_dec(x_12);
x_41 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_42 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_43 = lean_box(0);
x_44 = l_Lean_Meta_throwTacticEx___rarg(x_41, x_1, x_42, x_43, x_16, x_20);
lean_dec(x_16);
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
lean_object* x_49; 
x_49 = l_Lean_Meta_assignExprMVar(x_1, x_12, x_16, x_20);
lean_dec(x_16);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_15);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_15);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_15);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_Meta_RecursorInfo_firstIndexPos(x_3);
x_59 = lean_nat_dec_eq(x_10, x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_inc(x_1);
x_60 = l_Lean_Meta_getMVarTag(x_1, x_16, x_20);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_201; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_201 = lean_nat_dec_le(x_8, x_11);
if (x_201 == 0)
{
x_63 = x_62;
goto block_200;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
lean_dec(x_61);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_202 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_203 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_204 = lean_box(0);
x_205 = l_Lean_Meta_throwTacticEx___rarg(x_202, x_1, x_203, x_204, x_16, x_62);
lean_dec(x_16);
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
return x_205;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_205, 0);
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_205);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
block_200:
{
if (lean_obj_tag(x_19) == 7)
{
lean_object* x_64; lean_object* x_65; uint64_t x_66; lean_object* x_67; lean_object* x_68; uint8_t x_149; uint8_t x_150; 
x_64 = lean_ctor_get(x_19, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_19, 1);
lean_inc(x_65);
x_66 = lean_ctor_get_uint64(x_19, sizeof(void*)*3);
x_67 = l_Lean_Expr_headBeta(x_65);
x_149 = (uint8_t)((x_66 << 24) >> 61);
x_150 = l_Lean_BinderInfo_isInstImplicit(x_149);
if (x_150 == 0)
{
lean_object* x_151; 
x_151 = lean_box(0);
x_68 = x_151;
goto block_148;
}
else
{
uint8_t x_152; 
x_152 = l_Array_isEmpty___rarg(x_2);
if (x_152 == 0)
{
lean_object* x_153; 
x_153 = lean_box(0);
x_68 = x_153;
goto block_148;
}
else
{
lean_object* x_154; 
lean_inc(x_16);
lean_inc(x_67);
x_154 = l_Lean_Meta_synthInstance_x3f(x_67, x_16, x_63);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = l_Lean_Name_append___main(x_61, x_64);
lean_dec(x_61);
x_158 = 2;
lean_inc(x_16);
x_159 = l_Lean_Meta_mkFreshExprMVar(x_67, x_157, x_158, x_16, x_156);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
lean_inc(x_160);
x_162 = l_Lean_mkApp(x_12, x_160);
lean_inc(x_16);
lean_inc(x_1);
x_163 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_19, x_160, x_16, x_161);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_nat_add(x_10, x_166);
lean_dec(x_10);
x_168 = lean_nat_add(x_11, x_166);
lean_dec(x_11);
x_169 = l_Lean_Expr_mvarId_x21(x_160);
lean_dec(x_160);
x_170 = lean_box(0);
x_171 = l_Array_empty___closed__1;
x_172 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_171);
lean_ctor_set(x_172, 2, x_170);
x_173 = lean_array_push(x_15, x_172);
x_10 = x_167;
x_11 = x_168;
x_12 = x_162;
x_13 = x_164;
x_15 = x_173;
x_17 = x_165;
goto _start;
}
else
{
uint8_t x_175; 
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_175 = !lean_is_exclusive(x_163);
if (x_175 == 0)
{
return x_163;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_163, 0);
x_177 = lean_ctor_get(x_163, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_163);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_61);
x_179 = lean_ctor_get(x_154, 1);
lean_inc(x_179);
lean_dec(x_154);
x_180 = lean_ctor_get(x_155, 0);
lean_inc(x_180);
lean_dec(x_155);
lean_inc(x_180);
x_181 = l_Lean_mkApp(x_12, x_180);
lean_inc(x_16);
lean_inc(x_1);
x_182 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_19, x_180, x_16, x_179);
lean_dec(x_180);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = lean_unsigned_to_nat(1u);
x_186 = lean_nat_add(x_10, x_185);
lean_dec(x_10);
x_187 = lean_nat_add(x_11, x_185);
lean_dec(x_11);
x_10 = x_186;
x_11 = x_187;
x_12 = x_181;
x_13 = x_183;
x_17 = x_184;
goto _start;
}
else
{
uint8_t x_189; 
lean_dec(x_181);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_182);
if (x_189 == 0)
{
return x_182;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_182, 0);
x_191 = lean_ctor_get(x_182, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_182);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_193 = !lean_is_exclusive(x_154);
if (x_193 == 0)
{
return x_154;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_154, 0);
x_195 = lean_ctor_get(x_154, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_154);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
}
block_148:
{
lean_object* x_69; uint8_t x_70; 
lean_dec(x_68);
lean_inc(x_67);
x_69 = l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_67);
x_70 = lean_nat_dec_lt(x_69, x_6);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_129; uint8_t x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_71 = lean_nat_sub(x_69, x_6);
lean_dec(x_69);
x_72 = lean_array_get_size(x_4);
x_73 = lean_array_get_size(x_7);
x_74 = lean_nat_sub(x_72, x_73);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_sub(x_74, x_75);
lean_dec(x_74);
x_129 = lean_array_get_size(x_2);
x_130 = lean_nat_dec_lt(x_11, x_129);
lean_dec(x_129);
x_131 = l_Lean_Name_append___main(x_61, x_64);
lean_dec(x_61);
x_132 = 2;
lean_inc(x_16);
x_133 = l_Lean_Meta_mkFreshExprMVar(x_67, x_131, x_132, x_16, x_63);
if (x_130 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_box(0);
x_77 = x_136;
x_78 = x_134;
x_79 = x_135;
goto block_128;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
lean_dec(x_133);
x_139 = lean_array_fget(x_2, x_11);
x_77 = x_139;
x_78 = x_137;
x_79 = x_138;
goto block_128;
}
block_128:
{
lean_object* x_80; lean_object* x_81; 
lean_inc(x_78);
x_80 = l_Lean_mkApp(x_12, x_78);
lean_inc(x_16);
lean_inc(x_1);
x_81 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_19, x_78, x_16, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Expr_mvarId_x21(x_78);
lean_dec(x_78);
x_85 = l_Lean_Expr_fvarId_x21(x_5);
x_86 = l_Lean_Meta_tryClear(x_84, x_85, x_16, x_83);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = 1;
x_90 = l_Lean_Meta_introN(x_87, x_71, x_77, x_89, x_16, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_box(0);
x_96 = 0;
x_97 = l_Lean_Meta_introN(x_94, x_76, x_95, x_96, x_16, x_92);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
lean_inc(x_9);
lean_inc(x_72);
x_102 = l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(x_4, x_7, x_73, x_100, x_72, x_72, x_9);
lean_dec(x_72);
lean_dec(x_100);
lean_dec(x_73);
x_103 = x_93;
x_104 = lean_unsigned_to_nat(0u);
x_105 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_104, x_103);
x_106 = x_105;
x_107 = lean_nat_add(x_10, x_75);
lean_dec(x_10);
x_108 = lean_nat_add(x_11, x_75);
lean_dec(x_11);
x_109 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_109, 0, x_101);
lean_ctor_set(x_109, 1, x_106);
lean_ctor_set(x_109, 2, x_102);
x_110 = lean_array_push(x_15, x_109);
x_10 = x_107;
x_11 = x_108;
x_12 = x_80;
x_13 = x_82;
x_15 = x_110;
x_17 = x_99;
goto _start;
}
else
{
uint8_t x_112; 
lean_dec(x_93);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_97);
if (x_112 == 0)
{
return x_97;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_97, 0);
x_114 = lean_ctor_get(x_97, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_97);
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
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_90);
if (x_116 == 0)
{
return x_90;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_90, 0);
x_118 = lean_ctor_get(x_90, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_90);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_86);
if (x_120 == 0)
{
return x_86;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_86, 0);
x_122 = lean_ctor_get(x_86, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_86);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_81);
if (x_124 == 0)
{
return x_81;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_81, 0);
x_126 = lean_ctor_get(x_81, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_81);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_140 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_141 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_142 = lean_box(0);
x_143 = l_Lean_Meta_throwTacticEx___rarg(x_140, x_1, x_141, x_142, x_16, x_63);
lean_dec(x_16);
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
return x_143;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_143, 0);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_143);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_61);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_197 = l_Lean_Meta_isClassQuick___main___closed__1;
x_198 = l_unreachable_x21___rarg(x_197);
x_199 = lean_apply_2(x_198, x_16, x_63);
return x_199;
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_210 = !lean_is_exclusive(x_60);
if (x_210 == 0)
{
return x_60;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_60, 0);
x_212 = lean_ctor_get(x_60, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_60);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_12);
lean_ctor_set(x_214, 1, x_19);
x_215 = lean_unsigned_to_nat(0u);
lean_inc(x_16);
lean_inc(x_1);
x_216 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(x_1, x_7, x_7, x_215, x_214, x_16, x_20);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_ctor_get(x_217, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
lean_dec(x_217);
lean_inc(x_5);
x_221 = l_Lean_mkApp(x_219, x_5);
lean_inc(x_16);
lean_inc(x_1);
x_222 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_220, x_5, x_16, x_218);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_unsigned_to_nat(1u);
x_226 = lean_nat_add(x_10, x_225);
lean_dec(x_10);
x_227 = lean_array_get_size(x_7);
x_228 = lean_nat_add(x_226, x_227);
lean_dec(x_227);
lean_dec(x_226);
x_229 = 1;
x_10 = x_228;
x_12 = x_221;
x_13 = x_223;
x_14 = x_229;
x_17 = x_224;
goto _start;
}
else
{
uint8_t x_231; 
lean_dec(x_221);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_231 = !lean_is_exclusive(x_222);
if (x_231 == 0)
{
return x_222;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_222, 0);
x_233 = lean_ctor_get(x_222, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_222);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
else
{
uint8_t x_235; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_235 = !lean_is_exclusive(x_216);
if (x_235 == 0)
{
return x_216;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_216, 0);
x_237 = lean_ctor_get(x_216, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_216);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
}
}
}
else
{
uint8_t x_239; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_239 = !lean_is_exclusive(x_18);
if (x_239 == 0)
{
return x_18;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_18, 0);
x_241 = lean_ctor_get(x_18, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_18);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
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
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_14);
lean_dec(x_14);
x_19 = l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_18, x_15, x_16, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
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
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_14);
lean_dec(x_14);
x_19 = l___private_Lean_Meta_Tactic_Induction_4__finalizeAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_18, x_15, x_16, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_14 = l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_12);
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
x_27 = l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(x_1, x_2, x_3, x_4, x_5, x_14, x_6, x_20, x_7, x_24, x_19, x_8, x_16, x_25, x_26, x_9, x_17);
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
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
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
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = l_Lean_indentExpr(x_5);
x_7 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3;
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_10 = lean_box(0);
x_11 = l_Lean_Meta_throwTacticEx___rarg(x_9, x_1, x_8, x_10, x_3, x_4);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_3);
x_19 = l_Lean_indentExpr(x_18);
x_20 = l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__3;
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_box(0);
x_23 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_21, x_22, x_6, x_7);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_57; uint8_t x_77; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_10, x_15);
lean_dec(x_10);
x_17 = lean_nat_sub(x_9, x_16);
x_18 = lean_nat_sub(x_17, x_15);
lean_dec(x_17);
x_19 = l_Lean_Expr_Inhabited;
x_20 = lean_array_get(x_19, x_4, x_18);
x_77 = lean_nat_dec_eq(x_18, x_7);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = lean_expr_eqv(x_20, x_8);
if (x_78 == 0)
{
x_57 = x_12;
goto block_76;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_5);
x_79 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_79, 0, x_8);
x_80 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_81 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__9;
x_83 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_84, 0, x_3);
x_85 = l_Lean_indentExpr(x_84);
x_86 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_box(0);
x_88 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_86, x_87, x_11, x_12);
lean_dec(x_11);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
return x_88;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_88);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
x_57 = x_12;
goto block_76;
}
block_56:
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
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
x_46 = lean_box(0);
x_47 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_45, x_46, x_11, x_31);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_29);
if (x_52 == 0)
{
return x_29;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_29, 0);
x_54 = lean_ctor_get(x_29, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_29);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
}
block_76:
{
uint8_t x_58; 
x_58 = lean_nat_dec_lt(x_18, x_7);
if (x_58 == 0)
{
x_21 = x_57;
goto block_56;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = l_Lean_Expr_fvarId_x21(x_8);
lean_inc(x_20);
lean_inc(x_5);
x_60 = l_Lean_MetavarContext_exprDependsOn(x_5, x_20, x_59);
lean_dec(x_59);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
x_21 = x_57;
goto block_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_5);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_8);
x_63 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_64 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__6;
x_66 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_3);
x_68 = l_Lean_indentExpr(x_67);
x_69 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_box(0);
x_71 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_69, x_70, x_11, x_57);
lean_dec(x_11);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
return x_71;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_71);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_12);
return x_94;
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
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = x_8;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_52; 
x_15 = lean_array_fget(x_8, x_7);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_8, x_7, x_16);
x_18 = x_15;
x_19 = lean_array_get_size(x_4);
x_52 = lean_nat_dec_le(x_19, x_18);
if (x_52 == 0)
{
x_20 = x_10;
goto block_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_5);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_3);
x_54 = l_Lean_indentExpr(x_53);
x_55 = l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__3;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_box(0);
x_58 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_56, x_57, x_9, x_10);
lean_dec(x_9);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
block_51:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_36; 
x_21 = l_Lean_Expr_Inhabited;
x_22 = lean_array_get(x_21, x_4, x_18);
x_36 = l_Lean_Expr_isFVar(x_22);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_5);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_22);
x_38 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__3;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___closed__6;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_3);
x_43 = l_Lean_indentExpr(x_42);
x_44 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_box(0);
x_46 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_44, x_45, x_9, x_20);
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
x_23 = x_20;
goto block_35;
}
block_35:
{
lean_object* x_24; 
lean_inc(x_9);
lean_inc(x_19);
lean_inc(x_22);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_24 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_18, x_22, x_19, x_19, x_9, x_23);
lean_dec(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_7, x_26);
x_28 = x_22;
x_29 = lean_array_fset(x_17, x_7, x_28);
lean_dec(x_7);
x_7 = x_27;
x_8 = x_29;
x_10 = x_25;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_free_object(x_5);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_3);
x_37 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_38 = lean_box(0);
x_39 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_37, x_38, x_7, x_8);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_39);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_6, 1);
x_45 = lean_ctor_get(x_5, 0);
x_46 = lean_ctor_get(x_5, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_5);
x_47 = lean_ctor_get(x_10, 0);
x_48 = lean_array_get_size(x_4);
x_49 = lean_nat_dec_le(x_48, x_47);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = l_Lean_Level_Inhabited;
x_51 = lean_array_get(x_50, x_4, x_47);
x_52 = lean_array_push(x_45, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
x_5 = x_53;
x_6 = x_44;
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_3);
x_55 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_56 = lean_box(0);
x_57 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_55, x_56, x_7, x_8);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
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
x_24 = l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
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
x_37 = lean_box(0);
x_38 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_36, x_37, x_17, x_29);
lean_dec(x_17);
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
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_3);
x_43 = l_Array_toList___rarg(x_30);
lean_dec(x_30);
x_44 = l_Lean_mkConst(x_1, x_43);
lean_inc(x_17);
lean_inc(x_8);
x_45 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_8, x_15, x_5, x_44, x_17, x_29);
lean_dec(x_15);
if (lean_obj_tag(x_45) == 0)
{
if (x_6 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_17);
lean_inc(x_10);
x_48 = l_Lean_Meta_mkLambda(x_10, x_12, x_17, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_mkApp(x_46, x_49);
x_52 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_51, x_17, x_50);
lean_dec(x_10);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_46);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
return x_48;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_48, 0);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_48);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_45, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_dec(x_45);
x_59 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_11);
x_60 = lean_array_push(x_59, x_11);
lean_inc(x_17);
x_61 = l_Lean_Meta_mkLambda(x_60, x_12, x_17, x_58);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_17);
lean_inc(x_10);
x_64 = l_Lean_Meta_mkLambda(x_10, x_62, x_17, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_mkApp(x_57, x_65);
x_68 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_67, x_17, x_66);
lean_dec(x_10);
return x_68;
}
else
{
uint8_t x_69; 
lean_dec(x_57);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_69 = !lean_is_exclusive(x_64);
if (x_69 == 0)
{
return x_64;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_64, 0);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_64);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_57);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_73 = !lean_is_exclusive(x_61);
if (x_73 == 0)
{
return x_61;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_61, 0);
x_75 = lean_ctor_get(x_61, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_61);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_77 = !lean_is_exclusive(x_45);
if (x_77 == 0)
{
return x_45;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_45, 0);
x_79 = lean_ctor_get(x_45, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_45);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_13);
lean_dec(x_3);
x_81 = lean_ctor_get(x_25, 1);
lean_inc(x_81);
lean_dec(x_25);
x_82 = lean_ctor_get(x_26, 0);
lean_inc(x_82);
lean_dec(x_26);
x_83 = l_Array_toList___rarg(x_82);
lean_dec(x_82);
x_84 = l_Lean_mkConst(x_1, x_83);
lean_inc(x_17);
lean_inc(x_8);
x_85 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_8, x_15, x_5, x_84, x_17, x_81);
lean_dec(x_15);
if (lean_obj_tag(x_85) == 0)
{
if (x_6 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_17);
lean_inc(x_10);
x_88 = l_Lean_Meta_mkLambda(x_10, x_12, x_17, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_mkApp(x_86, x_89);
x_92 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_91, x_17, x_90);
lean_dec(x_10);
return x_92;
}
else
{
uint8_t x_93; 
lean_dec(x_86);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_93 = !lean_is_exclusive(x_88);
if (x_93 == 0)
{
return x_88;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_88, 0);
x_95 = lean_ctor_get(x_88, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_88);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_85, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_85, 1);
lean_inc(x_98);
lean_dec(x_85);
x_99 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_11);
x_100 = lean_array_push(x_99, x_11);
lean_inc(x_17);
x_101 = l_Lean_Meta_mkLambda(x_100, x_12, x_17, x_98);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_17);
lean_inc(x_10);
x_104 = l_Lean_Meta_mkLambda(x_10, x_102, x_17, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_mkApp(x_97, x_105);
x_108 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_107, x_17, x_106);
lean_dec(x_10);
return x_108;
}
else
{
uint8_t x_109; 
lean_dec(x_97);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_109 = !lean_is_exclusive(x_104);
if (x_109 == 0)
{
return x_104;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_104, 0);
x_111 = lean_ctor_get(x_104, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_104);
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
lean_dec(x_97);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_113 = !lean_is_exclusive(x_101);
if (x_113 == 0)
{
return x_101;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_101, 0);
x_115 = lean_ctor_get(x_101, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_101);
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
uint8_t x_117; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_117 = !lean_is_exclusive(x_85);
if (x_117 == 0)
{
return x_85;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_85, 0);
x_119 = lean_ctor_get(x_85, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_85);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
else
{
uint8_t x_121; 
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
x_121 = !lean_is_exclusive(x_25);
if (x_121 == 0)
{
return x_25;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_25, 0);
x_123 = lean_ctor_get(x_25, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_25);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
case 5:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_14, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_14, 1);
lean_inc(x_126);
lean_dec(x_14);
x_127 = lean_array_set(x_15, x_16, x_126);
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_nat_sub(x_16, x_128);
lean_dec(x_16);
x_14 = x_125;
x_15 = x_127;
x_16 = x_129;
goto _start;
}
default: 
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_131 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__3;
x_132 = lean_box(0);
x_133 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_131, x_132, x_17, x_18);
lean_dec(x_17);
return x_133;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
lean_inc(x_23);
x_24 = l_Lean_Meta_whnfUntil(x_23, x_2, x_15, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(x_3, x_23, x_15, x_26);
lean_dec(x_15);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_23);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_Expr_getAppNumArgsAux___main(x_29, x_30);
x_32 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_31);
x_33 = lean_mk_array(x_31, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_31, x_34);
lean_dec(x_31);
x_36 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_13, x_14, x_18, x_29, x_33, x_35, x_15, x_28);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_20);
if (x_41 == 0)
{
return x_20;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_20, 0);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_20);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_17);
if (x_45 == 0)
{
return x_17;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_17, 0);
x_47 = lean_ctor_get(x_17, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_17);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
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
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_10);
x_15 = lean_ctor_get(x_7, 5);
lean_inc(x_15);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_15, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 6);
lean_inc(x_19);
x_20 = l_List_redLength___main___rarg(x_19);
x_21 = lean_mk_empty_array_with_capacity(x_20);
lean_dec(x_20);
lean_inc(x_19);
x_22 = l_List_toArrayAux___main___rarg(x_19, x_21);
x_23 = x_22;
x_24 = lean_unsigned_to_nat(0u);
lean_inc(x_18);
lean_inc(x_6);
lean_inc(x_1);
x_25 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_6);
lean_closure_set(x_25, 2, x_9);
lean_closure_set(x_25, 3, x_11);
lean_closure_set(x_25, 4, x_18);
lean_closure_set(x_25, 5, x_19);
lean_closure_set(x_25, 6, x_24);
lean_closure_set(x_25, 7, x_23);
x_26 = x_25;
lean_inc(x_13);
x_27 = lean_apply_2(x_26, x_13, x_17);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_1);
x_30 = l_Lean_Meta_getMVarType(x_1, x_13, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_33 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = l_Lean_MetavarContext_exprDependsOn(x_18, x_31, x_2);
x_107 = lean_unbox(x_106);
lean_dec(x_106);
if (x_107 == 0)
{
x_34 = x_32;
goto block_105;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_108 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_108, 0, x_3);
x_109 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_110 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_112 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_box(0);
x_114 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_112, x_113, x_13, x_32);
lean_dec(x_13);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
return x_114;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_114, 0);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_114);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_18);
x_34 = x_32;
goto block_105;
}
block_105:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
lean_inc(x_28);
x_35 = x_28;
x_36 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_24, x_35);
x_37 = x_36;
x_38 = lean_array_push(x_37, x_2);
x_39 = 1;
x_40 = l_Lean_Meta_revert(x_1, x_38, x_39, x_13, x_34);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_array_get_size(x_28);
x_46 = lean_box(0);
x_47 = 0;
x_48 = l_Lean_Meta_introN(x_44, x_45, x_46, x_47, x_13, x_42);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l_Lean_Meta_intro1(x_52, x_47, x_13, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_80; uint8_t x_81; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_box(0);
x_59 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_28, x_51, x_28, x_24, x_58);
lean_dec(x_28);
x_80 = lean_ctor_get(x_55, 4);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_80, sizeof(void*)*1);
lean_dec(x_80);
if (x_81 == 0)
{
x_60 = x_55;
goto block_79;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_83 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_82, x_13, x_55);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_60 = x_86;
goto block_79;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
lean_inc(x_57);
x_88 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_88, 0, x_57);
x_89 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_90 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_82, x_90, x_13, x_87);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_60 = x_92;
goto block_79;
}
}
block_79:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = x_51;
x_62 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_24, x_61);
x_63 = x_62;
lean_inc(x_56);
x_64 = l_Lean_mkFVar(x_56);
lean_inc(x_57);
x_65 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_65, 0, x_57);
x_66 = lean_box(x_33);
lean_inc(x_57);
x_67 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_67, 0, x_56);
lean_closure_set(x_67, 1, x_8);
lean_closure_set(x_67, 2, x_57);
lean_closure_set(x_67, 3, x_3);
lean_closure_set(x_67, 4, x_4);
lean_closure_set(x_67, 5, x_6);
lean_closure_set(x_67, 6, x_7);
lean_closure_set(x_67, 7, x_15);
lean_closure_set(x_67, 8, x_66);
lean_closure_set(x_67, 9, x_43);
lean_closure_set(x_67, 10, x_59);
lean_closure_set(x_67, 11, x_63);
lean_closure_set(x_67, 12, x_64);
x_68 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_68, 0, x_65);
lean_closure_set(x_68, 1, x_67);
x_69 = l_Lean_Meta_getMVarDecl(x_57, x_13, x_60);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 4);
lean_inc(x_73);
lean_dec(x_70);
x_74 = l_Lean_Meta_withLocalContext___rarg(x_72, x_73, x_68, x_13, x_71);
lean_dec(x_13);
return x_74;
}
else
{
uint8_t x_75; 
lean_dec(x_68);
lean_dec(x_13);
x_75 = !lean_is_exclusive(x_69);
if (x_75 == 0)
{
return x_69;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_69, 0);
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_69);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_51);
lean_dec(x_43);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_53);
if (x_93 == 0)
{
return x_53;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_53, 0);
x_95 = lean_ctor_get(x_53, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_53);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_43);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_97 = !lean_is_exclusive(x_48);
if (x_97 == 0)
{
return x_48;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_48, 0);
x_99 = lean_ctor_get(x_48, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_48);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_101 = !lean_is_exclusive(x_40);
if (x_101 == 0)
{
return x_40;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_40, 0);
x_103 = lean_ctor_get(x_40, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_40);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_30);
if (x_119 == 0)
{
return x_30;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_30, 0);
x_121 = lean_ctor_get(x_30, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_30);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_27);
if (x_123 == 0)
{
return x_27;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_27, 0);
x_125 = lean_ctor_get(x_27, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_27);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_15);
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
x_127 = !lean_is_exclusive(x_16);
if (x_127 == 0)
{
return x_16;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_16, 0);
x_129 = lean_ctor_get(x_16, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_16);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
case 1:
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_12);
lean_dec(x_10);
x_131 = lean_ctor_get(x_7, 5);
lean_inc(x_131);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_132 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_131, x_13, x_14);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_7, 6);
lean_inc(x_135);
x_136 = l_List_redLength___main___rarg(x_135);
x_137 = lean_mk_empty_array_with_capacity(x_136);
lean_dec(x_136);
lean_inc(x_135);
x_138 = l_List_toArrayAux___main___rarg(x_135, x_137);
x_139 = x_138;
x_140 = lean_unsigned_to_nat(0u);
lean_inc(x_134);
lean_inc(x_6);
lean_inc(x_1);
x_141 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_141, 0, x_1);
lean_closure_set(x_141, 1, x_6);
lean_closure_set(x_141, 2, x_9);
lean_closure_set(x_141, 3, x_11);
lean_closure_set(x_141, 4, x_134);
lean_closure_set(x_141, 5, x_135);
lean_closure_set(x_141, 6, x_140);
lean_closure_set(x_141, 7, x_139);
x_142 = x_141;
lean_inc(x_13);
x_143 = lean_apply_2(x_142, x_13, x_133);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
lean_inc(x_1);
x_146 = l_Lean_Meta_getMVarType(x_1, x_13, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_149 == 0)
{
lean_object* x_222; uint8_t x_223; 
x_222 = l_Lean_MetavarContext_exprDependsOn(x_134, x_147, x_2);
x_223 = lean_unbox(x_222);
lean_dec(x_222);
if (x_223 == 0)
{
x_150 = x_148;
goto block_221;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
lean_dec(x_144);
lean_dec(x_131);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_224 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_224, 0, x_3);
x_225 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_226 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_224);
x_227 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_228 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_box(0);
x_230 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_228, x_229, x_13, x_148);
lean_dec(x_13);
x_231 = !lean_is_exclusive(x_230);
if (x_231 == 0)
{
return x_230;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_230, 0);
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_230);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
else
{
lean_dec(x_147);
lean_dec(x_134);
x_150 = x_148;
goto block_221;
}
block_221:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; 
lean_inc(x_144);
x_151 = x_144;
x_152 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_140, x_151);
x_153 = x_152;
x_154 = lean_array_push(x_153, x_2);
x_155 = 1;
x_156 = l_Lean_Meta_revert(x_1, x_154, x_155, x_13, x_150);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec(x_157);
x_161 = lean_array_get_size(x_144);
x_162 = lean_box(0);
x_163 = 0;
x_164 = l_Lean_Meta_introN(x_160, x_161, x_162, x_163, x_13, x_158);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_ctor_get(x_165, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_dec(x_165);
x_169 = l_Lean_Meta_intro1(x_168, x_163, x_13, x_166);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_196; uint8_t x_197; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec(x_170);
x_174 = lean_box(0);
x_175 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_144, x_167, x_144, x_140, x_174);
lean_dec(x_144);
x_196 = lean_ctor_get(x_171, 4);
lean_inc(x_196);
x_197 = lean_ctor_get_uint8(x_196, sizeof(void*)*1);
lean_dec(x_196);
if (x_197 == 0)
{
x_176 = x_171;
goto block_195;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_198 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_199 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_198, x_13, x_171);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_unbox(x_200);
lean_dec(x_200);
if (x_201 == 0)
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
lean_dec(x_199);
x_176 = x_202;
goto block_195;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_203 = lean_ctor_get(x_199, 1);
lean_inc(x_203);
lean_dec(x_199);
lean_inc(x_173);
x_204 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_204, 0, x_173);
x_205 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_206 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_204);
x_207 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_198, x_206, x_13, x_203);
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
lean_dec(x_207);
x_176 = x_208;
goto block_195;
}
}
block_195:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_177 = x_167;
x_178 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_140, x_177);
x_179 = x_178;
lean_inc(x_172);
x_180 = l_Lean_mkFVar(x_172);
lean_inc(x_173);
x_181 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_181, 0, x_173);
x_182 = lean_box(x_149);
lean_inc(x_173);
x_183 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_183, 0, x_172);
lean_closure_set(x_183, 1, x_8);
lean_closure_set(x_183, 2, x_173);
lean_closure_set(x_183, 3, x_3);
lean_closure_set(x_183, 4, x_4);
lean_closure_set(x_183, 5, x_6);
lean_closure_set(x_183, 6, x_7);
lean_closure_set(x_183, 7, x_131);
lean_closure_set(x_183, 8, x_182);
lean_closure_set(x_183, 9, x_159);
lean_closure_set(x_183, 10, x_175);
lean_closure_set(x_183, 11, x_179);
lean_closure_set(x_183, 12, x_180);
x_184 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_184, 0, x_181);
lean_closure_set(x_184, 1, x_183);
x_185 = l_Lean_Meta_getMVarDecl(x_173, x_13, x_176);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_186, 4);
lean_inc(x_189);
lean_dec(x_186);
x_190 = l_Lean_Meta_withLocalContext___rarg(x_188, x_189, x_184, x_13, x_187);
lean_dec(x_13);
return x_190;
}
else
{
uint8_t x_191; 
lean_dec(x_184);
lean_dec(x_13);
x_191 = !lean_is_exclusive(x_185);
if (x_191 == 0)
{
return x_185;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_185, 0);
x_193 = lean_ctor_get(x_185, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_185);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
}
else
{
uint8_t x_209; 
lean_dec(x_167);
lean_dec(x_159);
lean_dec(x_144);
lean_dec(x_131);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_209 = !lean_is_exclusive(x_169);
if (x_209 == 0)
{
return x_169;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_169, 0);
x_211 = lean_ctor_get(x_169, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_169);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
else
{
uint8_t x_213; 
lean_dec(x_159);
lean_dec(x_144);
lean_dec(x_131);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_213 = !lean_is_exclusive(x_164);
if (x_213 == 0)
{
return x_164;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_164, 0);
x_215 = lean_ctor_get(x_164, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_164);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
else
{
uint8_t x_217; 
lean_dec(x_144);
lean_dec(x_131);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_217 = !lean_is_exclusive(x_156);
if (x_217 == 0)
{
return x_156;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_156, 0);
x_219 = lean_ctor_get(x_156, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_156);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
}
else
{
uint8_t x_235; 
lean_dec(x_144);
lean_dec(x_134);
lean_dec(x_131);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_235 = !lean_is_exclusive(x_146);
if (x_235 == 0)
{
return x_146;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_146, 0);
x_237 = lean_ctor_get(x_146, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_146);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
else
{
uint8_t x_239; 
lean_dec(x_134);
lean_dec(x_131);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_239 = !lean_is_exclusive(x_143);
if (x_239 == 0)
{
return x_143;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_143, 0);
x_241 = lean_ctor_get(x_143, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_143);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
else
{
uint8_t x_243; 
lean_dec(x_131);
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
x_243 = !lean_is_exclusive(x_132);
if (x_243 == 0)
{
return x_132;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_132, 0);
x_245 = lean_ctor_get(x_132, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_132);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
case 2:
{
lean_object* x_247; lean_object* x_248; 
lean_dec(x_12);
lean_dec(x_10);
x_247 = lean_ctor_get(x_7, 5);
lean_inc(x_247);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_248 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_247, x_13, x_14);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
x_251 = lean_ctor_get(x_7, 6);
lean_inc(x_251);
x_252 = l_List_redLength___main___rarg(x_251);
x_253 = lean_mk_empty_array_with_capacity(x_252);
lean_dec(x_252);
lean_inc(x_251);
x_254 = l_List_toArrayAux___main___rarg(x_251, x_253);
x_255 = x_254;
x_256 = lean_unsigned_to_nat(0u);
lean_inc(x_250);
lean_inc(x_6);
lean_inc(x_1);
x_257 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_257, 0, x_1);
lean_closure_set(x_257, 1, x_6);
lean_closure_set(x_257, 2, x_9);
lean_closure_set(x_257, 3, x_11);
lean_closure_set(x_257, 4, x_250);
lean_closure_set(x_257, 5, x_251);
lean_closure_set(x_257, 6, x_256);
lean_closure_set(x_257, 7, x_255);
x_258 = x_257;
lean_inc(x_13);
x_259 = lean_apply_2(x_258, x_13, x_249);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
lean_inc(x_1);
x_262 = l_Lean_Meta_getMVarType(x_1, x_13, x_261);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_265 == 0)
{
lean_object* x_338; uint8_t x_339; 
x_338 = l_Lean_MetavarContext_exprDependsOn(x_250, x_263, x_2);
x_339 = lean_unbox(x_338);
lean_dec(x_338);
if (x_339 == 0)
{
x_266 = x_264;
goto block_337;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
lean_dec(x_260);
lean_dec(x_247);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_340 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_340, 0, x_3);
x_341 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_342 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_340);
x_343 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_344 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
x_345 = lean_box(0);
x_346 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_344, x_345, x_13, x_264);
lean_dec(x_13);
x_347 = !lean_is_exclusive(x_346);
if (x_347 == 0)
{
return x_346;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_346, 0);
x_349 = lean_ctor_get(x_346, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_346);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
else
{
lean_dec(x_263);
lean_dec(x_250);
x_266 = x_264;
goto block_337;
}
block_337:
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; 
lean_inc(x_260);
x_267 = x_260;
x_268 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_256, x_267);
x_269 = x_268;
x_270 = lean_array_push(x_269, x_2);
x_271 = 1;
x_272 = l_Lean_Meta_revert(x_1, x_270, x_271, x_13, x_266);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
x_275 = lean_ctor_get(x_273, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_273, 1);
lean_inc(x_276);
lean_dec(x_273);
x_277 = lean_array_get_size(x_260);
x_278 = lean_box(0);
x_279 = 0;
x_280 = l_Lean_Meta_introN(x_276, x_277, x_278, x_279, x_13, x_274);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_283 = lean_ctor_get(x_281, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_281, 1);
lean_inc(x_284);
lean_dec(x_281);
x_285 = l_Lean_Meta_intro1(x_284, x_279, x_13, x_282);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_312; uint8_t x_313; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_ctor_get(x_286, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_286, 1);
lean_inc(x_289);
lean_dec(x_286);
x_290 = lean_box(0);
x_291 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_260, x_283, x_260, x_256, x_290);
lean_dec(x_260);
x_312 = lean_ctor_get(x_287, 4);
lean_inc(x_312);
x_313 = lean_ctor_get_uint8(x_312, sizeof(void*)*1);
lean_dec(x_312);
if (x_313 == 0)
{
x_292 = x_287;
goto block_311;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_314 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_315 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_314, x_13, x_287);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_unbox(x_316);
lean_dec(x_316);
if (x_317 == 0)
{
lean_object* x_318; 
x_318 = lean_ctor_get(x_315, 1);
lean_inc(x_318);
lean_dec(x_315);
x_292 = x_318;
goto block_311;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_319 = lean_ctor_get(x_315, 1);
lean_inc(x_319);
lean_dec(x_315);
lean_inc(x_289);
x_320 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_320, 0, x_289);
x_321 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_322 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_320);
x_323 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_314, x_322, x_13, x_319);
x_324 = lean_ctor_get(x_323, 1);
lean_inc(x_324);
lean_dec(x_323);
x_292 = x_324;
goto block_311;
}
}
block_311:
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_293 = x_283;
x_294 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_256, x_293);
x_295 = x_294;
lean_inc(x_288);
x_296 = l_Lean_mkFVar(x_288);
lean_inc(x_289);
x_297 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_297, 0, x_289);
x_298 = lean_box(x_265);
lean_inc(x_289);
x_299 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_299, 0, x_288);
lean_closure_set(x_299, 1, x_8);
lean_closure_set(x_299, 2, x_289);
lean_closure_set(x_299, 3, x_3);
lean_closure_set(x_299, 4, x_4);
lean_closure_set(x_299, 5, x_6);
lean_closure_set(x_299, 6, x_7);
lean_closure_set(x_299, 7, x_247);
lean_closure_set(x_299, 8, x_298);
lean_closure_set(x_299, 9, x_275);
lean_closure_set(x_299, 10, x_291);
lean_closure_set(x_299, 11, x_295);
lean_closure_set(x_299, 12, x_296);
x_300 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_300, 0, x_297);
lean_closure_set(x_300, 1, x_299);
x_301 = l_Lean_Meta_getMVarDecl(x_289, x_13, x_292);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_302, 4);
lean_inc(x_305);
lean_dec(x_302);
x_306 = l_Lean_Meta_withLocalContext___rarg(x_304, x_305, x_300, x_13, x_303);
lean_dec(x_13);
return x_306;
}
else
{
uint8_t x_307; 
lean_dec(x_300);
lean_dec(x_13);
x_307 = !lean_is_exclusive(x_301);
if (x_307 == 0)
{
return x_301;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_301, 0);
x_309 = lean_ctor_get(x_301, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_301);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
}
else
{
uint8_t x_325; 
lean_dec(x_283);
lean_dec(x_275);
lean_dec(x_260);
lean_dec(x_247);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_325 = !lean_is_exclusive(x_285);
if (x_325 == 0)
{
return x_285;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_285, 0);
x_327 = lean_ctor_get(x_285, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_285);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
else
{
uint8_t x_329; 
lean_dec(x_275);
lean_dec(x_260);
lean_dec(x_247);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_329 = !lean_is_exclusive(x_280);
if (x_329 == 0)
{
return x_280;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_280, 0);
x_331 = lean_ctor_get(x_280, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_280);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
return x_332;
}
}
}
else
{
uint8_t x_333; 
lean_dec(x_260);
lean_dec(x_247);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_333 = !lean_is_exclusive(x_272);
if (x_333 == 0)
{
return x_272;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_272, 0);
x_335 = lean_ctor_get(x_272, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_272);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
}
}
else
{
uint8_t x_351; 
lean_dec(x_260);
lean_dec(x_250);
lean_dec(x_247);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_351 = !lean_is_exclusive(x_262);
if (x_351 == 0)
{
return x_262;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_262, 0);
x_353 = lean_ctor_get(x_262, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_262);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
}
}
else
{
uint8_t x_355; 
lean_dec(x_250);
lean_dec(x_247);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_355 = !lean_is_exclusive(x_259);
if (x_355 == 0)
{
return x_259;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_259, 0);
x_357 = lean_ctor_get(x_259, 1);
lean_inc(x_357);
lean_inc(x_356);
lean_dec(x_259);
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
lean_dec(x_247);
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
x_359 = !lean_is_exclusive(x_248);
if (x_359 == 0)
{
return x_248;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_248, 0);
x_361 = lean_ctor_get(x_248, 1);
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_248);
x_362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_361);
return x_362;
}
}
}
case 3:
{
lean_object* x_363; lean_object* x_364; 
lean_dec(x_12);
lean_dec(x_10);
x_363 = lean_ctor_get(x_7, 5);
lean_inc(x_363);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_364 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_363, x_13, x_14);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
lean_dec(x_364);
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_7, 6);
lean_inc(x_367);
x_368 = l_List_redLength___main___rarg(x_367);
x_369 = lean_mk_empty_array_with_capacity(x_368);
lean_dec(x_368);
lean_inc(x_367);
x_370 = l_List_toArrayAux___main___rarg(x_367, x_369);
x_371 = x_370;
x_372 = lean_unsigned_to_nat(0u);
lean_inc(x_366);
lean_inc(x_6);
lean_inc(x_1);
x_373 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_373, 0, x_1);
lean_closure_set(x_373, 1, x_6);
lean_closure_set(x_373, 2, x_9);
lean_closure_set(x_373, 3, x_11);
lean_closure_set(x_373, 4, x_366);
lean_closure_set(x_373, 5, x_367);
lean_closure_set(x_373, 6, x_372);
lean_closure_set(x_373, 7, x_371);
x_374 = x_373;
lean_inc(x_13);
x_375 = lean_apply_2(x_374, x_13, x_365);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec(x_375);
lean_inc(x_1);
x_378 = l_Lean_Meta_getMVarType(x_1, x_13, x_377);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; uint8_t x_381; lean_object* x_382; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_381 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_381 == 0)
{
lean_object* x_454; uint8_t x_455; 
x_454 = l_Lean_MetavarContext_exprDependsOn(x_366, x_379, x_2);
x_455 = lean_unbox(x_454);
lean_dec(x_454);
if (x_455 == 0)
{
x_382 = x_380;
goto block_453;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; 
lean_dec(x_376);
lean_dec(x_363);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_456 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_456, 0, x_3);
x_457 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_458 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_456);
x_459 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_460 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_460, 0, x_458);
lean_ctor_set(x_460, 1, x_459);
x_461 = lean_box(0);
x_462 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_460, x_461, x_13, x_380);
lean_dec(x_13);
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
lean_dec(x_379);
lean_dec(x_366);
x_382 = x_380;
goto block_453;
}
block_453:
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; 
lean_inc(x_376);
x_383 = x_376;
x_384 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_372, x_383);
x_385 = x_384;
x_386 = lean_array_push(x_385, x_2);
x_387 = 1;
x_388 = l_Lean_Meta_revert(x_1, x_386, x_387, x_13, x_382);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; lean_object* x_396; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = lean_ctor_get(x_389, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_389, 1);
lean_inc(x_392);
lean_dec(x_389);
x_393 = lean_array_get_size(x_376);
x_394 = lean_box(0);
x_395 = 0;
x_396 = l_Lean_Meta_introN(x_392, x_393, x_394, x_395, x_13, x_390);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_399 = lean_ctor_get(x_397, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_397, 1);
lean_inc(x_400);
lean_dec(x_397);
x_401 = l_Lean_Meta_intro1(x_400, x_395, x_13, x_398);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_428; uint8_t x_429; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = lean_ctor_get(x_402, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_402, 1);
lean_inc(x_405);
lean_dec(x_402);
x_406 = lean_box(0);
x_407 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_376, x_399, x_376, x_372, x_406);
lean_dec(x_376);
x_428 = lean_ctor_get(x_403, 4);
lean_inc(x_428);
x_429 = lean_ctor_get_uint8(x_428, sizeof(void*)*1);
lean_dec(x_428);
if (x_429 == 0)
{
x_408 = x_403;
goto block_427;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; 
x_430 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_431 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_430, x_13, x_403);
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_unbox(x_432);
lean_dec(x_432);
if (x_433 == 0)
{
lean_object* x_434; 
x_434 = lean_ctor_get(x_431, 1);
lean_inc(x_434);
lean_dec(x_431);
x_408 = x_434;
goto block_427;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_435 = lean_ctor_get(x_431, 1);
lean_inc(x_435);
lean_dec(x_431);
lean_inc(x_405);
x_436 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_436, 0, x_405);
x_437 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_438 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_436);
x_439 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_430, x_438, x_13, x_435);
x_440 = lean_ctor_get(x_439, 1);
lean_inc(x_440);
lean_dec(x_439);
x_408 = x_440;
goto block_427;
}
}
block_427:
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_409 = x_399;
x_410 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_372, x_409);
x_411 = x_410;
lean_inc(x_404);
x_412 = l_Lean_mkFVar(x_404);
lean_inc(x_405);
x_413 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_413, 0, x_405);
x_414 = lean_box(x_381);
lean_inc(x_405);
x_415 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_415, 0, x_404);
lean_closure_set(x_415, 1, x_8);
lean_closure_set(x_415, 2, x_405);
lean_closure_set(x_415, 3, x_3);
lean_closure_set(x_415, 4, x_4);
lean_closure_set(x_415, 5, x_6);
lean_closure_set(x_415, 6, x_7);
lean_closure_set(x_415, 7, x_363);
lean_closure_set(x_415, 8, x_414);
lean_closure_set(x_415, 9, x_391);
lean_closure_set(x_415, 10, x_407);
lean_closure_set(x_415, 11, x_411);
lean_closure_set(x_415, 12, x_412);
x_416 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_416, 0, x_413);
lean_closure_set(x_416, 1, x_415);
x_417 = l_Lean_Meta_getMVarDecl(x_405, x_13, x_408);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
x_420 = lean_ctor_get(x_418, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_418, 4);
lean_inc(x_421);
lean_dec(x_418);
x_422 = l_Lean_Meta_withLocalContext___rarg(x_420, x_421, x_416, x_13, x_419);
lean_dec(x_13);
return x_422;
}
else
{
uint8_t x_423; 
lean_dec(x_416);
lean_dec(x_13);
x_423 = !lean_is_exclusive(x_417);
if (x_423 == 0)
{
return x_417;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_417, 0);
x_425 = lean_ctor_get(x_417, 1);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_417);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
}
}
}
else
{
uint8_t x_441; 
lean_dec(x_399);
lean_dec(x_391);
lean_dec(x_376);
lean_dec(x_363);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_441 = !lean_is_exclusive(x_401);
if (x_441 == 0)
{
return x_401;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_442 = lean_ctor_get(x_401, 0);
x_443 = lean_ctor_get(x_401, 1);
lean_inc(x_443);
lean_inc(x_442);
lean_dec(x_401);
x_444 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_444, 0, x_442);
lean_ctor_set(x_444, 1, x_443);
return x_444;
}
}
}
else
{
uint8_t x_445; 
lean_dec(x_391);
lean_dec(x_376);
lean_dec(x_363);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_445 = !lean_is_exclusive(x_396);
if (x_445 == 0)
{
return x_396;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_446 = lean_ctor_get(x_396, 0);
x_447 = lean_ctor_get(x_396, 1);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_396);
x_448 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_448, 0, x_446);
lean_ctor_set(x_448, 1, x_447);
return x_448;
}
}
}
else
{
uint8_t x_449; 
lean_dec(x_376);
lean_dec(x_363);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_449 = !lean_is_exclusive(x_388);
if (x_449 == 0)
{
return x_388;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_450 = lean_ctor_get(x_388, 0);
x_451 = lean_ctor_get(x_388, 1);
lean_inc(x_451);
lean_inc(x_450);
lean_dec(x_388);
x_452 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_452, 0, x_450);
lean_ctor_set(x_452, 1, x_451);
return x_452;
}
}
}
}
else
{
uint8_t x_467; 
lean_dec(x_376);
lean_dec(x_366);
lean_dec(x_363);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_467 = !lean_is_exclusive(x_378);
if (x_467 == 0)
{
return x_378;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_468 = lean_ctor_get(x_378, 0);
x_469 = lean_ctor_get(x_378, 1);
lean_inc(x_469);
lean_inc(x_468);
lean_dec(x_378);
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
lean_dec(x_366);
lean_dec(x_363);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_471 = !lean_is_exclusive(x_375);
if (x_471 == 0)
{
return x_375;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_375, 0);
x_473 = lean_ctor_get(x_375, 1);
lean_inc(x_473);
lean_inc(x_472);
lean_dec(x_375);
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
lean_dec(x_363);
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
x_475 = !lean_is_exclusive(x_364);
if (x_475 == 0)
{
return x_364;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_364, 0);
x_477 = lean_ctor_get(x_364, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_364);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
}
}
case 4:
{
lean_object* x_479; lean_object* x_480; 
lean_dec(x_12);
lean_dec(x_10);
x_479 = lean_ctor_get(x_7, 5);
lean_inc(x_479);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_480 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_479, x_13, x_14);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_481 = lean_ctor_get(x_480, 1);
lean_inc(x_481);
lean_dec(x_480);
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
x_483 = lean_ctor_get(x_7, 6);
lean_inc(x_483);
x_484 = l_List_redLength___main___rarg(x_483);
x_485 = lean_mk_empty_array_with_capacity(x_484);
lean_dec(x_484);
lean_inc(x_483);
x_486 = l_List_toArrayAux___main___rarg(x_483, x_485);
x_487 = x_486;
x_488 = lean_unsigned_to_nat(0u);
lean_inc(x_482);
lean_inc(x_6);
lean_inc(x_1);
x_489 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_489, 0, x_1);
lean_closure_set(x_489, 1, x_6);
lean_closure_set(x_489, 2, x_9);
lean_closure_set(x_489, 3, x_11);
lean_closure_set(x_489, 4, x_482);
lean_closure_set(x_489, 5, x_483);
lean_closure_set(x_489, 6, x_488);
lean_closure_set(x_489, 7, x_487);
x_490 = x_489;
lean_inc(x_13);
x_491 = lean_apply_2(x_490, x_13, x_481);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_491, 1);
lean_inc(x_493);
lean_dec(x_491);
lean_inc(x_1);
x_494 = l_Lean_Meta_getMVarType(x_1, x_13, x_493);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; uint8_t x_497; lean_object* x_498; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
x_497 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_497 == 0)
{
lean_object* x_570; uint8_t x_571; 
x_570 = l_Lean_MetavarContext_exprDependsOn(x_482, x_495, x_2);
x_571 = lean_unbox(x_570);
lean_dec(x_570);
if (x_571 == 0)
{
x_498 = x_496;
goto block_569;
}
else
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; uint8_t x_579; 
lean_dec(x_492);
lean_dec(x_479);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_572 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_572, 0, x_3);
x_573 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_574 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_572);
x_575 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_576 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_576, 0, x_574);
lean_ctor_set(x_576, 1, x_575);
x_577 = lean_box(0);
x_578 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_576, x_577, x_13, x_496);
lean_dec(x_13);
x_579 = !lean_is_exclusive(x_578);
if (x_579 == 0)
{
return x_578;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_580 = lean_ctor_get(x_578, 0);
x_581 = lean_ctor_get(x_578, 1);
lean_inc(x_581);
lean_inc(x_580);
lean_dec(x_578);
x_582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_582, 0, x_580);
lean_ctor_set(x_582, 1, x_581);
return x_582;
}
}
}
else
{
lean_dec(x_495);
lean_dec(x_482);
x_498 = x_496;
goto block_569;
}
block_569:
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; lean_object* x_504; 
lean_inc(x_492);
x_499 = x_492;
x_500 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_488, x_499);
x_501 = x_500;
x_502 = lean_array_push(x_501, x_2);
x_503 = 1;
x_504 = l_Lean_Meta_revert(x_1, x_502, x_503, x_13, x_498);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; uint8_t x_511; lean_object* x_512; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
lean_dec(x_504);
x_507 = lean_ctor_get(x_505, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_505, 1);
lean_inc(x_508);
lean_dec(x_505);
x_509 = lean_array_get_size(x_492);
x_510 = lean_box(0);
x_511 = 0;
x_512 = l_Lean_Meta_introN(x_508, x_509, x_510, x_511, x_13, x_506);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_512, 1);
lean_inc(x_514);
lean_dec(x_512);
x_515 = lean_ctor_get(x_513, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_513, 1);
lean_inc(x_516);
lean_dec(x_513);
x_517 = l_Lean_Meta_intro1(x_516, x_511, x_13, x_514);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_544; uint8_t x_545; 
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
x_519 = lean_ctor_get(x_517, 1);
lean_inc(x_519);
lean_dec(x_517);
x_520 = lean_ctor_get(x_518, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_518, 1);
lean_inc(x_521);
lean_dec(x_518);
x_522 = lean_box(0);
x_523 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_492, x_515, x_492, x_488, x_522);
lean_dec(x_492);
x_544 = lean_ctor_get(x_519, 4);
lean_inc(x_544);
x_545 = lean_ctor_get_uint8(x_544, sizeof(void*)*1);
lean_dec(x_544);
if (x_545 == 0)
{
x_524 = x_519;
goto block_543;
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; uint8_t x_549; 
x_546 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_547 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_546, x_13, x_519);
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
x_549 = lean_unbox(x_548);
lean_dec(x_548);
if (x_549 == 0)
{
lean_object* x_550; 
x_550 = lean_ctor_get(x_547, 1);
lean_inc(x_550);
lean_dec(x_547);
x_524 = x_550;
goto block_543;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_551 = lean_ctor_get(x_547, 1);
lean_inc(x_551);
lean_dec(x_547);
lean_inc(x_521);
x_552 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_552, 0, x_521);
x_553 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_554 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_554, 0, x_553);
lean_ctor_set(x_554, 1, x_552);
x_555 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_546, x_554, x_13, x_551);
x_556 = lean_ctor_get(x_555, 1);
lean_inc(x_556);
lean_dec(x_555);
x_524 = x_556;
goto block_543;
}
}
block_543:
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_525 = x_515;
x_526 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_488, x_525);
x_527 = x_526;
lean_inc(x_520);
x_528 = l_Lean_mkFVar(x_520);
lean_inc(x_521);
x_529 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_529, 0, x_521);
x_530 = lean_box(x_497);
lean_inc(x_521);
x_531 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_531, 0, x_520);
lean_closure_set(x_531, 1, x_8);
lean_closure_set(x_531, 2, x_521);
lean_closure_set(x_531, 3, x_3);
lean_closure_set(x_531, 4, x_4);
lean_closure_set(x_531, 5, x_6);
lean_closure_set(x_531, 6, x_7);
lean_closure_set(x_531, 7, x_479);
lean_closure_set(x_531, 8, x_530);
lean_closure_set(x_531, 9, x_507);
lean_closure_set(x_531, 10, x_523);
lean_closure_set(x_531, 11, x_527);
lean_closure_set(x_531, 12, x_528);
x_532 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_532, 0, x_529);
lean_closure_set(x_532, 1, x_531);
x_533 = l_Lean_Meta_getMVarDecl(x_521, x_13, x_524);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
lean_dec(x_533);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
x_537 = lean_ctor_get(x_534, 4);
lean_inc(x_537);
lean_dec(x_534);
x_538 = l_Lean_Meta_withLocalContext___rarg(x_536, x_537, x_532, x_13, x_535);
lean_dec(x_13);
return x_538;
}
else
{
uint8_t x_539; 
lean_dec(x_532);
lean_dec(x_13);
x_539 = !lean_is_exclusive(x_533);
if (x_539 == 0)
{
return x_533;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_540 = lean_ctor_get(x_533, 0);
x_541 = lean_ctor_get(x_533, 1);
lean_inc(x_541);
lean_inc(x_540);
lean_dec(x_533);
x_542 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_542, 0, x_540);
lean_ctor_set(x_542, 1, x_541);
return x_542;
}
}
}
}
else
{
uint8_t x_557; 
lean_dec(x_515);
lean_dec(x_507);
lean_dec(x_492);
lean_dec(x_479);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_557 = !lean_is_exclusive(x_517);
if (x_557 == 0)
{
return x_517;
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_558 = lean_ctor_get(x_517, 0);
x_559 = lean_ctor_get(x_517, 1);
lean_inc(x_559);
lean_inc(x_558);
lean_dec(x_517);
x_560 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_560, 0, x_558);
lean_ctor_set(x_560, 1, x_559);
return x_560;
}
}
}
else
{
uint8_t x_561; 
lean_dec(x_507);
lean_dec(x_492);
lean_dec(x_479);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_561 = !lean_is_exclusive(x_512);
if (x_561 == 0)
{
return x_512;
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_562 = lean_ctor_get(x_512, 0);
x_563 = lean_ctor_get(x_512, 1);
lean_inc(x_563);
lean_inc(x_562);
lean_dec(x_512);
x_564 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_564, 0, x_562);
lean_ctor_set(x_564, 1, x_563);
return x_564;
}
}
}
else
{
uint8_t x_565; 
lean_dec(x_492);
lean_dec(x_479);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_565 = !lean_is_exclusive(x_504);
if (x_565 == 0)
{
return x_504;
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; 
x_566 = lean_ctor_get(x_504, 0);
x_567 = lean_ctor_get(x_504, 1);
lean_inc(x_567);
lean_inc(x_566);
lean_dec(x_504);
x_568 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_568, 0, x_566);
lean_ctor_set(x_568, 1, x_567);
return x_568;
}
}
}
}
else
{
uint8_t x_583; 
lean_dec(x_492);
lean_dec(x_482);
lean_dec(x_479);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_583 = !lean_is_exclusive(x_494);
if (x_583 == 0)
{
return x_494;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_494, 0);
x_585 = lean_ctor_get(x_494, 1);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_494);
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
lean_dec(x_482);
lean_dec(x_479);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_587 = !lean_is_exclusive(x_491);
if (x_587 == 0)
{
return x_491;
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_588 = lean_ctor_get(x_491, 0);
x_589 = lean_ctor_get(x_491, 1);
lean_inc(x_589);
lean_inc(x_588);
lean_dec(x_491);
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
lean_dec(x_479);
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
x_591 = !lean_is_exclusive(x_480);
if (x_591 == 0)
{
return x_480;
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_592 = lean_ctor_get(x_480, 0);
x_593 = lean_ctor_get(x_480, 1);
lean_inc(x_593);
lean_inc(x_592);
lean_dec(x_480);
x_594 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_594, 0, x_592);
lean_ctor_set(x_594, 1, x_593);
return x_594;
}
}
}
case 5:
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_595 = lean_ctor_get(x_10, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_10, 1);
lean_inc(x_596);
lean_dec(x_10);
x_597 = lean_array_set(x_11, x_12, x_596);
x_598 = lean_unsigned_to_nat(1u);
x_599 = lean_nat_sub(x_12, x_598);
lean_dec(x_12);
x_10 = x_595;
x_11 = x_597;
x_12 = x_599;
goto _start;
}
case 6:
{
lean_object* x_601; lean_object* x_602; 
lean_dec(x_12);
lean_dec(x_10);
x_601 = lean_ctor_get(x_7, 5);
lean_inc(x_601);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_602 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_601, x_13, x_14);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_603 = lean_ctor_get(x_602, 1);
lean_inc(x_603);
lean_dec(x_602);
x_604 = lean_ctor_get(x_603, 1);
lean_inc(x_604);
x_605 = lean_ctor_get(x_7, 6);
lean_inc(x_605);
x_606 = l_List_redLength___main___rarg(x_605);
x_607 = lean_mk_empty_array_with_capacity(x_606);
lean_dec(x_606);
lean_inc(x_605);
x_608 = l_List_toArrayAux___main___rarg(x_605, x_607);
x_609 = x_608;
x_610 = lean_unsigned_to_nat(0u);
lean_inc(x_604);
lean_inc(x_6);
lean_inc(x_1);
x_611 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_611, 0, x_1);
lean_closure_set(x_611, 1, x_6);
lean_closure_set(x_611, 2, x_9);
lean_closure_set(x_611, 3, x_11);
lean_closure_set(x_611, 4, x_604);
lean_closure_set(x_611, 5, x_605);
lean_closure_set(x_611, 6, x_610);
lean_closure_set(x_611, 7, x_609);
x_612 = x_611;
lean_inc(x_13);
x_613 = lean_apply_2(x_612, x_13, x_603);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_613, 1);
lean_inc(x_615);
lean_dec(x_613);
lean_inc(x_1);
x_616 = l_Lean_Meta_getMVarType(x_1, x_13, x_615);
if (lean_obj_tag(x_616) == 0)
{
lean_object* x_617; lean_object* x_618; uint8_t x_619; lean_object* x_620; 
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
lean_dec(x_616);
x_619 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_619 == 0)
{
lean_object* x_692; uint8_t x_693; 
x_692 = l_Lean_MetavarContext_exprDependsOn(x_604, x_617, x_2);
x_693 = lean_unbox(x_692);
lean_dec(x_692);
if (x_693 == 0)
{
x_620 = x_618;
goto block_691;
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; uint8_t x_701; 
lean_dec(x_614);
lean_dec(x_601);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_694 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_694, 0, x_3);
x_695 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_696 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_696, 0, x_695);
lean_ctor_set(x_696, 1, x_694);
x_697 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_698 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_698, 0, x_696);
lean_ctor_set(x_698, 1, x_697);
x_699 = lean_box(0);
x_700 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_698, x_699, x_13, x_618);
lean_dec(x_13);
x_701 = !lean_is_exclusive(x_700);
if (x_701 == 0)
{
return x_700;
}
else
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_702 = lean_ctor_get(x_700, 0);
x_703 = lean_ctor_get(x_700, 1);
lean_inc(x_703);
lean_inc(x_702);
lean_dec(x_700);
x_704 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_704, 0, x_702);
lean_ctor_set(x_704, 1, x_703);
return x_704;
}
}
}
else
{
lean_dec(x_617);
lean_dec(x_604);
x_620 = x_618;
goto block_691;
}
block_691:
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; uint8_t x_625; lean_object* x_626; 
lean_inc(x_614);
x_621 = x_614;
x_622 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_610, x_621);
x_623 = x_622;
x_624 = lean_array_push(x_623, x_2);
x_625 = 1;
x_626 = l_Lean_Meta_revert(x_1, x_624, x_625, x_13, x_620);
if (lean_obj_tag(x_626) == 0)
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; uint8_t x_633; lean_object* x_634; 
x_627 = lean_ctor_get(x_626, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_626, 1);
lean_inc(x_628);
lean_dec(x_626);
x_629 = lean_ctor_get(x_627, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_627, 1);
lean_inc(x_630);
lean_dec(x_627);
x_631 = lean_array_get_size(x_614);
x_632 = lean_box(0);
x_633 = 0;
x_634 = l_Lean_Meta_introN(x_630, x_631, x_632, x_633, x_13, x_628);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_634, 1);
lean_inc(x_636);
lean_dec(x_634);
x_637 = lean_ctor_get(x_635, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_635, 1);
lean_inc(x_638);
lean_dec(x_635);
x_639 = l_Lean_Meta_intro1(x_638, x_633, x_13, x_636);
if (lean_obj_tag(x_639) == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_666; uint8_t x_667; 
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_639, 1);
lean_inc(x_641);
lean_dec(x_639);
x_642 = lean_ctor_get(x_640, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_640, 1);
lean_inc(x_643);
lean_dec(x_640);
x_644 = lean_box(0);
x_645 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_614, x_637, x_614, x_610, x_644);
lean_dec(x_614);
x_666 = lean_ctor_get(x_641, 4);
lean_inc(x_666);
x_667 = lean_ctor_get_uint8(x_666, sizeof(void*)*1);
lean_dec(x_666);
if (x_667 == 0)
{
x_646 = x_641;
goto block_665;
}
else
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; uint8_t x_671; 
x_668 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_669 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_668, x_13, x_641);
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
x_671 = lean_unbox(x_670);
lean_dec(x_670);
if (x_671 == 0)
{
lean_object* x_672; 
x_672 = lean_ctor_get(x_669, 1);
lean_inc(x_672);
lean_dec(x_669);
x_646 = x_672;
goto block_665;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_673 = lean_ctor_get(x_669, 1);
lean_inc(x_673);
lean_dec(x_669);
lean_inc(x_643);
x_674 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_674, 0, x_643);
x_675 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_676 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_676, 0, x_675);
lean_ctor_set(x_676, 1, x_674);
x_677 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_668, x_676, x_13, x_673);
x_678 = lean_ctor_get(x_677, 1);
lean_inc(x_678);
lean_dec(x_677);
x_646 = x_678;
goto block_665;
}
}
block_665:
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_647 = x_637;
x_648 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_610, x_647);
x_649 = x_648;
lean_inc(x_642);
x_650 = l_Lean_mkFVar(x_642);
lean_inc(x_643);
x_651 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_651, 0, x_643);
x_652 = lean_box(x_619);
lean_inc(x_643);
x_653 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_653, 0, x_642);
lean_closure_set(x_653, 1, x_8);
lean_closure_set(x_653, 2, x_643);
lean_closure_set(x_653, 3, x_3);
lean_closure_set(x_653, 4, x_4);
lean_closure_set(x_653, 5, x_6);
lean_closure_set(x_653, 6, x_7);
lean_closure_set(x_653, 7, x_601);
lean_closure_set(x_653, 8, x_652);
lean_closure_set(x_653, 9, x_629);
lean_closure_set(x_653, 10, x_645);
lean_closure_set(x_653, 11, x_649);
lean_closure_set(x_653, 12, x_650);
x_654 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_654, 0, x_651);
lean_closure_set(x_654, 1, x_653);
x_655 = l_Lean_Meta_getMVarDecl(x_643, x_13, x_646);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
lean_dec(x_655);
x_658 = lean_ctor_get(x_656, 1);
lean_inc(x_658);
x_659 = lean_ctor_get(x_656, 4);
lean_inc(x_659);
lean_dec(x_656);
x_660 = l_Lean_Meta_withLocalContext___rarg(x_658, x_659, x_654, x_13, x_657);
lean_dec(x_13);
return x_660;
}
else
{
uint8_t x_661; 
lean_dec(x_654);
lean_dec(x_13);
x_661 = !lean_is_exclusive(x_655);
if (x_661 == 0)
{
return x_655;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_662 = lean_ctor_get(x_655, 0);
x_663 = lean_ctor_get(x_655, 1);
lean_inc(x_663);
lean_inc(x_662);
lean_dec(x_655);
x_664 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_664, 0, x_662);
lean_ctor_set(x_664, 1, x_663);
return x_664;
}
}
}
}
else
{
uint8_t x_679; 
lean_dec(x_637);
lean_dec(x_629);
lean_dec(x_614);
lean_dec(x_601);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_679 = !lean_is_exclusive(x_639);
if (x_679 == 0)
{
return x_639;
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_680 = lean_ctor_get(x_639, 0);
x_681 = lean_ctor_get(x_639, 1);
lean_inc(x_681);
lean_inc(x_680);
lean_dec(x_639);
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
lean_dec(x_629);
lean_dec(x_614);
lean_dec(x_601);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_683 = !lean_is_exclusive(x_634);
if (x_683 == 0)
{
return x_634;
}
else
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_684 = lean_ctor_get(x_634, 0);
x_685 = lean_ctor_get(x_634, 1);
lean_inc(x_685);
lean_inc(x_684);
lean_dec(x_634);
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
lean_dec(x_614);
lean_dec(x_601);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_687 = !lean_is_exclusive(x_626);
if (x_687 == 0)
{
return x_626;
}
else
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_688 = lean_ctor_get(x_626, 0);
x_689 = lean_ctor_get(x_626, 1);
lean_inc(x_689);
lean_inc(x_688);
lean_dec(x_626);
x_690 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_690, 0, x_688);
lean_ctor_set(x_690, 1, x_689);
return x_690;
}
}
}
}
else
{
uint8_t x_705; 
lean_dec(x_614);
lean_dec(x_604);
lean_dec(x_601);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_705 = !lean_is_exclusive(x_616);
if (x_705 == 0)
{
return x_616;
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_706 = lean_ctor_get(x_616, 0);
x_707 = lean_ctor_get(x_616, 1);
lean_inc(x_707);
lean_inc(x_706);
lean_dec(x_616);
x_708 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_708, 0, x_706);
lean_ctor_set(x_708, 1, x_707);
return x_708;
}
}
}
else
{
uint8_t x_709; 
lean_dec(x_604);
lean_dec(x_601);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_709 = !lean_is_exclusive(x_613);
if (x_709 == 0)
{
return x_613;
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; 
x_710 = lean_ctor_get(x_613, 0);
x_711 = lean_ctor_get(x_613, 1);
lean_inc(x_711);
lean_inc(x_710);
lean_dec(x_613);
x_712 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_712, 0, x_710);
lean_ctor_set(x_712, 1, x_711);
return x_712;
}
}
}
else
{
uint8_t x_713; 
lean_dec(x_601);
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
x_713 = !lean_is_exclusive(x_602);
if (x_713 == 0)
{
return x_602;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_714 = lean_ctor_get(x_602, 0);
x_715 = lean_ctor_get(x_602, 1);
lean_inc(x_715);
lean_inc(x_714);
lean_dec(x_602);
x_716 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_716, 0, x_714);
lean_ctor_set(x_716, 1, x_715);
return x_716;
}
}
}
case 7:
{
lean_object* x_717; lean_object* x_718; 
lean_dec(x_12);
lean_dec(x_10);
x_717 = lean_ctor_get(x_7, 5);
lean_inc(x_717);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_718 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_717, x_13, x_14);
if (lean_obj_tag(x_718) == 0)
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
x_719 = lean_ctor_get(x_718, 1);
lean_inc(x_719);
lean_dec(x_718);
x_720 = lean_ctor_get(x_719, 1);
lean_inc(x_720);
x_721 = lean_ctor_get(x_7, 6);
lean_inc(x_721);
x_722 = l_List_redLength___main___rarg(x_721);
x_723 = lean_mk_empty_array_with_capacity(x_722);
lean_dec(x_722);
lean_inc(x_721);
x_724 = l_List_toArrayAux___main___rarg(x_721, x_723);
x_725 = x_724;
x_726 = lean_unsigned_to_nat(0u);
lean_inc(x_720);
lean_inc(x_6);
lean_inc(x_1);
x_727 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_727, 0, x_1);
lean_closure_set(x_727, 1, x_6);
lean_closure_set(x_727, 2, x_9);
lean_closure_set(x_727, 3, x_11);
lean_closure_set(x_727, 4, x_720);
lean_closure_set(x_727, 5, x_721);
lean_closure_set(x_727, 6, x_726);
lean_closure_set(x_727, 7, x_725);
x_728 = x_727;
lean_inc(x_13);
x_729 = lean_apply_2(x_728, x_13, x_719);
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_729, 1);
lean_inc(x_731);
lean_dec(x_729);
lean_inc(x_1);
x_732 = l_Lean_Meta_getMVarType(x_1, x_13, x_731);
if (lean_obj_tag(x_732) == 0)
{
lean_object* x_733; lean_object* x_734; uint8_t x_735; lean_object* x_736; 
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_732, 1);
lean_inc(x_734);
lean_dec(x_732);
x_735 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_735 == 0)
{
lean_object* x_808; uint8_t x_809; 
x_808 = l_Lean_MetavarContext_exprDependsOn(x_720, x_733, x_2);
x_809 = lean_unbox(x_808);
lean_dec(x_808);
if (x_809 == 0)
{
x_736 = x_734;
goto block_807;
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; uint8_t x_817; 
lean_dec(x_730);
lean_dec(x_717);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_810 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_810, 0, x_3);
x_811 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_812 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_812, 0, x_811);
lean_ctor_set(x_812, 1, x_810);
x_813 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_814 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_814, 0, x_812);
lean_ctor_set(x_814, 1, x_813);
x_815 = lean_box(0);
x_816 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_814, x_815, x_13, x_734);
lean_dec(x_13);
x_817 = !lean_is_exclusive(x_816);
if (x_817 == 0)
{
return x_816;
}
else
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_818 = lean_ctor_get(x_816, 0);
x_819 = lean_ctor_get(x_816, 1);
lean_inc(x_819);
lean_inc(x_818);
lean_dec(x_816);
x_820 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_820, 0, x_818);
lean_ctor_set(x_820, 1, x_819);
return x_820;
}
}
}
else
{
lean_dec(x_733);
lean_dec(x_720);
x_736 = x_734;
goto block_807;
}
block_807:
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; uint8_t x_741; lean_object* x_742; 
lean_inc(x_730);
x_737 = x_730;
x_738 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_726, x_737);
x_739 = x_738;
x_740 = lean_array_push(x_739, x_2);
x_741 = 1;
x_742 = l_Lean_Meta_revert(x_1, x_740, x_741, x_13, x_736);
if (lean_obj_tag(x_742) == 0)
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; uint8_t x_749; lean_object* x_750; 
x_743 = lean_ctor_get(x_742, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_742, 1);
lean_inc(x_744);
lean_dec(x_742);
x_745 = lean_ctor_get(x_743, 0);
lean_inc(x_745);
x_746 = lean_ctor_get(x_743, 1);
lean_inc(x_746);
lean_dec(x_743);
x_747 = lean_array_get_size(x_730);
x_748 = lean_box(0);
x_749 = 0;
x_750 = l_Lean_Meta_introN(x_746, x_747, x_748, x_749, x_13, x_744);
if (lean_obj_tag(x_750) == 0)
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_751 = lean_ctor_get(x_750, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_750, 1);
lean_inc(x_752);
lean_dec(x_750);
x_753 = lean_ctor_get(x_751, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_751, 1);
lean_inc(x_754);
lean_dec(x_751);
x_755 = l_Lean_Meta_intro1(x_754, x_749, x_13, x_752);
if (lean_obj_tag(x_755) == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_782; uint8_t x_783; 
x_756 = lean_ctor_get(x_755, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_755, 1);
lean_inc(x_757);
lean_dec(x_755);
x_758 = lean_ctor_get(x_756, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_756, 1);
lean_inc(x_759);
lean_dec(x_756);
x_760 = lean_box(0);
x_761 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_730, x_753, x_730, x_726, x_760);
lean_dec(x_730);
x_782 = lean_ctor_get(x_757, 4);
lean_inc(x_782);
x_783 = lean_ctor_get_uint8(x_782, sizeof(void*)*1);
lean_dec(x_782);
if (x_783 == 0)
{
x_762 = x_757;
goto block_781;
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; uint8_t x_787; 
x_784 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_785 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_784, x_13, x_757);
x_786 = lean_ctor_get(x_785, 0);
lean_inc(x_786);
x_787 = lean_unbox(x_786);
lean_dec(x_786);
if (x_787 == 0)
{
lean_object* x_788; 
x_788 = lean_ctor_get(x_785, 1);
lean_inc(x_788);
lean_dec(x_785);
x_762 = x_788;
goto block_781;
}
else
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_789 = lean_ctor_get(x_785, 1);
lean_inc(x_789);
lean_dec(x_785);
lean_inc(x_759);
x_790 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_790, 0, x_759);
x_791 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_792 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_792, 0, x_791);
lean_ctor_set(x_792, 1, x_790);
x_793 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_784, x_792, x_13, x_789);
x_794 = lean_ctor_get(x_793, 1);
lean_inc(x_794);
lean_dec(x_793);
x_762 = x_794;
goto block_781;
}
}
block_781:
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; 
x_763 = x_753;
x_764 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_726, x_763);
x_765 = x_764;
lean_inc(x_758);
x_766 = l_Lean_mkFVar(x_758);
lean_inc(x_759);
x_767 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_767, 0, x_759);
x_768 = lean_box(x_735);
lean_inc(x_759);
x_769 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_769, 0, x_758);
lean_closure_set(x_769, 1, x_8);
lean_closure_set(x_769, 2, x_759);
lean_closure_set(x_769, 3, x_3);
lean_closure_set(x_769, 4, x_4);
lean_closure_set(x_769, 5, x_6);
lean_closure_set(x_769, 6, x_7);
lean_closure_set(x_769, 7, x_717);
lean_closure_set(x_769, 8, x_768);
lean_closure_set(x_769, 9, x_745);
lean_closure_set(x_769, 10, x_761);
lean_closure_set(x_769, 11, x_765);
lean_closure_set(x_769, 12, x_766);
x_770 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_770, 0, x_767);
lean_closure_set(x_770, 1, x_769);
x_771 = l_Lean_Meta_getMVarDecl(x_759, x_13, x_762);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_771, 1);
lean_inc(x_773);
lean_dec(x_771);
x_774 = lean_ctor_get(x_772, 1);
lean_inc(x_774);
x_775 = lean_ctor_get(x_772, 4);
lean_inc(x_775);
lean_dec(x_772);
x_776 = l_Lean_Meta_withLocalContext___rarg(x_774, x_775, x_770, x_13, x_773);
lean_dec(x_13);
return x_776;
}
else
{
uint8_t x_777; 
lean_dec(x_770);
lean_dec(x_13);
x_777 = !lean_is_exclusive(x_771);
if (x_777 == 0)
{
return x_771;
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_778 = lean_ctor_get(x_771, 0);
x_779 = lean_ctor_get(x_771, 1);
lean_inc(x_779);
lean_inc(x_778);
lean_dec(x_771);
x_780 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_780, 0, x_778);
lean_ctor_set(x_780, 1, x_779);
return x_780;
}
}
}
}
else
{
uint8_t x_795; 
lean_dec(x_753);
lean_dec(x_745);
lean_dec(x_730);
lean_dec(x_717);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_795 = !lean_is_exclusive(x_755);
if (x_795 == 0)
{
return x_755;
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_796 = lean_ctor_get(x_755, 0);
x_797 = lean_ctor_get(x_755, 1);
lean_inc(x_797);
lean_inc(x_796);
lean_dec(x_755);
x_798 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_798, 0, x_796);
lean_ctor_set(x_798, 1, x_797);
return x_798;
}
}
}
else
{
uint8_t x_799; 
lean_dec(x_745);
lean_dec(x_730);
lean_dec(x_717);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_799 = !lean_is_exclusive(x_750);
if (x_799 == 0)
{
return x_750;
}
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; 
x_800 = lean_ctor_get(x_750, 0);
x_801 = lean_ctor_get(x_750, 1);
lean_inc(x_801);
lean_inc(x_800);
lean_dec(x_750);
x_802 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_802, 0, x_800);
lean_ctor_set(x_802, 1, x_801);
return x_802;
}
}
}
else
{
uint8_t x_803; 
lean_dec(x_730);
lean_dec(x_717);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_803 = !lean_is_exclusive(x_742);
if (x_803 == 0)
{
return x_742;
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_804 = lean_ctor_get(x_742, 0);
x_805 = lean_ctor_get(x_742, 1);
lean_inc(x_805);
lean_inc(x_804);
lean_dec(x_742);
x_806 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_806, 0, x_804);
lean_ctor_set(x_806, 1, x_805);
return x_806;
}
}
}
}
else
{
uint8_t x_821; 
lean_dec(x_730);
lean_dec(x_720);
lean_dec(x_717);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_821 = !lean_is_exclusive(x_732);
if (x_821 == 0)
{
return x_732;
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_822 = lean_ctor_get(x_732, 0);
x_823 = lean_ctor_get(x_732, 1);
lean_inc(x_823);
lean_inc(x_822);
lean_dec(x_732);
x_824 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_824, 0, x_822);
lean_ctor_set(x_824, 1, x_823);
return x_824;
}
}
}
else
{
uint8_t x_825; 
lean_dec(x_720);
lean_dec(x_717);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_825 = !lean_is_exclusive(x_729);
if (x_825 == 0)
{
return x_729;
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_826 = lean_ctor_get(x_729, 0);
x_827 = lean_ctor_get(x_729, 1);
lean_inc(x_827);
lean_inc(x_826);
lean_dec(x_729);
x_828 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_828, 0, x_826);
lean_ctor_set(x_828, 1, x_827);
return x_828;
}
}
}
else
{
uint8_t x_829; 
lean_dec(x_717);
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
x_829 = !lean_is_exclusive(x_718);
if (x_829 == 0)
{
return x_718;
}
else
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; 
x_830 = lean_ctor_get(x_718, 0);
x_831 = lean_ctor_get(x_718, 1);
lean_inc(x_831);
lean_inc(x_830);
lean_dec(x_718);
x_832 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_832, 0, x_830);
lean_ctor_set(x_832, 1, x_831);
return x_832;
}
}
}
case 8:
{
lean_object* x_833; lean_object* x_834; 
lean_dec(x_12);
lean_dec(x_10);
x_833 = lean_ctor_get(x_7, 5);
lean_inc(x_833);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_834 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_833, x_13, x_14);
if (lean_obj_tag(x_834) == 0)
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; 
x_835 = lean_ctor_get(x_834, 1);
lean_inc(x_835);
lean_dec(x_834);
x_836 = lean_ctor_get(x_835, 1);
lean_inc(x_836);
x_837 = lean_ctor_get(x_7, 6);
lean_inc(x_837);
x_838 = l_List_redLength___main___rarg(x_837);
x_839 = lean_mk_empty_array_with_capacity(x_838);
lean_dec(x_838);
lean_inc(x_837);
x_840 = l_List_toArrayAux___main___rarg(x_837, x_839);
x_841 = x_840;
x_842 = lean_unsigned_to_nat(0u);
lean_inc(x_836);
lean_inc(x_6);
lean_inc(x_1);
x_843 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_843, 0, x_1);
lean_closure_set(x_843, 1, x_6);
lean_closure_set(x_843, 2, x_9);
lean_closure_set(x_843, 3, x_11);
lean_closure_set(x_843, 4, x_836);
lean_closure_set(x_843, 5, x_837);
lean_closure_set(x_843, 6, x_842);
lean_closure_set(x_843, 7, x_841);
x_844 = x_843;
lean_inc(x_13);
x_845 = lean_apply_2(x_844, x_13, x_835);
if (lean_obj_tag(x_845) == 0)
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_845, 1);
lean_inc(x_847);
lean_dec(x_845);
lean_inc(x_1);
x_848 = l_Lean_Meta_getMVarType(x_1, x_13, x_847);
if (lean_obj_tag(x_848) == 0)
{
lean_object* x_849; lean_object* x_850; uint8_t x_851; lean_object* x_852; 
x_849 = lean_ctor_get(x_848, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_848, 1);
lean_inc(x_850);
lean_dec(x_848);
x_851 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_851 == 0)
{
lean_object* x_924; uint8_t x_925; 
x_924 = l_Lean_MetavarContext_exprDependsOn(x_836, x_849, x_2);
x_925 = lean_unbox(x_924);
lean_dec(x_924);
if (x_925 == 0)
{
x_852 = x_850;
goto block_923;
}
else
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; uint8_t x_933; 
lean_dec(x_846);
lean_dec(x_833);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_926 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_926, 0, x_3);
x_927 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_928 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_928, 0, x_927);
lean_ctor_set(x_928, 1, x_926);
x_929 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_930 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_930, 0, x_928);
lean_ctor_set(x_930, 1, x_929);
x_931 = lean_box(0);
x_932 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_930, x_931, x_13, x_850);
lean_dec(x_13);
x_933 = !lean_is_exclusive(x_932);
if (x_933 == 0)
{
return x_932;
}
else
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; 
x_934 = lean_ctor_get(x_932, 0);
x_935 = lean_ctor_get(x_932, 1);
lean_inc(x_935);
lean_inc(x_934);
lean_dec(x_932);
x_936 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_936, 0, x_934);
lean_ctor_set(x_936, 1, x_935);
return x_936;
}
}
}
else
{
lean_dec(x_849);
lean_dec(x_836);
x_852 = x_850;
goto block_923;
}
block_923:
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; uint8_t x_857; lean_object* x_858; 
lean_inc(x_846);
x_853 = x_846;
x_854 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_842, x_853);
x_855 = x_854;
x_856 = lean_array_push(x_855, x_2);
x_857 = 1;
x_858 = l_Lean_Meta_revert(x_1, x_856, x_857, x_13, x_852);
if (lean_obj_tag(x_858) == 0)
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; uint8_t x_865; lean_object* x_866; 
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
x_863 = lean_array_get_size(x_846);
x_864 = lean_box(0);
x_865 = 0;
x_866 = l_Lean_Meta_introN(x_862, x_863, x_864, x_865, x_13, x_860);
if (lean_obj_tag(x_866) == 0)
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; 
x_867 = lean_ctor_get(x_866, 0);
lean_inc(x_867);
x_868 = lean_ctor_get(x_866, 1);
lean_inc(x_868);
lean_dec(x_866);
x_869 = lean_ctor_get(x_867, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_867, 1);
lean_inc(x_870);
lean_dec(x_867);
x_871 = l_Lean_Meta_intro1(x_870, x_865, x_13, x_868);
if (lean_obj_tag(x_871) == 0)
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_898; uint8_t x_899; 
x_872 = lean_ctor_get(x_871, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_871, 1);
lean_inc(x_873);
lean_dec(x_871);
x_874 = lean_ctor_get(x_872, 0);
lean_inc(x_874);
x_875 = lean_ctor_get(x_872, 1);
lean_inc(x_875);
lean_dec(x_872);
x_876 = lean_box(0);
x_877 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_846, x_869, x_846, x_842, x_876);
lean_dec(x_846);
x_898 = lean_ctor_get(x_873, 4);
lean_inc(x_898);
x_899 = lean_ctor_get_uint8(x_898, sizeof(void*)*1);
lean_dec(x_898);
if (x_899 == 0)
{
x_878 = x_873;
goto block_897;
}
else
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; uint8_t x_903; 
x_900 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_901 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_900, x_13, x_873);
x_902 = lean_ctor_get(x_901, 0);
lean_inc(x_902);
x_903 = lean_unbox(x_902);
lean_dec(x_902);
if (x_903 == 0)
{
lean_object* x_904; 
x_904 = lean_ctor_get(x_901, 1);
lean_inc(x_904);
lean_dec(x_901);
x_878 = x_904;
goto block_897;
}
else
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; 
x_905 = lean_ctor_get(x_901, 1);
lean_inc(x_905);
lean_dec(x_901);
lean_inc(x_875);
x_906 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_906, 0, x_875);
x_907 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_908 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_908, 0, x_907);
lean_ctor_set(x_908, 1, x_906);
x_909 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_900, x_908, x_13, x_905);
x_910 = lean_ctor_get(x_909, 1);
lean_inc(x_910);
lean_dec(x_909);
x_878 = x_910;
goto block_897;
}
}
block_897:
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; 
x_879 = x_869;
x_880 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_842, x_879);
x_881 = x_880;
lean_inc(x_874);
x_882 = l_Lean_mkFVar(x_874);
lean_inc(x_875);
x_883 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_883, 0, x_875);
x_884 = lean_box(x_851);
lean_inc(x_875);
x_885 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_885, 0, x_874);
lean_closure_set(x_885, 1, x_8);
lean_closure_set(x_885, 2, x_875);
lean_closure_set(x_885, 3, x_3);
lean_closure_set(x_885, 4, x_4);
lean_closure_set(x_885, 5, x_6);
lean_closure_set(x_885, 6, x_7);
lean_closure_set(x_885, 7, x_833);
lean_closure_set(x_885, 8, x_884);
lean_closure_set(x_885, 9, x_861);
lean_closure_set(x_885, 10, x_877);
lean_closure_set(x_885, 11, x_881);
lean_closure_set(x_885, 12, x_882);
x_886 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_886, 0, x_883);
lean_closure_set(x_886, 1, x_885);
x_887 = l_Lean_Meta_getMVarDecl(x_875, x_13, x_878);
if (lean_obj_tag(x_887) == 0)
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; 
x_888 = lean_ctor_get(x_887, 0);
lean_inc(x_888);
x_889 = lean_ctor_get(x_887, 1);
lean_inc(x_889);
lean_dec(x_887);
x_890 = lean_ctor_get(x_888, 1);
lean_inc(x_890);
x_891 = lean_ctor_get(x_888, 4);
lean_inc(x_891);
lean_dec(x_888);
x_892 = l_Lean_Meta_withLocalContext___rarg(x_890, x_891, x_886, x_13, x_889);
lean_dec(x_13);
return x_892;
}
else
{
uint8_t x_893; 
lean_dec(x_886);
lean_dec(x_13);
x_893 = !lean_is_exclusive(x_887);
if (x_893 == 0)
{
return x_887;
}
else
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; 
x_894 = lean_ctor_get(x_887, 0);
x_895 = lean_ctor_get(x_887, 1);
lean_inc(x_895);
lean_inc(x_894);
lean_dec(x_887);
x_896 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_896, 0, x_894);
lean_ctor_set(x_896, 1, x_895);
return x_896;
}
}
}
}
else
{
uint8_t x_911; 
lean_dec(x_869);
lean_dec(x_861);
lean_dec(x_846);
lean_dec(x_833);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_911 = !lean_is_exclusive(x_871);
if (x_911 == 0)
{
return x_871;
}
else
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; 
x_912 = lean_ctor_get(x_871, 0);
x_913 = lean_ctor_get(x_871, 1);
lean_inc(x_913);
lean_inc(x_912);
lean_dec(x_871);
x_914 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_914, 0, x_912);
lean_ctor_set(x_914, 1, x_913);
return x_914;
}
}
}
else
{
uint8_t x_915; 
lean_dec(x_861);
lean_dec(x_846);
lean_dec(x_833);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_915 = !lean_is_exclusive(x_866);
if (x_915 == 0)
{
return x_866;
}
else
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_916 = lean_ctor_get(x_866, 0);
x_917 = lean_ctor_get(x_866, 1);
lean_inc(x_917);
lean_inc(x_916);
lean_dec(x_866);
x_918 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_918, 0, x_916);
lean_ctor_set(x_918, 1, x_917);
return x_918;
}
}
}
else
{
uint8_t x_919; 
lean_dec(x_846);
lean_dec(x_833);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_919 = !lean_is_exclusive(x_858);
if (x_919 == 0)
{
return x_858;
}
else
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_920 = lean_ctor_get(x_858, 0);
x_921 = lean_ctor_get(x_858, 1);
lean_inc(x_921);
lean_inc(x_920);
lean_dec(x_858);
x_922 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_922, 0, x_920);
lean_ctor_set(x_922, 1, x_921);
return x_922;
}
}
}
}
else
{
uint8_t x_937; 
lean_dec(x_846);
lean_dec(x_836);
lean_dec(x_833);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_937 = !lean_is_exclusive(x_848);
if (x_937 == 0)
{
return x_848;
}
else
{
lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_938 = lean_ctor_get(x_848, 0);
x_939 = lean_ctor_get(x_848, 1);
lean_inc(x_939);
lean_inc(x_938);
lean_dec(x_848);
x_940 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_940, 0, x_938);
lean_ctor_set(x_940, 1, x_939);
return x_940;
}
}
}
else
{
uint8_t x_941; 
lean_dec(x_836);
lean_dec(x_833);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_941 = !lean_is_exclusive(x_845);
if (x_941 == 0)
{
return x_845;
}
else
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; 
x_942 = lean_ctor_get(x_845, 0);
x_943 = lean_ctor_get(x_845, 1);
lean_inc(x_943);
lean_inc(x_942);
lean_dec(x_845);
x_944 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_944, 0, x_942);
lean_ctor_set(x_944, 1, x_943);
return x_944;
}
}
}
else
{
uint8_t x_945; 
lean_dec(x_833);
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
x_945 = !lean_is_exclusive(x_834);
if (x_945 == 0)
{
return x_834;
}
else
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; 
x_946 = lean_ctor_get(x_834, 0);
x_947 = lean_ctor_get(x_834, 1);
lean_inc(x_947);
lean_inc(x_946);
lean_dec(x_834);
x_948 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_948, 0, x_946);
lean_ctor_set(x_948, 1, x_947);
return x_948;
}
}
}
case 9:
{
lean_object* x_949; lean_object* x_950; 
lean_dec(x_12);
lean_dec(x_10);
x_949 = lean_ctor_get(x_7, 5);
lean_inc(x_949);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_950 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_949, x_13, x_14);
if (lean_obj_tag(x_950) == 0)
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; 
x_951 = lean_ctor_get(x_950, 1);
lean_inc(x_951);
lean_dec(x_950);
x_952 = lean_ctor_get(x_951, 1);
lean_inc(x_952);
x_953 = lean_ctor_get(x_7, 6);
lean_inc(x_953);
x_954 = l_List_redLength___main___rarg(x_953);
x_955 = lean_mk_empty_array_with_capacity(x_954);
lean_dec(x_954);
lean_inc(x_953);
x_956 = l_List_toArrayAux___main___rarg(x_953, x_955);
x_957 = x_956;
x_958 = lean_unsigned_to_nat(0u);
lean_inc(x_952);
lean_inc(x_6);
lean_inc(x_1);
x_959 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_959, 0, x_1);
lean_closure_set(x_959, 1, x_6);
lean_closure_set(x_959, 2, x_9);
lean_closure_set(x_959, 3, x_11);
lean_closure_set(x_959, 4, x_952);
lean_closure_set(x_959, 5, x_953);
lean_closure_set(x_959, 6, x_958);
lean_closure_set(x_959, 7, x_957);
x_960 = x_959;
lean_inc(x_13);
x_961 = lean_apply_2(x_960, x_13, x_951);
if (lean_obj_tag(x_961) == 0)
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; 
x_962 = lean_ctor_get(x_961, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_961, 1);
lean_inc(x_963);
lean_dec(x_961);
lean_inc(x_1);
x_964 = l_Lean_Meta_getMVarType(x_1, x_13, x_963);
if (lean_obj_tag(x_964) == 0)
{
lean_object* x_965; lean_object* x_966; uint8_t x_967; lean_object* x_968; 
x_965 = lean_ctor_get(x_964, 0);
lean_inc(x_965);
x_966 = lean_ctor_get(x_964, 1);
lean_inc(x_966);
lean_dec(x_964);
x_967 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_967 == 0)
{
lean_object* x_1040; uint8_t x_1041; 
x_1040 = l_Lean_MetavarContext_exprDependsOn(x_952, x_965, x_2);
x_1041 = lean_unbox(x_1040);
lean_dec(x_1040);
if (x_1041 == 0)
{
x_968 = x_966;
goto block_1039;
}
else
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; uint8_t x_1049; 
lean_dec(x_962);
lean_dec(x_949);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_1042 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1042, 0, x_3);
x_1043 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1044 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1044, 0, x_1043);
lean_ctor_set(x_1044, 1, x_1042);
x_1045 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_1046 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1046, 0, x_1044);
lean_ctor_set(x_1046, 1, x_1045);
x_1047 = lean_box(0);
x_1048 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1046, x_1047, x_13, x_966);
lean_dec(x_13);
x_1049 = !lean_is_exclusive(x_1048);
if (x_1049 == 0)
{
return x_1048;
}
else
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
x_1050 = lean_ctor_get(x_1048, 0);
x_1051 = lean_ctor_get(x_1048, 1);
lean_inc(x_1051);
lean_inc(x_1050);
lean_dec(x_1048);
x_1052 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1052, 0, x_1050);
lean_ctor_set(x_1052, 1, x_1051);
return x_1052;
}
}
}
else
{
lean_dec(x_965);
lean_dec(x_952);
x_968 = x_966;
goto block_1039;
}
block_1039:
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; uint8_t x_973; lean_object* x_974; 
lean_inc(x_962);
x_969 = x_962;
x_970 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_958, x_969);
x_971 = x_970;
x_972 = lean_array_push(x_971, x_2);
x_973 = 1;
x_974 = l_Lean_Meta_revert(x_1, x_972, x_973, x_13, x_968);
if (lean_obj_tag(x_974) == 0)
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; uint8_t x_981; lean_object* x_982; 
x_975 = lean_ctor_get(x_974, 0);
lean_inc(x_975);
x_976 = lean_ctor_get(x_974, 1);
lean_inc(x_976);
lean_dec(x_974);
x_977 = lean_ctor_get(x_975, 0);
lean_inc(x_977);
x_978 = lean_ctor_get(x_975, 1);
lean_inc(x_978);
lean_dec(x_975);
x_979 = lean_array_get_size(x_962);
x_980 = lean_box(0);
x_981 = 0;
x_982 = l_Lean_Meta_introN(x_978, x_979, x_980, x_981, x_13, x_976);
if (lean_obj_tag(x_982) == 0)
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_983 = lean_ctor_get(x_982, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_982, 1);
lean_inc(x_984);
lean_dec(x_982);
x_985 = lean_ctor_get(x_983, 0);
lean_inc(x_985);
x_986 = lean_ctor_get(x_983, 1);
lean_inc(x_986);
lean_dec(x_983);
x_987 = l_Lean_Meta_intro1(x_986, x_981, x_13, x_984);
if (lean_obj_tag(x_987) == 0)
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_1014; uint8_t x_1015; 
x_988 = lean_ctor_get(x_987, 0);
lean_inc(x_988);
x_989 = lean_ctor_get(x_987, 1);
lean_inc(x_989);
lean_dec(x_987);
x_990 = lean_ctor_get(x_988, 0);
lean_inc(x_990);
x_991 = lean_ctor_get(x_988, 1);
lean_inc(x_991);
lean_dec(x_988);
x_992 = lean_box(0);
x_993 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_962, x_985, x_962, x_958, x_992);
lean_dec(x_962);
x_1014 = lean_ctor_get(x_989, 4);
lean_inc(x_1014);
x_1015 = lean_ctor_get_uint8(x_1014, sizeof(void*)*1);
lean_dec(x_1014);
if (x_1015 == 0)
{
x_994 = x_989;
goto block_1013;
}
else
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; uint8_t x_1019; 
x_1016 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1017 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1016, x_13, x_989);
x_1018 = lean_ctor_get(x_1017, 0);
lean_inc(x_1018);
x_1019 = lean_unbox(x_1018);
lean_dec(x_1018);
if (x_1019 == 0)
{
lean_object* x_1020; 
x_1020 = lean_ctor_get(x_1017, 1);
lean_inc(x_1020);
lean_dec(x_1017);
x_994 = x_1020;
goto block_1013;
}
else
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
x_1021 = lean_ctor_get(x_1017, 1);
lean_inc(x_1021);
lean_dec(x_1017);
lean_inc(x_991);
x_1022 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1022, 0, x_991);
x_1023 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_1024 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1024, 0, x_1023);
lean_ctor_set(x_1024, 1, x_1022);
x_1025 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1016, x_1024, x_13, x_1021);
x_1026 = lean_ctor_get(x_1025, 1);
lean_inc(x_1026);
lean_dec(x_1025);
x_994 = x_1026;
goto block_1013;
}
}
block_1013:
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; 
x_995 = x_985;
x_996 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_958, x_995);
x_997 = x_996;
lean_inc(x_990);
x_998 = l_Lean_mkFVar(x_990);
lean_inc(x_991);
x_999 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_999, 0, x_991);
x_1000 = lean_box(x_967);
lean_inc(x_991);
x_1001 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_1001, 0, x_990);
lean_closure_set(x_1001, 1, x_8);
lean_closure_set(x_1001, 2, x_991);
lean_closure_set(x_1001, 3, x_3);
lean_closure_set(x_1001, 4, x_4);
lean_closure_set(x_1001, 5, x_6);
lean_closure_set(x_1001, 6, x_7);
lean_closure_set(x_1001, 7, x_949);
lean_closure_set(x_1001, 8, x_1000);
lean_closure_set(x_1001, 9, x_977);
lean_closure_set(x_1001, 10, x_993);
lean_closure_set(x_1001, 11, x_997);
lean_closure_set(x_1001, 12, x_998);
x_1002 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_1002, 0, x_999);
lean_closure_set(x_1002, 1, x_1001);
x_1003 = l_Lean_Meta_getMVarDecl(x_991, x_13, x_994);
if (lean_obj_tag(x_1003) == 0)
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
x_1004 = lean_ctor_get(x_1003, 0);
lean_inc(x_1004);
x_1005 = lean_ctor_get(x_1003, 1);
lean_inc(x_1005);
lean_dec(x_1003);
x_1006 = lean_ctor_get(x_1004, 1);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_1004, 4);
lean_inc(x_1007);
lean_dec(x_1004);
x_1008 = l_Lean_Meta_withLocalContext___rarg(x_1006, x_1007, x_1002, x_13, x_1005);
lean_dec(x_13);
return x_1008;
}
else
{
uint8_t x_1009; 
lean_dec(x_1002);
lean_dec(x_13);
x_1009 = !lean_is_exclusive(x_1003);
if (x_1009 == 0)
{
return x_1003;
}
else
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1010 = lean_ctor_get(x_1003, 0);
x_1011 = lean_ctor_get(x_1003, 1);
lean_inc(x_1011);
lean_inc(x_1010);
lean_dec(x_1003);
x_1012 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1012, 0, x_1010);
lean_ctor_set(x_1012, 1, x_1011);
return x_1012;
}
}
}
}
else
{
uint8_t x_1027; 
lean_dec(x_985);
lean_dec(x_977);
lean_dec(x_962);
lean_dec(x_949);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1027 = !lean_is_exclusive(x_987);
if (x_1027 == 0)
{
return x_987;
}
else
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; 
x_1028 = lean_ctor_get(x_987, 0);
x_1029 = lean_ctor_get(x_987, 1);
lean_inc(x_1029);
lean_inc(x_1028);
lean_dec(x_987);
x_1030 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1030, 0, x_1028);
lean_ctor_set(x_1030, 1, x_1029);
return x_1030;
}
}
}
else
{
uint8_t x_1031; 
lean_dec(x_977);
lean_dec(x_962);
lean_dec(x_949);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1031 = !lean_is_exclusive(x_982);
if (x_1031 == 0)
{
return x_982;
}
else
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
x_1032 = lean_ctor_get(x_982, 0);
x_1033 = lean_ctor_get(x_982, 1);
lean_inc(x_1033);
lean_inc(x_1032);
lean_dec(x_982);
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
lean_dec(x_962);
lean_dec(x_949);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1035 = !lean_is_exclusive(x_974);
if (x_1035 == 0)
{
return x_974;
}
else
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1036 = lean_ctor_get(x_974, 0);
x_1037 = lean_ctor_get(x_974, 1);
lean_inc(x_1037);
lean_inc(x_1036);
lean_dec(x_974);
x_1038 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1038, 0, x_1036);
lean_ctor_set(x_1038, 1, x_1037);
return x_1038;
}
}
}
}
else
{
uint8_t x_1053; 
lean_dec(x_962);
lean_dec(x_952);
lean_dec(x_949);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1053 = !lean_is_exclusive(x_964);
if (x_1053 == 0)
{
return x_964;
}
else
{
lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
x_1054 = lean_ctor_get(x_964, 0);
x_1055 = lean_ctor_get(x_964, 1);
lean_inc(x_1055);
lean_inc(x_1054);
lean_dec(x_964);
x_1056 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1056, 0, x_1054);
lean_ctor_set(x_1056, 1, x_1055);
return x_1056;
}
}
}
else
{
uint8_t x_1057; 
lean_dec(x_952);
lean_dec(x_949);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1057 = !lean_is_exclusive(x_961);
if (x_1057 == 0)
{
return x_961;
}
else
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
x_1058 = lean_ctor_get(x_961, 0);
x_1059 = lean_ctor_get(x_961, 1);
lean_inc(x_1059);
lean_inc(x_1058);
lean_dec(x_961);
x_1060 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1060, 0, x_1058);
lean_ctor_set(x_1060, 1, x_1059);
return x_1060;
}
}
}
else
{
uint8_t x_1061; 
lean_dec(x_949);
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
x_1061 = !lean_is_exclusive(x_950);
if (x_1061 == 0)
{
return x_950;
}
else
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; 
x_1062 = lean_ctor_get(x_950, 0);
x_1063 = lean_ctor_get(x_950, 1);
lean_inc(x_1063);
lean_inc(x_1062);
lean_dec(x_950);
x_1064 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1064, 0, x_1062);
lean_ctor_set(x_1064, 1, x_1063);
return x_1064;
}
}
}
case 10:
{
lean_object* x_1065; lean_object* x_1066; 
lean_dec(x_12);
lean_dec(x_10);
x_1065 = lean_ctor_get(x_7, 5);
lean_inc(x_1065);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1066 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_1065, x_13, x_14);
if (lean_obj_tag(x_1066) == 0)
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; 
x_1067 = lean_ctor_get(x_1066, 1);
lean_inc(x_1067);
lean_dec(x_1066);
x_1068 = lean_ctor_get(x_1067, 1);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_7, 6);
lean_inc(x_1069);
x_1070 = l_List_redLength___main___rarg(x_1069);
x_1071 = lean_mk_empty_array_with_capacity(x_1070);
lean_dec(x_1070);
lean_inc(x_1069);
x_1072 = l_List_toArrayAux___main___rarg(x_1069, x_1071);
x_1073 = x_1072;
x_1074 = lean_unsigned_to_nat(0u);
lean_inc(x_1068);
lean_inc(x_6);
lean_inc(x_1);
x_1075 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_1075, 0, x_1);
lean_closure_set(x_1075, 1, x_6);
lean_closure_set(x_1075, 2, x_9);
lean_closure_set(x_1075, 3, x_11);
lean_closure_set(x_1075, 4, x_1068);
lean_closure_set(x_1075, 5, x_1069);
lean_closure_set(x_1075, 6, x_1074);
lean_closure_set(x_1075, 7, x_1073);
x_1076 = x_1075;
lean_inc(x_13);
x_1077 = lean_apply_2(x_1076, x_13, x_1067);
if (lean_obj_tag(x_1077) == 0)
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
x_1078 = lean_ctor_get(x_1077, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1077, 1);
lean_inc(x_1079);
lean_dec(x_1077);
lean_inc(x_1);
x_1080 = l_Lean_Meta_getMVarType(x_1, x_13, x_1079);
if (lean_obj_tag(x_1080) == 0)
{
lean_object* x_1081; lean_object* x_1082; uint8_t x_1083; lean_object* x_1084; 
x_1081 = lean_ctor_get(x_1080, 0);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_1080, 1);
lean_inc(x_1082);
lean_dec(x_1080);
x_1083 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_1083 == 0)
{
lean_object* x_1156; uint8_t x_1157; 
x_1156 = l_Lean_MetavarContext_exprDependsOn(x_1068, x_1081, x_2);
x_1157 = lean_unbox(x_1156);
lean_dec(x_1156);
if (x_1157 == 0)
{
x_1084 = x_1082;
goto block_1155;
}
else
{
lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; uint8_t x_1165; 
lean_dec(x_1078);
lean_dec(x_1065);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_1158 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1158, 0, x_3);
x_1159 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1160 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1160, 0, x_1159);
lean_ctor_set(x_1160, 1, x_1158);
x_1161 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_1162 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1162, 0, x_1160);
lean_ctor_set(x_1162, 1, x_1161);
x_1163 = lean_box(0);
x_1164 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1162, x_1163, x_13, x_1082);
lean_dec(x_13);
x_1165 = !lean_is_exclusive(x_1164);
if (x_1165 == 0)
{
return x_1164;
}
else
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; 
x_1166 = lean_ctor_get(x_1164, 0);
x_1167 = lean_ctor_get(x_1164, 1);
lean_inc(x_1167);
lean_inc(x_1166);
lean_dec(x_1164);
x_1168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1168, 0, x_1166);
lean_ctor_set(x_1168, 1, x_1167);
return x_1168;
}
}
}
else
{
lean_dec(x_1081);
lean_dec(x_1068);
x_1084 = x_1082;
goto block_1155;
}
block_1155:
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; uint8_t x_1089; lean_object* x_1090; 
lean_inc(x_1078);
x_1085 = x_1078;
x_1086 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1074, x_1085);
x_1087 = x_1086;
x_1088 = lean_array_push(x_1087, x_2);
x_1089 = 1;
x_1090 = l_Lean_Meta_revert(x_1, x_1088, x_1089, x_13, x_1084);
if (lean_obj_tag(x_1090) == 0)
{
lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; uint8_t x_1097; lean_object* x_1098; 
x_1091 = lean_ctor_get(x_1090, 0);
lean_inc(x_1091);
x_1092 = lean_ctor_get(x_1090, 1);
lean_inc(x_1092);
lean_dec(x_1090);
x_1093 = lean_ctor_get(x_1091, 0);
lean_inc(x_1093);
x_1094 = lean_ctor_get(x_1091, 1);
lean_inc(x_1094);
lean_dec(x_1091);
x_1095 = lean_array_get_size(x_1078);
x_1096 = lean_box(0);
x_1097 = 0;
x_1098 = l_Lean_Meta_introN(x_1094, x_1095, x_1096, x_1097, x_13, x_1092);
if (lean_obj_tag(x_1098) == 0)
{
lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
x_1099 = lean_ctor_get(x_1098, 0);
lean_inc(x_1099);
x_1100 = lean_ctor_get(x_1098, 1);
lean_inc(x_1100);
lean_dec(x_1098);
x_1101 = lean_ctor_get(x_1099, 0);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1099, 1);
lean_inc(x_1102);
lean_dec(x_1099);
x_1103 = l_Lean_Meta_intro1(x_1102, x_1097, x_13, x_1100);
if (lean_obj_tag(x_1103) == 0)
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1130; uint8_t x_1131; 
x_1104 = lean_ctor_get(x_1103, 0);
lean_inc(x_1104);
x_1105 = lean_ctor_get(x_1103, 1);
lean_inc(x_1105);
lean_dec(x_1103);
x_1106 = lean_ctor_get(x_1104, 0);
lean_inc(x_1106);
x_1107 = lean_ctor_get(x_1104, 1);
lean_inc(x_1107);
lean_dec(x_1104);
x_1108 = lean_box(0);
x_1109 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_1078, x_1101, x_1078, x_1074, x_1108);
lean_dec(x_1078);
x_1130 = lean_ctor_get(x_1105, 4);
lean_inc(x_1130);
x_1131 = lean_ctor_get_uint8(x_1130, sizeof(void*)*1);
lean_dec(x_1130);
if (x_1131 == 0)
{
x_1110 = x_1105;
goto block_1129;
}
else
{
lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; uint8_t x_1135; 
x_1132 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1133 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1132, x_13, x_1105);
x_1134 = lean_ctor_get(x_1133, 0);
lean_inc(x_1134);
x_1135 = lean_unbox(x_1134);
lean_dec(x_1134);
if (x_1135 == 0)
{
lean_object* x_1136; 
x_1136 = lean_ctor_get(x_1133, 1);
lean_inc(x_1136);
lean_dec(x_1133);
x_1110 = x_1136;
goto block_1129;
}
else
{
lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; 
x_1137 = lean_ctor_get(x_1133, 1);
lean_inc(x_1137);
lean_dec(x_1133);
lean_inc(x_1107);
x_1138 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1138, 0, x_1107);
x_1139 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_1140 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1140, 0, x_1139);
lean_ctor_set(x_1140, 1, x_1138);
x_1141 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1132, x_1140, x_13, x_1137);
x_1142 = lean_ctor_get(x_1141, 1);
lean_inc(x_1142);
lean_dec(x_1141);
x_1110 = x_1142;
goto block_1129;
}
}
block_1129:
{
lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; 
x_1111 = x_1101;
x_1112 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1074, x_1111);
x_1113 = x_1112;
lean_inc(x_1106);
x_1114 = l_Lean_mkFVar(x_1106);
lean_inc(x_1107);
x_1115 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_1115, 0, x_1107);
x_1116 = lean_box(x_1083);
lean_inc(x_1107);
x_1117 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_1117, 0, x_1106);
lean_closure_set(x_1117, 1, x_8);
lean_closure_set(x_1117, 2, x_1107);
lean_closure_set(x_1117, 3, x_3);
lean_closure_set(x_1117, 4, x_4);
lean_closure_set(x_1117, 5, x_6);
lean_closure_set(x_1117, 6, x_7);
lean_closure_set(x_1117, 7, x_1065);
lean_closure_set(x_1117, 8, x_1116);
lean_closure_set(x_1117, 9, x_1093);
lean_closure_set(x_1117, 10, x_1109);
lean_closure_set(x_1117, 11, x_1113);
lean_closure_set(x_1117, 12, x_1114);
x_1118 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_1118, 0, x_1115);
lean_closure_set(x_1118, 1, x_1117);
x_1119 = l_Lean_Meta_getMVarDecl(x_1107, x_13, x_1110);
if (lean_obj_tag(x_1119) == 0)
{
lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; 
x_1120 = lean_ctor_get(x_1119, 0);
lean_inc(x_1120);
x_1121 = lean_ctor_get(x_1119, 1);
lean_inc(x_1121);
lean_dec(x_1119);
x_1122 = lean_ctor_get(x_1120, 1);
lean_inc(x_1122);
x_1123 = lean_ctor_get(x_1120, 4);
lean_inc(x_1123);
lean_dec(x_1120);
x_1124 = l_Lean_Meta_withLocalContext___rarg(x_1122, x_1123, x_1118, x_13, x_1121);
lean_dec(x_13);
return x_1124;
}
else
{
uint8_t x_1125; 
lean_dec(x_1118);
lean_dec(x_13);
x_1125 = !lean_is_exclusive(x_1119);
if (x_1125 == 0)
{
return x_1119;
}
else
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; 
x_1126 = lean_ctor_get(x_1119, 0);
x_1127 = lean_ctor_get(x_1119, 1);
lean_inc(x_1127);
lean_inc(x_1126);
lean_dec(x_1119);
x_1128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1128, 0, x_1126);
lean_ctor_set(x_1128, 1, x_1127);
return x_1128;
}
}
}
}
else
{
uint8_t x_1143; 
lean_dec(x_1101);
lean_dec(x_1093);
lean_dec(x_1078);
lean_dec(x_1065);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1143 = !lean_is_exclusive(x_1103);
if (x_1143 == 0)
{
return x_1103;
}
else
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; 
x_1144 = lean_ctor_get(x_1103, 0);
x_1145 = lean_ctor_get(x_1103, 1);
lean_inc(x_1145);
lean_inc(x_1144);
lean_dec(x_1103);
x_1146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1146, 0, x_1144);
lean_ctor_set(x_1146, 1, x_1145);
return x_1146;
}
}
}
else
{
uint8_t x_1147; 
lean_dec(x_1093);
lean_dec(x_1078);
lean_dec(x_1065);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1147 = !lean_is_exclusive(x_1098);
if (x_1147 == 0)
{
return x_1098;
}
else
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
x_1148 = lean_ctor_get(x_1098, 0);
x_1149 = lean_ctor_get(x_1098, 1);
lean_inc(x_1149);
lean_inc(x_1148);
lean_dec(x_1098);
x_1150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1150, 0, x_1148);
lean_ctor_set(x_1150, 1, x_1149);
return x_1150;
}
}
}
else
{
uint8_t x_1151; 
lean_dec(x_1078);
lean_dec(x_1065);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1151 = !lean_is_exclusive(x_1090);
if (x_1151 == 0)
{
return x_1090;
}
else
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; 
x_1152 = lean_ctor_get(x_1090, 0);
x_1153 = lean_ctor_get(x_1090, 1);
lean_inc(x_1153);
lean_inc(x_1152);
lean_dec(x_1090);
x_1154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1154, 0, x_1152);
lean_ctor_set(x_1154, 1, x_1153);
return x_1154;
}
}
}
}
else
{
uint8_t x_1169; 
lean_dec(x_1078);
lean_dec(x_1068);
lean_dec(x_1065);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1169 = !lean_is_exclusive(x_1080);
if (x_1169 == 0)
{
return x_1080;
}
else
{
lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
x_1170 = lean_ctor_get(x_1080, 0);
x_1171 = lean_ctor_get(x_1080, 1);
lean_inc(x_1171);
lean_inc(x_1170);
lean_dec(x_1080);
x_1172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1172, 0, x_1170);
lean_ctor_set(x_1172, 1, x_1171);
return x_1172;
}
}
}
else
{
uint8_t x_1173; 
lean_dec(x_1068);
lean_dec(x_1065);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1173 = !lean_is_exclusive(x_1077);
if (x_1173 == 0)
{
return x_1077;
}
else
{
lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; 
x_1174 = lean_ctor_get(x_1077, 0);
x_1175 = lean_ctor_get(x_1077, 1);
lean_inc(x_1175);
lean_inc(x_1174);
lean_dec(x_1077);
x_1176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1176, 0, x_1174);
lean_ctor_set(x_1176, 1, x_1175);
return x_1176;
}
}
}
else
{
uint8_t x_1177; 
lean_dec(x_1065);
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
x_1177 = !lean_is_exclusive(x_1066);
if (x_1177 == 0)
{
return x_1066;
}
else
{
lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; 
x_1178 = lean_ctor_get(x_1066, 0);
x_1179 = lean_ctor_get(x_1066, 1);
lean_inc(x_1179);
lean_inc(x_1178);
lean_dec(x_1066);
x_1180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1180, 0, x_1178);
lean_ctor_set(x_1180, 1, x_1179);
return x_1180;
}
}
}
case 11:
{
lean_object* x_1181; lean_object* x_1182; 
lean_dec(x_12);
lean_dec(x_10);
x_1181 = lean_ctor_get(x_7, 5);
lean_inc(x_1181);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1182 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_1181, x_13, x_14);
if (lean_obj_tag(x_1182) == 0)
{
lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; 
x_1183 = lean_ctor_get(x_1182, 1);
lean_inc(x_1183);
lean_dec(x_1182);
x_1184 = lean_ctor_get(x_1183, 1);
lean_inc(x_1184);
x_1185 = lean_ctor_get(x_7, 6);
lean_inc(x_1185);
x_1186 = l_List_redLength___main___rarg(x_1185);
x_1187 = lean_mk_empty_array_with_capacity(x_1186);
lean_dec(x_1186);
lean_inc(x_1185);
x_1188 = l_List_toArrayAux___main___rarg(x_1185, x_1187);
x_1189 = x_1188;
x_1190 = lean_unsigned_to_nat(0u);
lean_inc(x_1184);
lean_inc(x_6);
lean_inc(x_1);
x_1191 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_1191, 0, x_1);
lean_closure_set(x_1191, 1, x_6);
lean_closure_set(x_1191, 2, x_9);
lean_closure_set(x_1191, 3, x_11);
lean_closure_set(x_1191, 4, x_1184);
lean_closure_set(x_1191, 5, x_1185);
lean_closure_set(x_1191, 6, x_1190);
lean_closure_set(x_1191, 7, x_1189);
x_1192 = x_1191;
lean_inc(x_13);
x_1193 = lean_apply_2(x_1192, x_13, x_1183);
if (lean_obj_tag(x_1193) == 0)
{
lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; 
x_1194 = lean_ctor_get(x_1193, 0);
lean_inc(x_1194);
x_1195 = lean_ctor_get(x_1193, 1);
lean_inc(x_1195);
lean_dec(x_1193);
lean_inc(x_1);
x_1196 = l_Lean_Meta_getMVarType(x_1, x_13, x_1195);
if (lean_obj_tag(x_1196) == 0)
{
lean_object* x_1197; lean_object* x_1198; uint8_t x_1199; lean_object* x_1200; 
x_1197 = lean_ctor_get(x_1196, 0);
lean_inc(x_1197);
x_1198 = lean_ctor_get(x_1196, 1);
lean_inc(x_1198);
lean_dec(x_1196);
x_1199 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_1199 == 0)
{
lean_object* x_1272; uint8_t x_1273; 
x_1272 = l_Lean_MetavarContext_exprDependsOn(x_1184, x_1197, x_2);
x_1273 = lean_unbox(x_1272);
lean_dec(x_1272);
if (x_1273 == 0)
{
x_1200 = x_1198;
goto block_1271;
}
else
{
lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; uint8_t x_1281; 
lean_dec(x_1194);
lean_dec(x_1181);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_1274 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1274, 0, x_3);
x_1275 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1276 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1276, 0, x_1275);
lean_ctor_set(x_1276, 1, x_1274);
x_1277 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_1278 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1278, 0, x_1276);
lean_ctor_set(x_1278, 1, x_1277);
x_1279 = lean_box(0);
x_1280 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1278, x_1279, x_13, x_1198);
lean_dec(x_13);
x_1281 = !lean_is_exclusive(x_1280);
if (x_1281 == 0)
{
return x_1280;
}
else
{
lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; 
x_1282 = lean_ctor_get(x_1280, 0);
x_1283 = lean_ctor_get(x_1280, 1);
lean_inc(x_1283);
lean_inc(x_1282);
lean_dec(x_1280);
x_1284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1284, 0, x_1282);
lean_ctor_set(x_1284, 1, x_1283);
return x_1284;
}
}
}
else
{
lean_dec(x_1197);
lean_dec(x_1184);
x_1200 = x_1198;
goto block_1271;
}
block_1271:
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; uint8_t x_1205; lean_object* x_1206; 
lean_inc(x_1194);
x_1201 = x_1194;
x_1202 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1190, x_1201);
x_1203 = x_1202;
x_1204 = lean_array_push(x_1203, x_2);
x_1205 = 1;
x_1206 = l_Lean_Meta_revert(x_1, x_1204, x_1205, x_13, x_1200);
if (lean_obj_tag(x_1206) == 0)
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; uint8_t x_1213; lean_object* x_1214; 
x_1207 = lean_ctor_get(x_1206, 0);
lean_inc(x_1207);
x_1208 = lean_ctor_get(x_1206, 1);
lean_inc(x_1208);
lean_dec(x_1206);
x_1209 = lean_ctor_get(x_1207, 0);
lean_inc(x_1209);
x_1210 = lean_ctor_get(x_1207, 1);
lean_inc(x_1210);
lean_dec(x_1207);
x_1211 = lean_array_get_size(x_1194);
x_1212 = lean_box(0);
x_1213 = 0;
x_1214 = l_Lean_Meta_introN(x_1210, x_1211, x_1212, x_1213, x_13, x_1208);
if (lean_obj_tag(x_1214) == 0)
{
lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; 
x_1215 = lean_ctor_get(x_1214, 0);
lean_inc(x_1215);
x_1216 = lean_ctor_get(x_1214, 1);
lean_inc(x_1216);
lean_dec(x_1214);
x_1217 = lean_ctor_get(x_1215, 0);
lean_inc(x_1217);
x_1218 = lean_ctor_get(x_1215, 1);
lean_inc(x_1218);
lean_dec(x_1215);
x_1219 = l_Lean_Meta_intro1(x_1218, x_1213, x_13, x_1216);
if (lean_obj_tag(x_1219) == 0)
{
lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1246; uint8_t x_1247; 
x_1220 = lean_ctor_get(x_1219, 0);
lean_inc(x_1220);
x_1221 = lean_ctor_get(x_1219, 1);
lean_inc(x_1221);
lean_dec(x_1219);
x_1222 = lean_ctor_get(x_1220, 0);
lean_inc(x_1222);
x_1223 = lean_ctor_get(x_1220, 1);
lean_inc(x_1223);
lean_dec(x_1220);
x_1224 = lean_box(0);
x_1225 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_1194, x_1217, x_1194, x_1190, x_1224);
lean_dec(x_1194);
x_1246 = lean_ctor_get(x_1221, 4);
lean_inc(x_1246);
x_1247 = lean_ctor_get_uint8(x_1246, sizeof(void*)*1);
lean_dec(x_1246);
if (x_1247 == 0)
{
x_1226 = x_1221;
goto block_1245;
}
else
{
lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; uint8_t x_1251; 
x_1248 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1249 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1248, x_13, x_1221);
x_1250 = lean_ctor_get(x_1249, 0);
lean_inc(x_1250);
x_1251 = lean_unbox(x_1250);
lean_dec(x_1250);
if (x_1251 == 0)
{
lean_object* x_1252; 
x_1252 = lean_ctor_get(x_1249, 1);
lean_inc(x_1252);
lean_dec(x_1249);
x_1226 = x_1252;
goto block_1245;
}
else
{
lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; 
x_1253 = lean_ctor_get(x_1249, 1);
lean_inc(x_1253);
lean_dec(x_1249);
lean_inc(x_1223);
x_1254 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1254, 0, x_1223);
x_1255 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_1256 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1256, 0, x_1255);
lean_ctor_set(x_1256, 1, x_1254);
x_1257 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1248, x_1256, x_13, x_1253);
x_1258 = lean_ctor_get(x_1257, 1);
lean_inc(x_1258);
lean_dec(x_1257);
x_1226 = x_1258;
goto block_1245;
}
}
block_1245:
{
lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; 
x_1227 = x_1217;
x_1228 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1190, x_1227);
x_1229 = x_1228;
lean_inc(x_1222);
x_1230 = l_Lean_mkFVar(x_1222);
lean_inc(x_1223);
x_1231 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_1231, 0, x_1223);
x_1232 = lean_box(x_1199);
lean_inc(x_1223);
x_1233 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_1233, 0, x_1222);
lean_closure_set(x_1233, 1, x_8);
lean_closure_set(x_1233, 2, x_1223);
lean_closure_set(x_1233, 3, x_3);
lean_closure_set(x_1233, 4, x_4);
lean_closure_set(x_1233, 5, x_6);
lean_closure_set(x_1233, 6, x_7);
lean_closure_set(x_1233, 7, x_1181);
lean_closure_set(x_1233, 8, x_1232);
lean_closure_set(x_1233, 9, x_1209);
lean_closure_set(x_1233, 10, x_1225);
lean_closure_set(x_1233, 11, x_1229);
lean_closure_set(x_1233, 12, x_1230);
x_1234 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_1234, 0, x_1231);
lean_closure_set(x_1234, 1, x_1233);
x_1235 = l_Lean_Meta_getMVarDecl(x_1223, x_13, x_1226);
if (lean_obj_tag(x_1235) == 0)
{
lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; 
x_1236 = lean_ctor_get(x_1235, 0);
lean_inc(x_1236);
x_1237 = lean_ctor_get(x_1235, 1);
lean_inc(x_1237);
lean_dec(x_1235);
x_1238 = lean_ctor_get(x_1236, 1);
lean_inc(x_1238);
x_1239 = lean_ctor_get(x_1236, 4);
lean_inc(x_1239);
lean_dec(x_1236);
x_1240 = l_Lean_Meta_withLocalContext___rarg(x_1238, x_1239, x_1234, x_13, x_1237);
lean_dec(x_13);
return x_1240;
}
else
{
uint8_t x_1241; 
lean_dec(x_1234);
lean_dec(x_13);
x_1241 = !lean_is_exclusive(x_1235);
if (x_1241 == 0)
{
return x_1235;
}
else
{
lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; 
x_1242 = lean_ctor_get(x_1235, 0);
x_1243 = lean_ctor_get(x_1235, 1);
lean_inc(x_1243);
lean_inc(x_1242);
lean_dec(x_1235);
x_1244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1244, 0, x_1242);
lean_ctor_set(x_1244, 1, x_1243);
return x_1244;
}
}
}
}
else
{
uint8_t x_1259; 
lean_dec(x_1217);
lean_dec(x_1209);
lean_dec(x_1194);
lean_dec(x_1181);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1259 = !lean_is_exclusive(x_1219);
if (x_1259 == 0)
{
return x_1219;
}
else
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; 
x_1260 = lean_ctor_get(x_1219, 0);
x_1261 = lean_ctor_get(x_1219, 1);
lean_inc(x_1261);
lean_inc(x_1260);
lean_dec(x_1219);
x_1262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1262, 0, x_1260);
lean_ctor_set(x_1262, 1, x_1261);
return x_1262;
}
}
}
else
{
uint8_t x_1263; 
lean_dec(x_1209);
lean_dec(x_1194);
lean_dec(x_1181);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1263 = !lean_is_exclusive(x_1214);
if (x_1263 == 0)
{
return x_1214;
}
else
{
lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; 
x_1264 = lean_ctor_get(x_1214, 0);
x_1265 = lean_ctor_get(x_1214, 1);
lean_inc(x_1265);
lean_inc(x_1264);
lean_dec(x_1214);
x_1266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1266, 0, x_1264);
lean_ctor_set(x_1266, 1, x_1265);
return x_1266;
}
}
}
else
{
uint8_t x_1267; 
lean_dec(x_1194);
lean_dec(x_1181);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1267 = !lean_is_exclusive(x_1206);
if (x_1267 == 0)
{
return x_1206;
}
else
{
lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; 
x_1268 = lean_ctor_get(x_1206, 0);
x_1269 = lean_ctor_get(x_1206, 1);
lean_inc(x_1269);
lean_inc(x_1268);
lean_dec(x_1206);
x_1270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1270, 0, x_1268);
lean_ctor_set(x_1270, 1, x_1269);
return x_1270;
}
}
}
}
else
{
uint8_t x_1285; 
lean_dec(x_1194);
lean_dec(x_1184);
lean_dec(x_1181);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1285 = !lean_is_exclusive(x_1196);
if (x_1285 == 0)
{
return x_1196;
}
else
{
lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; 
x_1286 = lean_ctor_get(x_1196, 0);
x_1287 = lean_ctor_get(x_1196, 1);
lean_inc(x_1287);
lean_inc(x_1286);
lean_dec(x_1196);
x_1288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1288, 0, x_1286);
lean_ctor_set(x_1288, 1, x_1287);
return x_1288;
}
}
}
else
{
uint8_t x_1289; 
lean_dec(x_1184);
lean_dec(x_1181);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1289 = !lean_is_exclusive(x_1193);
if (x_1289 == 0)
{
return x_1193;
}
else
{
lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; 
x_1290 = lean_ctor_get(x_1193, 0);
x_1291 = lean_ctor_get(x_1193, 1);
lean_inc(x_1291);
lean_inc(x_1290);
lean_dec(x_1193);
x_1292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1292, 0, x_1290);
lean_ctor_set(x_1292, 1, x_1291);
return x_1292;
}
}
}
else
{
uint8_t x_1293; 
lean_dec(x_1181);
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
x_1293 = !lean_is_exclusive(x_1182);
if (x_1293 == 0)
{
return x_1182;
}
else
{
lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; 
x_1294 = lean_ctor_get(x_1182, 0);
x_1295 = lean_ctor_get(x_1182, 1);
lean_inc(x_1295);
lean_inc(x_1294);
lean_dec(x_1182);
x_1296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1296, 0, x_1294);
lean_ctor_set(x_1296, 1, x_1295);
return x_1296;
}
}
}
default: 
{
lean_object* x_1297; lean_object* x_1298; 
lean_dec(x_12);
lean_dec(x_10);
x_1297 = lean_ctor_get(x_7, 5);
lean_inc(x_1297);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1298 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_1297, x_13, x_14);
if (lean_obj_tag(x_1298) == 0)
{
lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; 
x_1299 = lean_ctor_get(x_1298, 1);
lean_inc(x_1299);
lean_dec(x_1298);
x_1300 = lean_ctor_get(x_1299, 1);
lean_inc(x_1300);
x_1301 = lean_ctor_get(x_7, 6);
lean_inc(x_1301);
x_1302 = l_List_redLength___main___rarg(x_1301);
x_1303 = lean_mk_empty_array_with_capacity(x_1302);
lean_dec(x_1302);
lean_inc(x_1301);
x_1304 = l_List_toArrayAux___main___rarg(x_1301, x_1303);
x_1305 = x_1304;
x_1306 = lean_unsigned_to_nat(0u);
lean_inc(x_1300);
lean_inc(x_6);
lean_inc(x_1);
x_1307 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 10, 8);
lean_closure_set(x_1307, 0, x_1);
lean_closure_set(x_1307, 1, x_6);
lean_closure_set(x_1307, 2, x_9);
lean_closure_set(x_1307, 3, x_11);
lean_closure_set(x_1307, 4, x_1300);
lean_closure_set(x_1307, 5, x_1301);
lean_closure_set(x_1307, 6, x_1306);
lean_closure_set(x_1307, 7, x_1305);
x_1308 = x_1307;
lean_inc(x_13);
x_1309 = lean_apply_2(x_1308, x_13, x_1299);
if (lean_obj_tag(x_1309) == 0)
{
lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; 
x_1310 = lean_ctor_get(x_1309, 0);
lean_inc(x_1310);
x_1311 = lean_ctor_get(x_1309, 1);
lean_inc(x_1311);
lean_dec(x_1309);
lean_inc(x_1);
x_1312 = l_Lean_Meta_getMVarType(x_1, x_13, x_1311);
if (lean_obj_tag(x_1312) == 0)
{
lean_object* x_1313; lean_object* x_1314; uint8_t x_1315; lean_object* x_1316; 
x_1313 = lean_ctor_get(x_1312, 0);
lean_inc(x_1313);
x_1314 = lean_ctor_get(x_1312, 1);
lean_inc(x_1314);
lean_dec(x_1312);
x_1315 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_1315 == 0)
{
lean_object* x_1388; uint8_t x_1389; 
x_1388 = l_Lean_MetavarContext_exprDependsOn(x_1300, x_1313, x_2);
x_1389 = lean_unbox(x_1388);
lean_dec(x_1388);
if (x_1389 == 0)
{
x_1316 = x_1314;
goto block_1387;
}
else
{
lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; uint8_t x_1397; 
lean_dec(x_1310);
lean_dec(x_1297);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_1390 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1390, 0, x_3);
x_1391 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1392 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1392, 0, x_1391);
lean_ctor_set(x_1392, 1, x_1390);
x_1393 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_1394 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1394, 0, x_1392);
lean_ctor_set(x_1394, 1, x_1393);
x_1395 = lean_box(0);
x_1396 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1394, x_1395, x_13, x_1314);
lean_dec(x_13);
x_1397 = !lean_is_exclusive(x_1396);
if (x_1397 == 0)
{
return x_1396;
}
else
{
lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; 
x_1398 = lean_ctor_get(x_1396, 0);
x_1399 = lean_ctor_get(x_1396, 1);
lean_inc(x_1399);
lean_inc(x_1398);
lean_dec(x_1396);
x_1400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1400, 0, x_1398);
lean_ctor_set(x_1400, 1, x_1399);
return x_1400;
}
}
}
else
{
lean_dec(x_1313);
lean_dec(x_1300);
x_1316 = x_1314;
goto block_1387;
}
block_1387:
{
lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; uint8_t x_1321; lean_object* x_1322; 
lean_inc(x_1310);
x_1317 = x_1310;
x_1318 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1306, x_1317);
x_1319 = x_1318;
x_1320 = lean_array_push(x_1319, x_2);
x_1321 = 1;
x_1322 = l_Lean_Meta_revert(x_1, x_1320, x_1321, x_13, x_1316);
if (lean_obj_tag(x_1322) == 0)
{
lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; uint8_t x_1329; lean_object* x_1330; 
x_1323 = lean_ctor_get(x_1322, 0);
lean_inc(x_1323);
x_1324 = lean_ctor_get(x_1322, 1);
lean_inc(x_1324);
lean_dec(x_1322);
x_1325 = lean_ctor_get(x_1323, 0);
lean_inc(x_1325);
x_1326 = lean_ctor_get(x_1323, 1);
lean_inc(x_1326);
lean_dec(x_1323);
x_1327 = lean_array_get_size(x_1310);
x_1328 = lean_box(0);
x_1329 = 0;
x_1330 = l_Lean_Meta_introN(x_1326, x_1327, x_1328, x_1329, x_13, x_1324);
if (lean_obj_tag(x_1330) == 0)
{
lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; 
x_1331 = lean_ctor_get(x_1330, 0);
lean_inc(x_1331);
x_1332 = lean_ctor_get(x_1330, 1);
lean_inc(x_1332);
lean_dec(x_1330);
x_1333 = lean_ctor_get(x_1331, 0);
lean_inc(x_1333);
x_1334 = lean_ctor_get(x_1331, 1);
lean_inc(x_1334);
lean_dec(x_1331);
x_1335 = l_Lean_Meta_intro1(x_1334, x_1329, x_13, x_1332);
if (lean_obj_tag(x_1335) == 0)
{
lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1362; uint8_t x_1363; 
x_1336 = lean_ctor_get(x_1335, 0);
lean_inc(x_1336);
x_1337 = lean_ctor_get(x_1335, 1);
lean_inc(x_1337);
lean_dec(x_1335);
x_1338 = lean_ctor_get(x_1336, 0);
lean_inc(x_1338);
x_1339 = lean_ctor_get(x_1336, 1);
lean_inc(x_1339);
lean_dec(x_1336);
x_1340 = lean_box(0);
x_1341 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_1310, x_1333, x_1310, x_1306, x_1340);
lean_dec(x_1310);
x_1362 = lean_ctor_get(x_1337, 4);
lean_inc(x_1362);
x_1363 = lean_ctor_get_uint8(x_1362, sizeof(void*)*1);
lean_dec(x_1362);
if (x_1363 == 0)
{
x_1342 = x_1337;
goto block_1361;
}
else
{
lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; uint8_t x_1367; 
x_1364 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1365 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1364, x_13, x_1337);
x_1366 = lean_ctor_get(x_1365, 0);
lean_inc(x_1366);
x_1367 = lean_unbox(x_1366);
lean_dec(x_1366);
if (x_1367 == 0)
{
lean_object* x_1368; 
x_1368 = lean_ctor_get(x_1365, 1);
lean_inc(x_1368);
lean_dec(x_1365);
x_1342 = x_1368;
goto block_1361;
}
else
{
lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
x_1369 = lean_ctor_get(x_1365, 1);
lean_inc(x_1369);
lean_dec(x_1365);
lean_inc(x_1339);
x_1370 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1370, 0, x_1339);
x_1371 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_1372 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1372, 0, x_1371);
lean_ctor_set(x_1372, 1, x_1370);
x_1373 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1364, x_1372, x_13, x_1369);
x_1374 = lean_ctor_get(x_1373, 1);
lean_inc(x_1374);
lean_dec(x_1373);
x_1342 = x_1374;
goto block_1361;
}
}
block_1361:
{
lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; 
x_1343 = x_1333;
x_1344 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1306, x_1343);
x_1345 = x_1344;
lean_inc(x_1338);
x_1346 = l_Lean_mkFVar(x_1338);
lean_inc(x_1339);
x_1347 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_1347, 0, x_1339);
x_1348 = lean_box(x_1315);
lean_inc(x_1339);
x_1349 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 16, 13);
lean_closure_set(x_1349, 0, x_1338);
lean_closure_set(x_1349, 1, x_8);
lean_closure_set(x_1349, 2, x_1339);
lean_closure_set(x_1349, 3, x_3);
lean_closure_set(x_1349, 4, x_4);
lean_closure_set(x_1349, 5, x_6);
lean_closure_set(x_1349, 6, x_7);
lean_closure_set(x_1349, 7, x_1297);
lean_closure_set(x_1349, 8, x_1348);
lean_closure_set(x_1349, 9, x_1325);
lean_closure_set(x_1349, 10, x_1341);
lean_closure_set(x_1349, 11, x_1345);
lean_closure_set(x_1349, 12, x_1346);
x_1350 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_1350, 0, x_1347);
lean_closure_set(x_1350, 1, x_1349);
x_1351 = l_Lean_Meta_getMVarDecl(x_1339, x_13, x_1342);
if (lean_obj_tag(x_1351) == 0)
{
lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; 
x_1352 = lean_ctor_get(x_1351, 0);
lean_inc(x_1352);
x_1353 = lean_ctor_get(x_1351, 1);
lean_inc(x_1353);
lean_dec(x_1351);
x_1354 = lean_ctor_get(x_1352, 1);
lean_inc(x_1354);
x_1355 = lean_ctor_get(x_1352, 4);
lean_inc(x_1355);
lean_dec(x_1352);
x_1356 = l_Lean_Meta_withLocalContext___rarg(x_1354, x_1355, x_1350, x_13, x_1353);
lean_dec(x_13);
return x_1356;
}
else
{
uint8_t x_1357; 
lean_dec(x_1350);
lean_dec(x_13);
x_1357 = !lean_is_exclusive(x_1351);
if (x_1357 == 0)
{
return x_1351;
}
else
{
lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; 
x_1358 = lean_ctor_get(x_1351, 0);
x_1359 = lean_ctor_get(x_1351, 1);
lean_inc(x_1359);
lean_inc(x_1358);
lean_dec(x_1351);
x_1360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1360, 0, x_1358);
lean_ctor_set(x_1360, 1, x_1359);
return x_1360;
}
}
}
}
else
{
uint8_t x_1375; 
lean_dec(x_1333);
lean_dec(x_1325);
lean_dec(x_1310);
lean_dec(x_1297);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1375 = !lean_is_exclusive(x_1335);
if (x_1375 == 0)
{
return x_1335;
}
else
{
lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; 
x_1376 = lean_ctor_get(x_1335, 0);
x_1377 = lean_ctor_get(x_1335, 1);
lean_inc(x_1377);
lean_inc(x_1376);
lean_dec(x_1335);
x_1378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1378, 0, x_1376);
lean_ctor_set(x_1378, 1, x_1377);
return x_1378;
}
}
}
else
{
uint8_t x_1379; 
lean_dec(x_1325);
lean_dec(x_1310);
lean_dec(x_1297);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1379 = !lean_is_exclusive(x_1330);
if (x_1379 == 0)
{
return x_1330;
}
else
{
lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; 
x_1380 = lean_ctor_get(x_1330, 0);
x_1381 = lean_ctor_get(x_1330, 1);
lean_inc(x_1381);
lean_inc(x_1380);
lean_dec(x_1330);
x_1382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1382, 0, x_1380);
lean_ctor_set(x_1382, 1, x_1381);
return x_1382;
}
}
}
else
{
uint8_t x_1383; 
lean_dec(x_1310);
lean_dec(x_1297);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1383 = !lean_is_exclusive(x_1322);
if (x_1383 == 0)
{
return x_1322;
}
else
{
lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; 
x_1384 = lean_ctor_get(x_1322, 0);
x_1385 = lean_ctor_get(x_1322, 1);
lean_inc(x_1385);
lean_inc(x_1384);
lean_dec(x_1322);
x_1386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1386, 0, x_1384);
lean_ctor_set(x_1386, 1, x_1385);
return x_1386;
}
}
}
}
else
{
uint8_t x_1401; 
lean_dec(x_1310);
lean_dec(x_1300);
lean_dec(x_1297);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1401 = !lean_is_exclusive(x_1312);
if (x_1401 == 0)
{
return x_1312;
}
else
{
lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; 
x_1402 = lean_ctor_get(x_1312, 0);
x_1403 = lean_ctor_get(x_1312, 1);
lean_inc(x_1403);
lean_inc(x_1402);
lean_dec(x_1312);
x_1404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1404, 0, x_1402);
lean_ctor_set(x_1404, 1, x_1403);
return x_1404;
}
}
}
else
{
uint8_t x_1405; 
lean_dec(x_1300);
lean_dec(x_1297);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1405 = !lean_is_exclusive(x_1309);
if (x_1405 == 0)
{
return x_1309;
}
else
{
lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; 
x_1406 = lean_ctor_get(x_1309, 0);
x_1407 = lean_ctor_get(x_1309, 1);
lean_inc(x_1407);
lean_inc(x_1406);
lean_dec(x_1309);
x_1408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1408, 0, x_1406);
lean_ctor_set(x_1408, 1, x_1407);
return x_1408;
}
}
}
else
{
uint8_t x_1409; 
lean_dec(x_1297);
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
x_1409 = !lean_is_exclusive(x_1298);
if (x_1409 == 0)
{
return x_1298;
}
else
{
lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; 
x_1410 = lean_ctor_get(x_1298, 0);
x_1411 = lean_ctor_get(x_1298, 1);
lean_inc(x_1411);
lean_inc(x_1410);
lean_dec(x_1298);
x_1412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1412, 0, x_1410);
lean_ctor_set(x_1412, 1, x_1411);
return x_1412;
}
}
}
}
}
}
lean_object* l_Lean_Meta_induction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_1);
x_10 = l_Lean_Meta_getLocalDecl(x_1, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
lean_inc(x_8);
lean_inc(x_2);
x_14 = l_Lean_Meta_mkRecursorInfo(x_2, x_13, x_8, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_LocalDecl_type(x_11);
lean_dec(x_11);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_8);
lean_inc(x_17);
x_19 = l_Lean_Meta_whnfUntil(x_17, x_18, x_8, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(x_3, x_17, x_8, x_21);
lean_dec(x_8);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_17);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Expr_getAppNumArgsAux___main(x_24, x_25);
x_27 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_26);
x_28 = lean_mk_array(x_26, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_26, x_29);
lean_dec(x_26);
lean_inc(x_24);
x_31 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(x_3, x_1, x_2, x_4, x_5, x_6, x_15, x_18, x_24, x_24, x_28, x_30, x_8, x_23);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
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
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
return x_14;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_14, 0);
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_14);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
lean_object* l_Lean_Meta_induction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 4, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_induction___lambda__1___boxed), 9, 6);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_1);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_10);
lean_closure_set(x_11, 5, x_8);
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_getMVarDecl(x_1, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 4);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Meta_withLocalContext___rarg(x_16, x_17, x_12, x_6, x_15);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
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
x_17 = lean_unbox(x_9);
lean_dec(x_9);
x_18 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_18;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_15;
}
}
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_induction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_5);
return x_10;
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
