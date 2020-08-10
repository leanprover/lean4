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
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__4;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity(lean_object*);
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_Meta_induction___spec__2(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__5;
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_Lean_Level_Inhabited;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__4;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__9;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___boxed(lean_object**);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___boxed(lean_object**);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
extern lean_object* l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__3;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__2;
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__7;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_elem___main___at_Lean_Meta_induction___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7;
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__2;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__9;
lean_object* l_Lean_Meta_getMVarType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__8;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__2;
lean_object* l_Lean_MetavarContext_localDeclDependsOn(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__7;
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InductionSubgoal_inhabited___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__6;
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___boxed(lean_object**);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__4;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__6;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__3;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__5;
extern lean_object* l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__6;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isClassQuick___main___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
lean_object* l_Lean_Meta_whnfUntil(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__7;
lean_object* l_Lean_Meta_induction(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_nat_dec_le(x_8, x_11);
if (x_63 == 0)
{
x_64 = x_62;
goto block_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
lean_dec(x_61);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_200 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_201 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_202 = lean_box(0);
x_203 = l_Lean_Meta_throwTacticEx___rarg(x_200, x_1, x_201, x_202, x_16, x_62);
lean_dec(x_16);
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
return x_203;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_203, 0);
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_203);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
block_199:
{
if (lean_obj_tag(x_19) == 7)
{
lean_object* x_65; lean_object* x_66; uint64_t x_67; lean_object* x_68; lean_object* x_69; uint8_t x_148; uint8_t x_149; 
x_65 = lean_ctor_get(x_19, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_19, 1);
lean_inc(x_66);
x_67 = lean_ctor_get_uint64(x_19, sizeof(void*)*3);
x_68 = l_Lean_Expr_headBeta(x_66);
x_148 = (uint8_t)((x_67 << 24) >> 61);
x_149 = l_Lean_BinderInfo_isInstImplicit(x_148);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_box(0);
x_69 = x_150;
goto block_147;
}
else
{
uint8_t x_151; 
x_151 = l_Array_isEmpty___rarg(x_2);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_box(0);
x_69 = x_152;
goto block_147;
}
else
{
lean_object* x_153; 
lean_inc(x_16);
lean_inc(x_68);
x_153 = l_Lean_Meta_synthInstance_x3f(x_68, x_16, x_64);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = l_Lean_Name_append___main(x_61, x_65);
lean_dec(x_61);
x_157 = 2;
lean_inc(x_16);
x_158 = l_Lean_Meta_mkFreshExprMVar(x_68, x_156, x_157, x_16, x_155);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_159);
x_161 = l_Lean_mkApp(x_12, x_159);
lean_inc(x_16);
lean_inc(x_1);
x_162 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_19, x_159, x_16, x_160);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_unsigned_to_nat(1u);
x_166 = lean_nat_add(x_10, x_165);
lean_dec(x_10);
x_167 = lean_nat_add(x_11, x_165);
lean_dec(x_11);
x_168 = l_Lean_Expr_mvarId_x21(x_159);
lean_dec(x_159);
x_169 = lean_box(0);
x_170 = l_Array_empty___closed__1;
x_171 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_170);
lean_ctor_set(x_171, 2, x_169);
x_172 = lean_array_push(x_15, x_171);
x_10 = x_166;
x_11 = x_167;
x_12 = x_161;
x_13 = x_163;
x_15 = x_172;
x_17 = x_164;
goto _start;
}
else
{
uint8_t x_174; 
lean_dec(x_161);
lean_dec(x_159);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_174 = !lean_is_exclusive(x_162);
if (x_174 == 0)
{
return x_162;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_162, 0);
x_176 = lean_ctor_get(x_162, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_162);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_68);
lean_dec(x_65);
lean_dec(x_61);
x_178 = lean_ctor_get(x_153, 1);
lean_inc(x_178);
lean_dec(x_153);
x_179 = lean_ctor_get(x_154, 0);
lean_inc(x_179);
lean_dec(x_154);
lean_inc(x_179);
x_180 = l_Lean_mkApp(x_12, x_179);
lean_inc(x_16);
lean_inc(x_1);
x_181 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_19, x_179, x_16, x_178);
lean_dec(x_179);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_unsigned_to_nat(1u);
x_185 = lean_nat_add(x_10, x_184);
lean_dec(x_10);
x_186 = lean_nat_add(x_11, x_184);
lean_dec(x_11);
x_10 = x_185;
x_11 = x_186;
x_12 = x_180;
x_13 = x_182;
x_17 = x_183;
goto _start;
}
else
{
uint8_t x_188; 
lean_dec(x_180);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_181);
if (x_188 == 0)
{
return x_181;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_181, 0);
x_190 = lean_ctor_get(x_181, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_181);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_68);
lean_dec(x_65);
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
x_192 = !lean_is_exclusive(x_153);
if (x_192 == 0)
{
return x_153;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_153, 0);
x_194 = lean_ctor_get(x_153, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_153);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
block_147:
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_69);
lean_inc(x_68);
x_70 = l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_68);
x_71 = lean_nat_dec_lt(x_70, x_6);
x_72 = lean_nat_sub(x_70, x_6);
lean_dec(x_70);
x_73 = lean_array_get_size(x_4);
x_74 = lean_array_get_size(x_7);
x_75 = lean_nat_sub(x_73, x_74);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_sub(x_75, x_76);
lean_dec(x_75);
x_78 = lean_array_get_size(x_2);
x_79 = lean_nat_dec_lt(x_11, x_78);
lean_dec(x_78);
x_80 = l_Lean_Name_append___main(x_61, x_65);
lean_dec(x_61);
if (x_79 == 0)
{
lean_object* x_145; 
x_145 = lean_box(0);
x_81 = x_145;
goto block_144;
}
else
{
lean_object* x_146; 
x_146 = lean_array_fget(x_2, x_11);
x_81 = x_146;
goto block_144;
}
block_144:
{
lean_object* x_82; 
if (x_71 == 0)
{
x_82 = x_64;
goto block_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_68);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_136 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_137 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_138 = lean_box(0);
x_139 = l_Lean_Meta_throwTacticEx___rarg(x_136, x_1, x_137, x_138, x_16, x_64);
lean_dec(x_16);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
return x_139;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_139, 0);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_139);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
block_135:
{
uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = 2;
lean_inc(x_16);
x_84 = l_Lean_Meta_mkFreshExprMVar(x_68, x_80, x_83, x_16, x_82);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_85);
x_87 = l_Lean_mkApp(x_12, x_85);
lean_inc(x_16);
lean_inc(x_1);
x_88 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_19, x_85, x_16, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Expr_mvarId_x21(x_85);
lean_dec(x_85);
x_92 = l_Lean_Expr_fvarId_x21(x_5);
x_93 = l_Lean_Meta_tryClear(x_91, x_92, x_16, x_90);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = 1;
x_97 = l_Lean_Meta_introN(x_94, x_72, x_81, x_96, x_16, x_95);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; 
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
x_102 = lean_box(0);
x_103 = 0;
x_104 = l_Lean_Meta_introN(x_101, x_77, x_102, x_103, x_16, x_99);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
lean_inc(x_9);
lean_inc(x_73);
x_109 = l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(x_4, x_7, x_74, x_107, x_73, x_73, x_9);
lean_dec(x_73);
lean_dec(x_107);
lean_dec(x_74);
x_110 = x_100;
x_111 = lean_unsigned_to_nat(0u);
x_112 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_111, x_110);
x_113 = x_112;
x_114 = lean_nat_add(x_10, x_76);
lean_dec(x_10);
x_115 = lean_nat_add(x_11, x_76);
lean_dec(x_11);
x_116 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_116, 0, x_108);
lean_ctor_set(x_116, 1, x_113);
lean_ctor_set(x_116, 2, x_109);
x_117 = lean_array_push(x_15, x_116);
x_10 = x_114;
x_11 = x_115;
x_12 = x_87;
x_13 = x_89;
x_15 = x_117;
x_17 = x_106;
goto _start;
}
else
{
uint8_t x_119; 
lean_dec(x_100);
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_104);
if (x_119 == 0)
{
return x_104;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_104, 0);
x_121 = lean_ctor_get(x_104, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_104);
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
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_97);
if (x_123 == 0)
{
return x_97;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_97, 0);
x_125 = lean_ctor_get(x_97, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_97);
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
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_81);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_93);
if (x_127 == 0)
{
return x_93;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_93, 0);
x_129 = lean_ctor_get(x_93, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_93);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_81);
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_88);
if (x_131 == 0)
{
return x_88;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_88, 0);
x_133 = lean_ctor_get(x_88, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_88);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_61);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_196 = l_Lean_Meta_isClassQuick___main___closed__1;
x_197 = l_unreachable_x21___rarg(x_196);
x_198 = lean_apply_2(x_197, x_16, x_64);
return x_198;
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_60);
if (x_208 == 0)
{
return x_60;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_60, 0);
x_210 = lean_ctor_get(x_60, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_60);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_12);
lean_ctor_set(x_212, 1, x_19);
x_213 = lean_unsigned_to_nat(0u);
lean_inc(x_16);
lean_inc(x_1);
x_214 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(x_1, x_7, x_7, x_213, x_212, x_16, x_20);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
lean_dec(x_215);
lean_inc(x_5);
x_219 = l_Lean_mkApp(x_217, x_5);
lean_inc(x_16);
lean_inc(x_1);
x_220 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_218, x_5, x_16, x_216);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_unsigned_to_nat(1u);
x_224 = lean_nat_add(x_10, x_223);
lean_dec(x_10);
x_225 = lean_array_get_size(x_7);
x_226 = lean_nat_add(x_224, x_225);
lean_dec(x_225);
lean_dec(x_224);
x_227 = 1;
x_10 = x_226;
x_12 = x_219;
x_13 = x_221;
x_14 = x_227;
x_17 = x_222;
goto _start;
}
else
{
uint8_t x_229; 
lean_dec(x_219);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_229 = !lean_is_exclusive(x_220);
if (x_229 == 0)
{
return x_220;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_220, 0);
x_231 = lean_ctor_get(x_220, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_220);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
else
{
uint8_t x_233; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_233 = !lean_is_exclusive(x_214);
if (x_233 == 0)
{
return x_214;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_214, 0);
x_235 = lean_ctor_get(x_214, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_214);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
}
}
}
else
{
uint8_t x_237; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_237 = !lean_is_exclusive(x_18);
if (x_237 == 0)
{
return x_18;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_18, 0);
x_239 = lean_ctor_get(x_18, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_18);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
return x_240;
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_11, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_11, x_16);
lean_dec(x_11);
x_18 = lean_nat_sub(x_10, x_17);
x_19 = lean_nat_sub(x_18, x_16);
lean_dec(x_18);
x_20 = l_Lean_Expr_Inhabited;
x_21 = lean_array_get(x_20, x_5, x_19);
x_22 = lean_nat_dec_eq(x_19, x_8);
x_23 = lean_nat_dec_lt(x_19, x_8);
x_24 = lean_nat_dec_lt(x_8, x_19);
if (x_22 == 0)
{
uint8_t x_110; 
x_110 = lean_expr_eqv(x_21, x_9);
x_25 = x_110;
goto block_109;
}
else
{
uint8_t x_111; 
x_111 = 0;
x_25 = x_111;
goto block_109;
}
block_109:
{
uint8_t x_26; 
if (x_25 == 0)
{
uint8_t x_107; 
x_107 = 0;
x_26 = x_107;
goto block_106;
}
else
{
uint8_t x_108; 
x_108 = 1;
x_26 = x_108;
goto block_106;
}
block_106:
{
uint8_t x_27; 
if (x_23 == 0)
{
uint8_t x_102; 
x_102 = 0;
x_27 = x_102;
goto block_101;
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = l_Lean_Expr_fvarId_x21(x_9);
lean_inc(x_21);
lean_inc(x_6);
x_104 = l_Lean_MetavarContext_exprDependsOn(x_6, x_21, x_103);
lean_dec(x_103);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
x_27 = x_105;
goto block_101;
}
block_101:
{
uint8_t x_28; 
if (x_27 == 0)
{
uint8_t x_99; 
x_99 = 0;
x_28 = x_99;
goto block_98;
}
else
{
uint8_t x_100; 
x_100 = 1;
x_28 = x_100;
goto block_98;
}
block_98:
{
uint8_t x_29; 
if (x_24 == 0)
{
uint8_t x_94; 
x_94 = 0;
x_29 = x_94;
goto block_93;
}
else
{
uint8_t x_95; 
x_95 = l_List_elem___main___at_Lean_Meta_induction___spec__2(x_19, x_7);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = 0;
x_29 = x_96;
goto block_93;
}
else
{
uint8_t x_97; 
x_97 = l_Lean_Expr_isFVar(x_21);
x_29 = x_97;
goto block_93;
}
}
block_93:
{
uint8_t x_30; 
if (x_29 == 0)
{
uint8_t x_91; 
x_91 = 0;
x_30 = x_91;
goto block_90;
}
else
{
uint8_t x_92; 
x_92 = 1;
x_30 = x_92;
goto block_90;
}
block_90:
{
lean_object* x_31; 
if (x_26 == 0)
{
if (x_28 == 0)
{
x_31 = x_13;
goto block_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_6);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_9);
x_63 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_64 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__6;
x_66 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_4);
x_68 = l_Lean_indentExpr(x_67);
x_69 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_box(0);
x_71 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_69, x_70, x_12, x_13);
lean_dec(x_12);
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
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_6);
x_76 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_76, 0, x_9);
x_77 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_78 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__9;
x_80 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_4);
x_82 = l_Lean_indentExpr(x_81);
x_83 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_box(0);
x_85 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_83, x_84, x_12, x_13);
lean_dec(x_12);
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
block_61:
{
if (x_30 == 0)
{
lean_dec(x_21);
lean_dec(x_19);
x_11 = x_17;
x_13 = x_31;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_Expr_fvarId_x21(x_9);
lean_inc(x_12);
x_34 = l_Lean_Meta_getLocalDecl(x_33, x_12, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Expr_fvarId_x21(x_21);
lean_dec(x_21);
lean_inc(x_6);
x_38 = l_Lean_MetavarContext_localDeclDependsOn(x_6, x_35, x_37);
lean_dec(x_37);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_dec(x_19);
x_11 = x_17;
x_13 = x_36;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_9);
x_42 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_43 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__3;
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_nat_add(x_19, x_16);
lean_dec(x_19);
x_47 = l_Nat_repr(x_46);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_box(0);
x_52 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_50, x_51, x_12, x_36);
lean_dec(x_12);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_34);
if (x_57 == 0)
{
return x_34;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_34, 0);
x_59 = lean_ctor_get(x_34, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_34);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_13);
return x_113;
}
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_11, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_11, x_16);
lean_dec(x_11);
x_18 = lean_nat_sub(x_10, x_17);
x_19 = lean_nat_sub(x_18, x_16);
lean_dec(x_18);
x_20 = l_Lean_Expr_Inhabited;
x_21 = lean_array_get(x_20, x_5, x_19);
x_22 = lean_nat_dec_eq(x_19, x_8);
x_23 = lean_nat_dec_lt(x_19, x_8);
x_24 = lean_nat_dec_lt(x_8, x_19);
if (x_22 == 0)
{
uint8_t x_110; 
x_110 = lean_expr_eqv(x_21, x_9);
x_25 = x_110;
goto block_109;
}
else
{
uint8_t x_111; 
x_111 = 0;
x_25 = x_111;
goto block_109;
}
block_109:
{
uint8_t x_26; 
if (x_25 == 0)
{
uint8_t x_107; 
x_107 = 0;
x_26 = x_107;
goto block_106;
}
else
{
uint8_t x_108; 
x_108 = 1;
x_26 = x_108;
goto block_106;
}
block_106:
{
uint8_t x_27; 
if (x_23 == 0)
{
uint8_t x_102; 
x_102 = 0;
x_27 = x_102;
goto block_101;
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = l_Lean_Expr_fvarId_x21(x_9);
lean_inc(x_21);
lean_inc(x_6);
x_104 = l_Lean_MetavarContext_exprDependsOn(x_6, x_21, x_103);
lean_dec(x_103);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
x_27 = x_105;
goto block_101;
}
block_101:
{
uint8_t x_28; 
if (x_27 == 0)
{
uint8_t x_99; 
x_99 = 0;
x_28 = x_99;
goto block_98;
}
else
{
uint8_t x_100; 
x_100 = 1;
x_28 = x_100;
goto block_98;
}
block_98:
{
uint8_t x_29; 
if (x_24 == 0)
{
uint8_t x_94; 
x_94 = 0;
x_29 = x_94;
goto block_93;
}
else
{
uint8_t x_95; 
x_95 = l_List_elem___main___at_Lean_Meta_induction___spec__2(x_19, x_7);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = 0;
x_29 = x_96;
goto block_93;
}
else
{
uint8_t x_97; 
x_97 = l_Lean_Expr_isFVar(x_21);
x_29 = x_97;
goto block_93;
}
}
block_93:
{
uint8_t x_30; 
if (x_29 == 0)
{
uint8_t x_91; 
x_91 = 0;
x_30 = x_91;
goto block_90;
}
else
{
uint8_t x_92; 
x_92 = 1;
x_30 = x_92;
goto block_90;
}
block_90:
{
lean_object* x_31; 
if (x_26 == 0)
{
if (x_28 == 0)
{
x_31 = x_13;
goto block_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_6);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_9);
x_63 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_64 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__6;
x_66 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_4);
x_68 = l_Lean_indentExpr(x_67);
x_69 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_box(0);
x_71 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_69, x_70, x_12, x_13);
lean_dec(x_12);
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
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_6);
x_76 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_76, 0, x_9);
x_77 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_78 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__9;
x_80 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_4);
x_82 = l_Lean_indentExpr(x_81);
x_83 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_box(0);
x_85 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_83, x_84, x_12, x_13);
lean_dec(x_12);
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
block_61:
{
if (x_30 == 0)
{
lean_dec(x_21);
lean_dec(x_19);
x_11 = x_17;
x_13 = x_31;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_Expr_fvarId_x21(x_9);
lean_inc(x_12);
x_34 = l_Lean_Meta_getLocalDecl(x_33, x_12, x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Expr_fvarId_x21(x_21);
lean_dec(x_21);
lean_inc(x_6);
x_38 = l_Lean_MetavarContext_localDeclDependsOn(x_6, x_35, x_37);
lean_dec(x_37);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_dec(x_19);
x_11 = x_17;
x_13 = x_36;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_9);
x_42 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_43 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__3;
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_nat_add(x_19, x_16);
lean_dec(x_19);
x_47 = l_Nat_repr(x_46);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_box(0);
x_52 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_50, x_51, x_12, x_36);
lean_dec(x_12);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
return x_52;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_34);
if (x_57 == 0)
{
return x_34;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_34, 0);
x_59 = lean_ctor_get(x_34, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_34);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_13);
return x_113;
}
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise type index ");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" is not variable ");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_9);
x_13 = lean_nat_dec_lt(x_8, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = x_9;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_16 = lean_array_fget(x_9, x_8);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_fset(x_9, x_8, x_17);
x_19 = x_16;
x_20 = lean_array_get_size(x_5);
x_21 = lean_nat_dec_le(x_20, x_19);
x_22 = l_Lean_Expr_Inhabited;
x_23 = lean_array_get(x_22, x_5, x_19);
x_24 = l_Lean_Expr_isFVar(x_23);
if (x_24 == 0)
{
uint8_t x_64; 
x_64 = 0;
x_25 = x_64;
goto block_63;
}
else
{
uint8_t x_65; 
x_65 = 1;
x_25 = x_65;
goto block_63;
}
block_63:
{
lean_object* x_26; 
if (x_21 == 0)
{
x_26 = x_11;
goto block_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_6);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_4);
x_54 = l_Lean_indentExpr(x_53);
x_55 = l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__3;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_box(0);
x_58 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_56, x_57, x_10, x_11);
lean_dec(x_10);
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
block_52:
{
if (x_25 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_6);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_23);
x_28 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__3;
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__6;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_4);
x_33 = l_Lean_indentExpr(x_32);
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_box(0);
x_36 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_34, x_35, x_10, x_26);
lean_dec(x_10);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_inc(x_10);
lean_inc(x_20);
lean_inc(x_23);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_41 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_19, x_23, x_20, x_20, x_10, x_26);
lean_dec(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_8, x_43);
x_45 = x_23;
x_46 = lean_array_fset(x_18, x_8, x_45);
lean_dec(x_8);
x_8 = x_44;
x_9 = x_46;
x_11 = x_42;
goto _start;
}
else
{
uint8_t x_48; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_41);
if (x_48 == 0)
{
return x_41;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_41, 0);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_6, 1);
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_array_get_size(x_4);
x_31 = lean_nat_dec_le(x_30, x_29);
lean_dec(x_30);
x_32 = l_Lean_Level_Inhabited;
x_33 = lean_array_get(x_32, x_4, x_29);
x_34 = lean_array_push(x_28, x_33);
lean_ctor_set(x_5, 0, x_34);
if (x_31 == 0)
{
x_6 = x_27;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_5);
lean_dec(x_3);
x_36 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_37 = lean_box(0);
x_38 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_36, x_37, x_7, x_8);
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
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
x_49 = l_Lean_Level_Inhabited;
x_50 = lean_array_get(x_49, x_4, x_46);
x_51 = lean_array_push(x_44, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
if (x_48 == 0)
{
x_5 = x_52;
x_6 = x_43;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_52);
lean_dec(x_3);
x_54 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_55 = lean_box(0);
x_56 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_54, x_55, x_7, x_8);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise is not of the form (C ...)");
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
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("recursor '");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' can only eliminate into Prop");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
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
x_25 = l_List_foldlM___main___at_Lean_Meta_induction___spec__7(x_3, x_8, x_13, x_22, x_24, x_23, x_17, x_18);
lean_dec(x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_85; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Array_toList___rarg(x_28);
lean_dec(x_28);
lean_inc(x_1);
x_31 = l_Lean_mkConst(x_1, x_30);
x_85 = lean_unbox(x_29);
lean_dec(x_29);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = l_Lean_Level_isZero(x_13);
lean_dec(x_13);
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = 1;
x_32 = x_87;
goto block_84;
}
else
{
uint8_t x_88; 
x_88 = 0;
x_32 = x_88;
goto block_84;
}
}
else
{
uint8_t x_89; 
lean_dec(x_13);
x_89 = 0;
x_32 = x_89;
goto block_84;
}
block_84:
{
uint8_t x_33; 
if (x_32 == 0)
{
uint8_t x_82; 
x_82 = 0;
x_33 = x_82;
goto block_81;
}
else
{
uint8_t x_83; 
x_83 = 1;
x_33 = x_83;
goto block_81;
}
block_81:
{
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_17);
lean_inc(x_8);
x_34 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(x_8, x_15, x_5, x_31, x_17, x_27);
lean_dec(x_15);
if (lean_obj_tag(x_34) == 0)
{
if (x_6 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_17);
lean_inc(x_10);
x_37 = l_Lean_Meta_mkLambda(x_10, x_12, x_17, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_mkApp(x_35, x_38);
x_41 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_40, x_17, x_39);
lean_dec(x_10);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_34, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
lean_dec(x_34);
x_48 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_11);
x_49 = lean_array_push(x_48, x_11);
lean_inc(x_17);
x_50 = l_Lean_Meta_mkLambda(x_49, x_12, x_17, x_47);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_17);
lean_inc(x_10);
x_53 = l_Lean_Meta_mkLambda(x_10, x_51, x_17, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_mkApp(x_46, x_54);
x_57 = l___private_Lean_Meta_Tactic_Induction_5__finalize(x_8, x_2, x_4, x_7, x_11, x_10, x_9, x_56, x_17, x_55);
lean_dec(x_10);
return x_57;
}
else
{
uint8_t x_58; 
lean_dec(x_46);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_58 = !lean_is_exclusive(x_53);
if (x_58 == 0)
{
return x_53;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_53, 0);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_53);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_46);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_62 = !lean_is_exclusive(x_50);
if (x_62 == 0)
{
return x_50;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_50, 0);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_50);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_66 = !lean_is_exclusive(x_34);
if (x_66 == 0)
{
return x_34;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_34, 0);
x_68 = lean_ctor_get(x_34, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_34);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_70 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_70, 0, x_1);
x_71 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_72 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__9;
x_74 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_box(0);
x_76 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_74, x_75, x_17, x_27);
lean_dec(x_17);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
return x_76;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_76);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
else
{
uint8_t x_90; 
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
x_90 = !lean_is_exclusive(x_25);
if (x_90 == 0)
{
return x_25;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_25, 0);
x_92 = lean_ctor_get(x_25, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_25);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
case 5:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_14, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_14, 1);
lean_inc(x_95);
lean_dec(x_14);
x_96 = lean_array_set(x_15, x_16, x_95);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_sub(x_16, x_97);
lean_dec(x_16);
x_14 = x_94;
x_15 = x_96;
x_16 = x_98;
goto _start;
}
default: 
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_100 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_101 = lean_box(0);
x_102 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_100, x_101, x_17, x_18);
lean_dec(x_17);
return x_102;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
x_36 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_13, x_14, x_18, x_29, x_33, x_35, x_15, x_28);
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
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after revert&intro");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__4;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not support dependent elimination, but conclusion depends on major premise");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_25 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_6);
lean_closure_set(x_25, 2, x_7);
lean_closure_set(x_25, 3, x_9);
lean_closure_set(x_25, 4, x_11);
lean_closure_set(x_25, 5, x_18);
lean_closure_set(x_25, 6, x_19);
lean_closure_set(x_25, 7, x_24);
lean_closure_set(x_25, 8, x_23);
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
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_28);
x_34 = x_28;
x_35 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_24, x_34);
x_36 = x_35;
lean_inc(x_2);
x_37 = lean_array_push(x_36, x_2);
if (x_33 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = l_Lean_MetavarContext_exprDependsOn(x_18, x_31, x_2);
lean_dec(x_2);
x_118 = lean_unbox(x_117);
lean_dec(x_117);
if (x_118 == 0)
{
x_38 = x_32;
goto block_116;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_37);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_119 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_119, 0, x_3);
x_120 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_121 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_123 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_box(0);
x_125 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_123, x_124, x_13, x_32);
lean_dec(x_13);
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
return x_125;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_125);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_18);
lean_dec(x_2);
x_38 = x_32;
goto block_116;
}
block_116:
{
uint8_t x_39; lean_object* x_40; 
x_39 = 1;
x_40 = l_Lean_Meta_revert(x_1, x_37, x_39, x_13, x_38);
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
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_97; uint8_t x_98; 
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
x_59 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_28, x_51, x_28, x_24, x_58);
lean_dec(x_28);
x_60 = x_51;
x_61 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_24, x_60);
x_62 = x_61;
lean_inc(x_56);
x_63 = l_Lean_mkFVar(x_56);
lean_inc(x_57);
x_64 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_64, 0, x_57);
x_65 = lean_box(x_33);
lean_inc(x_57);
x_66 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_66, 0, x_56);
lean_closure_set(x_66, 1, x_8);
lean_closure_set(x_66, 2, x_57);
lean_closure_set(x_66, 3, x_3);
lean_closure_set(x_66, 4, x_4);
lean_closure_set(x_66, 5, x_6);
lean_closure_set(x_66, 6, x_7);
lean_closure_set(x_66, 7, x_15);
lean_closure_set(x_66, 8, x_65);
lean_closure_set(x_66, 9, x_43);
lean_closure_set(x_66, 10, x_59);
lean_closure_set(x_66, 11, x_62);
lean_closure_set(x_66, 12, x_63);
x_67 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_67, 0, x_64);
lean_closure_set(x_67, 1, x_66);
x_97 = lean_ctor_get(x_55, 4);
lean_inc(x_97);
x_98 = lean_ctor_get_uint8(x_97, sizeof(void*)*1);
lean_dec(x_97);
if (x_98 == 0)
{
x_68 = x_47;
x_69 = x_55;
goto block_96;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_100 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_99, x_13, x_55);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_unbox(x_101);
lean_dec(x_101);
x_68 = x_103;
x_69 = x_102;
goto block_96;
}
block_96:
{
if (x_68 == 0)
{
lean_object* x_70; 
x_70 = l_Lean_Meta_getMVarDecl(x_57, x_13, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 4);
lean_inc(x_74);
lean_dec(x_71);
x_75 = l_Lean_Meta_withLocalContext___rarg(x_73, x_74, x_67, x_13, x_72);
lean_dec(x_13);
return x_75;
}
else
{
uint8_t x_76; 
lean_dec(x_67);
lean_dec(x_13);
x_76 = !lean_is_exclusive(x_70);
if (x_76 == 0)
{
return x_70;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_70, 0);
x_78 = lean_ctor_get(x_70, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_70);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_inc(x_57);
x_80 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_80, 0, x_57);
x_81 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_82 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_84 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_83, x_82, x_13, x_69);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l_Lean_Meta_getMVarDecl(x_57, x_13, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 4);
lean_inc(x_90);
lean_dec(x_87);
x_91 = l_Lean_Meta_withLocalContext___rarg(x_89, x_90, x_67, x_13, x_88);
lean_dec(x_13);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec(x_67);
lean_dec(x_13);
x_92 = !lean_is_exclusive(x_86);
if (x_92 == 0)
{
return x_86;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_86, 0);
x_94 = lean_ctor_get(x_86, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_86);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
else
{
uint8_t x_104; 
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
x_104 = !lean_is_exclusive(x_53);
if (x_104 == 0)
{
return x_53;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_53, 0);
x_106 = lean_ctor_get(x_53, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_53);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_43);
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_108 = !lean_is_exclusive(x_48);
if (x_108 == 0)
{
return x_48;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_48, 0);
x_110 = lean_ctor_get(x_48, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_48);
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
lean_dec(x_28);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_112 = !lean_is_exclusive(x_40);
if (x_112 == 0)
{
return x_40;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_40, 0);
x_114 = lean_ctor_get(x_40, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_40);
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
uint8_t x_130; 
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
x_130 = !lean_is_exclusive(x_30);
if (x_130 == 0)
{
return x_30;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_30, 0);
x_132 = lean_ctor_get(x_30, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_30);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
uint8_t x_134; 
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
x_134 = !lean_is_exclusive(x_27);
if (x_134 == 0)
{
return x_27;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_27, 0);
x_136 = lean_ctor_get(x_27, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_27);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
uint8_t x_138; 
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
x_138 = !lean_is_exclusive(x_16);
if (x_138 == 0)
{
return x_16;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_16, 0);
x_140 = lean_ctor_get(x_16, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_16);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
case 1:
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_12);
lean_dec(x_10);
x_142 = lean_ctor_get(x_7, 5);
lean_inc(x_142);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_143 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_142, x_13, x_14);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_7, 6);
lean_inc(x_146);
x_147 = l_List_redLength___main___rarg(x_146);
x_148 = lean_mk_empty_array_with_capacity(x_147);
lean_dec(x_147);
lean_inc(x_146);
x_149 = l_List_toArrayAux___main___rarg(x_146, x_148);
x_150 = x_149;
x_151 = lean_unsigned_to_nat(0u);
lean_inc(x_145);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_152 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_152, 0, x_1);
lean_closure_set(x_152, 1, x_6);
lean_closure_set(x_152, 2, x_7);
lean_closure_set(x_152, 3, x_9);
lean_closure_set(x_152, 4, x_11);
lean_closure_set(x_152, 5, x_145);
lean_closure_set(x_152, 6, x_146);
lean_closure_set(x_152, 7, x_151);
lean_closure_set(x_152, 8, x_150);
x_153 = x_152;
lean_inc(x_13);
x_154 = lean_apply_2(x_153, x_13, x_144);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
lean_inc(x_1);
x_157 = l_Lean_Meta_getMVarType(x_1, x_13, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_155);
x_161 = x_155;
x_162 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_151, x_161);
x_163 = x_162;
lean_inc(x_2);
x_164 = lean_array_push(x_163, x_2);
if (x_160 == 0)
{
lean_object* x_244; uint8_t x_245; 
x_244 = l_Lean_MetavarContext_exprDependsOn(x_145, x_158, x_2);
lean_dec(x_2);
x_245 = lean_unbox(x_244);
lean_dec(x_244);
if (x_245 == 0)
{
x_165 = x_159;
goto block_243;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
lean_dec(x_164);
lean_dec(x_155);
lean_dec(x_142);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_246 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_246, 0, x_3);
x_247 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_248 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_246);
x_249 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_250 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_box(0);
x_252 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_250, x_251, x_13, x_159);
lean_dec(x_13);
x_253 = !lean_is_exclusive(x_252);
if (x_253 == 0)
{
return x_252;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_252, 0);
x_255 = lean_ctor_get(x_252, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_252);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
else
{
lean_dec(x_158);
lean_dec(x_145);
lean_dec(x_2);
x_165 = x_159;
goto block_243;
}
block_243:
{
uint8_t x_166; lean_object* x_167; 
x_166 = 1;
x_167 = l_Lean_Meta_revert(x_1, x_164, x_166, x_13, x_165);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec(x_168);
x_172 = lean_array_get_size(x_155);
x_173 = lean_box(0);
x_174 = 0;
x_175 = l_Lean_Meta_introN(x_171, x_172, x_173, x_174, x_13, x_169);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = l_Lean_Meta_intro1(x_179, x_174, x_13, x_177);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_224; uint8_t x_225; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = lean_ctor_get(x_181, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_181, 1);
lean_inc(x_184);
lean_dec(x_181);
x_185 = lean_box(0);
x_186 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_155, x_178, x_155, x_151, x_185);
lean_dec(x_155);
x_187 = x_178;
x_188 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_151, x_187);
x_189 = x_188;
lean_inc(x_183);
x_190 = l_Lean_mkFVar(x_183);
lean_inc(x_184);
x_191 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_191, 0, x_184);
x_192 = lean_box(x_160);
lean_inc(x_184);
x_193 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_193, 0, x_183);
lean_closure_set(x_193, 1, x_8);
lean_closure_set(x_193, 2, x_184);
lean_closure_set(x_193, 3, x_3);
lean_closure_set(x_193, 4, x_4);
lean_closure_set(x_193, 5, x_6);
lean_closure_set(x_193, 6, x_7);
lean_closure_set(x_193, 7, x_142);
lean_closure_set(x_193, 8, x_192);
lean_closure_set(x_193, 9, x_170);
lean_closure_set(x_193, 10, x_186);
lean_closure_set(x_193, 11, x_189);
lean_closure_set(x_193, 12, x_190);
x_194 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_194, 0, x_191);
lean_closure_set(x_194, 1, x_193);
x_224 = lean_ctor_get(x_182, 4);
lean_inc(x_224);
x_225 = lean_ctor_get_uint8(x_224, sizeof(void*)*1);
lean_dec(x_224);
if (x_225 == 0)
{
x_195 = x_174;
x_196 = x_182;
goto block_223;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_226 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_227 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_226, x_13, x_182);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_unbox(x_228);
lean_dec(x_228);
x_195 = x_230;
x_196 = x_229;
goto block_223;
}
block_223:
{
if (x_195 == 0)
{
lean_object* x_197; 
x_197 = l_Lean_Meta_getMVarDecl(x_184, x_13, x_196);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 4);
lean_inc(x_201);
lean_dec(x_198);
x_202 = l_Lean_Meta_withLocalContext___rarg(x_200, x_201, x_194, x_13, x_199);
lean_dec(x_13);
return x_202;
}
else
{
uint8_t x_203; 
lean_dec(x_194);
lean_dec(x_13);
x_203 = !lean_is_exclusive(x_197);
if (x_203 == 0)
{
return x_197;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_197, 0);
x_205 = lean_ctor_get(x_197, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_197);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_inc(x_184);
x_207 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_207, 0, x_184);
x_208 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_209 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
x_210 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_211 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_210, x_209, x_13, x_196);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = l_Lean_Meta_getMVarDecl(x_184, x_13, x_212);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
x_217 = lean_ctor_get(x_214, 4);
lean_inc(x_217);
lean_dec(x_214);
x_218 = l_Lean_Meta_withLocalContext___rarg(x_216, x_217, x_194, x_13, x_215);
lean_dec(x_13);
return x_218;
}
else
{
uint8_t x_219; 
lean_dec(x_194);
lean_dec(x_13);
x_219 = !lean_is_exclusive(x_213);
if (x_219 == 0)
{
return x_213;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_213, 0);
x_221 = lean_ctor_get(x_213, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_213);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_178);
lean_dec(x_170);
lean_dec(x_155);
lean_dec(x_142);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_231 = !lean_is_exclusive(x_180);
if (x_231 == 0)
{
return x_180;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_180, 0);
x_233 = lean_ctor_get(x_180, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_180);
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
lean_dec(x_170);
lean_dec(x_155);
lean_dec(x_142);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_235 = !lean_is_exclusive(x_175);
if (x_235 == 0)
{
return x_175;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_175, 0);
x_237 = lean_ctor_get(x_175, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_175);
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
lean_dec(x_155);
lean_dec(x_142);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_239 = !lean_is_exclusive(x_167);
if (x_239 == 0)
{
return x_167;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_167, 0);
x_241 = lean_ctor_get(x_167, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_167);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
}
else
{
uint8_t x_257; 
lean_dec(x_155);
lean_dec(x_145);
lean_dec(x_142);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_257 = !lean_is_exclusive(x_157);
if (x_257 == 0)
{
return x_157;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_157, 0);
x_259 = lean_ctor_get(x_157, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_157);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
else
{
uint8_t x_261; 
lean_dec(x_145);
lean_dec(x_142);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_261 = !lean_is_exclusive(x_154);
if (x_261 == 0)
{
return x_154;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_154, 0);
x_263 = lean_ctor_get(x_154, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_154);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
else
{
uint8_t x_265; 
lean_dec(x_142);
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
x_265 = !lean_is_exclusive(x_143);
if (x_265 == 0)
{
return x_143;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_143, 0);
x_267 = lean_ctor_get(x_143, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_143);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
}
case 2:
{
lean_object* x_269; lean_object* x_270; 
lean_dec(x_12);
lean_dec(x_10);
x_269 = lean_ctor_get(x_7, 5);
lean_inc(x_269);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_270 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_269, x_13, x_14);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
lean_dec(x_270);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_7, 6);
lean_inc(x_273);
x_274 = l_List_redLength___main___rarg(x_273);
x_275 = lean_mk_empty_array_with_capacity(x_274);
lean_dec(x_274);
lean_inc(x_273);
x_276 = l_List_toArrayAux___main___rarg(x_273, x_275);
x_277 = x_276;
x_278 = lean_unsigned_to_nat(0u);
lean_inc(x_272);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_279 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_279, 0, x_1);
lean_closure_set(x_279, 1, x_6);
lean_closure_set(x_279, 2, x_7);
lean_closure_set(x_279, 3, x_9);
lean_closure_set(x_279, 4, x_11);
lean_closure_set(x_279, 5, x_272);
lean_closure_set(x_279, 6, x_273);
lean_closure_set(x_279, 7, x_278);
lean_closure_set(x_279, 8, x_277);
x_280 = x_279;
lean_inc(x_13);
x_281 = lean_apply_2(x_280, x_13, x_271);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
lean_inc(x_1);
x_284 = l_Lean_Meta_getMVarType(x_1, x_13, x_283);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_282);
x_288 = x_282;
x_289 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_278, x_288);
x_290 = x_289;
lean_inc(x_2);
x_291 = lean_array_push(x_290, x_2);
if (x_287 == 0)
{
lean_object* x_371; uint8_t x_372; 
x_371 = l_Lean_MetavarContext_exprDependsOn(x_272, x_285, x_2);
lean_dec(x_2);
x_372 = lean_unbox(x_371);
lean_dec(x_371);
if (x_372 == 0)
{
x_292 = x_286;
goto block_370;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; 
lean_dec(x_291);
lean_dec(x_282);
lean_dec(x_269);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_373 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_373, 0, x_3);
x_374 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_375 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_373);
x_376 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_377 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
x_378 = lean_box(0);
x_379 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_377, x_378, x_13, x_286);
lean_dec(x_13);
x_380 = !lean_is_exclusive(x_379);
if (x_380 == 0)
{
return x_379;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_379, 0);
x_382 = lean_ctor_get(x_379, 1);
lean_inc(x_382);
lean_inc(x_381);
lean_dec(x_379);
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
return x_383;
}
}
}
else
{
lean_dec(x_285);
lean_dec(x_272);
lean_dec(x_2);
x_292 = x_286;
goto block_370;
}
block_370:
{
uint8_t x_293; lean_object* x_294; 
x_293 = 1;
x_294 = l_Lean_Meta_revert(x_1, x_291, x_293, x_13, x_292);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
x_297 = lean_ctor_get(x_295, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_295, 1);
lean_inc(x_298);
lean_dec(x_295);
x_299 = lean_array_get_size(x_282);
x_300 = lean_box(0);
x_301 = 0;
x_302 = l_Lean_Meta_introN(x_298, x_299, x_300, x_301, x_13, x_296);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
x_305 = lean_ctor_get(x_303, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_303, 1);
lean_inc(x_306);
lean_dec(x_303);
x_307 = l_Lean_Meta_intro1(x_306, x_301, x_13, x_304);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; lean_object* x_351; uint8_t x_352; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = lean_ctor_get(x_308, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_308, 1);
lean_inc(x_311);
lean_dec(x_308);
x_312 = lean_box(0);
x_313 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_282, x_305, x_282, x_278, x_312);
lean_dec(x_282);
x_314 = x_305;
x_315 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_278, x_314);
x_316 = x_315;
lean_inc(x_310);
x_317 = l_Lean_mkFVar(x_310);
lean_inc(x_311);
x_318 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_318, 0, x_311);
x_319 = lean_box(x_287);
lean_inc(x_311);
x_320 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_320, 0, x_310);
lean_closure_set(x_320, 1, x_8);
lean_closure_set(x_320, 2, x_311);
lean_closure_set(x_320, 3, x_3);
lean_closure_set(x_320, 4, x_4);
lean_closure_set(x_320, 5, x_6);
lean_closure_set(x_320, 6, x_7);
lean_closure_set(x_320, 7, x_269);
lean_closure_set(x_320, 8, x_319);
lean_closure_set(x_320, 9, x_297);
lean_closure_set(x_320, 10, x_313);
lean_closure_set(x_320, 11, x_316);
lean_closure_set(x_320, 12, x_317);
x_321 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_321, 0, x_318);
lean_closure_set(x_321, 1, x_320);
x_351 = lean_ctor_get(x_309, 4);
lean_inc(x_351);
x_352 = lean_ctor_get_uint8(x_351, sizeof(void*)*1);
lean_dec(x_351);
if (x_352 == 0)
{
x_322 = x_301;
x_323 = x_309;
goto block_350;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_353 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_354 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_353, x_13, x_309);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
lean_dec(x_354);
x_357 = lean_unbox(x_355);
lean_dec(x_355);
x_322 = x_357;
x_323 = x_356;
goto block_350;
}
block_350:
{
if (x_322 == 0)
{
lean_object* x_324; 
x_324 = l_Lean_Meta_getMVarDecl(x_311, x_13, x_323);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
x_328 = lean_ctor_get(x_325, 4);
lean_inc(x_328);
lean_dec(x_325);
x_329 = l_Lean_Meta_withLocalContext___rarg(x_327, x_328, x_321, x_13, x_326);
lean_dec(x_13);
return x_329;
}
else
{
uint8_t x_330; 
lean_dec(x_321);
lean_dec(x_13);
x_330 = !lean_is_exclusive(x_324);
if (x_330 == 0)
{
return x_324;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_324, 0);
x_332 = lean_ctor_get(x_324, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_324);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
return x_333;
}
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_inc(x_311);
x_334 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_334, 0, x_311);
x_335 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_336 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_334);
x_337 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_338 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_337, x_336, x_13, x_323);
x_339 = lean_ctor_get(x_338, 1);
lean_inc(x_339);
lean_dec(x_338);
x_340 = l_Lean_Meta_getMVarDecl(x_311, x_13, x_339);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
lean_dec(x_340);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_341, 4);
lean_inc(x_344);
lean_dec(x_341);
x_345 = l_Lean_Meta_withLocalContext___rarg(x_343, x_344, x_321, x_13, x_342);
lean_dec(x_13);
return x_345;
}
else
{
uint8_t x_346; 
lean_dec(x_321);
lean_dec(x_13);
x_346 = !lean_is_exclusive(x_340);
if (x_346 == 0)
{
return x_340;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_340, 0);
x_348 = lean_ctor_get(x_340, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_340);
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
return x_349;
}
}
}
}
}
else
{
uint8_t x_358; 
lean_dec(x_305);
lean_dec(x_297);
lean_dec(x_282);
lean_dec(x_269);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_358 = !lean_is_exclusive(x_307);
if (x_358 == 0)
{
return x_307;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_307, 0);
x_360 = lean_ctor_get(x_307, 1);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_307);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
return x_361;
}
}
}
else
{
uint8_t x_362; 
lean_dec(x_297);
lean_dec(x_282);
lean_dec(x_269);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_362 = !lean_is_exclusive(x_302);
if (x_362 == 0)
{
return x_302;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_302, 0);
x_364 = lean_ctor_get(x_302, 1);
lean_inc(x_364);
lean_inc(x_363);
lean_dec(x_302);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
return x_365;
}
}
}
else
{
uint8_t x_366; 
lean_dec(x_282);
lean_dec(x_269);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_366 = !lean_is_exclusive(x_294);
if (x_366 == 0)
{
return x_294;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_294, 0);
x_368 = lean_ctor_get(x_294, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_294);
x_369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
return x_369;
}
}
}
}
else
{
uint8_t x_384; 
lean_dec(x_282);
lean_dec(x_272);
lean_dec(x_269);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_384 = !lean_is_exclusive(x_284);
if (x_384 == 0)
{
return x_284;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_284, 0);
x_386 = lean_ctor_get(x_284, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_284);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
return x_387;
}
}
}
else
{
uint8_t x_388; 
lean_dec(x_272);
lean_dec(x_269);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_388 = !lean_is_exclusive(x_281);
if (x_388 == 0)
{
return x_281;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_281, 0);
x_390 = lean_ctor_get(x_281, 1);
lean_inc(x_390);
lean_inc(x_389);
lean_dec(x_281);
x_391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
return x_391;
}
}
}
else
{
uint8_t x_392; 
lean_dec(x_269);
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
x_392 = !lean_is_exclusive(x_270);
if (x_392 == 0)
{
return x_270;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_270, 0);
x_394 = lean_ctor_get(x_270, 1);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_270);
x_395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
return x_395;
}
}
}
case 3:
{
lean_object* x_396; lean_object* x_397; 
lean_dec(x_12);
lean_dec(x_10);
x_396 = lean_ctor_get(x_7, 5);
lean_inc(x_396);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_397 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_396, x_13, x_14);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
lean_dec(x_397);
x_399 = lean_ctor_get(x_398, 1);
lean_inc(x_399);
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_406 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_406, 0, x_1);
lean_closure_set(x_406, 1, x_6);
lean_closure_set(x_406, 2, x_7);
lean_closure_set(x_406, 3, x_9);
lean_closure_set(x_406, 4, x_11);
lean_closure_set(x_406, 5, x_399);
lean_closure_set(x_406, 6, x_400);
lean_closure_set(x_406, 7, x_405);
lean_closure_set(x_406, 8, x_404);
x_407 = x_406;
lean_inc(x_13);
x_408 = lean_apply_2(x_407, x_13, x_398);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
lean_inc(x_1);
x_411 = l_Lean_Meta_getMVarType(x_1, x_13, x_410);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; uint8_t x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_409);
x_415 = x_409;
x_416 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_405, x_415);
x_417 = x_416;
lean_inc(x_2);
x_418 = lean_array_push(x_417, x_2);
if (x_414 == 0)
{
lean_object* x_498; uint8_t x_499; 
x_498 = l_Lean_MetavarContext_exprDependsOn(x_399, x_412, x_2);
lean_dec(x_2);
x_499 = lean_unbox(x_498);
lean_dec(x_498);
if (x_499 == 0)
{
x_419 = x_413;
goto block_497;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; 
lean_dec(x_418);
lean_dec(x_409);
lean_dec(x_396);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_500 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_500, 0, x_3);
x_501 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_502 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_500);
x_503 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_504 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_503);
x_505 = lean_box(0);
x_506 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_504, x_505, x_13, x_413);
lean_dec(x_13);
x_507 = !lean_is_exclusive(x_506);
if (x_507 == 0)
{
return x_506;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_508 = lean_ctor_get(x_506, 0);
x_509 = lean_ctor_get(x_506, 1);
lean_inc(x_509);
lean_inc(x_508);
lean_dec(x_506);
x_510 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_510, 0, x_508);
lean_ctor_set(x_510, 1, x_509);
return x_510;
}
}
}
else
{
lean_dec(x_412);
lean_dec(x_399);
lean_dec(x_2);
x_419 = x_413;
goto block_497;
}
block_497:
{
uint8_t x_420; lean_object* x_421; 
x_420 = 1;
x_421 = l_Lean_Meta_revert(x_1, x_418, x_420, x_13, x_419);
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
x_429 = l_Lean_Meta_introN(x_425, x_426, x_427, x_428, x_13, x_423);
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
x_434 = l_Lean_Meta_intro1(x_433, x_428, x_13, x_431);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; lean_object* x_478; uint8_t x_479; 
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
x_440 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_409, x_432, x_409, x_405, x_439);
lean_dec(x_409);
x_441 = x_432;
x_442 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_405, x_441);
x_443 = x_442;
lean_inc(x_437);
x_444 = l_Lean_mkFVar(x_437);
lean_inc(x_438);
x_445 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_445, 0, x_438);
x_446 = lean_box(x_414);
lean_inc(x_438);
x_447 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_447, 0, x_437);
lean_closure_set(x_447, 1, x_8);
lean_closure_set(x_447, 2, x_438);
lean_closure_set(x_447, 3, x_3);
lean_closure_set(x_447, 4, x_4);
lean_closure_set(x_447, 5, x_6);
lean_closure_set(x_447, 6, x_7);
lean_closure_set(x_447, 7, x_396);
lean_closure_set(x_447, 8, x_446);
lean_closure_set(x_447, 9, x_424);
lean_closure_set(x_447, 10, x_440);
lean_closure_set(x_447, 11, x_443);
lean_closure_set(x_447, 12, x_444);
x_448 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_448, 0, x_445);
lean_closure_set(x_448, 1, x_447);
x_478 = lean_ctor_get(x_436, 4);
lean_inc(x_478);
x_479 = lean_ctor_get_uint8(x_478, sizeof(void*)*1);
lean_dec(x_478);
if (x_479 == 0)
{
x_449 = x_428;
x_450 = x_436;
goto block_477;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; 
x_480 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_481 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_480, x_13, x_436);
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
lean_dec(x_481);
x_484 = lean_unbox(x_482);
lean_dec(x_482);
x_449 = x_484;
x_450 = x_483;
goto block_477;
}
block_477:
{
if (x_449 == 0)
{
lean_object* x_451; 
x_451 = l_Lean_Meta_getMVarDecl(x_438, x_13, x_450);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_452, 4);
lean_inc(x_455);
lean_dec(x_452);
x_456 = l_Lean_Meta_withLocalContext___rarg(x_454, x_455, x_448, x_13, x_453);
lean_dec(x_13);
return x_456;
}
else
{
uint8_t x_457; 
lean_dec(x_448);
lean_dec(x_13);
x_457 = !lean_is_exclusive(x_451);
if (x_457 == 0)
{
return x_451;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_451, 0);
x_459 = lean_ctor_get(x_451, 1);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_451);
x_460 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_460, 0, x_458);
lean_ctor_set(x_460, 1, x_459);
return x_460;
}
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
lean_inc(x_438);
x_461 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_461, 0, x_438);
x_462 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_463 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_461);
x_464 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_465 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_464, x_463, x_13, x_450);
x_466 = lean_ctor_get(x_465, 1);
lean_inc(x_466);
lean_dec(x_465);
x_467 = l_Lean_Meta_getMVarDecl(x_438, x_13, x_466);
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
x_472 = l_Lean_Meta_withLocalContext___rarg(x_470, x_471, x_448, x_13, x_469);
lean_dec(x_13);
return x_472;
}
else
{
uint8_t x_473; 
lean_dec(x_448);
lean_dec(x_13);
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
}
}
else
{
uint8_t x_485; 
lean_dec(x_432);
lean_dec(x_424);
lean_dec(x_409);
lean_dec(x_396);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_485 = !lean_is_exclusive(x_434);
if (x_485 == 0)
{
return x_434;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_486 = lean_ctor_get(x_434, 0);
x_487 = lean_ctor_get(x_434, 1);
lean_inc(x_487);
lean_inc(x_486);
lean_dec(x_434);
x_488 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
return x_488;
}
}
}
else
{
uint8_t x_489; 
lean_dec(x_424);
lean_dec(x_409);
lean_dec(x_396);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_489 = !lean_is_exclusive(x_429);
if (x_489 == 0)
{
return x_429;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_490 = lean_ctor_get(x_429, 0);
x_491 = lean_ctor_get(x_429, 1);
lean_inc(x_491);
lean_inc(x_490);
lean_dec(x_429);
x_492 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_491);
return x_492;
}
}
}
else
{
uint8_t x_493; 
lean_dec(x_409);
lean_dec(x_396);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_493 = !lean_is_exclusive(x_421);
if (x_493 == 0)
{
return x_421;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_494 = lean_ctor_get(x_421, 0);
x_495 = lean_ctor_get(x_421, 1);
lean_inc(x_495);
lean_inc(x_494);
lean_dec(x_421);
x_496 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set(x_496, 1, x_495);
return x_496;
}
}
}
}
else
{
uint8_t x_511; 
lean_dec(x_409);
lean_dec(x_399);
lean_dec(x_396);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_511 = !lean_is_exclusive(x_411);
if (x_511 == 0)
{
return x_411;
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_512 = lean_ctor_get(x_411, 0);
x_513 = lean_ctor_get(x_411, 1);
lean_inc(x_513);
lean_inc(x_512);
lean_dec(x_411);
x_514 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_514, 0, x_512);
lean_ctor_set(x_514, 1, x_513);
return x_514;
}
}
}
else
{
uint8_t x_515; 
lean_dec(x_399);
lean_dec(x_396);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_515 = !lean_is_exclusive(x_408);
if (x_515 == 0)
{
return x_408;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_516 = lean_ctor_get(x_408, 0);
x_517 = lean_ctor_get(x_408, 1);
lean_inc(x_517);
lean_inc(x_516);
lean_dec(x_408);
x_518 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set(x_518, 1, x_517);
return x_518;
}
}
}
else
{
uint8_t x_519; 
lean_dec(x_396);
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
x_519 = !lean_is_exclusive(x_397);
if (x_519 == 0)
{
return x_397;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_520 = lean_ctor_get(x_397, 0);
x_521 = lean_ctor_get(x_397, 1);
lean_inc(x_521);
lean_inc(x_520);
lean_dec(x_397);
x_522 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_522, 0, x_520);
lean_ctor_set(x_522, 1, x_521);
return x_522;
}
}
}
case 4:
{
lean_object* x_523; lean_object* x_524; 
lean_dec(x_12);
lean_dec(x_10);
x_523 = lean_ctor_get(x_7, 5);
lean_inc(x_523);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_524 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_523, x_13, x_14);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_525 = lean_ctor_get(x_524, 1);
lean_inc(x_525);
lean_dec(x_524);
x_526 = lean_ctor_get(x_525, 1);
lean_inc(x_526);
x_527 = lean_ctor_get(x_7, 6);
lean_inc(x_527);
x_528 = l_List_redLength___main___rarg(x_527);
x_529 = lean_mk_empty_array_with_capacity(x_528);
lean_dec(x_528);
lean_inc(x_527);
x_530 = l_List_toArrayAux___main___rarg(x_527, x_529);
x_531 = x_530;
x_532 = lean_unsigned_to_nat(0u);
lean_inc(x_526);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_533 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_533, 0, x_1);
lean_closure_set(x_533, 1, x_6);
lean_closure_set(x_533, 2, x_7);
lean_closure_set(x_533, 3, x_9);
lean_closure_set(x_533, 4, x_11);
lean_closure_set(x_533, 5, x_526);
lean_closure_set(x_533, 6, x_527);
lean_closure_set(x_533, 7, x_532);
lean_closure_set(x_533, 8, x_531);
x_534 = x_533;
lean_inc(x_13);
x_535 = lean_apply_2(x_534, x_13, x_525);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
lean_dec(x_535);
lean_inc(x_1);
x_538 = l_Lean_Meta_getMVarType(x_1, x_13, x_537);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_538, 1);
lean_inc(x_540);
lean_dec(x_538);
x_541 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_536);
x_542 = x_536;
x_543 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_532, x_542);
x_544 = x_543;
lean_inc(x_2);
x_545 = lean_array_push(x_544, x_2);
if (x_541 == 0)
{
lean_object* x_625; uint8_t x_626; 
x_625 = l_Lean_MetavarContext_exprDependsOn(x_526, x_539, x_2);
lean_dec(x_2);
x_626 = lean_unbox(x_625);
lean_dec(x_625);
if (x_626 == 0)
{
x_546 = x_540;
goto block_624;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; uint8_t x_634; 
lean_dec(x_545);
lean_dec(x_536);
lean_dec(x_523);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_627 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_627, 0, x_3);
x_628 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_629 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_629, 0, x_628);
lean_ctor_set(x_629, 1, x_627);
x_630 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_631 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_631, 0, x_629);
lean_ctor_set(x_631, 1, x_630);
x_632 = lean_box(0);
x_633 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_631, x_632, x_13, x_540);
lean_dec(x_13);
x_634 = !lean_is_exclusive(x_633);
if (x_634 == 0)
{
return x_633;
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_635 = lean_ctor_get(x_633, 0);
x_636 = lean_ctor_get(x_633, 1);
lean_inc(x_636);
lean_inc(x_635);
lean_dec(x_633);
x_637 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_637, 0, x_635);
lean_ctor_set(x_637, 1, x_636);
return x_637;
}
}
}
else
{
lean_dec(x_539);
lean_dec(x_526);
lean_dec(x_2);
x_546 = x_540;
goto block_624;
}
block_624:
{
uint8_t x_547; lean_object* x_548; 
x_547 = 1;
x_548 = l_Lean_Meta_revert(x_1, x_545, x_547, x_13, x_546);
if (lean_obj_tag(x_548) == 0)
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; uint8_t x_555; lean_object* x_556; 
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
lean_dec(x_548);
x_551 = lean_ctor_get(x_549, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_549, 1);
lean_inc(x_552);
lean_dec(x_549);
x_553 = lean_array_get_size(x_536);
x_554 = lean_box(0);
x_555 = 0;
x_556 = l_Lean_Meta_introN(x_552, x_553, x_554, x_555, x_13, x_550);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
lean_dec(x_556);
x_559 = lean_ctor_get(x_557, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_557, 1);
lean_inc(x_560);
lean_dec(x_557);
x_561 = l_Lean_Meta_intro1(x_560, x_555, x_13, x_558);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; lean_object* x_577; lean_object* x_605; uint8_t x_606; 
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_561, 1);
lean_inc(x_563);
lean_dec(x_561);
x_564 = lean_ctor_get(x_562, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_562, 1);
lean_inc(x_565);
lean_dec(x_562);
x_566 = lean_box(0);
x_567 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_536, x_559, x_536, x_532, x_566);
lean_dec(x_536);
x_568 = x_559;
x_569 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_532, x_568);
x_570 = x_569;
lean_inc(x_564);
x_571 = l_Lean_mkFVar(x_564);
lean_inc(x_565);
x_572 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_572, 0, x_565);
x_573 = lean_box(x_541);
lean_inc(x_565);
x_574 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_574, 0, x_564);
lean_closure_set(x_574, 1, x_8);
lean_closure_set(x_574, 2, x_565);
lean_closure_set(x_574, 3, x_3);
lean_closure_set(x_574, 4, x_4);
lean_closure_set(x_574, 5, x_6);
lean_closure_set(x_574, 6, x_7);
lean_closure_set(x_574, 7, x_523);
lean_closure_set(x_574, 8, x_573);
lean_closure_set(x_574, 9, x_551);
lean_closure_set(x_574, 10, x_567);
lean_closure_set(x_574, 11, x_570);
lean_closure_set(x_574, 12, x_571);
x_575 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_575, 0, x_572);
lean_closure_set(x_575, 1, x_574);
x_605 = lean_ctor_get(x_563, 4);
lean_inc(x_605);
x_606 = lean_ctor_get_uint8(x_605, sizeof(void*)*1);
lean_dec(x_605);
if (x_606 == 0)
{
x_576 = x_555;
x_577 = x_563;
goto block_604;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; uint8_t x_611; 
x_607 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_608 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_607, x_13, x_563);
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_608, 1);
lean_inc(x_610);
lean_dec(x_608);
x_611 = lean_unbox(x_609);
lean_dec(x_609);
x_576 = x_611;
x_577 = x_610;
goto block_604;
}
block_604:
{
if (x_576 == 0)
{
lean_object* x_578; 
x_578 = l_Lean_Meta_getMVarDecl(x_565, x_13, x_577);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_578, 1);
lean_inc(x_580);
lean_dec(x_578);
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
x_582 = lean_ctor_get(x_579, 4);
lean_inc(x_582);
lean_dec(x_579);
x_583 = l_Lean_Meta_withLocalContext___rarg(x_581, x_582, x_575, x_13, x_580);
lean_dec(x_13);
return x_583;
}
else
{
uint8_t x_584; 
lean_dec(x_575);
lean_dec(x_13);
x_584 = !lean_is_exclusive(x_578);
if (x_584 == 0)
{
return x_578;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_585 = lean_ctor_get(x_578, 0);
x_586 = lean_ctor_get(x_578, 1);
lean_inc(x_586);
lean_inc(x_585);
lean_dec(x_578);
x_587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_587, 0, x_585);
lean_ctor_set(x_587, 1, x_586);
return x_587;
}
}
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
lean_inc(x_565);
x_588 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_588, 0, x_565);
x_589 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_590 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_588);
x_591 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_592 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_591, x_590, x_13, x_577);
x_593 = lean_ctor_get(x_592, 1);
lean_inc(x_593);
lean_dec(x_592);
x_594 = l_Lean_Meta_getMVarDecl(x_565, x_13, x_593);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_595 = lean_ctor_get(x_594, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_594, 1);
lean_inc(x_596);
lean_dec(x_594);
x_597 = lean_ctor_get(x_595, 1);
lean_inc(x_597);
x_598 = lean_ctor_get(x_595, 4);
lean_inc(x_598);
lean_dec(x_595);
x_599 = l_Lean_Meta_withLocalContext___rarg(x_597, x_598, x_575, x_13, x_596);
lean_dec(x_13);
return x_599;
}
else
{
uint8_t x_600; 
lean_dec(x_575);
lean_dec(x_13);
x_600 = !lean_is_exclusive(x_594);
if (x_600 == 0)
{
return x_594;
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_601 = lean_ctor_get(x_594, 0);
x_602 = lean_ctor_get(x_594, 1);
lean_inc(x_602);
lean_inc(x_601);
lean_dec(x_594);
x_603 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_603, 0, x_601);
lean_ctor_set(x_603, 1, x_602);
return x_603;
}
}
}
}
}
else
{
uint8_t x_612; 
lean_dec(x_559);
lean_dec(x_551);
lean_dec(x_536);
lean_dec(x_523);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_612 = !lean_is_exclusive(x_561);
if (x_612 == 0)
{
return x_561;
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = lean_ctor_get(x_561, 0);
x_614 = lean_ctor_get(x_561, 1);
lean_inc(x_614);
lean_inc(x_613);
lean_dec(x_561);
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
lean_dec(x_551);
lean_dec(x_536);
lean_dec(x_523);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_616 = !lean_is_exclusive(x_556);
if (x_616 == 0)
{
return x_556;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_617 = lean_ctor_get(x_556, 0);
x_618 = lean_ctor_get(x_556, 1);
lean_inc(x_618);
lean_inc(x_617);
lean_dec(x_556);
x_619 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_619, 0, x_617);
lean_ctor_set(x_619, 1, x_618);
return x_619;
}
}
}
else
{
uint8_t x_620; 
lean_dec(x_536);
lean_dec(x_523);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_620 = !lean_is_exclusive(x_548);
if (x_620 == 0)
{
return x_548;
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_621 = lean_ctor_get(x_548, 0);
x_622 = lean_ctor_get(x_548, 1);
lean_inc(x_622);
lean_inc(x_621);
lean_dec(x_548);
x_623 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_623, 0, x_621);
lean_ctor_set(x_623, 1, x_622);
return x_623;
}
}
}
}
else
{
uint8_t x_638; 
lean_dec(x_536);
lean_dec(x_526);
lean_dec(x_523);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_638 = !lean_is_exclusive(x_538);
if (x_638 == 0)
{
return x_538;
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_639 = lean_ctor_get(x_538, 0);
x_640 = lean_ctor_get(x_538, 1);
lean_inc(x_640);
lean_inc(x_639);
lean_dec(x_538);
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
lean_dec(x_526);
lean_dec(x_523);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_642 = !lean_is_exclusive(x_535);
if (x_642 == 0)
{
return x_535;
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_643 = lean_ctor_get(x_535, 0);
x_644 = lean_ctor_get(x_535, 1);
lean_inc(x_644);
lean_inc(x_643);
lean_dec(x_535);
x_645 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_645, 0, x_643);
lean_ctor_set(x_645, 1, x_644);
return x_645;
}
}
}
else
{
uint8_t x_646; 
lean_dec(x_523);
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
x_646 = !lean_is_exclusive(x_524);
if (x_646 == 0)
{
return x_524;
}
else
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_647 = lean_ctor_get(x_524, 0);
x_648 = lean_ctor_get(x_524, 1);
lean_inc(x_648);
lean_inc(x_647);
lean_dec(x_524);
x_649 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_649, 0, x_647);
lean_ctor_set(x_649, 1, x_648);
return x_649;
}
}
}
case 5:
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_650 = lean_ctor_get(x_10, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_10, 1);
lean_inc(x_651);
lean_dec(x_10);
x_652 = lean_array_set(x_11, x_12, x_651);
x_653 = lean_unsigned_to_nat(1u);
x_654 = lean_nat_sub(x_12, x_653);
lean_dec(x_12);
x_10 = x_650;
x_11 = x_652;
x_12 = x_654;
goto _start;
}
case 6:
{
lean_object* x_656; lean_object* x_657; 
lean_dec(x_12);
lean_dec(x_10);
x_656 = lean_ctor_get(x_7, 5);
lean_inc(x_656);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_657 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_656, x_13, x_14);
if (lean_obj_tag(x_657) == 0)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_658 = lean_ctor_get(x_657, 1);
lean_inc(x_658);
lean_dec(x_657);
x_659 = lean_ctor_get(x_658, 1);
lean_inc(x_659);
x_660 = lean_ctor_get(x_7, 6);
lean_inc(x_660);
x_661 = l_List_redLength___main___rarg(x_660);
x_662 = lean_mk_empty_array_with_capacity(x_661);
lean_dec(x_661);
lean_inc(x_660);
x_663 = l_List_toArrayAux___main___rarg(x_660, x_662);
x_664 = x_663;
x_665 = lean_unsigned_to_nat(0u);
lean_inc(x_659);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_666 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_666, 0, x_1);
lean_closure_set(x_666, 1, x_6);
lean_closure_set(x_666, 2, x_7);
lean_closure_set(x_666, 3, x_9);
lean_closure_set(x_666, 4, x_11);
lean_closure_set(x_666, 5, x_659);
lean_closure_set(x_666, 6, x_660);
lean_closure_set(x_666, 7, x_665);
lean_closure_set(x_666, 8, x_664);
x_667 = x_666;
lean_inc(x_13);
x_668 = lean_apply_2(x_667, x_13, x_658);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_668, 1);
lean_inc(x_670);
lean_dec(x_668);
lean_inc(x_1);
x_671 = l_Lean_Meta_getMVarType(x_1, x_13, x_670);
if (lean_obj_tag(x_671) == 0)
{
lean_object* x_672; lean_object* x_673; uint8_t x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_672 = lean_ctor_get(x_671, 0);
lean_inc(x_672);
x_673 = lean_ctor_get(x_671, 1);
lean_inc(x_673);
lean_dec(x_671);
x_674 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_669);
x_675 = x_669;
x_676 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_665, x_675);
x_677 = x_676;
lean_inc(x_2);
x_678 = lean_array_push(x_677, x_2);
if (x_674 == 0)
{
lean_object* x_758; uint8_t x_759; 
x_758 = l_Lean_MetavarContext_exprDependsOn(x_659, x_672, x_2);
lean_dec(x_2);
x_759 = lean_unbox(x_758);
lean_dec(x_758);
if (x_759 == 0)
{
x_679 = x_673;
goto block_757;
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; uint8_t x_767; 
lean_dec(x_678);
lean_dec(x_669);
lean_dec(x_656);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_760 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_760, 0, x_3);
x_761 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_762 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_762, 0, x_761);
lean_ctor_set(x_762, 1, x_760);
x_763 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_764 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_764, 0, x_762);
lean_ctor_set(x_764, 1, x_763);
x_765 = lean_box(0);
x_766 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_764, x_765, x_13, x_673);
lean_dec(x_13);
x_767 = !lean_is_exclusive(x_766);
if (x_767 == 0)
{
return x_766;
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; 
x_768 = lean_ctor_get(x_766, 0);
x_769 = lean_ctor_get(x_766, 1);
lean_inc(x_769);
lean_inc(x_768);
lean_dec(x_766);
x_770 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_770, 0, x_768);
lean_ctor_set(x_770, 1, x_769);
return x_770;
}
}
}
else
{
lean_dec(x_672);
lean_dec(x_659);
lean_dec(x_2);
x_679 = x_673;
goto block_757;
}
block_757:
{
uint8_t x_680; lean_object* x_681; 
x_680 = 1;
x_681 = l_Lean_Meta_revert(x_1, x_678, x_680, x_13, x_679);
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; uint8_t x_688; lean_object* x_689; 
x_682 = lean_ctor_get(x_681, 0);
lean_inc(x_682);
x_683 = lean_ctor_get(x_681, 1);
lean_inc(x_683);
lean_dec(x_681);
x_684 = lean_ctor_get(x_682, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_682, 1);
lean_inc(x_685);
lean_dec(x_682);
x_686 = lean_array_get_size(x_669);
x_687 = lean_box(0);
x_688 = 0;
x_689 = l_Lean_Meta_introN(x_685, x_686, x_687, x_688, x_13, x_683);
if (lean_obj_tag(x_689) == 0)
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
x_690 = lean_ctor_get(x_689, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_689, 1);
lean_inc(x_691);
lean_dec(x_689);
x_692 = lean_ctor_get(x_690, 0);
lean_inc(x_692);
x_693 = lean_ctor_get(x_690, 1);
lean_inc(x_693);
lean_dec(x_690);
x_694 = l_Lean_Meta_intro1(x_693, x_688, x_13, x_691);
if (lean_obj_tag(x_694) == 0)
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; uint8_t x_709; lean_object* x_710; lean_object* x_738; uint8_t x_739; 
x_695 = lean_ctor_get(x_694, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_694, 1);
lean_inc(x_696);
lean_dec(x_694);
x_697 = lean_ctor_get(x_695, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_695, 1);
lean_inc(x_698);
lean_dec(x_695);
x_699 = lean_box(0);
x_700 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_669, x_692, x_669, x_665, x_699);
lean_dec(x_669);
x_701 = x_692;
x_702 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_665, x_701);
x_703 = x_702;
lean_inc(x_697);
x_704 = l_Lean_mkFVar(x_697);
lean_inc(x_698);
x_705 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_705, 0, x_698);
x_706 = lean_box(x_674);
lean_inc(x_698);
x_707 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_707, 0, x_697);
lean_closure_set(x_707, 1, x_8);
lean_closure_set(x_707, 2, x_698);
lean_closure_set(x_707, 3, x_3);
lean_closure_set(x_707, 4, x_4);
lean_closure_set(x_707, 5, x_6);
lean_closure_set(x_707, 6, x_7);
lean_closure_set(x_707, 7, x_656);
lean_closure_set(x_707, 8, x_706);
lean_closure_set(x_707, 9, x_684);
lean_closure_set(x_707, 10, x_700);
lean_closure_set(x_707, 11, x_703);
lean_closure_set(x_707, 12, x_704);
x_708 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_708, 0, x_705);
lean_closure_set(x_708, 1, x_707);
x_738 = lean_ctor_get(x_696, 4);
lean_inc(x_738);
x_739 = lean_ctor_get_uint8(x_738, sizeof(void*)*1);
lean_dec(x_738);
if (x_739 == 0)
{
x_709 = x_688;
x_710 = x_696;
goto block_737;
}
else
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; uint8_t x_744; 
x_740 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_741 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_740, x_13, x_696);
x_742 = lean_ctor_get(x_741, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_741, 1);
lean_inc(x_743);
lean_dec(x_741);
x_744 = lean_unbox(x_742);
lean_dec(x_742);
x_709 = x_744;
x_710 = x_743;
goto block_737;
}
block_737:
{
if (x_709 == 0)
{
lean_object* x_711; 
x_711 = l_Lean_Meta_getMVarDecl(x_698, x_13, x_710);
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_712 = lean_ctor_get(x_711, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_711, 1);
lean_inc(x_713);
lean_dec(x_711);
x_714 = lean_ctor_get(x_712, 1);
lean_inc(x_714);
x_715 = lean_ctor_get(x_712, 4);
lean_inc(x_715);
lean_dec(x_712);
x_716 = l_Lean_Meta_withLocalContext___rarg(x_714, x_715, x_708, x_13, x_713);
lean_dec(x_13);
return x_716;
}
else
{
uint8_t x_717; 
lean_dec(x_708);
lean_dec(x_13);
x_717 = !lean_is_exclusive(x_711);
if (x_717 == 0)
{
return x_711;
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_718 = lean_ctor_get(x_711, 0);
x_719 = lean_ctor_get(x_711, 1);
lean_inc(x_719);
lean_inc(x_718);
lean_dec(x_711);
x_720 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_720, 0, x_718);
lean_ctor_set(x_720, 1, x_719);
return x_720;
}
}
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
lean_inc(x_698);
x_721 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_721, 0, x_698);
x_722 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_723 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set(x_723, 1, x_721);
x_724 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_725 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_724, x_723, x_13, x_710);
x_726 = lean_ctor_get(x_725, 1);
lean_inc(x_726);
lean_dec(x_725);
x_727 = l_Lean_Meta_getMVarDecl(x_698, x_13, x_726);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_727, 1);
lean_inc(x_729);
lean_dec(x_727);
x_730 = lean_ctor_get(x_728, 1);
lean_inc(x_730);
x_731 = lean_ctor_get(x_728, 4);
lean_inc(x_731);
lean_dec(x_728);
x_732 = l_Lean_Meta_withLocalContext___rarg(x_730, x_731, x_708, x_13, x_729);
lean_dec(x_13);
return x_732;
}
else
{
uint8_t x_733; 
lean_dec(x_708);
lean_dec(x_13);
x_733 = !lean_is_exclusive(x_727);
if (x_733 == 0)
{
return x_727;
}
else
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_734 = lean_ctor_get(x_727, 0);
x_735 = lean_ctor_get(x_727, 1);
lean_inc(x_735);
lean_inc(x_734);
lean_dec(x_727);
x_736 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_736, 0, x_734);
lean_ctor_set(x_736, 1, x_735);
return x_736;
}
}
}
}
}
else
{
uint8_t x_745; 
lean_dec(x_692);
lean_dec(x_684);
lean_dec(x_669);
lean_dec(x_656);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_745 = !lean_is_exclusive(x_694);
if (x_745 == 0)
{
return x_694;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_746 = lean_ctor_get(x_694, 0);
x_747 = lean_ctor_get(x_694, 1);
lean_inc(x_747);
lean_inc(x_746);
lean_dec(x_694);
x_748 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_748, 0, x_746);
lean_ctor_set(x_748, 1, x_747);
return x_748;
}
}
}
else
{
uint8_t x_749; 
lean_dec(x_684);
lean_dec(x_669);
lean_dec(x_656);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_749 = !lean_is_exclusive(x_689);
if (x_749 == 0)
{
return x_689;
}
else
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_750 = lean_ctor_get(x_689, 0);
x_751 = lean_ctor_get(x_689, 1);
lean_inc(x_751);
lean_inc(x_750);
lean_dec(x_689);
x_752 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_752, 0, x_750);
lean_ctor_set(x_752, 1, x_751);
return x_752;
}
}
}
else
{
uint8_t x_753; 
lean_dec(x_669);
lean_dec(x_656);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_753 = !lean_is_exclusive(x_681);
if (x_753 == 0)
{
return x_681;
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_754 = lean_ctor_get(x_681, 0);
x_755 = lean_ctor_get(x_681, 1);
lean_inc(x_755);
lean_inc(x_754);
lean_dec(x_681);
x_756 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_756, 0, x_754);
lean_ctor_set(x_756, 1, x_755);
return x_756;
}
}
}
}
else
{
uint8_t x_771; 
lean_dec(x_669);
lean_dec(x_659);
lean_dec(x_656);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_771 = !lean_is_exclusive(x_671);
if (x_771 == 0)
{
return x_671;
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_772 = lean_ctor_get(x_671, 0);
x_773 = lean_ctor_get(x_671, 1);
lean_inc(x_773);
lean_inc(x_772);
lean_dec(x_671);
x_774 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_774, 0, x_772);
lean_ctor_set(x_774, 1, x_773);
return x_774;
}
}
}
else
{
uint8_t x_775; 
lean_dec(x_659);
lean_dec(x_656);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_775 = !lean_is_exclusive(x_668);
if (x_775 == 0)
{
return x_668;
}
else
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_776 = lean_ctor_get(x_668, 0);
x_777 = lean_ctor_get(x_668, 1);
lean_inc(x_777);
lean_inc(x_776);
lean_dec(x_668);
x_778 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_778, 0, x_776);
lean_ctor_set(x_778, 1, x_777);
return x_778;
}
}
}
else
{
uint8_t x_779; 
lean_dec(x_656);
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
x_779 = !lean_is_exclusive(x_657);
if (x_779 == 0)
{
return x_657;
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_780 = lean_ctor_get(x_657, 0);
x_781 = lean_ctor_get(x_657, 1);
lean_inc(x_781);
lean_inc(x_780);
lean_dec(x_657);
x_782 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_782, 0, x_780);
lean_ctor_set(x_782, 1, x_781);
return x_782;
}
}
}
case 7:
{
lean_object* x_783; lean_object* x_784; 
lean_dec(x_12);
lean_dec(x_10);
x_783 = lean_ctor_get(x_7, 5);
lean_inc(x_783);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_784 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_783, x_13, x_14);
if (lean_obj_tag(x_784) == 0)
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
x_785 = lean_ctor_get(x_784, 1);
lean_inc(x_785);
lean_dec(x_784);
x_786 = lean_ctor_get(x_785, 1);
lean_inc(x_786);
x_787 = lean_ctor_get(x_7, 6);
lean_inc(x_787);
x_788 = l_List_redLength___main___rarg(x_787);
x_789 = lean_mk_empty_array_with_capacity(x_788);
lean_dec(x_788);
lean_inc(x_787);
x_790 = l_List_toArrayAux___main___rarg(x_787, x_789);
x_791 = x_790;
x_792 = lean_unsigned_to_nat(0u);
lean_inc(x_786);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_793 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_793, 0, x_1);
lean_closure_set(x_793, 1, x_6);
lean_closure_set(x_793, 2, x_7);
lean_closure_set(x_793, 3, x_9);
lean_closure_set(x_793, 4, x_11);
lean_closure_set(x_793, 5, x_786);
lean_closure_set(x_793, 6, x_787);
lean_closure_set(x_793, 7, x_792);
lean_closure_set(x_793, 8, x_791);
x_794 = x_793;
lean_inc(x_13);
x_795 = lean_apply_2(x_794, x_13, x_785);
if (lean_obj_tag(x_795) == 0)
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_796 = lean_ctor_get(x_795, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_795, 1);
lean_inc(x_797);
lean_dec(x_795);
lean_inc(x_1);
x_798 = l_Lean_Meta_getMVarType(x_1, x_13, x_797);
if (lean_obj_tag(x_798) == 0)
{
lean_object* x_799; lean_object* x_800; uint8_t x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_799 = lean_ctor_get(x_798, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_798, 1);
lean_inc(x_800);
lean_dec(x_798);
x_801 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_796);
x_802 = x_796;
x_803 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_792, x_802);
x_804 = x_803;
lean_inc(x_2);
x_805 = lean_array_push(x_804, x_2);
if (x_801 == 0)
{
lean_object* x_885; uint8_t x_886; 
x_885 = l_Lean_MetavarContext_exprDependsOn(x_786, x_799, x_2);
lean_dec(x_2);
x_886 = lean_unbox(x_885);
lean_dec(x_885);
if (x_886 == 0)
{
x_806 = x_800;
goto block_884;
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; uint8_t x_894; 
lean_dec(x_805);
lean_dec(x_796);
lean_dec(x_783);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_887 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_887, 0, x_3);
x_888 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_889 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_889, 0, x_888);
lean_ctor_set(x_889, 1, x_887);
x_890 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_891 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_891, 0, x_889);
lean_ctor_set(x_891, 1, x_890);
x_892 = lean_box(0);
x_893 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_891, x_892, x_13, x_800);
lean_dec(x_13);
x_894 = !lean_is_exclusive(x_893);
if (x_894 == 0)
{
return x_893;
}
else
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; 
x_895 = lean_ctor_get(x_893, 0);
x_896 = lean_ctor_get(x_893, 1);
lean_inc(x_896);
lean_inc(x_895);
lean_dec(x_893);
x_897 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_897, 0, x_895);
lean_ctor_set(x_897, 1, x_896);
return x_897;
}
}
}
else
{
lean_dec(x_799);
lean_dec(x_786);
lean_dec(x_2);
x_806 = x_800;
goto block_884;
}
block_884:
{
uint8_t x_807; lean_object* x_808; 
x_807 = 1;
x_808 = l_Lean_Meta_revert(x_1, x_805, x_807, x_13, x_806);
if (lean_obj_tag(x_808) == 0)
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; uint8_t x_815; lean_object* x_816; 
x_809 = lean_ctor_get(x_808, 0);
lean_inc(x_809);
x_810 = lean_ctor_get(x_808, 1);
lean_inc(x_810);
lean_dec(x_808);
x_811 = lean_ctor_get(x_809, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_809, 1);
lean_inc(x_812);
lean_dec(x_809);
x_813 = lean_array_get_size(x_796);
x_814 = lean_box(0);
x_815 = 0;
x_816 = l_Lean_Meta_introN(x_812, x_813, x_814, x_815, x_13, x_810);
if (lean_obj_tag(x_816) == 0)
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; 
x_817 = lean_ctor_get(x_816, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_816, 1);
lean_inc(x_818);
lean_dec(x_816);
x_819 = lean_ctor_get(x_817, 0);
lean_inc(x_819);
x_820 = lean_ctor_get(x_817, 1);
lean_inc(x_820);
lean_dec(x_817);
x_821 = l_Lean_Meta_intro1(x_820, x_815, x_13, x_818);
if (lean_obj_tag(x_821) == 0)
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; uint8_t x_836; lean_object* x_837; lean_object* x_865; uint8_t x_866; 
x_822 = lean_ctor_get(x_821, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_821, 1);
lean_inc(x_823);
lean_dec(x_821);
x_824 = lean_ctor_get(x_822, 0);
lean_inc(x_824);
x_825 = lean_ctor_get(x_822, 1);
lean_inc(x_825);
lean_dec(x_822);
x_826 = lean_box(0);
x_827 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_796, x_819, x_796, x_792, x_826);
lean_dec(x_796);
x_828 = x_819;
x_829 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_792, x_828);
x_830 = x_829;
lean_inc(x_824);
x_831 = l_Lean_mkFVar(x_824);
lean_inc(x_825);
x_832 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_832, 0, x_825);
x_833 = lean_box(x_801);
lean_inc(x_825);
x_834 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_834, 0, x_824);
lean_closure_set(x_834, 1, x_8);
lean_closure_set(x_834, 2, x_825);
lean_closure_set(x_834, 3, x_3);
lean_closure_set(x_834, 4, x_4);
lean_closure_set(x_834, 5, x_6);
lean_closure_set(x_834, 6, x_7);
lean_closure_set(x_834, 7, x_783);
lean_closure_set(x_834, 8, x_833);
lean_closure_set(x_834, 9, x_811);
lean_closure_set(x_834, 10, x_827);
lean_closure_set(x_834, 11, x_830);
lean_closure_set(x_834, 12, x_831);
x_835 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_835, 0, x_832);
lean_closure_set(x_835, 1, x_834);
x_865 = lean_ctor_get(x_823, 4);
lean_inc(x_865);
x_866 = lean_ctor_get_uint8(x_865, sizeof(void*)*1);
lean_dec(x_865);
if (x_866 == 0)
{
x_836 = x_815;
x_837 = x_823;
goto block_864;
}
else
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; uint8_t x_871; 
x_867 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_868 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_867, x_13, x_823);
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_868, 1);
lean_inc(x_870);
lean_dec(x_868);
x_871 = lean_unbox(x_869);
lean_dec(x_869);
x_836 = x_871;
x_837 = x_870;
goto block_864;
}
block_864:
{
if (x_836 == 0)
{
lean_object* x_838; 
x_838 = l_Lean_Meta_getMVarDecl(x_825, x_13, x_837);
if (lean_obj_tag(x_838) == 0)
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
x_839 = lean_ctor_get(x_838, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_838, 1);
lean_inc(x_840);
lean_dec(x_838);
x_841 = lean_ctor_get(x_839, 1);
lean_inc(x_841);
x_842 = lean_ctor_get(x_839, 4);
lean_inc(x_842);
lean_dec(x_839);
x_843 = l_Lean_Meta_withLocalContext___rarg(x_841, x_842, x_835, x_13, x_840);
lean_dec(x_13);
return x_843;
}
else
{
uint8_t x_844; 
lean_dec(x_835);
lean_dec(x_13);
x_844 = !lean_is_exclusive(x_838);
if (x_844 == 0)
{
return x_838;
}
else
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; 
x_845 = lean_ctor_get(x_838, 0);
x_846 = lean_ctor_get(x_838, 1);
lean_inc(x_846);
lean_inc(x_845);
lean_dec(x_838);
x_847 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_847, 0, x_845);
lean_ctor_set(x_847, 1, x_846);
return x_847;
}
}
}
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; 
lean_inc(x_825);
x_848 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_848, 0, x_825);
x_849 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_850 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_850, 0, x_849);
lean_ctor_set(x_850, 1, x_848);
x_851 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_852 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_851, x_850, x_13, x_837);
x_853 = lean_ctor_get(x_852, 1);
lean_inc(x_853);
lean_dec(x_852);
x_854 = l_Lean_Meta_getMVarDecl(x_825, x_13, x_853);
if (lean_obj_tag(x_854) == 0)
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; 
x_855 = lean_ctor_get(x_854, 0);
lean_inc(x_855);
x_856 = lean_ctor_get(x_854, 1);
lean_inc(x_856);
lean_dec(x_854);
x_857 = lean_ctor_get(x_855, 1);
lean_inc(x_857);
x_858 = lean_ctor_get(x_855, 4);
lean_inc(x_858);
lean_dec(x_855);
x_859 = l_Lean_Meta_withLocalContext___rarg(x_857, x_858, x_835, x_13, x_856);
lean_dec(x_13);
return x_859;
}
else
{
uint8_t x_860; 
lean_dec(x_835);
lean_dec(x_13);
x_860 = !lean_is_exclusive(x_854);
if (x_860 == 0)
{
return x_854;
}
else
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; 
x_861 = lean_ctor_get(x_854, 0);
x_862 = lean_ctor_get(x_854, 1);
lean_inc(x_862);
lean_inc(x_861);
lean_dec(x_854);
x_863 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_863, 0, x_861);
lean_ctor_set(x_863, 1, x_862);
return x_863;
}
}
}
}
}
else
{
uint8_t x_872; 
lean_dec(x_819);
lean_dec(x_811);
lean_dec(x_796);
lean_dec(x_783);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_872 = !lean_is_exclusive(x_821);
if (x_872 == 0)
{
return x_821;
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_873 = lean_ctor_get(x_821, 0);
x_874 = lean_ctor_get(x_821, 1);
lean_inc(x_874);
lean_inc(x_873);
lean_dec(x_821);
x_875 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_875, 0, x_873);
lean_ctor_set(x_875, 1, x_874);
return x_875;
}
}
}
else
{
uint8_t x_876; 
lean_dec(x_811);
lean_dec(x_796);
lean_dec(x_783);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_876 = !lean_is_exclusive(x_816);
if (x_876 == 0)
{
return x_816;
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_877 = lean_ctor_get(x_816, 0);
x_878 = lean_ctor_get(x_816, 1);
lean_inc(x_878);
lean_inc(x_877);
lean_dec(x_816);
x_879 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_879, 0, x_877);
lean_ctor_set(x_879, 1, x_878);
return x_879;
}
}
}
else
{
uint8_t x_880; 
lean_dec(x_796);
lean_dec(x_783);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_880 = !lean_is_exclusive(x_808);
if (x_880 == 0)
{
return x_808;
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_881 = lean_ctor_get(x_808, 0);
x_882 = lean_ctor_get(x_808, 1);
lean_inc(x_882);
lean_inc(x_881);
lean_dec(x_808);
x_883 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_883, 0, x_881);
lean_ctor_set(x_883, 1, x_882);
return x_883;
}
}
}
}
else
{
uint8_t x_898; 
lean_dec(x_796);
lean_dec(x_786);
lean_dec(x_783);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_898 = !lean_is_exclusive(x_798);
if (x_898 == 0)
{
return x_798;
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; 
x_899 = lean_ctor_get(x_798, 0);
x_900 = lean_ctor_get(x_798, 1);
lean_inc(x_900);
lean_inc(x_899);
lean_dec(x_798);
x_901 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_901, 0, x_899);
lean_ctor_set(x_901, 1, x_900);
return x_901;
}
}
}
else
{
uint8_t x_902; 
lean_dec(x_786);
lean_dec(x_783);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_902 = !lean_is_exclusive(x_795);
if (x_902 == 0)
{
return x_795;
}
else
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; 
x_903 = lean_ctor_get(x_795, 0);
x_904 = lean_ctor_get(x_795, 1);
lean_inc(x_904);
lean_inc(x_903);
lean_dec(x_795);
x_905 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_905, 0, x_903);
lean_ctor_set(x_905, 1, x_904);
return x_905;
}
}
}
else
{
uint8_t x_906; 
lean_dec(x_783);
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
x_906 = !lean_is_exclusive(x_784);
if (x_906 == 0)
{
return x_784;
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; 
x_907 = lean_ctor_get(x_784, 0);
x_908 = lean_ctor_get(x_784, 1);
lean_inc(x_908);
lean_inc(x_907);
lean_dec(x_784);
x_909 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_909, 0, x_907);
lean_ctor_set(x_909, 1, x_908);
return x_909;
}
}
}
case 8:
{
lean_object* x_910; lean_object* x_911; 
lean_dec(x_12);
lean_dec(x_10);
x_910 = lean_ctor_get(x_7, 5);
lean_inc(x_910);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_911 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_910, x_13, x_14);
if (lean_obj_tag(x_911) == 0)
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_912 = lean_ctor_get(x_911, 1);
lean_inc(x_912);
lean_dec(x_911);
x_913 = lean_ctor_get(x_912, 1);
lean_inc(x_913);
x_914 = lean_ctor_get(x_7, 6);
lean_inc(x_914);
x_915 = l_List_redLength___main___rarg(x_914);
x_916 = lean_mk_empty_array_with_capacity(x_915);
lean_dec(x_915);
lean_inc(x_914);
x_917 = l_List_toArrayAux___main___rarg(x_914, x_916);
x_918 = x_917;
x_919 = lean_unsigned_to_nat(0u);
lean_inc(x_913);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_920 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_920, 0, x_1);
lean_closure_set(x_920, 1, x_6);
lean_closure_set(x_920, 2, x_7);
lean_closure_set(x_920, 3, x_9);
lean_closure_set(x_920, 4, x_11);
lean_closure_set(x_920, 5, x_913);
lean_closure_set(x_920, 6, x_914);
lean_closure_set(x_920, 7, x_919);
lean_closure_set(x_920, 8, x_918);
x_921 = x_920;
lean_inc(x_13);
x_922 = lean_apply_2(x_921, x_13, x_912);
if (lean_obj_tag(x_922) == 0)
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; 
x_923 = lean_ctor_get(x_922, 0);
lean_inc(x_923);
x_924 = lean_ctor_get(x_922, 1);
lean_inc(x_924);
lean_dec(x_922);
lean_inc(x_1);
x_925 = l_Lean_Meta_getMVarType(x_1, x_13, x_924);
if (lean_obj_tag(x_925) == 0)
{
lean_object* x_926; lean_object* x_927; uint8_t x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; 
x_926 = lean_ctor_get(x_925, 0);
lean_inc(x_926);
x_927 = lean_ctor_get(x_925, 1);
lean_inc(x_927);
lean_dec(x_925);
x_928 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_923);
x_929 = x_923;
x_930 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_919, x_929);
x_931 = x_930;
lean_inc(x_2);
x_932 = lean_array_push(x_931, x_2);
if (x_928 == 0)
{
lean_object* x_1012; uint8_t x_1013; 
x_1012 = l_Lean_MetavarContext_exprDependsOn(x_913, x_926, x_2);
lean_dec(x_2);
x_1013 = lean_unbox(x_1012);
lean_dec(x_1012);
if (x_1013 == 0)
{
x_933 = x_927;
goto block_1011;
}
else
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; uint8_t x_1021; 
lean_dec(x_932);
lean_dec(x_923);
lean_dec(x_910);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_1014 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1014, 0, x_3);
x_1015 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_1016 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1016, 0, x_1015);
lean_ctor_set(x_1016, 1, x_1014);
x_1017 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_1018 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1018, 0, x_1016);
lean_ctor_set(x_1018, 1, x_1017);
x_1019 = lean_box(0);
x_1020 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1018, x_1019, x_13, x_927);
lean_dec(x_13);
x_1021 = !lean_is_exclusive(x_1020);
if (x_1021 == 0)
{
return x_1020;
}
else
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; 
x_1022 = lean_ctor_get(x_1020, 0);
x_1023 = lean_ctor_get(x_1020, 1);
lean_inc(x_1023);
lean_inc(x_1022);
lean_dec(x_1020);
x_1024 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1024, 0, x_1022);
lean_ctor_set(x_1024, 1, x_1023);
return x_1024;
}
}
}
else
{
lean_dec(x_926);
lean_dec(x_913);
lean_dec(x_2);
x_933 = x_927;
goto block_1011;
}
block_1011:
{
uint8_t x_934; lean_object* x_935; 
x_934 = 1;
x_935 = l_Lean_Meta_revert(x_1, x_932, x_934, x_13, x_933);
if (lean_obj_tag(x_935) == 0)
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; uint8_t x_942; lean_object* x_943; 
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
x_940 = lean_array_get_size(x_923);
x_941 = lean_box(0);
x_942 = 0;
x_943 = l_Lean_Meta_introN(x_939, x_940, x_941, x_942, x_13, x_937);
if (lean_obj_tag(x_943) == 0)
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; 
x_944 = lean_ctor_get(x_943, 0);
lean_inc(x_944);
x_945 = lean_ctor_get(x_943, 1);
lean_inc(x_945);
lean_dec(x_943);
x_946 = lean_ctor_get(x_944, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_944, 1);
lean_inc(x_947);
lean_dec(x_944);
x_948 = l_Lean_Meta_intro1(x_947, x_942, x_13, x_945);
if (lean_obj_tag(x_948) == 0)
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; uint8_t x_963; lean_object* x_964; lean_object* x_992; uint8_t x_993; 
x_949 = lean_ctor_get(x_948, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_948, 1);
lean_inc(x_950);
lean_dec(x_948);
x_951 = lean_ctor_get(x_949, 0);
lean_inc(x_951);
x_952 = lean_ctor_get(x_949, 1);
lean_inc(x_952);
lean_dec(x_949);
x_953 = lean_box(0);
x_954 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_923, x_946, x_923, x_919, x_953);
lean_dec(x_923);
x_955 = x_946;
x_956 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_919, x_955);
x_957 = x_956;
lean_inc(x_951);
x_958 = l_Lean_mkFVar(x_951);
lean_inc(x_952);
x_959 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_959, 0, x_952);
x_960 = lean_box(x_928);
lean_inc(x_952);
x_961 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_961, 0, x_951);
lean_closure_set(x_961, 1, x_8);
lean_closure_set(x_961, 2, x_952);
lean_closure_set(x_961, 3, x_3);
lean_closure_set(x_961, 4, x_4);
lean_closure_set(x_961, 5, x_6);
lean_closure_set(x_961, 6, x_7);
lean_closure_set(x_961, 7, x_910);
lean_closure_set(x_961, 8, x_960);
lean_closure_set(x_961, 9, x_938);
lean_closure_set(x_961, 10, x_954);
lean_closure_set(x_961, 11, x_957);
lean_closure_set(x_961, 12, x_958);
x_962 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_962, 0, x_959);
lean_closure_set(x_962, 1, x_961);
x_992 = lean_ctor_get(x_950, 4);
lean_inc(x_992);
x_993 = lean_ctor_get_uint8(x_992, sizeof(void*)*1);
lean_dec(x_992);
if (x_993 == 0)
{
x_963 = x_942;
x_964 = x_950;
goto block_991;
}
else
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; uint8_t x_998; 
x_994 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_995 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_994, x_13, x_950);
x_996 = lean_ctor_get(x_995, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_995, 1);
lean_inc(x_997);
lean_dec(x_995);
x_998 = lean_unbox(x_996);
lean_dec(x_996);
x_963 = x_998;
x_964 = x_997;
goto block_991;
}
block_991:
{
if (x_963 == 0)
{
lean_object* x_965; 
x_965 = l_Lean_Meta_getMVarDecl(x_952, x_13, x_964);
if (lean_obj_tag(x_965) == 0)
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; 
x_966 = lean_ctor_get(x_965, 0);
lean_inc(x_966);
x_967 = lean_ctor_get(x_965, 1);
lean_inc(x_967);
lean_dec(x_965);
x_968 = lean_ctor_get(x_966, 1);
lean_inc(x_968);
x_969 = lean_ctor_get(x_966, 4);
lean_inc(x_969);
lean_dec(x_966);
x_970 = l_Lean_Meta_withLocalContext___rarg(x_968, x_969, x_962, x_13, x_967);
lean_dec(x_13);
return x_970;
}
else
{
uint8_t x_971; 
lean_dec(x_962);
lean_dec(x_13);
x_971 = !lean_is_exclusive(x_965);
if (x_971 == 0)
{
return x_965;
}
else
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; 
x_972 = lean_ctor_get(x_965, 0);
x_973 = lean_ctor_get(x_965, 1);
lean_inc(x_973);
lean_inc(x_972);
lean_dec(x_965);
x_974 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_974, 0, x_972);
lean_ctor_set(x_974, 1, x_973);
return x_974;
}
}
}
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; 
lean_inc(x_952);
x_975 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_975, 0, x_952);
x_976 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_977 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_977, 0, x_976);
lean_ctor_set(x_977, 1, x_975);
x_978 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_979 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_978, x_977, x_13, x_964);
x_980 = lean_ctor_get(x_979, 1);
lean_inc(x_980);
lean_dec(x_979);
x_981 = l_Lean_Meta_getMVarDecl(x_952, x_13, x_980);
if (lean_obj_tag(x_981) == 0)
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; 
x_982 = lean_ctor_get(x_981, 0);
lean_inc(x_982);
x_983 = lean_ctor_get(x_981, 1);
lean_inc(x_983);
lean_dec(x_981);
x_984 = lean_ctor_get(x_982, 1);
lean_inc(x_984);
x_985 = lean_ctor_get(x_982, 4);
lean_inc(x_985);
lean_dec(x_982);
x_986 = l_Lean_Meta_withLocalContext___rarg(x_984, x_985, x_962, x_13, x_983);
lean_dec(x_13);
return x_986;
}
else
{
uint8_t x_987; 
lean_dec(x_962);
lean_dec(x_13);
x_987 = !lean_is_exclusive(x_981);
if (x_987 == 0)
{
return x_981;
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; 
x_988 = lean_ctor_get(x_981, 0);
x_989 = lean_ctor_get(x_981, 1);
lean_inc(x_989);
lean_inc(x_988);
lean_dec(x_981);
x_990 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_990, 0, x_988);
lean_ctor_set(x_990, 1, x_989);
return x_990;
}
}
}
}
}
else
{
uint8_t x_999; 
lean_dec(x_946);
lean_dec(x_938);
lean_dec(x_923);
lean_dec(x_910);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_999 = !lean_is_exclusive(x_948);
if (x_999 == 0)
{
return x_948;
}
else
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
x_1000 = lean_ctor_get(x_948, 0);
x_1001 = lean_ctor_get(x_948, 1);
lean_inc(x_1001);
lean_inc(x_1000);
lean_dec(x_948);
x_1002 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1002, 0, x_1000);
lean_ctor_set(x_1002, 1, x_1001);
return x_1002;
}
}
}
else
{
uint8_t x_1003; 
lean_dec(x_938);
lean_dec(x_923);
lean_dec(x_910);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1003 = !lean_is_exclusive(x_943);
if (x_1003 == 0)
{
return x_943;
}
else
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
x_1004 = lean_ctor_get(x_943, 0);
x_1005 = lean_ctor_get(x_943, 1);
lean_inc(x_1005);
lean_inc(x_1004);
lean_dec(x_943);
x_1006 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1006, 0, x_1004);
lean_ctor_set(x_1006, 1, x_1005);
return x_1006;
}
}
}
else
{
uint8_t x_1007; 
lean_dec(x_923);
lean_dec(x_910);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1007 = !lean_is_exclusive(x_935);
if (x_1007 == 0)
{
return x_935;
}
else
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
x_1008 = lean_ctor_get(x_935, 0);
x_1009 = lean_ctor_get(x_935, 1);
lean_inc(x_1009);
lean_inc(x_1008);
lean_dec(x_935);
x_1010 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1010, 0, x_1008);
lean_ctor_set(x_1010, 1, x_1009);
return x_1010;
}
}
}
}
else
{
uint8_t x_1025; 
lean_dec(x_923);
lean_dec(x_913);
lean_dec(x_910);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1025 = !lean_is_exclusive(x_925);
if (x_1025 == 0)
{
return x_925;
}
else
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; 
x_1026 = lean_ctor_get(x_925, 0);
x_1027 = lean_ctor_get(x_925, 1);
lean_inc(x_1027);
lean_inc(x_1026);
lean_dec(x_925);
x_1028 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1028, 0, x_1026);
lean_ctor_set(x_1028, 1, x_1027);
return x_1028;
}
}
}
else
{
uint8_t x_1029; 
lean_dec(x_913);
lean_dec(x_910);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1029 = !lean_is_exclusive(x_922);
if (x_1029 == 0)
{
return x_922;
}
else
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1030 = lean_ctor_get(x_922, 0);
x_1031 = lean_ctor_get(x_922, 1);
lean_inc(x_1031);
lean_inc(x_1030);
lean_dec(x_922);
x_1032 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1032, 0, x_1030);
lean_ctor_set(x_1032, 1, x_1031);
return x_1032;
}
}
}
else
{
uint8_t x_1033; 
lean_dec(x_910);
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
x_1033 = !lean_is_exclusive(x_911);
if (x_1033 == 0)
{
return x_911;
}
else
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
x_1034 = lean_ctor_get(x_911, 0);
x_1035 = lean_ctor_get(x_911, 1);
lean_inc(x_1035);
lean_inc(x_1034);
lean_dec(x_911);
x_1036 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1036, 0, x_1034);
lean_ctor_set(x_1036, 1, x_1035);
return x_1036;
}
}
}
case 9:
{
lean_object* x_1037; lean_object* x_1038; 
lean_dec(x_12);
lean_dec(x_10);
x_1037 = lean_ctor_get(x_7, 5);
lean_inc(x_1037);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1038 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_1037, x_13, x_14);
if (lean_obj_tag(x_1038) == 0)
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; 
x_1039 = lean_ctor_get(x_1038, 1);
lean_inc(x_1039);
lean_dec(x_1038);
x_1040 = lean_ctor_get(x_1039, 1);
lean_inc(x_1040);
x_1041 = lean_ctor_get(x_7, 6);
lean_inc(x_1041);
x_1042 = l_List_redLength___main___rarg(x_1041);
x_1043 = lean_mk_empty_array_with_capacity(x_1042);
lean_dec(x_1042);
lean_inc(x_1041);
x_1044 = l_List_toArrayAux___main___rarg(x_1041, x_1043);
x_1045 = x_1044;
x_1046 = lean_unsigned_to_nat(0u);
lean_inc(x_1040);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_1047 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_1047, 0, x_1);
lean_closure_set(x_1047, 1, x_6);
lean_closure_set(x_1047, 2, x_7);
lean_closure_set(x_1047, 3, x_9);
lean_closure_set(x_1047, 4, x_11);
lean_closure_set(x_1047, 5, x_1040);
lean_closure_set(x_1047, 6, x_1041);
lean_closure_set(x_1047, 7, x_1046);
lean_closure_set(x_1047, 8, x_1045);
x_1048 = x_1047;
lean_inc(x_13);
x_1049 = lean_apply_2(x_1048, x_13, x_1039);
if (lean_obj_tag(x_1049) == 0)
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
x_1050 = lean_ctor_get(x_1049, 0);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1049, 1);
lean_inc(x_1051);
lean_dec(x_1049);
lean_inc(x_1);
x_1052 = l_Lean_Meta_getMVarType(x_1, x_13, x_1051);
if (lean_obj_tag(x_1052) == 0)
{
lean_object* x_1053; lean_object* x_1054; uint8_t x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
x_1053 = lean_ctor_get(x_1052, 0);
lean_inc(x_1053);
x_1054 = lean_ctor_get(x_1052, 1);
lean_inc(x_1054);
lean_dec(x_1052);
x_1055 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_1050);
x_1056 = x_1050;
x_1057 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1046, x_1056);
x_1058 = x_1057;
lean_inc(x_2);
x_1059 = lean_array_push(x_1058, x_2);
if (x_1055 == 0)
{
lean_object* x_1139; uint8_t x_1140; 
x_1139 = l_Lean_MetavarContext_exprDependsOn(x_1040, x_1053, x_2);
lean_dec(x_2);
x_1140 = lean_unbox(x_1139);
lean_dec(x_1139);
if (x_1140 == 0)
{
x_1060 = x_1054;
goto block_1138;
}
else
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; uint8_t x_1148; 
lean_dec(x_1059);
lean_dec(x_1050);
lean_dec(x_1037);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_1141 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1141, 0, x_3);
x_1142 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_1143 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1143, 0, x_1142);
lean_ctor_set(x_1143, 1, x_1141);
x_1144 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_1145 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1145, 0, x_1143);
lean_ctor_set(x_1145, 1, x_1144);
x_1146 = lean_box(0);
x_1147 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1145, x_1146, x_13, x_1054);
lean_dec(x_13);
x_1148 = !lean_is_exclusive(x_1147);
if (x_1148 == 0)
{
return x_1147;
}
else
{
lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; 
x_1149 = lean_ctor_get(x_1147, 0);
x_1150 = lean_ctor_get(x_1147, 1);
lean_inc(x_1150);
lean_inc(x_1149);
lean_dec(x_1147);
x_1151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1151, 0, x_1149);
lean_ctor_set(x_1151, 1, x_1150);
return x_1151;
}
}
}
else
{
lean_dec(x_1053);
lean_dec(x_1040);
lean_dec(x_2);
x_1060 = x_1054;
goto block_1138;
}
block_1138:
{
uint8_t x_1061; lean_object* x_1062; 
x_1061 = 1;
x_1062 = l_Lean_Meta_revert(x_1, x_1059, x_1061, x_13, x_1060);
if (lean_obj_tag(x_1062) == 0)
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; uint8_t x_1069; lean_object* x_1070; 
x_1063 = lean_ctor_get(x_1062, 0);
lean_inc(x_1063);
x_1064 = lean_ctor_get(x_1062, 1);
lean_inc(x_1064);
lean_dec(x_1062);
x_1065 = lean_ctor_get(x_1063, 0);
lean_inc(x_1065);
x_1066 = lean_ctor_get(x_1063, 1);
lean_inc(x_1066);
lean_dec(x_1063);
x_1067 = lean_array_get_size(x_1050);
x_1068 = lean_box(0);
x_1069 = 0;
x_1070 = l_Lean_Meta_introN(x_1066, x_1067, x_1068, x_1069, x_13, x_1064);
if (lean_obj_tag(x_1070) == 0)
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; 
x_1071 = lean_ctor_get(x_1070, 0);
lean_inc(x_1071);
x_1072 = lean_ctor_get(x_1070, 1);
lean_inc(x_1072);
lean_dec(x_1070);
x_1073 = lean_ctor_get(x_1071, 0);
lean_inc(x_1073);
x_1074 = lean_ctor_get(x_1071, 1);
lean_inc(x_1074);
lean_dec(x_1071);
x_1075 = l_Lean_Meta_intro1(x_1074, x_1069, x_13, x_1072);
if (lean_obj_tag(x_1075) == 0)
{
lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; uint8_t x_1090; lean_object* x_1091; lean_object* x_1119; uint8_t x_1120; 
x_1076 = lean_ctor_get(x_1075, 0);
lean_inc(x_1076);
x_1077 = lean_ctor_get(x_1075, 1);
lean_inc(x_1077);
lean_dec(x_1075);
x_1078 = lean_ctor_get(x_1076, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1076, 1);
lean_inc(x_1079);
lean_dec(x_1076);
x_1080 = lean_box(0);
x_1081 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_1050, x_1073, x_1050, x_1046, x_1080);
lean_dec(x_1050);
x_1082 = x_1073;
x_1083 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1046, x_1082);
x_1084 = x_1083;
lean_inc(x_1078);
x_1085 = l_Lean_mkFVar(x_1078);
lean_inc(x_1079);
x_1086 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_1086, 0, x_1079);
x_1087 = lean_box(x_1055);
lean_inc(x_1079);
x_1088 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_1088, 0, x_1078);
lean_closure_set(x_1088, 1, x_8);
lean_closure_set(x_1088, 2, x_1079);
lean_closure_set(x_1088, 3, x_3);
lean_closure_set(x_1088, 4, x_4);
lean_closure_set(x_1088, 5, x_6);
lean_closure_set(x_1088, 6, x_7);
lean_closure_set(x_1088, 7, x_1037);
lean_closure_set(x_1088, 8, x_1087);
lean_closure_set(x_1088, 9, x_1065);
lean_closure_set(x_1088, 10, x_1081);
lean_closure_set(x_1088, 11, x_1084);
lean_closure_set(x_1088, 12, x_1085);
x_1089 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_1089, 0, x_1086);
lean_closure_set(x_1089, 1, x_1088);
x_1119 = lean_ctor_get(x_1077, 4);
lean_inc(x_1119);
x_1120 = lean_ctor_get_uint8(x_1119, sizeof(void*)*1);
lean_dec(x_1119);
if (x_1120 == 0)
{
x_1090 = x_1069;
x_1091 = x_1077;
goto block_1118;
}
else
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; uint8_t x_1125; 
x_1121 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_1122 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1121, x_13, x_1077);
x_1123 = lean_ctor_get(x_1122, 0);
lean_inc(x_1123);
x_1124 = lean_ctor_get(x_1122, 1);
lean_inc(x_1124);
lean_dec(x_1122);
x_1125 = lean_unbox(x_1123);
lean_dec(x_1123);
x_1090 = x_1125;
x_1091 = x_1124;
goto block_1118;
}
block_1118:
{
if (x_1090 == 0)
{
lean_object* x_1092; 
x_1092 = l_Lean_Meta_getMVarDecl(x_1079, x_13, x_1091);
if (lean_obj_tag(x_1092) == 0)
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; 
x_1093 = lean_ctor_get(x_1092, 0);
lean_inc(x_1093);
x_1094 = lean_ctor_get(x_1092, 1);
lean_inc(x_1094);
lean_dec(x_1092);
x_1095 = lean_ctor_get(x_1093, 1);
lean_inc(x_1095);
x_1096 = lean_ctor_get(x_1093, 4);
lean_inc(x_1096);
lean_dec(x_1093);
x_1097 = l_Lean_Meta_withLocalContext___rarg(x_1095, x_1096, x_1089, x_13, x_1094);
lean_dec(x_13);
return x_1097;
}
else
{
uint8_t x_1098; 
lean_dec(x_1089);
lean_dec(x_13);
x_1098 = !lean_is_exclusive(x_1092);
if (x_1098 == 0)
{
return x_1092;
}
else
{
lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; 
x_1099 = lean_ctor_get(x_1092, 0);
x_1100 = lean_ctor_get(x_1092, 1);
lean_inc(x_1100);
lean_inc(x_1099);
lean_dec(x_1092);
x_1101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1101, 0, x_1099);
lean_ctor_set(x_1101, 1, x_1100);
return x_1101;
}
}
}
else
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; 
lean_inc(x_1079);
x_1102 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1102, 0, x_1079);
x_1103 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_1104 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1104, 0, x_1103);
lean_ctor_set(x_1104, 1, x_1102);
x_1105 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_1106 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1105, x_1104, x_13, x_1091);
x_1107 = lean_ctor_get(x_1106, 1);
lean_inc(x_1107);
lean_dec(x_1106);
x_1108 = l_Lean_Meta_getMVarDecl(x_1079, x_13, x_1107);
if (lean_obj_tag(x_1108) == 0)
{
lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; 
x_1109 = lean_ctor_get(x_1108, 0);
lean_inc(x_1109);
x_1110 = lean_ctor_get(x_1108, 1);
lean_inc(x_1110);
lean_dec(x_1108);
x_1111 = lean_ctor_get(x_1109, 1);
lean_inc(x_1111);
x_1112 = lean_ctor_get(x_1109, 4);
lean_inc(x_1112);
lean_dec(x_1109);
x_1113 = l_Lean_Meta_withLocalContext___rarg(x_1111, x_1112, x_1089, x_13, x_1110);
lean_dec(x_13);
return x_1113;
}
else
{
uint8_t x_1114; 
lean_dec(x_1089);
lean_dec(x_13);
x_1114 = !lean_is_exclusive(x_1108);
if (x_1114 == 0)
{
return x_1108;
}
else
{
lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; 
x_1115 = lean_ctor_get(x_1108, 0);
x_1116 = lean_ctor_get(x_1108, 1);
lean_inc(x_1116);
lean_inc(x_1115);
lean_dec(x_1108);
x_1117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1117, 0, x_1115);
lean_ctor_set(x_1117, 1, x_1116);
return x_1117;
}
}
}
}
}
else
{
uint8_t x_1126; 
lean_dec(x_1073);
lean_dec(x_1065);
lean_dec(x_1050);
lean_dec(x_1037);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1126 = !lean_is_exclusive(x_1075);
if (x_1126 == 0)
{
return x_1075;
}
else
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; 
x_1127 = lean_ctor_get(x_1075, 0);
x_1128 = lean_ctor_get(x_1075, 1);
lean_inc(x_1128);
lean_inc(x_1127);
lean_dec(x_1075);
x_1129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1129, 0, x_1127);
lean_ctor_set(x_1129, 1, x_1128);
return x_1129;
}
}
}
else
{
uint8_t x_1130; 
lean_dec(x_1065);
lean_dec(x_1050);
lean_dec(x_1037);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1130 = !lean_is_exclusive(x_1070);
if (x_1130 == 0)
{
return x_1070;
}
else
{
lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; 
x_1131 = lean_ctor_get(x_1070, 0);
x_1132 = lean_ctor_get(x_1070, 1);
lean_inc(x_1132);
lean_inc(x_1131);
lean_dec(x_1070);
x_1133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1133, 0, x_1131);
lean_ctor_set(x_1133, 1, x_1132);
return x_1133;
}
}
}
else
{
uint8_t x_1134; 
lean_dec(x_1050);
lean_dec(x_1037);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1134 = !lean_is_exclusive(x_1062);
if (x_1134 == 0)
{
return x_1062;
}
else
{
lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; 
x_1135 = lean_ctor_get(x_1062, 0);
x_1136 = lean_ctor_get(x_1062, 1);
lean_inc(x_1136);
lean_inc(x_1135);
lean_dec(x_1062);
x_1137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1137, 0, x_1135);
lean_ctor_set(x_1137, 1, x_1136);
return x_1137;
}
}
}
}
else
{
uint8_t x_1152; 
lean_dec(x_1050);
lean_dec(x_1040);
lean_dec(x_1037);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1152 = !lean_is_exclusive(x_1052);
if (x_1152 == 0)
{
return x_1052;
}
else
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
x_1153 = lean_ctor_get(x_1052, 0);
x_1154 = lean_ctor_get(x_1052, 1);
lean_inc(x_1154);
lean_inc(x_1153);
lean_dec(x_1052);
x_1155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1155, 0, x_1153);
lean_ctor_set(x_1155, 1, x_1154);
return x_1155;
}
}
}
else
{
uint8_t x_1156; 
lean_dec(x_1040);
lean_dec(x_1037);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1156 = !lean_is_exclusive(x_1049);
if (x_1156 == 0)
{
return x_1049;
}
else
{
lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
x_1157 = lean_ctor_get(x_1049, 0);
x_1158 = lean_ctor_get(x_1049, 1);
lean_inc(x_1158);
lean_inc(x_1157);
lean_dec(x_1049);
x_1159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1159, 0, x_1157);
lean_ctor_set(x_1159, 1, x_1158);
return x_1159;
}
}
}
else
{
uint8_t x_1160; 
lean_dec(x_1037);
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
x_1160 = !lean_is_exclusive(x_1038);
if (x_1160 == 0)
{
return x_1038;
}
else
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; 
x_1161 = lean_ctor_get(x_1038, 0);
x_1162 = lean_ctor_get(x_1038, 1);
lean_inc(x_1162);
lean_inc(x_1161);
lean_dec(x_1038);
x_1163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1163, 0, x_1161);
lean_ctor_set(x_1163, 1, x_1162);
return x_1163;
}
}
}
case 10:
{
lean_object* x_1164; lean_object* x_1165; 
lean_dec(x_12);
lean_dec(x_10);
x_1164 = lean_ctor_get(x_7, 5);
lean_inc(x_1164);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1165 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_1164, x_13, x_14);
if (lean_obj_tag(x_1165) == 0)
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; 
x_1166 = lean_ctor_get(x_1165, 1);
lean_inc(x_1166);
lean_dec(x_1165);
x_1167 = lean_ctor_get(x_1166, 1);
lean_inc(x_1167);
x_1168 = lean_ctor_get(x_7, 6);
lean_inc(x_1168);
x_1169 = l_List_redLength___main___rarg(x_1168);
x_1170 = lean_mk_empty_array_with_capacity(x_1169);
lean_dec(x_1169);
lean_inc(x_1168);
x_1171 = l_List_toArrayAux___main___rarg(x_1168, x_1170);
x_1172 = x_1171;
x_1173 = lean_unsigned_to_nat(0u);
lean_inc(x_1167);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_1174 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_1174, 0, x_1);
lean_closure_set(x_1174, 1, x_6);
lean_closure_set(x_1174, 2, x_7);
lean_closure_set(x_1174, 3, x_9);
lean_closure_set(x_1174, 4, x_11);
lean_closure_set(x_1174, 5, x_1167);
lean_closure_set(x_1174, 6, x_1168);
lean_closure_set(x_1174, 7, x_1173);
lean_closure_set(x_1174, 8, x_1172);
x_1175 = x_1174;
lean_inc(x_13);
x_1176 = lean_apply_2(x_1175, x_13, x_1166);
if (lean_obj_tag(x_1176) == 0)
{
lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; 
x_1177 = lean_ctor_get(x_1176, 0);
lean_inc(x_1177);
x_1178 = lean_ctor_get(x_1176, 1);
lean_inc(x_1178);
lean_dec(x_1176);
lean_inc(x_1);
x_1179 = l_Lean_Meta_getMVarType(x_1, x_13, x_1178);
if (lean_obj_tag(x_1179) == 0)
{
lean_object* x_1180; lean_object* x_1181; uint8_t x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; 
x_1180 = lean_ctor_get(x_1179, 0);
lean_inc(x_1180);
x_1181 = lean_ctor_get(x_1179, 1);
lean_inc(x_1181);
lean_dec(x_1179);
x_1182 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_1177);
x_1183 = x_1177;
x_1184 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1173, x_1183);
x_1185 = x_1184;
lean_inc(x_2);
x_1186 = lean_array_push(x_1185, x_2);
if (x_1182 == 0)
{
lean_object* x_1266; uint8_t x_1267; 
x_1266 = l_Lean_MetavarContext_exprDependsOn(x_1167, x_1180, x_2);
lean_dec(x_2);
x_1267 = lean_unbox(x_1266);
lean_dec(x_1266);
if (x_1267 == 0)
{
x_1187 = x_1181;
goto block_1265;
}
else
{
lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; uint8_t x_1275; 
lean_dec(x_1186);
lean_dec(x_1177);
lean_dec(x_1164);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_1268 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1268, 0, x_3);
x_1269 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_1270 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1270, 0, x_1269);
lean_ctor_set(x_1270, 1, x_1268);
x_1271 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_1272 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1272, 0, x_1270);
lean_ctor_set(x_1272, 1, x_1271);
x_1273 = lean_box(0);
x_1274 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1272, x_1273, x_13, x_1181);
lean_dec(x_13);
x_1275 = !lean_is_exclusive(x_1274);
if (x_1275 == 0)
{
return x_1274;
}
else
{
lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; 
x_1276 = lean_ctor_get(x_1274, 0);
x_1277 = lean_ctor_get(x_1274, 1);
lean_inc(x_1277);
lean_inc(x_1276);
lean_dec(x_1274);
x_1278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1278, 0, x_1276);
lean_ctor_set(x_1278, 1, x_1277);
return x_1278;
}
}
}
else
{
lean_dec(x_1180);
lean_dec(x_1167);
lean_dec(x_2);
x_1187 = x_1181;
goto block_1265;
}
block_1265:
{
uint8_t x_1188; lean_object* x_1189; 
x_1188 = 1;
x_1189 = l_Lean_Meta_revert(x_1, x_1186, x_1188, x_13, x_1187);
if (lean_obj_tag(x_1189) == 0)
{
lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; uint8_t x_1196; lean_object* x_1197; 
x_1190 = lean_ctor_get(x_1189, 0);
lean_inc(x_1190);
x_1191 = lean_ctor_get(x_1189, 1);
lean_inc(x_1191);
lean_dec(x_1189);
x_1192 = lean_ctor_get(x_1190, 0);
lean_inc(x_1192);
x_1193 = lean_ctor_get(x_1190, 1);
lean_inc(x_1193);
lean_dec(x_1190);
x_1194 = lean_array_get_size(x_1177);
x_1195 = lean_box(0);
x_1196 = 0;
x_1197 = l_Lean_Meta_introN(x_1193, x_1194, x_1195, x_1196, x_13, x_1191);
if (lean_obj_tag(x_1197) == 0)
{
lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
x_1198 = lean_ctor_get(x_1197, 0);
lean_inc(x_1198);
x_1199 = lean_ctor_get(x_1197, 1);
lean_inc(x_1199);
lean_dec(x_1197);
x_1200 = lean_ctor_get(x_1198, 0);
lean_inc(x_1200);
x_1201 = lean_ctor_get(x_1198, 1);
lean_inc(x_1201);
lean_dec(x_1198);
x_1202 = l_Lean_Meta_intro1(x_1201, x_1196, x_13, x_1199);
if (lean_obj_tag(x_1202) == 0)
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; uint8_t x_1217; lean_object* x_1218; lean_object* x_1246; uint8_t x_1247; 
x_1203 = lean_ctor_get(x_1202, 0);
lean_inc(x_1203);
x_1204 = lean_ctor_get(x_1202, 1);
lean_inc(x_1204);
lean_dec(x_1202);
x_1205 = lean_ctor_get(x_1203, 0);
lean_inc(x_1205);
x_1206 = lean_ctor_get(x_1203, 1);
lean_inc(x_1206);
lean_dec(x_1203);
x_1207 = lean_box(0);
x_1208 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_1177, x_1200, x_1177, x_1173, x_1207);
lean_dec(x_1177);
x_1209 = x_1200;
x_1210 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1173, x_1209);
x_1211 = x_1210;
lean_inc(x_1205);
x_1212 = l_Lean_mkFVar(x_1205);
lean_inc(x_1206);
x_1213 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_1213, 0, x_1206);
x_1214 = lean_box(x_1182);
lean_inc(x_1206);
x_1215 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_1215, 0, x_1205);
lean_closure_set(x_1215, 1, x_8);
lean_closure_set(x_1215, 2, x_1206);
lean_closure_set(x_1215, 3, x_3);
lean_closure_set(x_1215, 4, x_4);
lean_closure_set(x_1215, 5, x_6);
lean_closure_set(x_1215, 6, x_7);
lean_closure_set(x_1215, 7, x_1164);
lean_closure_set(x_1215, 8, x_1214);
lean_closure_set(x_1215, 9, x_1192);
lean_closure_set(x_1215, 10, x_1208);
lean_closure_set(x_1215, 11, x_1211);
lean_closure_set(x_1215, 12, x_1212);
x_1216 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_1216, 0, x_1213);
lean_closure_set(x_1216, 1, x_1215);
x_1246 = lean_ctor_get(x_1204, 4);
lean_inc(x_1246);
x_1247 = lean_ctor_get_uint8(x_1246, sizeof(void*)*1);
lean_dec(x_1246);
if (x_1247 == 0)
{
x_1217 = x_1196;
x_1218 = x_1204;
goto block_1245;
}
else
{
lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; uint8_t x_1252; 
x_1248 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_1249 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1248, x_13, x_1204);
x_1250 = lean_ctor_get(x_1249, 0);
lean_inc(x_1250);
x_1251 = lean_ctor_get(x_1249, 1);
lean_inc(x_1251);
lean_dec(x_1249);
x_1252 = lean_unbox(x_1250);
lean_dec(x_1250);
x_1217 = x_1252;
x_1218 = x_1251;
goto block_1245;
}
block_1245:
{
if (x_1217 == 0)
{
lean_object* x_1219; 
x_1219 = l_Lean_Meta_getMVarDecl(x_1206, x_13, x_1218);
if (lean_obj_tag(x_1219) == 0)
{
lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; 
x_1220 = lean_ctor_get(x_1219, 0);
lean_inc(x_1220);
x_1221 = lean_ctor_get(x_1219, 1);
lean_inc(x_1221);
lean_dec(x_1219);
x_1222 = lean_ctor_get(x_1220, 1);
lean_inc(x_1222);
x_1223 = lean_ctor_get(x_1220, 4);
lean_inc(x_1223);
lean_dec(x_1220);
x_1224 = l_Lean_Meta_withLocalContext___rarg(x_1222, x_1223, x_1216, x_13, x_1221);
lean_dec(x_13);
return x_1224;
}
else
{
uint8_t x_1225; 
lean_dec(x_1216);
lean_dec(x_13);
x_1225 = !lean_is_exclusive(x_1219);
if (x_1225 == 0)
{
return x_1219;
}
else
{
lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; 
x_1226 = lean_ctor_get(x_1219, 0);
x_1227 = lean_ctor_get(x_1219, 1);
lean_inc(x_1227);
lean_inc(x_1226);
lean_dec(x_1219);
x_1228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1228, 0, x_1226);
lean_ctor_set(x_1228, 1, x_1227);
return x_1228;
}
}
}
else
{
lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; 
lean_inc(x_1206);
x_1229 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1229, 0, x_1206);
x_1230 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_1231 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1231, 0, x_1230);
lean_ctor_set(x_1231, 1, x_1229);
x_1232 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_1233 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1232, x_1231, x_13, x_1218);
x_1234 = lean_ctor_get(x_1233, 1);
lean_inc(x_1234);
lean_dec(x_1233);
x_1235 = l_Lean_Meta_getMVarDecl(x_1206, x_13, x_1234);
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
x_1240 = l_Lean_Meta_withLocalContext___rarg(x_1238, x_1239, x_1216, x_13, x_1237);
lean_dec(x_13);
return x_1240;
}
else
{
uint8_t x_1241; 
lean_dec(x_1216);
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
}
else
{
uint8_t x_1253; 
lean_dec(x_1200);
lean_dec(x_1192);
lean_dec(x_1177);
lean_dec(x_1164);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1253 = !lean_is_exclusive(x_1202);
if (x_1253 == 0)
{
return x_1202;
}
else
{
lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; 
x_1254 = lean_ctor_get(x_1202, 0);
x_1255 = lean_ctor_get(x_1202, 1);
lean_inc(x_1255);
lean_inc(x_1254);
lean_dec(x_1202);
x_1256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1256, 0, x_1254);
lean_ctor_set(x_1256, 1, x_1255);
return x_1256;
}
}
}
else
{
uint8_t x_1257; 
lean_dec(x_1192);
lean_dec(x_1177);
lean_dec(x_1164);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1257 = !lean_is_exclusive(x_1197);
if (x_1257 == 0)
{
return x_1197;
}
else
{
lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
x_1258 = lean_ctor_get(x_1197, 0);
x_1259 = lean_ctor_get(x_1197, 1);
lean_inc(x_1259);
lean_inc(x_1258);
lean_dec(x_1197);
x_1260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1260, 0, x_1258);
lean_ctor_set(x_1260, 1, x_1259);
return x_1260;
}
}
}
else
{
uint8_t x_1261; 
lean_dec(x_1177);
lean_dec(x_1164);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1261 = !lean_is_exclusive(x_1189);
if (x_1261 == 0)
{
return x_1189;
}
else
{
lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; 
x_1262 = lean_ctor_get(x_1189, 0);
x_1263 = lean_ctor_get(x_1189, 1);
lean_inc(x_1263);
lean_inc(x_1262);
lean_dec(x_1189);
x_1264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1264, 0, x_1262);
lean_ctor_set(x_1264, 1, x_1263);
return x_1264;
}
}
}
}
else
{
uint8_t x_1279; 
lean_dec(x_1177);
lean_dec(x_1167);
lean_dec(x_1164);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1279 = !lean_is_exclusive(x_1179);
if (x_1279 == 0)
{
return x_1179;
}
else
{
lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; 
x_1280 = lean_ctor_get(x_1179, 0);
x_1281 = lean_ctor_get(x_1179, 1);
lean_inc(x_1281);
lean_inc(x_1280);
lean_dec(x_1179);
x_1282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1282, 0, x_1280);
lean_ctor_set(x_1282, 1, x_1281);
return x_1282;
}
}
}
else
{
uint8_t x_1283; 
lean_dec(x_1167);
lean_dec(x_1164);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1283 = !lean_is_exclusive(x_1176);
if (x_1283 == 0)
{
return x_1176;
}
else
{
lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; 
x_1284 = lean_ctor_get(x_1176, 0);
x_1285 = lean_ctor_get(x_1176, 1);
lean_inc(x_1285);
lean_inc(x_1284);
lean_dec(x_1176);
x_1286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1286, 0, x_1284);
lean_ctor_set(x_1286, 1, x_1285);
return x_1286;
}
}
}
else
{
uint8_t x_1287; 
lean_dec(x_1164);
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
x_1287 = !lean_is_exclusive(x_1165);
if (x_1287 == 0)
{
return x_1165;
}
else
{
lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; 
x_1288 = lean_ctor_get(x_1165, 0);
x_1289 = lean_ctor_get(x_1165, 1);
lean_inc(x_1289);
lean_inc(x_1288);
lean_dec(x_1165);
x_1290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1290, 0, x_1288);
lean_ctor_set(x_1290, 1, x_1289);
return x_1290;
}
}
}
case 11:
{
lean_object* x_1291; lean_object* x_1292; 
lean_dec(x_12);
lean_dec(x_10);
x_1291 = lean_ctor_get(x_7, 5);
lean_inc(x_1291);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1292 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_1291, x_13, x_14);
if (lean_obj_tag(x_1292) == 0)
{
lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; 
x_1293 = lean_ctor_get(x_1292, 1);
lean_inc(x_1293);
lean_dec(x_1292);
x_1294 = lean_ctor_get(x_1293, 1);
lean_inc(x_1294);
x_1295 = lean_ctor_get(x_7, 6);
lean_inc(x_1295);
x_1296 = l_List_redLength___main___rarg(x_1295);
x_1297 = lean_mk_empty_array_with_capacity(x_1296);
lean_dec(x_1296);
lean_inc(x_1295);
x_1298 = l_List_toArrayAux___main___rarg(x_1295, x_1297);
x_1299 = x_1298;
x_1300 = lean_unsigned_to_nat(0u);
lean_inc(x_1294);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_1301 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_1301, 0, x_1);
lean_closure_set(x_1301, 1, x_6);
lean_closure_set(x_1301, 2, x_7);
lean_closure_set(x_1301, 3, x_9);
lean_closure_set(x_1301, 4, x_11);
lean_closure_set(x_1301, 5, x_1294);
lean_closure_set(x_1301, 6, x_1295);
lean_closure_set(x_1301, 7, x_1300);
lean_closure_set(x_1301, 8, x_1299);
x_1302 = x_1301;
lean_inc(x_13);
x_1303 = lean_apply_2(x_1302, x_13, x_1293);
if (lean_obj_tag(x_1303) == 0)
{
lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; 
x_1304 = lean_ctor_get(x_1303, 0);
lean_inc(x_1304);
x_1305 = lean_ctor_get(x_1303, 1);
lean_inc(x_1305);
lean_dec(x_1303);
lean_inc(x_1);
x_1306 = l_Lean_Meta_getMVarType(x_1, x_13, x_1305);
if (lean_obj_tag(x_1306) == 0)
{
lean_object* x_1307; lean_object* x_1308; uint8_t x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; 
x_1307 = lean_ctor_get(x_1306, 0);
lean_inc(x_1307);
x_1308 = lean_ctor_get(x_1306, 1);
lean_inc(x_1308);
lean_dec(x_1306);
x_1309 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_1304);
x_1310 = x_1304;
x_1311 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1300, x_1310);
x_1312 = x_1311;
lean_inc(x_2);
x_1313 = lean_array_push(x_1312, x_2);
if (x_1309 == 0)
{
lean_object* x_1393; uint8_t x_1394; 
x_1393 = l_Lean_MetavarContext_exprDependsOn(x_1294, x_1307, x_2);
lean_dec(x_2);
x_1394 = lean_unbox(x_1393);
lean_dec(x_1393);
if (x_1394 == 0)
{
x_1314 = x_1308;
goto block_1392;
}
else
{
lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; uint8_t x_1402; 
lean_dec(x_1313);
lean_dec(x_1304);
lean_dec(x_1291);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_1395 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1395, 0, x_3);
x_1396 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_1397 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1397, 0, x_1396);
lean_ctor_set(x_1397, 1, x_1395);
x_1398 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_1399 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1399, 0, x_1397);
lean_ctor_set(x_1399, 1, x_1398);
x_1400 = lean_box(0);
x_1401 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1399, x_1400, x_13, x_1308);
lean_dec(x_13);
x_1402 = !lean_is_exclusive(x_1401);
if (x_1402 == 0)
{
return x_1401;
}
else
{
lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; 
x_1403 = lean_ctor_get(x_1401, 0);
x_1404 = lean_ctor_get(x_1401, 1);
lean_inc(x_1404);
lean_inc(x_1403);
lean_dec(x_1401);
x_1405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1405, 0, x_1403);
lean_ctor_set(x_1405, 1, x_1404);
return x_1405;
}
}
}
else
{
lean_dec(x_1307);
lean_dec(x_1294);
lean_dec(x_2);
x_1314 = x_1308;
goto block_1392;
}
block_1392:
{
uint8_t x_1315; lean_object* x_1316; 
x_1315 = 1;
x_1316 = l_Lean_Meta_revert(x_1, x_1313, x_1315, x_13, x_1314);
if (lean_obj_tag(x_1316) == 0)
{
lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; uint8_t x_1323; lean_object* x_1324; 
x_1317 = lean_ctor_get(x_1316, 0);
lean_inc(x_1317);
x_1318 = lean_ctor_get(x_1316, 1);
lean_inc(x_1318);
lean_dec(x_1316);
x_1319 = lean_ctor_get(x_1317, 0);
lean_inc(x_1319);
x_1320 = lean_ctor_get(x_1317, 1);
lean_inc(x_1320);
lean_dec(x_1317);
x_1321 = lean_array_get_size(x_1304);
x_1322 = lean_box(0);
x_1323 = 0;
x_1324 = l_Lean_Meta_introN(x_1320, x_1321, x_1322, x_1323, x_13, x_1318);
if (lean_obj_tag(x_1324) == 0)
{
lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; 
x_1325 = lean_ctor_get(x_1324, 0);
lean_inc(x_1325);
x_1326 = lean_ctor_get(x_1324, 1);
lean_inc(x_1326);
lean_dec(x_1324);
x_1327 = lean_ctor_get(x_1325, 0);
lean_inc(x_1327);
x_1328 = lean_ctor_get(x_1325, 1);
lean_inc(x_1328);
lean_dec(x_1325);
x_1329 = l_Lean_Meta_intro1(x_1328, x_1323, x_13, x_1326);
if (lean_obj_tag(x_1329) == 0)
{
lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; uint8_t x_1344; lean_object* x_1345; lean_object* x_1373; uint8_t x_1374; 
x_1330 = lean_ctor_get(x_1329, 0);
lean_inc(x_1330);
x_1331 = lean_ctor_get(x_1329, 1);
lean_inc(x_1331);
lean_dec(x_1329);
x_1332 = lean_ctor_get(x_1330, 0);
lean_inc(x_1332);
x_1333 = lean_ctor_get(x_1330, 1);
lean_inc(x_1333);
lean_dec(x_1330);
x_1334 = lean_box(0);
x_1335 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_1304, x_1327, x_1304, x_1300, x_1334);
lean_dec(x_1304);
x_1336 = x_1327;
x_1337 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1300, x_1336);
x_1338 = x_1337;
lean_inc(x_1332);
x_1339 = l_Lean_mkFVar(x_1332);
lean_inc(x_1333);
x_1340 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_1340, 0, x_1333);
x_1341 = lean_box(x_1309);
lean_inc(x_1333);
x_1342 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_1342, 0, x_1332);
lean_closure_set(x_1342, 1, x_8);
lean_closure_set(x_1342, 2, x_1333);
lean_closure_set(x_1342, 3, x_3);
lean_closure_set(x_1342, 4, x_4);
lean_closure_set(x_1342, 5, x_6);
lean_closure_set(x_1342, 6, x_7);
lean_closure_set(x_1342, 7, x_1291);
lean_closure_set(x_1342, 8, x_1341);
lean_closure_set(x_1342, 9, x_1319);
lean_closure_set(x_1342, 10, x_1335);
lean_closure_set(x_1342, 11, x_1338);
lean_closure_set(x_1342, 12, x_1339);
x_1343 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_1343, 0, x_1340);
lean_closure_set(x_1343, 1, x_1342);
x_1373 = lean_ctor_get(x_1331, 4);
lean_inc(x_1373);
x_1374 = lean_ctor_get_uint8(x_1373, sizeof(void*)*1);
lean_dec(x_1373);
if (x_1374 == 0)
{
x_1344 = x_1323;
x_1345 = x_1331;
goto block_1372;
}
else
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; uint8_t x_1379; 
x_1375 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_1376 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1375, x_13, x_1331);
x_1377 = lean_ctor_get(x_1376, 0);
lean_inc(x_1377);
x_1378 = lean_ctor_get(x_1376, 1);
lean_inc(x_1378);
lean_dec(x_1376);
x_1379 = lean_unbox(x_1377);
lean_dec(x_1377);
x_1344 = x_1379;
x_1345 = x_1378;
goto block_1372;
}
block_1372:
{
if (x_1344 == 0)
{
lean_object* x_1346; 
x_1346 = l_Lean_Meta_getMVarDecl(x_1333, x_13, x_1345);
if (lean_obj_tag(x_1346) == 0)
{
lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; 
x_1347 = lean_ctor_get(x_1346, 0);
lean_inc(x_1347);
x_1348 = lean_ctor_get(x_1346, 1);
lean_inc(x_1348);
lean_dec(x_1346);
x_1349 = lean_ctor_get(x_1347, 1);
lean_inc(x_1349);
x_1350 = lean_ctor_get(x_1347, 4);
lean_inc(x_1350);
lean_dec(x_1347);
x_1351 = l_Lean_Meta_withLocalContext___rarg(x_1349, x_1350, x_1343, x_13, x_1348);
lean_dec(x_13);
return x_1351;
}
else
{
uint8_t x_1352; 
lean_dec(x_1343);
lean_dec(x_13);
x_1352 = !lean_is_exclusive(x_1346);
if (x_1352 == 0)
{
return x_1346;
}
else
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; 
x_1353 = lean_ctor_get(x_1346, 0);
x_1354 = lean_ctor_get(x_1346, 1);
lean_inc(x_1354);
lean_inc(x_1353);
lean_dec(x_1346);
x_1355 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1355, 0, x_1353);
lean_ctor_set(x_1355, 1, x_1354);
return x_1355;
}
}
}
else
{
lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; 
lean_inc(x_1333);
x_1356 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1356, 0, x_1333);
x_1357 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_1358 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1358, 0, x_1357);
lean_ctor_set(x_1358, 1, x_1356);
x_1359 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_1360 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1359, x_1358, x_13, x_1345);
x_1361 = lean_ctor_get(x_1360, 1);
lean_inc(x_1361);
lean_dec(x_1360);
x_1362 = l_Lean_Meta_getMVarDecl(x_1333, x_13, x_1361);
if (lean_obj_tag(x_1362) == 0)
{
lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; 
x_1363 = lean_ctor_get(x_1362, 0);
lean_inc(x_1363);
x_1364 = lean_ctor_get(x_1362, 1);
lean_inc(x_1364);
lean_dec(x_1362);
x_1365 = lean_ctor_get(x_1363, 1);
lean_inc(x_1365);
x_1366 = lean_ctor_get(x_1363, 4);
lean_inc(x_1366);
lean_dec(x_1363);
x_1367 = l_Lean_Meta_withLocalContext___rarg(x_1365, x_1366, x_1343, x_13, x_1364);
lean_dec(x_13);
return x_1367;
}
else
{
uint8_t x_1368; 
lean_dec(x_1343);
lean_dec(x_13);
x_1368 = !lean_is_exclusive(x_1362);
if (x_1368 == 0)
{
return x_1362;
}
else
{
lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; 
x_1369 = lean_ctor_get(x_1362, 0);
x_1370 = lean_ctor_get(x_1362, 1);
lean_inc(x_1370);
lean_inc(x_1369);
lean_dec(x_1362);
x_1371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1371, 0, x_1369);
lean_ctor_set(x_1371, 1, x_1370);
return x_1371;
}
}
}
}
}
else
{
uint8_t x_1380; 
lean_dec(x_1327);
lean_dec(x_1319);
lean_dec(x_1304);
lean_dec(x_1291);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1380 = !lean_is_exclusive(x_1329);
if (x_1380 == 0)
{
return x_1329;
}
else
{
lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; 
x_1381 = lean_ctor_get(x_1329, 0);
x_1382 = lean_ctor_get(x_1329, 1);
lean_inc(x_1382);
lean_inc(x_1381);
lean_dec(x_1329);
x_1383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1383, 0, x_1381);
lean_ctor_set(x_1383, 1, x_1382);
return x_1383;
}
}
}
else
{
uint8_t x_1384; 
lean_dec(x_1319);
lean_dec(x_1304);
lean_dec(x_1291);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1384 = !lean_is_exclusive(x_1324);
if (x_1384 == 0)
{
return x_1324;
}
else
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; 
x_1385 = lean_ctor_get(x_1324, 0);
x_1386 = lean_ctor_get(x_1324, 1);
lean_inc(x_1386);
lean_inc(x_1385);
lean_dec(x_1324);
x_1387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1387, 0, x_1385);
lean_ctor_set(x_1387, 1, x_1386);
return x_1387;
}
}
}
else
{
uint8_t x_1388; 
lean_dec(x_1304);
lean_dec(x_1291);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1388 = !lean_is_exclusive(x_1316);
if (x_1388 == 0)
{
return x_1316;
}
else
{
lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; 
x_1389 = lean_ctor_get(x_1316, 0);
x_1390 = lean_ctor_get(x_1316, 1);
lean_inc(x_1390);
lean_inc(x_1389);
lean_dec(x_1316);
x_1391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1391, 0, x_1389);
lean_ctor_set(x_1391, 1, x_1390);
return x_1391;
}
}
}
}
else
{
uint8_t x_1406; 
lean_dec(x_1304);
lean_dec(x_1294);
lean_dec(x_1291);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1406 = !lean_is_exclusive(x_1306);
if (x_1406 == 0)
{
return x_1306;
}
else
{
lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; 
x_1407 = lean_ctor_get(x_1306, 0);
x_1408 = lean_ctor_get(x_1306, 1);
lean_inc(x_1408);
lean_inc(x_1407);
lean_dec(x_1306);
x_1409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1409, 0, x_1407);
lean_ctor_set(x_1409, 1, x_1408);
return x_1409;
}
}
}
else
{
uint8_t x_1410; 
lean_dec(x_1294);
lean_dec(x_1291);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1410 = !lean_is_exclusive(x_1303);
if (x_1410 == 0)
{
return x_1303;
}
else
{
lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; 
x_1411 = lean_ctor_get(x_1303, 0);
x_1412 = lean_ctor_get(x_1303, 1);
lean_inc(x_1412);
lean_inc(x_1411);
lean_dec(x_1303);
x_1413 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1413, 0, x_1411);
lean_ctor_set(x_1413, 1, x_1412);
return x_1413;
}
}
}
else
{
uint8_t x_1414; 
lean_dec(x_1291);
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
x_1414 = !lean_is_exclusive(x_1292);
if (x_1414 == 0)
{
return x_1292;
}
else
{
lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; 
x_1415 = lean_ctor_get(x_1292, 0);
x_1416 = lean_ctor_get(x_1292, 1);
lean_inc(x_1416);
lean_inc(x_1415);
lean_dec(x_1292);
x_1417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1417, 0, x_1415);
lean_ctor_set(x_1417, 1, x_1416);
return x_1417;
}
}
}
default: 
{
lean_object* x_1418; lean_object* x_1419; 
lean_dec(x_12);
lean_dec(x_10);
x_1418 = lean_ctor_get(x_7, 5);
lean_inc(x_1418);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1419 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_1418, x_13, x_14);
if (lean_obj_tag(x_1419) == 0)
{
lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; 
x_1420 = lean_ctor_get(x_1419, 1);
lean_inc(x_1420);
lean_dec(x_1419);
x_1421 = lean_ctor_get(x_1420, 1);
lean_inc(x_1421);
x_1422 = lean_ctor_get(x_7, 6);
lean_inc(x_1422);
x_1423 = l_List_redLength___main___rarg(x_1422);
x_1424 = lean_mk_empty_array_with_capacity(x_1423);
lean_dec(x_1423);
lean_inc(x_1422);
x_1425 = l_List_toArrayAux___main___rarg(x_1422, x_1424);
x_1426 = x_1425;
x_1427 = lean_unsigned_to_nat(0u);
lean_inc(x_1421);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_1428 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_1428, 0, x_1);
lean_closure_set(x_1428, 1, x_6);
lean_closure_set(x_1428, 2, x_7);
lean_closure_set(x_1428, 3, x_9);
lean_closure_set(x_1428, 4, x_11);
lean_closure_set(x_1428, 5, x_1421);
lean_closure_set(x_1428, 6, x_1422);
lean_closure_set(x_1428, 7, x_1427);
lean_closure_set(x_1428, 8, x_1426);
x_1429 = x_1428;
lean_inc(x_13);
x_1430 = lean_apply_2(x_1429, x_13, x_1420);
if (lean_obj_tag(x_1430) == 0)
{
lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; 
x_1431 = lean_ctor_get(x_1430, 0);
lean_inc(x_1431);
x_1432 = lean_ctor_get(x_1430, 1);
lean_inc(x_1432);
lean_dec(x_1430);
lean_inc(x_1);
x_1433 = l_Lean_Meta_getMVarType(x_1, x_13, x_1432);
if (lean_obj_tag(x_1433) == 0)
{
lean_object* x_1434; lean_object* x_1435; uint8_t x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; 
x_1434 = lean_ctor_get(x_1433, 0);
lean_inc(x_1434);
x_1435 = lean_ctor_get(x_1433, 1);
lean_inc(x_1435);
lean_dec(x_1433);
x_1436 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_1431);
x_1437 = x_1431;
x_1438 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1427, x_1437);
x_1439 = x_1438;
lean_inc(x_2);
x_1440 = lean_array_push(x_1439, x_2);
if (x_1436 == 0)
{
lean_object* x_1520; uint8_t x_1521; 
x_1520 = l_Lean_MetavarContext_exprDependsOn(x_1421, x_1434, x_2);
lean_dec(x_2);
x_1521 = lean_unbox(x_1520);
lean_dec(x_1520);
if (x_1521 == 0)
{
x_1441 = x_1435;
goto block_1519;
}
else
{
lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; uint8_t x_1529; 
lean_dec(x_1440);
lean_dec(x_1431);
lean_dec(x_1418);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_1522 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1522, 0, x_3);
x_1523 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_1524 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1524, 0, x_1523);
lean_ctor_set(x_1524, 1, x_1522);
x_1525 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_1526 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1526, 0, x_1524);
lean_ctor_set(x_1526, 1, x_1525);
x_1527 = lean_box(0);
x_1528 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1526, x_1527, x_13, x_1435);
lean_dec(x_13);
x_1529 = !lean_is_exclusive(x_1528);
if (x_1529 == 0)
{
return x_1528;
}
else
{
lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; 
x_1530 = lean_ctor_get(x_1528, 0);
x_1531 = lean_ctor_get(x_1528, 1);
lean_inc(x_1531);
lean_inc(x_1530);
lean_dec(x_1528);
x_1532 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1532, 0, x_1530);
lean_ctor_set(x_1532, 1, x_1531);
return x_1532;
}
}
}
else
{
lean_dec(x_1434);
lean_dec(x_1421);
lean_dec(x_2);
x_1441 = x_1435;
goto block_1519;
}
block_1519:
{
uint8_t x_1442; lean_object* x_1443; 
x_1442 = 1;
x_1443 = l_Lean_Meta_revert(x_1, x_1440, x_1442, x_13, x_1441);
if (lean_obj_tag(x_1443) == 0)
{
lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; uint8_t x_1450; lean_object* x_1451; 
x_1444 = lean_ctor_get(x_1443, 0);
lean_inc(x_1444);
x_1445 = lean_ctor_get(x_1443, 1);
lean_inc(x_1445);
lean_dec(x_1443);
x_1446 = lean_ctor_get(x_1444, 0);
lean_inc(x_1446);
x_1447 = lean_ctor_get(x_1444, 1);
lean_inc(x_1447);
lean_dec(x_1444);
x_1448 = lean_array_get_size(x_1431);
x_1449 = lean_box(0);
x_1450 = 0;
x_1451 = l_Lean_Meta_introN(x_1447, x_1448, x_1449, x_1450, x_13, x_1445);
if (lean_obj_tag(x_1451) == 0)
{
lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; 
x_1452 = lean_ctor_get(x_1451, 0);
lean_inc(x_1452);
x_1453 = lean_ctor_get(x_1451, 1);
lean_inc(x_1453);
lean_dec(x_1451);
x_1454 = lean_ctor_get(x_1452, 0);
lean_inc(x_1454);
x_1455 = lean_ctor_get(x_1452, 1);
lean_inc(x_1455);
lean_dec(x_1452);
x_1456 = l_Lean_Meta_intro1(x_1455, x_1450, x_13, x_1453);
if (lean_obj_tag(x_1456) == 0)
{
lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; uint8_t x_1471; lean_object* x_1472; lean_object* x_1500; uint8_t x_1501; 
x_1457 = lean_ctor_get(x_1456, 0);
lean_inc(x_1457);
x_1458 = lean_ctor_get(x_1456, 1);
lean_inc(x_1458);
lean_dec(x_1456);
x_1459 = lean_ctor_get(x_1457, 0);
lean_inc(x_1459);
x_1460 = lean_ctor_get(x_1457, 1);
lean_inc(x_1460);
lean_dec(x_1457);
x_1461 = lean_box(0);
x_1462 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_1431, x_1454, x_1431, x_1427, x_1461);
lean_dec(x_1431);
x_1463 = x_1454;
x_1464 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1427, x_1463);
x_1465 = x_1464;
lean_inc(x_1459);
x_1466 = l_Lean_mkFVar(x_1459);
lean_inc(x_1460);
x_1467 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_1467, 0, x_1460);
x_1468 = lean_box(x_1436);
lean_inc(x_1460);
x_1469 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_1469, 0, x_1459);
lean_closure_set(x_1469, 1, x_8);
lean_closure_set(x_1469, 2, x_1460);
lean_closure_set(x_1469, 3, x_3);
lean_closure_set(x_1469, 4, x_4);
lean_closure_set(x_1469, 5, x_6);
lean_closure_set(x_1469, 6, x_7);
lean_closure_set(x_1469, 7, x_1418);
lean_closure_set(x_1469, 8, x_1468);
lean_closure_set(x_1469, 9, x_1446);
lean_closure_set(x_1469, 10, x_1462);
lean_closure_set(x_1469, 11, x_1465);
lean_closure_set(x_1469, 12, x_1466);
x_1470 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_1470, 0, x_1467);
lean_closure_set(x_1470, 1, x_1469);
x_1500 = lean_ctor_get(x_1458, 4);
lean_inc(x_1500);
x_1501 = lean_ctor_get_uint8(x_1500, sizeof(void*)*1);
lean_dec(x_1500);
if (x_1501 == 0)
{
x_1471 = x_1450;
x_1472 = x_1458;
goto block_1499;
}
else
{
lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; uint8_t x_1506; 
x_1502 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_1503 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1502, x_13, x_1458);
x_1504 = lean_ctor_get(x_1503, 0);
lean_inc(x_1504);
x_1505 = lean_ctor_get(x_1503, 1);
lean_inc(x_1505);
lean_dec(x_1503);
x_1506 = lean_unbox(x_1504);
lean_dec(x_1504);
x_1471 = x_1506;
x_1472 = x_1505;
goto block_1499;
}
block_1499:
{
if (x_1471 == 0)
{
lean_object* x_1473; 
x_1473 = l_Lean_Meta_getMVarDecl(x_1460, x_13, x_1472);
if (lean_obj_tag(x_1473) == 0)
{
lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; 
x_1474 = lean_ctor_get(x_1473, 0);
lean_inc(x_1474);
x_1475 = lean_ctor_get(x_1473, 1);
lean_inc(x_1475);
lean_dec(x_1473);
x_1476 = lean_ctor_get(x_1474, 1);
lean_inc(x_1476);
x_1477 = lean_ctor_get(x_1474, 4);
lean_inc(x_1477);
lean_dec(x_1474);
x_1478 = l_Lean_Meta_withLocalContext___rarg(x_1476, x_1477, x_1470, x_13, x_1475);
lean_dec(x_13);
return x_1478;
}
else
{
uint8_t x_1479; 
lean_dec(x_1470);
lean_dec(x_13);
x_1479 = !lean_is_exclusive(x_1473);
if (x_1479 == 0)
{
return x_1473;
}
else
{
lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; 
x_1480 = lean_ctor_get(x_1473, 0);
x_1481 = lean_ctor_get(x_1473, 1);
lean_inc(x_1481);
lean_inc(x_1480);
lean_dec(x_1473);
x_1482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1482, 0, x_1480);
lean_ctor_set(x_1482, 1, x_1481);
return x_1482;
}
}
}
else
{
lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; 
lean_inc(x_1460);
x_1483 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1483, 0, x_1460);
x_1484 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_1485 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1485, 0, x_1484);
lean_ctor_set(x_1485, 1, x_1483);
x_1486 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_1487 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1486, x_1485, x_13, x_1472);
x_1488 = lean_ctor_get(x_1487, 1);
lean_inc(x_1488);
lean_dec(x_1487);
x_1489 = l_Lean_Meta_getMVarDecl(x_1460, x_13, x_1488);
if (lean_obj_tag(x_1489) == 0)
{
lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; 
x_1490 = lean_ctor_get(x_1489, 0);
lean_inc(x_1490);
x_1491 = lean_ctor_get(x_1489, 1);
lean_inc(x_1491);
lean_dec(x_1489);
x_1492 = lean_ctor_get(x_1490, 1);
lean_inc(x_1492);
x_1493 = lean_ctor_get(x_1490, 4);
lean_inc(x_1493);
lean_dec(x_1490);
x_1494 = l_Lean_Meta_withLocalContext___rarg(x_1492, x_1493, x_1470, x_13, x_1491);
lean_dec(x_13);
return x_1494;
}
else
{
uint8_t x_1495; 
lean_dec(x_1470);
lean_dec(x_13);
x_1495 = !lean_is_exclusive(x_1489);
if (x_1495 == 0)
{
return x_1489;
}
else
{
lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; 
x_1496 = lean_ctor_get(x_1489, 0);
x_1497 = lean_ctor_get(x_1489, 1);
lean_inc(x_1497);
lean_inc(x_1496);
lean_dec(x_1489);
x_1498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1498, 0, x_1496);
lean_ctor_set(x_1498, 1, x_1497);
return x_1498;
}
}
}
}
}
else
{
uint8_t x_1507; 
lean_dec(x_1454);
lean_dec(x_1446);
lean_dec(x_1431);
lean_dec(x_1418);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1507 = !lean_is_exclusive(x_1456);
if (x_1507 == 0)
{
return x_1456;
}
else
{
lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; 
x_1508 = lean_ctor_get(x_1456, 0);
x_1509 = lean_ctor_get(x_1456, 1);
lean_inc(x_1509);
lean_inc(x_1508);
lean_dec(x_1456);
x_1510 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1510, 0, x_1508);
lean_ctor_set(x_1510, 1, x_1509);
return x_1510;
}
}
}
else
{
uint8_t x_1511; 
lean_dec(x_1446);
lean_dec(x_1431);
lean_dec(x_1418);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1511 = !lean_is_exclusive(x_1451);
if (x_1511 == 0)
{
return x_1451;
}
else
{
lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; 
x_1512 = lean_ctor_get(x_1451, 0);
x_1513 = lean_ctor_get(x_1451, 1);
lean_inc(x_1513);
lean_inc(x_1512);
lean_dec(x_1451);
x_1514 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1514, 0, x_1512);
lean_ctor_set(x_1514, 1, x_1513);
return x_1514;
}
}
}
else
{
uint8_t x_1515; 
lean_dec(x_1431);
lean_dec(x_1418);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1515 = !lean_is_exclusive(x_1443);
if (x_1515 == 0)
{
return x_1443;
}
else
{
lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; 
x_1516 = lean_ctor_get(x_1443, 0);
x_1517 = lean_ctor_get(x_1443, 1);
lean_inc(x_1517);
lean_inc(x_1516);
lean_dec(x_1443);
x_1518 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1518, 0, x_1516);
lean_ctor_set(x_1518, 1, x_1517);
return x_1518;
}
}
}
}
else
{
uint8_t x_1533; 
lean_dec(x_1431);
lean_dec(x_1421);
lean_dec(x_1418);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1533 = !lean_is_exclusive(x_1433);
if (x_1533 == 0)
{
return x_1433;
}
else
{
lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; 
x_1534 = lean_ctor_get(x_1433, 0);
x_1535 = lean_ctor_get(x_1433, 1);
lean_inc(x_1535);
lean_inc(x_1534);
lean_dec(x_1433);
x_1536 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1536, 0, x_1534);
lean_ctor_set(x_1536, 1, x_1535);
return x_1536;
}
}
}
else
{
uint8_t x_1537; 
lean_dec(x_1421);
lean_dec(x_1418);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1537 = !lean_is_exclusive(x_1430);
if (x_1537 == 0)
{
return x_1430;
}
else
{
lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; 
x_1538 = lean_ctor_get(x_1430, 0);
x_1539 = lean_ctor_get(x_1430, 1);
lean_inc(x_1539);
lean_inc(x_1538);
lean_dec(x_1430);
x_1540 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1540, 0, x_1538);
lean_ctor_set(x_1540, 1, x_1539);
return x_1540;
}
}
}
else
{
uint8_t x_1541; 
lean_dec(x_1418);
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
x_1541 = !lean_is_exclusive(x_1419);
if (x_1541 == 0)
{
return x_1419;
}
else
{
lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; 
x_1542 = lean_ctor_get(x_1419, 0);
x_1543 = lean_ctor_get(x_1419, 1);
lean_inc(x_1543);
lean_inc(x_1542);
lean_dec(x_1419);
x_1544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1544, 0, x_1542);
lean_ctor_set(x_1544, 1, x_1543);
return x_1544;
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
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_3);
x_11 = l_Lean_Meta_getLocalDecl(x_3, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
lean_inc(x_7);
lean_inc(x_4);
x_15 = l_Lean_Meta_mkRecursorInfo(x_4, x_14, x_7, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_LocalDecl_type(x_12);
lean_dec(x_12);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_7);
lean_inc(x_18);
x_20 = l_Lean_Meta_whnfUntil(x_18, x_19, x_7, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(x_1, x_18, x_7, x_22);
lean_dec(x_7);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_18);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Expr_getAppNumArgsAux___main(x_25, x_26);
x_28 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_27);
x_29 = lean_mk_array(x_27, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_27, x_30);
lean_dec(x_27);
lean_inc(x_25);
x_32 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9(x_1, x_3, x_4, x_5, x_6, x_2, x_16, x_19, x_25, x_25, x_29, x_31, x_7, x_24);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
return x_15;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_15, 0);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_15);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_11);
if (x_41 == 0)
{
return x_11;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_11, 0);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_11);
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
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_9);
if (x_45 == 0)
{
return x_9;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_9, 0);
x_47 = lean_ctor_get(x_9, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_9);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Meta_induction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_9 = l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_induction___lambda__1___boxed), 8, 6);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_4);
lean_closure_set(x_10, 5, x_9);
x_11 = l_Lean_Meta_getMVarDecl(x_1, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 4);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Meta_withLocalContext___rarg(x_14, x_15, x_10, x_6, x_13);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
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
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
return x_14;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
return x_14;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___main___at_Lean_Meta_induction___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_9;
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_6);
lean_dec(x_6);
x_20 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(x_1, x_2, x_3, x_4, x_5, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_20;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_9);
lean_dec(x_9);
x_18 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_18;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_15;
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
lean_object* l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
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
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__1 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__1);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__2 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__2);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__3 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__3);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__4 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__4();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__4);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__5 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__5();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__5);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__6 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__6();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___closed__6);
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
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__9 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__9();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__9);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__2 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__2);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__3 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__3);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__4 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__4);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__6 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__6);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__7 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__7();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__7);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8);
res = l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
