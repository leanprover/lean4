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
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_4);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_24 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8;
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
x_31 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_32 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
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
x_46 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_47 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_18 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_12);
x_22 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_23 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
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
x_40 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_41 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
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
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_nat_dec_le(x_8, x_11);
if (x_61 == 0)
{
x_62 = x_60;
goto block_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_dec(x_59);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_197 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_198 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_199 = l_Lean_Meta_throwTacticEx___rarg(x_197, x_1, x_198, x_16, x_60);
lean_dec(x_16);
x_200 = !lean_is_exclusive(x_199);
if (x_200 == 0)
{
return x_199;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_199, 0);
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_199);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
block_196:
{
if (lean_obj_tag(x_19) == 7)
{
lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; uint8_t x_145; uint8_t x_146; 
x_63 = lean_ctor_get(x_19, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_19, 1);
lean_inc(x_64);
x_65 = lean_ctor_get_uint64(x_19, sizeof(void*)*3);
x_66 = l_Lean_Expr_headBeta(x_64);
x_145 = (uint8_t)((x_65 << 24) >> 61);
x_146 = l_Lean_BinderInfo_isInstImplicit(x_145);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_box(0);
x_67 = x_147;
goto block_144;
}
else
{
uint8_t x_148; 
x_148 = l_Array_isEmpty___rarg(x_2);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_box(0);
x_67 = x_149;
goto block_144;
}
else
{
lean_object* x_150; 
lean_inc(x_16);
lean_inc(x_66);
x_150 = l_Lean_Meta_synthInstance_x3f(x_66, x_16, x_62);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = l_Lean_Name_append___main(x_59, x_63);
lean_dec(x_59);
x_154 = 2;
lean_inc(x_16);
x_155 = l_Lean_Meta_mkFreshExprMVar(x_66, x_153, x_154, x_16, x_152);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
lean_inc(x_156);
x_158 = l_Lean_mkApp(x_12, x_156);
lean_inc(x_16);
lean_inc(x_1);
x_159 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_19, x_156, x_16, x_157);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_unsigned_to_nat(1u);
x_163 = lean_nat_add(x_10, x_162);
lean_dec(x_10);
x_164 = lean_nat_add(x_11, x_162);
lean_dec(x_11);
x_165 = l_Lean_Expr_mvarId_x21(x_156);
lean_dec(x_156);
x_166 = lean_box(0);
x_167 = l_Array_empty___closed__1;
x_168 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_167);
lean_ctor_set(x_168, 2, x_166);
x_169 = lean_array_push(x_15, x_168);
x_10 = x_163;
x_11 = x_164;
x_12 = x_158;
x_13 = x_160;
x_15 = x_169;
x_17 = x_161;
goto _start;
}
else
{
uint8_t x_171; 
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_171 = !lean_is_exclusive(x_159);
if (x_171 == 0)
{
return x_159;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_159, 0);
x_173 = lean_ctor_get(x_159, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_159);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_59);
x_175 = lean_ctor_get(x_150, 1);
lean_inc(x_175);
lean_dec(x_150);
x_176 = lean_ctor_get(x_151, 0);
lean_inc(x_176);
lean_dec(x_151);
lean_inc(x_176);
x_177 = l_Lean_mkApp(x_12, x_176);
lean_inc(x_16);
lean_inc(x_1);
x_178 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_19, x_176, x_16, x_175);
lean_dec(x_176);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_unsigned_to_nat(1u);
x_182 = lean_nat_add(x_10, x_181);
lean_dec(x_10);
x_183 = lean_nat_add(x_11, x_181);
lean_dec(x_11);
x_10 = x_182;
x_11 = x_183;
x_12 = x_177;
x_13 = x_179;
x_17 = x_180;
goto _start;
}
else
{
uint8_t x_185; 
lean_dec(x_177);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_185 = !lean_is_exclusive(x_178);
if (x_185 == 0)
{
return x_178;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_178, 0);
x_187 = lean_ctor_get(x_178, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_178);
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
uint8_t x_189; 
lean_dec(x_66);
lean_dec(x_63);
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
x_189 = !lean_is_exclusive(x_150);
if (x_189 == 0)
{
return x_150;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_150, 0);
x_191 = lean_ctor_get(x_150, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_150);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
}
block_144:
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_67);
lean_inc(x_66);
x_68 = l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_66);
x_69 = lean_nat_dec_lt(x_68, x_6);
x_70 = lean_nat_sub(x_68, x_6);
lean_dec(x_68);
x_71 = lean_array_get_size(x_4);
x_72 = lean_array_get_size(x_7);
x_73 = lean_nat_sub(x_71, x_72);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_sub(x_73, x_74);
lean_dec(x_73);
x_76 = lean_array_get_size(x_2);
x_77 = lean_nat_dec_lt(x_11, x_76);
lean_dec(x_76);
x_78 = l_Lean_Name_append___main(x_59, x_63);
lean_dec(x_59);
if (x_77 == 0)
{
lean_object* x_142; 
x_142 = lean_box(0);
x_79 = x_142;
goto block_141;
}
else
{
lean_object* x_143; 
x_143 = lean_array_fget(x_2, x_11);
x_79 = x_143;
goto block_141;
}
block_141:
{
lean_object* x_80; 
if (x_69 == 0)
{
x_80 = x_62;
goto block_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_66);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_134 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_135 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_136 = l_Lean_Meta_throwTacticEx___rarg(x_134, x_1, x_135, x_16, x_62);
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
block_133:
{
uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = 2;
lean_inc(x_16);
x_82 = l_Lean_Meta_mkFreshExprMVar(x_66, x_78, x_81, x_16, x_80);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_83);
x_85 = l_Lean_mkApp(x_12, x_83);
lean_inc(x_16);
lean_inc(x_1);
x_86 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_19, x_83, x_16, x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Expr_mvarId_x21(x_83);
lean_dec(x_83);
x_90 = l_Lean_Expr_fvarId_x21(x_5);
x_91 = l_Lean_Meta_tryClear(x_89, x_90, x_16, x_88);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = 1;
x_95 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_94, x_92, x_70, x_79, x_16, x_93);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; 
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
x_100 = lean_box(0);
x_101 = 0;
x_102 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_101, x_99, x_75, x_100, x_16, x_97);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
lean_inc(x_9);
lean_inc(x_71);
x_107 = l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(x_4, x_7, x_72, x_105, x_71, x_71, x_9);
lean_dec(x_71);
lean_dec(x_105);
lean_dec(x_72);
x_108 = x_98;
x_109 = lean_unsigned_to_nat(0u);
x_110 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_109, x_108);
x_111 = x_110;
x_112 = lean_nat_add(x_10, x_74);
lean_dec(x_10);
x_113 = lean_nat_add(x_11, x_74);
lean_dec(x_11);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_106);
lean_ctor_set(x_114, 1, x_111);
lean_ctor_set(x_114, 2, x_107);
x_115 = lean_array_push(x_15, x_114);
x_10 = x_112;
x_11 = x_113;
x_12 = x_85;
x_13 = x_87;
x_15 = x_115;
x_17 = x_104;
goto _start;
}
else
{
uint8_t x_117; 
lean_dec(x_98);
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_102);
if (x_117 == 0)
{
return x_102;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_102, 0);
x_119 = lean_ctor_get(x_102, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_102);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_95);
if (x_121 == 0)
{
return x_95;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_95, 0);
x_123 = lean_ctor_get(x_95, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_95);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_79);
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_91);
if (x_125 == 0)
{
return x_91;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_91, 0);
x_127 = lean_ctor_get(x_91, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_91);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_85);
lean_dec(x_83);
lean_dec(x_79);
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_86);
if (x_129 == 0)
{
return x_86;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_86, 0);
x_131 = lean_ctor_get(x_86, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_86);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_59);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_193 = l_Lean_Meta_isClassQuick___main___closed__1;
x_194 = l_unreachable_x21___rarg(x_193);
x_195 = lean_apply_2(x_194, x_16, x_62);
return x_195;
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_204 = !lean_is_exclusive(x_58);
if (x_204 == 0)
{
return x_58;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_58, 0);
x_206 = lean_ctor_get(x_58, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_58);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_12);
lean_ctor_set(x_208, 1, x_19);
x_209 = lean_unsigned_to_nat(0u);
lean_inc(x_16);
lean_inc(x_1);
x_210 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(x_1, x_7, x_7, x_209, x_208, x_16, x_20);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
lean_inc(x_5);
x_215 = l_Lean_mkApp(x_213, x_5);
lean_inc(x_16);
lean_inc(x_1);
x_216 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_214, x_5, x_16, x_212);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_unsigned_to_nat(1u);
x_220 = lean_nat_add(x_10, x_219);
lean_dec(x_10);
x_221 = lean_array_get_size(x_7);
x_222 = lean_nat_add(x_220, x_221);
lean_dec(x_221);
lean_dec(x_220);
x_223 = 1;
x_10 = x_222;
x_12 = x_215;
x_13 = x_217;
x_14 = x_223;
x_17 = x_218;
goto _start;
}
else
{
uint8_t x_225; 
lean_dec(x_215);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_225 = !lean_is_exclusive(x_216);
if (x_225 == 0)
{
return x_216;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_216, 0);
x_227 = lean_ctor_get(x_216, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_216);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
else
{
uint8_t x_229; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_229 = !lean_is_exclusive(x_210);
if (x_229 == 0)
{
return x_210;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_210, 0);
x_231 = lean_ctor_get(x_210, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_210);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
}
}
}
else
{
uint8_t x_233; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_233 = !lean_is_exclusive(x_18);
if (x_233 == 0)
{
return x_18;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_18, 0);
x_235 = lean_ctor_get(x_18, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_18);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = l_Lean_indentExpr(x_5);
x_7 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3;
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_10 = l_Lean_Meta_throwTacticEx___rarg(x_9, x_1, x_8, x_3, x_4);
return x_10;
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
uint8_t x_107; 
x_107 = lean_expr_eqv(x_21, x_9);
x_25 = x_107;
goto block_106;
}
else
{
uint8_t x_108; 
x_108 = 0;
x_25 = x_108;
goto block_106;
}
block_106:
{
uint8_t x_26; 
if (x_25 == 0)
{
uint8_t x_104; 
x_104 = 0;
x_26 = x_104;
goto block_103;
}
else
{
uint8_t x_105; 
x_105 = 1;
x_26 = x_105;
goto block_103;
}
block_103:
{
uint8_t x_27; 
if (x_23 == 0)
{
uint8_t x_99; 
x_99 = 0;
x_27 = x_99;
goto block_98;
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = l_Lean_Expr_fvarId_x21(x_9);
lean_inc(x_21);
lean_inc(x_6);
x_101 = l_Lean_MetavarContext_exprDependsOn(x_6, x_21, x_100);
lean_dec(x_100);
x_102 = lean_unbox(x_101);
lean_dec(x_101);
x_27 = x_102;
goto block_98;
}
block_98:
{
uint8_t x_28; 
if (x_27 == 0)
{
uint8_t x_96; 
x_96 = 0;
x_28 = x_96;
goto block_95;
}
else
{
uint8_t x_97; 
x_97 = 1;
x_28 = x_97;
goto block_95;
}
block_95:
{
uint8_t x_29; 
if (x_24 == 0)
{
uint8_t x_91; 
x_91 = 0;
x_29 = x_91;
goto block_90;
}
else
{
uint8_t x_92; 
x_92 = l_List_elem___main___at_Lean_Meta_induction___spec__2(x_19, x_7);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = 0;
x_29 = x_93;
goto block_90;
}
else
{
uint8_t x_94; 
x_94 = l_Lean_Expr_isFVar(x_21);
x_29 = x_94;
goto block_90;
}
}
block_90:
{
uint8_t x_30; 
if (x_29 == 0)
{
uint8_t x_88; 
x_88 = 0;
x_30 = x_88;
goto block_87;
}
else
{
uint8_t x_89; 
x_89 = 1;
x_30 = x_89;
goto block_87;
}
block_87:
{
lean_object* x_31; 
if (x_26 == 0)
{
if (x_28 == 0)
{
x_31 = x_13;
goto block_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_6);
x_61 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_61, 0, x_9);
x_62 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_63 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__6;
x_65 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_4);
x_67 = l_Lean_indentExpr(x_66);
x_68 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_68, x_12, x_13);
lean_dec(x_12);
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
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_6);
x_74 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_74, 0, x_9);
x_75 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_76 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__9;
x_78 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_79, 0, x_4);
x_80 = l_Lean_indentExpr(x_79);
x_81 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_81, x_12, x_13);
lean_dec(x_12);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
return x_82;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_82);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
block_60:
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
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
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
x_51 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_50, x_12, x_36);
lean_dec(x_12);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_34);
if (x_56 == 0)
{
return x_34;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_34, 0);
x_58 = lean_ctor_get(x_34, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_34);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
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
lean_object* x_109; lean_object* x_110; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_13);
return x_110;
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
uint8_t x_107; 
x_107 = lean_expr_eqv(x_21, x_9);
x_25 = x_107;
goto block_106;
}
else
{
uint8_t x_108; 
x_108 = 0;
x_25 = x_108;
goto block_106;
}
block_106:
{
uint8_t x_26; 
if (x_25 == 0)
{
uint8_t x_104; 
x_104 = 0;
x_26 = x_104;
goto block_103;
}
else
{
uint8_t x_105; 
x_105 = 1;
x_26 = x_105;
goto block_103;
}
block_103:
{
uint8_t x_27; 
if (x_23 == 0)
{
uint8_t x_99; 
x_99 = 0;
x_27 = x_99;
goto block_98;
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = l_Lean_Expr_fvarId_x21(x_9);
lean_inc(x_21);
lean_inc(x_6);
x_101 = l_Lean_MetavarContext_exprDependsOn(x_6, x_21, x_100);
lean_dec(x_100);
x_102 = lean_unbox(x_101);
lean_dec(x_101);
x_27 = x_102;
goto block_98;
}
block_98:
{
uint8_t x_28; 
if (x_27 == 0)
{
uint8_t x_96; 
x_96 = 0;
x_28 = x_96;
goto block_95;
}
else
{
uint8_t x_97; 
x_97 = 1;
x_28 = x_97;
goto block_95;
}
block_95:
{
uint8_t x_29; 
if (x_24 == 0)
{
uint8_t x_91; 
x_91 = 0;
x_29 = x_91;
goto block_90;
}
else
{
uint8_t x_92; 
x_92 = l_List_elem___main___at_Lean_Meta_induction___spec__2(x_19, x_7);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = 0;
x_29 = x_93;
goto block_90;
}
else
{
uint8_t x_94; 
x_94 = l_Lean_Expr_isFVar(x_21);
x_29 = x_94;
goto block_90;
}
}
block_90:
{
uint8_t x_30; 
if (x_29 == 0)
{
uint8_t x_88; 
x_88 = 0;
x_30 = x_88;
goto block_87;
}
else
{
uint8_t x_89; 
x_89 = 1;
x_30 = x_89;
goto block_87;
}
block_87:
{
lean_object* x_31; 
if (x_26 == 0)
{
if (x_28 == 0)
{
x_31 = x_13;
goto block_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_6);
x_61 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_61, 0, x_9);
x_62 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_63 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__6;
x_65 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_4);
x_67 = l_Lean_indentExpr(x_66);
x_68 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_68, x_12, x_13);
lean_dec(x_12);
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
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_6);
x_74 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_74, 0, x_9);
x_75 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_76 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__9;
x_78 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_79, 0, x_4);
x_80 = l_Lean_indentExpr(x_79);
x_81 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_81, x_12, x_13);
lean_dec(x_12);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
return x_82;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_82);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
block_60:
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
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
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
x_51 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_50, x_12, x_36);
lean_dec(x_12);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_34);
if (x_56 == 0)
{
return x_34;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_34, 0);
x_58 = lean_ctor_get(x_34, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_34);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
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
lean_object* x_109; lean_object* x_110; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_13);
return x_110;
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
uint8_t x_62; 
x_62 = 0;
x_25 = x_62;
goto block_61;
}
else
{
uint8_t x_63; 
x_63 = 1;
x_25 = x_63;
goto block_61;
}
block_61:
{
lean_object* x_26; 
if (x_21 == 0)
{
x_26 = x_11;
goto block_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_6);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_4);
x_53 = l_Lean_indentExpr(x_52);
x_54 = l_List_forM___main___at_Lean_Meta_induction___spec__1___closed__3;
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_55, x_10, x_11);
lean_dec(x_10);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
block_51:
{
if (x_25 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
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
x_35 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_34, x_10, x_26);
lean_dec(x_10);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_inc(x_10);
lean_inc(x_20);
lean_inc(x_23);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_40 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_19, x_23, x_20, x_20, x_10, x_26);
lean_dec(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_8, x_42);
x_44 = x_23;
x_45 = lean_array_fset(x_18, x_8, x_44);
lean_dec(x_8);
x_8 = x_43;
x_9 = x_45;
x_11 = x_41;
goto _start;
}
else
{
uint8_t x_47; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
return x_40;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_40, 0);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_40);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
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
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_5);
lean_dec(x_3);
x_36 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_37 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_36, x_7, x_8);
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
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_6, 1);
x_43 = lean_ctor_get(x_5, 0);
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_5);
x_45 = lean_ctor_get(x_10, 0);
x_46 = lean_array_get_size(x_4);
x_47 = lean_nat_dec_le(x_46, x_45);
lean_dec(x_46);
x_48 = l_Lean_Level_Inhabited;
x_49 = lean_array_get(x_48, x_4, x_45);
x_50 = lean_array_push(x_43, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
if (x_47 == 0)
{
x_5 = x_51;
x_6 = x_42;
goto _start;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_51);
lean_dec(x_3);
x_53 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_54 = l_Lean_Meta_throwTacticEx___rarg(x_1, x_2, x_53, x_7, x_8);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_84; 
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
x_84 = lean_unbox(x_29);
lean_dec(x_29);
if (x_84 == 0)
{
uint8_t x_85; 
x_85 = l_Lean_Level_isZero(x_13);
lean_dec(x_13);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = 1;
x_32 = x_86;
goto block_83;
}
else
{
uint8_t x_87; 
x_87 = 0;
x_32 = x_87;
goto block_83;
}
}
else
{
uint8_t x_88; 
lean_dec(x_13);
x_88 = 0;
x_32 = x_88;
goto block_83;
}
block_83:
{
uint8_t x_33; 
if (x_32 == 0)
{
uint8_t x_81; 
x_81 = 0;
x_33 = x_81;
goto block_80;
}
else
{
uint8_t x_82; 
x_82 = 1;
x_33 = x_82;
goto block_80;
}
block_80:
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
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
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
x_75 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_74, x_17, x_27);
lean_dec(x_17);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
return x_75;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
else
{
uint8_t x_89; 
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
x_89 = !lean_is_exclusive(x_25);
if (x_89 == 0)
{
return x_25;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_25, 0);
x_91 = lean_ctor_get(x_25, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_25);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
case 5:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_14, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_14, 1);
lean_inc(x_94);
lean_dec(x_14);
x_95 = lean_array_set(x_15, x_16, x_94);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_sub(x_16, x_96);
lean_dec(x_16);
x_14 = x_93;
x_15 = x_95;
x_16 = x_97;
goto _start;
}
default: 
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_99 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__3;
x_100 = l_Lean_Meta_throwTacticEx___rarg(x_3, x_8, x_99, x_17, x_18);
lean_dec(x_17);
return x_100;
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
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
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
x_124 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_123, x_13, x_32);
lean_dec(x_13);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
return x_124;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_124, 0);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_124);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
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
x_48 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_47, x_44, x_45, x_46, x_13, x_42);
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
uint8_t x_129; 
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
x_129 = !lean_is_exclusive(x_30);
if (x_129 == 0)
{
return x_30;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_30, 0);
x_131 = lean_ctor_get(x_30, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_30);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
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
x_133 = !lean_is_exclusive(x_27);
if (x_133 == 0)
{
return x_27;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_27, 0);
x_135 = lean_ctor_get(x_27, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_27);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
uint8_t x_137; 
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
x_137 = !lean_is_exclusive(x_16);
if (x_137 == 0)
{
return x_16;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_16, 0);
x_139 = lean_ctor_get(x_16, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_16);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
case 1:
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_12);
lean_dec(x_10);
x_141 = lean_ctor_get(x_7, 5);
lean_inc(x_141);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_142 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_141, x_13, x_14);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_7, 6);
lean_inc(x_145);
x_146 = l_List_redLength___main___rarg(x_145);
x_147 = lean_mk_empty_array_with_capacity(x_146);
lean_dec(x_146);
lean_inc(x_145);
x_148 = l_List_toArrayAux___main___rarg(x_145, x_147);
x_149 = x_148;
x_150 = lean_unsigned_to_nat(0u);
lean_inc(x_144);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_151 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_151, 0, x_1);
lean_closure_set(x_151, 1, x_6);
lean_closure_set(x_151, 2, x_7);
lean_closure_set(x_151, 3, x_9);
lean_closure_set(x_151, 4, x_11);
lean_closure_set(x_151, 5, x_144);
lean_closure_set(x_151, 6, x_145);
lean_closure_set(x_151, 7, x_150);
lean_closure_set(x_151, 8, x_149);
x_152 = x_151;
lean_inc(x_13);
x_153 = lean_apply_2(x_152, x_13, x_143);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_inc(x_1);
x_156 = l_Lean_Meta_getMVarType(x_1, x_13, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_154);
x_160 = x_154;
x_161 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_150, x_160);
x_162 = x_161;
lean_inc(x_2);
x_163 = lean_array_push(x_162, x_2);
if (x_159 == 0)
{
lean_object* x_243; uint8_t x_244; 
x_243 = l_Lean_MetavarContext_exprDependsOn(x_144, x_157, x_2);
lean_dec(x_2);
x_244 = lean_unbox(x_243);
lean_dec(x_243);
if (x_244 == 0)
{
x_164 = x_158;
goto block_242;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
lean_dec(x_163);
lean_dec(x_154);
lean_dec(x_141);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_245 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_245, 0, x_3);
x_246 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_247 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_245);
x_248 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_249 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
x_250 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_249, x_13, x_158);
lean_dec(x_13);
x_251 = !lean_is_exclusive(x_250);
if (x_251 == 0)
{
return x_250;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_250, 0);
x_253 = lean_ctor_get(x_250, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_250);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
else
{
lean_dec(x_157);
lean_dec(x_144);
lean_dec(x_2);
x_164 = x_158;
goto block_242;
}
block_242:
{
uint8_t x_165; lean_object* x_166; 
x_165 = 1;
x_166 = l_Lean_Meta_revert(x_1, x_163, x_165, x_13, x_164);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
lean_dec(x_167);
x_171 = lean_array_get_size(x_154);
x_172 = lean_box(0);
x_173 = 0;
x_174 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_173, x_170, x_171, x_172, x_13, x_168);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_dec(x_175);
x_179 = l_Lean_Meta_intro1(x_178, x_173, x_13, x_176);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_223; uint8_t x_224; 
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
x_184 = lean_box(0);
x_185 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_154, x_177, x_154, x_150, x_184);
lean_dec(x_154);
x_186 = x_177;
x_187 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_150, x_186);
x_188 = x_187;
lean_inc(x_182);
x_189 = l_Lean_mkFVar(x_182);
lean_inc(x_183);
x_190 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_190, 0, x_183);
x_191 = lean_box(x_159);
lean_inc(x_183);
x_192 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_192, 0, x_182);
lean_closure_set(x_192, 1, x_8);
lean_closure_set(x_192, 2, x_183);
lean_closure_set(x_192, 3, x_3);
lean_closure_set(x_192, 4, x_4);
lean_closure_set(x_192, 5, x_6);
lean_closure_set(x_192, 6, x_7);
lean_closure_set(x_192, 7, x_141);
lean_closure_set(x_192, 8, x_191);
lean_closure_set(x_192, 9, x_169);
lean_closure_set(x_192, 10, x_185);
lean_closure_set(x_192, 11, x_188);
lean_closure_set(x_192, 12, x_189);
x_193 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_193, 0, x_190);
lean_closure_set(x_193, 1, x_192);
x_223 = lean_ctor_get(x_181, 4);
lean_inc(x_223);
x_224 = lean_ctor_get_uint8(x_223, sizeof(void*)*1);
lean_dec(x_223);
if (x_224 == 0)
{
x_194 = x_173;
x_195 = x_181;
goto block_222;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_225 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_226 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_225, x_13, x_181);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_unbox(x_227);
lean_dec(x_227);
x_194 = x_229;
x_195 = x_228;
goto block_222;
}
block_222:
{
if (x_194 == 0)
{
lean_object* x_196; 
x_196 = l_Lean_Meta_getMVarDecl(x_183, x_13, x_195);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_197, 4);
lean_inc(x_200);
lean_dec(x_197);
x_201 = l_Lean_Meta_withLocalContext___rarg(x_199, x_200, x_193, x_13, x_198);
lean_dec(x_13);
return x_201;
}
else
{
uint8_t x_202; 
lean_dec(x_193);
lean_dec(x_13);
x_202 = !lean_is_exclusive(x_196);
if (x_202 == 0)
{
return x_196;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_196, 0);
x_204 = lean_ctor_get(x_196, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_196);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_inc(x_183);
x_206 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_206, 0, x_183);
x_207 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_208 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
x_209 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_210 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_209, x_208, x_13, x_195);
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = l_Lean_Meta_getMVarDecl(x_183, x_13, x_211);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
x_216 = lean_ctor_get(x_213, 4);
lean_inc(x_216);
lean_dec(x_213);
x_217 = l_Lean_Meta_withLocalContext___rarg(x_215, x_216, x_193, x_13, x_214);
lean_dec(x_13);
return x_217;
}
else
{
uint8_t x_218; 
lean_dec(x_193);
lean_dec(x_13);
x_218 = !lean_is_exclusive(x_212);
if (x_218 == 0)
{
return x_212;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_212, 0);
x_220 = lean_ctor_get(x_212, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_212);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
}
}
else
{
uint8_t x_230; 
lean_dec(x_177);
lean_dec(x_169);
lean_dec(x_154);
lean_dec(x_141);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_230 = !lean_is_exclusive(x_179);
if (x_230 == 0)
{
return x_179;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_179, 0);
x_232 = lean_ctor_get(x_179, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_179);
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
lean_dec(x_169);
lean_dec(x_154);
lean_dec(x_141);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_234 = !lean_is_exclusive(x_174);
if (x_234 == 0)
{
return x_174;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_174, 0);
x_236 = lean_ctor_get(x_174, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_174);
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
lean_dec(x_154);
lean_dec(x_141);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_238 = !lean_is_exclusive(x_166);
if (x_238 == 0)
{
return x_166;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_166, 0);
x_240 = lean_ctor_get(x_166, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_166);
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
uint8_t x_255; 
lean_dec(x_154);
lean_dec(x_144);
lean_dec(x_141);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_255 = !lean_is_exclusive(x_156);
if (x_255 == 0)
{
return x_156;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_156, 0);
x_257 = lean_ctor_get(x_156, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_156);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
else
{
uint8_t x_259; 
lean_dec(x_144);
lean_dec(x_141);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_259 = !lean_is_exclusive(x_153);
if (x_259 == 0)
{
return x_153;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_153, 0);
x_261 = lean_ctor_get(x_153, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_153);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
else
{
uint8_t x_263; 
lean_dec(x_141);
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
x_263 = !lean_is_exclusive(x_142);
if (x_263 == 0)
{
return x_142;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_142, 0);
x_265 = lean_ctor_get(x_142, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_142);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
case 2:
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_12);
lean_dec(x_10);
x_267 = lean_ctor_get(x_7, 5);
lean_inc(x_267);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_268 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_267, x_13, x_14);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec(x_268);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_7, 6);
lean_inc(x_271);
x_272 = l_List_redLength___main___rarg(x_271);
x_273 = lean_mk_empty_array_with_capacity(x_272);
lean_dec(x_272);
lean_inc(x_271);
x_274 = l_List_toArrayAux___main___rarg(x_271, x_273);
x_275 = x_274;
x_276 = lean_unsigned_to_nat(0u);
lean_inc(x_270);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_277 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_277, 0, x_1);
lean_closure_set(x_277, 1, x_6);
lean_closure_set(x_277, 2, x_7);
lean_closure_set(x_277, 3, x_9);
lean_closure_set(x_277, 4, x_11);
lean_closure_set(x_277, 5, x_270);
lean_closure_set(x_277, 6, x_271);
lean_closure_set(x_277, 7, x_276);
lean_closure_set(x_277, 8, x_275);
x_278 = x_277;
lean_inc(x_13);
x_279 = lean_apply_2(x_278, x_13, x_269);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
lean_inc(x_1);
x_282 = l_Lean_Meta_getMVarType(x_1, x_13, x_281);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_280);
x_286 = x_280;
x_287 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_276, x_286);
x_288 = x_287;
lean_inc(x_2);
x_289 = lean_array_push(x_288, x_2);
if (x_285 == 0)
{
lean_object* x_369; uint8_t x_370; 
x_369 = l_Lean_MetavarContext_exprDependsOn(x_270, x_283, x_2);
lean_dec(x_2);
x_370 = lean_unbox(x_369);
lean_dec(x_369);
if (x_370 == 0)
{
x_290 = x_284;
goto block_368;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; 
lean_dec(x_289);
lean_dec(x_280);
lean_dec(x_267);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_371 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_371, 0, x_3);
x_372 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_373 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_371);
x_374 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_375 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_374);
x_376 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_375, x_13, x_284);
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
lean_dec(x_283);
lean_dec(x_270);
lean_dec(x_2);
x_290 = x_284;
goto block_368;
}
block_368:
{
uint8_t x_291; lean_object* x_292; 
x_291 = 1;
x_292 = l_Lean_Meta_revert(x_1, x_289, x_291, x_13, x_290);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; lean_object* x_300; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_295 = lean_ctor_get(x_293, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_293, 1);
lean_inc(x_296);
lean_dec(x_293);
x_297 = lean_array_get_size(x_280);
x_298 = lean_box(0);
x_299 = 0;
x_300 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_299, x_296, x_297, x_298, x_13, x_294);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_ctor_get(x_301, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_301, 1);
lean_inc(x_304);
lean_dec(x_301);
x_305 = l_Lean_Meta_intro1(x_304, x_299, x_13, x_302);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_349; uint8_t x_350; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
x_308 = lean_ctor_get(x_306, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_306, 1);
lean_inc(x_309);
lean_dec(x_306);
x_310 = lean_box(0);
x_311 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_280, x_303, x_280, x_276, x_310);
lean_dec(x_280);
x_312 = x_303;
x_313 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_276, x_312);
x_314 = x_313;
lean_inc(x_308);
x_315 = l_Lean_mkFVar(x_308);
lean_inc(x_309);
x_316 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_316, 0, x_309);
x_317 = lean_box(x_285);
lean_inc(x_309);
x_318 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_318, 0, x_308);
lean_closure_set(x_318, 1, x_8);
lean_closure_set(x_318, 2, x_309);
lean_closure_set(x_318, 3, x_3);
lean_closure_set(x_318, 4, x_4);
lean_closure_set(x_318, 5, x_6);
lean_closure_set(x_318, 6, x_7);
lean_closure_set(x_318, 7, x_267);
lean_closure_set(x_318, 8, x_317);
lean_closure_set(x_318, 9, x_295);
lean_closure_set(x_318, 10, x_311);
lean_closure_set(x_318, 11, x_314);
lean_closure_set(x_318, 12, x_315);
x_319 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_319, 0, x_316);
lean_closure_set(x_319, 1, x_318);
x_349 = lean_ctor_get(x_307, 4);
lean_inc(x_349);
x_350 = lean_ctor_get_uint8(x_349, sizeof(void*)*1);
lean_dec(x_349);
if (x_350 == 0)
{
x_320 = x_299;
x_321 = x_307;
goto block_348;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; 
x_351 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_352 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_351, x_13, x_307);
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_355 = lean_unbox(x_353);
lean_dec(x_353);
x_320 = x_355;
x_321 = x_354;
goto block_348;
}
block_348:
{
if (x_320 == 0)
{
lean_object* x_322; 
x_322 = l_Lean_Meta_getMVarDecl(x_309, x_13, x_321);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
x_326 = lean_ctor_get(x_323, 4);
lean_inc(x_326);
lean_dec(x_323);
x_327 = l_Lean_Meta_withLocalContext___rarg(x_325, x_326, x_319, x_13, x_324);
lean_dec(x_13);
return x_327;
}
else
{
uint8_t x_328; 
lean_dec(x_319);
lean_dec(x_13);
x_328 = !lean_is_exclusive(x_322);
if (x_328 == 0)
{
return x_322;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_322, 0);
x_330 = lean_ctor_get(x_322, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_322);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
return x_331;
}
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_inc(x_309);
x_332 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_332, 0, x_309);
x_333 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_334 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_332);
x_335 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_336 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_335, x_334, x_13, x_321);
x_337 = lean_ctor_get(x_336, 1);
lean_inc(x_337);
lean_dec(x_336);
x_338 = l_Lean_Meta_getMVarDecl(x_309, x_13, x_337);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
x_342 = lean_ctor_get(x_339, 4);
lean_inc(x_342);
lean_dec(x_339);
x_343 = l_Lean_Meta_withLocalContext___rarg(x_341, x_342, x_319, x_13, x_340);
lean_dec(x_13);
return x_343;
}
else
{
uint8_t x_344; 
lean_dec(x_319);
lean_dec(x_13);
x_344 = !lean_is_exclusive(x_338);
if (x_344 == 0)
{
return x_338;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_338, 0);
x_346 = lean_ctor_get(x_338, 1);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_338);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
return x_347;
}
}
}
}
}
else
{
uint8_t x_356; 
lean_dec(x_303);
lean_dec(x_295);
lean_dec(x_280);
lean_dec(x_267);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_356 = !lean_is_exclusive(x_305);
if (x_356 == 0)
{
return x_305;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = lean_ctor_get(x_305, 0);
x_358 = lean_ctor_get(x_305, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_305);
x_359 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
return x_359;
}
}
}
else
{
uint8_t x_360; 
lean_dec(x_295);
lean_dec(x_280);
lean_dec(x_267);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_360 = !lean_is_exclusive(x_300);
if (x_360 == 0)
{
return x_300;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_300, 0);
x_362 = lean_ctor_get(x_300, 1);
lean_inc(x_362);
lean_inc(x_361);
lean_dec(x_300);
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_362);
return x_363;
}
}
}
else
{
uint8_t x_364; 
lean_dec(x_280);
lean_dec(x_267);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_364 = !lean_is_exclusive(x_292);
if (x_364 == 0)
{
return x_292;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_292, 0);
x_366 = lean_ctor_get(x_292, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_292);
x_367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
return x_367;
}
}
}
}
else
{
uint8_t x_381; 
lean_dec(x_280);
lean_dec(x_270);
lean_dec(x_267);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_381 = !lean_is_exclusive(x_282);
if (x_381 == 0)
{
return x_282;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_282, 0);
x_383 = lean_ctor_get(x_282, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_282);
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
lean_dec(x_270);
lean_dec(x_267);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_385 = !lean_is_exclusive(x_279);
if (x_385 == 0)
{
return x_279;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_279, 0);
x_387 = lean_ctor_get(x_279, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_279);
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
lean_dec(x_267);
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
x_389 = !lean_is_exclusive(x_268);
if (x_389 == 0)
{
return x_268;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_268, 0);
x_391 = lean_ctor_get(x_268, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_268);
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
x_394 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_393, x_13, x_14);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_395 = lean_ctor_get(x_394, 1);
lean_inc(x_395);
lean_dec(x_394);
x_396 = lean_ctor_get(x_395, 1);
lean_inc(x_396);
x_397 = lean_ctor_get(x_7, 6);
lean_inc(x_397);
x_398 = l_List_redLength___main___rarg(x_397);
x_399 = lean_mk_empty_array_with_capacity(x_398);
lean_dec(x_398);
lean_inc(x_397);
x_400 = l_List_toArrayAux___main___rarg(x_397, x_399);
x_401 = x_400;
x_402 = lean_unsigned_to_nat(0u);
lean_inc(x_396);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_403 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_403, 0, x_1);
lean_closure_set(x_403, 1, x_6);
lean_closure_set(x_403, 2, x_7);
lean_closure_set(x_403, 3, x_9);
lean_closure_set(x_403, 4, x_11);
lean_closure_set(x_403, 5, x_396);
lean_closure_set(x_403, 6, x_397);
lean_closure_set(x_403, 7, x_402);
lean_closure_set(x_403, 8, x_401);
x_404 = x_403;
lean_inc(x_13);
x_405 = lean_apply_2(x_404, x_13, x_395);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
lean_inc(x_1);
x_408 = l_Lean_Meta_getMVarType(x_1, x_13, x_407);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; uint8_t x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_411 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_406);
x_412 = x_406;
x_413 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_402, x_412);
x_414 = x_413;
lean_inc(x_2);
x_415 = lean_array_push(x_414, x_2);
if (x_411 == 0)
{
lean_object* x_495; uint8_t x_496; 
x_495 = l_Lean_MetavarContext_exprDependsOn(x_396, x_409, x_2);
lean_dec(x_2);
x_496 = lean_unbox(x_495);
lean_dec(x_495);
if (x_496 == 0)
{
x_416 = x_410;
goto block_494;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; 
lean_dec(x_415);
lean_dec(x_406);
lean_dec(x_393);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_497 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_497, 0, x_3);
x_498 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_499 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_497);
x_500 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_501 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_500);
x_502 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_501, x_13, x_410);
lean_dec(x_13);
x_503 = !lean_is_exclusive(x_502);
if (x_503 == 0)
{
return x_502;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_504 = lean_ctor_get(x_502, 0);
x_505 = lean_ctor_get(x_502, 1);
lean_inc(x_505);
lean_inc(x_504);
lean_dec(x_502);
x_506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_505);
return x_506;
}
}
}
else
{
lean_dec(x_409);
lean_dec(x_396);
lean_dec(x_2);
x_416 = x_410;
goto block_494;
}
block_494:
{
uint8_t x_417; lean_object* x_418; 
x_417 = 1;
x_418 = l_Lean_Meta_revert(x_1, x_415, x_417, x_13, x_416);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_418, 1);
lean_inc(x_420);
lean_dec(x_418);
x_421 = lean_ctor_get(x_419, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_419, 1);
lean_inc(x_422);
lean_dec(x_419);
x_423 = lean_array_get_size(x_406);
x_424 = lean_box(0);
x_425 = 0;
x_426 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_425, x_422, x_423, x_424, x_13, x_420);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
x_429 = lean_ctor_get(x_427, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_427, 1);
lean_inc(x_430);
lean_dec(x_427);
x_431 = l_Lean_Meta_intro1(x_430, x_425, x_13, x_428);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; lean_object* x_475; uint8_t x_476; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
x_434 = lean_ctor_get(x_432, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_432, 1);
lean_inc(x_435);
lean_dec(x_432);
x_436 = lean_box(0);
x_437 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_406, x_429, x_406, x_402, x_436);
lean_dec(x_406);
x_438 = x_429;
x_439 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_402, x_438);
x_440 = x_439;
lean_inc(x_434);
x_441 = l_Lean_mkFVar(x_434);
lean_inc(x_435);
x_442 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_442, 0, x_435);
x_443 = lean_box(x_411);
lean_inc(x_435);
x_444 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_444, 0, x_434);
lean_closure_set(x_444, 1, x_8);
lean_closure_set(x_444, 2, x_435);
lean_closure_set(x_444, 3, x_3);
lean_closure_set(x_444, 4, x_4);
lean_closure_set(x_444, 5, x_6);
lean_closure_set(x_444, 6, x_7);
lean_closure_set(x_444, 7, x_393);
lean_closure_set(x_444, 8, x_443);
lean_closure_set(x_444, 9, x_421);
lean_closure_set(x_444, 10, x_437);
lean_closure_set(x_444, 11, x_440);
lean_closure_set(x_444, 12, x_441);
x_445 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_445, 0, x_442);
lean_closure_set(x_445, 1, x_444);
x_475 = lean_ctor_get(x_433, 4);
lean_inc(x_475);
x_476 = lean_ctor_get_uint8(x_475, sizeof(void*)*1);
lean_dec(x_475);
if (x_476 == 0)
{
x_446 = x_425;
x_447 = x_433;
goto block_474;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; uint8_t x_481; 
x_477 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_478 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_477, x_13, x_433);
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
lean_dec(x_478);
x_481 = lean_unbox(x_479);
lean_dec(x_479);
x_446 = x_481;
x_447 = x_480;
goto block_474;
}
block_474:
{
if (x_446 == 0)
{
lean_object* x_448; 
x_448 = l_Lean_Meta_getMVarDecl(x_435, x_13, x_447);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
x_451 = lean_ctor_get(x_449, 1);
lean_inc(x_451);
x_452 = lean_ctor_get(x_449, 4);
lean_inc(x_452);
lean_dec(x_449);
x_453 = l_Lean_Meta_withLocalContext___rarg(x_451, x_452, x_445, x_13, x_450);
lean_dec(x_13);
return x_453;
}
else
{
uint8_t x_454; 
lean_dec(x_445);
lean_dec(x_13);
x_454 = !lean_is_exclusive(x_448);
if (x_454 == 0)
{
return x_448;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = lean_ctor_get(x_448, 0);
x_456 = lean_ctor_get(x_448, 1);
lean_inc(x_456);
lean_inc(x_455);
lean_dec(x_448);
x_457 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_456);
return x_457;
}
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_inc(x_435);
x_458 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_458, 0, x_435);
x_459 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_460 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_460, 0, x_459);
lean_ctor_set(x_460, 1, x_458);
x_461 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_462 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_461, x_460, x_13, x_447);
x_463 = lean_ctor_get(x_462, 1);
lean_inc(x_463);
lean_dec(x_462);
x_464 = l_Lean_Meta_getMVarDecl(x_435, x_13, x_463);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_464, 1);
lean_inc(x_466);
lean_dec(x_464);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_465, 4);
lean_inc(x_468);
lean_dec(x_465);
x_469 = l_Lean_Meta_withLocalContext___rarg(x_467, x_468, x_445, x_13, x_466);
lean_dec(x_13);
return x_469;
}
else
{
uint8_t x_470; 
lean_dec(x_445);
lean_dec(x_13);
x_470 = !lean_is_exclusive(x_464);
if (x_470 == 0)
{
return x_464;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_464, 0);
x_472 = lean_ctor_get(x_464, 1);
lean_inc(x_472);
lean_inc(x_471);
lean_dec(x_464);
x_473 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set(x_473, 1, x_472);
return x_473;
}
}
}
}
}
else
{
uint8_t x_482; 
lean_dec(x_429);
lean_dec(x_421);
lean_dec(x_406);
lean_dec(x_393);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_482 = !lean_is_exclusive(x_431);
if (x_482 == 0)
{
return x_431;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_483 = lean_ctor_get(x_431, 0);
x_484 = lean_ctor_get(x_431, 1);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_431);
x_485 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_484);
return x_485;
}
}
}
else
{
uint8_t x_486; 
lean_dec(x_421);
lean_dec(x_406);
lean_dec(x_393);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_486 = !lean_is_exclusive(x_426);
if (x_486 == 0)
{
return x_426;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_487 = lean_ctor_get(x_426, 0);
x_488 = lean_ctor_get(x_426, 1);
lean_inc(x_488);
lean_inc(x_487);
lean_dec(x_426);
x_489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_488);
return x_489;
}
}
}
else
{
uint8_t x_490; 
lean_dec(x_406);
lean_dec(x_393);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_490 = !lean_is_exclusive(x_418);
if (x_490 == 0)
{
return x_418;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_418, 0);
x_492 = lean_ctor_get(x_418, 1);
lean_inc(x_492);
lean_inc(x_491);
lean_dec(x_418);
x_493 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_492);
return x_493;
}
}
}
}
else
{
uint8_t x_507; 
lean_dec(x_406);
lean_dec(x_396);
lean_dec(x_393);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_507 = !lean_is_exclusive(x_408);
if (x_507 == 0)
{
return x_408;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_508 = lean_ctor_get(x_408, 0);
x_509 = lean_ctor_get(x_408, 1);
lean_inc(x_509);
lean_inc(x_508);
lean_dec(x_408);
x_510 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_510, 0, x_508);
lean_ctor_set(x_510, 1, x_509);
return x_510;
}
}
}
else
{
uint8_t x_511; 
lean_dec(x_396);
lean_dec(x_393);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_511 = !lean_is_exclusive(x_405);
if (x_511 == 0)
{
return x_405;
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_512 = lean_ctor_get(x_405, 0);
x_513 = lean_ctor_get(x_405, 1);
lean_inc(x_513);
lean_inc(x_512);
lean_dec(x_405);
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
lean_dec(x_393);
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
x_515 = !lean_is_exclusive(x_394);
if (x_515 == 0)
{
return x_394;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_516 = lean_ctor_get(x_394, 0);
x_517 = lean_ctor_get(x_394, 1);
lean_inc(x_517);
lean_inc(x_516);
lean_dec(x_394);
x_518 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set(x_518, 1, x_517);
return x_518;
}
}
}
case 4:
{
lean_object* x_519; lean_object* x_520; 
lean_dec(x_12);
lean_dec(x_10);
x_519 = lean_ctor_get(x_7, 5);
lean_inc(x_519);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_520 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_519, x_13, x_14);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_521 = lean_ctor_get(x_520, 1);
lean_inc(x_521);
lean_dec(x_520);
x_522 = lean_ctor_get(x_521, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_7, 6);
lean_inc(x_523);
x_524 = l_List_redLength___main___rarg(x_523);
x_525 = lean_mk_empty_array_with_capacity(x_524);
lean_dec(x_524);
lean_inc(x_523);
x_526 = l_List_toArrayAux___main___rarg(x_523, x_525);
x_527 = x_526;
x_528 = lean_unsigned_to_nat(0u);
lean_inc(x_522);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_529 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_529, 0, x_1);
lean_closure_set(x_529, 1, x_6);
lean_closure_set(x_529, 2, x_7);
lean_closure_set(x_529, 3, x_9);
lean_closure_set(x_529, 4, x_11);
lean_closure_set(x_529, 5, x_522);
lean_closure_set(x_529, 6, x_523);
lean_closure_set(x_529, 7, x_528);
lean_closure_set(x_529, 8, x_527);
x_530 = x_529;
lean_inc(x_13);
x_531 = lean_apply_2(x_530, x_13, x_521);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
lean_dec(x_531);
lean_inc(x_1);
x_534 = l_Lean_Meta_getMVarType(x_1, x_13, x_533);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; lean_object* x_536; uint8_t x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
lean_dec(x_534);
x_537 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_532);
x_538 = x_532;
x_539 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_528, x_538);
x_540 = x_539;
lean_inc(x_2);
x_541 = lean_array_push(x_540, x_2);
if (x_537 == 0)
{
lean_object* x_621; uint8_t x_622; 
x_621 = l_Lean_MetavarContext_exprDependsOn(x_522, x_535, x_2);
lean_dec(x_2);
x_622 = lean_unbox(x_621);
lean_dec(x_621);
if (x_622 == 0)
{
x_542 = x_536;
goto block_620;
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; uint8_t x_629; 
lean_dec(x_541);
lean_dec(x_532);
lean_dec(x_519);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_623 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_623, 0, x_3);
x_624 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_625 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_625, 0, x_624);
lean_ctor_set(x_625, 1, x_623);
x_626 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_627 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_627, 0, x_625);
lean_ctor_set(x_627, 1, x_626);
x_628 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_627, x_13, x_536);
lean_dec(x_13);
x_629 = !lean_is_exclusive(x_628);
if (x_629 == 0)
{
return x_628;
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_630 = lean_ctor_get(x_628, 0);
x_631 = lean_ctor_get(x_628, 1);
lean_inc(x_631);
lean_inc(x_630);
lean_dec(x_628);
x_632 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_632, 0, x_630);
lean_ctor_set(x_632, 1, x_631);
return x_632;
}
}
}
else
{
lean_dec(x_535);
lean_dec(x_522);
lean_dec(x_2);
x_542 = x_536;
goto block_620;
}
block_620:
{
uint8_t x_543; lean_object* x_544; 
x_543 = 1;
x_544 = l_Lean_Meta_revert(x_1, x_541, x_543, x_13, x_542);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; uint8_t x_551; lean_object* x_552; 
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_544, 1);
lean_inc(x_546);
lean_dec(x_544);
x_547 = lean_ctor_get(x_545, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_545, 1);
lean_inc(x_548);
lean_dec(x_545);
x_549 = lean_array_get_size(x_532);
x_550 = lean_box(0);
x_551 = 0;
x_552 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_551, x_548, x_549, x_550, x_13, x_546);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_552, 1);
lean_inc(x_554);
lean_dec(x_552);
x_555 = lean_ctor_get(x_553, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_553, 1);
lean_inc(x_556);
lean_dec(x_553);
x_557 = l_Lean_Meta_intro1(x_556, x_551, x_13, x_554);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; lean_object* x_573; lean_object* x_601; uint8_t x_602; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
lean_dec(x_557);
x_560 = lean_ctor_get(x_558, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_558, 1);
lean_inc(x_561);
lean_dec(x_558);
x_562 = lean_box(0);
x_563 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_532, x_555, x_532, x_528, x_562);
lean_dec(x_532);
x_564 = x_555;
x_565 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_528, x_564);
x_566 = x_565;
lean_inc(x_560);
x_567 = l_Lean_mkFVar(x_560);
lean_inc(x_561);
x_568 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_568, 0, x_561);
x_569 = lean_box(x_537);
lean_inc(x_561);
x_570 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_570, 0, x_560);
lean_closure_set(x_570, 1, x_8);
lean_closure_set(x_570, 2, x_561);
lean_closure_set(x_570, 3, x_3);
lean_closure_set(x_570, 4, x_4);
lean_closure_set(x_570, 5, x_6);
lean_closure_set(x_570, 6, x_7);
lean_closure_set(x_570, 7, x_519);
lean_closure_set(x_570, 8, x_569);
lean_closure_set(x_570, 9, x_547);
lean_closure_set(x_570, 10, x_563);
lean_closure_set(x_570, 11, x_566);
lean_closure_set(x_570, 12, x_567);
x_571 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_571, 0, x_568);
lean_closure_set(x_571, 1, x_570);
x_601 = lean_ctor_get(x_559, 4);
lean_inc(x_601);
x_602 = lean_ctor_get_uint8(x_601, sizeof(void*)*1);
lean_dec(x_601);
if (x_602 == 0)
{
x_572 = x_551;
x_573 = x_559;
goto block_600;
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; uint8_t x_607; 
x_603 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_604 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_603, x_13, x_559);
x_605 = lean_ctor_get(x_604, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_604, 1);
lean_inc(x_606);
lean_dec(x_604);
x_607 = lean_unbox(x_605);
lean_dec(x_605);
x_572 = x_607;
x_573 = x_606;
goto block_600;
}
block_600:
{
if (x_572 == 0)
{
lean_object* x_574; 
x_574 = l_Lean_Meta_getMVarDecl(x_561, x_13, x_573);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_574, 1);
lean_inc(x_576);
lean_dec(x_574);
x_577 = lean_ctor_get(x_575, 1);
lean_inc(x_577);
x_578 = lean_ctor_get(x_575, 4);
lean_inc(x_578);
lean_dec(x_575);
x_579 = l_Lean_Meta_withLocalContext___rarg(x_577, x_578, x_571, x_13, x_576);
lean_dec(x_13);
return x_579;
}
else
{
uint8_t x_580; 
lean_dec(x_571);
lean_dec(x_13);
x_580 = !lean_is_exclusive(x_574);
if (x_580 == 0)
{
return x_574;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_581 = lean_ctor_get(x_574, 0);
x_582 = lean_ctor_get(x_574, 1);
lean_inc(x_582);
lean_inc(x_581);
lean_dec(x_574);
x_583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_583, 0, x_581);
lean_ctor_set(x_583, 1, x_582);
return x_583;
}
}
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
lean_inc(x_561);
x_584 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_584, 0, x_561);
x_585 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_586 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_584);
x_587 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_588 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_587, x_586, x_13, x_573);
x_589 = lean_ctor_get(x_588, 1);
lean_inc(x_589);
lean_dec(x_588);
x_590 = l_Lean_Meta_getMVarDecl(x_561, x_13, x_589);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_590, 1);
lean_inc(x_592);
lean_dec(x_590);
x_593 = lean_ctor_get(x_591, 1);
lean_inc(x_593);
x_594 = lean_ctor_get(x_591, 4);
lean_inc(x_594);
lean_dec(x_591);
x_595 = l_Lean_Meta_withLocalContext___rarg(x_593, x_594, x_571, x_13, x_592);
lean_dec(x_13);
return x_595;
}
else
{
uint8_t x_596; 
lean_dec(x_571);
lean_dec(x_13);
x_596 = !lean_is_exclusive(x_590);
if (x_596 == 0)
{
return x_590;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_590, 0);
x_598 = lean_ctor_get(x_590, 1);
lean_inc(x_598);
lean_inc(x_597);
lean_dec(x_590);
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_597);
lean_ctor_set(x_599, 1, x_598);
return x_599;
}
}
}
}
}
else
{
uint8_t x_608; 
lean_dec(x_555);
lean_dec(x_547);
lean_dec(x_532);
lean_dec(x_519);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_608 = !lean_is_exclusive(x_557);
if (x_608 == 0)
{
return x_557;
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_609 = lean_ctor_get(x_557, 0);
x_610 = lean_ctor_get(x_557, 1);
lean_inc(x_610);
lean_inc(x_609);
lean_dec(x_557);
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
lean_dec(x_547);
lean_dec(x_532);
lean_dec(x_519);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_612 = !lean_is_exclusive(x_552);
if (x_612 == 0)
{
return x_552;
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = lean_ctor_get(x_552, 0);
x_614 = lean_ctor_get(x_552, 1);
lean_inc(x_614);
lean_inc(x_613);
lean_dec(x_552);
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
lean_dec(x_532);
lean_dec(x_519);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_616 = !lean_is_exclusive(x_544);
if (x_616 == 0)
{
return x_544;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_617 = lean_ctor_get(x_544, 0);
x_618 = lean_ctor_get(x_544, 1);
lean_inc(x_618);
lean_inc(x_617);
lean_dec(x_544);
x_619 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_619, 0, x_617);
lean_ctor_set(x_619, 1, x_618);
return x_619;
}
}
}
}
else
{
uint8_t x_633; 
lean_dec(x_532);
lean_dec(x_522);
lean_dec(x_519);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_633 = !lean_is_exclusive(x_534);
if (x_633 == 0)
{
return x_534;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_634 = lean_ctor_get(x_534, 0);
x_635 = lean_ctor_get(x_534, 1);
lean_inc(x_635);
lean_inc(x_634);
lean_dec(x_534);
x_636 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_636, 0, x_634);
lean_ctor_set(x_636, 1, x_635);
return x_636;
}
}
}
else
{
uint8_t x_637; 
lean_dec(x_522);
lean_dec(x_519);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_637 = !lean_is_exclusive(x_531);
if (x_637 == 0)
{
return x_531;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_638 = lean_ctor_get(x_531, 0);
x_639 = lean_ctor_get(x_531, 1);
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_531);
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_638);
lean_ctor_set(x_640, 1, x_639);
return x_640;
}
}
}
else
{
uint8_t x_641; 
lean_dec(x_519);
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
x_641 = !lean_is_exclusive(x_520);
if (x_641 == 0)
{
return x_520;
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_642 = lean_ctor_get(x_520, 0);
x_643 = lean_ctor_get(x_520, 1);
lean_inc(x_643);
lean_inc(x_642);
lean_dec(x_520);
x_644 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_644, 0, x_642);
lean_ctor_set(x_644, 1, x_643);
return x_644;
}
}
}
case 5:
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_645 = lean_ctor_get(x_10, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_10, 1);
lean_inc(x_646);
lean_dec(x_10);
x_647 = lean_array_set(x_11, x_12, x_646);
x_648 = lean_unsigned_to_nat(1u);
x_649 = lean_nat_sub(x_12, x_648);
lean_dec(x_12);
x_10 = x_645;
x_11 = x_647;
x_12 = x_649;
goto _start;
}
case 6:
{
lean_object* x_651; lean_object* x_652; 
lean_dec(x_12);
lean_dec(x_10);
x_651 = lean_ctor_get(x_7, 5);
lean_inc(x_651);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_652 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_651, x_13, x_14);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_653 = lean_ctor_get(x_652, 1);
lean_inc(x_653);
lean_dec(x_652);
x_654 = lean_ctor_get(x_653, 1);
lean_inc(x_654);
x_655 = lean_ctor_get(x_7, 6);
lean_inc(x_655);
x_656 = l_List_redLength___main___rarg(x_655);
x_657 = lean_mk_empty_array_with_capacity(x_656);
lean_dec(x_656);
lean_inc(x_655);
x_658 = l_List_toArrayAux___main___rarg(x_655, x_657);
x_659 = x_658;
x_660 = lean_unsigned_to_nat(0u);
lean_inc(x_654);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_661 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_661, 0, x_1);
lean_closure_set(x_661, 1, x_6);
lean_closure_set(x_661, 2, x_7);
lean_closure_set(x_661, 3, x_9);
lean_closure_set(x_661, 4, x_11);
lean_closure_set(x_661, 5, x_654);
lean_closure_set(x_661, 6, x_655);
lean_closure_set(x_661, 7, x_660);
lean_closure_set(x_661, 8, x_659);
x_662 = x_661;
lean_inc(x_13);
x_663 = lean_apply_2(x_662, x_13, x_653);
if (lean_obj_tag(x_663) == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_663, 1);
lean_inc(x_665);
lean_dec(x_663);
lean_inc(x_1);
x_666 = l_Lean_Meta_getMVarType(x_1, x_13, x_665);
if (lean_obj_tag(x_666) == 0)
{
lean_object* x_667; lean_object* x_668; uint8_t x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_667 = lean_ctor_get(x_666, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_666, 1);
lean_inc(x_668);
lean_dec(x_666);
x_669 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_664);
x_670 = x_664;
x_671 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_660, x_670);
x_672 = x_671;
lean_inc(x_2);
x_673 = lean_array_push(x_672, x_2);
if (x_669 == 0)
{
lean_object* x_753; uint8_t x_754; 
x_753 = l_Lean_MetavarContext_exprDependsOn(x_654, x_667, x_2);
lean_dec(x_2);
x_754 = lean_unbox(x_753);
lean_dec(x_753);
if (x_754 == 0)
{
x_674 = x_668;
goto block_752;
}
else
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; uint8_t x_761; 
lean_dec(x_673);
lean_dec(x_664);
lean_dec(x_651);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_755 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_755, 0, x_3);
x_756 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_757 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_757, 0, x_756);
lean_ctor_set(x_757, 1, x_755);
x_758 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_759 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_759, 0, x_757);
lean_ctor_set(x_759, 1, x_758);
x_760 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_759, x_13, x_668);
lean_dec(x_13);
x_761 = !lean_is_exclusive(x_760);
if (x_761 == 0)
{
return x_760;
}
else
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; 
x_762 = lean_ctor_get(x_760, 0);
x_763 = lean_ctor_get(x_760, 1);
lean_inc(x_763);
lean_inc(x_762);
lean_dec(x_760);
x_764 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_764, 0, x_762);
lean_ctor_set(x_764, 1, x_763);
return x_764;
}
}
}
else
{
lean_dec(x_667);
lean_dec(x_654);
lean_dec(x_2);
x_674 = x_668;
goto block_752;
}
block_752:
{
uint8_t x_675; lean_object* x_676; 
x_675 = 1;
x_676 = l_Lean_Meta_revert(x_1, x_673, x_675, x_13, x_674);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; uint8_t x_683; lean_object* x_684; 
x_677 = lean_ctor_get(x_676, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_676, 1);
lean_inc(x_678);
lean_dec(x_676);
x_679 = lean_ctor_get(x_677, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_677, 1);
lean_inc(x_680);
lean_dec(x_677);
x_681 = lean_array_get_size(x_664);
x_682 = lean_box(0);
x_683 = 0;
x_684 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_683, x_680, x_681, x_682, x_13, x_678);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_685 = lean_ctor_get(x_684, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_684, 1);
lean_inc(x_686);
lean_dec(x_684);
x_687 = lean_ctor_get(x_685, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_685, 1);
lean_inc(x_688);
lean_dec(x_685);
x_689 = l_Lean_Meta_intro1(x_688, x_683, x_13, x_686);
if (lean_obj_tag(x_689) == 0)
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; uint8_t x_704; lean_object* x_705; lean_object* x_733; uint8_t x_734; 
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
x_694 = lean_box(0);
x_695 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_664, x_687, x_664, x_660, x_694);
lean_dec(x_664);
x_696 = x_687;
x_697 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_660, x_696);
x_698 = x_697;
lean_inc(x_692);
x_699 = l_Lean_mkFVar(x_692);
lean_inc(x_693);
x_700 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_700, 0, x_693);
x_701 = lean_box(x_669);
lean_inc(x_693);
x_702 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_702, 0, x_692);
lean_closure_set(x_702, 1, x_8);
lean_closure_set(x_702, 2, x_693);
lean_closure_set(x_702, 3, x_3);
lean_closure_set(x_702, 4, x_4);
lean_closure_set(x_702, 5, x_6);
lean_closure_set(x_702, 6, x_7);
lean_closure_set(x_702, 7, x_651);
lean_closure_set(x_702, 8, x_701);
lean_closure_set(x_702, 9, x_679);
lean_closure_set(x_702, 10, x_695);
lean_closure_set(x_702, 11, x_698);
lean_closure_set(x_702, 12, x_699);
x_703 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_703, 0, x_700);
lean_closure_set(x_703, 1, x_702);
x_733 = lean_ctor_get(x_691, 4);
lean_inc(x_733);
x_734 = lean_ctor_get_uint8(x_733, sizeof(void*)*1);
lean_dec(x_733);
if (x_734 == 0)
{
x_704 = x_683;
x_705 = x_691;
goto block_732;
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; uint8_t x_739; 
x_735 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_736 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_735, x_13, x_691);
x_737 = lean_ctor_get(x_736, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_736, 1);
lean_inc(x_738);
lean_dec(x_736);
x_739 = lean_unbox(x_737);
lean_dec(x_737);
x_704 = x_739;
x_705 = x_738;
goto block_732;
}
block_732:
{
if (x_704 == 0)
{
lean_object* x_706; 
x_706 = l_Lean_Meta_getMVarDecl(x_693, x_13, x_705);
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
x_711 = l_Lean_Meta_withLocalContext___rarg(x_709, x_710, x_703, x_13, x_708);
lean_dec(x_13);
return x_711;
}
else
{
uint8_t x_712; 
lean_dec(x_703);
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
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; 
lean_inc(x_693);
x_716 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_716, 0, x_693);
x_717 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_718 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_718, 0, x_717);
lean_ctor_set(x_718, 1, x_716);
x_719 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_720 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_719, x_718, x_13, x_705);
x_721 = lean_ctor_get(x_720, 1);
lean_inc(x_721);
lean_dec(x_720);
x_722 = l_Lean_Meta_getMVarDecl(x_693, x_13, x_721);
if (lean_obj_tag(x_722) == 0)
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_723 = lean_ctor_get(x_722, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_722, 1);
lean_inc(x_724);
lean_dec(x_722);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
x_726 = lean_ctor_get(x_723, 4);
lean_inc(x_726);
lean_dec(x_723);
x_727 = l_Lean_Meta_withLocalContext___rarg(x_725, x_726, x_703, x_13, x_724);
lean_dec(x_13);
return x_727;
}
else
{
uint8_t x_728; 
lean_dec(x_703);
lean_dec(x_13);
x_728 = !lean_is_exclusive(x_722);
if (x_728 == 0)
{
return x_722;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_729 = lean_ctor_get(x_722, 0);
x_730 = lean_ctor_get(x_722, 1);
lean_inc(x_730);
lean_inc(x_729);
lean_dec(x_722);
x_731 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_731, 0, x_729);
lean_ctor_set(x_731, 1, x_730);
return x_731;
}
}
}
}
}
else
{
uint8_t x_740; 
lean_dec(x_687);
lean_dec(x_679);
lean_dec(x_664);
lean_dec(x_651);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_740 = !lean_is_exclusive(x_689);
if (x_740 == 0)
{
return x_689;
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_741 = lean_ctor_get(x_689, 0);
x_742 = lean_ctor_get(x_689, 1);
lean_inc(x_742);
lean_inc(x_741);
lean_dec(x_689);
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
lean_dec(x_679);
lean_dec(x_664);
lean_dec(x_651);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_744 = !lean_is_exclusive(x_684);
if (x_744 == 0)
{
return x_684;
}
else
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_745 = lean_ctor_get(x_684, 0);
x_746 = lean_ctor_get(x_684, 1);
lean_inc(x_746);
lean_inc(x_745);
lean_dec(x_684);
x_747 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_747, 0, x_745);
lean_ctor_set(x_747, 1, x_746);
return x_747;
}
}
}
else
{
uint8_t x_748; 
lean_dec(x_664);
lean_dec(x_651);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_748 = !lean_is_exclusive(x_676);
if (x_748 == 0)
{
return x_676;
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; 
x_749 = lean_ctor_get(x_676, 0);
x_750 = lean_ctor_get(x_676, 1);
lean_inc(x_750);
lean_inc(x_749);
lean_dec(x_676);
x_751 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_751, 0, x_749);
lean_ctor_set(x_751, 1, x_750);
return x_751;
}
}
}
}
else
{
uint8_t x_765; 
lean_dec(x_664);
lean_dec(x_654);
lean_dec(x_651);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_765 = !lean_is_exclusive(x_666);
if (x_765 == 0)
{
return x_666;
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; 
x_766 = lean_ctor_get(x_666, 0);
x_767 = lean_ctor_get(x_666, 1);
lean_inc(x_767);
lean_inc(x_766);
lean_dec(x_666);
x_768 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_768, 0, x_766);
lean_ctor_set(x_768, 1, x_767);
return x_768;
}
}
}
else
{
uint8_t x_769; 
lean_dec(x_654);
lean_dec(x_651);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_769 = !lean_is_exclusive(x_663);
if (x_769 == 0)
{
return x_663;
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; 
x_770 = lean_ctor_get(x_663, 0);
x_771 = lean_ctor_get(x_663, 1);
lean_inc(x_771);
lean_inc(x_770);
lean_dec(x_663);
x_772 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_772, 0, x_770);
lean_ctor_set(x_772, 1, x_771);
return x_772;
}
}
}
else
{
uint8_t x_773; 
lean_dec(x_651);
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
x_773 = !lean_is_exclusive(x_652);
if (x_773 == 0)
{
return x_652;
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_774 = lean_ctor_get(x_652, 0);
x_775 = lean_ctor_get(x_652, 1);
lean_inc(x_775);
lean_inc(x_774);
lean_dec(x_652);
x_776 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_776, 0, x_774);
lean_ctor_set(x_776, 1, x_775);
return x_776;
}
}
}
case 7:
{
lean_object* x_777; lean_object* x_778; 
lean_dec(x_12);
lean_dec(x_10);
x_777 = lean_ctor_get(x_7, 5);
lean_inc(x_777);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_778 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_777, x_13, x_14);
if (lean_obj_tag(x_778) == 0)
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_779 = lean_ctor_get(x_778, 1);
lean_inc(x_779);
lean_dec(x_778);
x_780 = lean_ctor_get(x_779, 1);
lean_inc(x_780);
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_787 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_787, 0, x_1);
lean_closure_set(x_787, 1, x_6);
lean_closure_set(x_787, 2, x_7);
lean_closure_set(x_787, 3, x_9);
lean_closure_set(x_787, 4, x_11);
lean_closure_set(x_787, 5, x_780);
lean_closure_set(x_787, 6, x_781);
lean_closure_set(x_787, 7, x_786);
lean_closure_set(x_787, 8, x_785);
x_788 = x_787;
lean_inc(x_13);
x_789 = lean_apply_2(x_788, x_13, x_779);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
lean_dec(x_789);
lean_inc(x_1);
x_792 = l_Lean_Meta_getMVarType(x_1, x_13, x_791);
if (lean_obj_tag(x_792) == 0)
{
lean_object* x_793; lean_object* x_794; uint8_t x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; 
x_793 = lean_ctor_get(x_792, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_792, 1);
lean_inc(x_794);
lean_dec(x_792);
x_795 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_790);
x_796 = x_790;
x_797 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_786, x_796);
x_798 = x_797;
lean_inc(x_2);
x_799 = lean_array_push(x_798, x_2);
if (x_795 == 0)
{
lean_object* x_879; uint8_t x_880; 
x_879 = l_Lean_MetavarContext_exprDependsOn(x_780, x_793, x_2);
lean_dec(x_2);
x_880 = lean_unbox(x_879);
lean_dec(x_879);
if (x_880 == 0)
{
x_800 = x_794;
goto block_878;
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; uint8_t x_887; 
lean_dec(x_799);
lean_dec(x_790);
lean_dec(x_777);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_881 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_881, 0, x_3);
x_882 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_883 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_883, 0, x_882);
lean_ctor_set(x_883, 1, x_881);
x_884 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_885 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_885, 0, x_883);
lean_ctor_set(x_885, 1, x_884);
x_886 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_885, x_13, x_794);
lean_dec(x_13);
x_887 = !lean_is_exclusive(x_886);
if (x_887 == 0)
{
return x_886;
}
else
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; 
x_888 = lean_ctor_get(x_886, 0);
x_889 = lean_ctor_get(x_886, 1);
lean_inc(x_889);
lean_inc(x_888);
lean_dec(x_886);
x_890 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_890, 0, x_888);
lean_ctor_set(x_890, 1, x_889);
return x_890;
}
}
}
else
{
lean_dec(x_793);
lean_dec(x_780);
lean_dec(x_2);
x_800 = x_794;
goto block_878;
}
block_878:
{
uint8_t x_801; lean_object* x_802; 
x_801 = 1;
x_802 = l_Lean_Meta_revert(x_1, x_799, x_801, x_13, x_800);
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
x_810 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_809, x_806, x_807, x_808, x_13, x_804);
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
x_815 = l_Lean_Meta_intro1(x_814, x_809, x_13, x_812);
if (lean_obj_tag(x_815) == 0)
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; uint8_t x_830; lean_object* x_831; lean_object* x_859; uint8_t x_860; 
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
x_821 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_790, x_813, x_790, x_786, x_820);
lean_dec(x_790);
x_822 = x_813;
x_823 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_786, x_822);
x_824 = x_823;
lean_inc(x_818);
x_825 = l_Lean_mkFVar(x_818);
lean_inc(x_819);
x_826 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_826, 0, x_819);
x_827 = lean_box(x_795);
lean_inc(x_819);
x_828 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_828, 0, x_818);
lean_closure_set(x_828, 1, x_8);
lean_closure_set(x_828, 2, x_819);
lean_closure_set(x_828, 3, x_3);
lean_closure_set(x_828, 4, x_4);
lean_closure_set(x_828, 5, x_6);
lean_closure_set(x_828, 6, x_7);
lean_closure_set(x_828, 7, x_777);
lean_closure_set(x_828, 8, x_827);
lean_closure_set(x_828, 9, x_805);
lean_closure_set(x_828, 10, x_821);
lean_closure_set(x_828, 11, x_824);
lean_closure_set(x_828, 12, x_825);
x_829 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_829, 0, x_826);
lean_closure_set(x_829, 1, x_828);
x_859 = lean_ctor_get(x_817, 4);
lean_inc(x_859);
x_860 = lean_ctor_get_uint8(x_859, sizeof(void*)*1);
lean_dec(x_859);
if (x_860 == 0)
{
x_830 = x_809;
x_831 = x_817;
goto block_858;
}
else
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; uint8_t x_865; 
x_861 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_862 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_861, x_13, x_817);
x_863 = lean_ctor_get(x_862, 0);
lean_inc(x_863);
x_864 = lean_ctor_get(x_862, 1);
lean_inc(x_864);
lean_dec(x_862);
x_865 = lean_unbox(x_863);
lean_dec(x_863);
x_830 = x_865;
x_831 = x_864;
goto block_858;
}
block_858:
{
if (x_830 == 0)
{
lean_object* x_832; 
x_832 = l_Lean_Meta_getMVarDecl(x_819, x_13, x_831);
if (lean_obj_tag(x_832) == 0)
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_832, 1);
lean_inc(x_834);
lean_dec(x_832);
x_835 = lean_ctor_get(x_833, 1);
lean_inc(x_835);
x_836 = lean_ctor_get(x_833, 4);
lean_inc(x_836);
lean_dec(x_833);
x_837 = l_Lean_Meta_withLocalContext___rarg(x_835, x_836, x_829, x_13, x_834);
lean_dec(x_13);
return x_837;
}
else
{
uint8_t x_838; 
lean_dec(x_829);
lean_dec(x_13);
x_838 = !lean_is_exclusive(x_832);
if (x_838 == 0)
{
return x_832;
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; 
x_839 = lean_ctor_get(x_832, 0);
x_840 = lean_ctor_get(x_832, 1);
lean_inc(x_840);
lean_inc(x_839);
lean_dec(x_832);
x_841 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_841, 0, x_839);
lean_ctor_set(x_841, 1, x_840);
return x_841;
}
}
}
else
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; 
lean_inc(x_819);
x_842 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_842, 0, x_819);
x_843 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_844 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_844, 0, x_843);
lean_ctor_set(x_844, 1, x_842);
x_845 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_846 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_845, x_844, x_13, x_831);
x_847 = lean_ctor_get(x_846, 1);
lean_inc(x_847);
lean_dec(x_846);
x_848 = l_Lean_Meta_getMVarDecl(x_819, x_13, x_847);
if (lean_obj_tag(x_848) == 0)
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; 
x_849 = lean_ctor_get(x_848, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_848, 1);
lean_inc(x_850);
lean_dec(x_848);
x_851 = lean_ctor_get(x_849, 1);
lean_inc(x_851);
x_852 = lean_ctor_get(x_849, 4);
lean_inc(x_852);
lean_dec(x_849);
x_853 = l_Lean_Meta_withLocalContext___rarg(x_851, x_852, x_829, x_13, x_850);
lean_dec(x_13);
return x_853;
}
else
{
uint8_t x_854; 
lean_dec(x_829);
lean_dec(x_13);
x_854 = !lean_is_exclusive(x_848);
if (x_854 == 0)
{
return x_848;
}
else
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; 
x_855 = lean_ctor_get(x_848, 0);
x_856 = lean_ctor_get(x_848, 1);
lean_inc(x_856);
lean_inc(x_855);
lean_dec(x_848);
x_857 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_857, 0, x_855);
lean_ctor_set(x_857, 1, x_856);
return x_857;
}
}
}
}
}
else
{
uint8_t x_866; 
lean_dec(x_813);
lean_dec(x_805);
lean_dec(x_790);
lean_dec(x_777);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_866 = !lean_is_exclusive(x_815);
if (x_866 == 0)
{
return x_815;
}
else
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; 
x_867 = lean_ctor_get(x_815, 0);
x_868 = lean_ctor_get(x_815, 1);
lean_inc(x_868);
lean_inc(x_867);
lean_dec(x_815);
x_869 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_869, 0, x_867);
lean_ctor_set(x_869, 1, x_868);
return x_869;
}
}
}
else
{
uint8_t x_870; 
lean_dec(x_805);
lean_dec(x_790);
lean_dec(x_777);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_870 = !lean_is_exclusive(x_810);
if (x_870 == 0)
{
return x_810;
}
else
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; 
x_871 = lean_ctor_get(x_810, 0);
x_872 = lean_ctor_get(x_810, 1);
lean_inc(x_872);
lean_inc(x_871);
lean_dec(x_810);
x_873 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_873, 0, x_871);
lean_ctor_set(x_873, 1, x_872);
return x_873;
}
}
}
else
{
uint8_t x_874; 
lean_dec(x_790);
lean_dec(x_777);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_874 = !lean_is_exclusive(x_802);
if (x_874 == 0)
{
return x_802;
}
else
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; 
x_875 = lean_ctor_get(x_802, 0);
x_876 = lean_ctor_get(x_802, 1);
lean_inc(x_876);
lean_inc(x_875);
lean_dec(x_802);
x_877 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_877, 0, x_875);
lean_ctor_set(x_877, 1, x_876);
return x_877;
}
}
}
}
else
{
uint8_t x_891; 
lean_dec(x_790);
lean_dec(x_780);
lean_dec(x_777);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_891 = !lean_is_exclusive(x_792);
if (x_891 == 0)
{
return x_792;
}
else
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_892 = lean_ctor_get(x_792, 0);
x_893 = lean_ctor_get(x_792, 1);
lean_inc(x_893);
lean_inc(x_892);
lean_dec(x_792);
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
lean_dec(x_780);
lean_dec(x_777);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_895 = !lean_is_exclusive(x_789);
if (x_895 == 0)
{
return x_789;
}
else
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; 
x_896 = lean_ctor_get(x_789, 0);
x_897 = lean_ctor_get(x_789, 1);
lean_inc(x_897);
lean_inc(x_896);
lean_dec(x_789);
x_898 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_898, 0, x_896);
lean_ctor_set(x_898, 1, x_897);
return x_898;
}
}
}
else
{
uint8_t x_899; 
lean_dec(x_777);
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
x_899 = !lean_is_exclusive(x_778);
if (x_899 == 0)
{
return x_778;
}
else
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; 
x_900 = lean_ctor_get(x_778, 0);
x_901 = lean_ctor_get(x_778, 1);
lean_inc(x_901);
lean_inc(x_900);
lean_dec(x_778);
x_902 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_902, 0, x_900);
lean_ctor_set(x_902, 1, x_901);
return x_902;
}
}
}
case 8:
{
lean_object* x_903; lean_object* x_904; 
lean_dec(x_12);
lean_dec(x_10);
x_903 = lean_ctor_get(x_7, 5);
lean_inc(x_903);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_904 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_903, x_13, x_14);
if (lean_obj_tag(x_904) == 0)
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; 
x_905 = lean_ctor_get(x_904, 1);
lean_inc(x_905);
lean_dec(x_904);
x_906 = lean_ctor_get(x_905, 1);
lean_inc(x_906);
x_907 = lean_ctor_get(x_7, 6);
lean_inc(x_907);
x_908 = l_List_redLength___main___rarg(x_907);
x_909 = lean_mk_empty_array_with_capacity(x_908);
lean_dec(x_908);
lean_inc(x_907);
x_910 = l_List_toArrayAux___main___rarg(x_907, x_909);
x_911 = x_910;
x_912 = lean_unsigned_to_nat(0u);
lean_inc(x_906);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_913 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_913, 0, x_1);
lean_closure_set(x_913, 1, x_6);
lean_closure_set(x_913, 2, x_7);
lean_closure_set(x_913, 3, x_9);
lean_closure_set(x_913, 4, x_11);
lean_closure_set(x_913, 5, x_906);
lean_closure_set(x_913, 6, x_907);
lean_closure_set(x_913, 7, x_912);
lean_closure_set(x_913, 8, x_911);
x_914 = x_913;
lean_inc(x_13);
x_915 = lean_apply_2(x_914, x_13, x_905);
if (lean_obj_tag(x_915) == 0)
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_916 = lean_ctor_get(x_915, 0);
lean_inc(x_916);
x_917 = lean_ctor_get(x_915, 1);
lean_inc(x_917);
lean_dec(x_915);
lean_inc(x_1);
x_918 = l_Lean_Meta_getMVarType(x_1, x_13, x_917);
if (lean_obj_tag(x_918) == 0)
{
lean_object* x_919; lean_object* x_920; uint8_t x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; 
x_919 = lean_ctor_get(x_918, 0);
lean_inc(x_919);
x_920 = lean_ctor_get(x_918, 1);
lean_inc(x_920);
lean_dec(x_918);
x_921 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_916);
x_922 = x_916;
x_923 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_912, x_922);
x_924 = x_923;
lean_inc(x_2);
x_925 = lean_array_push(x_924, x_2);
if (x_921 == 0)
{
lean_object* x_1005; uint8_t x_1006; 
x_1005 = l_Lean_MetavarContext_exprDependsOn(x_906, x_919, x_2);
lean_dec(x_2);
x_1006 = lean_unbox(x_1005);
lean_dec(x_1005);
if (x_1006 == 0)
{
x_926 = x_920;
goto block_1004;
}
else
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; uint8_t x_1013; 
lean_dec(x_925);
lean_dec(x_916);
lean_dec(x_903);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_1007 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1007, 0, x_3);
x_1008 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_1009 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1009, 0, x_1008);
lean_ctor_set(x_1009, 1, x_1007);
x_1010 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_1011 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1011, 0, x_1009);
lean_ctor_set(x_1011, 1, x_1010);
x_1012 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1011, x_13, x_920);
lean_dec(x_13);
x_1013 = !lean_is_exclusive(x_1012);
if (x_1013 == 0)
{
return x_1012;
}
else
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
x_1014 = lean_ctor_get(x_1012, 0);
x_1015 = lean_ctor_get(x_1012, 1);
lean_inc(x_1015);
lean_inc(x_1014);
lean_dec(x_1012);
x_1016 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1016, 0, x_1014);
lean_ctor_set(x_1016, 1, x_1015);
return x_1016;
}
}
}
else
{
lean_dec(x_919);
lean_dec(x_906);
lean_dec(x_2);
x_926 = x_920;
goto block_1004;
}
block_1004:
{
uint8_t x_927; lean_object* x_928; 
x_927 = 1;
x_928 = l_Lean_Meta_revert(x_1, x_925, x_927, x_13, x_926);
if (lean_obj_tag(x_928) == 0)
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; uint8_t x_935; lean_object* x_936; 
x_929 = lean_ctor_get(x_928, 0);
lean_inc(x_929);
x_930 = lean_ctor_get(x_928, 1);
lean_inc(x_930);
lean_dec(x_928);
x_931 = lean_ctor_get(x_929, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_929, 1);
lean_inc(x_932);
lean_dec(x_929);
x_933 = lean_array_get_size(x_916);
x_934 = lean_box(0);
x_935 = 0;
x_936 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_935, x_932, x_933, x_934, x_13, x_930);
if (lean_obj_tag(x_936) == 0)
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; 
x_937 = lean_ctor_get(x_936, 0);
lean_inc(x_937);
x_938 = lean_ctor_get(x_936, 1);
lean_inc(x_938);
lean_dec(x_936);
x_939 = lean_ctor_get(x_937, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_937, 1);
lean_inc(x_940);
lean_dec(x_937);
x_941 = l_Lean_Meta_intro1(x_940, x_935, x_13, x_938);
if (lean_obj_tag(x_941) == 0)
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; uint8_t x_956; lean_object* x_957; lean_object* x_985; uint8_t x_986; 
x_942 = lean_ctor_get(x_941, 0);
lean_inc(x_942);
x_943 = lean_ctor_get(x_941, 1);
lean_inc(x_943);
lean_dec(x_941);
x_944 = lean_ctor_get(x_942, 0);
lean_inc(x_944);
x_945 = lean_ctor_get(x_942, 1);
lean_inc(x_945);
lean_dec(x_942);
x_946 = lean_box(0);
x_947 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_916, x_939, x_916, x_912, x_946);
lean_dec(x_916);
x_948 = x_939;
x_949 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_912, x_948);
x_950 = x_949;
lean_inc(x_944);
x_951 = l_Lean_mkFVar(x_944);
lean_inc(x_945);
x_952 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_952, 0, x_945);
x_953 = lean_box(x_921);
lean_inc(x_945);
x_954 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_954, 0, x_944);
lean_closure_set(x_954, 1, x_8);
lean_closure_set(x_954, 2, x_945);
lean_closure_set(x_954, 3, x_3);
lean_closure_set(x_954, 4, x_4);
lean_closure_set(x_954, 5, x_6);
lean_closure_set(x_954, 6, x_7);
lean_closure_set(x_954, 7, x_903);
lean_closure_set(x_954, 8, x_953);
lean_closure_set(x_954, 9, x_931);
lean_closure_set(x_954, 10, x_947);
lean_closure_set(x_954, 11, x_950);
lean_closure_set(x_954, 12, x_951);
x_955 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_955, 0, x_952);
lean_closure_set(x_955, 1, x_954);
x_985 = lean_ctor_get(x_943, 4);
lean_inc(x_985);
x_986 = lean_ctor_get_uint8(x_985, sizeof(void*)*1);
lean_dec(x_985);
if (x_986 == 0)
{
x_956 = x_935;
x_957 = x_943;
goto block_984;
}
else
{
lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; uint8_t x_991; 
x_987 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_988 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_987, x_13, x_943);
x_989 = lean_ctor_get(x_988, 0);
lean_inc(x_989);
x_990 = lean_ctor_get(x_988, 1);
lean_inc(x_990);
lean_dec(x_988);
x_991 = lean_unbox(x_989);
lean_dec(x_989);
x_956 = x_991;
x_957 = x_990;
goto block_984;
}
block_984:
{
if (x_956 == 0)
{
lean_object* x_958; 
x_958 = l_Lean_Meta_getMVarDecl(x_945, x_13, x_957);
if (lean_obj_tag(x_958) == 0)
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; 
x_959 = lean_ctor_get(x_958, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_958, 1);
lean_inc(x_960);
lean_dec(x_958);
x_961 = lean_ctor_get(x_959, 1);
lean_inc(x_961);
x_962 = lean_ctor_get(x_959, 4);
lean_inc(x_962);
lean_dec(x_959);
x_963 = l_Lean_Meta_withLocalContext___rarg(x_961, x_962, x_955, x_13, x_960);
lean_dec(x_13);
return x_963;
}
else
{
uint8_t x_964; 
lean_dec(x_955);
lean_dec(x_13);
x_964 = !lean_is_exclusive(x_958);
if (x_964 == 0)
{
return x_958;
}
else
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; 
x_965 = lean_ctor_get(x_958, 0);
x_966 = lean_ctor_get(x_958, 1);
lean_inc(x_966);
lean_inc(x_965);
lean_dec(x_958);
x_967 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_967, 0, x_965);
lean_ctor_set(x_967, 1, x_966);
return x_967;
}
}
}
else
{
lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
lean_inc(x_945);
x_968 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_968, 0, x_945);
x_969 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_970 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_970, 0, x_969);
lean_ctor_set(x_970, 1, x_968);
x_971 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_972 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_971, x_970, x_13, x_957);
x_973 = lean_ctor_get(x_972, 1);
lean_inc(x_973);
lean_dec(x_972);
x_974 = l_Lean_Meta_getMVarDecl(x_945, x_13, x_973);
if (lean_obj_tag(x_974) == 0)
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; 
x_975 = lean_ctor_get(x_974, 0);
lean_inc(x_975);
x_976 = lean_ctor_get(x_974, 1);
lean_inc(x_976);
lean_dec(x_974);
x_977 = lean_ctor_get(x_975, 1);
lean_inc(x_977);
x_978 = lean_ctor_get(x_975, 4);
lean_inc(x_978);
lean_dec(x_975);
x_979 = l_Lean_Meta_withLocalContext___rarg(x_977, x_978, x_955, x_13, x_976);
lean_dec(x_13);
return x_979;
}
else
{
uint8_t x_980; 
lean_dec(x_955);
lean_dec(x_13);
x_980 = !lean_is_exclusive(x_974);
if (x_980 == 0)
{
return x_974;
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; 
x_981 = lean_ctor_get(x_974, 0);
x_982 = lean_ctor_get(x_974, 1);
lean_inc(x_982);
lean_inc(x_981);
lean_dec(x_974);
x_983 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_983, 0, x_981);
lean_ctor_set(x_983, 1, x_982);
return x_983;
}
}
}
}
}
else
{
uint8_t x_992; 
lean_dec(x_939);
lean_dec(x_931);
lean_dec(x_916);
lean_dec(x_903);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_992 = !lean_is_exclusive(x_941);
if (x_992 == 0)
{
return x_941;
}
else
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; 
x_993 = lean_ctor_get(x_941, 0);
x_994 = lean_ctor_get(x_941, 1);
lean_inc(x_994);
lean_inc(x_993);
lean_dec(x_941);
x_995 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_995, 0, x_993);
lean_ctor_set(x_995, 1, x_994);
return x_995;
}
}
}
else
{
uint8_t x_996; 
lean_dec(x_931);
lean_dec(x_916);
lean_dec(x_903);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_996 = !lean_is_exclusive(x_936);
if (x_996 == 0)
{
return x_936;
}
else
{
lean_object* x_997; lean_object* x_998; lean_object* x_999; 
x_997 = lean_ctor_get(x_936, 0);
x_998 = lean_ctor_get(x_936, 1);
lean_inc(x_998);
lean_inc(x_997);
lean_dec(x_936);
x_999 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_999, 0, x_997);
lean_ctor_set(x_999, 1, x_998);
return x_999;
}
}
}
else
{
uint8_t x_1000; 
lean_dec(x_916);
lean_dec(x_903);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1000 = !lean_is_exclusive(x_928);
if (x_1000 == 0)
{
return x_928;
}
else
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; 
x_1001 = lean_ctor_get(x_928, 0);
x_1002 = lean_ctor_get(x_928, 1);
lean_inc(x_1002);
lean_inc(x_1001);
lean_dec(x_928);
x_1003 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1003, 0, x_1001);
lean_ctor_set(x_1003, 1, x_1002);
return x_1003;
}
}
}
}
else
{
uint8_t x_1017; 
lean_dec(x_916);
lean_dec(x_906);
lean_dec(x_903);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1017 = !lean_is_exclusive(x_918);
if (x_1017 == 0)
{
return x_918;
}
else
{
lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
x_1018 = lean_ctor_get(x_918, 0);
x_1019 = lean_ctor_get(x_918, 1);
lean_inc(x_1019);
lean_inc(x_1018);
lean_dec(x_918);
x_1020 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1020, 0, x_1018);
lean_ctor_set(x_1020, 1, x_1019);
return x_1020;
}
}
}
else
{
uint8_t x_1021; 
lean_dec(x_906);
lean_dec(x_903);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1021 = !lean_is_exclusive(x_915);
if (x_1021 == 0)
{
return x_915;
}
else
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; 
x_1022 = lean_ctor_get(x_915, 0);
x_1023 = lean_ctor_get(x_915, 1);
lean_inc(x_1023);
lean_inc(x_1022);
lean_dec(x_915);
x_1024 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1024, 0, x_1022);
lean_ctor_set(x_1024, 1, x_1023);
return x_1024;
}
}
}
else
{
uint8_t x_1025; 
lean_dec(x_903);
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
x_1025 = !lean_is_exclusive(x_904);
if (x_1025 == 0)
{
return x_904;
}
else
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; 
x_1026 = lean_ctor_get(x_904, 0);
x_1027 = lean_ctor_get(x_904, 1);
lean_inc(x_1027);
lean_inc(x_1026);
lean_dec(x_904);
x_1028 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1028, 0, x_1026);
lean_ctor_set(x_1028, 1, x_1027);
return x_1028;
}
}
}
case 9:
{
lean_object* x_1029; lean_object* x_1030; 
lean_dec(x_12);
lean_dec(x_10);
x_1029 = lean_ctor_get(x_7, 5);
lean_inc(x_1029);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1030 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_1029, x_13, x_14);
if (lean_obj_tag(x_1030) == 0)
{
lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1031 = lean_ctor_get(x_1030, 1);
lean_inc(x_1031);
lean_dec(x_1030);
x_1032 = lean_ctor_get(x_1031, 1);
lean_inc(x_1032);
x_1033 = lean_ctor_get(x_7, 6);
lean_inc(x_1033);
x_1034 = l_List_redLength___main___rarg(x_1033);
x_1035 = lean_mk_empty_array_with_capacity(x_1034);
lean_dec(x_1034);
lean_inc(x_1033);
x_1036 = l_List_toArrayAux___main___rarg(x_1033, x_1035);
x_1037 = x_1036;
x_1038 = lean_unsigned_to_nat(0u);
lean_inc(x_1032);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_1039 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_1039, 0, x_1);
lean_closure_set(x_1039, 1, x_6);
lean_closure_set(x_1039, 2, x_7);
lean_closure_set(x_1039, 3, x_9);
lean_closure_set(x_1039, 4, x_11);
lean_closure_set(x_1039, 5, x_1032);
lean_closure_set(x_1039, 6, x_1033);
lean_closure_set(x_1039, 7, x_1038);
lean_closure_set(x_1039, 8, x_1037);
x_1040 = x_1039;
lean_inc(x_13);
x_1041 = lean_apply_2(x_1040, x_13, x_1031);
if (lean_obj_tag(x_1041) == 0)
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
x_1042 = lean_ctor_get(x_1041, 0);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_1041, 1);
lean_inc(x_1043);
lean_dec(x_1041);
lean_inc(x_1);
x_1044 = l_Lean_Meta_getMVarType(x_1, x_13, x_1043);
if (lean_obj_tag(x_1044) == 0)
{
lean_object* x_1045; lean_object* x_1046; uint8_t x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
x_1045 = lean_ctor_get(x_1044, 0);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_1044, 1);
lean_inc(x_1046);
lean_dec(x_1044);
x_1047 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_1042);
x_1048 = x_1042;
x_1049 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1038, x_1048);
x_1050 = x_1049;
lean_inc(x_2);
x_1051 = lean_array_push(x_1050, x_2);
if (x_1047 == 0)
{
lean_object* x_1131; uint8_t x_1132; 
x_1131 = l_Lean_MetavarContext_exprDependsOn(x_1032, x_1045, x_2);
lean_dec(x_2);
x_1132 = lean_unbox(x_1131);
lean_dec(x_1131);
if (x_1132 == 0)
{
x_1052 = x_1046;
goto block_1130;
}
else
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; uint8_t x_1139; 
lean_dec(x_1051);
lean_dec(x_1042);
lean_dec(x_1029);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_1133 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1133, 0, x_3);
x_1134 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_1135 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1135, 0, x_1134);
lean_ctor_set(x_1135, 1, x_1133);
x_1136 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_1137 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1137, 0, x_1135);
lean_ctor_set(x_1137, 1, x_1136);
x_1138 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1137, x_13, x_1046);
lean_dec(x_13);
x_1139 = !lean_is_exclusive(x_1138);
if (x_1139 == 0)
{
return x_1138;
}
else
{
lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; 
x_1140 = lean_ctor_get(x_1138, 0);
x_1141 = lean_ctor_get(x_1138, 1);
lean_inc(x_1141);
lean_inc(x_1140);
lean_dec(x_1138);
x_1142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1142, 0, x_1140);
lean_ctor_set(x_1142, 1, x_1141);
return x_1142;
}
}
}
else
{
lean_dec(x_1045);
lean_dec(x_1032);
lean_dec(x_2);
x_1052 = x_1046;
goto block_1130;
}
block_1130:
{
uint8_t x_1053; lean_object* x_1054; 
x_1053 = 1;
x_1054 = l_Lean_Meta_revert(x_1, x_1051, x_1053, x_13, x_1052);
if (lean_obj_tag(x_1054) == 0)
{
lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; uint8_t x_1061; lean_object* x_1062; 
x_1055 = lean_ctor_get(x_1054, 0);
lean_inc(x_1055);
x_1056 = lean_ctor_get(x_1054, 1);
lean_inc(x_1056);
lean_dec(x_1054);
x_1057 = lean_ctor_get(x_1055, 0);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1055, 1);
lean_inc(x_1058);
lean_dec(x_1055);
x_1059 = lean_array_get_size(x_1042);
x_1060 = lean_box(0);
x_1061 = 0;
x_1062 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1061, x_1058, x_1059, x_1060, x_13, x_1056);
if (lean_obj_tag(x_1062) == 0)
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; 
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
x_1067 = l_Lean_Meta_intro1(x_1066, x_1061, x_13, x_1064);
if (lean_obj_tag(x_1067) == 0)
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; uint8_t x_1082; lean_object* x_1083; lean_object* x_1111; uint8_t x_1112; 
x_1068 = lean_ctor_get(x_1067, 0);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_1067, 1);
lean_inc(x_1069);
lean_dec(x_1067);
x_1070 = lean_ctor_get(x_1068, 0);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_1068, 1);
lean_inc(x_1071);
lean_dec(x_1068);
x_1072 = lean_box(0);
x_1073 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_1042, x_1065, x_1042, x_1038, x_1072);
lean_dec(x_1042);
x_1074 = x_1065;
x_1075 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1038, x_1074);
x_1076 = x_1075;
lean_inc(x_1070);
x_1077 = l_Lean_mkFVar(x_1070);
lean_inc(x_1071);
x_1078 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_1078, 0, x_1071);
x_1079 = lean_box(x_1047);
lean_inc(x_1071);
x_1080 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_1080, 0, x_1070);
lean_closure_set(x_1080, 1, x_8);
lean_closure_set(x_1080, 2, x_1071);
lean_closure_set(x_1080, 3, x_3);
lean_closure_set(x_1080, 4, x_4);
lean_closure_set(x_1080, 5, x_6);
lean_closure_set(x_1080, 6, x_7);
lean_closure_set(x_1080, 7, x_1029);
lean_closure_set(x_1080, 8, x_1079);
lean_closure_set(x_1080, 9, x_1057);
lean_closure_set(x_1080, 10, x_1073);
lean_closure_set(x_1080, 11, x_1076);
lean_closure_set(x_1080, 12, x_1077);
x_1081 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_1081, 0, x_1078);
lean_closure_set(x_1081, 1, x_1080);
x_1111 = lean_ctor_get(x_1069, 4);
lean_inc(x_1111);
x_1112 = lean_ctor_get_uint8(x_1111, sizeof(void*)*1);
lean_dec(x_1111);
if (x_1112 == 0)
{
x_1082 = x_1061;
x_1083 = x_1069;
goto block_1110;
}
else
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; uint8_t x_1117; 
x_1113 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_1114 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1113, x_13, x_1069);
x_1115 = lean_ctor_get(x_1114, 0);
lean_inc(x_1115);
x_1116 = lean_ctor_get(x_1114, 1);
lean_inc(x_1116);
lean_dec(x_1114);
x_1117 = lean_unbox(x_1115);
lean_dec(x_1115);
x_1082 = x_1117;
x_1083 = x_1116;
goto block_1110;
}
block_1110:
{
if (x_1082 == 0)
{
lean_object* x_1084; 
x_1084 = l_Lean_Meta_getMVarDecl(x_1071, x_13, x_1083);
if (lean_obj_tag(x_1084) == 0)
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; 
x_1085 = lean_ctor_get(x_1084, 0);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1084, 1);
lean_inc(x_1086);
lean_dec(x_1084);
x_1087 = lean_ctor_get(x_1085, 1);
lean_inc(x_1087);
x_1088 = lean_ctor_get(x_1085, 4);
lean_inc(x_1088);
lean_dec(x_1085);
x_1089 = l_Lean_Meta_withLocalContext___rarg(x_1087, x_1088, x_1081, x_13, x_1086);
lean_dec(x_13);
return x_1089;
}
else
{
uint8_t x_1090; 
lean_dec(x_1081);
lean_dec(x_13);
x_1090 = !lean_is_exclusive(x_1084);
if (x_1090 == 0)
{
return x_1084;
}
else
{
lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; 
x_1091 = lean_ctor_get(x_1084, 0);
x_1092 = lean_ctor_get(x_1084, 1);
lean_inc(x_1092);
lean_inc(x_1091);
lean_dec(x_1084);
x_1093 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1093, 0, x_1091);
lean_ctor_set(x_1093, 1, x_1092);
return x_1093;
}
}
}
else
{
lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
lean_inc(x_1071);
x_1094 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1094, 0, x_1071);
x_1095 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_1096 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1096, 0, x_1095);
lean_ctor_set(x_1096, 1, x_1094);
x_1097 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_1098 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1097, x_1096, x_13, x_1083);
x_1099 = lean_ctor_get(x_1098, 1);
lean_inc(x_1099);
lean_dec(x_1098);
x_1100 = l_Lean_Meta_getMVarDecl(x_1071, x_13, x_1099);
if (lean_obj_tag(x_1100) == 0)
{
lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; 
x_1101 = lean_ctor_get(x_1100, 0);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1100, 1);
lean_inc(x_1102);
lean_dec(x_1100);
x_1103 = lean_ctor_get(x_1101, 1);
lean_inc(x_1103);
x_1104 = lean_ctor_get(x_1101, 4);
lean_inc(x_1104);
lean_dec(x_1101);
x_1105 = l_Lean_Meta_withLocalContext___rarg(x_1103, x_1104, x_1081, x_13, x_1102);
lean_dec(x_13);
return x_1105;
}
else
{
uint8_t x_1106; 
lean_dec(x_1081);
lean_dec(x_13);
x_1106 = !lean_is_exclusive(x_1100);
if (x_1106 == 0)
{
return x_1100;
}
else
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; 
x_1107 = lean_ctor_get(x_1100, 0);
x_1108 = lean_ctor_get(x_1100, 1);
lean_inc(x_1108);
lean_inc(x_1107);
lean_dec(x_1100);
x_1109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1109, 0, x_1107);
lean_ctor_set(x_1109, 1, x_1108);
return x_1109;
}
}
}
}
}
else
{
uint8_t x_1118; 
lean_dec(x_1065);
lean_dec(x_1057);
lean_dec(x_1042);
lean_dec(x_1029);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1118 = !lean_is_exclusive(x_1067);
if (x_1118 == 0)
{
return x_1067;
}
else
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; 
x_1119 = lean_ctor_get(x_1067, 0);
x_1120 = lean_ctor_get(x_1067, 1);
lean_inc(x_1120);
lean_inc(x_1119);
lean_dec(x_1067);
x_1121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1121, 0, x_1119);
lean_ctor_set(x_1121, 1, x_1120);
return x_1121;
}
}
}
else
{
uint8_t x_1122; 
lean_dec(x_1057);
lean_dec(x_1042);
lean_dec(x_1029);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1122 = !lean_is_exclusive(x_1062);
if (x_1122 == 0)
{
return x_1062;
}
else
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; 
x_1123 = lean_ctor_get(x_1062, 0);
x_1124 = lean_ctor_get(x_1062, 1);
lean_inc(x_1124);
lean_inc(x_1123);
lean_dec(x_1062);
x_1125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1125, 0, x_1123);
lean_ctor_set(x_1125, 1, x_1124);
return x_1125;
}
}
}
else
{
uint8_t x_1126; 
lean_dec(x_1042);
lean_dec(x_1029);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1126 = !lean_is_exclusive(x_1054);
if (x_1126 == 0)
{
return x_1054;
}
else
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; 
x_1127 = lean_ctor_get(x_1054, 0);
x_1128 = lean_ctor_get(x_1054, 1);
lean_inc(x_1128);
lean_inc(x_1127);
lean_dec(x_1054);
x_1129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1129, 0, x_1127);
lean_ctor_set(x_1129, 1, x_1128);
return x_1129;
}
}
}
}
else
{
uint8_t x_1143; 
lean_dec(x_1042);
lean_dec(x_1032);
lean_dec(x_1029);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1143 = !lean_is_exclusive(x_1044);
if (x_1143 == 0)
{
return x_1044;
}
else
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; 
x_1144 = lean_ctor_get(x_1044, 0);
x_1145 = lean_ctor_get(x_1044, 1);
lean_inc(x_1145);
lean_inc(x_1144);
lean_dec(x_1044);
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
lean_dec(x_1032);
lean_dec(x_1029);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1147 = !lean_is_exclusive(x_1041);
if (x_1147 == 0)
{
return x_1041;
}
else
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
x_1148 = lean_ctor_get(x_1041, 0);
x_1149 = lean_ctor_get(x_1041, 1);
lean_inc(x_1149);
lean_inc(x_1148);
lean_dec(x_1041);
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
lean_dec(x_1029);
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
x_1151 = !lean_is_exclusive(x_1030);
if (x_1151 == 0)
{
return x_1030;
}
else
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; 
x_1152 = lean_ctor_get(x_1030, 0);
x_1153 = lean_ctor_get(x_1030, 1);
lean_inc(x_1153);
lean_inc(x_1152);
lean_dec(x_1030);
x_1154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1154, 0, x_1152);
lean_ctor_set(x_1154, 1, x_1153);
return x_1154;
}
}
}
case 10:
{
lean_object* x_1155; lean_object* x_1156; 
lean_dec(x_12);
lean_dec(x_10);
x_1155 = lean_ctor_get(x_7, 5);
lean_inc(x_1155);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1156 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_1155, x_13, x_14);
if (lean_obj_tag(x_1156) == 0)
{
lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
x_1157 = lean_ctor_get(x_1156, 1);
lean_inc(x_1157);
lean_dec(x_1156);
x_1158 = lean_ctor_get(x_1157, 1);
lean_inc(x_1158);
x_1159 = lean_ctor_get(x_7, 6);
lean_inc(x_1159);
x_1160 = l_List_redLength___main___rarg(x_1159);
x_1161 = lean_mk_empty_array_with_capacity(x_1160);
lean_dec(x_1160);
lean_inc(x_1159);
x_1162 = l_List_toArrayAux___main___rarg(x_1159, x_1161);
x_1163 = x_1162;
x_1164 = lean_unsigned_to_nat(0u);
lean_inc(x_1158);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_1165 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_1165, 0, x_1);
lean_closure_set(x_1165, 1, x_6);
lean_closure_set(x_1165, 2, x_7);
lean_closure_set(x_1165, 3, x_9);
lean_closure_set(x_1165, 4, x_11);
lean_closure_set(x_1165, 5, x_1158);
lean_closure_set(x_1165, 6, x_1159);
lean_closure_set(x_1165, 7, x_1164);
lean_closure_set(x_1165, 8, x_1163);
x_1166 = x_1165;
lean_inc(x_13);
x_1167 = lean_apply_2(x_1166, x_13, x_1157);
if (lean_obj_tag(x_1167) == 0)
{
lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; 
x_1168 = lean_ctor_get(x_1167, 0);
lean_inc(x_1168);
x_1169 = lean_ctor_get(x_1167, 1);
lean_inc(x_1169);
lean_dec(x_1167);
lean_inc(x_1);
x_1170 = l_Lean_Meta_getMVarType(x_1, x_13, x_1169);
if (lean_obj_tag(x_1170) == 0)
{
lean_object* x_1171; lean_object* x_1172; uint8_t x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
x_1171 = lean_ctor_get(x_1170, 0);
lean_inc(x_1171);
x_1172 = lean_ctor_get(x_1170, 1);
lean_inc(x_1172);
lean_dec(x_1170);
x_1173 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_1168);
x_1174 = x_1168;
x_1175 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1164, x_1174);
x_1176 = x_1175;
lean_inc(x_2);
x_1177 = lean_array_push(x_1176, x_2);
if (x_1173 == 0)
{
lean_object* x_1257; uint8_t x_1258; 
x_1257 = l_Lean_MetavarContext_exprDependsOn(x_1158, x_1171, x_2);
lean_dec(x_2);
x_1258 = lean_unbox(x_1257);
lean_dec(x_1257);
if (x_1258 == 0)
{
x_1178 = x_1172;
goto block_1256;
}
else
{
lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; uint8_t x_1265; 
lean_dec(x_1177);
lean_dec(x_1168);
lean_dec(x_1155);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_1259 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1259, 0, x_3);
x_1260 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_1261 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1261, 0, x_1260);
lean_ctor_set(x_1261, 1, x_1259);
x_1262 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_1263 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1263, 0, x_1261);
lean_ctor_set(x_1263, 1, x_1262);
x_1264 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1263, x_13, x_1172);
lean_dec(x_13);
x_1265 = !lean_is_exclusive(x_1264);
if (x_1265 == 0)
{
return x_1264;
}
else
{
lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; 
x_1266 = lean_ctor_get(x_1264, 0);
x_1267 = lean_ctor_get(x_1264, 1);
lean_inc(x_1267);
lean_inc(x_1266);
lean_dec(x_1264);
x_1268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1268, 0, x_1266);
lean_ctor_set(x_1268, 1, x_1267);
return x_1268;
}
}
}
else
{
lean_dec(x_1171);
lean_dec(x_1158);
lean_dec(x_2);
x_1178 = x_1172;
goto block_1256;
}
block_1256:
{
uint8_t x_1179; lean_object* x_1180; 
x_1179 = 1;
x_1180 = l_Lean_Meta_revert(x_1, x_1177, x_1179, x_13, x_1178);
if (lean_obj_tag(x_1180) == 0)
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; uint8_t x_1187; lean_object* x_1188; 
x_1181 = lean_ctor_get(x_1180, 0);
lean_inc(x_1181);
x_1182 = lean_ctor_get(x_1180, 1);
lean_inc(x_1182);
lean_dec(x_1180);
x_1183 = lean_ctor_get(x_1181, 0);
lean_inc(x_1183);
x_1184 = lean_ctor_get(x_1181, 1);
lean_inc(x_1184);
lean_dec(x_1181);
x_1185 = lean_array_get_size(x_1168);
x_1186 = lean_box(0);
x_1187 = 0;
x_1188 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1187, x_1184, x_1185, x_1186, x_13, x_1182);
if (lean_obj_tag(x_1188) == 0)
{
lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; 
x_1189 = lean_ctor_get(x_1188, 0);
lean_inc(x_1189);
x_1190 = lean_ctor_get(x_1188, 1);
lean_inc(x_1190);
lean_dec(x_1188);
x_1191 = lean_ctor_get(x_1189, 0);
lean_inc(x_1191);
x_1192 = lean_ctor_get(x_1189, 1);
lean_inc(x_1192);
lean_dec(x_1189);
x_1193 = l_Lean_Meta_intro1(x_1192, x_1187, x_13, x_1190);
if (lean_obj_tag(x_1193) == 0)
{
lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; uint8_t x_1208; lean_object* x_1209; lean_object* x_1237; uint8_t x_1238; 
x_1194 = lean_ctor_get(x_1193, 0);
lean_inc(x_1194);
x_1195 = lean_ctor_get(x_1193, 1);
lean_inc(x_1195);
lean_dec(x_1193);
x_1196 = lean_ctor_get(x_1194, 0);
lean_inc(x_1196);
x_1197 = lean_ctor_get(x_1194, 1);
lean_inc(x_1197);
lean_dec(x_1194);
x_1198 = lean_box(0);
x_1199 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_1168, x_1191, x_1168, x_1164, x_1198);
lean_dec(x_1168);
x_1200 = x_1191;
x_1201 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1164, x_1200);
x_1202 = x_1201;
lean_inc(x_1196);
x_1203 = l_Lean_mkFVar(x_1196);
lean_inc(x_1197);
x_1204 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_1204, 0, x_1197);
x_1205 = lean_box(x_1173);
lean_inc(x_1197);
x_1206 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_1206, 0, x_1196);
lean_closure_set(x_1206, 1, x_8);
lean_closure_set(x_1206, 2, x_1197);
lean_closure_set(x_1206, 3, x_3);
lean_closure_set(x_1206, 4, x_4);
lean_closure_set(x_1206, 5, x_6);
lean_closure_set(x_1206, 6, x_7);
lean_closure_set(x_1206, 7, x_1155);
lean_closure_set(x_1206, 8, x_1205);
lean_closure_set(x_1206, 9, x_1183);
lean_closure_set(x_1206, 10, x_1199);
lean_closure_set(x_1206, 11, x_1202);
lean_closure_set(x_1206, 12, x_1203);
x_1207 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_1207, 0, x_1204);
lean_closure_set(x_1207, 1, x_1206);
x_1237 = lean_ctor_get(x_1195, 4);
lean_inc(x_1237);
x_1238 = lean_ctor_get_uint8(x_1237, sizeof(void*)*1);
lean_dec(x_1237);
if (x_1238 == 0)
{
x_1208 = x_1187;
x_1209 = x_1195;
goto block_1236;
}
else
{
lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; uint8_t x_1243; 
x_1239 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_1240 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1239, x_13, x_1195);
x_1241 = lean_ctor_get(x_1240, 0);
lean_inc(x_1241);
x_1242 = lean_ctor_get(x_1240, 1);
lean_inc(x_1242);
lean_dec(x_1240);
x_1243 = lean_unbox(x_1241);
lean_dec(x_1241);
x_1208 = x_1243;
x_1209 = x_1242;
goto block_1236;
}
block_1236:
{
if (x_1208 == 0)
{
lean_object* x_1210; 
x_1210 = l_Lean_Meta_getMVarDecl(x_1197, x_13, x_1209);
if (lean_obj_tag(x_1210) == 0)
{
lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; 
x_1211 = lean_ctor_get(x_1210, 0);
lean_inc(x_1211);
x_1212 = lean_ctor_get(x_1210, 1);
lean_inc(x_1212);
lean_dec(x_1210);
x_1213 = lean_ctor_get(x_1211, 1);
lean_inc(x_1213);
x_1214 = lean_ctor_get(x_1211, 4);
lean_inc(x_1214);
lean_dec(x_1211);
x_1215 = l_Lean_Meta_withLocalContext___rarg(x_1213, x_1214, x_1207, x_13, x_1212);
lean_dec(x_13);
return x_1215;
}
else
{
uint8_t x_1216; 
lean_dec(x_1207);
lean_dec(x_13);
x_1216 = !lean_is_exclusive(x_1210);
if (x_1216 == 0)
{
return x_1210;
}
else
{
lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; 
x_1217 = lean_ctor_get(x_1210, 0);
x_1218 = lean_ctor_get(x_1210, 1);
lean_inc(x_1218);
lean_inc(x_1217);
lean_dec(x_1210);
x_1219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1219, 0, x_1217);
lean_ctor_set(x_1219, 1, x_1218);
return x_1219;
}
}
}
else
{
lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; 
lean_inc(x_1197);
x_1220 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1220, 0, x_1197);
x_1221 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_1222 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1222, 0, x_1221);
lean_ctor_set(x_1222, 1, x_1220);
x_1223 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_1224 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1223, x_1222, x_13, x_1209);
x_1225 = lean_ctor_get(x_1224, 1);
lean_inc(x_1225);
lean_dec(x_1224);
x_1226 = l_Lean_Meta_getMVarDecl(x_1197, x_13, x_1225);
if (lean_obj_tag(x_1226) == 0)
{
lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; 
x_1227 = lean_ctor_get(x_1226, 0);
lean_inc(x_1227);
x_1228 = lean_ctor_get(x_1226, 1);
lean_inc(x_1228);
lean_dec(x_1226);
x_1229 = lean_ctor_get(x_1227, 1);
lean_inc(x_1229);
x_1230 = lean_ctor_get(x_1227, 4);
lean_inc(x_1230);
lean_dec(x_1227);
x_1231 = l_Lean_Meta_withLocalContext___rarg(x_1229, x_1230, x_1207, x_13, x_1228);
lean_dec(x_13);
return x_1231;
}
else
{
uint8_t x_1232; 
lean_dec(x_1207);
lean_dec(x_13);
x_1232 = !lean_is_exclusive(x_1226);
if (x_1232 == 0)
{
return x_1226;
}
else
{
lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; 
x_1233 = lean_ctor_get(x_1226, 0);
x_1234 = lean_ctor_get(x_1226, 1);
lean_inc(x_1234);
lean_inc(x_1233);
lean_dec(x_1226);
x_1235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1235, 0, x_1233);
lean_ctor_set(x_1235, 1, x_1234);
return x_1235;
}
}
}
}
}
else
{
uint8_t x_1244; 
lean_dec(x_1191);
lean_dec(x_1183);
lean_dec(x_1168);
lean_dec(x_1155);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1244 = !lean_is_exclusive(x_1193);
if (x_1244 == 0)
{
return x_1193;
}
else
{
lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; 
x_1245 = lean_ctor_get(x_1193, 0);
x_1246 = lean_ctor_get(x_1193, 1);
lean_inc(x_1246);
lean_inc(x_1245);
lean_dec(x_1193);
x_1247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1247, 0, x_1245);
lean_ctor_set(x_1247, 1, x_1246);
return x_1247;
}
}
}
else
{
uint8_t x_1248; 
lean_dec(x_1183);
lean_dec(x_1168);
lean_dec(x_1155);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1248 = !lean_is_exclusive(x_1188);
if (x_1248 == 0)
{
return x_1188;
}
else
{
lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; 
x_1249 = lean_ctor_get(x_1188, 0);
x_1250 = lean_ctor_get(x_1188, 1);
lean_inc(x_1250);
lean_inc(x_1249);
lean_dec(x_1188);
x_1251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1251, 0, x_1249);
lean_ctor_set(x_1251, 1, x_1250);
return x_1251;
}
}
}
else
{
uint8_t x_1252; 
lean_dec(x_1168);
lean_dec(x_1155);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1252 = !lean_is_exclusive(x_1180);
if (x_1252 == 0)
{
return x_1180;
}
else
{
lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; 
x_1253 = lean_ctor_get(x_1180, 0);
x_1254 = lean_ctor_get(x_1180, 1);
lean_inc(x_1254);
lean_inc(x_1253);
lean_dec(x_1180);
x_1255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1255, 0, x_1253);
lean_ctor_set(x_1255, 1, x_1254);
return x_1255;
}
}
}
}
else
{
uint8_t x_1269; 
lean_dec(x_1168);
lean_dec(x_1158);
lean_dec(x_1155);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1269 = !lean_is_exclusive(x_1170);
if (x_1269 == 0)
{
return x_1170;
}
else
{
lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; 
x_1270 = lean_ctor_get(x_1170, 0);
x_1271 = lean_ctor_get(x_1170, 1);
lean_inc(x_1271);
lean_inc(x_1270);
lean_dec(x_1170);
x_1272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1272, 0, x_1270);
lean_ctor_set(x_1272, 1, x_1271);
return x_1272;
}
}
}
else
{
uint8_t x_1273; 
lean_dec(x_1158);
lean_dec(x_1155);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1273 = !lean_is_exclusive(x_1167);
if (x_1273 == 0)
{
return x_1167;
}
else
{
lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; 
x_1274 = lean_ctor_get(x_1167, 0);
x_1275 = lean_ctor_get(x_1167, 1);
lean_inc(x_1275);
lean_inc(x_1274);
lean_dec(x_1167);
x_1276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1276, 0, x_1274);
lean_ctor_set(x_1276, 1, x_1275);
return x_1276;
}
}
}
else
{
uint8_t x_1277; 
lean_dec(x_1155);
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
x_1277 = !lean_is_exclusive(x_1156);
if (x_1277 == 0)
{
return x_1156;
}
else
{
lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; 
x_1278 = lean_ctor_get(x_1156, 0);
x_1279 = lean_ctor_get(x_1156, 1);
lean_inc(x_1279);
lean_inc(x_1278);
lean_dec(x_1156);
x_1280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1280, 0, x_1278);
lean_ctor_set(x_1280, 1, x_1279);
return x_1280;
}
}
}
case 11:
{
lean_object* x_1281; lean_object* x_1282; 
lean_dec(x_12);
lean_dec(x_10);
x_1281 = lean_ctor_get(x_7, 5);
lean_inc(x_1281);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1282 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_1281, x_13, x_14);
if (lean_obj_tag(x_1282) == 0)
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; 
x_1283 = lean_ctor_get(x_1282, 1);
lean_inc(x_1283);
lean_dec(x_1282);
x_1284 = lean_ctor_get(x_1283, 1);
lean_inc(x_1284);
x_1285 = lean_ctor_get(x_7, 6);
lean_inc(x_1285);
x_1286 = l_List_redLength___main___rarg(x_1285);
x_1287 = lean_mk_empty_array_with_capacity(x_1286);
lean_dec(x_1286);
lean_inc(x_1285);
x_1288 = l_List_toArrayAux___main___rarg(x_1285, x_1287);
x_1289 = x_1288;
x_1290 = lean_unsigned_to_nat(0u);
lean_inc(x_1284);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_1291 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_1291, 0, x_1);
lean_closure_set(x_1291, 1, x_6);
lean_closure_set(x_1291, 2, x_7);
lean_closure_set(x_1291, 3, x_9);
lean_closure_set(x_1291, 4, x_11);
lean_closure_set(x_1291, 5, x_1284);
lean_closure_set(x_1291, 6, x_1285);
lean_closure_set(x_1291, 7, x_1290);
lean_closure_set(x_1291, 8, x_1289);
x_1292 = x_1291;
lean_inc(x_13);
x_1293 = lean_apply_2(x_1292, x_13, x_1283);
if (lean_obj_tag(x_1293) == 0)
{
lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; 
x_1294 = lean_ctor_get(x_1293, 0);
lean_inc(x_1294);
x_1295 = lean_ctor_get(x_1293, 1);
lean_inc(x_1295);
lean_dec(x_1293);
lean_inc(x_1);
x_1296 = l_Lean_Meta_getMVarType(x_1, x_13, x_1295);
if (lean_obj_tag(x_1296) == 0)
{
lean_object* x_1297; lean_object* x_1298; uint8_t x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; 
x_1297 = lean_ctor_get(x_1296, 0);
lean_inc(x_1297);
x_1298 = lean_ctor_get(x_1296, 1);
lean_inc(x_1298);
lean_dec(x_1296);
x_1299 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_1294);
x_1300 = x_1294;
x_1301 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1290, x_1300);
x_1302 = x_1301;
lean_inc(x_2);
x_1303 = lean_array_push(x_1302, x_2);
if (x_1299 == 0)
{
lean_object* x_1383; uint8_t x_1384; 
x_1383 = l_Lean_MetavarContext_exprDependsOn(x_1284, x_1297, x_2);
lean_dec(x_2);
x_1384 = lean_unbox(x_1383);
lean_dec(x_1383);
if (x_1384 == 0)
{
x_1304 = x_1298;
goto block_1382;
}
else
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; uint8_t x_1391; 
lean_dec(x_1303);
lean_dec(x_1294);
lean_dec(x_1281);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_1385 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1385, 0, x_3);
x_1386 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_1387 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1387, 0, x_1386);
lean_ctor_set(x_1387, 1, x_1385);
x_1388 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_1389 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1389, 0, x_1387);
lean_ctor_set(x_1389, 1, x_1388);
x_1390 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1389, x_13, x_1298);
lean_dec(x_13);
x_1391 = !lean_is_exclusive(x_1390);
if (x_1391 == 0)
{
return x_1390;
}
else
{
lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; 
x_1392 = lean_ctor_get(x_1390, 0);
x_1393 = lean_ctor_get(x_1390, 1);
lean_inc(x_1393);
lean_inc(x_1392);
lean_dec(x_1390);
x_1394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1394, 0, x_1392);
lean_ctor_set(x_1394, 1, x_1393);
return x_1394;
}
}
}
else
{
lean_dec(x_1297);
lean_dec(x_1284);
lean_dec(x_2);
x_1304 = x_1298;
goto block_1382;
}
block_1382:
{
uint8_t x_1305; lean_object* x_1306; 
x_1305 = 1;
x_1306 = l_Lean_Meta_revert(x_1, x_1303, x_1305, x_13, x_1304);
if (lean_obj_tag(x_1306) == 0)
{
lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; uint8_t x_1313; lean_object* x_1314; 
x_1307 = lean_ctor_get(x_1306, 0);
lean_inc(x_1307);
x_1308 = lean_ctor_get(x_1306, 1);
lean_inc(x_1308);
lean_dec(x_1306);
x_1309 = lean_ctor_get(x_1307, 0);
lean_inc(x_1309);
x_1310 = lean_ctor_get(x_1307, 1);
lean_inc(x_1310);
lean_dec(x_1307);
x_1311 = lean_array_get_size(x_1294);
x_1312 = lean_box(0);
x_1313 = 0;
x_1314 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1313, x_1310, x_1311, x_1312, x_13, x_1308);
if (lean_obj_tag(x_1314) == 0)
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; 
x_1315 = lean_ctor_get(x_1314, 0);
lean_inc(x_1315);
x_1316 = lean_ctor_get(x_1314, 1);
lean_inc(x_1316);
lean_dec(x_1314);
x_1317 = lean_ctor_get(x_1315, 0);
lean_inc(x_1317);
x_1318 = lean_ctor_get(x_1315, 1);
lean_inc(x_1318);
lean_dec(x_1315);
x_1319 = l_Lean_Meta_intro1(x_1318, x_1313, x_13, x_1316);
if (lean_obj_tag(x_1319) == 0)
{
lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; uint8_t x_1334; lean_object* x_1335; lean_object* x_1363; uint8_t x_1364; 
x_1320 = lean_ctor_get(x_1319, 0);
lean_inc(x_1320);
x_1321 = lean_ctor_get(x_1319, 1);
lean_inc(x_1321);
lean_dec(x_1319);
x_1322 = lean_ctor_get(x_1320, 0);
lean_inc(x_1322);
x_1323 = lean_ctor_get(x_1320, 1);
lean_inc(x_1323);
lean_dec(x_1320);
x_1324 = lean_box(0);
x_1325 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_1294, x_1317, x_1294, x_1290, x_1324);
lean_dec(x_1294);
x_1326 = x_1317;
x_1327 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1290, x_1326);
x_1328 = x_1327;
lean_inc(x_1322);
x_1329 = l_Lean_mkFVar(x_1322);
lean_inc(x_1323);
x_1330 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_1330, 0, x_1323);
x_1331 = lean_box(x_1299);
lean_inc(x_1323);
x_1332 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_1332, 0, x_1322);
lean_closure_set(x_1332, 1, x_8);
lean_closure_set(x_1332, 2, x_1323);
lean_closure_set(x_1332, 3, x_3);
lean_closure_set(x_1332, 4, x_4);
lean_closure_set(x_1332, 5, x_6);
lean_closure_set(x_1332, 6, x_7);
lean_closure_set(x_1332, 7, x_1281);
lean_closure_set(x_1332, 8, x_1331);
lean_closure_set(x_1332, 9, x_1309);
lean_closure_set(x_1332, 10, x_1325);
lean_closure_set(x_1332, 11, x_1328);
lean_closure_set(x_1332, 12, x_1329);
x_1333 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_1333, 0, x_1330);
lean_closure_set(x_1333, 1, x_1332);
x_1363 = lean_ctor_get(x_1321, 4);
lean_inc(x_1363);
x_1364 = lean_ctor_get_uint8(x_1363, sizeof(void*)*1);
lean_dec(x_1363);
if (x_1364 == 0)
{
x_1334 = x_1313;
x_1335 = x_1321;
goto block_1362;
}
else
{
lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; uint8_t x_1369; 
x_1365 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_1366 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1365, x_13, x_1321);
x_1367 = lean_ctor_get(x_1366, 0);
lean_inc(x_1367);
x_1368 = lean_ctor_get(x_1366, 1);
lean_inc(x_1368);
lean_dec(x_1366);
x_1369 = lean_unbox(x_1367);
lean_dec(x_1367);
x_1334 = x_1369;
x_1335 = x_1368;
goto block_1362;
}
block_1362:
{
if (x_1334 == 0)
{
lean_object* x_1336; 
x_1336 = l_Lean_Meta_getMVarDecl(x_1323, x_13, x_1335);
if (lean_obj_tag(x_1336) == 0)
{
lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; 
x_1337 = lean_ctor_get(x_1336, 0);
lean_inc(x_1337);
x_1338 = lean_ctor_get(x_1336, 1);
lean_inc(x_1338);
lean_dec(x_1336);
x_1339 = lean_ctor_get(x_1337, 1);
lean_inc(x_1339);
x_1340 = lean_ctor_get(x_1337, 4);
lean_inc(x_1340);
lean_dec(x_1337);
x_1341 = l_Lean_Meta_withLocalContext___rarg(x_1339, x_1340, x_1333, x_13, x_1338);
lean_dec(x_13);
return x_1341;
}
else
{
uint8_t x_1342; 
lean_dec(x_1333);
lean_dec(x_13);
x_1342 = !lean_is_exclusive(x_1336);
if (x_1342 == 0)
{
return x_1336;
}
else
{
lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; 
x_1343 = lean_ctor_get(x_1336, 0);
x_1344 = lean_ctor_get(x_1336, 1);
lean_inc(x_1344);
lean_inc(x_1343);
lean_dec(x_1336);
x_1345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1345, 0, x_1343);
lean_ctor_set(x_1345, 1, x_1344);
return x_1345;
}
}
}
else
{
lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; 
lean_inc(x_1323);
x_1346 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1346, 0, x_1323);
x_1347 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_1348 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1348, 0, x_1347);
lean_ctor_set(x_1348, 1, x_1346);
x_1349 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_1350 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1349, x_1348, x_13, x_1335);
x_1351 = lean_ctor_get(x_1350, 1);
lean_inc(x_1351);
lean_dec(x_1350);
x_1352 = l_Lean_Meta_getMVarDecl(x_1323, x_13, x_1351);
if (lean_obj_tag(x_1352) == 0)
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; 
x_1353 = lean_ctor_get(x_1352, 0);
lean_inc(x_1353);
x_1354 = lean_ctor_get(x_1352, 1);
lean_inc(x_1354);
lean_dec(x_1352);
x_1355 = lean_ctor_get(x_1353, 1);
lean_inc(x_1355);
x_1356 = lean_ctor_get(x_1353, 4);
lean_inc(x_1356);
lean_dec(x_1353);
x_1357 = l_Lean_Meta_withLocalContext___rarg(x_1355, x_1356, x_1333, x_13, x_1354);
lean_dec(x_13);
return x_1357;
}
else
{
uint8_t x_1358; 
lean_dec(x_1333);
lean_dec(x_13);
x_1358 = !lean_is_exclusive(x_1352);
if (x_1358 == 0)
{
return x_1352;
}
else
{
lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; 
x_1359 = lean_ctor_get(x_1352, 0);
x_1360 = lean_ctor_get(x_1352, 1);
lean_inc(x_1360);
lean_inc(x_1359);
lean_dec(x_1352);
x_1361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1361, 0, x_1359);
lean_ctor_set(x_1361, 1, x_1360);
return x_1361;
}
}
}
}
}
else
{
uint8_t x_1370; 
lean_dec(x_1317);
lean_dec(x_1309);
lean_dec(x_1294);
lean_dec(x_1281);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1370 = !lean_is_exclusive(x_1319);
if (x_1370 == 0)
{
return x_1319;
}
else
{
lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; 
x_1371 = lean_ctor_get(x_1319, 0);
x_1372 = lean_ctor_get(x_1319, 1);
lean_inc(x_1372);
lean_inc(x_1371);
lean_dec(x_1319);
x_1373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1373, 0, x_1371);
lean_ctor_set(x_1373, 1, x_1372);
return x_1373;
}
}
}
else
{
uint8_t x_1374; 
lean_dec(x_1309);
lean_dec(x_1294);
lean_dec(x_1281);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1374 = !lean_is_exclusive(x_1314);
if (x_1374 == 0)
{
return x_1314;
}
else
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
x_1375 = lean_ctor_get(x_1314, 0);
x_1376 = lean_ctor_get(x_1314, 1);
lean_inc(x_1376);
lean_inc(x_1375);
lean_dec(x_1314);
x_1377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1377, 0, x_1375);
lean_ctor_set(x_1377, 1, x_1376);
return x_1377;
}
}
}
else
{
uint8_t x_1378; 
lean_dec(x_1294);
lean_dec(x_1281);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1378 = !lean_is_exclusive(x_1306);
if (x_1378 == 0)
{
return x_1306;
}
else
{
lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
x_1379 = lean_ctor_get(x_1306, 0);
x_1380 = lean_ctor_get(x_1306, 1);
lean_inc(x_1380);
lean_inc(x_1379);
lean_dec(x_1306);
x_1381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1381, 0, x_1379);
lean_ctor_set(x_1381, 1, x_1380);
return x_1381;
}
}
}
}
else
{
uint8_t x_1395; 
lean_dec(x_1294);
lean_dec(x_1284);
lean_dec(x_1281);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1395 = !lean_is_exclusive(x_1296);
if (x_1395 == 0)
{
return x_1296;
}
else
{
lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; 
x_1396 = lean_ctor_get(x_1296, 0);
x_1397 = lean_ctor_get(x_1296, 1);
lean_inc(x_1397);
lean_inc(x_1396);
lean_dec(x_1296);
x_1398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1398, 0, x_1396);
lean_ctor_set(x_1398, 1, x_1397);
return x_1398;
}
}
}
else
{
uint8_t x_1399; 
lean_dec(x_1284);
lean_dec(x_1281);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1399 = !lean_is_exclusive(x_1293);
if (x_1399 == 0)
{
return x_1293;
}
else
{
lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; 
x_1400 = lean_ctor_get(x_1293, 0);
x_1401 = lean_ctor_get(x_1293, 1);
lean_inc(x_1401);
lean_inc(x_1400);
lean_dec(x_1293);
x_1402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1402, 0, x_1400);
lean_ctor_set(x_1402, 1, x_1401);
return x_1402;
}
}
}
else
{
uint8_t x_1403; 
lean_dec(x_1281);
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
x_1403 = !lean_is_exclusive(x_1282);
if (x_1403 == 0)
{
return x_1282;
}
else
{
lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; 
x_1404 = lean_ctor_get(x_1282, 0);
x_1405 = lean_ctor_get(x_1282, 1);
lean_inc(x_1405);
lean_inc(x_1404);
lean_dec(x_1282);
x_1406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1406, 0, x_1404);
lean_ctor_set(x_1406, 1, x_1405);
return x_1406;
}
}
}
default: 
{
lean_object* x_1407; lean_object* x_1408; 
lean_dec(x_12);
lean_dec(x_10);
x_1407 = lean_ctor_get(x_7, 5);
lean_inc(x_1407);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1408 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_6, x_9, x_11, x_1407, x_13, x_14);
if (lean_obj_tag(x_1408) == 0)
{
lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; 
x_1409 = lean_ctor_get(x_1408, 1);
lean_inc(x_1409);
lean_dec(x_1408);
x_1410 = lean_ctor_get(x_1409, 1);
lean_inc(x_1410);
x_1411 = lean_ctor_get(x_7, 6);
lean_inc(x_1411);
x_1412 = l_List_redLength___main___rarg(x_1411);
x_1413 = lean_mk_empty_array_with_capacity(x_1412);
lean_dec(x_1412);
lean_inc(x_1411);
x_1414 = l_List_toArrayAux___main___rarg(x_1411, x_1413);
x_1415 = x_1414;
x_1416 = lean_unsigned_to_nat(0u);
lean_inc(x_1410);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_1417 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__5___boxed), 11, 9);
lean_closure_set(x_1417, 0, x_1);
lean_closure_set(x_1417, 1, x_6);
lean_closure_set(x_1417, 2, x_7);
lean_closure_set(x_1417, 3, x_9);
lean_closure_set(x_1417, 4, x_11);
lean_closure_set(x_1417, 5, x_1410);
lean_closure_set(x_1417, 6, x_1411);
lean_closure_set(x_1417, 7, x_1416);
lean_closure_set(x_1417, 8, x_1415);
x_1418 = x_1417;
lean_inc(x_13);
x_1419 = lean_apply_2(x_1418, x_13, x_1409);
if (lean_obj_tag(x_1419) == 0)
{
lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; 
x_1420 = lean_ctor_get(x_1419, 0);
lean_inc(x_1420);
x_1421 = lean_ctor_get(x_1419, 1);
lean_inc(x_1421);
lean_dec(x_1419);
lean_inc(x_1);
x_1422 = l_Lean_Meta_getMVarType(x_1, x_13, x_1421);
if (lean_obj_tag(x_1422) == 0)
{
lean_object* x_1423; lean_object* x_1424; uint8_t x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; 
x_1423 = lean_ctor_get(x_1422, 0);
lean_inc(x_1423);
x_1424 = lean_ctor_get(x_1422, 1);
lean_inc(x_1424);
lean_dec(x_1422);
x_1425 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
lean_inc(x_1420);
x_1426 = x_1420;
x_1427 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1416, x_1426);
x_1428 = x_1427;
lean_inc(x_2);
x_1429 = lean_array_push(x_1428, x_2);
if (x_1425 == 0)
{
lean_object* x_1509; uint8_t x_1510; 
x_1509 = l_Lean_MetavarContext_exprDependsOn(x_1410, x_1423, x_2);
lean_dec(x_2);
x_1510 = lean_unbox(x_1509);
lean_dec(x_1509);
if (x_1510 == 0)
{
x_1430 = x_1424;
goto block_1508;
}
else
{
lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; uint8_t x_1517; 
lean_dec(x_1429);
lean_dec(x_1420);
lean_dec(x_1407);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_1511 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1511, 0, x_3);
x_1512 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__6;
x_1513 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1513, 0, x_1512);
lean_ctor_set(x_1513, 1, x_1511);
x_1514 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__8;
x_1515 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1515, 0, x_1513);
lean_ctor_set(x_1515, 1, x_1514);
x_1516 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1515, x_13, x_1424);
lean_dec(x_13);
x_1517 = !lean_is_exclusive(x_1516);
if (x_1517 == 0)
{
return x_1516;
}
else
{
lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; 
x_1518 = lean_ctor_get(x_1516, 0);
x_1519 = lean_ctor_get(x_1516, 1);
lean_inc(x_1519);
lean_inc(x_1518);
lean_dec(x_1516);
x_1520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1520, 0, x_1518);
lean_ctor_set(x_1520, 1, x_1519);
return x_1520;
}
}
}
else
{
lean_dec(x_1423);
lean_dec(x_1410);
lean_dec(x_2);
x_1430 = x_1424;
goto block_1508;
}
block_1508:
{
uint8_t x_1431; lean_object* x_1432; 
x_1431 = 1;
x_1432 = l_Lean_Meta_revert(x_1, x_1429, x_1431, x_13, x_1430);
if (lean_obj_tag(x_1432) == 0)
{
lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; uint8_t x_1439; lean_object* x_1440; 
x_1433 = lean_ctor_get(x_1432, 0);
lean_inc(x_1433);
x_1434 = lean_ctor_get(x_1432, 1);
lean_inc(x_1434);
lean_dec(x_1432);
x_1435 = lean_ctor_get(x_1433, 0);
lean_inc(x_1435);
x_1436 = lean_ctor_get(x_1433, 1);
lean_inc(x_1436);
lean_dec(x_1433);
x_1437 = lean_array_get_size(x_1420);
x_1438 = lean_box(0);
x_1439 = 0;
x_1440 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_1439, x_1436, x_1437, x_1438, x_13, x_1434);
if (lean_obj_tag(x_1440) == 0)
{
lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; 
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
x_1445 = l_Lean_Meta_intro1(x_1444, x_1439, x_13, x_1442);
if (lean_obj_tag(x_1445) == 0)
{
lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; uint8_t x_1460; lean_object* x_1461; lean_object* x_1489; uint8_t x_1490; 
x_1446 = lean_ctor_get(x_1445, 0);
lean_inc(x_1446);
x_1447 = lean_ctor_get(x_1445, 1);
lean_inc(x_1447);
lean_dec(x_1445);
x_1448 = lean_ctor_get(x_1446, 0);
lean_inc(x_1448);
x_1449 = lean_ctor_get(x_1446, 1);
lean_inc(x_1449);
lean_dec(x_1446);
x_1450 = lean_box(0);
x_1451 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__6(x_1420, x_1443, x_1420, x_1416, x_1450);
lean_dec(x_1420);
x_1452 = x_1443;
x_1453 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1416, x_1452);
x_1454 = x_1453;
lean_inc(x_1448);
x_1455 = l_Lean_mkFVar(x_1448);
lean_inc(x_1449);
x_1456 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 3, 1);
lean_closure_set(x_1456, 0, x_1449);
x_1457 = lean_box(x_1425);
lean_inc(x_1449);
x_1458 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___lambda__1___boxed), 16, 13);
lean_closure_set(x_1458, 0, x_1448);
lean_closure_set(x_1458, 1, x_8);
lean_closure_set(x_1458, 2, x_1449);
lean_closure_set(x_1458, 3, x_3);
lean_closure_set(x_1458, 4, x_4);
lean_closure_set(x_1458, 5, x_6);
lean_closure_set(x_1458, 6, x_7);
lean_closure_set(x_1458, 7, x_1407);
lean_closure_set(x_1458, 8, x_1457);
lean_closure_set(x_1458, 9, x_1435);
lean_closure_set(x_1458, 10, x_1451);
lean_closure_set(x_1458, 11, x_1454);
lean_closure_set(x_1458, 12, x_1455);
x_1459 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_1459, 0, x_1456);
lean_closure_set(x_1459, 1, x_1458);
x_1489 = lean_ctor_get(x_1447, 4);
lean_inc(x_1489);
x_1490 = lean_ctor_get_uint8(x_1489, sizeof(void*)*1);
lean_dec(x_1489);
if (x_1490 == 0)
{
x_1460 = x_1439;
x_1461 = x_1447;
goto block_1488;
}
else
{
lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; uint8_t x_1495; 
x_1491 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_1492 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1491, x_13, x_1447);
x_1493 = lean_ctor_get(x_1492, 0);
lean_inc(x_1493);
x_1494 = lean_ctor_get(x_1492, 1);
lean_inc(x_1494);
lean_dec(x_1492);
x_1495 = lean_unbox(x_1493);
lean_dec(x_1493);
x_1460 = x_1495;
x_1461 = x_1494;
goto block_1488;
}
block_1488:
{
if (x_1460 == 0)
{
lean_object* x_1462; 
x_1462 = l_Lean_Meta_getMVarDecl(x_1449, x_13, x_1461);
if (lean_obj_tag(x_1462) == 0)
{
lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; 
x_1463 = lean_ctor_get(x_1462, 0);
lean_inc(x_1463);
x_1464 = lean_ctor_get(x_1462, 1);
lean_inc(x_1464);
lean_dec(x_1462);
x_1465 = lean_ctor_get(x_1463, 1);
lean_inc(x_1465);
x_1466 = lean_ctor_get(x_1463, 4);
lean_inc(x_1466);
lean_dec(x_1463);
x_1467 = l_Lean_Meta_withLocalContext___rarg(x_1465, x_1466, x_1459, x_13, x_1464);
lean_dec(x_13);
return x_1467;
}
else
{
uint8_t x_1468; 
lean_dec(x_1459);
lean_dec(x_13);
x_1468 = !lean_is_exclusive(x_1462);
if (x_1468 == 0)
{
return x_1462;
}
else
{
lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; 
x_1469 = lean_ctor_get(x_1462, 0);
x_1470 = lean_ctor_get(x_1462, 1);
lean_inc(x_1470);
lean_inc(x_1469);
lean_dec(x_1462);
x_1471 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1471, 0, x_1469);
lean_ctor_set(x_1471, 1, x_1470);
return x_1471;
}
}
}
else
{
lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; 
lean_inc(x_1449);
x_1472 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1472, 0, x_1449);
x_1473 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__5;
x_1474 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1474, 0, x_1473);
lean_ctor_set(x_1474, 1, x_1472);
x_1475 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__9___closed__1;
x_1476 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1475, x_1474, x_13, x_1461);
x_1477 = lean_ctor_get(x_1476, 1);
lean_inc(x_1477);
lean_dec(x_1476);
x_1478 = l_Lean_Meta_getMVarDecl(x_1449, x_13, x_1477);
if (lean_obj_tag(x_1478) == 0)
{
lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; 
x_1479 = lean_ctor_get(x_1478, 0);
lean_inc(x_1479);
x_1480 = lean_ctor_get(x_1478, 1);
lean_inc(x_1480);
lean_dec(x_1478);
x_1481 = lean_ctor_get(x_1479, 1);
lean_inc(x_1481);
x_1482 = lean_ctor_get(x_1479, 4);
lean_inc(x_1482);
lean_dec(x_1479);
x_1483 = l_Lean_Meta_withLocalContext___rarg(x_1481, x_1482, x_1459, x_13, x_1480);
lean_dec(x_13);
return x_1483;
}
else
{
uint8_t x_1484; 
lean_dec(x_1459);
lean_dec(x_13);
x_1484 = !lean_is_exclusive(x_1478);
if (x_1484 == 0)
{
return x_1478;
}
else
{
lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; 
x_1485 = lean_ctor_get(x_1478, 0);
x_1486 = lean_ctor_get(x_1478, 1);
lean_inc(x_1486);
lean_inc(x_1485);
lean_dec(x_1478);
x_1487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1487, 0, x_1485);
lean_ctor_set(x_1487, 1, x_1486);
return x_1487;
}
}
}
}
}
else
{
uint8_t x_1496; 
lean_dec(x_1443);
lean_dec(x_1435);
lean_dec(x_1420);
lean_dec(x_1407);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1496 = !lean_is_exclusive(x_1445);
if (x_1496 == 0)
{
return x_1445;
}
else
{
lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; 
x_1497 = lean_ctor_get(x_1445, 0);
x_1498 = lean_ctor_get(x_1445, 1);
lean_inc(x_1498);
lean_inc(x_1497);
lean_dec(x_1445);
x_1499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1499, 0, x_1497);
lean_ctor_set(x_1499, 1, x_1498);
return x_1499;
}
}
}
else
{
uint8_t x_1500; 
lean_dec(x_1435);
lean_dec(x_1420);
lean_dec(x_1407);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1500 = !lean_is_exclusive(x_1440);
if (x_1500 == 0)
{
return x_1440;
}
else
{
lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; 
x_1501 = lean_ctor_get(x_1440, 0);
x_1502 = lean_ctor_get(x_1440, 1);
lean_inc(x_1502);
lean_inc(x_1501);
lean_dec(x_1440);
x_1503 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1503, 0, x_1501);
lean_ctor_set(x_1503, 1, x_1502);
return x_1503;
}
}
}
else
{
uint8_t x_1504; 
lean_dec(x_1420);
lean_dec(x_1407);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1504 = !lean_is_exclusive(x_1432);
if (x_1504 == 0)
{
return x_1432;
}
else
{
lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; 
x_1505 = lean_ctor_get(x_1432, 0);
x_1506 = lean_ctor_get(x_1432, 1);
lean_inc(x_1506);
lean_inc(x_1505);
lean_dec(x_1432);
x_1507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1507, 0, x_1505);
lean_ctor_set(x_1507, 1, x_1506);
return x_1507;
}
}
}
}
else
{
uint8_t x_1521; 
lean_dec(x_1420);
lean_dec(x_1410);
lean_dec(x_1407);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1521 = !lean_is_exclusive(x_1422);
if (x_1521 == 0)
{
return x_1422;
}
else
{
lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; 
x_1522 = lean_ctor_get(x_1422, 0);
x_1523 = lean_ctor_get(x_1422, 1);
lean_inc(x_1523);
lean_inc(x_1522);
lean_dec(x_1422);
x_1524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1524, 0, x_1522);
lean_ctor_set(x_1524, 1, x_1523);
return x_1524;
}
}
}
else
{
uint8_t x_1525; 
lean_dec(x_1410);
lean_dec(x_1407);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1525 = !lean_is_exclusive(x_1419);
if (x_1525 == 0)
{
return x_1419;
}
else
{
lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; 
x_1526 = lean_ctor_get(x_1419, 0);
x_1527 = lean_ctor_get(x_1419, 1);
lean_inc(x_1527);
lean_inc(x_1526);
lean_dec(x_1419);
x_1528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1528, 0, x_1526);
lean_ctor_set(x_1528, 1, x_1527);
return x_1528;
}
}
}
else
{
uint8_t x_1529; 
lean_dec(x_1407);
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
x_1529 = !lean_is_exclusive(x_1408);
if (x_1529 == 0)
{
return x_1408;
}
else
{
lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; 
x_1530 = lean_ctor_get(x_1408, 0);
x_1531 = lean_ctor_get(x_1408, 1);
lean_inc(x_1531);
lean_inc(x_1530);
lean_dec(x_1408);
x_1532 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1532, 0, x_1530);
lean_ctor_set(x_1532, 1, x_1531);
return x_1532;
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
