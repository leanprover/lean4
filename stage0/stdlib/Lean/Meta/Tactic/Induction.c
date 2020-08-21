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
extern lean_object* l_Lean_Core_getConstInfo___closed__5;
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity(lean_object*);
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_induction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
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
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_3__forallTelescopeReducingAuxAux___main___rarg___closed__2;
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
lean_object* l_Lean_Meta_assignExprMVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed(lean_object**);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__6;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__3___closed__3;
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_33 = l_Lean_Meta_assignExprMVar___rarg(x_1, x_12, x_16, x_17, x_18, x_19, x_23);
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
x_48 = l_Lean_Meta_assignExprMVar___rarg(x_1, x_12, x_16, x_17, x_18, x_19, x_23);
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
x_154 = l_Lean_Meta_mkFreshExprMVar___rarg(x_62, x_152, x_153, x_16, x_17, x_18, x_19, x_151);
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
x_128 = l_Lean_Meta_mkFreshExprMVar___rarg(x_62, x_126, x_127, x_16, x_17, x_18, x_19, x_58);
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
x_83 = l_Lean_Core_getConstInfo___closed__5;
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
x_40 = l_Lean_Core_getConstInfo___closed__5;
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
x_66 = l_Lean_Core_getConstInfo___closed__5;
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
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_11);
x_19 = lean_ctor_get(x_8, 5);
lean_inc(x_19);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_20 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_7, x_10, x_12, x_19, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_io_ref_get(x_15, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_8, 6);
lean_inc(x_26);
x_27 = l_List_redLength___main___rarg(x_26);
x_28 = lean_mk_empty_array_with_capacity(x_27);
lean_dec(x_27);
lean_inc(x_26);
x_29 = l_List_toArrayAux___main___rarg(x_26, x_28);
x_30 = x_29;
x_31 = lean_unsigned_to_nat(0u);
lean_inc(x_25);
lean_inc(x_7);
lean_inc(x_1);
x_32 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_32, 0, x_1);
lean_closure_set(x_32, 1, x_7);
lean_closure_set(x_32, 2, x_10);
lean_closure_set(x_32, 3, x_12);
lean_closure_set(x_32, 4, x_25);
lean_closure_set(x_32, 5, x_26);
lean_closure_set(x_32, 6, x_31);
lean_closure_set(x_32, 7, x_30);
x_33 = x_32;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_34 = lean_apply_5(x_33, x_14, x_15, x_16, x_17, x_24);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_1);
x_37 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_40 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = l_Lean_MetavarContext_exprDependsOn(x_25, x_38, x_2);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
x_41 = x_39;
goto block_118;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_35);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_121 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_121, 0, x_3);
x_122 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_123 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_125 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_box(0);
x_127 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_125, x_126, x_14, x_15, x_16, x_17, x_39);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
return x_127;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_127);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
lean_dec(x_38);
lean_dec(x_25);
x_41 = x_39;
goto block_118;
}
block_118:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
lean_inc(x_35);
x_42 = x_35;
x_43 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_31, x_42);
x_44 = x_43;
x_45 = lean_array_push(x_44, x_2);
x_46 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_47 = l_Lean_Meta_revert(x_1, x_45, x_46, x_14, x_15, x_16, x_17, x_41);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
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
x_52 = lean_array_get_size(x_35);
x_53 = lean_box(0);
x_54 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_55 = l_Lean_Meta_introN(x_51, x_52, x_53, x_54, x_14, x_15, x_16, x_17, x_49);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_60 = l_Lean_Meta_intro1(x_59, x_54, x_14, x_15, x_16, x_17, x_57);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_87; lean_object* x_88; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_box(0);
x_66 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_35, x_58, x_35, x_31, x_65);
lean_dec(x_35);
x_96 = l_Lean_Core_getTraceState___rarg(x_17, x_62);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get_uint8(x_97, sizeof(void*)*1);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_87 = x_54;
x_88 = x_99;
goto block_95;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_102 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_101, x_16, x_17, x_100);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_unbox(x_103);
lean_dec(x_103);
x_87 = x_105;
x_88 = x_104;
goto block_95;
}
block_86:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = x_58;
x_69 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_31, x_68);
x_70 = x_69;
lean_inc(x_63);
x_71 = l_Lean_mkFVar(x_63);
lean_inc(x_64);
x_72 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_72, 0, x_64);
x_73 = lean_box(x_40);
lean_inc(x_64);
x_74 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_74, 0, x_63);
lean_closure_set(x_74, 1, x_9);
lean_closure_set(x_74, 2, x_64);
lean_closure_set(x_74, 3, x_3);
lean_closure_set(x_74, 4, x_4);
lean_closure_set(x_74, 5, x_7);
lean_closure_set(x_74, 6, x_8);
lean_closure_set(x_74, 7, x_19);
lean_closure_set(x_74, 8, x_73);
lean_closure_set(x_74, 9, x_50);
lean_closure_set(x_74, 10, x_66);
lean_closure_set(x_74, 11, x_70);
lean_closure_set(x_74, 12, x_71);
x_75 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_75, 0, x_72);
lean_closure_set(x_75, 1, x_74);
x_76 = l_Lean_Meta_getMVarDecl(x_64, x_14, x_15, x_16, x_17, x_67);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 4);
lean_inc(x_80);
lean_dec(x_77);
x_81 = l_Lean_Meta_withLocalContext___rarg(x_79, x_80, x_75, x_14, x_15, x_16, x_17, x_78);
lean_dec(x_14);
return x_81;
}
else
{
uint8_t x_82; 
lean_dec(x_75);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_82 = !lean_is_exclusive(x_76);
if (x_82 == 0)
{
return x_76;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_76, 0);
x_84 = lean_ctor_get(x_76, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_76);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
block_95:
{
if (x_87 == 0)
{
x_67 = x_88;
goto block_86;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_inc(x_64);
x_89 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_89, 0, x_64);
x_90 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_91 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_93 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_92, x_91, x_14, x_15, x_16, x_17, x_88);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_67 = x_94;
goto block_86;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_35);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_106 = !lean_is_exclusive(x_60);
if (x_106 == 0)
{
return x_60;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_60, 0);
x_108 = lean_ctor_get(x_60, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_60);
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
lean_dec(x_50);
lean_dec(x_35);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_110 = !lean_is_exclusive(x_55);
if (x_110 == 0)
{
return x_55;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_55, 0);
x_112 = lean_ctor_get(x_55, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_55);
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
lean_dec(x_35);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_47);
if (x_114 == 0)
{
return x_47;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_47, 0);
x_116 = lean_ctor_get(x_47, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_47);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_35);
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_37);
if (x_132 == 0)
{
return x_37;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_37, 0);
x_134 = lean_ctor_get(x_37, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_37);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_34);
if (x_136 == 0)
{
return x_34;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_34, 0);
x_138 = lean_ctor_get(x_34, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_34);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_20);
if (x_140 == 0)
{
return x_20;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_20, 0);
x_142 = lean_ctor_get(x_20, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_20);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
case 1:
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_13);
lean_dec(x_11);
x_144 = lean_ctor_get(x_8, 5);
lean_inc(x_144);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_145 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_7, x_10, x_12, x_144, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_io_ref_get(x_15, x_146);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_ctor_get(x_148, 0);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_ctor_get(x_8, 6);
lean_inc(x_151);
x_152 = l_List_redLength___main___rarg(x_151);
x_153 = lean_mk_empty_array_with_capacity(x_152);
lean_dec(x_152);
lean_inc(x_151);
x_154 = l_List_toArrayAux___main___rarg(x_151, x_153);
x_155 = x_154;
x_156 = lean_unsigned_to_nat(0u);
lean_inc(x_150);
lean_inc(x_7);
lean_inc(x_1);
x_157 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_157, 0, x_1);
lean_closure_set(x_157, 1, x_7);
lean_closure_set(x_157, 2, x_10);
lean_closure_set(x_157, 3, x_12);
lean_closure_set(x_157, 4, x_150);
lean_closure_set(x_157, 5, x_151);
lean_closure_set(x_157, 6, x_156);
lean_closure_set(x_157, 7, x_155);
x_158 = x_157;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_159 = lean_apply_5(x_158, x_14, x_15, x_16, x_17, x_149);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
lean_inc(x_1);
x_162 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_161);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_165 == 0)
{
lean_object* x_244; uint8_t x_245; 
x_244 = l_Lean_MetavarContext_exprDependsOn(x_150, x_163, x_2);
x_245 = lean_unbox(x_244);
lean_dec(x_244);
if (x_245 == 0)
{
x_166 = x_164;
goto block_243;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
lean_dec(x_160);
lean_dec(x_144);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_246 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_246, 0, x_3);
x_247 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_248 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_246);
x_249 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_250 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_box(0);
x_252 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_250, x_251, x_14, x_15, x_16, x_17, x_164);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
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
lean_dec(x_163);
lean_dec(x_150);
x_166 = x_164;
goto block_243;
}
block_243:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; 
lean_inc(x_160);
x_167 = x_160;
x_168 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_156, x_167);
x_169 = x_168;
x_170 = lean_array_push(x_169, x_2);
x_171 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_172 = l_Lean_Meta_revert(x_1, x_170, x_171, x_14, x_15, x_16, x_17, x_166);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
lean_dec(x_173);
x_177 = lean_array_get_size(x_160);
x_178 = lean_box(0);
x_179 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_180 = l_Lean_Meta_introN(x_176, x_177, x_178, x_179, x_14, x_15, x_16, x_17, x_174);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
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
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_185 = l_Lean_Meta_intro1(x_184, x_179, x_14, x_15, x_16, x_17, x_182);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_212; lean_object* x_213; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_ctor_get(x_186, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
x_190 = lean_box(0);
x_191 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_160, x_183, x_160, x_156, x_190);
lean_dec(x_160);
x_221 = l_Lean_Core_getTraceState___rarg(x_17, x_187);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get_uint8(x_222, sizeof(void*)*1);
lean_dec(x_222);
if (x_223 == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_dec(x_221);
x_212 = x_179;
x_213 = x_224;
goto block_220;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_225 = lean_ctor_get(x_221, 1);
lean_inc(x_225);
lean_dec(x_221);
x_226 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_227 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_226, x_16, x_17, x_225);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_unbox(x_228);
lean_dec(x_228);
x_212 = x_230;
x_213 = x_229;
goto block_220;
}
block_211:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_193 = x_183;
x_194 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_156, x_193);
x_195 = x_194;
lean_inc(x_188);
x_196 = l_Lean_mkFVar(x_188);
lean_inc(x_189);
x_197 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_197, 0, x_189);
x_198 = lean_box(x_165);
lean_inc(x_189);
x_199 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_199, 0, x_188);
lean_closure_set(x_199, 1, x_9);
lean_closure_set(x_199, 2, x_189);
lean_closure_set(x_199, 3, x_3);
lean_closure_set(x_199, 4, x_4);
lean_closure_set(x_199, 5, x_7);
lean_closure_set(x_199, 6, x_8);
lean_closure_set(x_199, 7, x_144);
lean_closure_set(x_199, 8, x_198);
lean_closure_set(x_199, 9, x_175);
lean_closure_set(x_199, 10, x_191);
lean_closure_set(x_199, 11, x_195);
lean_closure_set(x_199, 12, x_196);
x_200 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_200, 0, x_197);
lean_closure_set(x_200, 1, x_199);
x_201 = l_Lean_Meta_getMVarDecl(x_189, x_14, x_15, x_16, x_17, x_192);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_202, 4);
lean_inc(x_205);
lean_dec(x_202);
x_206 = l_Lean_Meta_withLocalContext___rarg(x_204, x_205, x_200, x_14, x_15, x_16, x_17, x_203);
lean_dec(x_14);
return x_206;
}
else
{
uint8_t x_207; 
lean_dec(x_200);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_207 = !lean_is_exclusive(x_201);
if (x_207 == 0)
{
return x_201;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_201, 0);
x_209 = lean_ctor_get(x_201, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_201);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
block_220:
{
if (x_212 == 0)
{
x_192 = x_213;
goto block_211;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_inc(x_189);
x_214 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_214, 0, x_189);
x_215 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_216 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
x_217 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_218 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_217, x_216, x_14, x_15, x_16, x_17, x_213);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_192 = x_219;
goto block_211;
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_183);
lean_dec(x_175);
lean_dec(x_160);
lean_dec(x_144);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_231 = !lean_is_exclusive(x_185);
if (x_231 == 0)
{
return x_185;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_185, 0);
x_233 = lean_ctor_get(x_185, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_185);
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
lean_dec(x_175);
lean_dec(x_160);
lean_dec(x_144);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_235 = !lean_is_exclusive(x_180);
if (x_235 == 0)
{
return x_180;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_180, 0);
x_237 = lean_ctor_get(x_180, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_180);
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
lean_dec(x_160);
lean_dec(x_144);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_239 = !lean_is_exclusive(x_172);
if (x_239 == 0)
{
return x_172;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_172, 0);
x_241 = lean_ctor_get(x_172, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_172);
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
lean_dec(x_160);
lean_dec(x_150);
lean_dec(x_144);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_257 = !lean_is_exclusive(x_162);
if (x_257 == 0)
{
return x_162;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_162, 0);
x_259 = lean_ctor_get(x_162, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_162);
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
lean_dec(x_150);
lean_dec(x_144);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_261 = !lean_is_exclusive(x_159);
if (x_261 == 0)
{
return x_159;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_159, 0);
x_263 = lean_ctor_get(x_159, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_159);
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
lean_dec(x_144);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_265 = !lean_is_exclusive(x_145);
if (x_265 == 0)
{
return x_145;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_145, 0);
x_267 = lean_ctor_get(x_145, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_145);
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
lean_dec(x_13);
lean_dec(x_11);
x_269 = lean_ctor_get(x_8, 5);
lean_inc(x_269);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_270 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_7, x_10, x_12, x_269, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
lean_dec(x_270);
x_272 = lean_io_ref_get(x_15, x_271);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
x_275 = lean_ctor_get(x_273, 0);
lean_inc(x_275);
lean_dec(x_273);
x_276 = lean_ctor_get(x_8, 6);
lean_inc(x_276);
x_277 = l_List_redLength___main___rarg(x_276);
x_278 = lean_mk_empty_array_with_capacity(x_277);
lean_dec(x_277);
lean_inc(x_276);
x_279 = l_List_toArrayAux___main___rarg(x_276, x_278);
x_280 = x_279;
x_281 = lean_unsigned_to_nat(0u);
lean_inc(x_275);
lean_inc(x_7);
lean_inc(x_1);
x_282 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_282, 0, x_1);
lean_closure_set(x_282, 1, x_7);
lean_closure_set(x_282, 2, x_10);
lean_closure_set(x_282, 3, x_12);
lean_closure_set(x_282, 4, x_275);
lean_closure_set(x_282, 5, x_276);
lean_closure_set(x_282, 6, x_281);
lean_closure_set(x_282, 7, x_280);
x_283 = x_282;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_284 = lean_apply_5(x_283, x_14, x_15, x_16, x_17, x_274);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
lean_inc(x_1);
x_287 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_286);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_290 == 0)
{
lean_object* x_369; uint8_t x_370; 
x_369 = l_Lean_MetavarContext_exprDependsOn(x_275, x_288, x_2);
x_370 = lean_unbox(x_369);
lean_dec(x_369);
if (x_370 == 0)
{
x_291 = x_289;
goto block_368;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; 
lean_dec(x_285);
lean_dec(x_269);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_371 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_371, 0, x_3);
x_372 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_373 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_371);
x_374 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_375 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_374);
x_376 = lean_box(0);
x_377 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_375, x_376, x_14, x_15, x_16, x_17, x_289);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_378 = !lean_is_exclusive(x_377);
if (x_378 == 0)
{
return x_377;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_377, 0);
x_380 = lean_ctor_get(x_377, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_377);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
return x_381;
}
}
}
else
{
lean_dec(x_288);
lean_dec(x_275);
x_291 = x_289;
goto block_368;
}
block_368:
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; 
lean_inc(x_285);
x_292 = x_285;
x_293 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_281, x_292);
x_294 = x_293;
x_295 = lean_array_push(x_294, x_2);
x_296 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_297 = l_Lean_Meta_revert(x_1, x_295, x_296, x_14, x_15, x_16, x_17, x_291);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; lean_object* x_305; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = lean_ctor_get(x_298, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
x_302 = lean_array_get_size(x_285);
x_303 = lean_box(0);
x_304 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_305 = l_Lean_Meta_introN(x_301, x_302, x_303, x_304, x_14, x_15, x_16, x_17, x_299);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
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
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_310 = l_Lean_Meta_intro1(x_309, x_304, x_14, x_15, x_16, x_17, x_307);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_337; lean_object* x_338; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = lean_ctor_get(x_311, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_311, 1);
lean_inc(x_314);
lean_dec(x_311);
x_315 = lean_box(0);
x_316 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_285, x_308, x_285, x_281, x_315);
lean_dec(x_285);
x_346 = l_Lean_Core_getTraceState___rarg(x_17, x_312);
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get_uint8(x_347, sizeof(void*)*1);
lean_dec(x_347);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_346, 1);
lean_inc(x_349);
lean_dec(x_346);
x_337 = x_304;
x_338 = x_349;
goto block_345;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; 
x_350 = lean_ctor_get(x_346, 1);
lean_inc(x_350);
lean_dec(x_346);
x_351 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_352 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_351, x_16, x_17, x_350);
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_355 = lean_unbox(x_353);
lean_dec(x_353);
x_337 = x_355;
x_338 = x_354;
goto block_345;
}
block_336:
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_318 = x_308;
x_319 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_281, x_318);
x_320 = x_319;
lean_inc(x_313);
x_321 = l_Lean_mkFVar(x_313);
lean_inc(x_314);
x_322 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_322, 0, x_314);
x_323 = lean_box(x_290);
lean_inc(x_314);
x_324 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_324, 0, x_313);
lean_closure_set(x_324, 1, x_9);
lean_closure_set(x_324, 2, x_314);
lean_closure_set(x_324, 3, x_3);
lean_closure_set(x_324, 4, x_4);
lean_closure_set(x_324, 5, x_7);
lean_closure_set(x_324, 6, x_8);
lean_closure_set(x_324, 7, x_269);
lean_closure_set(x_324, 8, x_323);
lean_closure_set(x_324, 9, x_300);
lean_closure_set(x_324, 10, x_316);
lean_closure_set(x_324, 11, x_320);
lean_closure_set(x_324, 12, x_321);
x_325 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_325, 0, x_322);
lean_closure_set(x_325, 1, x_324);
x_326 = l_Lean_Meta_getMVarDecl(x_314, x_14, x_15, x_16, x_17, x_317);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec(x_326);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
x_330 = lean_ctor_get(x_327, 4);
lean_inc(x_330);
lean_dec(x_327);
x_331 = l_Lean_Meta_withLocalContext___rarg(x_329, x_330, x_325, x_14, x_15, x_16, x_17, x_328);
lean_dec(x_14);
return x_331;
}
else
{
uint8_t x_332; 
lean_dec(x_325);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_332 = !lean_is_exclusive(x_326);
if (x_332 == 0)
{
return x_326;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_326, 0);
x_334 = lean_ctor_get(x_326, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_326);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
return x_335;
}
}
}
block_345:
{
if (x_337 == 0)
{
x_317 = x_338;
goto block_336;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_inc(x_314);
x_339 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_339, 0, x_314);
x_340 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_341 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_339);
x_342 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_343 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_342, x_341, x_14, x_15, x_16, x_17, x_338);
x_344 = lean_ctor_get(x_343, 1);
lean_inc(x_344);
lean_dec(x_343);
x_317 = x_344;
goto block_336;
}
}
}
else
{
uint8_t x_356; 
lean_dec(x_308);
lean_dec(x_300);
lean_dec(x_285);
lean_dec(x_269);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_356 = !lean_is_exclusive(x_310);
if (x_356 == 0)
{
return x_310;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = lean_ctor_get(x_310, 0);
x_358 = lean_ctor_get(x_310, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_310);
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
lean_dec(x_300);
lean_dec(x_285);
lean_dec(x_269);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_360 = !lean_is_exclusive(x_305);
if (x_360 == 0)
{
return x_305;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_305, 0);
x_362 = lean_ctor_get(x_305, 1);
lean_inc(x_362);
lean_inc(x_361);
lean_dec(x_305);
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
lean_dec(x_285);
lean_dec(x_269);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_364 = !lean_is_exclusive(x_297);
if (x_364 == 0)
{
return x_297;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_297, 0);
x_366 = lean_ctor_get(x_297, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_297);
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
uint8_t x_382; 
lean_dec(x_285);
lean_dec(x_275);
lean_dec(x_269);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_382 = !lean_is_exclusive(x_287);
if (x_382 == 0)
{
return x_287;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_287, 0);
x_384 = lean_ctor_get(x_287, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_287);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
return x_385;
}
}
}
else
{
uint8_t x_386; 
lean_dec(x_275);
lean_dec(x_269);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_386 = !lean_is_exclusive(x_284);
if (x_386 == 0)
{
return x_284;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_284, 0);
x_388 = lean_ctor_get(x_284, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_284);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
}
else
{
uint8_t x_390; 
lean_dec(x_269);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_390 = !lean_is_exclusive(x_270);
if (x_390 == 0)
{
return x_270;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_270, 0);
x_392 = lean_ctor_get(x_270, 1);
lean_inc(x_392);
lean_inc(x_391);
lean_dec(x_270);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
return x_393;
}
}
}
case 3:
{
lean_object* x_394; lean_object* x_395; 
lean_dec(x_13);
lean_dec(x_11);
x_394 = lean_ctor_get(x_8, 5);
lean_inc(x_394);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_395 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_7, x_10, x_12, x_394, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_396 = lean_ctor_get(x_395, 1);
lean_inc(x_396);
lean_dec(x_395);
x_397 = lean_io_ref_get(x_15, x_396);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
lean_dec(x_397);
x_400 = lean_ctor_get(x_398, 0);
lean_inc(x_400);
lean_dec(x_398);
x_401 = lean_ctor_get(x_8, 6);
lean_inc(x_401);
x_402 = l_List_redLength___main___rarg(x_401);
x_403 = lean_mk_empty_array_with_capacity(x_402);
lean_dec(x_402);
lean_inc(x_401);
x_404 = l_List_toArrayAux___main___rarg(x_401, x_403);
x_405 = x_404;
x_406 = lean_unsigned_to_nat(0u);
lean_inc(x_400);
lean_inc(x_7);
lean_inc(x_1);
x_407 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_407, 0, x_1);
lean_closure_set(x_407, 1, x_7);
lean_closure_set(x_407, 2, x_10);
lean_closure_set(x_407, 3, x_12);
lean_closure_set(x_407, 4, x_400);
lean_closure_set(x_407, 5, x_401);
lean_closure_set(x_407, 6, x_406);
lean_closure_set(x_407, 7, x_405);
x_408 = x_407;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_409 = lean_apply_5(x_408, x_14, x_15, x_16, x_17, x_399);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
lean_inc(x_1);
x_412 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_411);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec(x_412);
x_415 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_415 == 0)
{
lean_object* x_494; uint8_t x_495; 
x_494 = l_Lean_MetavarContext_exprDependsOn(x_400, x_413, x_2);
x_495 = lean_unbox(x_494);
lean_dec(x_494);
if (x_495 == 0)
{
x_416 = x_414;
goto block_493;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; 
lean_dec(x_410);
lean_dec(x_394);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_496 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_496, 0, x_3);
x_497 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_498 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_496);
x_499 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_500 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_499);
x_501 = lean_box(0);
x_502 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_500, x_501, x_14, x_15, x_16, x_17, x_414);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
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
lean_dec(x_413);
lean_dec(x_400);
x_416 = x_414;
goto block_493;
}
block_493:
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; 
lean_inc(x_410);
x_417 = x_410;
x_418 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_406, x_417);
x_419 = x_418;
x_420 = lean_array_push(x_419, x_2);
x_421 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_422 = l_Lean_Meta_revert(x_1, x_420, x_421, x_14, x_15, x_16, x_17, x_416);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
lean_dec(x_422);
x_425 = lean_ctor_get(x_423, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_423, 1);
lean_inc(x_426);
lean_dec(x_423);
x_427 = lean_array_get_size(x_410);
x_428 = lean_box(0);
x_429 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_430 = l_Lean_Meta_introN(x_426, x_427, x_428, x_429, x_14, x_15, x_16, x_17, x_424);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
lean_dec(x_430);
x_433 = lean_ctor_get(x_431, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_431, 1);
lean_inc(x_434);
lean_dec(x_431);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_435 = l_Lean_Meta_intro1(x_434, x_429, x_14, x_15, x_16, x_17, x_432);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_462; lean_object* x_463; lean_object* x_471; lean_object* x_472; uint8_t x_473; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
lean_dec(x_435);
x_438 = lean_ctor_get(x_436, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_436, 1);
lean_inc(x_439);
lean_dec(x_436);
x_440 = lean_box(0);
x_441 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_410, x_433, x_410, x_406, x_440);
lean_dec(x_410);
x_471 = l_Lean_Core_getTraceState___rarg(x_17, x_437);
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
x_473 = lean_ctor_get_uint8(x_472, sizeof(void*)*1);
lean_dec(x_472);
if (x_473 == 0)
{
lean_object* x_474; 
x_474 = lean_ctor_get(x_471, 1);
lean_inc(x_474);
lean_dec(x_471);
x_462 = x_429;
x_463 = x_474;
goto block_470;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; 
x_475 = lean_ctor_get(x_471, 1);
lean_inc(x_475);
lean_dec(x_471);
x_476 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_477 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_476, x_16, x_17, x_475);
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_477, 1);
lean_inc(x_479);
lean_dec(x_477);
x_480 = lean_unbox(x_478);
lean_dec(x_478);
x_462 = x_480;
x_463 = x_479;
goto block_470;
}
block_461:
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_443 = x_433;
x_444 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_406, x_443);
x_445 = x_444;
lean_inc(x_438);
x_446 = l_Lean_mkFVar(x_438);
lean_inc(x_439);
x_447 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_447, 0, x_439);
x_448 = lean_box(x_415);
lean_inc(x_439);
x_449 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_449, 0, x_438);
lean_closure_set(x_449, 1, x_9);
lean_closure_set(x_449, 2, x_439);
lean_closure_set(x_449, 3, x_3);
lean_closure_set(x_449, 4, x_4);
lean_closure_set(x_449, 5, x_7);
lean_closure_set(x_449, 6, x_8);
lean_closure_set(x_449, 7, x_394);
lean_closure_set(x_449, 8, x_448);
lean_closure_set(x_449, 9, x_425);
lean_closure_set(x_449, 10, x_441);
lean_closure_set(x_449, 11, x_445);
lean_closure_set(x_449, 12, x_446);
x_450 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_450, 0, x_447);
lean_closure_set(x_450, 1, x_449);
x_451 = l_Lean_Meta_getMVarDecl(x_439, x_14, x_15, x_16, x_17, x_442);
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
x_456 = l_Lean_Meta_withLocalContext___rarg(x_454, x_455, x_450, x_14, x_15, x_16, x_17, x_453);
lean_dec(x_14);
return x_456;
}
else
{
uint8_t x_457; 
lean_dec(x_450);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
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
block_470:
{
if (x_462 == 0)
{
x_442 = x_463;
goto block_461;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_inc(x_439);
x_464 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_464, 0, x_439);
x_465 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_466 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_464);
x_467 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_468 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_467, x_466, x_14, x_15, x_16, x_17, x_463);
x_469 = lean_ctor_get(x_468, 1);
lean_inc(x_469);
lean_dec(x_468);
x_442 = x_469;
goto block_461;
}
}
}
else
{
uint8_t x_481; 
lean_dec(x_433);
lean_dec(x_425);
lean_dec(x_410);
lean_dec(x_394);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_481 = !lean_is_exclusive(x_435);
if (x_481 == 0)
{
return x_435;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_435, 0);
x_483 = lean_ctor_get(x_435, 1);
lean_inc(x_483);
lean_inc(x_482);
lean_dec(x_435);
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
lean_dec(x_425);
lean_dec(x_410);
lean_dec(x_394);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_485 = !lean_is_exclusive(x_430);
if (x_485 == 0)
{
return x_430;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_486 = lean_ctor_get(x_430, 0);
x_487 = lean_ctor_get(x_430, 1);
lean_inc(x_487);
lean_inc(x_486);
lean_dec(x_430);
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
lean_dec(x_410);
lean_dec(x_394);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_489 = !lean_is_exclusive(x_422);
if (x_489 == 0)
{
return x_422;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_490 = lean_ctor_get(x_422, 0);
x_491 = lean_ctor_get(x_422, 1);
lean_inc(x_491);
lean_inc(x_490);
lean_dec(x_422);
x_492 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_491);
return x_492;
}
}
}
}
else
{
uint8_t x_507; 
lean_dec(x_410);
lean_dec(x_400);
lean_dec(x_394);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_507 = !lean_is_exclusive(x_412);
if (x_507 == 0)
{
return x_412;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_508 = lean_ctor_get(x_412, 0);
x_509 = lean_ctor_get(x_412, 1);
lean_inc(x_509);
lean_inc(x_508);
lean_dec(x_412);
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
lean_dec(x_400);
lean_dec(x_394);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_511 = !lean_is_exclusive(x_409);
if (x_511 == 0)
{
return x_409;
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_512 = lean_ctor_get(x_409, 0);
x_513 = lean_ctor_get(x_409, 1);
lean_inc(x_513);
lean_inc(x_512);
lean_dec(x_409);
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
lean_dec(x_394);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_515 = !lean_is_exclusive(x_395);
if (x_515 == 0)
{
return x_395;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_516 = lean_ctor_get(x_395, 0);
x_517 = lean_ctor_get(x_395, 1);
lean_inc(x_517);
lean_inc(x_516);
lean_dec(x_395);
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
lean_dec(x_13);
lean_dec(x_11);
x_519 = lean_ctor_get(x_8, 5);
lean_inc(x_519);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_520 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_7, x_10, x_12, x_519, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_521 = lean_ctor_get(x_520, 1);
lean_inc(x_521);
lean_dec(x_520);
x_522 = lean_io_ref_get(x_15, x_521);
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
lean_dec(x_522);
x_525 = lean_ctor_get(x_523, 0);
lean_inc(x_525);
lean_dec(x_523);
x_526 = lean_ctor_get(x_8, 6);
lean_inc(x_526);
x_527 = l_List_redLength___main___rarg(x_526);
x_528 = lean_mk_empty_array_with_capacity(x_527);
lean_dec(x_527);
lean_inc(x_526);
x_529 = l_List_toArrayAux___main___rarg(x_526, x_528);
x_530 = x_529;
x_531 = lean_unsigned_to_nat(0u);
lean_inc(x_525);
lean_inc(x_7);
lean_inc(x_1);
x_532 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_532, 0, x_1);
lean_closure_set(x_532, 1, x_7);
lean_closure_set(x_532, 2, x_10);
lean_closure_set(x_532, 3, x_12);
lean_closure_set(x_532, 4, x_525);
lean_closure_set(x_532, 5, x_526);
lean_closure_set(x_532, 6, x_531);
lean_closure_set(x_532, 7, x_530);
x_533 = x_532;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_534 = lean_apply_5(x_533, x_14, x_15, x_16, x_17, x_524);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
lean_dec(x_534);
lean_inc(x_1);
x_537 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_536);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; lean_object* x_539; uint8_t x_540; lean_object* x_541; 
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_537, 1);
lean_inc(x_539);
lean_dec(x_537);
x_540 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_540 == 0)
{
lean_object* x_619; uint8_t x_620; 
x_619 = l_Lean_MetavarContext_exprDependsOn(x_525, x_538, x_2);
x_620 = lean_unbox(x_619);
lean_dec(x_619);
if (x_620 == 0)
{
x_541 = x_539;
goto block_618;
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; uint8_t x_628; 
lean_dec(x_535);
lean_dec(x_519);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_621 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_621, 0, x_3);
x_622 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_623 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_623, 0, x_622);
lean_ctor_set(x_623, 1, x_621);
x_624 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_625 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_625, 0, x_623);
lean_ctor_set(x_625, 1, x_624);
x_626 = lean_box(0);
x_627 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_625, x_626, x_14, x_15, x_16, x_17, x_539);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_628 = !lean_is_exclusive(x_627);
if (x_628 == 0)
{
return x_627;
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_629 = lean_ctor_get(x_627, 0);
x_630 = lean_ctor_get(x_627, 1);
lean_inc(x_630);
lean_inc(x_629);
lean_dec(x_627);
x_631 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_631, 0, x_629);
lean_ctor_set(x_631, 1, x_630);
return x_631;
}
}
}
else
{
lean_dec(x_538);
lean_dec(x_525);
x_541 = x_539;
goto block_618;
}
block_618:
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; uint8_t x_546; lean_object* x_547; 
lean_inc(x_535);
x_542 = x_535;
x_543 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_531, x_542);
x_544 = x_543;
x_545 = lean_array_push(x_544, x_2);
x_546 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_547 = l_Lean_Meta_revert(x_1, x_545, x_546, x_14, x_15, x_16, x_17, x_541);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; uint8_t x_554; lean_object* x_555; 
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_547, 1);
lean_inc(x_549);
lean_dec(x_547);
x_550 = lean_ctor_get(x_548, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_548, 1);
lean_inc(x_551);
lean_dec(x_548);
x_552 = lean_array_get_size(x_535);
x_553 = lean_box(0);
x_554 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_555 = l_Lean_Meta_introN(x_551, x_552, x_553, x_554, x_14, x_15, x_16, x_17, x_549);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
lean_dec(x_555);
x_558 = lean_ctor_get(x_556, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_556, 1);
lean_inc(x_559);
lean_dec(x_556);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_560 = l_Lean_Meta_intro1(x_559, x_554, x_14, x_15, x_16, x_17, x_557);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; uint8_t x_587; lean_object* x_588; lean_object* x_596; lean_object* x_597; uint8_t x_598; 
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_560, 1);
lean_inc(x_562);
lean_dec(x_560);
x_563 = lean_ctor_get(x_561, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_561, 1);
lean_inc(x_564);
lean_dec(x_561);
x_565 = lean_box(0);
x_566 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_535, x_558, x_535, x_531, x_565);
lean_dec(x_535);
x_596 = l_Lean_Core_getTraceState___rarg(x_17, x_562);
x_597 = lean_ctor_get(x_596, 0);
lean_inc(x_597);
x_598 = lean_ctor_get_uint8(x_597, sizeof(void*)*1);
lean_dec(x_597);
if (x_598 == 0)
{
lean_object* x_599; 
x_599 = lean_ctor_get(x_596, 1);
lean_inc(x_599);
lean_dec(x_596);
x_587 = x_554;
x_588 = x_599;
goto block_595;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; uint8_t x_605; 
x_600 = lean_ctor_get(x_596, 1);
lean_inc(x_600);
lean_dec(x_596);
x_601 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_602 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_601, x_16, x_17, x_600);
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
lean_dec(x_602);
x_605 = lean_unbox(x_603);
lean_dec(x_603);
x_587 = x_605;
x_588 = x_604;
goto block_595;
}
block_586:
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_568 = x_558;
x_569 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_531, x_568);
x_570 = x_569;
lean_inc(x_563);
x_571 = l_Lean_mkFVar(x_563);
lean_inc(x_564);
x_572 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_572, 0, x_564);
x_573 = lean_box(x_540);
lean_inc(x_564);
x_574 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_574, 0, x_563);
lean_closure_set(x_574, 1, x_9);
lean_closure_set(x_574, 2, x_564);
lean_closure_set(x_574, 3, x_3);
lean_closure_set(x_574, 4, x_4);
lean_closure_set(x_574, 5, x_7);
lean_closure_set(x_574, 6, x_8);
lean_closure_set(x_574, 7, x_519);
lean_closure_set(x_574, 8, x_573);
lean_closure_set(x_574, 9, x_550);
lean_closure_set(x_574, 10, x_566);
lean_closure_set(x_574, 11, x_570);
lean_closure_set(x_574, 12, x_571);
x_575 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_575, 0, x_572);
lean_closure_set(x_575, 1, x_574);
x_576 = l_Lean_Meta_getMVarDecl(x_564, x_14, x_15, x_16, x_17, x_567);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
lean_dec(x_576);
x_579 = lean_ctor_get(x_577, 1);
lean_inc(x_579);
x_580 = lean_ctor_get(x_577, 4);
lean_inc(x_580);
lean_dec(x_577);
x_581 = l_Lean_Meta_withLocalContext___rarg(x_579, x_580, x_575, x_14, x_15, x_16, x_17, x_578);
lean_dec(x_14);
return x_581;
}
else
{
uint8_t x_582; 
lean_dec(x_575);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_582 = !lean_is_exclusive(x_576);
if (x_582 == 0)
{
return x_576;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_576, 0);
x_584 = lean_ctor_get(x_576, 1);
lean_inc(x_584);
lean_inc(x_583);
lean_dec(x_576);
x_585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set(x_585, 1, x_584);
return x_585;
}
}
}
block_595:
{
if (x_587 == 0)
{
x_567 = x_588;
goto block_586;
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
lean_inc(x_564);
x_589 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_589, 0, x_564);
x_590 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_591 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_589);
x_592 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_593 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_592, x_591, x_14, x_15, x_16, x_17, x_588);
x_594 = lean_ctor_get(x_593, 1);
lean_inc(x_594);
lean_dec(x_593);
x_567 = x_594;
goto block_586;
}
}
}
else
{
uint8_t x_606; 
lean_dec(x_558);
lean_dec(x_550);
lean_dec(x_535);
lean_dec(x_519);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_606 = !lean_is_exclusive(x_560);
if (x_606 == 0)
{
return x_560;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_607 = lean_ctor_get(x_560, 0);
x_608 = lean_ctor_get(x_560, 1);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_560);
x_609 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_609, 0, x_607);
lean_ctor_set(x_609, 1, x_608);
return x_609;
}
}
}
else
{
uint8_t x_610; 
lean_dec(x_550);
lean_dec(x_535);
lean_dec(x_519);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_610 = !lean_is_exclusive(x_555);
if (x_610 == 0)
{
return x_555;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_611 = lean_ctor_get(x_555, 0);
x_612 = lean_ctor_get(x_555, 1);
lean_inc(x_612);
lean_inc(x_611);
lean_dec(x_555);
x_613 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_613, 0, x_611);
lean_ctor_set(x_613, 1, x_612);
return x_613;
}
}
}
else
{
uint8_t x_614; 
lean_dec(x_535);
lean_dec(x_519);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_614 = !lean_is_exclusive(x_547);
if (x_614 == 0)
{
return x_547;
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_615 = lean_ctor_get(x_547, 0);
x_616 = lean_ctor_get(x_547, 1);
lean_inc(x_616);
lean_inc(x_615);
lean_dec(x_547);
x_617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_617, 0, x_615);
lean_ctor_set(x_617, 1, x_616);
return x_617;
}
}
}
}
else
{
uint8_t x_632; 
lean_dec(x_535);
lean_dec(x_525);
lean_dec(x_519);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_632 = !lean_is_exclusive(x_537);
if (x_632 == 0)
{
return x_537;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_633 = lean_ctor_get(x_537, 0);
x_634 = lean_ctor_get(x_537, 1);
lean_inc(x_634);
lean_inc(x_633);
lean_dec(x_537);
x_635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set(x_635, 1, x_634);
return x_635;
}
}
}
else
{
uint8_t x_636; 
lean_dec(x_525);
lean_dec(x_519);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_636 = !lean_is_exclusive(x_534);
if (x_636 == 0)
{
return x_534;
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_637 = lean_ctor_get(x_534, 0);
x_638 = lean_ctor_get(x_534, 1);
lean_inc(x_638);
lean_inc(x_637);
lean_dec(x_534);
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_637);
lean_ctor_set(x_639, 1, x_638);
return x_639;
}
}
}
else
{
uint8_t x_640; 
lean_dec(x_519);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_640 = !lean_is_exclusive(x_520);
if (x_640 == 0)
{
return x_520;
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_641 = lean_ctor_get(x_520, 0);
x_642 = lean_ctor_get(x_520, 1);
lean_inc(x_642);
lean_inc(x_641);
lean_dec(x_520);
x_643 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_643, 0, x_641);
lean_ctor_set(x_643, 1, x_642);
return x_643;
}
}
}
case 5:
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_644 = lean_ctor_get(x_11, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_11, 1);
lean_inc(x_645);
lean_dec(x_11);
x_646 = lean_array_set(x_12, x_13, x_645);
x_647 = lean_unsigned_to_nat(1u);
x_648 = lean_nat_sub(x_13, x_647);
lean_dec(x_13);
x_11 = x_644;
x_12 = x_646;
x_13 = x_648;
goto _start;
}
case 6:
{
lean_object* x_650; lean_object* x_651; 
lean_dec(x_13);
lean_dec(x_11);
x_650 = lean_ctor_get(x_8, 5);
lean_inc(x_650);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_651 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_7, x_10, x_12, x_650, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_652 = lean_ctor_get(x_651, 1);
lean_inc(x_652);
lean_dec(x_651);
x_653 = lean_io_ref_get(x_15, x_652);
x_654 = lean_ctor_get(x_653, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_653, 1);
lean_inc(x_655);
lean_dec(x_653);
x_656 = lean_ctor_get(x_654, 0);
lean_inc(x_656);
lean_dec(x_654);
x_657 = lean_ctor_get(x_8, 6);
lean_inc(x_657);
x_658 = l_List_redLength___main___rarg(x_657);
x_659 = lean_mk_empty_array_with_capacity(x_658);
lean_dec(x_658);
lean_inc(x_657);
x_660 = l_List_toArrayAux___main___rarg(x_657, x_659);
x_661 = x_660;
x_662 = lean_unsigned_to_nat(0u);
lean_inc(x_656);
lean_inc(x_7);
lean_inc(x_1);
x_663 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_663, 0, x_1);
lean_closure_set(x_663, 1, x_7);
lean_closure_set(x_663, 2, x_10);
lean_closure_set(x_663, 3, x_12);
lean_closure_set(x_663, 4, x_656);
lean_closure_set(x_663, 5, x_657);
lean_closure_set(x_663, 6, x_662);
lean_closure_set(x_663, 7, x_661);
x_664 = x_663;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_665 = lean_apply_5(x_664, x_14, x_15, x_16, x_17, x_655);
if (lean_obj_tag(x_665) == 0)
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_666 = lean_ctor_get(x_665, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_665, 1);
lean_inc(x_667);
lean_dec(x_665);
lean_inc(x_1);
x_668 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_667);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; lean_object* x_670; uint8_t x_671; lean_object* x_672; 
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_668, 1);
lean_inc(x_670);
lean_dec(x_668);
x_671 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_671 == 0)
{
lean_object* x_750; uint8_t x_751; 
x_750 = l_Lean_MetavarContext_exprDependsOn(x_656, x_669, x_2);
x_751 = lean_unbox(x_750);
lean_dec(x_750);
if (x_751 == 0)
{
x_672 = x_670;
goto block_749;
}
else
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; uint8_t x_759; 
lean_dec(x_666);
lean_dec(x_650);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_752 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_752, 0, x_3);
x_753 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_754 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_754, 0, x_753);
lean_ctor_set(x_754, 1, x_752);
x_755 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_756 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_756, 0, x_754);
lean_ctor_set(x_756, 1, x_755);
x_757 = lean_box(0);
x_758 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_756, x_757, x_14, x_15, x_16, x_17, x_670);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_759 = !lean_is_exclusive(x_758);
if (x_759 == 0)
{
return x_758;
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; 
x_760 = lean_ctor_get(x_758, 0);
x_761 = lean_ctor_get(x_758, 1);
lean_inc(x_761);
lean_inc(x_760);
lean_dec(x_758);
x_762 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_762, 0, x_760);
lean_ctor_set(x_762, 1, x_761);
return x_762;
}
}
}
else
{
lean_dec(x_669);
lean_dec(x_656);
x_672 = x_670;
goto block_749;
}
block_749:
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; uint8_t x_677; lean_object* x_678; 
lean_inc(x_666);
x_673 = x_666;
x_674 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_662, x_673);
x_675 = x_674;
x_676 = lean_array_push(x_675, x_2);
x_677 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_678 = l_Lean_Meta_revert(x_1, x_676, x_677, x_14, x_15, x_16, x_17, x_672);
if (lean_obj_tag(x_678) == 0)
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; uint8_t x_685; lean_object* x_686; 
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_678, 1);
lean_inc(x_680);
lean_dec(x_678);
x_681 = lean_ctor_get(x_679, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_679, 1);
lean_inc(x_682);
lean_dec(x_679);
x_683 = lean_array_get_size(x_666);
x_684 = lean_box(0);
x_685 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_686 = l_Lean_Meta_introN(x_682, x_683, x_684, x_685, x_14, x_15, x_16, x_17, x_680);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_686, 1);
lean_inc(x_688);
lean_dec(x_686);
x_689 = lean_ctor_get(x_687, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_687, 1);
lean_inc(x_690);
lean_dec(x_687);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_691 = l_Lean_Meta_intro1(x_690, x_685, x_14, x_15, x_16, x_17, x_688);
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; uint8_t x_718; lean_object* x_719; lean_object* x_727; lean_object* x_728; uint8_t x_729; 
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
x_696 = lean_box(0);
x_697 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_666, x_689, x_666, x_662, x_696);
lean_dec(x_666);
x_727 = l_Lean_Core_getTraceState___rarg(x_17, x_693);
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
x_729 = lean_ctor_get_uint8(x_728, sizeof(void*)*1);
lean_dec(x_728);
if (x_729 == 0)
{
lean_object* x_730; 
x_730 = lean_ctor_get(x_727, 1);
lean_inc(x_730);
lean_dec(x_727);
x_718 = x_685;
x_719 = x_730;
goto block_726;
}
else
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; uint8_t x_736; 
x_731 = lean_ctor_get(x_727, 1);
lean_inc(x_731);
lean_dec(x_727);
x_732 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_733 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_732, x_16, x_17, x_731);
x_734 = lean_ctor_get(x_733, 0);
lean_inc(x_734);
x_735 = lean_ctor_get(x_733, 1);
lean_inc(x_735);
lean_dec(x_733);
x_736 = lean_unbox(x_734);
lean_dec(x_734);
x_718 = x_736;
x_719 = x_735;
goto block_726;
}
block_717:
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_699 = x_689;
x_700 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_662, x_699);
x_701 = x_700;
lean_inc(x_694);
x_702 = l_Lean_mkFVar(x_694);
lean_inc(x_695);
x_703 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_703, 0, x_695);
x_704 = lean_box(x_671);
lean_inc(x_695);
x_705 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_705, 0, x_694);
lean_closure_set(x_705, 1, x_9);
lean_closure_set(x_705, 2, x_695);
lean_closure_set(x_705, 3, x_3);
lean_closure_set(x_705, 4, x_4);
lean_closure_set(x_705, 5, x_7);
lean_closure_set(x_705, 6, x_8);
lean_closure_set(x_705, 7, x_650);
lean_closure_set(x_705, 8, x_704);
lean_closure_set(x_705, 9, x_681);
lean_closure_set(x_705, 10, x_697);
lean_closure_set(x_705, 11, x_701);
lean_closure_set(x_705, 12, x_702);
x_706 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_706, 0, x_703);
lean_closure_set(x_706, 1, x_705);
x_707 = l_Lean_Meta_getMVarDecl(x_695, x_14, x_15, x_16, x_17, x_698);
if (lean_obj_tag(x_707) == 0)
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
x_708 = lean_ctor_get(x_707, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_707, 1);
lean_inc(x_709);
lean_dec(x_707);
x_710 = lean_ctor_get(x_708, 1);
lean_inc(x_710);
x_711 = lean_ctor_get(x_708, 4);
lean_inc(x_711);
lean_dec(x_708);
x_712 = l_Lean_Meta_withLocalContext___rarg(x_710, x_711, x_706, x_14, x_15, x_16, x_17, x_709);
lean_dec(x_14);
return x_712;
}
else
{
uint8_t x_713; 
lean_dec(x_706);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_713 = !lean_is_exclusive(x_707);
if (x_713 == 0)
{
return x_707;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_714 = lean_ctor_get(x_707, 0);
x_715 = lean_ctor_get(x_707, 1);
lean_inc(x_715);
lean_inc(x_714);
lean_dec(x_707);
x_716 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_716, 0, x_714);
lean_ctor_set(x_716, 1, x_715);
return x_716;
}
}
}
block_726:
{
if (x_718 == 0)
{
x_698 = x_719;
goto block_717;
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
lean_inc(x_695);
x_720 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_720, 0, x_695);
x_721 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_722 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_722, 0, x_721);
lean_ctor_set(x_722, 1, x_720);
x_723 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_724 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_723, x_722, x_14, x_15, x_16, x_17, x_719);
x_725 = lean_ctor_get(x_724, 1);
lean_inc(x_725);
lean_dec(x_724);
x_698 = x_725;
goto block_717;
}
}
}
else
{
uint8_t x_737; 
lean_dec(x_689);
lean_dec(x_681);
lean_dec(x_666);
lean_dec(x_650);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_737 = !lean_is_exclusive(x_691);
if (x_737 == 0)
{
return x_691;
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_738 = lean_ctor_get(x_691, 0);
x_739 = lean_ctor_get(x_691, 1);
lean_inc(x_739);
lean_inc(x_738);
lean_dec(x_691);
x_740 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_740, 0, x_738);
lean_ctor_set(x_740, 1, x_739);
return x_740;
}
}
}
else
{
uint8_t x_741; 
lean_dec(x_681);
lean_dec(x_666);
lean_dec(x_650);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_741 = !lean_is_exclusive(x_686);
if (x_741 == 0)
{
return x_686;
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_742 = lean_ctor_get(x_686, 0);
x_743 = lean_ctor_get(x_686, 1);
lean_inc(x_743);
lean_inc(x_742);
lean_dec(x_686);
x_744 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_744, 0, x_742);
lean_ctor_set(x_744, 1, x_743);
return x_744;
}
}
}
else
{
uint8_t x_745; 
lean_dec(x_666);
lean_dec(x_650);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_745 = !lean_is_exclusive(x_678);
if (x_745 == 0)
{
return x_678;
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_746 = lean_ctor_get(x_678, 0);
x_747 = lean_ctor_get(x_678, 1);
lean_inc(x_747);
lean_inc(x_746);
lean_dec(x_678);
x_748 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_748, 0, x_746);
lean_ctor_set(x_748, 1, x_747);
return x_748;
}
}
}
}
else
{
uint8_t x_763; 
lean_dec(x_666);
lean_dec(x_656);
lean_dec(x_650);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_763 = !lean_is_exclusive(x_668);
if (x_763 == 0)
{
return x_668;
}
else
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_764 = lean_ctor_get(x_668, 0);
x_765 = lean_ctor_get(x_668, 1);
lean_inc(x_765);
lean_inc(x_764);
lean_dec(x_668);
x_766 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_766, 0, x_764);
lean_ctor_set(x_766, 1, x_765);
return x_766;
}
}
}
else
{
uint8_t x_767; 
lean_dec(x_656);
lean_dec(x_650);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_767 = !lean_is_exclusive(x_665);
if (x_767 == 0)
{
return x_665;
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; 
x_768 = lean_ctor_get(x_665, 0);
x_769 = lean_ctor_get(x_665, 1);
lean_inc(x_769);
lean_inc(x_768);
lean_dec(x_665);
x_770 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_770, 0, x_768);
lean_ctor_set(x_770, 1, x_769);
return x_770;
}
}
}
else
{
uint8_t x_771; 
lean_dec(x_650);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_771 = !lean_is_exclusive(x_651);
if (x_771 == 0)
{
return x_651;
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_772 = lean_ctor_get(x_651, 0);
x_773 = lean_ctor_get(x_651, 1);
lean_inc(x_773);
lean_inc(x_772);
lean_dec(x_651);
x_774 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_774, 0, x_772);
lean_ctor_set(x_774, 1, x_773);
return x_774;
}
}
}
case 7:
{
lean_object* x_775; lean_object* x_776; 
lean_dec(x_13);
lean_dec(x_11);
x_775 = lean_ctor_get(x_8, 5);
lean_inc(x_775);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_776 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_7, x_10, x_12, x_775, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_776) == 0)
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_777 = lean_ctor_get(x_776, 1);
lean_inc(x_777);
lean_dec(x_776);
x_778 = lean_io_ref_get(x_15, x_777);
x_779 = lean_ctor_get(x_778, 0);
lean_inc(x_779);
x_780 = lean_ctor_get(x_778, 1);
lean_inc(x_780);
lean_dec(x_778);
x_781 = lean_ctor_get(x_779, 0);
lean_inc(x_781);
lean_dec(x_779);
x_782 = lean_ctor_get(x_8, 6);
lean_inc(x_782);
x_783 = l_List_redLength___main___rarg(x_782);
x_784 = lean_mk_empty_array_with_capacity(x_783);
lean_dec(x_783);
lean_inc(x_782);
x_785 = l_List_toArrayAux___main___rarg(x_782, x_784);
x_786 = x_785;
x_787 = lean_unsigned_to_nat(0u);
lean_inc(x_781);
lean_inc(x_7);
lean_inc(x_1);
x_788 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_788, 0, x_1);
lean_closure_set(x_788, 1, x_7);
lean_closure_set(x_788, 2, x_10);
lean_closure_set(x_788, 3, x_12);
lean_closure_set(x_788, 4, x_781);
lean_closure_set(x_788, 5, x_782);
lean_closure_set(x_788, 6, x_787);
lean_closure_set(x_788, 7, x_786);
x_789 = x_788;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_790 = lean_apply_5(x_789, x_14, x_15, x_16, x_17, x_780);
if (lean_obj_tag(x_790) == 0)
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_791 = lean_ctor_get(x_790, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_790, 1);
lean_inc(x_792);
lean_dec(x_790);
lean_inc(x_1);
x_793 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_792);
if (lean_obj_tag(x_793) == 0)
{
lean_object* x_794; lean_object* x_795; uint8_t x_796; lean_object* x_797; 
x_794 = lean_ctor_get(x_793, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_793, 1);
lean_inc(x_795);
lean_dec(x_793);
x_796 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_796 == 0)
{
lean_object* x_875; uint8_t x_876; 
x_875 = l_Lean_MetavarContext_exprDependsOn(x_781, x_794, x_2);
x_876 = lean_unbox(x_875);
lean_dec(x_875);
if (x_876 == 0)
{
x_797 = x_795;
goto block_874;
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; uint8_t x_884; 
lean_dec(x_791);
lean_dec(x_775);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_877 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_877, 0, x_3);
x_878 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_879 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_879, 0, x_878);
lean_ctor_set(x_879, 1, x_877);
x_880 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_881 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_881, 0, x_879);
lean_ctor_set(x_881, 1, x_880);
x_882 = lean_box(0);
x_883 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_881, x_882, x_14, x_15, x_16, x_17, x_795);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_884 = !lean_is_exclusive(x_883);
if (x_884 == 0)
{
return x_883;
}
else
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; 
x_885 = lean_ctor_get(x_883, 0);
x_886 = lean_ctor_get(x_883, 1);
lean_inc(x_886);
lean_inc(x_885);
lean_dec(x_883);
x_887 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_887, 0, x_885);
lean_ctor_set(x_887, 1, x_886);
return x_887;
}
}
}
else
{
lean_dec(x_794);
lean_dec(x_781);
x_797 = x_795;
goto block_874;
}
block_874:
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; uint8_t x_802; lean_object* x_803; 
lean_inc(x_791);
x_798 = x_791;
x_799 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_787, x_798);
x_800 = x_799;
x_801 = lean_array_push(x_800, x_2);
x_802 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_803 = l_Lean_Meta_revert(x_1, x_801, x_802, x_14, x_15, x_16, x_17, x_797);
if (lean_obj_tag(x_803) == 0)
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; uint8_t x_810; lean_object* x_811; 
x_804 = lean_ctor_get(x_803, 0);
lean_inc(x_804);
x_805 = lean_ctor_get(x_803, 1);
lean_inc(x_805);
lean_dec(x_803);
x_806 = lean_ctor_get(x_804, 0);
lean_inc(x_806);
x_807 = lean_ctor_get(x_804, 1);
lean_inc(x_807);
lean_dec(x_804);
x_808 = lean_array_get_size(x_791);
x_809 = lean_box(0);
x_810 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_811 = l_Lean_Meta_introN(x_807, x_808, x_809, x_810, x_14, x_15, x_16, x_17, x_805);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_811, 1);
lean_inc(x_813);
lean_dec(x_811);
x_814 = lean_ctor_get(x_812, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_812, 1);
lean_inc(x_815);
lean_dec(x_812);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_816 = l_Lean_Meta_intro1(x_815, x_810, x_14, x_15, x_16, x_17, x_813);
if (lean_obj_tag(x_816) == 0)
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; uint8_t x_843; lean_object* x_844; lean_object* x_852; lean_object* x_853; uint8_t x_854; 
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
x_821 = lean_box(0);
x_822 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_791, x_814, x_791, x_787, x_821);
lean_dec(x_791);
x_852 = l_Lean_Core_getTraceState___rarg(x_17, x_818);
x_853 = lean_ctor_get(x_852, 0);
lean_inc(x_853);
x_854 = lean_ctor_get_uint8(x_853, sizeof(void*)*1);
lean_dec(x_853);
if (x_854 == 0)
{
lean_object* x_855; 
x_855 = lean_ctor_get(x_852, 1);
lean_inc(x_855);
lean_dec(x_852);
x_843 = x_810;
x_844 = x_855;
goto block_851;
}
else
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; uint8_t x_861; 
x_856 = lean_ctor_get(x_852, 1);
lean_inc(x_856);
lean_dec(x_852);
x_857 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_858 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_857, x_16, x_17, x_856);
x_859 = lean_ctor_get(x_858, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_858, 1);
lean_inc(x_860);
lean_dec(x_858);
x_861 = lean_unbox(x_859);
lean_dec(x_859);
x_843 = x_861;
x_844 = x_860;
goto block_851;
}
block_842:
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
x_824 = x_814;
x_825 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_787, x_824);
x_826 = x_825;
lean_inc(x_819);
x_827 = l_Lean_mkFVar(x_819);
lean_inc(x_820);
x_828 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_828, 0, x_820);
x_829 = lean_box(x_796);
lean_inc(x_820);
x_830 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_830, 0, x_819);
lean_closure_set(x_830, 1, x_9);
lean_closure_set(x_830, 2, x_820);
lean_closure_set(x_830, 3, x_3);
lean_closure_set(x_830, 4, x_4);
lean_closure_set(x_830, 5, x_7);
lean_closure_set(x_830, 6, x_8);
lean_closure_set(x_830, 7, x_775);
lean_closure_set(x_830, 8, x_829);
lean_closure_set(x_830, 9, x_806);
lean_closure_set(x_830, 10, x_822);
lean_closure_set(x_830, 11, x_826);
lean_closure_set(x_830, 12, x_827);
x_831 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_831, 0, x_828);
lean_closure_set(x_831, 1, x_830);
x_832 = l_Lean_Meta_getMVarDecl(x_820, x_14, x_15, x_16, x_17, x_823);
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
x_837 = l_Lean_Meta_withLocalContext___rarg(x_835, x_836, x_831, x_14, x_15, x_16, x_17, x_834);
lean_dec(x_14);
return x_837;
}
else
{
uint8_t x_838; 
lean_dec(x_831);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
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
block_851:
{
if (x_843 == 0)
{
x_823 = x_844;
goto block_842;
}
else
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; 
lean_inc(x_820);
x_845 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_845, 0, x_820);
x_846 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_847 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_847, 0, x_846);
lean_ctor_set(x_847, 1, x_845);
x_848 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_849 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_848, x_847, x_14, x_15, x_16, x_17, x_844);
x_850 = lean_ctor_get(x_849, 1);
lean_inc(x_850);
lean_dec(x_849);
x_823 = x_850;
goto block_842;
}
}
}
else
{
uint8_t x_862; 
lean_dec(x_814);
lean_dec(x_806);
lean_dec(x_791);
lean_dec(x_775);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_862 = !lean_is_exclusive(x_816);
if (x_862 == 0)
{
return x_816;
}
else
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; 
x_863 = lean_ctor_get(x_816, 0);
x_864 = lean_ctor_get(x_816, 1);
lean_inc(x_864);
lean_inc(x_863);
lean_dec(x_816);
x_865 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_865, 0, x_863);
lean_ctor_set(x_865, 1, x_864);
return x_865;
}
}
}
else
{
uint8_t x_866; 
lean_dec(x_806);
lean_dec(x_791);
lean_dec(x_775);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_866 = !lean_is_exclusive(x_811);
if (x_866 == 0)
{
return x_811;
}
else
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; 
x_867 = lean_ctor_get(x_811, 0);
x_868 = lean_ctor_get(x_811, 1);
lean_inc(x_868);
lean_inc(x_867);
lean_dec(x_811);
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
lean_dec(x_791);
lean_dec(x_775);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_870 = !lean_is_exclusive(x_803);
if (x_870 == 0)
{
return x_803;
}
else
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; 
x_871 = lean_ctor_get(x_803, 0);
x_872 = lean_ctor_get(x_803, 1);
lean_inc(x_872);
lean_inc(x_871);
lean_dec(x_803);
x_873 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_873, 0, x_871);
lean_ctor_set(x_873, 1, x_872);
return x_873;
}
}
}
}
else
{
uint8_t x_888; 
lean_dec(x_791);
lean_dec(x_781);
lean_dec(x_775);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_888 = !lean_is_exclusive(x_793);
if (x_888 == 0)
{
return x_793;
}
else
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; 
x_889 = lean_ctor_get(x_793, 0);
x_890 = lean_ctor_get(x_793, 1);
lean_inc(x_890);
lean_inc(x_889);
lean_dec(x_793);
x_891 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_891, 0, x_889);
lean_ctor_set(x_891, 1, x_890);
return x_891;
}
}
}
else
{
uint8_t x_892; 
lean_dec(x_781);
lean_dec(x_775);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_892 = !lean_is_exclusive(x_790);
if (x_892 == 0)
{
return x_790;
}
else
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; 
x_893 = lean_ctor_get(x_790, 0);
x_894 = lean_ctor_get(x_790, 1);
lean_inc(x_894);
lean_inc(x_893);
lean_dec(x_790);
x_895 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_895, 0, x_893);
lean_ctor_set(x_895, 1, x_894);
return x_895;
}
}
}
else
{
uint8_t x_896; 
lean_dec(x_775);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_896 = !lean_is_exclusive(x_776);
if (x_896 == 0)
{
return x_776;
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; 
x_897 = lean_ctor_get(x_776, 0);
x_898 = lean_ctor_get(x_776, 1);
lean_inc(x_898);
lean_inc(x_897);
lean_dec(x_776);
x_899 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_899, 0, x_897);
lean_ctor_set(x_899, 1, x_898);
return x_899;
}
}
}
case 8:
{
lean_object* x_900; lean_object* x_901; 
lean_dec(x_13);
lean_dec(x_11);
x_900 = lean_ctor_get(x_8, 5);
lean_inc(x_900);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_901 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_7, x_10, x_12, x_900, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_901) == 0)
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; 
x_902 = lean_ctor_get(x_901, 1);
lean_inc(x_902);
lean_dec(x_901);
x_903 = lean_io_ref_get(x_15, x_902);
x_904 = lean_ctor_get(x_903, 0);
lean_inc(x_904);
x_905 = lean_ctor_get(x_903, 1);
lean_inc(x_905);
lean_dec(x_903);
x_906 = lean_ctor_get(x_904, 0);
lean_inc(x_906);
lean_dec(x_904);
x_907 = lean_ctor_get(x_8, 6);
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
lean_inc(x_1);
x_913 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_913, 0, x_1);
lean_closure_set(x_913, 1, x_7);
lean_closure_set(x_913, 2, x_10);
lean_closure_set(x_913, 3, x_12);
lean_closure_set(x_913, 4, x_906);
lean_closure_set(x_913, 5, x_907);
lean_closure_set(x_913, 6, x_912);
lean_closure_set(x_913, 7, x_911);
x_914 = x_913;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_915 = lean_apply_5(x_914, x_14, x_15, x_16, x_17, x_905);
if (lean_obj_tag(x_915) == 0)
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_916 = lean_ctor_get(x_915, 0);
lean_inc(x_916);
x_917 = lean_ctor_get(x_915, 1);
lean_inc(x_917);
lean_dec(x_915);
lean_inc(x_1);
x_918 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_917);
if (lean_obj_tag(x_918) == 0)
{
lean_object* x_919; lean_object* x_920; uint8_t x_921; lean_object* x_922; 
x_919 = lean_ctor_get(x_918, 0);
lean_inc(x_919);
x_920 = lean_ctor_get(x_918, 1);
lean_inc(x_920);
lean_dec(x_918);
x_921 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_921 == 0)
{
lean_object* x_1000; uint8_t x_1001; 
x_1000 = l_Lean_MetavarContext_exprDependsOn(x_906, x_919, x_2);
x_1001 = lean_unbox(x_1000);
lean_dec(x_1000);
if (x_1001 == 0)
{
x_922 = x_920;
goto block_999;
}
else
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; uint8_t x_1009; 
lean_dec(x_916);
lean_dec(x_900);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_1002 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1002, 0, x_3);
x_1003 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1004 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1004, 0, x_1003);
lean_ctor_set(x_1004, 1, x_1002);
x_1005 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_1006 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1006, 0, x_1004);
lean_ctor_set(x_1006, 1, x_1005);
x_1007 = lean_box(0);
x_1008 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_1006, x_1007, x_14, x_15, x_16, x_17, x_920);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1009 = !lean_is_exclusive(x_1008);
if (x_1009 == 0)
{
return x_1008;
}
else
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1010 = lean_ctor_get(x_1008, 0);
x_1011 = lean_ctor_get(x_1008, 1);
lean_inc(x_1011);
lean_inc(x_1010);
lean_dec(x_1008);
x_1012 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1012, 0, x_1010);
lean_ctor_set(x_1012, 1, x_1011);
return x_1012;
}
}
}
else
{
lean_dec(x_919);
lean_dec(x_906);
x_922 = x_920;
goto block_999;
}
block_999:
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; uint8_t x_927; lean_object* x_928; 
lean_inc(x_916);
x_923 = x_916;
x_924 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_912, x_923);
x_925 = x_924;
x_926 = lean_array_push(x_925, x_2);
x_927 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_928 = l_Lean_Meta_revert(x_1, x_926, x_927, x_14, x_15, x_16, x_17, x_922);
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
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_936 = l_Lean_Meta_introN(x_932, x_933, x_934, x_935, x_14, x_15, x_16, x_17, x_930);
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
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_941 = l_Lean_Meta_intro1(x_940, x_935, x_14, x_15, x_16, x_17, x_938);
if (lean_obj_tag(x_941) == 0)
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; uint8_t x_968; lean_object* x_969; lean_object* x_977; lean_object* x_978; uint8_t x_979; 
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
x_947 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_916, x_939, x_916, x_912, x_946);
lean_dec(x_916);
x_977 = l_Lean_Core_getTraceState___rarg(x_17, x_943);
x_978 = lean_ctor_get(x_977, 0);
lean_inc(x_978);
x_979 = lean_ctor_get_uint8(x_978, sizeof(void*)*1);
lean_dec(x_978);
if (x_979 == 0)
{
lean_object* x_980; 
x_980 = lean_ctor_get(x_977, 1);
lean_inc(x_980);
lean_dec(x_977);
x_968 = x_935;
x_969 = x_980;
goto block_976;
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; uint8_t x_986; 
x_981 = lean_ctor_get(x_977, 1);
lean_inc(x_981);
lean_dec(x_977);
x_982 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_983 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_982, x_16, x_17, x_981);
x_984 = lean_ctor_get(x_983, 0);
lean_inc(x_984);
x_985 = lean_ctor_get(x_983, 1);
lean_inc(x_985);
lean_dec(x_983);
x_986 = lean_unbox(x_984);
lean_dec(x_984);
x_968 = x_986;
x_969 = x_985;
goto block_976;
}
block_967:
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; 
x_949 = x_939;
x_950 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_912, x_949);
x_951 = x_950;
lean_inc(x_944);
x_952 = l_Lean_mkFVar(x_944);
lean_inc(x_945);
x_953 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_953, 0, x_945);
x_954 = lean_box(x_921);
lean_inc(x_945);
x_955 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_955, 0, x_944);
lean_closure_set(x_955, 1, x_9);
lean_closure_set(x_955, 2, x_945);
lean_closure_set(x_955, 3, x_3);
lean_closure_set(x_955, 4, x_4);
lean_closure_set(x_955, 5, x_7);
lean_closure_set(x_955, 6, x_8);
lean_closure_set(x_955, 7, x_900);
lean_closure_set(x_955, 8, x_954);
lean_closure_set(x_955, 9, x_931);
lean_closure_set(x_955, 10, x_947);
lean_closure_set(x_955, 11, x_951);
lean_closure_set(x_955, 12, x_952);
x_956 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_956, 0, x_953);
lean_closure_set(x_956, 1, x_955);
x_957 = l_Lean_Meta_getMVarDecl(x_945, x_14, x_15, x_16, x_17, x_948);
if (lean_obj_tag(x_957) == 0)
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; 
x_958 = lean_ctor_get(x_957, 0);
lean_inc(x_958);
x_959 = lean_ctor_get(x_957, 1);
lean_inc(x_959);
lean_dec(x_957);
x_960 = lean_ctor_get(x_958, 1);
lean_inc(x_960);
x_961 = lean_ctor_get(x_958, 4);
lean_inc(x_961);
lean_dec(x_958);
x_962 = l_Lean_Meta_withLocalContext___rarg(x_960, x_961, x_956, x_14, x_15, x_16, x_17, x_959);
lean_dec(x_14);
return x_962;
}
else
{
uint8_t x_963; 
lean_dec(x_956);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_963 = !lean_is_exclusive(x_957);
if (x_963 == 0)
{
return x_957;
}
else
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; 
x_964 = lean_ctor_get(x_957, 0);
x_965 = lean_ctor_get(x_957, 1);
lean_inc(x_965);
lean_inc(x_964);
lean_dec(x_957);
x_966 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_966, 0, x_964);
lean_ctor_set(x_966, 1, x_965);
return x_966;
}
}
}
block_976:
{
if (x_968 == 0)
{
x_948 = x_969;
goto block_967;
}
else
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; 
lean_inc(x_945);
x_970 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_970, 0, x_945);
x_971 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_972 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_972, 0, x_971);
lean_ctor_set(x_972, 1, x_970);
x_973 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_974 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_973, x_972, x_14, x_15, x_16, x_17, x_969);
x_975 = lean_ctor_get(x_974, 1);
lean_inc(x_975);
lean_dec(x_974);
x_948 = x_975;
goto block_967;
}
}
}
else
{
uint8_t x_987; 
lean_dec(x_939);
lean_dec(x_931);
lean_dec(x_916);
lean_dec(x_900);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_987 = !lean_is_exclusive(x_941);
if (x_987 == 0)
{
return x_941;
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; 
x_988 = lean_ctor_get(x_941, 0);
x_989 = lean_ctor_get(x_941, 1);
lean_inc(x_989);
lean_inc(x_988);
lean_dec(x_941);
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
lean_dec(x_931);
lean_dec(x_916);
lean_dec(x_900);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_991 = !lean_is_exclusive(x_936);
if (x_991 == 0)
{
return x_936;
}
else
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; 
x_992 = lean_ctor_get(x_936, 0);
x_993 = lean_ctor_get(x_936, 1);
lean_inc(x_993);
lean_inc(x_992);
lean_dec(x_936);
x_994 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_994, 0, x_992);
lean_ctor_set(x_994, 1, x_993);
return x_994;
}
}
}
else
{
uint8_t x_995; 
lean_dec(x_916);
lean_dec(x_900);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_995 = !lean_is_exclusive(x_928);
if (x_995 == 0)
{
return x_928;
}
else
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; 
x_996 = lean_ctor_get(x_928, 0);
x_997 = lean_ctor_get(x_928, 1);
lean_inc(x_997);
lean_inc(x_996);
lean_dec(x_928);
x_998 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_998, 0, x_996);
lean_ctor_set(x_998, 1, x_997);
return x_998;
}
}
}
}
else
{
uint8_t x_1013; 
lean_dec(x_916);
lean_dec(x_906);
lean_dec(x_900);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1013 = !lean_is_exclusive(x_918);
if (x_1013 == 0)
{
return x_918;
}
else
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
x_1014 = lean_ctor_get(x_918, 0);
x_1015 = lean_ctor_get(x_918, 1);
lean_inc(x_1015);
lean_inc(x_1014);
lean_dec(x_918);
x_1016 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1016, 0, x_1014);
lean_ctor_set(x_1016, 1, x_1015);
return x_1016;
}
}
}
else
{
uint8_t x_1017; 
lean_dec(x_906);
lean_dec(x_900);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1017 = !lean_is_exclusive(x_915);
if (x_1017 == 0)
{
return x_915;
}
else
{
lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
x_1018 = lean_ctor_get(x_915, 0);
x_1019 = lean_ctor_get(x_915, 1);
lean_inc(x_1019);
lean_inc(x_1018);
lean_dec(x_915);
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
lean_dec(x_900);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1021 = !lean_is_exclusive(x_901);
if (x_1021 == 0)
{
return x_901;
}
else
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; 
x_1022 = lean_ctor_get(x_901, 0);
x_1023 = lean_ctor_get(x_901, 1);
lean_inc(x_1023);
lean_inc(x_1022);
lean_dec(x_901);
x_1024 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1024, 0, x_1022);
lean_ctor_set(x_1024, 1, x_1023);
return x_1024;
}
}
}
case 9:
{
lean_object* x_1025; lean_object* x_1026; 
lean_dec(x_13);
lean_dec(x_11);
x_1025 = lean_ctor_get(x_8, 5);
lean_inc(x_1025);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_1026 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_7, x_10, x_12, x_1025, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_1026) == 0)
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
x_1027 = lean_ctor_get(x_1026, 1);
lean_inc(x_1027);
lean_dec(x_1026);
x_1028 = lean_io_ref_get(x_15, x_1027);
x_1029 = lean_ctor_get(x_1028, 0);
lean_inc(x_1029);
x_1030 = lean_ctor_get(x_1028, 1);
lean_inc(x_1030);
lean_dec(x_1028);
x_1031 = lean_ctor_get(x_1029, 0);
lean_inc(x_1031);
lean_dec(x_1029);
x_1032 = lean_ctor_get(x_8, 6);
lean_inc(x_1032);
x_1033 = l_List_redLength___main___rarg(x_1032);
x_1034 = lean_mk_empty_array_with_capacity(x_1033);
lean_dec(x_1033);
lean_inc(x_1032);
x_1035 = l_List_toArrayAux___main___rarg(x_1032, x_1034);
x_1036 = x_1035;
x_1037 = lean_unsigned_to_nat(0u);
lean_inc(x_1031);
lean_inc(x_7);
lean_inc(x_1);
x_1038 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_1038, 0, x_1);
lean_closure_set(x_1038, 1, x_7);
lean_closure_set(x_1038, 2, x_10);
lean_closure_set(x_1038, 3, x_12);
lean_closure_set(x_1038, 4, x_1031);
lean_closure_set(x_1038, 5, x_1032);
lean_closure_set(x_1038, 6, x_1037);
lean_closure_set(x_1038, 7, x_1036);
x_1039 = x_1038;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1040 = lean_apply_5(x_1039, x_14, x_15, x_16, x_17, x_1030);
if (lean_obj_tag(x_1040) == 0)
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
x_1041 = lean_ctor_get(x_1040, 0);
lean_inc(x_1041);
x_1042 = lean_ctor_get(x_1040, 1);
lean_inc(x_1042);
lean_dec(x_1040);
lean_inc(x_1);
x_1043 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_1042);
if (lean_obj_tag(x_1043) == 0)
{
lean_object* x_1044; lean_object* x_1045; uint8_t x_1046; lean_object* x_1047; 
x_1044 = lean_ctor_get(x_1043, 0);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_1043, 1);
lean_inc(x_1045);
lean_dec(x_1043);
x_1046 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_1046 == 0)
{
lean_object* x_1125; uint8_t x_1126; 
x_1125 = l_Lean_MetavarContext_exprDependsOn(x_1031, x_1044, x_2);
x_1126 = lean_unbox(x_1125);
lean_dec(x_1125);
if (x_1126 == 0)
{
x_1047 = x_1045;
goto block_1124;
}
else
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; uint8_t x_1134; 
lean_dec(x_1041);
lean_dec(x_1025);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_1127 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1127, 0, x_3);
x_1128 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1129 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1129, 0, x_1128);
lean_ctor_set(x_1129, 1, x_1127);
x_1130 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_1131 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1131, 0, x_1129);
lean_ctor_set(x_1131, 1, x_1130);
x_1132 = lean_box(0);
x_1133 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_1131, x_1132, x_14, x_15, x_16, x_17, x_1045);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1134 = !lean_is_exclusive(x_1133);
if (x_1134 == 0)
{
return x_1133;
}
else
{
lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; 
x_1135 = lean_ctor_get(x_1133, 0);
x_1136 = lean_ctor_get(x_1133, 1);
lean_inc(x_1136);
lean_inc(x_1135);
lean_dec(x_1133);
x_1137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1137, 0, x_1135);
lean_ctor_set(x_1137, 1, x_1136);
return x_1137;
}
}
}
else
{
lean_dec(x_1044);
lean_dec(x_1031);
x_1047 = x_1045;
goto block_1124;
}
block_1124:
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; uint8_t x_1052; lean_object* x_1053; 
lean_inc(x_1041);
x_1048 = x_1041;
x_1049 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1037, x_1048);
x_1050 = x_1049;
x_1051 = lean_array_push(x_1050, x_2);
x_1052 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1053 = l_Lean_Meta_revert(x_1, x_1051, x_1052, x_14, x_15, x_16, x_17, x_1047);
if (lean_obj_tag(x_1053) == 0)
{
lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; uint8_t x_1060; lean_object* x_1061; 
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
x_1058 = lean_array_get_size(x_1041);
x_1059 = lean_box(0);
x_1060 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1061 = l_Lean_Meta_introN(x_1057, x_1058, x_1059, x_1060, x_14, x_15, x_16, x_17, x_1055);
if (lean_obj_tag(x_1061) == 0)
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; 
x_1062 = lean_ctor_get(x_1061, 0);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_1061, 1);
lean_inc(x_1063);
lean_dec(x_1061);
x_1064 = lean_ctor_get(x_1062, 0);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_1062, 1);
lean_inc(x_1065);
lean_dec(x_1062);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1066 = l_Lean_Meta_intro1(x_1065, x_1060, x_14, x_15, x_16, x_17, x_1063);
if (lean_obj_tag(x_1066) == 0)
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; uint8_t x_1093; lean_object* x_1094; lean_object* x_1102; lean_object* x_1103; uint8_t x_1104; 
x_1067 = lean_ctor_get(x_1066, 0);
lean_inc(x_1067);
x_1068 = lean_ctor_get(x_1066, 1);
lean_inc(x_1068);
lean_dec(x_1066);
x_1069 = lean_ctor_get(x_1067, 0);
lean_inc(x_1069);
x_1070 = lean_ctor_get(x_1067, 1);
lean_inc(x_1070);
lean_dec(x_1067);
x_1071 = lean_box(0);
x_1072 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_1041, x_1064, x_1041, x_1037, x_1071);
lean_dec(x_1041);
x_1102 = l_Lean_Core_getTraceState___rarg(x_17, x_1068);
x_1103 = lean_ctor_get(x_1102, 0);
lean_inc(x_1103);
x_1104 = lean_ctor_get_uint8(x_1103, sizeof(void*)*1);
lean_dec(x_1103);
if (x_1104 == 0)
{
lean_object* x_1105; 
x_1105 = lean_ctor_get(x_1102, 1);
lean_inc(x_1105);
lean_dec(x_1102);
x_1093 = x_1060;
x_1094 = x_1105;
goto block_1101;
}
else
{
lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; uint8_t x_1111; 
x_1106 = lean_ctor_get(x_1102, 1);
lean_inc(x_1106);
lean_dec(x_1102);
x_1107 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1108 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1107, x_16, x_17, x_1106);
x_1109 = lean_ctor_get(x_1108, 0);
lean_inc(x_1109);
x_1110 = lean_ctor_get(x_1108, 1);
lean_inc(x_1110);
lean_dec(x_1108);
x_1111 = lean_unbox(x_1109);
lean_dec(x_1109);
x_1093 = x_1111;
x_1094 = x_1110;
goto block_1101;
}
block_1092:
{
lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; 
x_1074 = x_1064;
x_1075 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1037, x_1074);
x_1076 = x_1075;
lean_inc(x_1069);
x_1077 = l_Lean_mkFVar(x_1069);
lean_inc(x_1070);
x_1078 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1078, 0, x_1070);
x_1079 = lean_box(x_1046);
lean_inc(x_1070);
x_1080 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_1080, 0, x_1069);
lean_closure_set(x_1080, 1, x_9);
lean_closure_set(x_1080, 2, x_1070);
lean_closure_set(x_1080, 3, x_3);
lean_closure_set(x_1080, 4, x_4);
lean_closure_set(x_1080, 5, x_7);
lean_closure_set(x_1080, 6, x_8);
lean_closure_set(x_1080, 7, x_1025);
lean_closure_set(x_1080, 8, x_1079);
lean_closure_set(x_1080, 9, x_1056);
lean_closure_set(x_1080, 10, x_1072);
lean_closure_set(x_1080, 11, x_1076);
lean_closure_set(x_1080, 12, x_1077);
x_1081 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_1081, 0, x_1078);
lean_closure_set(x_1081, 1, x_1080);
x_1082 = l_Lean_Meta_getMVarDecl(x_1070, x_14, x_15, x_16, x_17, x_1073);
if (lean_obj_tag(x_1082) == 0)
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
x_1083 = lean_ctor_get(x_1082, 0);
lean_inc(x_1083);
x_1084 = lean_ctor_get(x_1082, 1);
lean_inc(x_1084);
lean_dec(x_1082);
x_1085 = lean_ctor_get(x_1083, 1);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1083, 4);
lean_inc(x_1086);
lean_dec(x_1083);
x_1087 = l_Lean_Meta_withLocalContext___rarg(x_1085, x_1086, x_1081, x_14, x_15, x_16, x_17, x_1084);
lean_dec(x_14);
return x_1087;
}
else
{
uint8_t x_1088; 
lean_dec(x_1081);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1088 = !lean_is_exclusive(x_1082);
if (x_1088 == 0)
{
return x_1082;
}
else
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; 
x_1089 = lean_ctor_get(x_1082, 0);
x_1090 = lean_ctor_get(x_1082, 1);
lean_inc(x_1090);
lean_inc(x_1089);
lean_dec(x_1082);
x_1091 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1091, 0, x_1089);
lean_ctor_set(x_1091, 1, x_1090);
return x_1091;
}
}
}
block_1101:
{
if (x_1093 == 0)
{
x_1073 = x_1094;
goto block_1092;
}
else
{
lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
lean_inc(x_1070);
x_1095 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1095, 0, x_1070);
x_1096 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_1097 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1097, 0, x_1096);
lean_ctor_set(x_1097, 1, x_1095);
x_1098 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1099 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1098, x_1097, x_14, x_15, x_16, x_17, x_1094);
x_1100 = lean_ctor_get(x_1099, 1);
lean_inc(x_1100);
lean_dec(x_1099);
x_1073 = x_1100;
goto block_1092;
}
}
}
else
{
uint8_t x_1112; 
lean_dec(x_1064);
lean_dec(x_1056);
lean_dec(x_1041);
lean_dec(x_1025);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1112 = !lean_is_exclusive(x_1066);
if (x_1112 == 0)
{
return x_1066;
}
else
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
x_1113 = lean_ctor_get(x_1066, 0);
x_1114 = lean_ctor_get(x_1066, 1);
lean_inc(x_1114);
lean_inc(x_1113);
lean_dec(x_1066);
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
lean_dec(x_1056);
lean_dec(x_1041);
lean_dec(x_1025);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1116 = !lean_is_exclusive(x_1061);
if (x_1116 == 0)
{
return x_1061;
}
else
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; 
x_1117 = lean_ctor_get(x_1061, 0);
x_1118 = lean_ctor_get(x_1061, 1);
lean_inc(x_1118);
lean_inc(x_1117);
lean_dec(x_1061);
x_1119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1119, 0, x_1117);
lean_ctor_set(x_1119, 1, x_1118);
return x_1119;
}
}
}
else
{
uint8_t x_1120; 
lean_dec(x_1041);
lean_dec(x_1025);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1120 = !lean_is_exclusive(x_1053);
if (x_1120 == 0)
{
return x_1053;
}
else
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
x_1121 = lean_ctor_get(x_1053, 0);
x_1122 = lean_ctor_get(x_1053, 1);
lean_inc(x_1122);
lean_inc(x_1121);
lean_dec(x_1053);
x_1123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1123, 0, x_1121);
lean_ctor_set(x_1123, 1, x_1122);
return x_1123;
}
}
}
}
else
{
uint8_t x_1138; 
lean_dec(x_1041);
lean_dec(x_1031);
lean_dec(x_1025);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1138 = !lean_is_exclusive(x_1043);
if (x_1138 == 0)
{
return x_1043;
}
else
{
lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; 
x_1139 = lean_ctor_get(x_1043, 0);
x_1140 = lean_ctor_get(x_1043, 1);
lean_inc(x_1140);
lean_inc(x_1139);
lean_dec(x_1043);
x_1141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1141, 0, x_1139);
lean_ctor_set(x_1141, 1, x_1140);
return x_1141;
}
}
}
else
{
uint8_t x_1142; 
lean_dec(x_1031);
lean_dec(x_1025);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1142 = !lean_is_exclusive(x_1040);
if (x_1142 == 0)
{
return x_1040;
}
else
{
lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; 
x_1143 = lean_ctor_get(x_1040, 0);
x_1144 = lean_ctor_get(x_1040, 1);
lean_inc(x_1144);
lean_inc(x_1143);
lean_dec(x_1040);
x_1145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1145, 0, x_1143);
lean_ctor_set(x_1145, 1, x_1144);
return x_1145;
}
}
}
else
{
uint8_t x_1146; 
lean_dec(x_1025);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1146 = !lean_is_exclusive(x_1026);
if (x_1146 == 0)
{
return x_1026;
}
else
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; 
x_1147 = lean_ctor_get(x_1026, 0);
x_1148 = lean_ctor_get(x_1026, 1);
lean_inc(x_1148);
lean_inc(x_1147);
lean_dec(x_1026);
x_1149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1149, 0, x_1147);
lean_ctor_set(x_1149, 1, x_1148);
return x_1149;
}
}
}
case 10:
{
lean_object* x_1150; lean_object* x_1151; 
lean_dec(x_13);
lean_dec(x_11);
x_1150 = lean_ctor_get(x_8, 5);
lean_inc(x_1150);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_1151 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_7, x_10, x_12, x_1150, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_1151) == 0)
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; 
x_1152 = lean_ctor_get(x_1151, 1);
lean_inc(x_1152);
lean_dec(x_1151);
x_1153 = lean_io_ref_get(x_15, x_1152);
x_1154 = lean_ctor_get(x_1153, 0);
lean_inc(x_1154);
x_1155 = lean_ctor_get(x_1153, 1);
lean_inc(x_1155);
lean_dec(x_1153);
x_1156 = lean_ctor_get(x_1154, 0);
lean_inc(x_1156);
lean_dec(x_1154);
x_1157 = lean_ctor_get(x_8, 6);
lean_inc(x_1157);
x_1158 = l_List_redLength___main___rarg(x_1157);
x_1159 = lean_mk_empty_array_with_capacity(x_1158);
lean_dec(x_1158);
lean_inc(x_1157);
x_1160 = l_List_toArrayAux___main___rarg(x_1157, x_1159);
x_1161 = x_1160;
x_1162 = lean_unsigned_to_nat(0u);
lean_inc(x_1156);
lean_inc(x_7);
lean_inc(x_1);
x_1163 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_1163, 0, x_1);
lean_closure_set(x_1163, 1, x_7);
lean_closure_set(x_1163, 2, x_10);
lean_closure_set(x_1163, 3, x_12);
lean_closure_set(x_1163, 4, x_1156);
lean_closure_set(x_1163, 5, x_1157);
lean_closure_set(x_1163, 6, x_1162);
lean_closure_set(x_1163, 7, x_1161);
x_1164 = x_1163;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1165 = lean_apply_5(x_1164, x_14, x_15, x_16, x_17, x_1155);
if (lean_obj_tag(x_1165) == 0)
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; 
x_1166 = lean_ctor_get(x_1165, 0);
lean_inc(x_1166);
x_1167 = lean_ctor_get(x_1165, 1);
lean_inc(x_1167);
lean_dec(x_1165);
lean_inc(x_1);
x_1168 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_1167);
if (lean_obj_tag(x_1168) == 0)
{
lean_object* x_1169; lean_object* x_1170; uint8_t x_1171; lean_object* x_1172; 
x_1169 = lean_ctor_get(x_1168, 0);
lean_inc(x_1169);
x_1170 = lean_ctor_get(x_1168, 1);
lean_inc(x_1170);
lean_dec(x_1168);
x_1171 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_1171 == 0)
{
lean_object* x_1250; uint8_t x_1251; 
x_1250 = l_Lean_MetavarContext_exprDependsOn(x_1156, x_1169, x_2);
x_1251 = lean_unbox(x_1250);
lean_dec(x_1250);
if (x_1251 == 0)
{
x_1172 = x_1170;
goto block_1249;
}
else
{
lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; uint8_t x_1259; 
lean_dec(x_1166);
lean_dec(x_1150);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_1252 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1252, 0, x_3);
x_1253 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1254 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1254, 0, x_1253);
lean_ctor_set(x_1254, 1, x_1252);
x_1255 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_1256 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1256, 0, x_1254);
lean_ctor_set(x_1256, 1, x_1255);
x_1257 = lean_box(0);
x_1258 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_1256, x_1257, x_14, x_15, x_16, x_17, x_1170);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1259 = !lean_is_exclusive(x_1258);
if (x_1259 == 0)
{
return x_1258;
}
else
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; 
x_1260 = lean_ctor_get(x_1258, 0);
x_1261 = lean_ctor_get(x_1258, 1);
lean_inc(x_1261);
lean_inc(x_1260);
lean_dec(x_1258);
x_1262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1262, 0, x_1260);
lean_ctor_set(x_1262, 1, x_1261);
return x_1262;
}
}
}
else
{
lean_dec(x_1169);
lean_dec(x_1156);
x_1172 = x_1170;
goto block_1249;
}
block_1249:
{
lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; uint8_t x_1177; lean_object* x_1178; 
lean_inc(x_1166);
x_1173 = x_1166;
x_1174 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1162, x_1173);
x_1175 = x_1174;
x_1176 = lean_array_push(x_1175, x_2);
x_1177 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1178 = l_Lean_Meta_revert(x_1, x_1176, x_1177, x_14, x_15, x_16, x_17, x_1172);
if (lean_obj_tag(x_1178) == 0)
{
lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; uint8_t x_1185; lean_object* x_1186; 
x_1179 = lean_ctor_get(x_1178, 0);
lean_inc(x_1179);
x_1180 = lean_ctor_get(x_1178, 1);
lean_inc(x_1180);
lean_dec(x_1178);
x_1181 = lean_ctor_get(x_1179, 0);
lean_inc(x_1181);
x_1182 = lean_ctor_get(x_1179, 1);
lean_inc(x_1182);
lean_dec(x_1179);
x_1183 = lean_array_get_size(x_1166);
x_1184 = lean_box(0);
x_1185 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1186 = l_Lean_Meta_introN(x_1182, x_1183, x_1184, x_1185, x_14, x_15, x_16, x_17, x_1180);
if (lean_obj_tag(x_1186) == 0)
{
lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; 
x_1187 = lean_ctor_get(x_1186, 0);
lean_inc(x_1187);
x_1188 = lean_ctor_get(x_1186, 1);
lean_inc(x_1188);
lean_dec(x_1186);
x_1189 = lean_ctor_get(x_1187, 0);
lean_inc(x_1189);
x_1190 = lean_ctor_get(x_1187, 1);
lean_inc(x_1190);
lean_dec(x_1187);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1191 = l_Lean_Meta_intro1(x_1190, x_1185, x_14, x_15, x_16, x_17, x_1188);
if (lean_obj_tag(x_1191) == 0)
{
lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; uint8_t x_1218; lean_object* x_1219; lean_object* x_1227; lean_object* x_1228; uint8_t x_1229; 
x_1192 = lean_ctor_get(x_1191, 0);
lean_inc(x_1192);
x_1193 = lean_ctor_get(x_1191, 1);
lean_inc(x_1193);
lean_dec(x_1191);
x_1194 = lean_ctor_get(x_1192, 0);
lean_inc(x_1194);
x_1195 = lean_ctor_get(x_1192, 1);
lean_inc(x_1195);
lean_dec(x_1192);
x_1196 = lean_box(0);
x_1197 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_1166, x_1189, x_1166, x_1162, x_1196);
lean_dec(x_1166);
x_1227 = l_Lean_Core_getTraceState___rarg(x_17, x_1193);
x_1228 = lean_ctor_get(x_1227, 0);
lean_inc(x_1228);
x_1229 = lean_ctor_get_uint8(x_1228, sizeof(void*)*1);
lean_dec(x_1228);
if (x_1229 == 0)
{
lean_object* x_1230; 
x_1230 = lean_ctor_get(x_1227, 1);
lean_inc(x_1230);
lean_dec(x_1227);
x_1218 = x_1185;
x_1219 = x_1230;
goto block_1226;
}
else
{
lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; uint8_t x_1236; 
x_1231 = lean_ctor_get(x_1227, 1);
lean_inc(x_1231);
lean_dec(x_1227);
x_1232 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1233 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1232, x_16, x_17, x_1231);
x_1234 = lean_ctor_get(x_1233, 0);
lean_inc(x_1234);
x_1235 = lean_ctor_get(x_1233, 1);
lean_inc(x_1235);
lean_dec(x_1233);
x_1236 = lean_unbox(x_1234);
lean_dec(x_1234);
x_1218 = x_1236;
x_1219 = x_1235;
goto block_1226;
}
block_1217:
{
lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; 
x_1199 = x_1189;
x_1200 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1162, x_1199);
x_1201 = x_1200;
lean_inc(x_1194);
x_1202 = l_Lean_mkFVar(x_1194);
lean_inc(x_1195);
x_1203 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1203, 0, x_1195);
x_1204 = lean_box(x_1171);
lean_inc(x_1195);
x_1205 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_1205, 0, x_1194);
lean_closure_set(x_1205, 1, x_9);
lean_closure_set(x_1205, 2, x_1195);
lean_closure_set(x_1205, 3, x_3);
lean_closure_set(x_1205, 4, x_4);
lean_closure_set(x_1205, 5, x_7);
lean_closure_set(x_1205, 6, x_8);
lean_closure_set(x_1205, 7, x_1150);
lean_closure_set(x_1205, 8, x_1204);
lean_closure_set(x_1205, 9, x_1181);
lean_closure_set(x_1205, 10, x_1197);
lean_closure_set(x_1205, 11, x_1201);
lean_closure_set(x_1205, 12, x_1202);
x_1206 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_1206, 0, x_1203);
lean_closure_set(x_1206, 1, x_1205);
x_1207 = l_Lean_Meta_getMVarDecl(x_1195, x_14, x_15, x_16, x_17, x_1198);
if (lean_obj_tag(x_1207) == 0)
{
lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; 
x_1208 = lean_ctor_get(x_1207, 0);
lean_inc(x_1208);
x_1209 = lean_ctor_get(x_1207, 1);
lean_inc(x_1209);
lean_dec(x_1207);
x_1210 = lean_ctor_get(x_1208, 1);
lean_inc(x_1210);
x_1211 = lean_ctor_get(x_1208, 4);
lean_inc(x_1211);
lean_dec(x_1208);
x_1212 = l_Lean_Meta_withLocalContext___rarg(x_1210, x_1211, x_1206, x_14, x_15, x_16, x_17, x_1209);
lean_dec(x_14);
return x_1212;
}
else
{
uint8_t x_1213; 
lean_dec(x_1206);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1213 = !lean_is_exclusive(x_1207);
if (x_1213 == 0)
{
return x_1207;
}
else
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
x_1214 = lean_ctor_get(x_1207, 0);
x_1215 = lean_ctor_get(x_1207, 1);
lean_inc(x_1215);
lean_inc(x_1214);
lean_dec(x_1207);
x_1216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1216, 0, x_1214);
lean_ctor_set(x_1216, 1, x_1215);
return x_1216;
}
}
}
block_1226:
{
if (x_1218 == 0)
{
x_1198 = x_1219;
goto block_1217;
}
else
{
lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; 
lean_inc(x_1195);
x_1220 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1220, 0, x_1195);
x_1221 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_1222 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1222, 0, x_1221);
lean_ctor_set(x_1222, 1, x_1220);
x_1223 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1224 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1223, x_1222, x_14, x_15, x_16, x_17, x_1219);
x_1225 = lean_ctor_get(x_1224, 1);
lean_inc(x_1225);
lean_dec(x_1224);
x_1198 = x_1225;
goto block_1217;
}
}
}
else
{
uint8_t x_1237; 
lean_dec(x_1189);
lean_dec(x_1181);
lean_dec(x_1166);
lean_dec(x_1150);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1237 = !lean_is_exclusive(x_1191);
if (x_1237 == 0)
{
return x_1191;
}
else
{
lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; 
x_1238 = lean_ctor_get(x_1191, 0);
x_1239 = lean_ctor_get(x_1191, 1);
lean_inc(x_1239);
lean_inc(x_1238);
lean_dec(x_1191);
x_1240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1240, 0, x_1238);
lean_ctor_set(x_1240, 1, x_1239);
return x_1240;
}
}
}
else
{
uint8_t x_1241; 
lean_dec(x_1181);
lean_dec(x_1166);
lean_dec(x_1150);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1241 = !lean_is_exclusive(x_1186);
if (x_1241 == 0)
{
return x_1186;
}
else
{
lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; 
x_1242 = lean_ctor_get(x_1186, 0);
x_1243 = lean_ctor_get(x_1186, 1);
lean_inc(x_1243);
lean_inc(x_1242);
lean_dec(x_1186);
x_1244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1244, 0, x_1242);
lean_ctor_set(x_1244, 1, x_1243);
return x_1244;
}
}
}
else
{
uint8_t x_1245; 
lean_dec(x_1166);
lean_dec(x_1150);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1245 = !lean_is_exclusive(x_1178);
if (x_1245 == 0)
{
return x_1178;
}
else
{
lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; 
x_1246 = lean_ctor_get(x_1178, 0);
x_1247 = lean_ctor_get(x_1178, 1);
lean_inc(x_1247);
lean_inc(x_1246);
lean_dec(x_1178);
x_1248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1248, 0, x_1246);
lean_ctor_set(x_1248, 1, x_1247);
return x_1248;
}
}
}
}
else
{
uint8_t x_1263; 
lean_dec(x_1166);
lean_dec(x_1156);
lean_dec(x_1150);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1263 = !lean_is_exclusive(x_1168);
if (x_1263 == 0)
{
return x_1168;
}
else
{
lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; 
x_1264 = lean_ctor_get(x_1168, 0);
x_1265 = lean_ctor_get(x_1168, 1);
lean_inc(x_1265);
lean_inc(x_1264);
lean_dec(x_1168);
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
lean_dec(x_1156);
lean_dec(x_1150);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1267 = !lean_is_exclusive(x_1165);
if (x_1267 == 0)
{
return x_1165;
}
else
{
lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; 
x_1268 = lean_ctor_get(x_1165, 0);
x_1269 = lean_ctor_get(x_1165, 1);
lean_inc(x_1269);
lean_inc(x_1268);
lean_dec(x_1165);
x_1270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1270, 0, x_1268);
lean_ctor_set(x_1270, 1, x_1269);
return x_1270;
}
}
}
else
{
uint8_t x_1271; 
lean_dec(x_1150);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1271 = !lean_is_exclusive(x_1151);
if (x_1271 == 0)
{
return x_1151;
}
else
{
lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; 
x_1272 = lean_ctor_get(x_1151, 0);
x_1273 = lean_ctor_get(x_1151, 1);
lean_inc(x_1273);
lean_inc(x_1272);
lean_dec(x_1151);
x_1274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1274, 0, x_1272);
lean_ctor_set(x_1274, 1, x_1273);
return x_1274;
}
}
}
case 11:
{
lean_object* x_1275; lean_object* x_1276; 
lean_dec(x_13);
lean_dec(x_11);
x_1275 = lean_ctor_get(x_8, 5);
lean_inc(x_1275);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_1276 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_7, x_10, x_12, x_1275, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_1276) == 0)
{
lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; 
x_1277 = lean_ctor_get(x_1276, 1);
lean_inc(x_1277);
lean_dec(x_1276);
x_1278 = lean_io_ref_get(x_15, x_1277);
x_1279 = lean_ctor_get(x_1278, 0);
lean_inc(x_1279);
x_1280 = lean_ctor_get(x_1278, 1);
lean_inc(x_1280);
lean_dec(x_1278);
x_1281 = lean_ctor_get(x_1279, 0);
lean_inc(x_1281);
lean_dec(x_1279);
x_1282 = lean_ctor_get(x_8, 6);
lean_inc(x_1282);
x_1283 = l_List_redLength___main___rarg(x_1282);
x_1284 = lean_mk_empty_array_with_capacity(x_1283);
lean_dec(x_1283);
lean_inc(x_1282);
x_1285 = l_List_toArrayAux___main___rarg(x_1282, x_1284);
x_1286 = x_1285;
x_1287 = lean_unsigned_to_nat(0u);
lean_inc(x_1281);
lean_inc(x_7);
lean_inc(x_1);
x_1288 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_1288, 0, x_1);
lean_closure_set(x_1288, 1, x_7);
lean_closure_set(x_1288, 2, x_10);
lean_closure_set(x_1288, 3, x_12);
lean_closure_set(x_1288, 4, x_1281);
lean_closure_set(x_1288, 5, x_1282);
lean_closure_set(x_1288, 6, x_1287);
lean_closure_set(x_1288, 7, x_1286);
x_1289 = x_1288;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1290 = lean_apply_5(x_1289, x_14, x_15, x_16, x_17, x_1280);
if (lean_obj_tag(x_1290) == 0)
{
lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; 
x_1291 = lean_ctor_get(x_1290, 0);
lean_inc(x_1291);
x_1292 = lean_ctor_get(x_1290, 1);
lean_inc(x_1292);
lean_dec(x_1290);
lean_inc(x_1);
x_1293 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_1292);
if (lean_obj_tag(x_1293) == 0)
{
lean_object* x_1294; lean_object* x_1295; uint8_t x_1296; lean_object* x_1297; 
x_1294 = lean_ctor_get(x_1293, 0);
lean_inc(x_1294);
x_1295 = lean_ctor_get(x_1293, 1);
lean_inc(x_1295);
lean_dec(x_1293);
x_1296 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_1296 == 0)
{
lean_object* x_1375; uint8_t x_1376; 
x_1375 = l_Lean_MetavarContext_exprDependsOn(x_1281, x_1294, x_2);
x_1376 = lean_unbox(x_1375);
lean_dec(x_1375);
if (x_1376 == 0)
{
x_1297 = x_1295;
goto block_1374;
}
else
{
lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; uint8_t x_1384; 
lean_dec(x_1291);
lean_dec(x_1275);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_1377 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1377, 0, x_3);
x_1378 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1379 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1379, 0, x_1378);
lean_ctor_set(x_1379, 1, x_1377);
x_1380 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_1381 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1381, 0, x_1379);
lean_ctor_set(x_1381, 1, x_1380);
x_1382 = lean_box(0);
x_1383 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_1381, x_1382, x_14, x_15, x_16, x_17, x_1295);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1384 = !lean_is_exclusive(x_1383);
if (x_1384 == 0)
{
return x_1383;
}
else
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; 
x_1385 = lean_ctor_get(x_1383, 0);
x_1386 = lean_ctor_get(x_1383, 1);
lean_inc(x_1386);
lean_inc(x_1385);
lean_dec(x_1383);
x_1387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1387, 0, x_1385);
lean_ctor_set(x_1387, 1, x_1386);
return x_1387;
}
}
}
else
{
lean_dec(x_1294);
lean_dec(x_1281);
x_1297 = x_1295;
goto block_1374;
}
block_1374:
{
lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; uint8_t x_1302; lean_object* x_1303; 
lean_inc(x_1291);
x_1298 = x_1291;
x_1299 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1287, x_1298);
x_1300 = x_1299;
x_1301 = lean_array_push(x_1300, x_2);
x_1302 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1303 = l_Lean_Meta_revert(x_1, x_1301, x_1302, x_14, x_15, x_16, x_17, x_1297);
if (lean_obj_tag(x_1303) == 0)
{
lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; uint8_t x_1310; lean_object* x_1311; 
x_1304 = lean_ctor_get(x_1303, 0);
lean_inc(x_1304);
x_1305 = lean_ctor_get(x_1303, 1);
lean_inc(x_1305);
lean_dec(x_1303);
x_1306 = lean_ctor_get(x_1304, 0);
lean_inc(x_1306);
x_1307 = lean_ctor_get(x_1304, 1);
lean_inc(x_1307);
lean_dec(x_1304);
x_1308 = lean_array_get_size(x_1291);
x_1309 = lean_box(0);
x_1310 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1311 = l_Lean_Meta_introN(x_1307, x_1308, x_1309, x_1310, x_14, x_15, x_16, x_17, x_1305);
if (lean_obj_tag(x_1311) == 0)
{
lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; 
x_1312 = lean_ctor_get(x_1311, 0);
lean_inc(x_1312);
x_1313 = lean_ctor_get(x_1311, 1);
lean_inc(x_1313);
lean_dec(x_1311);
x_1314 = lean_ctor_get(x_1312, 0);
lean_inc(x_1314);
x_1315 = lean_ctor_get(x_1312, 1);
lean_inc(x_1315);
lean_dec(x_1312);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1316 = l_Lean_Meta_intro1(x_1315, x_1310, x_14, x_15, x_16, x_17, x_1313);
if (lean_obj_tag(x_1316) == 0)
{
lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; uint8_t x_1343; lean_object* x_1344; lean_object* x_1352; lean_object* x_1353; uint8_t x_1354; 
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
x_1321 = lean_box(0);
x_1322 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_1291, x_1314, x_1291, x_1287, x_1321);
lean_dec(x_1291);
x_1352 = l_Lean_Core_getTraceState___rarg(x_17, x_1318);
x_1353 = lean_ctor_get(x_1352, 0);
lean_inc(x_1353);
x_1354 = lean_ctor_get_uint8(x_1353, sizeof(void*)*1);
lean_dec(x_1353);
if (x_1354 == 0)
{
lean_object* x_1355; 
x_1355 = lean_ctor_get(x_1352, 1);
lean_inc(x_1355);
lean_dec(x_1352);
x_1343 = x_1310;
x_1344 = x_1355;
goto block_1351;
}
else
{
lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; uint8_t x_1361; 
x_1356 = lean_ctor_get(x_1352, 1);
lean_inc(x_1356);
lean_dec(x_1352);
x_1357 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1358 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1357, x_16, x_17, x_1356);
x_1359 = lean_ctor_get(x_1358, 0);
lean_inc(x_1359);
x_1360 = lean_ctor_get(x_1358, 1);
lean_inc(x_1360);
lean_dec(x_1358);
x_1361 = lean_unbox(x_1359);
lean_dec(x_1359);
x_1343 = x_1361;
x_1344 = x_1360;
goto block_1351;
}
block_1342:
{
lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; 
x_1324 = x_1314;
x_1325 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1287, x_1324);
x_1326 = x_1325;
lean_inc(x_1319);
x_1327 = l_Lean_mkFVar(x_1319);
lean_inc(x_1320);
x_1328 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1328, 0, x_1320);
x_1329 = lean_box(x_1296);
lean_inc(x_1320);
x_1330 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_1330, 0, x_1319);
lean_closure_set(x_1330, 1, x_9);
lean_closure_set(x_1330, 2, x_1320);
lean_closure_set(x_1330, 3, x_3);
lean_closure_set(x_1330, 4, x_4);
lean_closure_set(x_1330, 5, x_7);
lean_closure_set(x_1330, 6, x_8);
lean_closure_set(x_1330, 7, x_1275);
lean_closure_set(x_1330, 8, x_1329);
lean_closure_set(x_1330, 9, x_1306);
lean_closure_set(x_1330, 10, x_1322);
lean_closure_set(x_1330, 11, x_1326);
lean_closure_set(x_1330, 12, x_1327);
x_1331 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_1331, 0, x_1328);
lean_closure_set(x_1331, 1, x_1330);
x_1332 = l_Lean_Meta_getMVarDecl(x_1320, x_14, x_15, x_16, x_17, x_1323);
if (lean_obj_tag(x_1332) == 0)
{
lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; 
x_1333 = lean_ctor_get(x_1332, 0);
lean_inc(x_1333);
x_1334 = lean_ctor_get(x_1332, 1);
lean_inc(x_1334);
lean_dec(x_1332);
x_1335 = lean_ctor_get(x_1333, 1);
lean_inc(x_1335);
x_1336 = lean_ctor_get(x_1333, 4);
lean_inc(x_1336);
lean_dec(x_1333);
x_1337 = l_Lean_Meta_withLocalContext___rarg(x_1335, x_1336, x_1331, x_14, x_15, x_16, x_17, x_1334);
lean_dec(x_14);
return x_1337;
}
else
{
uint8_t x_1338; 
lean_dec(x_1331);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1338 = !lean_is_exclusive(x_1332);
if (x_1338 == 0)
{
return x_1332;
}
else
{
lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; 
x_1339 = lean_ctor_get(x_1332, 0);
x_1340 = lean_ctor_get(x_1332, 1);
lean_inc(x_1340);
lean_inc(x_1339);
lean_dec(x_1332);
x_1341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1341, 0, x_1339);
lean_ctor_set(x_1341, 1, x_1340);
return x_1341;
}
}
}
block_1351:
{
if (x_1343 == 0)
{
x_1323 = x_1344;
goto block_1342;
}
else
{
lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
lean_inc(x_1320);
x_1345 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1345, 0, x_1320);
x_1346 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_1347 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1347, 0, x_1346);
lean_ctor_set(x_1347, 1, x_1345);
x_1348 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1349 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1348, x_1347, x_14, x_15, x_16, x_17, x_1344);
x_1350 = lean_ctor_get(x_1349, 1);
lean_inc(x_1350);
lean_dec(x_1349);
x_1323 = x_1350;
goto block_1342;
}
}
}
else
{
uint8_t x_1362; 
lean_dec(x_1314);
lean_dec(x_1306);
lean_dec(x_1291);
lean_dec(x_1275);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1362 = !lean_is_exclusive(x_1316);
if (x_1362 == 0)
{
return x_1316;
}
else
{
lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; 
x_1363 = lean_ctor_get(x_1316, 0);
x_1364 = lean_ctor_get(x_1316, 1);
lean_inc(x_1364);
lean_inc(x_1363);
lean_dec(x_1316);
x_1365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1365, 0, x_1363);
lean_ctor_set(x_1365, 1, x_1364);
return x_1365;
}
}
}
else
{
uint8_t x_1366; 
lean_dec(x_1306);
lean_dec(x_1291);
lean_dec(x_1275);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1366 = !lean_is_exclusive(x_1311);
if (x_1366 == 0)
{
return x_1311;
}
else
{
lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; 
x_1367 = lean_ctor_get(x_1311, 0);
x_1368 = lean_ctor_get(x_1311, 1);
lean_inc(x_1368);
lean_inc(x_1367);
lean_dec(x_1311);
x_1369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1369, 0, x_1367);
lean_ctor_set(x_1369, 1, x_1368);
return x_1369;
}
}
}
else
{
uint8_t x_1370; 
lean_dec(x_1291);
lean_dec(x_1275);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1370 = !lean_is_exclusive(x_1303);
if (x_1370 == 0)
{
return x_1303;
}
else
{
lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; 
x_1371 = lean_ctor_get(x_1303, 0);
x_1372 = lean_ctor_get(x_1303, 1);
lean_inc(x_1372);
lean_inc(x_1371);
lean_dec(x_1303);
x_1373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1373, 0, x_1371);
lean_ctor_set(x_1373, 1, x_1372);
return x_1373;
}
}
}
}
else
{
uint8_t x_1388; 
lean_dec(x_1291);
lean_dec(x_1281);
lean_dec(x_1275);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1388 = !lean_is_exclusive(x_1293);
if (x_1388 == 0)
{
return x_1293;
}
else
{
lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; 
x_1389 = lean_ctor_get(x_1293, 0);
x_1390 = lean_ctor_get(x_1293, 1);
lean_inc(x_1390);
lean_inc(x_1389);
lean_dec(x_1293);
x_1391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1391, 0, x_1389);
lean_ctor_set(x_1391, 1, x_1390);
return x_1391;
}
}
}
else
{
uint8_t x_1392; 
lean_dec(x_1281);
lean_dec(x_1275);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1392 = !lean_is_exclusive(x_1290);
if (x_1392 == 0)
{
return x_1290;
}
else
{
lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; 
x_1393 = lean_ctor_get(x_1290, 0);
x_1394 = lean_ctor_get(x_1290, 1);
lean_inc(x_1394);
lean_inc(x_1393);
lean_dec(x_1290);
x_1395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1395, 0, x_1393);
lean_ctor_set(x_1395, 1, x_1394);
return x_1395;
}
}
}
else
{
uint8_t x_1396; 
lean_dec(x_1275);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1396 = !lean_is_exclusive(x_1276);
if (x_1396 == 0)
{
return x_1276;
}
else
{
lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; 
x_1397 = lean_ctor_get(x_1276, 0);
x_1398 = lean_ctor_get(x_1276, 1);
lean_inc(x_1398);
lean_inc(x_1397);
lean_dec(x_1276);
x_1399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1399, 0, x_1397);
lean_ctor_set(x_1399, 1, x_1398);
return x_1399;
}
}
}
default: 
{
lean_object* x_1400; lean_object* x_1401; 
lean_dec(x_13);
lean_dec(x_11);
x_1400 = lean_ctor_get(x_8, 5);
lean_inc(x_1400);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_1);
x_1401 = l_List_forM___main___at_Lean_Meta_induction___spec__1(x_1, x_7, x_10, x_12, x_1400, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_1401) == 0)
{
lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; 
x_1402 = lean_ctor_get(x_1401, 1);
lean_inc(x_1402);
lean_dec(x_1401);
x_1403 = lean_io_ref_get(x_15, x_1402);
x_1404 = lean_ctor_get(x_1403, 0);
lean_inc(x_1404);
x_1405 = lean_ctor_get(x_1403, 1);
lean_inc(x_1405);
lean_dec(x_1403);
x_1406 = lean_ctor_get(x_1404, 0);
lean_inc(x_1406);
lean_dec(x_1404);
x_1407 = lean_ctor_get(x_8, 6);
lean_inc(x_1407);
x_1408 = l_List_redLength___main___rarg(x_1407);
x_1409 = lean_mk_empty_array_with_capacity(x_1408);
lean_dec(x_1408);
lean_inc(x_1407);
x_1410 = l_List_toArrayAux___main___rarg(x_1407, x_1409);
x_1411 = x_1410;
x_1412 = lean_unsigned_to_nat(0u);
lean_inc(x_1406);
lean_inc(x_7);
lean_inc(x_1);
x_1413 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__4___boxed), 13, 8);
lean_closure_set(x_1413, 0, x_1);
lean_closure_set(x_1413, 1, x_7);
lean_closure_set(x_1413, 2, x_10);
lean_closure_set(x_1413, 3, x_12);
lean_closure_set(x_1413, 4, x_1406);
lean_closure_set(x_1413, 5, x_1407);
lean_closure_set(x_1413, 6, x_1412);
lean_closure_set(x_1413, 7, x_1411);
x_1414 = x_1413;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_1415 = lean_apply_5(x_1414, x_14, x_15, x_16, x_17, x_1405);
if (lean_obj_tag(x_1415) == 0)
{
lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; 
x_1416 = lean_ctor_get(x_1415, 0);
lean_inc(x_1416);
x_1417 = lean_ctor_get(x_1415, 1);
lean_inc(x_1417);
lean_dec(x_1415);
lean_inc(x_1);
x_1418 = l_Lean_Meta_getMVarType(x_1, x_14, x_15, x_16, x_17, x_1417);
if (lean_obj_tag(x_1418) == 0)
{
lean_object* x_1419; lean_object* x_1420; uint8_t x_1421; lean_object* x_1422; 
x_1419 = lean_ctor_get(x_1418, 0);
lean_inc(x_1419);
x_1420 = lean_ctor_get(x_1418, 1);
lean_inc(x_1420);
lean_dec(x_1418);
x_1421 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
if (x_1421 == 0)
{
lean_object* x_1500; uint8_t x_1501; 
x_1500 = l_Lean_MetavarContext_exprDependsOn(x_1406, x_1419, x_2);
x_1501 = lean_unbox(x_1500);
lean_dec(x_1500);
if (x_1501 == 0)
{
x_1422 = x_1420;
goto block_1499;
}
else
{
lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; uint8_t x_1509; 
lean_dec(x_1416);
lean_dec(x_1400);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_1502 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1502, 0, x_3);
x_1503 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__7___closed__6;
x_1504 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1504, 0, x_1503);
lean_ctor_set(x_1504, 1, x_1502);
x_1505 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__8;
x_1506 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1506, 0, x_1504);
lean_ctor_set(x_1506, 1, x_1505);
x_1507 = lean_box(0);
x_1508 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_1506, x_1507, x_14, x_15, x_16, x_17, x_1420);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1509 = !lean_is_exclusive(x_1508);
if (x_1509 == 0)
{
return x_1508;
}
else
{
lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; 
x_1510 = lean_ctor_get(x_1508, 0);
x_1511 = lean_ctor_get(x_1508, 1);
lean_inc(x_1511);
lean_inc(x_1510);
lean_dec(x_1508);
x_1512 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1512, 0, x_1510);
lean_ctor_set(x_1512, 1, x_1511);
return x_1512;
}
}
}
else
{
lean_dec(x_1419);
lean_dec(x_1406);
x_1422 = x_1420;
goto block_1499;
}
block_1499:
{
lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; uint8_t x_1427; lean_object* x_1428; 
lean_inc(x_1416);
x_1423 = x_1416;
x_1424 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1412, x_1423);
x_1425 = x_1424;
x_1426 = lean_array_push(x_1425, x_2);
x_1427 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1428 = l_Lean_Meta_revert(x_1, x_1426, x_1427, x_14, x_15, x_16, x_17, x_1422);
if (lean_obj_tag(x_1428) == 0)
{
lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; uint8_t x_1435; lean_object* x_1436; 
x_1429 = lean_ctor_get(x_1428, 0);
lean_inc(x_1429);
x_1430 = lean_ctor_get(x_1428, 1);
lean_inc(x_1430);
lean_dec(x_1428);
x_1431 = lean_ctor_get(x_1429, 0);
lean_inc(x_1431);
x_1432 = lean_ctor_get(x_1429, 1);
lean_inc(x_1432);
lean_dec(x_1429);
x_1433 = lean_array_get_size(x_1416);
x_1434 = lean_box(0);
x_1435 = 0;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1436 = l_Lean_Meta_introN(x_1432, x_1433, x_1434, x_1435, x_14, x_15, x_16, x_17, x_1430);
if (lean_obj_tag(x_1436) == 0)
{
lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; 
x_1437 = lean_ctor_get(x_1436, 0);
lean_inc(x_1437);
x_1438 = lean_ctor_get(x_1436, 1);
lean_inc(x_1438);
lean_dec(x_1436);
x_1439 = lean_ctor_get(x_1437, 0);
lean_inc(x_1439);
x_1440 = lean_ctor_get(x_1437, 1);
lean_inc(x_1440);
lean_dec(x_1437);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1441 = l_Lean_Meta_intro1(x_1440, x_1435, x_14, x_15, x_16, x_17, x_1438);
if (lean_obj_tag(x_1441) == 0)
{
lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; uint8_t x_1468; lean_object* x_1469; lean_object* x_1477; lean_object* x_1478; uint8_t x_1479; 
x_1442 = lean_ctor_get(x_1441, 0);
lean_inc(x_1442);
x_1443 = lean_ctor_get(x_1441, 1);
lean_inc(x_1443);
lean_dec(x_1441);
x_1444 = lean_ctor_get(x_1442, 0);
lean_inc(x_1444);
x_1445 = lean_ctor_get(x_1442, 1);
lean_inc(x_1445);
lean_dec(x_1442);
x_1446 = lean_box(0);
x_1447 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__5(x_1416, x_1439, x_1416, x_1412, x_1446);
lean_dec(x_1416);
x_1477 = l_Lean_Core_getTraceState___rarg(x_17, x_1443);
x_1478 = lean_ctor_get(x_1477, 0);
lean_inc(x_1478);
x_1479 = lean_ctor_get_uint8(x_1478, sizeof(void*)*1);
lean_dec(x_1478);
if (x_1479 == 0)
{
lean_object* x_1480; 
x_1480 = lean_ctor_get(x_1477, 1);
lean_inc(x_1480);
lean_dec(x_1477);
x_1468 = x_1435;
x_1469 = x_1480;
goto block_1476;
}
else
{
lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; uint8_t x_1486; 
x_1481 = lean_ctor_get(x_1477, 1);
lean_inc(x_1481);
lean_dec(x_1477);
x_1482 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1483 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1482, x_16, x_17, x_1481);
x_1484 = lean_ctor_get(x_1483, 0);
lean_inc(x_1484);
x_1485 = lean_ctor_get(x_1483, 1);
lean_inc(x_1485);
lean_dec(x_1483);
x_1486 = lean_unbox(x_1484);
lean_dec(x_1484);
x_1468 = x_1486;
x_1469 = x_1485;
goto block_1476;
}
block_1467:
{
lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; 
x_1449 = x_1439;
x_1450 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1412, x_1449);
x_1451 = x_1450;
lean_inc(x_1444);
x_1452 = l_Lean_mkFVar(x_1444);
lean_inc(x_1445);
x_1453 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1453, 0, x_1445);
x_1454 = lean_box(x_1421);
lean_inc(x_1445);
x_1455 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___lambda__1___boxed), 19, 13);
lean_closure_set(x_1455, 0, x_1444);
lean_closure_set(x_1455, 1, x_9);
lean_closure_set(x_1455, 2, x_1445);
lean_closure_set(x_1455, 3, x_3);
lean_closure_set(x_1455, 4, x_4);
lean_closure_set(x_1455, 5, x_7);
lean_closure_set(x_1455, 6, x_8);
lean_closure_set(x_1455, 7, x_1400);
lean_closure_set(x_1455, 8, x_1454);
lean_closure_set(x_1455, 9, x_1431);
lean_closure_set(x_1455, 10, x_1447);
lean_closure_set(x_1455, 11, x_1451);
lean_closure_set(x_1455, 12, x_1452);
x_1456 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_1456, 0, x_1453);
lean_closure_set(x_1456, 1, x_1455);
x_1457 = l_Lean_Meta_getMVarDecl(x_1445, x_14, x_15, x_16, x_17, x_1448);
if (lean_obj_tag(x_1457) == 0)
{
lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; 
x_1458 = lean_ctor_get(x_1457, 0);
lean_inc(x_1458);
x_1459 = lean_ctor_get(x_1457, 1);
lean_inc(x_1459);
lean_dec(x_1457);
x_1460 = lean_ctor_get(x_1458, 1);
lean_inc(x_1460);
x_1461 = lean_ctor_get(x_1458, 4);
lean_inc(x_1461);
lean_dec(x_1458);
x_1462 = l_Lean_Meta_withLocalContext___rarg(x_1460, x_1461, x_1456, x_14, x_15, x_16, x_17, x_1459);
lean_dec(x_14);
return x_1462;
}
else
{
uint8_t x_1463; 
lean_dec(x_1456);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_1463 = !lean_is_exclusive(x_1457);
if (x_1463 == 0)
{
return x_1457;
}
else
{
lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; 
x_1464 = lean_ctor_get(x_1457, 0);
x_1465 = lean_ctor_get(x_1457, 1);
lean_inc(x_1465);
lean_inc(x_1464);
lean_dec(x_1457);
x_1466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1466, 0, x_1464);
lean_ctor_set(x_1466, 1, x_1465);
return x_1466;
}
}
}
block_1476:
{
if (x_1468 == 0)
{
x_1448 = x_1469;
goto block_1467;
}
else
{
lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; 
lean_inc(x_1445);
x_1470 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1470, 0, x_1445);
x_1471 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__5;
x_1472 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1472, 0, x_1471);
lean_ctor_set(x_1472, 1, x_1470);
x_1473 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8___closed__1;
x_1474 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1473, x_1472, x_14, x_15, x_16, x_17, x_1469);
x_1475 = lean_ctor_get(x_1474, 1);
lean_inc(x_1475);
lean_dec(x_1474);
x_1448 = x_1475;
goto block_1467;
}
}
}
else
{
uint8_t x_1487; 
lean_dec(x_1439);
lean_dec(x_1431);
lean_dec(x_1416);
lean_dec(x_1400);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1487 = !lean_is_exclusive(x_1441);
if (x_1487 == 0)
{
return x_1441;
}
else
{
lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; 
x_1488 = lean_ctor_get(x_1441, 0);
x_1489 = lean_ctor_get(x_1441, 1);
lean_inc(x_1489);
lean_inc(x_1488);
lean_dec(x_1441);
x_1490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1490, 0, x_1488);
lean_ctor_set(x_1490, 1, x_1489);
return x_1490;
}
}
}
else
{
uint8_t x_1491; 
lean_dec(x_1431);
lean_dec(x_1416);
lean_dec(x_1400);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1491 = !lean_is_exclusive(x_1436);
if (x_1491 == 0)
{
return x_1436;
}
else
{
lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; 
x_1492 = lean_ctor_get(x_1436, 0);
x_1493 = lean_ctor_get(x_1436, 1);
lean_inc(x_1493);
lean_inc(x_1492);
lean_dec(x_1436);
x_1494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1494, 0, x_1492);
lean_ctor_set(x_1494, 1, x_1493);
return x_1494;
}
}
}
else
{
uint8_t x_1495; 
lean_dec(x_1416);
lean_dec(x_1400);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_1495 = !lean_is_exclusive(x_1428);
if (x_1495 == 0)
{
return x_1428;
}
else
{
lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; 
x_1496 = lean_ctor_get(x_1428, 0);
x_1497 = lean_ctor_get(x_1428, 1);
lean_inc(x_1497);
lean_inc(x_1496);
lean_dec(x_1428);
x_1498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1498, 0, x_1496);
lean_ctor_set(x_1498, 1, x_1497);
return x_1498;
}
}
}
}
else
{
uint8_t x_1513; 
lean_dec(x_1416);
lean_dec(x_1406);
lean_dec(x_1400);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1513 = !lean_is_exclusive(x_1418);
if (x_1513 == 0)
{
return x_1418;
}
else
{
lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; 
x_1514 = lean_ctor_get(x_1418, 0);
x_1515 = lean_ctor_get(x_1418, 1);
lean_inc(x_1515);
lean_inc(x_1514);
lean_dec(x_1418);
x_1516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1516, 0, x_1514);
lean_ctor_set(x_1516, 1, x_1515);
return x_1516;
}
}
}
else
{
uint8_t x_1517; 
lean_dec(x_1406);
lean_dec(x_1400);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1517 = !lean_is_exclusive(x_1415);
if (x_1517 == 0)
{
return x_1415;
}
else
{
lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; 
x_1518 = lean_ctor_get(x_1415, 0);
x_1519 = lean_ctor_get(x_1415, 1);
lean_inc(x_1519);
lean_inc(x_1518);
lean_dec(x_1415);
x_1520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1520, 0, x_1518);
lean_ctor_set(x_1520, 1, x_1519);
return x_1520;
}
}
}
else
{
uint8_t x_1521; 
lean_dec(x_1400);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1521 = !lean_is_exclusive(x_1401);
if (x_1521 == 0)
{
return x_1401;
}
else
{
lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; 
x_1522 = lean_ctor_get(x_1401, 0);
x_1523 = lean_ctor_get(x_1401, 1);
lean_inc(x_1523);
lean_inc(x_1522);
lean_dec(x_1401);
x_1524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1524, 0, x_1522);
lean_ctor_set(x_1524, 1, x_1523);
return x_1524;
}
}
}
}
}
}
lean_object* l_Lean_Meta_induction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_9);
lean_inc(x_1);
x_14 = l_Lean_Meta_getLocalDecl(x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_18 = l_Lean_Meta_mkRecursorInfo(x_2, x_17, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_LocalDecl_type(x_15);
lean_dec(x_15);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_21);
x_23 = l_Lean_Meta_whnfUntil(x_21, x_22, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(x_3, x_21, x_9, x_10, x_11, x_12, x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Lean_Expr_getAppNumArgsAux___main(x_28, x_29);
x_31 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_30);
x_32 = lean_mk_array(x_30, x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_sub(x_30, x_33);
lean_dec(x_30);
lean_inc(x_28);
x_35 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(x_3, x_1, x_2, x_4, x_5, x_6, x_7, x_19, x_22, x_28, x_28, x_32, x_34, x_9, x_10, x_11, x_12, x_27);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
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
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_18, 0);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_18);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Meta_induction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = l___private_Lean_Meta_Basic_3__forallTelescopeReducingAuxAux___main___rarg___closed__1;
x_14 = l___private_Lean_Meta_Basic_3__forallTelescopeReducingAuxAux___main___rarg___closed__2;
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_induction___lambda__1___boxed), 13, 7);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_3);
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_13);
lean_closure_set(x_15, 5, x_14);
lean_closure_set(x_15, 6, x_11);
x_16 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive_x3f___main___spec__4___rarg), 7, 2);
lean_closure_set(x_16, 0, x_12);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_Meta_getMVarDecl(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 4);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_Meta_withLocalContext___rarg(x_20, x_21, x_16, x_6, x_7, x_8, x_9, x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
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
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
}
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_induction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
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
