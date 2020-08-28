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
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize___main(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity(lean_object*);
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8;
lean_object* l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Meta_introN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__2;
lean_object* l_Lean_Meta_induction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3;
lean_object* l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___boxed(lean_object**);
lean_object* l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2;
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_Lean_Level_Inhabited;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Lean_Meta_InferType_4__getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_induction___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___boxed(lean_object**);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2;
lean_object* l_Lean_Meta_checkNotAssigned___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_elem___main___at_Lean_Meta_induction___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_induction___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2;
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
extern lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2;
extern lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__3;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7;
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1;
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_getParamNamesImpl___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__7;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__9;
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3;
lean_object* l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
lean_object* l_Lean_MetavarContext_localDeclDependsOn(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_InductionSubgoal_inhabited___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7;
lean_object* l___private_Lean_Meta_SynthInstance_10__synthInstanceImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
uint8_t l_List_elem___main___at_Lean_Meta_induction___spec__5(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6;
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value_x3f(lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4;
lean_object* l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3;
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___boxed(lean_object**);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__6;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__8;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5;
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__6;
extern lean_object* l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed(lean_object**);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__3;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
extern lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1;
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6;
uint8_t l_Lean_Level_isZero(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__5;
extern lean_object* l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3;
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___boxed(lean_object**);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__8;
lean_object* l_Lean_Meta_synthInstance_x3f___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3;
lean_object* l_Lean_Meta_InductionSubgoal_inhabited;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Expr_isForall(x_9);
if (x_10 == 0)
{
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
else
{
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = l_Lean_Expr_isForall(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
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
x_13 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_4, x_5, x_6, x_7, x_8, x_9);
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
x_16 = l_Lean_Meta_whnfForall___at___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___spec__1(x_14, x_5, x_6, x_7, x_8, x_15);
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
x_20 = l___private_Lean_Meta_SynthInstance_10__synthInstanceImp(x_19, x_5, x_6, x_7, x_8, x_18);
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
x_9 = l_Lean_Meta_whnfForall___at___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Meta_synthInstance_x3f___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_21 = l_Lean_Meta_whnfForall___at___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___spec__1(x_13, x_16, x_17, x_18, x_19, x_20);
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
x_33 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(x_1, x_12, x_16, x_17, x_18, x_19, x_23);
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
x_48 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(x_1, x_12, x_16, x_17, x_18, x_19, x_23);
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
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_194; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_194 = lean_nat_dec_le(x_8, x_11);
if (x_194 == 0)
{
x_58 = x_57;
goto block_193;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_dec(x_56);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_195 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_196 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_197 = lean_box(0);
x_198 = l_Lean_Meta_throwTacticEx___rarg(x_195, x_1, x_196, x_197, x_16, x_17, x_18, x_19, x_57);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_199 = !lean_is_exclusive(x_198);
if (x_199 == 0)
{
return x_198;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_198, 0);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_198);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
block_193:
{
if (lean_obj_tag(x_22) == 7)
{
lean_object* x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; lean_object* x_63; uint8_t x_143; uint8_t x_144; 
x_59 = lean_ctor_get(x_22, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_22, 1);
lean_inc(x_60);
x_61 = lean_ctor_get_uint64(x_22, sizeof(void*)*3);
x_62 = l_Lean_Expr_headBeta(x_60);
x_143 = (uint8_t)((x_61 << 24) >> 61);
x_144 = l_Lean_BinderInfo_isInstImplicit(x_143);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_box(0);
x_63 = x_145;
goto block_142;
}
else
{
uint8_t x_146; 
x_146 = l_Array_isEmpty___rarg(x_2);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_box(0);
x_63 = x_147;
goto block_142;
}
else
{
lean_object* x_148; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_62);
x_148 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(x_62, x_16, x_17, x_18, x_19, x_58);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l_Lean_Name_append___main(x_56, x_59);
lean_dec(x_56);
x_152 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_62, x_151, x_16, x_17, x_18, x_19, x_150);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
lean_inc(x_153);
x_155 = l_Lean_mkApp(x_12, x_153);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_156 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_22, x_153, x_16, x_17, x_18, x_19, x_154);
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
x_20 = x_158;
goto _start;
}
else
{
uint8_t x_168; 
lean_dec(x_155);
lean_dec(x_153);
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
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_56);
x_172 = lean_ctor_get(x_148, 1);
lean_inc(x_172);
lean_dec(x_148);
x_173 = lean_ctor_get(x_149, 0);
lean_inc(x_173);
lean_dec(x_149);
lean_inc(x_173);
x_174 = l_Lean_mkApp(x_12, x_173);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_175 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_22, x_173, x_16, x_17, x_18, x_19, x_172);
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
x_20 = x_177;
goto _start;
}
else
{
uint8_t x_182; 
lean_dec(x_174);
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
x_186 = !lean_is_exclusive(x_148);
if (x_186 == 0)
{
return x_148;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_148, 0);
x_188 = lean_ctor_get(x_148, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_148);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
}
block_142:
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_63);
lean_inc(x_62);
x_64 = l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(x_62);
x_65 = lean_nat_dec_lt(x_64, x_6);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
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
x_127 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_62, x_126, x_16, x_17, x_18, x_19, x_58);
if (x_125 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_box(0);
x_72 = x_130;
x_73 = x_128;
x_74 = x_129;
goto block_123;
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
x_72 = x_133;
x_73 = x_131;
x_74 = x_132;
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
lean_inc(x_16);
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
lean_inc(x_16);
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
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
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
x_134 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_135 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
x_136 = lean_box(0);
x_137 = l_Lean_Meta_throwTacticEx___rarg(x_134, x_1, x_135, x_136, x_16, x_17, x_18, x_19, x_58);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
return x_137;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_137);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_56);
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_190 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
x_191 = l_unreachable_x21___rarg(x_190);
x_192 = lean_apply_5(x_191, x_16, x_17, x_18, x_19, x_58);
return x_192;
}
}
}
else
{
uint8_t x_203; 
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
x_203 = !lean_is_exclusive(x_55);
if (x_203 == 0)
{
return x_55;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_55, 0);
x_205 = lean_ctor_get(x_55, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_55);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_12);
lean_ctor_set(x_207, 1, x_22);
x_208 = lean_unsigned_to_nat(0u);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_209 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4(x_1, x_7, x_7, x_208, x_207, x_16, x_17, x_18, x_19, x_23);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
lean_dec(x_210);
lean_inc(x_5);
x_214 = l_Lean_mkApp(x_212, x_5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_215 = l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(x_1, x_213, x_5, x_16, x_17, x_18, x_19, x_211);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_unsigned_to_nat(1u);
x_219 = lean_nat_add(x_10, x_218);
lean_dec(x_10);
x_220 = lean_array_get_size(x_7);
x_221 = lean_nat_add(x_219, x_220);
lean_dec(x_220);
lean_dec(x_219);
x_222 = 1;
x_10 = x_221;
x_12 = x_214;
x_13 = x_216;
x_14 = x_222;
x_20 = x_217;
goto _start;
}
else
{
uint8_t x_224; 
lean_dec(x_214);
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
x_224 = !lean_is_exclusive(x_215);
if (x_224 == 0)
{
return x_215;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_215, 0);
x_226 = lean_ctor_get(x_215, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_215);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
uint8_t x_228; 
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
x_228 = !lean_is_exclusive(x_209);
if (x_228 == 0)
{
return x_209;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_209, 0);
x_230 = lean_ctor_get(x_209, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_209);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
}
}
}
else
{
uint8_t x_232; 
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
x_232 = !lean_is_exclusive(x_21);
if (x_232 == 0)
{
return x_21;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_21, 0);
x_234 = lean_ctor_get(x_21, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_21);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_18 = l_Lean_Meta_inferType___at_Lean_Meta_mkAuxDefinitionFor___spec__1(x_8, x_9, x_10, x_11, x_12, x_16);
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
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_induction___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1;
x_9 = l_unreachable_x21___rarg(x_8);
x_10 = lean_apply_5(x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = l_Lean_LocalDecl_value_x3f(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_17; 
lean_free_object(x_12);
lean_dec(x_2);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_2 = x_17;
x_7 = x_15;
goto _start;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = l_Lean_LocalDecl_value_x3f(x_19);
lean_dec(x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_2);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_2 = x_23;
x_7 = x_20;
goto _start;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
case 2:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1(x_29, x_3, x_4, x_5, x_6, x_7);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
lean_ctor_set(x_30, 0, x_2);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
x_2 = x_37;
x_7 = x_36;
goto _start;
}
}
case 4:
{
lean_object* x_39; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_39 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = l_Lean_Expr_isAppOf(x_41, x_1);
if (x_43 == 0)
{
lean_object* x_44; 
lean_free_object(x_39);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_41);
x_44 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_41, x_3, x_4, x_5, x_6, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_44, 0);
lean_dec(x_47);
lean_ctor_set(x_44, 0, x_41);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_41);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
lean_dec(x_45);
x_2 = x_51;
x_7 = x_50;
goto _start;
}
}
else
{
uint8_t x_53; 
lean_dec(x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_44);
if (x_53 == 0)
{
return x_44;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_44, 0);
x_55 = lean_ctor_get(x_44, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_44);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_39;
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_39, 0);
x_58 = lean_ctor_get(x_39, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_39);
x_59 = l_Lean_Expr_isAppOf(x_57, x_1);
if (x_59 == 0)
{
lean_object* x_60; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_57);
x_60 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_57, x_3, x_4, x_5, x_6, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_dec(x_60);
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
lean_dec(x_61);
x_2 = x_66;
x_7 = x_65;
goto _start;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_57);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = lean_ctor_get(x_60, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_60, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_70 = x_60;
} else {
 lean_dec_ref(x_60);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
lean_object* x_72; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_57);
lean_ctor_set(x_72, 1, x_58);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_39);
if (x_73 == 0)
{
return x_39;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_39, 0);
x_75 = lean_ctor_get(x_39, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_39);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
case 5:
{
lean_object* x_77; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_77 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
x_81 = l_Lean_Expr_isAppOf(x_79, x_1);
if (x_81 == 0)
{
lean_object* x_82; 
lean_free_object(x_77);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_79);
x_82 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_79, x_3, x_4, x_5, x_6, x_80);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_82, 0);
lean_dec(x_85);
lean_ctor_set(x_82, 0, x_79);
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_79);
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_dec(x_82);
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
lean_dec(x_83);
x_2 = x_89;
x_7 = x_88;
goto _start;
}
}
else
{
uint8_t x_91; 
lean_dec(x_79);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_82);
if (x_91 == 0)
{
return x_82;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_82, 0);
x_93 = lean_ctor_get(x_82, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_82);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_77;
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_77, 0);
x_96 = lean_ctor_get(x_77, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_77);
x_97 = l_Lean_Expr_isAppOf(x_95, x_1);
if (x_97 == 0)
{
lean_object* x_98; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_95);
x_98 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_95, x_3, x_4, x_5, x_6, x_96);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_95);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_95);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_dec(x_98);
x_104 = lean_ctor_get(x_99, 0);
lean_inc(x_104);
lean_dec(x_99);
x_2 = x_104;
x_7 = x_103;
goto _start;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_95);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_106 = lean_ctor_get(x_98, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_98, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_108 = x_98;
} else {
 lean_dec_ref(x_98);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_95);
lean_ctor_set(x_110, 1, x_96);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = !lean_is_exclusive(x_77);
if (x_111 == 0)
{
return x_77;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_77, 0);
x_113 = lean_ctor_get(x_77, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_77);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
case 8:
{
lean_object* x_115; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_115 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = l_Lean_Expr_isAppOf(x_117, x_1);
if (x_119 == 0)
{
lean_object* x_120; 
lean_free_object(x_115);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_117);
x_120 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_117, x_3, x_4, x_5, x_6, x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_122 = !lean_is_exclusive(x_120);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_120, 0);
lean_dec(x_123);
lean_ctor_set(x_120, 0, x_117);
return x_120;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
lean_dec(x_120);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_117);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_117);
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
lean_dec(x_120);
x_127 = lean_ctor_get(x_121, 0);
lean_inc(x_127);
lean_dec(x_121);
x_2 = x_127;
x_7 = x_126;
goto _start;
}
}
else
{
uint8_t x_129; 
lean_dec(x_117);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_129 = !lean_is_exclusive(x_120);
if (x_129 == 0)
{
return x_120;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_120, 0);
x_131 = lean_ctor_get(x_120, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_120);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_115;
}
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_115, 0);
x_134 = lean_ctor_get(x_115, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_115);
x_135 = l_Lean_Expr_isAppOf(x_133, x_1);
if (x_135 == 0)
{
lean_object* x_136; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_133);
x_136 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_133, x_3, x_4, x_5, x_6, x_134);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_133);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_133);
x_141 = lean_ctor_get(x_136, 1);
lean_inc(x_141);
lean_dec(x_136);
x_142 = lean_ctor_get(x_137, 0);
lean_inc(x_142);
lean_dec(x_137);
x_2 = x_142;
x_7 = x_141;
goto _start;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_144 = lean_ctor_get(x_136, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_136, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_146 = x_136;
} else {
 lean_dec_ref(x_136);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_133);
lean_ctor_set(x_148, 1, x_134);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_149 = !lean_is_exclusive(x_115);
if (x_149 == 0)
{
return x_115;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_115, 0);
x_151 = lean_ctor_get(x_115, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_115);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
case 10:
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_2, 1);
lean_inc(x_153);
lean_dec(x_2);
x_2 = x_153;
goto _start;
}
case 11:
{
lean_object* x_155; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_155 = l_Lean_WHNF_whnfCore___main___at___private_Lean_Meta_WHNF_3__whnfCoreImp___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = lean_ctor_get(x_155, 1);
x_159 = l_Lean_Expr_isAppOf(x_157, x_1);
if (x_159 == 0)
{
lean_object* x_160; 
lean_free_object(x_155);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_157);
x_160 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_157, x_3, x_4, x_5, x_6, x_158);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
uint8_t x_162; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_162 = !lean_is_exclusive(x_160);
if (x_162 == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_160, 0);
lean_dec(x_163);
lean_ctor_set(x_160, 0, x_157);
return x_160;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
lean_dec(x_160);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_157);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_157);
x_166 = lean_ctor_get(x_160, 1);
lean_inc(x_166);
lean_dec(x_160);
x_167 = lean_ctor_get(x_161, 0);
lean_inc(x_167);
lean_dec(x_161);
x_2 = x_167;
x_7 = x_166;
goto _start;
}
}
else
{
uint8_t x_169; 
lean_dec(x_157);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_169 = !lean_is_exclusive(x_160);
if (x_169 == 0)
{
return x_160;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_160, 0);
x_171 = lean_ctor_get(x_160, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_160);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_155;
}
}
else
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_173 = lean_ctor_get(x_155, 0);
x_174 = lean_ctor_get(x_155, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_155);
x_175 = l_Lean_Expr_isAppOf(x_173, x_1);
if (x_175 == 0)
{
lean_object* x_176; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_173);
x_176 = l_Lean_WHNF_unfoldDefinitionAux___at___private_Lean_Meta_WHNF_2__unfoldDefinitionImp_x3f___spec__2(x_173, x_3, x_4, x_5, x_6, x_174);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_173);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_173);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec(x_176);
x_182 = lean_ctor_get(x_177, 0);
lean_inc(x_182);
lean_dec(x_177);
x_2 = x_182;
x_7 = x_181;
goto _start;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_173);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_184 = lean_ctor_get(x_176, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_176, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_186 = x_176;
} else {
 lean_dec_ref(x_176);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
lean_object* x_188; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_173);
lean_ctor_set(x_188, 1, x_174);
return x_188;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_189 = !lean_is_exclusive(x_155);
if (x_189 == 0)
{
return x_155;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_155, 0);
x_191 = lean_ctor_get(x_155, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_155);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
case 12:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_2);
x_193 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_whnfImpl___main___spec__1___closed__1;
x_194 = l_unreachable_x21___rarg(x_193);
x_195 = lean_apply_5(x_194, x_3, x_4, x_5, x_6, x_7);
return x_195;
}
default: 
{
lean_object* x_196; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_2);
lean_ctor_set(x_196, 1, x_7);
return x_196;
}
}
}
}
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_induction___spec__3(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Expr_isAppOf(x_10, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
x_12 = lean_box(0);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = l_Lean_Expr_isAppOf(x_14, x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise type is ill-formed");
return x_1;
}
}
lean_object* _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_23 = l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3;
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
uint8_t l_List_elem___main___at_Lean_Meta_induction___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is an index in major premise, but it depends on index occurring at position #");
return x_1;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is an index in major premise, but it occurs in previous arguments");
return x_1;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is an index in major premise, but it occurs more than once");
return x_1;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
x_85 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9;
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
x_27 = l_List_elem___main___at_Lean_Meta_induction___spec__5(x_21, x_6);
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
x_32 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_31, x_11, x_12, x_13, x_14, x_24);
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
x_42 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3;
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
x_68 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6;
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
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise type index ");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" is not variable ");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_8);
x_15 = lean_nat_dec_lt(x_7, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
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
x_58 = l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3;
x_59 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_box(0);
x_61 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_59, x_60, x_9, x_10, x_11, x_12, x_13);
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
x_41 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6;
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
lean_inc(x_22);
lean_inc(x_25);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_21, x_25, x_22, x_22, x_9, x_10, x_11, x_12, x_26);
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
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Level_normalize___main(x_9);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = l_Lean_Level_normalize___main(x_11);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise is not of the form (C ...)");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("recursor '");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' can only eliminate into Prop");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
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
x_28 = l_List_foldlM___main___at_Lean_Meta_induction___spec__10(x_3, x_8, x_13, x_25, x_27, x_26, x_17, x_18, x_19, x_20, x_21);
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
x_36 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__9;
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
lean_inc(x_10);
x_51 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_10, x_12, x_17, x_18, x_19, x_20, x_50);
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
x_64 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_63, x_12, x_17, x_18, x_19, x_20, x_61);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_10);
x_67 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_10, x_65, x_17, x_18, x_19, x_20, x_66);
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
lean_inc(x_10);
x_91 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_10, x_12, x_17, x_18, x_19, x_20, x_90);
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
x_104 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_103, x_12, x_17, x_18, x_19, x_20, x_101);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_10);
x_107 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_10, x_105, x_17, x_18, x_19, x_20, x_106);
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
x_134 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3;
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
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_20 = l___private_Lean_Meta_InferType_4__getLevelImp(x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9(x_21, x_15, x_16, x_17, x_18, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_1, x_15, x_16, x_17, x_18, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_LocalDecl_type(x_27);
lean_dec(x_27);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_29);
x_30 = l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(x_29, x_2, x_15, x_16, x_17, x_18, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(x_3, x_29, x_15, x_16, x_17, x_18, x_32);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_29);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_Expr_getAppNumArgsAux___main(x_35, x_36);
x_38 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_37);
x_39 = lean_mk_array(x_37, x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_37, x_40);
lean_dec(x_37);
x_42 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_3, x_11, x_12, x_13, x_14, x_24, x_35, x_39, x_41, x_15, x_16, x_17, x_18, x_34);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_29);
lean_dec(x_24);
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
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_24);
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
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
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
x_51 = !lean_is_exclusive(x_20);
if (x_51 == 0)
{
return x_20;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_20, 0);
x_53 = lean_ctor_get(x_20, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_20);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after revert&intro");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not support dependent elimination, but conclusion depends on major premise");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
lean_dec(x_12);
x_20 = lean_ctor_get(x_9, 5);
lean_inc(x_20);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_1);
x_21 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_8, x_11, x_13, x_20, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_16, x_17, x_18, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_9, 6);
lean_inc(x_26);
x_27 = l_List_redLength___main___rarg(x_26);
x_28 = lean_mk_empty_array_with_capacity(x_27);
lean_dec(x_27);
lean_inc(x_26);
x_29 = l_List_toArrayAux___main___rarg(x_26, x_28);
x_30 = x_29;
x_31 = lean_unsigned_to_nat(0u);
lean_inc(x_24);
lean_inc(x_8);
lean_inc(x_1);
x_32 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_32, 0, x_1);
lean_closure_set(x_32, 1, x_8);
lean_closure_set(x_32, 2, x_11);
lean_closure_set(x_32, 3, x_13);
lean_closure_set(x_32, 4, x_24);
lean_closure_set(x_32, 5, x_26);
lean_closure_set(x_32, 6, x_31);
lean_closure_set(x_32, 7, x_30);
x_33 = x_32;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_34 = lean_apply_5(x_33, x_15, x_16, x_17, x_18, x_25);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_1);
x_37 = l_Lean_Meta_getMVarType(x_1, x_15, x_16, x_17, x_18, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
if (x_40 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = l_Lean_MetavarContext_exprDependsOn(x_24, x_38, x_2);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
x_41 = x_39;
goto block_132;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_135 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_135, 0, x_3);
x_136 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_137 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__8;
x_139 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_box(0);
x_141 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_1, x_139, x_140, x_15, x_16, x_17, x_18, x_39);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
return x_141;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_141, 0);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_141);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
lean_dec(x_38);
lean_dec(x_24);
x_41 = x_39;
goto block_132;
}
block_132:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
lean_inc(x_35);
x_42 = x_35;
x_43 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_31, x_42);
x_44 = x_43;
x_45 = lean_array_push(x_44, x_2);
x_46 = 1;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_47 = l_Lean_Meta_revert(x_1, x_45, x_46, x_15, x_16, x_17, x_18, x_41);
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
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_55 = l_Lean_Meta_introN(x_51, x_52, x_53, x_54, x_15, x_16, x_17, x_18, x_49);
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
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_60 = l_Lean_Meta_intro1(x_59, x_54, x_15, x_16, x_17, x_18, x_57);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_95; lean_object* x_96; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
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
x_66 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_35, x_58, x_35, x_31, x_65);
lean_dec(x_35);
x_104 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_105 = lean_ctor_get(x_104, 2);
lean_inc(x_105);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_106 = lean_apply_5(x_105, x_15, x_16, x_17, x_18, x_62);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_107, sizeof(void*)*1);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
x_95 = x_54;
x_96 = x_109;
goto block_103;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
lean_dec(x_106);
x_111 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_112 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_111, x_15, x_16, x_17, x_18, x_110);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_unbox(x_113);
lean_dec(x_113);
x_95 = x_115;
x_96 = x_114;
goto block_103;
}
}
else
{
uint8_t x_116; 
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_116 = !lean_is_exclusive(x_106);
if (x_116 == 0)
{
return x_106;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_106, 0);
x_118 = lean_ctor_get(x_106, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_106);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
block_94:
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
x_74 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 19, 13);
lean_closure_set(x_74, 0, x_63);
lean_closure_set(x_74, 1, x_10);
lean_closure_set(x_74, 2, x_64);
lean_closure_set(x_74, 3, x_3);
lean_closure_set(x_74, 4, x_4);
lean_closure_set(x_74, 5, x_8);
lean_closure_set(x_74, 6, x_9);
lean_closure_set(x_74, 7, x_20);
lean_closure_set(x_74, 8, x_73);
lean_closure_set(x_74, 9, x_50);
lean_closure_set(x_74, 10, x_66);
lean_closure_set(x_74, 11, x_70);
lean_closure_set(x_74, 12, x_71);
x_75 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_75, 0, x_72);
lean_closure_set(x_75, 1, x_74);
x_76 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_64, x_15, x_16, x_17, x_18, x_67);
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
x_81 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_79, x_80, x_75, x_15, x_16, x_17, x_18, x_78);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
return x_81;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_81);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_81);
if (x_86 == 0)
{
return x_81;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_81, 0);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_81);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_75);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_90 = !lean_is_exclusive(x_76);
if (x_90 == 0)
{
return x_76;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_76, 0);
x_92 = lean_ctor_get(x_76, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_76);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
block_103:
{
if (x_95 == 0)
{
x_67 = x_96;
goto block_94;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_inc(x_64);
x_97 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_97, 0, x_64);
x_98 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__5;
x_99 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_101 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_100, x_99, x_15, x_16, x_17, x_18, x_96);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_67 = x_102;
goto block_94;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_120 = !lean_is_exclusive(x_60);
if (x_120 == 0)
{
return x_60;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_60, 0);
x_122 = lean_ctor_get(x_60, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_60);
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
lean_dec(x_50);
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_124 = !lean_is_exclusive(x_55);
if (x_124 == 0)
{
return x_55;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_55, 0);
x_126 = lean_ctor_get(x_55, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_55);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_128 = !lean_is_exclusive(x_47);
if (x_128 == 0)
{
return x_47;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_47, 0);
x_130 = lean_ctor_get(x_47, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_47);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_146 = !lean_is_exclusive(x_37);
if (x_146 == 0)
{
return x_37;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_37, 0);
x_148 = lean_ctor_get(x_37, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_37);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_34);
if (x_150 == 0)
{
return x_34;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_34, 0);
x_152 = lean_ctor_get(x_34, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_34);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_154 = !lean_is_exclusive(x_21);
if (x_154 == 0)
{
return x_21;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_21, 0);
x_156 = lean_ctor_get(x_21, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_21);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
case 1:
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_14);
lean_dec(x_12);
x_158 = lean_ctor_get(x_9, 5);
lean_inc(x_158);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_1);
x_159 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_8, x_11, x_13, x_158, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
x_161 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_16, x_17, x_18, x_160);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get(x_9, 6);
lean_inc(x_164);
x_165 = l_List_redLength___main___rarg(x_164);
x_166 = lean_mk_empty_array_with_capacity(x_165);
lean_dec(x_165);
lean_inc(x_164);
x_167 = l_List_toArrayAux___main___rarg(x_164, x_166);
x_168 = x_167;
x_169 = lean_unsigned_to_nat(0u);
lean_inc(x_162);
lean_inc(x_8);
lean_inc(x_1);
x_170 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_170, 0, x_1);
lean_closure_set(x_170, 1, x_8);
lean_closure_set(x_170, 2, x_11);
lean_closure_set(x_170, 3, x_13);
lean_closure_set(x_170, 4, x_162);
lean_closure_set(x_170, 5, x_164);
lean_closure_set(x_170, 6, x_169);
lean_closure_set(x_170, 7, x_168);
x_171 = x_170;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_172 = lean_apply_5(x_171, x_15, x_16, x_17, x_18, x_163);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
lean_inc(x_1);
x_175 = l_Lean_Meta_getMVarType(x_1, x_15, x_16, x_17, x_18, x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
if (x_178 == 0)
{
lean_object* x_271; uint8_t x_272; 
x_271 = l_Lean_MetavarContext_exprDependsOn(x_162, x_176, x_2);
x_272 = lean_unbox(x_271);
lean_dec(x_271);
if (x_272 == 0)
{
x_179 = x_177;
goto block_270;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
lean_dec(x_173);
lean_dec(x_158);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_273 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_273, 0, x_3);
x_274 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_275 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_273);
x_276 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__8;
x_277 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_box(0);
x_279 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_1, x_277, x_278, x_15, x_16, x_17, x_18, x_177);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_280 = !lean_is_exclusive(x_279);
if (x_280 == 0)
{
return x_279;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_279, 0);
x_282 = lean_ctor_get(x_279, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_279);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
return x_283;
}
}
}
else
{
lean_dec(x_176);
lean_dec(x_162);
x_179 = x_177;
goto block_270;
}
block_270:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; 
lean_inc(x_173);
x_180 = x_173;
x_181 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_169, x_180);
x_182 = x_181;
x_183 = lean_array_push(x_182, x_2);
x_184 = 1;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_185 = l_Lean_Meta_revert(x_1, x_183, x_184, x_15, x_16, x_17, x_18, x_179);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; 
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
x_190 = lean_array_get_size(x_173);
x_191 = lean_box(0);
x_192 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_193 = l_Lean_Meta_introN(x_189, x_190, x_191, x_192, x_15, x_16, x_17, x_18, x_187);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_ctor_get(x_194, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
lean_dec(x_194);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_198 = l_Lean_Meta_intro1(x_197, x_192, x_15, x_16, x_17, x_18, x_195);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_233; lean_object* x_234; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = lean_ctor_get(x_199, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
lean_dec(x_199);
x_203 = lean_box(0);
x_204 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_173, x_196, x_173, x_169, x_203);
lean_dec(x_173);
x_242 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_243 = lean_ctor_get(x_242, 2);
lean_inc(x_243);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_244 = lean_apply_5(x_243, x_15, x_16, x_17, x_18, x_200);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; uint8_t x_246; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get_uint8(x_245, sizeof(void*)*1);
lean_dec(x_245);
if (x_246 == 0)
{
lean_object* x_247; 
x_247 = lean_ctor_get(x_244, 1);
lean_inc(x_247);
lean_dec(x_244);
x_233 = x_192;
x_234 = x_247;
goto block_241;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_248 = lean_ctor_get(x_244, 1);
lean_inc(x_248);
lean_dec(x_244);
x_249 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_250 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_249, x_15, x_16, x_17, x_18, x_248);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_unbox(x_251);
lean_dec(x_251);
x_233 = x_253;
x_234 = x_252;
goto block_241;
}
}
else
{
uint8_t x_254; 
lean_dec(x_204);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_196);
lean_dec(x_188);
lean_dec(x_158);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_254 = !lean_is_exclusive(x_244);
if (x_254 == 0)
{
return x_244;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_244, 0);
x_256 = lean_ctor_get(x_244, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_244);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
block_232:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_206 = x_196;
x_207 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_169, x_206);
x_208 = x_207;
lean_inc(x_201);
x_209 = l_Lean_mkFVar(x_201);
lean_inc(x_202);
x_210 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_210, 0, x_202);
x_211 = lean_box(x_178);
lean_inc(x_202);
x_212 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 19, 13);
lean_closure_set(x_212, 0, x_201);
lean_closure_set(x_212, 1, x_10);
lean_closure_set(x_212, 2, x_202);
lean_closure_set(x_212, 3, x_3);
lean_closure_set(x_212, 4, x_4);
lean_closure_set(x_212, 5, x_8);
lean_closure_set(x_212, 6, x_9);
lean_closure_set(x_212, 7, x_158);
lean_closure_set(x_212, 8, x_211);
lean_closure_set(x_212, 9, x_188);
lean_closure_set(x_212, 10, x_204);
lean_closure_set(x_212, 11, x_208);
lean_closure_set(x_212, 12, x_209);
x_213 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_213, 0, x_210);
lean_closure_set(x_213, 1, x_212);
x_214 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_202, x_15, x_16, x_17, x_18, x_205);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_215, 4);
lean_inc(x_218);
lean_dec(x_215);
x_219 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_217, x_218, x_213, x_15, x_16, x_17, x_18, x_216);
if (lean_obj_tag(x_219) == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_219);
if (x_220 == 0)
{
return x_219;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_219, 0);
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_219);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
else
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_219);
if (x_224 == 0)
{
return x_219;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_219, 0);
x_226 = lean_ctor_get(x_219, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_219);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_213);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_228 = !lean_is_exclusive(x_214);
if (x_228 == 0)
{
return x_214;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_214, 0);
x_230 = lean_ctor_get(x_214, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_214);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
block_241:
{
if (x_233 == 0)
{
x_205 = x_234;
goto block_232;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_inc(x_202);
x_235 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_235, 0, x_202);
x_236 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__5;
x_237 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_235);
x_238 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_239 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_238, x_237, x_15, x_16, x_17, x_18, x_234);
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
x_205 = x_240;
goto block_232;
}
}
}
else
{
uint8_t x_258; 
lean_dec(x_196);
lean_dec(x_188);
lean_dec(x_173);
lean_dec(x_158);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_258 = !lean_is_exclusive(x_198);
if (x_258 == 0)
{
return x_198;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_198, 0);
x_260 = lean_ctor_get(x_198, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_198);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
else
{
uint8_t x_262; 
lean_dec(x_188);
lean_dec(x_173);
lean_dec(x_158);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_262 = !lean_is_exclusive(x_193);
if (x_262 == 0)
{
return x_193;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_193, 0);
x_264 = lean_ctor_get(x_193, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_193);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_173);
lean_dec(x_158);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_266 = !lean_is_exclusive(x_185);
if (x_266 == 0)
{
return x_185;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_185, 0);
x_268 = lean_ctor_get(x_185, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_185);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
}
else
{
uint8_t x_284; 
lean_dec(x_173);
lean_dec(x_162);
lean_dec(x_158);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_284 = !lean_is_exclusive(x_175);
if (x_284 == 0)
{
return x_175;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_175, 0);
x_286 = lean_ctor_get(x_175, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_175);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
return x_287;
}
}
}
else
{
uint8_t x_288; 
lean_dec(x_162);
lean_dec(x_158);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_288 = !lean_is_exclusive(x_172);
if (x_288 == 0)
{
return x_172;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_172, 0);
x_290 = lean_ctor_get(x_172, 1);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_172);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
return x_291;
}
}
}
else
{
uint8_t x_292; 
lean_dec(x_158);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_292 = !lean_is_exclusive(x_159);
if (x_292 == 0)
{
return x_159;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_159, 0);
x_294 = lean_ctor_get(x_159, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_159);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
case 2:
{
lean_object* x_296; lean_object* x_297; 
lean_dec(x_14);
lean_dec(x_12);
x_296 = lean_ctor_get(x_9, 5);
lean_inc(x_296);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_1);
x_297 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_8, x_11, x_13, x_296, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
lean_dec(x_297);
x_299 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_16, x_17, x_18, x_298);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_ctor_get(x_9, 6);
lean_inc(x_302);
x_303 = l_List_redLength___main___rarg(x_302);
x_304 = lean_mk_empty_array_with_capacity(x_303);
lean_dec(x_303);
lean_inc(x_302);
x_305 = l_List_toArrayAux___main___rarg(x_302, x_304);
x_306 = x_305;
x_307 = lean_unsigned_to_nat(0u);
lean_inc(x_300);
lean_inc(x_8);
lean_inc(x_1);
x_308 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_308, 0, x_1);
lean_closure_set(x_308, 1, x_8);
lean_closure_set(x_308, 2, x_11);
lean_closure_set(x_308, 3, x_13);
lean_closure_set(x_308, 4, x_300);
lean_closure_set(x_308, 5, x_302);
lean_closure_set(x_308, 6, x_307);
lean_closure_set(x_308, 7, x_306);
x_309 = x_308;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_310 = lean_apply_5(x_309, x_15, x_16, x_17, x_18, x_301);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
lean_inc(x_1);
x_313 = l_Lean_Meta_getMVarType(x_1, x_15, x_16, x_17, x_18, x_312);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; lean_object* x_317; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
if (x_316 == 0)
{
lean_object* x_409; uint8_t x_410; 
x_409 = l_Lean_MetavarContext_exprDependsOn(x_300, x_314, x_2);
x_410 = lean_unbox(x_409);
lean_dec(x_409);
if (x_410 == 0)
{
x_317 = x_315;
goto block_408;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
lean_dec(x_311);
lean_dec(x_296);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_411 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_411, 0, x_3);
x_412 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_413 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_411);
x_414 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__8;
x_415 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
x_416 = lean_box(0);
x_417 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_1, x_415, x_416, x_15, x_16, x_17, x_18, x_315);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_418 = !lean_is_exclusive(x_417);
if (x_418 == 0)
{
return x_417;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_417, 0);
x_420 = lean_ctor_get(x_417, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_417);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
}
}
else
{
lean_dec(x_314);
lean_dec(x_300);
x_317 = x_315;
goto block_408;
}
block_408:
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; 
lean_inc(x_311);
x_318 = x_311;
x_319 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_307, x_318);
x_320 = x_319;
x_321 = lean_array_push(x_320, x_2);
x_322 = 1;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_323 = l_Lean_Meta_revert(x_1, x_321, x_322, x_15, x_16, x_17, x_18, x_317);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; lean_object* x_331; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_326 = lean_ctor_get(x_324, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_324, 1);
lean_inc(x_327);
lean_dec(x_324);
x_328 = lean_array_get_size(x_311);
x_329 = lean_box(0);
x_330 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_331 = l_Lean_Meta_introN(x_327, x_328, x_329, x_330, x_15, x_16, x_17, x_18, x_325);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = lean_ctor_get(x_332, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_332, 1);
lean_inc(x_335);
lean_dec(x_332);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_336 = l_Lean_Meta_intro1(x_335, x_330, x_15, x_16, x_17, x_18, x_333);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_371; lean_object* x_372; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec(x_336);
x_339 = lean_ctor_get(x_337, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_337, 1);
lean_inc(x_340);
lean_dec(x_337);
x_341 = lean_box(0);
x_342 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_311, x_334, x_311, x_307, x_341);
lean_dec(x_311);
x_380 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_381 = lean_ctor_get(x_380, 2);
lean_inc(x_381);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_382 = lean_apply_5(x_381, x_15, x_16, x_17, x_18, x_338);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; uint8_t x_384; 
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get_uint8(x_383, sizeof(void*)*1);
lean_dec(x_383);
if (x_384 == 0)
{
lean_object* x_385; 
x_385 = lean_ctor_get(x_382, 1);
lean_inc(x_385);
lean_dec(x_382);
x_371 = x_330;
x_372 = x_385;
goto block_379;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; 
x_386 = lean_ctor_get(x_382, 1);
lean_inc(x_386);
lean_dec(x_382);
x_387 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_388 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_387, x_15, x_16, x_17, x_18, x_386);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = lean_unbox(x_389);
lean_dec(x_389);
x_371 = x_391;
x_372 = x_390;
goto block_379;
}
}
else
{
uint8_t x_392; 
lean_dec(x_342);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_334);
lean_dec(x_326);
lean_dec(x_296);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_392 = !lean_is_exclusive(x_382);
if (x_392 == 0)
{
return x_382;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_382, 0);
x_394 = lean_ctor_get(x_382, 1);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_382);
x_395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
return x_395;
}
}
block_370:
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_344 = x_334;
x_345 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_307, x_344);
x_346 = x_345;
lean_inc(x_339);
x_347 = l_Lean_mkFVar(x_339);
lean_inc(x_340);
x_348 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_348, 0, x_340);
x_349 = lean_box(x_316);
lean_inc(x_340);
x_350 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 19, 13);
lean_closure_set(x_350, 0, x_339);
lean_closure_set(x_350, 1, x_10);
lean_closure_set(x_350, 2, x_340);
lean_closure_set(x_350, 3, x_3);
lean_closure_set(x_350, 4, x_4);
lean_closure_set(x_350, 5, x_8);
lean_closure_set(x_350, 6, x_9);
lean_closure_set(x_350, 7, x_296);
lean_closure_set(x_350, 8, x_349);
lean_closure_set(x_350, 9, x_326);
lean_closure_set(x_350, 10, x_342);
lean_closure_set(x_350, 11, x_346);
lean_closure_set(x_350, 12, x_347);
x_351 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_351, 0, x_348);
lean_closure_set(x_351, 1, x_350);
x_352 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_340, x_15, x_16, x_17, x_18, x_343);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_353, 4);
lean_inc(x_356);
lean_dec(x_353);
x_357 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_355, x_356, x_351, x_15, x_16, x_17, x_18, x_354);
if (lean_obj_tag(x_357) == 0)
{
uint8_t x_358; 
x_358 = !lean_is_exclusive(x_357);
if (x_358 == 0)
{
return x_357;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_357, 0);
x_360 = lean_ctor_get(x_357, 1);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_357);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
return x_361;
}
}
else
{
uint8_t x_362; 
x_362 = !lean_is_exclusive(x_357);
if (x_362 == 0)
{
return x_357;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_357, 0);
x_364 = lean_ctor_get(x_357, 1);
lean_inc(x_364);
lean_inc(x_363);
lean_dec(x_357);
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
lean_dec(x_351);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_366 = !lean_is_exclusive(x_352);
if (x_366 == 0)
{
return x_352;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_352, 0);
x_368 = lean_ctor_get(x_352, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_352);
x_369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
return x_369;
}
}
}
block_379:
{
if (x_371 == 0)
{
x_343 = x_372;
goto block_370;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_inc(x_340);
x_373 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_373, 0, x_340);
x_374 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__5;
x_375 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_373);
x_376 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_377 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_376, x_375, x_15, x_16, x_17, x_18, x_372);
x_378 = lean_ctor_get(x_377, 1);
lean_inc(x_378);
lean_dec(x_377);
x_343 = x_378;
goto block_370;
}
}
}
else
{
uint8_t x_396; 
lean_dec(x_334);
lean_dec(x_326);
lean_dec(x_311);
lean_dec(x_296);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_396 = !lean_is_exclusive(x_336);
if (x_396 == 0)
{
return x_336;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_336, 0);
x_398 = lean_ctor_get(x_336, 1);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_336);
x_399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_399, 1, x_398);
return x_399;
}
}
}
else
{
uint8_t x_400; 
lean_dec(x_326);
lean_dec(x_311);
lean_dec(x_296);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_400 = !lean_is_exclusive(x_331);
if (x_400 == 0)
{
return x_331;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_331, 0);
x_402 = lean_ctor_get(x_331, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_331);
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
return x_403;
}
}
}
else
{
uint8_t x_404; 
lean_dec(x_311);
lean_dec(x_296);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_404 = !lean_is_exclusive(x_323);
if (x_404 == 0)
{
return x_323;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_405 = lean_ctor_get(x_323, 0);
x_406 = lean_ctor_get(x_323, 1);
lean_inc(x_406);
lean_inc(x_405);
lean_dec(x_323);
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_406);
return x_407;
}
}
}
}
else
{
uint8_t x_422; 
lean_dec(x_311);
lean_dec(x_300);
lean_dec(x_296);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_422 = !lean_is_exclusive(x_313);
if (x_422 == 0)
{
return x_313;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_313, 0);
x_424 = lean_ctor_get(x_313, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_313);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
return x_425;
}
}
}
else
{
uint8_t x_426; 
lean_dec(x_300);
lean_dec(x_296);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_426 = !lean_is_exclusive(x_310);
if (x_426 == 0)
{
return x_310;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_310, 0);
x_428 = lean_ctor_get(x_310, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_310);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
else
{
uint8_t x_430; 
lean_dec(x_296);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_430 = !lean_is_exclusive(x_297);
if (x_430 == 0)
{
return x_297;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_297, 0);
x_432 = lean_ctor_get(x_297, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_297);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
return x_433;
}
}
}
case 3:
{
lean_object* x_434; lean_object* x_435; 
lean_dec(x_14);
lean_dec(x_12);
x_434 = lean_ctor_get(x_9, 5);
lean_inc(x_434);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_1);
x_435 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_8, x_11, x_13, x_434, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_436 = lean_ctor_get(x_435, 1);
lean_inc(x_436);
lean_dec(x_435);
x_437 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_16, x_17, x_18, x_436);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
lean_dec(x_437);
x_440 = lean_ctor_get(x_9, 6);
lean_inc(x_440);
x_441 = l_List_redLength___main___rarg(x_440);
x_442 = lean_mk_empty_array_with_capacity(x_441);
lean_dec(x_441);
lean_inc(x_440);
x_443 = l_List_toArrayAux___main___rarg(x_440, x_442);
x_444 = x_443;
x_445 = lean_unsigned_to_nat(0u);
lean_inc(x_438);
lean_inc(x_8);
lean_inc(x_1);
x_446 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_446, 0, x_1);
lean_closure_set(x_446, 1, x_8);
lean_closure_set(x_446, 2, x_11);
lean_closure_set(x_446, 3, x_13);
lean_closure_set(x_446, 4, x_438);
lean_closure_set(x_446, 5, x_440);
lean_closure_set(x_446, 6, x_445);
lean_closure_set(x_446, 7, x_444);
x_447 = x_446;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_448 = lean_apply_5(x_447, x_15, x_16, x_17, x_18, x_439);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
lean_inc(x_1);
x_451 = l_Lean_Meta_getMVarType(x_1, x_15, x_16, x_17, x_18, x_450);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_454 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
if (x_454 == 0)
{
lean_object* x_547; uint8_t x_548; 
x_547 = l_Lean_MetavarContext_exprDependsOn(x_438, x_452, x_2);
x_548 = lean_unbox(x_547);
lean_dec(x_547);
if (x_548 == 0)
{
x_455 = x_453;
goto block_546;
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; uint8_t x_556; 
lean_dec(x_449);
lean_dec(x_434);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_549 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_549, 0, x_3);
x_550 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_551 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_551, 0, x_550);
lean_ctor_set(x_551, 1, x_549);
x_552 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__8;
x_553 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_553, 0, x_551);
lean_ctor_set(x_553, 1, x_552);
x_554 = lean_box(0);
x_555 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_1, x_553, x_554, x_15, x_16, x_17, x_18, x_453);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_556 = !lean_is_exclusive(x_555);
if (x_556 == 0)
{
return x_555;
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_557 = lean_ctor_get(x_555, 0);
x_558 = lean_ctor_get(x_555, 1);
lean_inc(x_558);
lean_inc(x_557);
lean_dec(x_555);
x_559 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_559, 0, x_557);
lean_ctor_set(x_559, 1, x_558);
return x_559;
}
}
}
else
{
lean_dec(x_452);
lean_dec(x_438);
x_455 = x_453;
goto block_546;
}
block_546:
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; uint8_t x_460; lean_object* x_461; 
lean_inc(x_449);
x_456 = x_449;
x_457 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_445, x_456);
x_458 = x_457;
x_459 = lean_array_push(x_458, x_2);
x_460 = 1;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_461 = l_Lean_Meta_revert(x_1, x_459, x_460, x_15, x_16, x_17, x_18, x_455);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; uint8_t x_468; lean_object* x_469; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
lean_dec(x_461);
x_464 = lean_ctor_get(x_462, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_462, 1);
lean_inc(x_465);
lean_dec(x_462);
x_466 = lean_array_get_size(x_449);
x_467 = lean_box(0);
x_468 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_469 = l_Lean_Meta_introN(x_465, x_466, x_467, x_468, x_15, x_16, x_17, x_18, x_463);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
lean_dec(x_469);
x_472 = lean_ctor_get(x_470, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_470, 1);
lean_inc(x_473);
lean_dec(x_470);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_474 = l_Lean_Meta_intro1(x_473, x_468, x_15, x_16, x_17, x_18, x_471);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_509; lean_object* x_510; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
lean_dec(x_474);
x_477 = lean_ctor_get(x_475, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_475, 1);
lean_inc(x_478);
lean_dec(x_475);
x_479 = lean_box(0);
x_480 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_449, x_472, x_449, x_445, x_479);
lean_dec(x_449);
x_518 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_519 = lean_ctor_get(x_518, 2);
lean_inc(x_519);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_520 = lean_apply_5(x_519, x_15, x_16, x_17, x_18, x_476);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; uint8_t x_522; 
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
x_522 = lean_ctor_get_uint8(x_521, sizeof(void*)*1);
lean_dec(x_521);
if (x_522 == 0)
{
lean_object* x_523; 
x_523 = lean_ctor_get(x_520, 1);
lean_inc(x_523);
lean_dec(x_520);
x_509 = x_468;
x_510 = x_523;
goto block_517;
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; uint8_t x_529; 
x_524 = lean_ctor_get(x_520, 1);
lean_inc(x_524);
lean_dec(x_520);
x_525 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_526 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_525, x_15, x_16, x_17, x_18, x_524);
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_526, 1);
lean_inc(x_528);
lean_dec(x_526);
x_529 = lean_unbox(x_527);
lean_dec(x_527);
x_509 = x_529;
x_510 = x_528;
goto block_517;
}
}
else
{
uint8_t x_530; 
lean_dec(x_480);
lean_dec(x_478);
lean_dec(x_477);
lean_dec(x_472);
lean_dec(x_464);
lean_dec(x_434);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_530 = !lean_is_exclusive(x_520);
if (x_530 == 0)
{
return x_520;
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_531 = lean_ctor_get(x_520, 0);
x_532 = lean_ctor_get(x_520, 1);
lean_inc(x_532);
lean_inc(x_531);
lean_dec(x_520);
x_533 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_533, 0, x_531);
lean_ctor_set(x_533, 1, x_532);
return x_533;
}
}
block_508:
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_482 = x_472;
x_483 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_445, x_482);
x_484 = x_483;
lean_inc(x_477);
x_485 = l_Lean_mkFVar(x_477);
lean_inc(x_478);
x_486 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_486, 0, x_478);
x_487 = lean_box(x_454);
lean_inc(x_478);
x_488 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 19, 13);
lean_closure_set(x_488, 0, x_477);
lean_closure_set(x_488, 1, x_10);
lean_closure_set(x_488, 2, x_478);
lean_closure_set(x_488, 3, x_3);
lean_closure_set(x_488, 4, x_4);
lean_closure_set(x_488, 5, x_8);
lean_closure_set(x_488, 6, x_9);
lean_closure_set(x_488, 7, x_434);
lean_closure_set(x_488, 8, x_487);
lean_closure_set(x_488, 9, x_464);
lean_closure_set(x_488, 10, x_480);
lean_closure_set(x_488, 11, x_484);
lean_closure_set(x_488, 12, x_485);
x_489 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_489, 0, x_486);
lean_closure_set(x_489, 1, x_488);
x_490 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_478, x_15, x_16, x_17, x_18, x_481);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec(x_490);
x_493 = lean_ctor_get(x_491, 1);
lean_inc(x_493);
x_494 = lean_ctor_get(x_491, 4);
lean_inc(x_494);
lean_dec(x_491);
x_495 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_493, x_494, x_489, x_15, x_16, x_17, x_18, x_492);
if (lean_obj_tag(x_495) == 0)
{
uint8_t x_496; 
x_496 = !lean_is_exclusive(x_495);
if (x_496 == 0)
{
return x_495;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_497 = lean_ctor_get(x_495, 0);
x_498 = lean_ctor_get(x_495, 1);
lean_inc(x_498);
lean_inc(x_497);
lean_dec(x_495);
x_499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_499, 0, x_497);
lean_ctor_set(x_499, 1, x_498);
return x_499;
}
}
else
{
uint8_t x_500; 
x_500 = !lean_is_exclusive(x_495);
if (x_500 == 0)
{
return x_495;
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_501 = lean_ctor_get(x_495, 0);
x_502 = lean_ctor_get(x_495, 1);
lean_inc(x_502);
lean_inc(x_501);
lean_dec(x_495);
x_503 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_503, 0, x_501);
lean_ctor_set(x_503, 1, x_502);
return x_503;
}
}
}
else
{
uint8_t x_504; 
lean_dec(x_489);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_504 = !lean_is_exclusive(x_490);
if (x_504 == 0)
{
return x_490;
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_505 = lean_ctor_get(x_490, 0);
x_506 = lean_ctor_get(x_490, 1);
lean_inc(x_506);
lean_inc(x_505);
lean_dec(x_490);
x_507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_507, 0, x_505);
lean_ctor_set(x_507, 1, x_506);
return x_507;
}
}
}
block_517:
{
if (x_509 == 0)
{
x_481 = x_510;
goto block_508;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
lean_inc(x_478);
x_511 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_511, 0, x_478);
x_512 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__5;
x_513 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_513, 0, x_512);
lean_ctor_set(x_513, 1, x_511);
x_514 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_515 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_514, x_513, x_15, x_16, x_17, x_18, x_510);
x_516 = lean_ctor_get(x_515, 1);
lean_inc(x_516);
lean_dec(x_515);
x_481 = x_516;
goto block_508;
}
}
}
else
{
uint8_t x_534; 
lean_dec(x_472);
lean_dec(x_464);
lean_dec(x_449);
lean_dec(x_434);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_534 = !lean_is_exclusive(x_474);
if (x_534 == 0)
{
return x_474;
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_535 = lean_ctor_get(x_474, 0);
x_536 = lean_ctor_get(x_474, 1);
lean_inc(x_536);
lean_inc(x_535);
lean_dec(x_474);
x_537 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_537, 0, x_535);
lean_ctor_set(x_537, 1, x_536);
return x_537;
}
}
}
else
{
uint8_t x_538; 
lean_dec(x_464);
lean_dec(x_449);
lean_dec(x_434);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_538 = !lean_is_exclusive(x_469);
if (x_538 == 0)
{
return x_469;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_539 = lean_ctor_get(x_469, 0);
x_540 = lean_ctor_get(x_469, 1);
lean_inc(x_540);
lean_inc(x_539);
lean_dec(x_469);
x_541 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_541, 0, x_539);
lean_ctor_set(x_541, 1, x_540);
return x_541;
}
}
}
else
{
uint8_t x_542; 
lean_dec(x_449);
lean_dec(x_434);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_542 = !lean_is_exclusive(x_461);
if (x_542 == 0)
{
return x_461;
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_543 = lean_ctor_get(x_461, 0);
x_544 = lean_ctor_get(x_461, 1);
lean_inc(x_544);
lean_inc(x_543);
lean_dec(x_461);
x_545 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_545, 0, x_543);
lean_ctor_set(x_545, 1, x_544);
return x_545;
}
}
}
}
else
{
uint8_t x_560; 
lean_dec(x_449);
lean_dec(x_438);
lean_dec(x_434);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_560 = !lean_is_exclusive(x_451);
if (x_560 == 0)
{
return x_451;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_561 = lean_ctor_get(x_451, 0);
x_562 = lean_ctor_get(x_451, 1);
lean_inc(x_562);
lean_inc(x_561);
lean_dec(x_451);
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_561);
lean_ctor_set(x_563, 1, x_562);
return x_563;
}
}
}
else
{
uint8_t x_564; 
lean_dec(x_438);
lean_dec(x_434);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_564 = !lean_is_exclusive(x_448);
if (x_564 == 0)
{
return x_448;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_565 = lean_ctor_get(x_448, 0);
x_566 = lean_ctor_get(x_448, 1);
lean_inc(x_566);
lean_inc(x_565);
lean_dec(x_448);
x_567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_566);
return x_567;
}
}
}
else
{
uint8_t x_568; 
lean_dec(x_434);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_568 = !lean_is_exclusive(x_435);
if (x_568 == 0)
{
return x_435;
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_569 = lean_ctor_get(x_435, 0);
x_570 = lean_ctor_get(x_435, 1);
lean_inc(x_570);
lean_inc(x_569);
lean_dec(x_435);
x_571 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_571, 0, x_569);
lean_ctor_set(x_571, 1, x_570);
return x_571;
}
}
}
case 4:
{
lean_object* x_572; lean_object* x_573; 
lean_dec(x_14);
lean_dec(x_12);
x_572 = lean_ctor_get(x_9, 5);
lean_inc(x_572);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_1);
x_573 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_8, x_11, x_13, x_572, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_574 = lean_ctor_get(x_573, 1);
lean_inc(x_574);
lean_dec(x_573);
x_575 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_16, x_17, x_18, x_574);
x_576 = lean_ctor_get(x_575, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_575, 1);
lean_inc(x_577);
lean_dec(x_575);
x_578 = lean_ctor_get(x_9, 6);
lean_inc(x_578);
x_579 = l_List_redLength___main___rarg(x_578);
x_580 = lean_mk_empty_array_with_capacity(x_579);
lean_dec(x_579);
lean_inc(x_578);
x_581 = l_List_toArrayAux___main___rarg(x_578, x_580);
x_582 = x_581;
x_583 = lean_unsigned_to_nat(0u);
lean_inc(x_576);
lean_inc(x_8);
lean_inc(x_1);
x_584 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_584, 0, x_1);
lean_closure_set(x_584, 1, x_8);
lean_closure_set(x_584, 2, x_11);
lean_closure_set(x_584, 3, x_13);
lean_closure_set(x_584, 4, x_576);
lean_closure_set(x_584, 5, x_578);
lean_closure_set(x_584, 6, x_583);
lean_closure_set(x_584, 7, x_582);
x_585 = x_584;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_586 = lean_apply_5(x_585, x_15, x_16, x_17, x_18, x_577);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_586, 1);
lean_inc(x_588);
lean_dec(x_586);
lean_inc(x_1);
x_589 = l_Lean_Meta_getMVarType(x_1, x_15, x_16, x_17, x_18, x_588);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; uint8_t x_592; lean_object* x_593; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
lean_dec(x_589);
x_592 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
if (x_592 == 0)
{
lean_object* x_685; uint8_t x_686; 
x_685 = l_Lean_MetavarContext_exprDependsOn(x_576, x_590, x_2);
x_686 = lean_unbox(x_685);
lean_dec(x_685);
if (x_686 == 0)
{
x_593 = x_591;
goto block_684;
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; uint8_t x_694; 
lean_dec(x_587);
lean_dec(x_572);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_687 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_687, 0, x_3);
x_688 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_689 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_689, 0, x_688);
lean_ctor_set(x_689, 1, x_687);
x_690 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__8;
x_691 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_691, 0, x_689);
lean_ctor_set(x_691, 1, x_690);
x_692 = lean_box(0);
x_693 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_1, x_691, x_692, x_15, x_16, x_17, x_18, x_591);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_694 = !lean_is_exclusive(x_693);
if (x_694 == 0)
{
return x_693;
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_695 = lean_ctor_get(x_693, 0);
x_696 = lean_ctor_get(x_693, 1);
lean_inc(x_696);
lean_inc(x_695);
lean_dec(x_693);
x_697 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_697, 0, x_695);
lean_ctor_set(x_697, 1, x_696);
return x_697;
}
}
}
else
{
lean_dec(x_590);
lean_dec(x_576);
x_593 = x_591;
goto block_684;
}
block_684:
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; uint8_t x_598; lean_object* x_599; 
lean_inc(x_587);
x_594 = x_587;
x_595 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_583, x_594);
x_596 = x_595;
x_597 = lean_array_push(x_596, x_2);
x_598 = 1;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_599 = l_Lean_Meta_revert(x_1, x_597, x_598, x_15, x_16, x_17, x_18, x_593);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; uint8_t x_606; lean_object* x_607; 
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
x_602 = lean_ctor_get(x_600, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_600, 1);
lean_inc(x_603);
lean_dec(x_600);
x_604 = lean_array_get_size(x_587);
x_605 = lean_box(0);
x_606 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_607 = l_Lean_Meta_introN(x_603, x_604, x_605, x_606, x_15, x_16, x_17, x_18, x_601);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_607, 1);
lean_inc(x_609);
lean_dec(x_607);
x_610 = lean_ctor_get(x_608, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_608, 1);
lean_inc(x_611);
lean_dec(x_608);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_612 = l_Lean_Meta_intro1(x_611, x_606, x_15, x_16, x_17, x_18, x_609);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; uint8_t x_647; lean_object* x_648; lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
lean_dec(x_612);
x_615 = lean_ctor_get(x_613, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_613, 1);
lean_inc(x_616);
lean_dec(x_613);
x_617 = lean_box(0);
x_618 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_587, x_610, x_587, x_583, x_617);
lean_dec(x_587);
x_656 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_657 = lean_ctor_get(x_656, 2);
lean_inc(x_657);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_658 = lean_apply_5(x_657, x_15, x_16, x_17, x_18, x_614);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; uint8_t x_660; 
x_659 = lean_ctor_get(x_658, 0);
lean_inc(x_659);
x_660 = lean_ctor_get_uint8(x_659, sizeof(void*)*1);
lean_dec(x_659);
if (x_660 == 0)
{
lean_object* x_661; 
x_661 = lean_ctor_get(x_658, 1);
lean_inc(x_661);
lean_dec(x_658);
x_647 = x_606;
x_648 = x_661;
goto block_655;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; uint8_t x_667; 
x_662 = lean_ctor_get(x_658, 1);
lean_inc(x_662);
lean_dec(x_658);
x_663 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_664 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_663, x_15, x_16, x_17, x_18, x_662);
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_664, 1);
lean_inc(x_666);
lean_dec(x_664);
x_667 = lean_unbox(x_665);
lean_dec(x_665);
x_647 = x_667;
x_648 = x_666;
goto block_655;
}
}
else
{
uint8_t x_668; 
lean_dec(x_618);
lean_dec(x_616);
lean_dec(x_615);
lean_dec(x_610);
lean_dec(x_602);
lean_dec(x_572);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_668 = !lean_is_exclusive(x_658);
if (x_668 == 0)
{
return x_658;
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_669 = lean_ctor_get(x_658, 0);
x_670 = lean_ctor_get(x_658, 1);
lean_inc(x_670);
lean_inc(x_669);
lean_dec(x_658);
x_671 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_671, 0, x_669);
lean_ctor_set(x_671, 1, x_670);
return x_671;
}
}
block_646:
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_620 = x_610;
x_621 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_583, x_620);
x_622 = x_621;
lean_inc(x_615);
x_623 = l_Lean_mkFVar(x_615);
lean_inc(x_616);
x_624 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_624, 0, x_616);
x_625 = lean_box(x_592);
lean_inc(x_616);
x_626 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 19, 13);
lean_closure_set(x_626, 0, x_615);
lean_closure_set(x_626, 1, x_10);
lean_closure_set(x_626, 2, x_616);
lean_closure_set(x_626, 3, x_3);
lean_closure_set(x_626, 4, x_4);
lean_closure_set(x_626, 5, x_8);
lean_closure_set(x_626, 6, x_9);
lean_closure_set(x_626, 7, x_572);
lean_closure_set(x_626, 8, x_625);
lean_closure_set(x_626, 9, x_602);
lean_closure_set(x_626, 10, x_618);
lean_closure_set(x_626, 11, x_622);
lean_closure_set(x_626, 12, x_623);
x_627 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_627, 0, x_624);
lean_closure_set(x_627, 1, x_626);
x_628 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_616, x_15, x_16, x_17, x_18, x_619);
if (lean_obj_tag(x_628) == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_629 = lean_ctor_get(x_628, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_628, 1);
lean_inc(x_630);
lean_dec(x_628);
x_631 = lean_ctor_get(x_629, 1);
lean_inc(x_631);
x_632 = lean_ctor_get(x_629, 4);
lean_inc(x_632);
lean_dec(x_629);
x_633 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_631, x_632, x_627, x_15, x_16, x_17, x_18, x_630);
if (lean_obj_tag(x_633) == 0)
{
uint8_t x_634; 
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
x_637 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_637, 0, x_635);
lean_ctor_set(x_637, 1, x_636);
return x_637;
}
}
else
{
uint8_t x_638; 
x_638 = !lean_is_exclusive(x_633);
if (x_638 == 0)
{
return x_633;
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_639 = lean_ctor_get(x_633, 0);
x_640 = lean_ctor_get(x_633, 1);
lean_inc(x_640);
lean_inc(x_639);
lean_dec(x_633);
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
lean_dec(x_627);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_642 = !lean_is_exclusive(x_628);
if (x_642 == 0)
{
return x_628;
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_643 = lean_ctor_get(x_628, 0);
x_644 = lean_ctor_get(x_628, 1);
lean_inc(x_644);
lean_inc(x_643);
lean_dec(x_628);
x_645 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_645, 0, x_643);
lean_ctor_set(x_645, 1, x_644);
return x_645;
}
}
}
block_655:
{
if (x_647 == 0)
{
x_619 = x_648;
goto block_646;
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
lean_inc(x_616);
x_649 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_649, 0, x_616);
x_650 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__5;
x_651 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_651, 0, x_650);
lean_ctor_set(x_651, 1, x_649);
x_652 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_653 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_652, x_651, x_15, x_16, x_17, x_18, x_648);
x_654 = lean_ctor_get(x_653, 1);
lean_inc(x_654);
lean_dec(x_653);
x_619 = x_654;
goto block_646;
}
}
}
else
{
uint8_t x_672; 
lean_dec(x_610);
lean_dec(x_602);
lean_dec(x_587);
lean_dec(x_572);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_672 = !lean_is_exclusive(x_612);
if (x_672 == 0)
{
return x_612;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_673 = lean_ctor_get(x_612, 0);
x_674 = lean_ctor_get(x_612, 1);
lean_inc(x_674);
lean_inc(x_673);
lean_dec(x_612);
x_675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_675, 0, x_673);
lean_ctor_set(x_675, 1, x_674);
return x_675;
}
}
}
else
{
uint8_t x_676; 
lean_dec(x_602);
lean_dec(x_587);
lean_dec(x_572);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_676 = !lean_is_exclusive(x_607);
if (x_676 == 0)
{
return x_607;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_677 = lean_ctor_get(x_607, 0);
x_678 = lean_ctor_get(x_607, 1);
lean_inc(x_678);
lean_inc(x_677);
lean_dec(x_607);
x_679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_679, 0, x_677);
lean_ctor_set(x_679, 1, x_678);
return x_679;
}
}
}
else
{
uint8_t x_680; 
lean_dec(x_587);
lean_dec(x_572);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_680 = !lean_is_exclusive(x_599);
if (x_680 == 0)
{
return x_599;
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_681 = lean_ctor_get(x_599, 0);
x_682 = lean_ctor_get(x_599, 1);
lean_inc(x_682);
lean_inc(x_681);
lean_dec(x_599);
x_683 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_683, 0, x_681);
lean_ctor_set(x_683, 1, x_682);
return x_683;
}
}
}
}
else
{
uint8_t x_698; 
lean_dec(x_587);
lean_dec(x_576);
lean_dec(x_572);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_698 = !lean_is_exclusive(x_589);
if (x_698 == 0)
{
return x_589;
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; 
x_699 = lean_ctor_get(x_589, 0);
x_700 = lean_ctor_get(x_589, 1);
lean_inc(x_700);
lean_inc(x_699);
lean_dec(x_589);
x_701 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_701, 0, x_699);
lean_ctor_set(x_701, 1, x_700);
return x_701;
}
}
}
else
{
uint8_t x_702; 
lean_dec(x_576);
lean_dec(x_572);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_702 = !lean_is_exclusive(x_586);
if (x_702 == 0)
{
return x_586;
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; 
x_703 = lean_ctor_get(x_586, 0);
x_704 = lean_ctor_get(x_586, 1);
lean_inc(x_704);
lean_inc(x_703);
lean_dec(x_586);
x_705 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_705, 0, x_703);
lean_ctor_set(x_705, 1, x_704);
return x_705;
}
}
}
else
{
uint8_t x_706; 
lean_dec(x_572);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_706 = !lean_is_exclusive(x_573);
if (x_706 == 0)
{
return x_573;
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; 
x_707 = lean_ctor_get(x_573, 0);
x_708 = lean_ctor_get(x_573, 1);
lean_inc(x_708);
lean_inc(x_707);
lean_dec(x_573);
x_709 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_709, 0, x_707);
lean_ctor_set(x_709, 1, x_708);
return x_709;
}
}
}
case 5:
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
x_710 = lean_ctor_get(x_12, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_12, 1);
lean_inc(x_711);
lean_dec(x_12);
x_712 = lean_array_set(x_13, x_14, x_711);
x_713 = lean_unsigned_to_nat(1u);
x_714 = lean_nat_sub(x_14, x_713);
lean_dec(x_14);
x_12 = x_710;
x_13 = x_712;
x_14 = x_714;
goto _start;
}
case 6:
{
lean_object* x_716; lean_object* x_717; 
lean_dec(x_14);
lean_dec(x_12);
x_716 = lean_ctor_get(x_9, 5);
lean_inc(x_716);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_1);
x_717 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_8, x_11, x_13, x_716, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_718 = lean_ctor_get(x_717, 1);
lean_inc(x_718);
lean_dec(x_717);
x_719 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_16, x_17, x_18, x_718);
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_719, 1);
lean_inc(x_721);
lean_dec(x_719);
x_722 = lean_ctor_get(x_9, 6);
lean_inc(x_722);
x_723 = l_List_redLength___main___rarg(x_722);
x_724 = lean_mk_empty_array_with_capacity(x_723);
lean_dec(x_723);
lean_inc(x_722);
x_725 = l_List_toArrayAux___main___rarg(x_722, x_724);
x_726 = x_725;
x_727 = lean_unsigned_to_nat(0u);
lean_inc(x_720);
lean_inc(x_8);
lean_inc(x_1);
x_728 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_728, 0, x_1);
lean_closure_set(x_728, 1, x_8);
lean_closure_set(x_728, 2, x_11);
lean_closure_set(x_728, 3, x_13);
lean_closure_set(x_728, 4, x_720);
lean_closure_set(x_728, 5, x_722);
lean_closure_set(x_728, 6, x_727);
lean_closure_set(x_728, 7, x_726);
x_729 = x_728;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_730 = lean_apply_5(x_729, x_15, x_16, x_17, x_18, x_721);
if (lean_obj_tag(x_730) == 0)
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; 
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_730, 1);
lean_inc(x_732);
lean_dec(x_730);
lean_inc(x_1);
x_733 = l_Lean_Meta_getMVarType(x_1, x_15, x_16, x_17, x_18, x_732);
if (lean_obj_tag(x_733) == 0)
{
lean_object* x_734; lean_object* x_735; uint8_t x_736; lean_object* x_737; 
x_734 = lean_ctor_get(x_733, 0);
lean_inc(x_734);
x_735 = lean_ctor_get(x_733, 1);
lean_inc(x_735);
lean_dec(x_733);
x_736 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
if (x_736 == 0)
{
lean_object* x_829; uint8_t x_830; 
x_829 = l_Lean_MetavarContext_exprDependsOn(x_720, x_734, x_2);
x_830 = lean_unbox(x_829);
lean_dec(x_829);
if (x_830 == 0)
{
x_737 = x_735;
goto block_828;
}
else
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; uint8_t x_838; 
lean_dec(x_731);
lean_dec(x_716);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_831 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_831, 0, x_3);
x_832 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_833 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_833, 0, x_832);
lean_ctor_set(x_833, 1, x_831);
x_834 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__8;
x_835 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_835, 0, x_833);
lean_ctor_set(x_835, 1, x_834);
x_836 = lean_box(0);
x_837 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_1, x_835, x_836, x_15, x_16, x_17, x_18, x_735);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_838 = !lean_is_exclusive(x_837);
if (x_838 == 0)
{
return x_837;
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; 
x_839 = lean_ctor_get(x_837, 0);
x_840 = lean_ctor_get(x_837, 1);
lean_inc(x_840);
lean_inc(x_839);
lean_dec(x_837);
x_841 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_841, 0, x_839);
lean_ctor_set(x_841, 1, x_840);
return x_841;
}
}
}
else
{
lean_dec(x_734);
lean_dec(x_720);
x_737 = x_735;
goto block_828;
}
block_828:
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; uint8_t x_742; lean_object* x_743; 
lean_inc(x_731);
x_738 = x_731;
x_739 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_727, x_738);
x_740 = x_739;
x_741 = lean_array_push(x_740, x_2);
x_742 = 1;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_743 = l_Lean_Meta_revert(x_1, x_741, x_742, x_15, x_16, x_17, x_18, x_737);
if (lean_obj_tag(x_743) == 0)
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; uint8_t x_750; lean_object* x_751; 
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_743, 1);
lean_inc(x_745);
lean_dec(x_743);
x_746 = lean_ctor_get(x_744, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_744, 1);
lean_inc(x_747);
lean_dec(x_744);
x_748 = lean_array_get_size(x_731);
x_749 = lean_box(0);
x_750 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_751 = l_Lean_Meta_introN(x_747, x_748, x_749, x_750, x_15, x_16, x_17, x_18, x_745);
if (lean_obj_tag(x_751) == 0)
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_752 = lean_ctor_get(x_751, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_751, 1);
lean_inc(x_753);
lean_dec(x_751);
x_754 = lean_ctor_get(x_752, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_752, 1);
lean_inc(x_755);
lean_dec(x_752);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_756 = l_Lean_Meta_intro1(x_755, x_750, x_15, x_16, x_17, x_18, x_753);
if (lean_obj_tag(x_756) == 0)
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; uint8_t x_791; lean_object* x_792; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
x_757 = lean_ctor_get(x_756, 0);
lean_inc(x_757);
x_758 = lean_ctor_get(x_756, 1);
lean_inc(x_758);
lean_dec(x_756);
x_759 = lean_ctor_get(x_757, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_757, 1);
lean_inc(x_760);
lean_dec(x_757);
x_761 = lean_box(0);
x_762 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_731, x_754, x_731, x_727, x_761);
lean_dec(x_731);
x_800 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_801 = lean_ctor_get(x_800, 2);
lean_inc(x_801);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_802 = lean_apply_5(x_801, x_15, x_16, x_17, x_18, x_758);
if (lean_obj_tag(x_802) == 0)
{
lean_object* x_803; uint8_t x_804; 
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
x_804 = lean_ctor_get_uint8(x_803, sizeof(void*)*1);
lean_dec(x_803);
if (x_804 == 0)
{
lean_object* x_805; 
x_805 = lean_ctor_get(x_802, 1);
lean_inc(x_805);
lean_dec(x_802);
x_791 = x_750;
x_792 = x_805;
goto block_799;
}
else
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; uint8_t x_811; 
x_806 = lean_ctor_get(x_802, 1);
lean_inc(x_806);
lean_dec(x_802);
x_807 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_808 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_807, x_15, x_16, x_17, x_18, x_806);
x_809 = lean_ctor_get(x_808, 0);
lean_inc(x_809);
x_810 = lean_ctor_get(x_808, 1);
lean_inc(x_810);
lean_dec(x_808);
x_811 = lean_unbox(x_809);
lean_dec(x_809);
x_791 = x_811;
x_792 = x_810;
goto block_799;
}
}
else
{
uint8_t x_812; 
lean_dec(x_762);
lean_dec(x_760);
lean_dec(x_759);
lean_dec(x_754);
lean_dec(x_746);
lean_dec(x_716);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_812 = !lean_is_exclusive(x_802);
if (x_812 == 0)
{
return x_802;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_813 = lean_ctor_get(x_802, 0);
x_814 = lean_ctor_get(x_802, 1);
lean_inc(x_814);
lean_inc(x_813);
lean_dec(x_802);
x_815 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_815, 0, x_813);
lean_ctor_set(x_815, 1, x_814);
return x_815;
}
}
block_790:
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; 
x_764 = x_754;
x_765 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_727, x_764);
x_766 = x_765;
lean_inc(x_759);
x_767 = l_Lean_mkFVar(x_759);
lean_inc(x_760);
x_768 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_768, 0, x_760);
x_769 = lean_box(x_736);
lean_inc(x_760);
x_770 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 19, 13);
lean_closure_set(x_770, 0, x_759);
lean_closure_set(x_770, 1, x_10);
lean_closure_set(x_770, 2, x_760);
lean_closure_set(x_770, 3, x_3);
lean_closure_set(x_770, 4, x_4);
lean_closure_set(x_770, 5, x_8);
lean_closure_set(x_770, 6, x_9);
lean_closure_set(x_770, 7, x_716);
lean_closure_set(x_770, 8, x_769);
lean_closure_set(x_770, 9, x_746);
lean_closure_set(x_770, 10, x_762);
lean_closure_set(x_770, 11, x_766);
lean_closure_set(x_770, 12, x_767);
x_771 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_771, 0, x_768);
lean_closure_set(x_771, 1, x_770);
x_772 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_760, x_15, x_16, x_17, x_18, x_763);
if (lean_obj_tag(x_772) == 0)
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; 
x_773 = lean_ctor_get(x_772, 0);
lean_inc(x_773);
x_774 = lean_ctor_get(x_772, 1);
lean_inc(x_774);
lean_dec(x_772);
x_775 = lean_ctor_get(x_773, 1);
lean_inc(x_775);
x_776 = lean_ctor_get(x_773, 4);
lean_inc(x_776);
lean_dec(x_773);
x_777 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_775, x_776, x_771, x_15, x_16, x_17, x_18, x_774);
if (lean_obj_tag(x_777) == 0)
{
uint8_t x_778; 
x_778 = !lean_is_exclusive(x_777);
if (x_778 == 0)
{
return x_777;
}
else
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; 
x_779 = lean_ctor_get(x_777, 0);
x_780 = lean_ctor_get(x_777, 1);
lean_inc(x_780);
lean_inc(x_779);
lean_dec(x_777);
x_781 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_781, 0, x_779);
lean_ctor_set(x_781, 1, x_780);
return x_781;
}
}
else
{
uint8_t x_782; 
x_782 = !lean_is_exclusive(x_777);
if (x_782 == 0)
{
return x_777;
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_783 = lean_ctor_get(x_777, 0);
x_784 = lean_ctor_get(x_777, 1);
lean_inc(x_784);
lean_inc(x_783);
lean_dec(x_777);
x_785 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_785, 0, x_783);
lean_ctor_set(x_785, 1, x_784);
return x_785;
}
}
}
else
{
uint8_t x_786; 
lean_dec(x_771);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_786 = !lean_is_exclusive(x_772);
if (x_786 == 0)
{
return x_772;
}
else
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_787 = lean_ctor_get(x_772, 0);
x_788 = lean_ctor_get(x_772, 1);
lean_inc(x_788);
lean_inc(x_787);
lean_dec(x_772);
x_789 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_789, 0, x_787);
lean_ctor_set(x_789, 1, x_788);
return x_789;
}
}
}
block_799:
{
if (x_791 == 0)
{
x_763 = x_792;
goto block_790;
}
else
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
lean_inc(x_760);
x_793 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_793, 0, x_760);
x_794 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__5;
x_795 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_795, 0, x_794);
lean_ctor_set(x_795, 1, x_793);
x_796 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_797 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_796, x_795, x_15, x_16, x_17, x_18, x_792);
x_798 = lean_ctor_get(x_797, 1);
lean_inc(x_798);
lean_dec(x_797);
x_763 = x_798;
goto block_790;
}
}
}
else
{
uint8_t x_816; 
lean_dec(x_754);
lean_dec(x_746);
lean_dec(x_731);
lean_dec(x_716);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_816 = !lean_is_exclusive(x_756);
if (x_816 == 0)
{
return x_756;
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_817 = lean_ctor_get(x_756, 0);
x_818 = lean_ctor_get(x_756, 1);
lean_inc(x_818);
lean_inc(x_817);
lean_dec(x_756);
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
lean_dec(x_746);
lean_dec(x_731);
lean_dec(x_716);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_820 = !lean_is_exclusive(x_751);
if (x_820 == 0)
{
return x_751;
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_821 = lean_ctor_get(x_751, 0);
x_822 = lean_ctor_get(x_751, 1);
lean_inc(x_822);
lean_inc(x_821);
lean_dec(x_751);
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
lean_dec(x_731);
lean_dec(x_716);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_824 = !lean_is_exclusive(x_743);
if (x_824 == 0)
{
return x_743;
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_825 = lean_ctor_get(x_743, 0);
x_826 = lean_ctor_get(x_743, 1);
lean_inc(x_826);
lean_inc(x_825);
lean_dec(x_743);
x_827 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_827, 0, x_825);
lean_ctor_set(x_827, 1, x_826);
return x_827;
}
}
}
}
else
{
uint8_t x_842; 
lean_dec(x_731);
lean_dec(x_720);
lean_dec(x_716);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_842 = !lean_is_exclusive(x_733);
if (x_842 == 0)
{
return x_733;
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; 
x_843 = lean_ctor_get(x_733, 0);
x_844 = lean_ctor_get(x_733, 1);
lean_inc(x_844);
lean_inc(x_843);
lean_dec(x_733);
x_845 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_845, 0, x_843);
lean_ctor_set(x_845, 1, x_844);
return x_845;
}
}
}
else
{
uint8_t x_846; 
lean_dec(x_720);
lean_dec(x_716);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_846 = !lean_is_exclusive(x_730);
if (x_846 == 0)
{
return x_730;
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; 
x_847 = lean_ctor_get(x_730, 0);
x_848 = lean_ctor_get(x_730, 1);
lean_inc(x_848);
lean_inc(x_847);
lean_dec(x_730);
x_849 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_849, 0, x_847);
lean_ctor_set(x_849, 1, x_848);
return x_849;
}
}
}
else
{
uint8_t x_850; 
lean_dec(x_716);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_850 = !lean_is_exclusive(x_717);
if (x_850 == 0)
{
return x_717;
}
else
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; 
x_851 = lean_ctor_get(x_717, 0);
x_852 = lean_ctor_get(x_717, 1);
lean_inc(x_852);
lean_inc(x_851);
lean_dec(x_717);
x_853 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_853, 0, x_851);
lean_ctor_set(x_853, 1, x_852);
return x_853;
}
}
}
case 7:
{
lean_object* x_854; lean_object* x_855; 
lean_dec(x_14);
lean_dec(x_12);
x_854 = lean_ctor_get(x_9, 5);
lean_inc(x_854);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_1);
x_855 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_8, x_11, x_13, x_854, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_855) == 0)
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
x_856 = lean_ctor_get(x_855, 1);
lean_inc(x_856);
lean_dec(x_855);
x_857 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_16, x_17, x_18, x_856);
x_858 = lean_ctor_get(x_857, 0);
lean_inc(x_858);
x_859 = lean_ctor_get(x_857, 1);
lean_inc(x_859);
lean_dec(x_857);
x_860 = lean_ctor_get(x_9, 6);
lean_inc(x_860);
x_861 = l_List_redLength___main___rarg(x_860);
x_862 = lean_mk_empty_array_with_capacity(x_861);
lean_dec(x_861);
lean_inc(x_860);
x_863 = l_List_toArrayAux___main___rarg(x_860, x_862);
x_864 = x_863;
x_865 = lean_unsigned_to_nat(0u);
lean_inc(x_858);
lean_inc(x_8);
lean_inc(x_1);
x_866 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_866, 0, x_1);
lean_closure_set(x_866, 1, x_8);
lean_closure_set(x_866, 2, x_11);
lean_closure_set(x_866, 3, x_13);
lean_closure_set(x_866, 4, x_858);
lean_closure_set(x_866, 5, x_860);
lean_closure_set(x_866, 6, x_865);
lean_closure_set(x_866, 7, x_864);
x_867 = x_866;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_868 = lean_apply_5(x_867, x_15, x_16, x_17, x_18, x_859);
if (lean_obj_tag(x_868) == 0)
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; 
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_868, 1);
lean_inc(x_870);
lean_dec(x_868);
lean_inc(x_1);
x_871 = l_Lean_Meta_getMVarType(x_1, x_15, x_16, x_17, x_18, x_870);
if (lean_obj_tag(x_871) == 0)
{
lean_object* x_872; lean_object* x_873; uint8_t x_874; lean_object* x_875; 
x_872 = lean_ctor_get(x_871, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_871, 1);
lean_inc(x_873);
lean_dec(x_871);
x_874 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
if (x_874 == 0)
{
lean_object* x_967; uint8_t x_968; 
x_967 = l_Lean_MetavarContext_exprDependsOn(x_858, x_872, x_2);
x_968 = lean_unbox(x_967);
lean_dec(x_967);
if (x_968 == 0)
{
x_875 = x_873;
goto block_966;
}
else
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; uint8_t x_976; 
lean_dec(x_869);
lean_dec(x_854);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_969 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_969, 0, x_3);
x_970 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_971 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_971, 0, x_970);
lean_ctor_set(x_971, 1, x_969);
x_972 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__8;
x_973 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_973, 0, x_971);
lean_ctor_set(x_973, 1, x_972);
x_974 = lean_box(0);
x_975 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_1, x_973, x_974, x_15, x_16, x_17, x_18, x_873);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_976 = !lean_is_exclusive(x_975);
if (x_976 == 0)
{
return x_975;
}
else
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; 
x_977 = lean_ctor_get(x_975, 0);
x_978 = lean_ctor_get(x_975, 1);
lean_inc(x_978);
lean_inc(x_977);
lean_dec(x_975);
x_979 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_979, 0, x_977);
lean_ctor_set(x_979, 1, x_978);
return x_979;
}
}
}
else
{
lean_dec(x_872);
lean_dec(x_858);
x_875 = x_873;
goto block_966;
}
block_966:
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; uint8_t x_880; lean_object* x_881; 
lean_inc(x_869);
x_876 = x_869;
x_877 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_865, x_876);
x_878 = x_877;
x_879 = lean_array_push(x_878, x_2);
x_880 = 1;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_881 = l_Lean_Meta_revert(x_1, x_879, x_880, x_15, x_16, x_17, x_18, x_875);
if (lean_obj_tag(x_881) == 0)
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; uint8_t x_888; lean_object* x_889; 
x_882 = lean_ctor_get(x_881, 0);
lean_inc(x_882);
x_883 = lean_ctor_get(x_881, 1);
lean_inc(x_883);
lean_dec(x_881);
x_884 = lean_ctor_get(x_882, 0);
lean_inc(x_884);
x_885 = lean_ctor_get(x_882, 1);
lean_inc(x_885);
lean_dec(x_882);
x_886 = lean_array_get_size(x_869);
x_887 = lean_box(0);
x_888 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_889 = l_Lean_Meta_introN(x_885, x_886, x_887, x_888, x_15, x_16, x_17, x_18, x_883);
if (lean_obj_tag(x_889) == 0)
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_890 = lean_ctor_get(x_889, 0);
lean_inc(x_890);
x_891 = lean_ctor_get(x_889, 1);
lean_inc(x_891);
lean_dec(x_889);
x_892 = lean_ctor_get(x_890, 0);
lean_inc(x_892);
x_893 = lean_ctor_get(x_890, 1);
lean_inc(x_893);
lean_dec(x_890);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_894 = l_Lean_Meta_intro1(x_893, x_888, x_15, x_16, x_17, x_18, x_891);
if (lean_obj_tag(x_894) == 0)
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; uint8_t x_929; lean_object* x_930; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_895 = lean_ctor_get(x_894, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_894, 1);
lean_inc(x_896);
lean_dec(x_894);
x_897 = lean_ctor_get(x_895, 0);
lean_inc(x_897);
x_898 = lean_ctor_get(x_895, 1);
lean_inc(x_898);
lean_dec(x_895);
x_899 = lean_box(0);
x_900 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_869, x_892, x_869, x_865, x_899);
lean_dec(x_869);
x_938 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_939 = lean_ctor_get(x_938, 2);
lean_inc(x_939);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_940 = lean_apply_5(x_939, x_15, x_16, x_17, x_18, x_896);
if (lean_obj_tag(x_940) == 0)
{
lean_object* x_941; uint8_t x_942; 
x_941 = lean_ctor_get(x_940, 0);
lean_inc(x_941);
x_942 = lean_ctor_get_uint8(x_941, sizeof(void*)*1);
lean_dec(x_941);
if (x_942 == 0)
{
lean_object* x_943; 
x_943 = lean_ctor_get(x_940, 1);
lean_inc(x_943);
lean_dec(x_940);
x_929 = x_888;
x_930 = x_943;
goto block_937;
}
else
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; uint8_t x_949; 
x_944 = lean_ctor_get(x_940, 1);
lean_inc(x_944);
lean_dec(x_940);
x_945 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_946 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_945, x_15, x_16, x_17, x_18, x_944);
x_947 = lean_ctor_get(x_946, 0);
lean_inc(x_947);
x_948 = lean_ctor_get(x_946, 1);
lean_inc(x_948);
lean_dec(x_946);
x_949 = lean_unbox(x_947);
lean_dec(x_947);
x_929 = x_949;
x_930 = x_948;
goto block_937;
}
}
else
{
uint8_t x_950; 
lean_dec(x_900);
lean_dec(x_898);
lean_dec(x_897);
lean_dec(x_892);
lean_dec(x_884);
lean_dec(x_854);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_950 = !lean_is_exclusive(x_940);
if (x_950 == 0)
{
return x_940;
}
else
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; 
x_951 = lean_ctor_get(x_940, 0);
x_952 = lean_ctor_get(x_940, 1);
lean_inc(x_952);
lean_inc(x_951);
lean_dec(x_940);
x_953 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_953, 0, x_951);
lean_ctor_set(x_953, 1, x_952);
return x_953;
}
}
block_928:
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; 
x_902 = x_892;
x_903 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_865, x_902);
x_904 = x_903;
lean_inc(x_897);
x_905 = l_Lean_mkFVar(x_897);
lean_inc(x_898);
x_906 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_906, 0, x_898);
x_907 = lean_box(x_874);
lean_inc(x_898);
x_908 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 19, 13);
lean_closure_set(x_908, 0, x_897);
lean_closure_set(x_908, 1, x_10);
lean_closure_set(x_908, 2, x_898);
lean_closure_set(x_908, 3, x_3);
lean_closure_set(x_908, 4, x_4);
lean_closure_set(x_908, 5, x_8);
lean_closure_set(x_908, 6, x_9);
lean_closure_set(x_908, 7, x_854);
lean_closure_set(x_908, 8, x_907);
lean_closure_set(x_908, 9, x_884);
lean_closure_set(x_908, 10, x_900);
lean_closure_set(x_908, 11, x_904);
lean_closure_set(x_908, 12, x_905);
x_909 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_909, 0, x_906);
lean_closure_set(x_909, 1, x_908);
x_910 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_898, x_15, x_16, x_17, x_18, x_901);
if (lean_obj_tag(x_910) == 0)
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; 
x_911 = lean_ctor_get(x_910, 0);
lean_inc(x_911);
x_912 = lean_ctor_get(x_910, 1);
lean_inc(x_912);
lean_dec(x_910);
x_913 = lean_ctor_get(x_911, 1);
lean_inc(x_913);
x_914 = lean_ctor_get(x_911, 4);
lean_inc(x_914);
lean_dec(x_911);
x_915 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_913, x_914, x_909, x_15, x_16, x_17, x_18, x_912);
if (lean_obj_tag(x_915) == 0)
{
uint8_t x_916; 
x_916 = !lean_is_exclusive(x_915);
if (x_916 == 0)
{
return x_915;
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; 
x_917 = lean_ctor_get(x_915, 0);
x_918 = lean_ctor_get(x_915, 1);
lean_inc(x_918);
lean_inc(x_917);
lean_dec(x_915);
x_919 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_919, 0, x_917);
lean_ctor_set(x_919, 1, x_918);
return x_919;
}
}
else
{
uint8_t x_920; 
x_920 = !lean_is_exclusive(x_915);
if (x_920 == 0)
{
return x_915;
}
else
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; 
x_921 = lean_ctor_get(x_915, 0);
x_922 = lean_ctor_get(x_915, 1);
lean_inc(x_922);
lean_inc(x_921);
lean_dec(x_915);
x_923 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_923, 0, x_921);
lean_ctor_set(x_923, 1, x_922);
return x_923;
}
}
}
else
{
uint8_t x_924; 
lean_dec(x_909);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_924 = !lean_is_exclusive(x_910);
if (x_924 == 0)
{
return x_910;
}
else
{
lean_object* x_925; lean_object* x_926; lean_object* x_927; 
x_925 = lean_ctor_get(x_910, 0);
x_926 = lean_ctor_get(x_910, 1);
lean_inc(x_926);
lean_inc(x_925);
lean_dec(x_910);
x_927 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_927, 0, x_925);
lean_ctor_set(x_927, 1, x_926);
return x_927;
}
}
}
block_937:
{
if (x_929 == 0)
{
x_901 = x_930;
goto block_928;
}
else
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; 
lean_inc(x_898);
x_931 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_931, 0, x_898);
x_932 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__5;
x_933 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_933, 0, x_932);
lean_ctor_set(x_933, 1, x_931);
x_934 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_935 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_934, x_933, x_15, x_16, x_17, x_18, x_930);
x_936 = lean_ctor_get(x_935, 1);
lean_inc(x_936);
lean_dec(x_935);
x_901 = x_936;
goto block_928;
}
}
}
else
{
uint8_t x_954; 
lean_dec(x_892);
lean_dec(x_884);
lean_dec(x_869);
lean_dec(x_854);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_954 = !lean_is_exclusive(x_894);
if (x_954 == 0)
{
return x_894;
}
else
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; 
x_955 = lean_ctor_get(x_894, 0);
x_956 = lean_ctor_get(x_894, 1);
lean_inc(x_956);
lean_inc(x_955);
lean_dec(x_894);
x_957 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_957, 0, x_955);
lean_ctor_set(x_957, 1, x_956);
return x_957;
}
}
}
else
{
uint8_t x_958; 
lean_dec(x_884);
lean_dec(x_869);
lean_dec(x_854);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_958 = !lean_is_exclusive(x_889);
if (x_958 == 0)
{
return x_889;
}
else
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; 
x_959 = lean_ctor_get(x_889, 0);
x_960 = lean_ctor_get(x_889, 1);
lean_inc(x_960);
lean_inc(x_959);
lean_dec(x_889);
x_961 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_961, 0, x_959);
lean_ctor_set(x_961, 1, x_960);
return x_961;
}
}
}
else
{
uint8_t x_962; 
lean_dec(x_869);
lean_dec(x_854);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_962 = !lean_is_exclusive(x_881);
if (x_962 == 0)
{
return x_881;
}
else
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; 
x_963 = lean_ctor_get(x_881, 0);
x_964 = lean_ctor_get(x_881, 1);
lean_inc(x_964);
lean_inc(x_963);
lean_dec(x_881);
x_965 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_965, 0, x_963);
lean_ctor_set(x_965, 1, x_964);
return x_965;
}
}
}
}
else
{
uint8_t x_980; 
lean_dec(x_869);
lean_dec(x_858);
lean_dec(x_854);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_980 = !lean_is_exclusive(x_871);
if (x_980 == 0)
{
return x_871;
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; 
x_981 = lean_ctor_get(x_871, 0);
x_982 = lean_ctor_get(x_871, 1);
lean_inc(x_982);
lean_inc(x_981);
lean_dec(x_871);
x_983 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_983, 0, x_981);
lean_ctor_set(x_983, 1, x_982);
return x_983;
}
}
}
else
{
uint8_t x_984; 
lean_dec(x_858);
lean_dec(x_854);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_984 = !lean_is_exclusive(x_868);
if (x_984 == 0)
{
return x_868;
}
else
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_985 = lean_ctor_get(x_868, 0);
x_986 = lean_ctor_get(x_868, 1);
lean_inc(x_986);
lean_inc(x_985);
lean_dec(x_868);
x_987 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_987, 0, x_985);
lean_ctor_set(x_987, 1, x_986);
return x_987;
}
}
}
else
{
uint8_t x_988; 
lean_dec(x_854);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_988 = !lean_is_exclusive(x_855);
if (x_988 == 0)
{
return x_855;
}
else
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; 
x_989 = lean_ctor_get(x_855, 0);
x_990 = lean_ctor_get(x_855, 1);
lean_inc(x_990);
lean_inc(x_989);
lean_dec(x_855);
x_991 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_991, 0, x_989);
lean_ctor_set(x_991, 1, x_990);
return x_991;
}
}
}
case 8:
{
lean_object* x_992; lean_object* x_993; 
lean_dec(x_14);
lean_dec(x_12);
x_992 = lean_ctor_get(x_9, 5);
lean_inc(x_992);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_1);
x_993 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_8, x_11, x_13, x_992, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_993) == 0)
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
x_994 = lean_ctor_get(x_993, 1);
lean_inc(x_994);
lean_dec(x_993);
x_995 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_16, x_17, x_18, x_994);
x_996 = lean_ctor_get(x_995, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_995, 1);
lean_inc(x_997);
lean_dec(x_995);
x_998 = lean_ctor_get(x_9, 6);
lean_inc(x_998);
x_999 = l_List_redLength___main___rarg(x_998);
x_1000 = lean_mk_empty_array_with_capacity(x_999);
lean_dec(x_999);
lean_inc(x_998);
x_1001 = l_List_toArrayAux___main___rarg(x_998, x_1000);
x_1002 = x_1001;
x_1003 = lean_unsigned_to_nat(0u);
lean_inc(x_996);
lean_inc(x_8);
lean_inc(x_1);
x_1004 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_1004, 0, x_1);
lean_closure_set(x_1004, 1, x_8);
lean_closure_set(x_1004, 2, x_11);
lean_closure_set(x_1004, 3, x_13);
lean_closure_set(x_1004, 4, x_996);
lean_closure_set(x_1004, 5, x_998);
lean_closure_set(x_1004, 6, x_1003);
lean_closure_set(x_1004, 7, x_1002);
x_1005 = x_1004;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1006 = lean_apply_5(x_1005, x_15, x_16, x_17, x_18, x_997);
if (lean_obj_tag(x_1006) == 0)
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; 
x_1007 = lean_ctor_get(x_1006, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_1006, 1);
lean_inc(x_1008);
lean_dec(x_1006);
lean_inc(x_1);
x_1009 = l_Lean_Meta_getMVarType(x_1, x_15, x_16, x_17, x_18, x_1008);
if (lean_obj_tag(x_1009) == 0)
{
lean_object* x_1010; lean_object* x_1011; uint8_t x_1012; lean_object* x_1013; 
x_1010 = lean_ctor_get(x_1009, 0);
lean_inc(x_1010);
x_1011 = lean_ctor_get(x_1009, 1);
lean_inc(x_1011);
lean_dec(x_1009);
x_1012 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
if (x_1012 == 0)
{
lean_object* x_1105; uint8_t x_1106; 
x_1105 = l_Lean_MetavarContext_exprDependsOn(x_996, x_1010, x_2);
x_1106 = lean_unbox(x_1105);
lean_dec(x_1105);
if (x_1106 == 0)
{
x_1013 = x_1011;
goto block_1104;
}
else
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; uint8_t x_1114; 
lean_dec(x_1007);
lean_dec(x_992);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_1107 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1107, 0, x_3);
x_1108 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_1109 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1109, 0, x_1108);
lean_ctor_set(x_1109, 1, x_1107);
x_1110 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__8;
x_1111 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1111, 0, x_1109);
lean_ctor_set(x_1111, 1, x_1110);
x_1112 = lean_box(0);
x_1113 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_1, x_1111, x_1112, x_15, x_16, x_17, x_18, x_1011);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_1114 = !lean_is_exclusive(x_1113);
if (x_1114 == 0)
{
return x_1113;
}
else
{
lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; 
x_1115 = lean_ctor_get(x_1113, 0);
x_1116 = lean_ctor_get(x_1113, 1);
lean_inc(x_1116);
lean_inc(x_1115);
lean_dec(x_1113);
x_1117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1117, 0, x_1115);
lean_ctor_set(x_1117, 1, x_1116);
return x_1117;
}
}
}
else
{
lean_dec(x_1010);
lean_dec(x_996);
x_1013 = x_1011;
goto block_1104;
}
block_1104:
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; uint8_t x_1018; lean_object* x_1019; 
lean_inc(x_1007);
x_1014 = x_1007;
x_1015 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1003, x_1014);
x_1016 = x_1015;
x_1017 = lean_array_push(x_1016, x_2);
x_1018 = 1;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1019 = l_Lean_Meta_revert(x_1, x_1017, x_1018, x_15, x_16, x_17, x_18, x_1013);
if (lean_obj_tag(x_1019) == 0)
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; uint8_t x_1026; lean_object* x_1027; 
x_1020 = lean_ctor_get(x_1019, 0);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_1019, 1);
lean_inc(x_1021);
lean_dec(x_1019);
x_1022 = lean_ctor_get(x_1020, 0);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_1020, 1);
lean_inc(x_1023);
lean_dec(x_1020);
x_1024 = lean_array_get_size(x_1007);
x_1025 = lean_box(0);
x_1026 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1027 = l_Lean_Meta_introN(x_1023, x_1024, x_1025, x_1026, x_15, x_16, x_17, x_18, x_1021);
if (lean_obj_tag(x_1027) == 0)
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1028 = lean_ctor_get(x_1027, 0);
lean_inc(x_1028);
x_1029 = lean_ctor_get(x_1027, 1);
lean_inc(x_1029);
lean_dec(x_1027);
x_1030 = lean_ctor_get(x_1028, 0);
lean_inc(x_1030);
x_1031 = lean_ctor_get(x_1028, 1);
lean_inc(x_1031);
lean_dec(x_1028);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1032 = l_Lean_Meta_intro1(x_1031, x_1026, x_15, x_16, x_17, x_18, x_1029);
if (lean_obj_tag(x_1032) == 0)
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; uint8_t x_1067; lean_object* x_1068; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; 
x_1033 = lean_ctor_get(x_1032, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_1032, 1);
lean_inc(x_1034);
lean_dec(x_1032);
x_1035 = lean_ctor_get(x_1033, 0);
lean_inc(x_1035);
x_1036 = lean_ctor_get(x_1033, 1);
lean_inc(x_1036);
lean_dec(x_1033);
x_1037 = lean_box(0);
x_1038 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1007, x_1030, x_1007, x_1003, x_1037);
lean_dec(x_1007);
x_1076 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_1077 = lean_ctor_get(x_1076, 2);
lean_inc(x_1077);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1078 = lean_apply_5(x_1077, x_15, x_16, x_17, x_18, x_1034);
if (lean_obj_tag(x_1078) == 0)
{
lean_object* x_1079; uint8_t x_1080; 
x_1079 = lean_ctor_get(x_1078, 0);
lean_inc(x_1079);
x_1080 = lean_ctor_get_uint8(x_1079, sizeof(void*)*1);
lean_dec(x_1079);
if (x_1080 == 0)
{
lean_object* x_1081; 
x_1081 = lean_ctor_get(x_1078, 1);
lean_inc(x_1081);
lean_dec(x_1078);
x_1067 = x_1026;
x_1068 = x_1081;
goto block_1075;
}
else
{
lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; uint8_t x_1087; 
x_1082 = lean_ctor_get(x_1078, 1);
lean_inc(x_1082);
lean_dec(x_1078);
x_1083 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1084 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1083, x_15, x_16, x_17, x_18, x_1082);
x_1085 = lean_ctor_get(x_1084, 0);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1084, 1);
lean_inc(x_1086);
lean_dec(x_1084);
x_1087 = lean_unbox(x_1085);
lean_dec(x_1085);
x_1067 = x_1087;
x_1068 = x_1086;
goto block_1075;
}
}
else
{
uint8_t x_1088; 
lean_dec(x_1038);
lean_dec(x_1036);
lean_dec(x_1035);
lean_dec(x_1030);
lean_dec(x_1022);
lean_dec(x_992);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1088 = !lean_is_exclusive(x_1078);
if (x_1088 == 0)
{
return x_1078;
}
else
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; 
x_1089 = lean_ctor_get(x_1078, 0);
x_1090 = lean_ctor_get(x_1078, 1);
lean_inc(x_1090);
lean_inc(x_1089);
lean_dec(x_1078);
x_1091 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1091, 0, x_1089);
lean_ctor_set(x_1091, 1, x_1090);
return x_1091;
}
}
block_1066:
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; 
x_1040 = x_1030;
x_1041 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1003, x_1040);
x_1042 = x_1041;
lean_inc(x_1035);
x_1043 = l_Lean_mkFVar(x_1035);
lean_inc(x_1036);
x_1044 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1044, 0, x_1036);
x_1045 = lean_box(x_1012);
lean_inc(x_1036);
x_1046 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 19, 13);
lean_closure_set(x_1046, 0, x_1035);
lean_closure_set(x_1046, 1, x_10);
lean_closure_set(x_1046, 2, x_1036);
lean_closure_set(x_1046, 3, x_3);
lean_closure_set(x_1046, 4, x_4);
lean_closure_set(x_1046, 5, x_8);
lean_closure_set(x_1046, 6, x_9);
lean_closure_set(x_1046, 7, x_992);
lean_closure_set(x_1046, 8, x_1045);
lean_closure_set(x_1046, 9, x_1022);
lean_closure_set(x_1046, 10, x_1038);
lean_closure_set(x_1046, 11, x_1042);
lean_closure_set(x_1046, 12, x_1043);
x_1047 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_1047, 0, x_1044);
lean_closure_set(x_1047, 1, x_1046);
x_1048 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_1036, x_15, x_16, x_17, x_18, x_1039);
if (lean_obj_tag(x_1048) == 0)
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; 
x_1049 = lean_ctor_get(x_1048, 0);
lean_inc(x_1049);
x_1050 = lean_ctor_get(x_1048, 1);
lean_inc(x_1050);
lean_dec(x_1048);
x_1051 = lean_ctor_get(x_1049, 1);
lean_inc(x_1051);
x_1052 = lean_ctor_get(x_1049, 4);
lean_inc(x_1052);
lean_dec(x_1049);
x_1053 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_1051, x_1052, x_1047, x_15, x_16, x_17, x_18, x_1050);
if (lean_obj_tag(x_1053) == 0)
{
uint8_t x_1054; 
x_1054 = !lean_is_exclusive(x_1053);
if (x_1054 == 0)
{
return x_1053;
}
else
{
lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; 
x_1055 = lean_ctor_get(x_1053, 0);
x_1056 = lean_ctor_get(x_1053, 1);
lean_inc(x_1056);
lean_inc(x_1055);
lean_dec(x_1053);
x_1057 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1057, 0, x_1055);
lean_ctor_set(x_1057, 1, x_1056);
return x_1057;
}
}
else
{
uint8_t x_1058; 
x_1058 = !lean_is_exclusive(x_1053);
if (x_1058 == 0)
{
return x_1053;
}
else
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; 
x_1059 = lean_ctor_get(x_1053, 0);
x_1060 = lean_ctor_get(x_1053, 1);
lean_inc(x_1060);
lean_inc(x_1059);
lean_dec(x_1053);
x_1061 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1061, 0, x_1059);
lean_ctor_set(x_1061, 1, x_1060);
return x_1061;
}
}
}
else
{
uint8_t x_1062; 
lean_dec(x_1047);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_1062 = !lean_is_exclusive(x_1048);
if (x_1062 == 0)
{
return x_1048;
}
else
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
x_1063 = lean_ctor_get(x_1048, 0);
x_1064 = lean_ctor_get(x_1048, 1);
lean_inc(x_1064);
lean_inc(x_1063);
lean_dec(x_1048);
x_1065 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1065, 0, x_1063);
lean_ctor_set(x_1065, 1, x_1064);
return x_1065;
}
}
}
block_1075:
{
if (x_1067 == 0)
{
x_1039 = x_1068;
goto block_1066;
}
else
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; 
lean_inc(x_1036);
x_1069 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1069, 0, x_1036);
x_1070 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__5;
x_1071 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1071, 0, x_1070);
lean_ctor_set(x_1071, 1, x_1069);
x_1072 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1073 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1072, x_1071, x_15, x_16, x_17, x_18, x_1068);
x_1074 = lean_ctor_get(x_1073, 1);
lean_inc(x_1074);
lean_dec(x_1073);
x_1039 = x_1074;
goto block_1066;
}
}
}
else
{
uint8_t x_1092; 
lean_dec(x_1030);
lean_dec(x_1022);
lean_dec(x_1007);
lean_dec(x_992);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1092 = !lean_is_exclusive(x_1032);
if (x_1092 == 0)
{
return x_1032;
}
else
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; 
x_1093 = lean_ctor_get(x_1032, 0);
x_1094 = lean_ctor_get(x_1032, 1);
lean_inc(x_1094);
lean_inc(x_1093);
lean_dec(x_1032);
x_1095 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1095, 0, x_1093);
lean_ctor_set(x_1095, 1, x_1094);
return x_1095;
}
}
}
else
{
uint8_t x_1096; 
lean_dec(x_1022);
lean_dec(x_1007);
lean_dec(x_992);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1096 = !lean_is_exclusive(x_1027);
if (x_1096 == 0)
{
return x_1027;
}
else
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; 
x_1097 = lean_ctor_get(x_1027, 0);
x_1098 = lean_ctor_get(x_1027, 1);
lean_inc(x_1098);
lean_inc(x_1097);
lean_dec(x_1027);
x_1099 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1099, 0, x_1097);
lean_ctor_set(x_1099, 1, x_1098);
return x_1099;
}
}
}
else
{
uint8_t x_1100; 
lean_dec(x_1007);
lean_dec(x_992);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1100 = !lean_is_exclusive(x_1019);
if (x_1100 == 0)
{
return x_1019;
}
else
{
lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
x_1101 = lean_ctor_get(x_1019, 0);
x_1102 = lean_ctor_get(x_1019, 1);
lean_inc(x_1102);
lean_inc(x_1101);
lean_dec(x_1019);
x_1103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1103, 0, x_1101);
lean_ctor_set(x_1103, 1, x_1102);
return x_1103;
}
}
}
}
else
{
uint8_t x_1118; 
lean_dec(x_1007);
lean_dec(x_996);
lean_dec(x_992);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1118 = !lean_is_exclusive(x_1009);
if (x_1118 == 0)
{
return x_1009;
}
else
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; 
x_1119 = lean_ctor_get(x_1009, 0);
x_1120 = lean_ctor_get(x_1009, 1);
lean_inc(x_1120);
lean_inc(x_1119);
lean_dec(x_1009);
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
lean_dec(x_996);
lean_dec(x_992);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1122 = !lean_is_exclusive(x_1006);
if (x_1122 == 0)
{
return x_1006;
}
else
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; 
x_1123 = lean_ctor_get(x_1006, 0);
x_1124 = lean_ctor_get(x_1006, 1);
lean_inc(x_1124);
lean_inc(x_1123);
lean_dec(x_1006);
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
lean_dec(x_992);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1126 = !lean_is_exclusive(x_993);
if (x_1126 == 0)
{
return x_993;
}
else
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; 
x_1127 = lean_ctor_get(x_993, 0);
x_1128 = lean_ctor_get(x_993, 1);
lean_inc(x_1128);
lean_inc(x_1127);
lean_dec(x_993);
x_1129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1129, 0, x_1127);
lean_ctor_set(x_1129, 1, x_1128);
return x_1129;
}
}
}
case 9:
{
lean_object* x_1130; lean_object* x_1131; 
lean_dec(x_14);
lean_dec(x_12);
x_1130 = lean_ctor_get(x_9, 5);
lean_inc(x_1130);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_1);
x_1131 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_8, x_11, x_13, x_1130, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_1131) == 0)
{
lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
x_1132 = lean_ctor_get(x_1131, 1);
lean_inc(x_1132);
lean_dec(x_1131);
x_1133 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_16, x_17, x_18, x_1132);
x_1134 = lean_ctor_get(x_1133, 0);
lean_inc(x_1134);
x_1135 = lean_ctor_get(x_1133, 1);
lean_inc(x_1135);
lean_dec(x_1133);
x_1136 = lean_ctor_get(x_9, 6);
lean_inc(x_1136);
x_1137 = l_List_redLength___main___rarg(x_1136);
x_1138 = lean_mk_empty_array_with_capacity(x_1137);
lean_dec(x_1137);
lean_inc(x_1136);
x_1139 = l_List_toArrayAux___main___rarg(x_1136, x_1138);
x_1140 = x_1139;
x_1141 = lean_unsigned_to_nat(0u);
lean_inc(x_1134);
lean_inc(x_8);
lean_inc(x_1);
x_1142 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_1142, 0, x_1);
lean_closure_set(x_1142, 1, x_8);
lean_closure_set(x_1142, 2, x_11);
lean_closure_set(x_1142, 3, x_13);
lean_closure_set(x_1142, 4, x_1134);
lean_closure_set(x_1142, 5, x_1136);
lean_closure_set(x_1142, 6, x_1141);
lean_closure_set(x_1142, 7, x_1140);
x_1143 = x_1142;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1144 = lean_apply_5(x_1143, x_15, x_16, x_17, x_18, x_1135);
if (lean_obj_tag(x_1144) == 0)
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
x_1145 = lean_ctor_get(x_1144, 0);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_1144, 1);
lean_inc(x_1146);
lean_dec(x_1144);
lean_inc(x_1);
x_1147 = l_Lean_Meta_getMVarType(x_1, x_15, x_16, x_17, x_18, x_1146);
if (lean_obj_tag(x_1147) == 0)
{
lean_object* x_1148; lean_object* x_1149; uint8_t x_1150; lean_object* x_1151; 
x_1148 = lean_ctor_get(x_1147, 0);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_1147, 1);
lean_inc(x_1149);
lean_dec(x_1147);
x_1150 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
if (x_1150 == 0)
{
lean_object* x_1243; uint8_t x_1244; 
x_1243 = l_Lean_MetavarContext_exprDependsOn(x_1134, x_1148, x_2);
x_1244 = lean_unbox(x_1243);
lean_dec(x_1243);
if (x_1244 == 0)
{
x_1151 = x_1149;
goto block_1242;
}
else
{
lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; uint8_t x_1252; 
lean_dec(x_1145);
lean_dec(x_1130);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_1245 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1245, 0, x_3);
x_1246 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_1247 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1247, 0, x_1246);
lean_ctor_set(x_1247, 1, x_1245);
x_1248 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__8;
x_1249 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1249, 0, x_1247);
lean_ctor_set(x_1249, 1, x_1248);
x_1250 = lean_box(0);
x_1251 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_1, x_1249, x_1250, x_15, x_16, x_17, x_18, x_1149);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_1252 = !lean_is_exclusive(x_1251);
if (x_1252 == 0)
{
return x_1251;
}
else
{
lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; 
x_1253 = lean_ctor_get(x_1251, 0);
x_1254 = lean_ctor_get(x_1251, 1);
lean_inc(x_1254);
lean_inc(x_1253);
lean_dec(x_1251);
x_1255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1255, 0, x_1253);
lean_ctor_set(x_1255, 1, x_1254);
return x_1255;
}
}
}
else
{
lean_dec(x_1148);
lean_dec(x_1134);
x_1151 = x_1149;
goto block_1242;
}
block_1242:
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; uint8_t x_1156; lean_object* x_1157; 
lean_inc(x_1145);
x_1152 = x_1145;
x_1153 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1141, x_1152);
x_1154 = x_1153;
x_1155 = lean_array_push(x_1154, x_2);
x_1156 = 1;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1157 = l_Lean_Meta_revert(x_1, x_1155, x_1156, x_15, x_16, x_17, x_18, x_1151);
if (lean_obj_tag(x_1157) == 0)
{
lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; uint8_t x_1164; lean_object* x_1165; 
x_1158 = lean_ctor_get(x_1157, 0);
lean_inc(x_1158);
x_1159 = lean_ctor_get(x_1157, 1);
lean_inc(x_1159);
lean_dec(x_1157);
x_1160 = lean_ctor_get(x_1158, 0);
lean_inc(x_1160);
x_1161 = lean_ctor_get(x_1158, 1);
lean_inc(x_1161);
lean_dec(x_1158);
x_1162 = lean_array_get_size(x_1145);
x_1163 = lean_box(0);
x_1164 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1165 = l_Lean_Meta_introN(x_1161, x_1162, x_1163, x_1164, x_15, x_16, x_17, x_18, x_1159);
if (lean_obj_tag(x_1165) == 0)
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; 
x_1166 = lean_ctor_get(x_1165, 0);
lean_inc(x_1166);
x_1167 = lean_ctor_get(x_1165, 1);
lean_inc(x_1167);
lean_dec(x_1165);
x_1168 = lean_ctor_get(x_1166, 0);
lean_inc(x_1168);
x_1169 = lean_ctor_get(x_1166, 1);
lean_inc(x_1169);
lean_dec(x_1166);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1170 = l_Lean_Meta_intro1(x_1169, x_1164, x_15, x_16, x_17, x_18, x_1167);
if (lean_obj_tag(x_1170) == 0)
{
lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; uint8_t x_1205; lean_object* x_1206; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
x_1171 = lean_ctor_get(x_1170, 0);
lean_inc(x_1171);
x_1172 = lean_ctor_get(x_1170, 1);
lean_inc(x_1172);
lean_dec(x_1170);
x_1173 = lean_ctor_get(x_1171, 0);
lean_inc(x_1173);
x_1174 = lean_ctor_get(x_1171, 1);
lean_inc(x_1174);
lean_dec(x_1171);
x_1175 = lean_box(0);
x_1176 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1145, x_1168, x_1145, x_1141, x_1175);
lean_dec(x_1145);
x_1214 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_1215 = lean_ctor_get(x_1214, 2);
lean_inc(x_1215);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1216 = lean_apply_5(x_1215, x_15, x_16, x_17, x_18, x_1172);
if (lean_obj_tag(x_1216) == 0)
{
lean_object* x_1217; uint8_t x_1218; 
x_1217 = lean_ctor_get(x_1216, 0);
lean_inc(x_1217);
x_1218 = lean_ctor_get_uint8(x_1217, sizeof(void*)*1);
lean_dec(x_1217);
if (x_1218 == 0)
{
lean_object* x_1219; 
x_1219 = lean_ctor_get(x_1216, 1);
lean_inc(x_1219);
lean_dec(x_1216);
x_1205 = x_1164;
x_1206 = x_1219;
goto block_1213;
}
else
{
lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; uint8_t x_1225; 
x_1220 = lean_ctor_get(x_1216, 1);
lean_inc(x_1220);
lean_dec(x_1216);
x_1221 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1222 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1221, x_15, x_16, x_17, x_18, x_1220);
x_1223 = lean_ctor_get(x_1222, 0);
lean_inc(x_1223);
x_1224 = lean_ctor_get(x_1222, 1);
lean_inc(x_1224);
lean_dec(x_1222);
x_1225 = lean_unbox(x_1223);
lean_dec(x_1223);
x_1205 = x_1225;
x_1206 = x_1224;
goto block_1213;
}
}
else
{
uint8_t x_1226; 
lean_dec(x_1176);
lean_dec(x_1174);
lean_dec(x_1173);
lean_dec(x_1168);
lean_dec(x_1160);
lean_dec(x_1130);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1226 = !lean_is_exclusive(x_1216);
if (x_1226 == 0)
{
return x_1216;
}
else
{
lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; 
x_1227 = lean_ctor_get(x_1216, 0);
x_1228 = lean_ctor_get(x_1216, 1);
lean_inc(x_1228);
lean_inc(x_1227);
lean_dec(x_1216);
x_1229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1229, 0, x_1227);
lean_ctor_set(x_1229, 1, x_1228);
return x_1229;
}
}
block_1204:
{
lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1178 = x_1168;
x_1179 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1141, x_1178);
x_1180 = x_1179;
lean_inc(x_1173);
x_1181 = l_Lean_mkFVar(x_1173);
lean_inc(x_1174);
x_1182 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1182, 0, x_1174);
x_1183 = lean_box(x_1150);
lean_inc(x_1174);
x_1184 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 19, 13);
lean_closure_set(x_1184, 0, x_1173);
lean_closure_set(x_1184, 1, x_10);
lean_closure_set(x_1184, 2, x_1174);
lean_closure_set(x_1184, 3, x_3);
lean_closure_set(x_1184, 4, x_4);
lean_closure_set(x_1184, 5, x_8);
lean_closure_set(x_1184, 6, x_9);
lean_closure_set(x_1184, 7, x_1130);
lean_closure_set(x_1184, 8, x_1183);
lean_closure_set(x_1184, 9, x_1160);
lean_closure_set(x_1184, 10, x_1176);
lean_closure_set(x_1184, 11, x_1180);
lean_closure_set(x_1184, 12, x_1181);
x_1185 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_1185, 0, x_1182);
lean_closure_set(x_1185, 1, x_1184);
x_1186 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_1174, x_15, x_16, x_17, x_18, x_1177);
if (lean_obj_tag(x_1186) == 0)
{
lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; 
x_1187 = lean_ctor_get(x_1186, 0);
lean_inc(x_1187);
x_1188 = lean_ctor_get(x_1186, 1);
lean_inc(x_1188);
lean_dec(x_1186);
x_1189 = lean_ctor_get(x_1187, 1);
lean_inc(x_1189);
x_1190 = lean_ctor_get(x_1187, 4);
lean_inc(x_1190);
lean_dec(x_1187);
x_1191 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_1189, x_1190, x_1185, x_15, x_16, x_17, x_18, x_1188);
if (lean_obj_tag(x_1191) == 0)
{
uint8_t x_1192; 
x_1192 = !lean_is_exclusive(x_1191);
if (x_1192 == 0)
{
return x_1191;
}
else
{
lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
x_1193 = lean_ctor_get(x_1191, 0);
x_1194 = lean_ctor_get(x_1191, 1);
lean_inc(x_1194);
lean_inc(x_1193);
lean_dec(x_1191);
x_1195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1195, 0, x_1193);
lean_ctor_set(x_1195, 1, x_1194);
return x_1195;
}
}
else
{
uint8_t x_1196; 
x_1196 = !lean_is_exclusive(x_1191);
if (x_1196 == 0)
{
return x_1191;
}
else
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; 
x_1197 = lean_ctor_get(x_1191, 0);
x_1198 = lean_ctor_get(x_1191, 1);
lean_inc(x_1198);
lean_inc(x_1197);
lean_dec(x_1191);
x_1199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1199, 0, x_1197);
lean_ctor_set(x_1199, 1, x_1198);
return x_1199;
}
}
}
else
{
uint8_t x_1200; 
lean_dec(x_1185);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_1200 = !lean_is_exclusive(x_1186);
if (x_1200 == 0)
{
return x_1186;
}
else
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; 
x_1201 = lean_ctor_get(x_1186, 0);
x_1202 = lean_ctor_get(x_1186, 1);
lean_inc(x_1202);
lean_inc(x_1201);
lean_dec(x_1186);
x_1203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1203, 0, x_1201);
lean_ctor_set(x_1203, 1, x_1202);
return x_1203;
}
}
}
block_1213:
{
if (x_1205 == 0)
{
x_1177 = x_1206;
goto block_1204;
}
else
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; 
lean_inc(x_1174);
x_1207 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1207, 0, x_1174);
x_1208 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__5;
x_1209 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1209, 0, x_1208);
lean_ctor_set(x_1209, 1, x_1207);
x_1210 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1211 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1210, x_1209, x_15, x_16, x_17, x_18, x_1206);
x_1212 = lean_ctor_get(x_1211, 1);
lean_inc(x_1212);
lean_dec(x_1211);
x_1177 = x_1212;
goto block_1204;
}
}
}
else
{
uint8_t x_1230; 
lean_dec(x_1168);
lean_dec(x_1160);
lean_dec(x_1145);
lean_dec(x_1130);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1230 = !lean_is_exclusive(x_1170);
if (x_1230 == 0)
{
return x_1170;
}
else
{
lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; 
x_1231 = lean_ctor_get(x_1170, 0);
x_1232 = lean_ctor_get(x_1170, 1);
lean_inc(x_1232);
lean_inc(x_1231);
lean_dec(x_1170);
x_1233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1233, 0, x_1231);
lean_ctor_set(x_1233, 1, x_1232);
return x_1233;
}
}
}
else
{
uint8_t x_1234; 
lean_dec(x_1160);
lean_dec(x_1145);
lean_dec(x_1130);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1234 = !lean_is_exclusive(x_1165);
if (x_1234 == 0)
{
return x_1165;
}
else
{
lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; 
x_1235 = lean_ctor_get(x_1165, 0);
x_1236 = lean_ctor_get(x_1165, 1);
lean_inc(x_1236);
lean_inc(x_1235);
lean_dec(x_1165);
x_1237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1237, 0, x_1235);
lean_ctor_set(x_1237, 1, x_1236);
return x_1237;
}
}
}
else
{
uint8_t x_1238; 
lean_dec(x_1145);
lean_dec(x_1130);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1238 = !lean_is_exclusive(x_1157);
if (x_1238 == 0)
{
return x_1157;
}
else
{
lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; 
x_1239 = lean_ctor_get(x_1157, 0);
x_1240 = lean_ctor_get(x_1157, 1);
lean_inc(x_1240);
lean_inc(x_1239);
lean_dec(x_1157);
x_1241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1241, 0, x_1239);
lean_ctor_set(x_1241, 1, x_1240);
return x_1241;
}
}
}
}
else
{
uint8_t x_1256; 
lean_dec(x_1145);
lean_dec(x_1134);
lean_dec(x_1130);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1256 = !lean_is_exclusive(x_1147);
if (x_1256 == 0)
{
return x_1147;
}
else
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; 
x_1257 = lean_ctor_get(x_1147, 0);
x_1258 = lean_ctor_get(x_1147, 1);
lean_inc(x_1258);
lean_inc(x_1257);
lean_dec(x_1147);
x_1259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1259, 0, x_1257);
lean_ctor_set(x_1259, 1, x_1258);
return x_1259;
}
}
}
else
{
uint8_t x_1260; 
lean_dec(x_1134);
lean_dec(x_1130);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1260 = !lean_is_exclusive(x_1144);
if (x_1260 == 0)
{
return x_1144;
}
else
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; 
x_1261 = lean_ctor_get(x_1144, 0);
x_1262 = lean_ctor_get(x_1144, 1);
lean_inc(x_1262);
lean_inc(x_1261);
lean_dec(x_1144);
x_1263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1263, 0, x_1261);
lean_ctor_set(x_1263, 1, x_1262);
return x_1263;
}
}
}
else
{
uint8_t x_1264; 
lean_dec(x_1130);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1264 = !lean_is_exclusive(x_1131);
if (x_1264 == 0)
{
return x_1131;
}
else
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; 
x_1265 = lean_ctor_get(x_1131, 0);
x_1266 = lean_ctor_get(x_1131, 1);
lean_inc(x_1266);
lean_inc(x_1265);
lean_dec(x_1131);
x_1267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1267, 0, x_1265);
lean_ctor_set(x_1267, 1, x_1266);
return x_1267;
}
}
}
case 10:
{
lean_object* x_1268; lean_object* x_1269; 
lean_dec(x_14);
lean_dec(x_12);
x_1268 = lean_ctor_get(x_9, 5);
lean_inc(x_1268);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_1);
x_1269 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_8, x_11, x_13, x_1268, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_1269) == 0)
{
lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; 
x_1270 = lean_ctor_get(x_1269, 1);
lean_inc(x_1270);
lean_dec(x_1269);
x_1271 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_16, x_17, x_18, x_1270);
x_1272 = lean_ctor_get(x_1271, 0);
lean_inc(x_1272);
x_1273 = lean_ctor_get(x_1271, 1);
lean_inc(x_1273);
lean_dec(x_1271);
x_1274 = lean_ctor_get(x_9, 6);
lean_inc(x_1274);
x_1275 = l_List_redLength___main___rarg(x_1274);
x_1276 = lean_mk_empty_array_with_capacity(x_1275);
lean_dec(x_1275);
lean_inc(x_1274);
x_1277 = l_List_toArrayAux___main___rarg(x_1274, x_1276);
x_1278 = x_1277;
x_1279 = lean_unsigned_to_nat(0u);
lean_inc(x_1272);
lean_inc(x_8);
lean_inc(x_1);
x_1280 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_1280, 0, x_1);
lean_closure_set(x_1280, 1, x_8);
lean_closure_set(x_1280, 2, x_11);
lean_closure_set(x_1280, 3, x_13);
lean_closure_set(x_1280, 4, x_1272);
lean_closure_set(x_1280, 5, x_1274);
lean_closure_set(x_1280, 6, x_1279);
lean_closure_set(x_1280, 7, x_1278);
x_1281 = x_1280;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1282 = lean_apply_5(x_1281, x_15, x_16, x_17, x_18, x_1273);
if (lean_obj_tag(x_1282) == 0)
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; 
x_1283 = lean_ctor_get(x_1282, 0);
lean_inc(x_1283);
x_1284 = lean_ctor_get(x_1282, 1);
lean_inc(x_1284);
lean_dec(x_1282);
lean_inc(x_1);
x_1285 = l_Lean_Meta_getMVarType(x_1, x_15, x_16, x_17, x_18, x_1284);
if (lean_obj_tag(x_1285) == 0)
{
lean_object* x_1286; lean_object* x_1287; uint8_t x_1288; lean_object* x_1289; 
x_1286 = lean_ctor_get(x_1285, 0);
lean_inc(x_1286);
x_1287 = lean_ctor_get(x_1285, 1);
lean_inc(x_1287);
lean_dec(x_1285);
x_1288 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
if (x_1288 == 0)
{
lean_object* x_1381; uint8_t x_1382; 
x_1381 = l_Lean_MetavarContext_exprDependsOn(x_1272, x_1286, x_2);
x_1382 = lean_unbox(x_1381);
lean_dec(x_1381);
if (x_1382 == 0)
{
x_1289 = x_1287;
goto block_1380;
}
else
{
lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; uint8_t x_1390; 
lean_dec(x_1283);
lean_dec(x_1268);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_1383 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1383, 0, x_3);
x_1384 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_1385 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1385, 0, x_1384);
lean_ctor_set(x_1385, 1, x_1383);
x_1386 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__8;
x_1387 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1387, 0, x_1385);
lean_ctor_set(x_1387, 1, x_1386);
x_1388 = lean_box(0);
x_1389 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_1, x_1387, x_1388, x_15, x_16, x_17, x_18, x_1287);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_1390 = !lean_is_exclusive(x_1389);
if (x_1390 == 0)
{
return x_1389;
}
else
{
lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; 
x_1391 = lean_ctor_get(x_1389, 0);
x_1392 = lean_ctor_get(x_1389, 1);
lean_inc(x_1392);
lean_inc(x_1391);
lean_dec(x_1389);
x_1393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1393, 0, x_1391);
lean_ctor_set(x_1393, 1, x_1392);
return x_1393;
}
}
}
else
{
lean_dec(x_1286);
lean_dec(x_1272);
x_1289 = x_1287;
goto block_1380;
}
block_1380:
{
lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; uint8_t x_1294; lean_object* x_1295; 
lean_inc(x_1283);
x_1290 = x_1283;
x_1291 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1279, x_1290);
x_1292 = x_1291;
x_1293 = lean_array_push(x_1292, x_2);
x_1294 = 1;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1295 = l_Lean_Meta_revert(x_1, x_1293, x_1294, x_15, x_16, x_17, x_18, x_1289);
if (lean_obj_tag(x_1295) == 0)
{
lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; uint8_t x_1302; lean_object* x_1303; 
x_1296 = lean_ctor_get(x_1295, 0);
lean_inc(x_1296);
x_1297 = lean_ctor_get(x_1295, 1);
lean_inc(x_1297);
lean_dec(x_1295);
x_1298 = lean_ctor_get(x_1296, 0);
lean_inc(x_1298);
x_1299 = lean_ctor_get(x_1296, 1);
lean_inc(x_1299);
lean_dec(x_1296);
x_1300 = lean_array_get_size(x_1283);
x_1301 = lean_box(0);
x_1302 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1303 = l_Lean_Meta_introN(x_1299, x_1300, x_1301, x_1302, x_15, x_16, x_17, x_18, x_1297);
if (lean_obj_tag(x_1303) == 0)
{
lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; 
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
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1308 = l_Lean_Meta_intro1(x_1307, x_1302, x_15, x_16, x_17, x_18, x_1305);
if (lean_obj_tag(x_1308) == 0)
{
lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; uint8_t x_1343; lean_object* x_1344; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; 
x_1309 = lean_ctor_get(x_1308, 0);
lean_inc(x_1309);
x_1310 = lean_ctor_get(x_1308, 1);
lean_inc(x_1310);
lean_dec(x_1308);
x_1311 = lean_ctor_get(x_1309, 0);
lean_inc(x_1311);
x_1312 = lean_ctor_get(x_1309, 1);
lean_inc(x_1312);
lean_dec(x_1309);
x_1313 = lean_box(0);
x_1314 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1283, x_1306, x_1283, x_1279, x_1313);
lean_dec(x_1283);
x_1352 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_1353 = lean_ctor_get(x_1352, 2);
lean_inc(x_1353);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1354 = lean_apply_5(x_1353, x_15, x_16, x_17, x_18, x_1310);
if (lean_obj_tag(x_1354) == 0)
{
lean_object* x_1355; uint8_t x_1356; 
x_1355 = lean_ctor_get(x_1354, 0);
lean_inc(x_1355);
x_1356 = lean_ctor_get_uint8(x_1355, sizeof(void*)*1);
lean_dec(x_1355);
if (x_1356 == 0)
{
lean_object* x_1357; 
x_1357 = lean_ctor_get(x_1354, 1);
lean_inc(x_1357);
lean_dec(x_1354);
x_1343 = x_1302;
x_1344 = x_1357;
goto block_1351;
}
else
{
lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; uint8_t x_1363; 
x_1358 = lean_ctor_get(x_1354, 1);
lean_inc(x_1358);
lean_dec(x_1354);
x_1359 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1360 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1359, x_15, x_16, x_17, x_18, x_1358);
x_1361 = lean_ctor_get(x_1360, 0);
lean_inc(x_1361);
x_1362 = lean_ctor_get(x_1360, 1);
lean_inc(x_1362);
lean_dec(x_1360);
x_1363 = lean_unbox(x_1361);
lean_dec(x_1361);
x_1343 = x_1363;
x_1344 = x_1362;
goto block_1351;
}
}
else
{
uint8_t x_1364; 
lean_dec(x_1314);
lean_dec(x_1312);
lean_dec(x_1311);
lean_dec(x_1306);
lean_dec(x_1298);
lean_dec(x_1268);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1364 = !lean_is_exclusive(x_1354);
if (x_1364 == 0)
{
return x_1354;
}
else
{
lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; 
x_1365 = lean_ctor_get(x_1354, 0);
x_1366 = lean_ctor_get(x_1354, 1);
lean_inc(x_1366);
lean_inc(x_1365);
lean_dec(x_1354);
x_1367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1367, 0, x_1365);
lean_ctor_set(x_1367, 1, x_1366);
return x_1367;
}
}
block_1342:
{
lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; 
x_1316 = x_1306;
x_1317 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1279, x_1316);
x_1318 = x_1317;
lean_inc(x_1311);
x_1319 = l_Lean_mkFVar(x_1311);
lean_inc(x_1312);
x_1320 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1320, 0, x_1312);
x_1321 = lean_box(x_1288);
lean_inc(x_1312);
x_1322 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 19, 13);
lean_closure_set(x_1322, 0, x_1311);
lean_closure_set(x_1322, 1, x_10);
lean_closure_set(x_1322, 2, x_1312);
lean_closure_set(x_1322, 3, x_3);
lean_closure_set(x_1322, 4, x_4);
lean_closure_set(x_1322, 5, x_8);
lean_closure_set(x_1322, 6, x_9);
lean_closure_set(x_1322, 7, x_1268);
lean_closure_set(x_1322, 8, x_1321);
lean_closure_set(x_1322, 9, x_1298);
lean_closure_set(x_1322, 10, x_1314);
lean_closure_set(x_1322, 11, x_1318);
lean_closure_set(x_1322, 12, x_1319);
x_1323 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_1323, 0, x_1320);
lean_closure_set(x_1323, 1, x_1322);
x_1324 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_1312, x_15, x_16, x_17, x_18, x_1315);
if (lean_obj_tag(x_1324) == 0)
{
lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; 
x_1325 = lean_ctor_get(x_1324, 0);
lean_inc(x_1325);
x_1326 = lean_ctor_get(x_1324, 1);
lean_inc(x_1326);
lean_dec(x_1324);
x_1327 = lean_ctor_get(x_1325, 1);
lean_inc(x_1327);
x_1328 = lean_ctor_get(x_1325, 4);
lean_inc(x_1328);
lean_dec(x_1325);
x_1329 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_1327, x_1328, x_1323, x_15, x_16, x_17, x_18, x_1326);
if (lean_obj_tag(x_1329) == 0)
{
uint8_t x_1330; 
x_1330 = !lean_is_exclusive(x_1329);
if (x_1330 == 0)
{
return x_1329;
}
else
{
lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; 
x_1331 = lean_ctor_get(x_1329, 0);
x_1332 = lean_ctor_get(x_1329, 1);
lean_inc(x_1332);
lean_inc(x_1331);
lean_dec(x_1329);
x_1333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1333, 0, x_1331);
lean_ctor_set(x_1333, 1, x_1332);
return x_1333;
}
}
else
{
uint8_t x_1334; 
x_1334 = !lean_is_exclusive(x_1329);
if (x_1334 == 0)
{
return x_1329;
}
else
{
lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; 
x_1335 = lean_ctor_get(x_1329, 0);
x_1336 = lean_ctor_get(x_1329, 1);
lean_inc(x_1336);
lean_inc(x_1335);
lean_dec(x_1329);
x_1337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1337, 0, x_1335);
lean_ctor_set(x_1337, 1, x_1336);
return x_1337;
}
}
}
else
{
uint8_t x_1338; 
lean_dec(x_1323);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_1338 = !lean_is_exclusive(x_1324);
if (x_1338 == 0)
{
return x_1324;
}
else
{
lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; 
x_1339 = lean_ctor_get(x_1324, 0);
x_1340 = lean_ctor_get(x_1324, 1);
lean_inc(x_1340);
lean_inc(x_1339);
lean_dec(x_1324);
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
x_1315 = x_1344;
goto block_1342;
}
else
{
lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
lean_inc(x_1312);
x_1345 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1345, 0, x_1312);
x_1346 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__5;
x_1347 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1347, 0, x_1346);
lean_ctor_set(x_1347, 1, x_1345);
x_1348 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1349 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1348, x_1347, x_15, x_16, x_17, x_18, x_1344);
x_1350 = lean_ctor_get(x_1349, 1);
lean_inc(x_1350);
lean_dec(x_1349);
x_1315 = x_1350;
goto block_1342;
}
}
}
else
{
uint8_t x_1368; 
lean_dec(x_1306);
lean_dec(x_1298);
lean_dec(x_1283);
lean_dec(x_1268);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1368 = !lean_is_exclusive(x_1308);
if (x_1368 == 0)
{
return x_1308;
}
else
{
lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; 
x_1369 = lean_ctor_get(x_1308, 0);
x_1370 = lean_ctor_get(x_1308, 1);
lean_inc(x_1370);
lean_inc(x_1369);
lean_dec(x_1308);
x_1371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1371, 0, x_1369);
lean_ctor_set(x_1371, 1, x_1370);
return x_1371;
}
}
}
else
{
uint8_t x_1372; 
lean_dec(x_1298);
lean_dec(x_1283);
lean_dec(x_1268);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1372 = !lean_is_exclusive(x_1303);
if (x_1372 == 0)
{
return x_1303;
}
else
{
lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; 
x_1373 = lean_ctor_get(x_1303, 0);
x_1374 = lean_ctor_get(x_1303, 1);
lean_inc(x_1374);
lean_inc(x_1373);
lean_dec(x_1303);
x_1375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1375, 0, x_1373);
lean_ctor_set(x_1375, 1, x_1374);
return x_1375;
}
}
}
else
{
uint8_t x_1376; 
lean_dec(x_1283);
lean_dec(x_1268);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1376 = !lean_is_exclusive(x_1295);
if (x_1376 == 0)
{
return x_1295;
}
else
{
lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; 
x_1377 = lean_ctor_get(x_1295, 0);
x_1378 = lean_ctor_get(x_1295, 1);
lean_inc(x_1378);
lean_inc(x_1377);
lean_dec(x_1295);
x_1379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1379, 0, x_1377);
lean_ctor_set(x_1379, 1, x_1378);
return x_1379;
}
}
}
}
else
{
uint8_t x_1394; 
lean_dec(x_1283);
lean_dec(x_1272);
lean_dec(x_1268);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1394 = !lean_is_exclusive(x_1285);
if (x_1394 == 0)
{
return x_1285;
}
else
{
lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; 
x_1395 = lean_ctor_get(x_1285, 0);
x_1396 = lean_ctor_get(x_1285, 1);
lean_inc(x_1396);
lean_inc(x_1395);
lean_dec(x_1285);
x_1397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1397, 0, x_1395);
lean_ctor_set(x_1397, 1, x_1396);
return x_1397;
}
}
}
else
{
uint8_t x_1398; 
lean_dec(x_1272);
lean_dec(x_1268);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1398 = !lean_is_exclusive(x_1282);
if (x_1398 == 0)
{
return x_1282;
}
else
{
lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; 
x_1399 = lean_ctor_get(x_1282, 0);
x_1400 = lean_ctor_get(x_1282, 1);
lean_inc(x_1400);
lean_inc(x_1399);
lean_dec(x_1282);
x_1401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1401, 0, x_1399);
lean_ctor_set(x_1401, 1, x_1400);
return x_1401;
}
}
}
else
{
uint8_t x_1402; 
lean_dec(x_1268);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1402 = !lean_is_exclusive(x_1269);
if (x_1402 == 0)
{
return x_1269;
}
else
{
lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; 
x_1403 = lean_ctor_get(x_1269, 0);
x_1404 = lean_ctor_get(x_1269, 1);
lean_inc(x_1404);
lean_inc(x_1403);
lean_dec(x_1269);
x_1405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1405, 0, x_1403);
lean_ctor_set(x_1405, 1, x_1404);
return x_1405;
}
}
}
case 11:
{
lean_object* x_1406; lean_object* x_1407; 
lean_dec(x_14);
lean_dec(x_12);
x_1406 = lean_ctor_get(x_9, 5);
lean_inc(x_1406);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_1);
x_1407 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_8, x_11, x_13, x_1406, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_1407) == 0)
{
lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; 
x_1408 = lean_ctor_get(x_1407, 1);
lean_inc(x_1408);
lean_dec(x_1407);
x_1409 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_16, x_17, x_18, x_1408);
x_1410 = lean_ctor_get(x_1409, 0);
lean_inc(x_1410);
x_1411 = lean_ctor_get(x_1409, 1);
lean_inc(x_1411);
lean_dec(x_1409);
x_1412 = lean_ctor_get(x_9, 6);
lean_inc(x_1412);
x_1413 = l_List_redLength___main___rarg(x_1412);
x_1414 = lean_mk_empty_array_with_capacity(x_1413);
lean_dec(x_1413);
lean_inc(x_1412);
x_1415 = l_List_toArrayAux___main___rarg(x_1412, x_1414);
x_1416 = x_1415;
x_1417 = lean_unsigned_to_nat(0u);
lean_inc(x_1410);
lean_inc(x_8);
lean_inc(x_1);
x_1418 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_1418, 0, x_1);
lean_closure_set(x_1418, 1, x_8);
lean_closure_set(x_1418, 2, x_11);
lean_closure_set(x_1418, 3, x_13);
lean_closure_set(x_1418, 4, x_1410);
lean_closure_set(x_1418, 5, x_1412);
lean_closure_set(x_1418, 6, x_1417);
lean_closure_set(x_1418, 7, x_1416);
x_1419 = x_1418;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1420 = lean_apply_5(x_1419, x_15, x_16, x_17, x_18, x_1411);
if (lean_obj_tag(x_1420) == 0)
{
lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; 
x_1421 = lean_ctor_get(x_1420, 0);
lean_inc(x_1421);
x_1422 = lean_ctor_get(x_1420, 1);
lean_inc(x_1422);
lean_dec(x_1420);
lean_inc(x_1);
x_1423 = l_Lean_Meta_getMVarType(x_1, x_15, x_16, x_17, x_18, x_1422);
if (lean_obj_tag(x_1423) == 0)
{
lean_object* x_1424; lean_object* x_1425; uint8_t x_1426; lean_object* x_1427; 
x_1424 = lean_ctor_get(x_1423, 0);
lean_inc(x_1424);
x_1425 = lean_ctor_get(x_1423, 1);
lean_inc(x_1425);
lean_dec(x_1423);
x_1426 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
if (x_1426 == 0)
{
lean_object* x_1519; uint8_t x_1520; 
x_1519 = l_Lean_MetavarContext_exprDependsOn(x_1410, x_1424, x_2);
x_1520 = lean_unbox(x_1519);
lean_dec(x_1519);
if (x_1520 == 0)
{
x_1427 = x_1425;
goto block_1518;
}
else
{
lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; uint8_t x_1528; 
lean_dec(x_1421);
lean_dec(x_1406);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_1521 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1521, 0, x_3);
x_1522 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_1523 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1523, 0, x_1522);
lean_ctor_set(x_1523, 1, x_1521);
x_1524 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__8;
x_1525 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1525, 0, x_1523);
lean_ctor_set(x_1525, 1, x_1524);
x_1526 = lean_box(0);
x_1527 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_1, x_1525, x_1526, x_15, x_16, x_17, x_18, x_1425);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_1528 = !lean_is_exclusive(x_1527);
if (x_1528 == 0)
{
return x_1527;
}
else
{
lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; 
x_1529 = lean_ctor_get(x_1527, 0);
x_1530 = lean_ctor_get(x_1527, 1);
lean_inc(x_1530);
lean_inc(x_1529);
lean_dec(x_1527);
x_1531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1531, 0, x_1529);
lean_ctor_set(x_1531, 1, x_1530);
return x_1531;
}
}
}
else
{
lean_dec(x_1424);
lean_dec(x_1410);
x_1427 = x_1425;
goto block_1518;
}
block_1518:
{
lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; uint8_t x_1432; lean_object* x_1433; 
lean_inc(x_1421);
x_1428 = x_1421;
x_1429 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1417, x_1428);
x_1430 = x_1429;
x_1431 = lean_array_push(x_1430, x_2);
x_1432 = 1;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1433 = l_Lean_Meta_revert(x_1, x_1431, x_1432, x_15, x_16, x_17, x_18, x_1427);
if (lean_obj_tag(x_1433) == 0)
{
lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; uint8_t x_1440; lean_object* x_1441; 
x_1434 = lean_ctor_get(x_1433, 0);
lean_inc(x_1434);
x_1435 = lean_ctor_get(x_1433, 1);
lean_inc(x_1435);
lean_dec(x_1433);
x_1436 = lean_ctor_get(x_1434, 0);
lean_inc(x_1436);
x_1437 = lean_ctor_get(x_1434, 1);
lean_inc(x_1437);
lean_dec(x_1434);
x_1438 = lean_array_get_size(x_1421);
x_1439 = lean_box(0);
x_1440 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1441 = l_Lean_Meta_introN(x_1437, x_1438, x_1439, x_1440, x_15, x_16, x_17, x_18, x_1435);
if (lean_obj_tag(x_1441) == 0)
{
lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; 
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
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1446 = l_Lean_Meta_intro1(x_1445, x_1440, x_15, x_16, x_17, x_18, x_1443);
if (lean_obj_tag(x_1446) == 0)
{
lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; uint8_t x_1481; lean_object* x_1482; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; 
x_1447 = lean_ctor_get(x_1446, 0);
lean_inc(x_1447);
x_1448 = lean_ctor_get(x_1446, 1);
lean_inc(x_1448);
lean_dec(x_1446);
x_1449 = lean_ctor_get(x_1447, 0);
lean_inc(x_1449);
x_1450 = lean_ctor_get(x_1447, 1);
lean_inc(x_1450);
lean_dec(x_1447);
x_1451 = lean_box(0);
x_1452 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1421, x_1444, x_1421, x_1417, x_1451);
lean_dec(x_1421);
x_1490 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_1491 = lean_ctor_get(x_1490, 2);
lean_inc(x_1491);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1492 = lean_apply_5(x_1491, x_15, x_16, x_17, x_18, x_1448);
if (lean_obj_tag(x_1492) == 0)
{
lean_object* x_1493; uint8_t x_1494; 
x_1493 = lean_ctor_get(x_1492, 0);
lean_inc(x_1493);
x_1494 = lean_ctor_get_uint8(x_1493, sizeof(void*)*1);
lean_dec(x_1493);
if (x_1494 == 0)
{
lean_object* x_1495; 
x_1495 = lean_ctor_get(x_1492, 1);
lean_inc(x_1495);
lean_dec(x_1492);
x_1481 = x_1440;
x_1482 = x_1495;
goto block_1489;
}
else
{
lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; uint8_t x_1501; 
x_1496 = lean_ctor_get(x_1492, 1);
lean_inc(x_1496);
lean_dec(x_1492);
x_1497 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1498 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1497, x_15, x_16, x_17, x_18, x_1496);
x_1499 = lean_ctor_get(x_1498, 0);
lean_inc(x_1499);
x_1500 = lean_ctor_get(x_1498, 1);
lean_inc(x_1500);
lean_dec(x_1498);
x_1501 = lean_unbox(x_1499);
lean_dec(x_1499);
x_1481 = x_1501;
x_1482 = x_1500;
goto block_1489;
}
}
else
{
uint8_t x_1502; 
lean_dec(x_1452);
lean_dec(x_1450);
lean_dec(x_1449);
lean_dec(x_1444);
lean_dec(x_1436);
lean_dec(x_1406);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1502 = !lean_is_exclusive(x_1492);
if (x_1502 == 0)
{
return x_1492;
}
else
{
lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; 
x_1503 = lean_ctor_get(x_1492, 0);
x_1504 = lean_ctor_get(x_1492, 1);
lean_inc(x_1504);
lean_inc(x_1503);
lean_dec(x_1492);
x_1505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1505, 0, x_1503);
lean_ctor_set(x_1505, 1, x_1504);
return x_1505;
}
}
block_1480:
{
lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; 
x_1454 = x_1444;
x_1455 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1417, x_1454);
x_1456 = x_1455;
lean_inc(x_1449);
x_1457 = l_Lean_mkFVar(x_1449);
lean_inc(x_1450);
x_1458 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1458, 0, x_1450);
x_1459 = lean_box(x_1426);
lean_inc(x_1450);
x_1460 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 19, 13);
lean_closure_set(x_1460, 0, x_1449);
lean_closure_set(x_1460, 1, x_10);
lean_closure_set(x_1460, 2, x_1450);
lean_closure_set(x_1460, 3, x_3);
lean_closure_set(x_1460, 4, x_4);
lean_closure_set(x_1460, 5, x_8);
lean_closure_set(x_1460, 6, x_9);
lean_closure_set(x_1460, 7, x_1406);
lean_closure_set(x_1460, 8, x_1459);
lean_closure_set(x_1460, 9, x_1436);
lean_closure_set(x_1460, 10, x_1452);
lean_closure_set(x_1460, 11, x_1456);
lean_closure_set(x_1460, 12, x_1457);
x_1461 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_1461, 0, x_1458);
lean_closure_set(x_1461, 1, x_1460);
x_1462 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_1450, x_15, x_16, x_17, x_18, x_1453);
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
x_1467 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_1465, x_1466, x_1461, x_15, x_16, x_17, x_18, x_1464);
if (lean_obj_tag(x_1467) == 0)
{
uint8_t x_1468; 
x_1468 = !lean_is_exclusive(x_1467);
if (x_1468 == 0)
{
return x_1467;
}
else
{
lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; 
x_1469 = lean_ctor_get(x_1467, 0);
x_1470 = lean_ctor_get(x_1467, 1);
lean_inc(x_1470);
lean_inc(x_1469);
lean_dec(x_1467);
x_1471 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1471, 0, x_1469);
lean_ctor_set(x_1471, 1, x_1470);
return x_1471;
}
}
else
{
uint8_t x_1472; 
x_1472 = !lean_is_exclusive(x_1467);
if (x_1472 == 0)
{
return x_1467;
}
else
{
lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; 
x_1473 = lean_ctor_get(x_1467, 0);
x_1474 = lean_ctor_get(x_1467, 1);
lean_inc(x_1474);
lean_inc(x_1473);
lean_dec(x_1467);
x_1475 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1475, 0, x_1473);
lean_ctor_set(x_1475, 1, x_1474);
return x_1475;
}
}
}
else
{
uint8_t x_1476; 
lean_dec(x_1461);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_1476 = !lean_is_exclusive(x_1462);
if (x_1476 == 0)
{
return x_1462;
}
else
{
lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; 
x_1477 = lean_ctor_get(x_1462, 0);
x_1478 = lean_ctor_get(x_1462, 1);
lean_inc(x_1478);
lean_inc(x_1477);
lean_dec(x_1462);
x_1479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1479, 0, x_1477);
lean_ctor_set(x_1479, 1, x_1478);
return x_1479;
}
}
}
block_1489:
{
if (x_1481 == 0)
{
x_1453 = x_1482;
goto block_1480;
}
else
{
lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; 
lean_inc(x_1450);
x_1483 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1483, 0, x_1450);
x_1484 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__5;
x_1485 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1485, 0, x_1484);
lean_ctor_set(x_1485, 1, x_1483);
x_1486 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1487 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1486, x_1485, x_15, x_16, x_17, x_18, x_1482);
x_1488 = lean_ctor_get(x_1487, 1);
lean_inc(x_1488);
lean_dec(x_1487);
x_1453 = x_1488;
goto block_1480;
}
}
}
else
{
uint8_t x_1506; 
lean_dec(x_1444);
lean_dec(x_1436);
lean_dec(x_1421);
lean_dec(x_1406);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1506 = !lean_is_exclusive(x_1446);
if (x_1506 == 0)
{
return x_1446;
}
else
{
lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; 
x_1507 = lean_ctor_get(x_1446, 0);
x_1508 = lean_ctor_get(x_1446, 1);
lean_inc(x_1508);
lean_inc(x_1507);
lean_dec(x_1446);
x_1509 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1509, 0, x_1507);
lean_ctor_set(x_1509, 1, x_1508);
return x_1509;
}
}
}
else
{
uint8_t x_1510; 
lean_dec(x_1436);
lean_dec(x_1421);
lean_dec(x_1406);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1510 = !lean_is_exclusive(x_1441);
if (x_1510 == 0)
{
return x_1441;
}
else
{
lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; 
x_1511 = lean_ctor_get(x_1441, 0);
x_1512 = lean_ctor_get(x_1441, 1);
lean_inc(x_1512);
lean_inc(x_1511);
lean_dec(x_1441);
x_1513 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1513, 0, x_1511);
lean_ctor_set(x_1513, 1, x_1512);
return x_1513;
}
}
}
else
{
uint8_t x_1514; 
lean_dec(x_1421);
lean_dec(x_1406);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1514 = !lean_is_exclusive(x_1433);
if (x_1514 == 0)
{
return x_1433;
}
else
{
lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; 
x_1515 = lean_ctor_get(x_1433, 0);
x_1516 = lean_ctor_get(x_1433, 1);
lean_inc(x_1516);
lean_inc(x_1515);
lean_dec(x_1433);
x_1517 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1517, 0, x_1515);
lean_ctor_set(x_1517, 1, x_1516);
return x_1517;
}
}
}
}
else
{
uint8_t x_1532; 
lean_dec(x_1421);
lean_dec(x_1410);
lean_dec(x_1406);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1532 = !lean_is_exclusive(x_1423);
if (x_1532 == 0)
{
return x_1423;
}
else
{
lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; 
x_1533 = lean_ctor_get(x_1423, 0);
x_1534 = lean_ctor_get(x_1423, 1);
lean_inc(x_1534);
lean_inc(x_1533);
lean_dec(x_1423);
x_1535 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1535, 0, x_1533);
lean_ctor_set(x_1535, 1, x_1534);
return x_1535;
}
}
}
else
{
uint8_t x_1536; 
lean_dec(x_1410);
lean_dec(x_1406);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1536 = !lean_is_exclusive(x_1420);
if (x_1536 == 0)
{
return x_1420;
}
else
{
lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; 
x_1537 = lean_ctor_get(x_1420, 0);
x_1538 = lean_ctor_get(x_1420, 1);
lean_inc(x_1538);
lean_inc(x_1537);
lean_dec(x_1420);
x_1539 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1539, 0, x_1537);
lean_ctor_set(x_1539, 1, x_1538);
return x_1539;
}
}
}
else
{
uint8_t x_1540; 
lean_dec(x_1406);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1540 = !lean_is_exclusive(x_1407);
if (x_1540 == 0)
{
return x_1407;
}
else
{
lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; 
x_1541 = lean_ctor_get(x_1407, 0);
x_1542 = lean_ctor_get(x_1407, 1);
lean_inc(x_1542);
lean_inc(x_1541);
lean_dec(x_1407);
x_1543 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1543, 0, x_1541);
lean_ctor_set(x_1543, 1, x_1542);
return x_1543;
}
}
}
default: 
{
lean_object* x_1544; lean_object* x_1545; 
lean_dec(x_14);
lean_dec(x_12);
x_1544 = lean_ctor_get(x_9, 5);
lean_inc(x_1544);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_1);
x_1545 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_8, x_11, x_13, x_1544, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_1545) == 0)
{
lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; 
x_1546 = lean_ctor_get(x_1545, 1);
lean_inc(x_1546);
lean_dec(x_1545);
x_1547 = l_Lean_Meta_getMCtx___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_16, x_17, x_18, x_1546);
x_1548 = lean_ctor_get(x_1547, 0);
lean_inc(x_1548);
x_1549 = lean_ctor_get(x_1547, 1);
lean_inc(x_1549);
lean_dec(x_1547);
x_1550 = lean_ctor_get(x_9, 6);
lean_inc(x_1550);
x_1551 = l_List_redLength___main___rarg(x_1550);
x_1552 = lean_mk_empty_array_with_capacity(x_1551);
lean_dec(x_1551);
lean_inc(x_1550);
x_1553 = l_List_toArrayAux___main___rarg(x_1550, x_1552);
x_1554 = x_1553;
x_1555 = lean_unsigned_to_nat(0u);
lean_inc(x_1548);
lean_inc(x_8);
lean_inc(x_1);
x_1556 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_1556, 0, x_1);
lean_closure_set(x_1556, 1, x_8);
lean_closure_set(x_1556, 2, x_11);
lean_closure_set(x_1556, 3, x_13);
lean_closure_set(x_1556, 4, x_1548);
lean_closure_set(x_1556, 5, x_1550);
lean_closure_set(x_1556, 6, x_1555);
lean_closure_set(x_1556, 7, x_1554);
x_1557 = x_1556;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1558 = lean_apply_5(x_1557, x_15, x_16, x_17, x_18, x_1549);
if (lean_obj_tag(x_1558) == 0)
{
lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; 
x_1559 = lean_ctor_get(x_1558, 0);
lean_inc(x_1559);
x_1560 = lean_ctor_get(x_1558, 1);
lean_inc(x_1560);
lean_dec(x_1558);
lean_inc(x_1);
x_1561 = l_Lean_Meta_getMVarType(x_1, x_15, x_16, x_17, x_18, x_1560);
if (lean_obj_tag(x_1561) == 0)
{
lean_object* x_1562; lean_object* x_1563; uint8_t x_1564; lean_object* x_1565; 
x_1562 = lean_ctor_get(x_1561, 0);
lean_inc(x_1562);
x_1563 = lean_ctor_get(x_1561, 1);
lean_inc(x_1563);
lean_dec(x_1561);
x_1564 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
if (x_1564 == 0)
{
lean_object* x_1657; uint8_t x_1658; 
x_1657 = l_Lean_MetavarContext_exprDependsOn(x_1548, x_1562, x_2);
x_1658 = lean_unbox(x_1657);
lean_dec(x_1657);
if (x_1658 == 0)
{
x_1565 = x_1563;
goto block_1656;
}
else
{
lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; uint8_t x_1666; 
lean_dec(x_1559);
lean_dec(x_1544);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_1659 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1659, 0, x_3);
x_1660 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_1661 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1661, 0, x_1660);
lean_ctor_set(x_1661, 1, x_1659);
x_1662 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__8;
x_1663 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1663, 0, x_1661);
lean_ctor_set(x_1663, 1, x_1662);
x_1664 = lean_box(0);
x_1665 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_1, x_1663, x_1664, x_15, x_16, x_17, x_18, x_1563);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_1666 = !lean_is_exclusive(x_1665);
if (x_1666 == 0)
{
return x_1665;
}
else
{
lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; 
x_1667 = lean_ctor_get(x_1665, 0);
x_1668 = lean_ctor_get(x_1665, 1);
lean_inc(x_1668);
lean_inc(x_1667);
lean_dec(x_1665);
x_1669 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1669, 0, x_1667);
lean_ctor_set(x_1669, 1, x_1668);
return x_1669;
}
}
}
else
{
lean_dec(x_1562);
lean_dec(x_1548);
x_1565 = x_1563;
goto block_1656;
}
block_1656:
{
lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; uint8_t x_1570; lean_object* x_1571; 
lean_inc(x_1559);
x_1566 = x_1559;
x_1567 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1555, x_1566);
x_1568 = x_1567;
x_1569 = lean_array_push(x_1568, x_2);
x_1570 = 1;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1571 = l_Lean_Meta_revert(x_1, x_1569, x_1570, x_15, x_16, x_17, x_18, x_1565);
if (lean_obj_tag(x_1571) == 0)
{
lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; uint8_t x_1578; lean_object* x_1579; 
x_1572 = lean_ctor_get(x_1571, 0);
lean_inc(x_1572);
x_1573 = lean_ctor_get(x_1571, 1);
lean_inc(x_1573);
lean_dec(x_1571);
x_1574 = lean_ctor_get(x_1572, 0);
lean_inc(x_1574);
x_1575 = lean_ctor_get(x_1572, 1);
lean_inc(x_1575);
lean_dec(x_1572);
x_1576 = lean_array_get_size(x_1559);
x_1577 = lean_box(0);
x_1578 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1579 = l_Lean_Meta_introN(x_1575, x_1576, x_1577, x_1578, x_15, x_16, x_17, x_18, x_1573);
if (lean_obj_tag(x_1579) == 0)
{
lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; 
x_1580 = lean_ctor_get(x_1579, 0);
lean_inc(x_1580);
x_1581 = lean_ctor_get(x_1579, 1);
lean_inc(x_1581);
lean_dec(x_1579);
x_1582 = lean_ctor_get(x_1580, 0);
lean_inc(x_1582);
x_1583 = lean_ctor_get(x_1580, 1);
lean_inc(x_1583);
lean_dec(x_1580);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1584 = l_Lean_Meta_intro1(x_1583, x_1578, x_15, x_16, x_17, x_18, x_1581);
if (lean_obj_tag(x_1584) == 0)
{
lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; uint8_t x_1619; lean_object* x_1620; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; 
x_1585 = lean_ctor_get(x_1584, 0);
lean_inc(x_1585);
x_1586 = lean_ctor_get(x_1584, 1);
lean_inc(x_1586);
lean_dec(x_1584);
x_1587 = lean_ctor_get(x_1585, 0);
lean_inc(x_1587);
x_1588 = lean_ctor_get(x_1585, 1);
lean_inc(x_1588);
lean_dec(x_1585);
x_1589 = lean_box(0);
x_1590 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1559, x_1582, x_1559, x_1555, x_1589);
lean_dec(x_1559);
x_1628 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_1629 = lean_ctor_get(x_1628, 2);
lean_inc(x_1629);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_1630 = lean_apply_5(x_1629, x_15, x_16, x_17, x_18, x_1586);
if (lean_obj_tag(x_1630) == 0)
{
lean_object* x_1631; uint8_t x_1632; 
x_1631 = lean_ctor_get(x_1630, 0);
lean_inc(x_1631);
x_1632 = lean_ctor_get_uint8(x_1631, sizeof(void*)*1);
lean_dec(x_1631);
if (x_1632 == 0)
{
lean_object* x_1633; 
x_1633 = lean_ctor_get(x_1630, 1);
lean_inc(x_1633);
lean_dec(x_1630);
x_1619 = x_1578;
x_1620 = x_1633;
goto block_1627;
}
else
{
lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; uint8_t x_1639; 
x_1634 = lean_ctor_get(x_1630, 1);
lean_inc(x_1634);
lean_dec(x_1630);
x_1635 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1636 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_1635, x_15, x_16, x_17, x_18, x_1634);
x_1637 = lean_ctor_get(x_1636, 0);
lean_inc(x_1637);
x_1638 = lean_ctor_get(x_1636, 1);
lean_inc(x_1638);
lean_dec(x_1636);
x_1639 = lean_unbox(x_1637);
lean_dec(x_1637);
x_1619 = x_1639;
x_1620 = x_1638;
goto block_1627;
}
}
else
{
uint8_t x_1640; 
lean_dec(x_1590);
lean_dec(x_1588);
lean_dec(x_1587);
lean_dec(x_1582);
lean_dec(x_1574);
lean_dec(x_1544);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1640 = !lean_is_exclusive(x_1630);
if (x_1640 == 0)
{
return x_1630;
}
else
{
lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; 
x_1641 = lean_ctor_get(x_1630, 0);
x_1642 = lean_ctor_get(x_1630, 1);
lean_inc(x_1642);
lean_inc(x_1641);
lean_dec(x_1630);
x_1643 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1643, 0, x_1641);
lean_ctor_set(x_1643, 1, x_1642);
return x_1643;
}
}
block_1618:
{
lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; 
x_1592 = x_1582;
x_1593 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1555, x_1592);
x_1594 = x_1593;
lean_inc(x_1587);
x_1595 = l_Lean_mkFVar(x_1587);
lean_inc(x_1588);
x_1596 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1596, 0, x_1588);
x_1597 = lean_box(x_1564);
lean_inc(x_1588);
x_1598 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 19, 13);
lean_closure_set(x_1598, 0, x_1587);
lean_closure_set(x_1598, 1, x_10);
lean_closure_set(x_1598, 2, x_1588);
lean_closure_set(x_1598, 3, x_3);
lean_closure_set(x_1598, 4, x_4);
lean_closure_set(x_1598, 5, x_8);
lean_closure_set(x_1598, 6, x_9);
lean_closure_set(x_1598, 7, x_1544);
lean_closure_set(x_1598, 8, x_1597);
lean_closure_set(x_1598, 9, x_1574);
lean_closure_set(x_1598, 10, x_1590);
lean_closure_set(x_1598, 11, x_1594);
lean_closure_set(x_1598, 12, x_1595);
x_1599 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_1599, 0, x_1596);
lean_closure_set(x_1599, 1, x_1598);
x_1600 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_1588, x_15, x_16, x_17, x_18, x_1591);
if (lean_obj_tag(x_1600) == 0)
{
lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; 
x_1601 = lean_ctor_get(x_1600, 0);
lean_inc(x_1601);
x_1602 = lean_ctor_get(x_1600, 1);
lean_inc(x_1602);
lean_dec(x_1600);
x_1603 = lean_ctor_get(x_1601, 1);
lean_inc(x_1603);
x_1604 = lean_ctor_get(x_1601, 4);
lean_inc(x_1604);
lean_dec(x_1601);
x_1605 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_1603, x_1604, x_1599, x_15, x_16, x_17, x_18, x_1602);
if (lean_obj_tag(x_1605) == 0)
{
uint8_t x_1606; 
x_1606 = !lean_is_exclusive(x_1605);
if (x_1606 == 0)
{
return x_1605;
}
else
{
lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; 
x_1607 = lean_ctor_get(x_1605, 0);
x_1608 = lean_ctor_get(x_1605, 1);
lean_inc(x_1608);
lean_inc(x_1607);
lean_dec(x_1605);
x_1609 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1609, 0, x_1607);
lean_ctor_set(x_1609, 1, x_1608);
return x_1609;
}
}
else
{
uint8_t x_1610; 
x_1610 = !lean_is_exclusive(x_1605);
if (x_1610 == 0)
{
return x_1605;
}
else
{
lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; 
x_1611 = lean_ctor_get(x_1605, 0);
x_1612 = lean_ctor_get(x_1605, 1);
lean_inc(x_1612);
lean_inc(x_1611);
lean_dec(x_1605);
x_1613 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1613, 0, x_1611);
lean_ctor_set(x_1613, 1, x_1612);
return x_1613;
}
}
}
else
{
uint8_t x_1614; 
lean_dec(x_1599);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_1614 = !lean_is_exclusive(x_1600);
if (x_1614 == 0)
{
return x_1600;
}
else
{
lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; 
x_1615 = lean_ctor_get(x_1600, 0);
x_1616 = lean_ctor_get(x_1600, 1);
lean_inc(x_1616);
lean_inc(x_1615);
lean_dec(x_1600);
x_1617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1617, 0, x_1615);
lean_ctor_set(x_1617, 1, x_1616);
return x_1617;
}
}
}
block_1627:
{
if (x_1619 == 0)
{
x_1591 = x_1620;
goto block_1618;
}
else
{
lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; 
lean_inc(x_1588);
x_1621 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_1621, 0, x_1588);
x_1622 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__5;
x_1623 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1623, 0, x_1622);
lean_ctor_set(x_1623, 1, x_1621);
x_1624 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1625 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_1624, x_1623, x_15, x_16, x_17, x_18, x_1620);
x_1626 = lean_ctor_get(x_1625, 1);
lean_inc(x_1626);
lean_dec(x_1625);
x_1591 = x_1626;
goto block_1618;
}
}
}
else
{
uint8_t x_1644; 
lean_dec(x_1582);
lean_dec(x_1574);
lean_dec(x_1559);
lean_dec(x_1544);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1644 = !lean_is_exclusive(x_1584);
if (x_1644 == 0)
{
return x_1584;
}
else
{
lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; 
x_1645 = lean_ctor_get(x_1584, 0);
x_1646 = lean_ctor_get(x_1584, 1);
lean_inc(x_1646);
lean_inc(x_1645);
lean_dec(x_1584);
x_1647 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1647, 0, x_1645);
lean_ctor_set(x_1647, 1, x_1646);
return x_1647;
}
}
}
else
{
uint8_t x_1648; 
lean_dec(x_1574);
lean_dec(x_1559);
lean_dec(x_1544);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1648 = !lean_is_exclusive(x_1579);
if (x_1648 == 0)
{
return x_1579;
}
else
{
lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; 
x_1649 = lean_ctor_get(x_1579, 0);
x_1650 = lean_ctor_get(x_1579, 1);
lean_inc(x_1650);
lean_inc(x_1649);
lean_dec(x_1579);
x_1651 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1651, 0, x_1649);
lean_ctor_set(x_1651, 1, x_1650);
return x_1651;
}
}
}
else
{
uint8_t x_1652; 
lean_dec(x_1559);
lean_dec(x_1544);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_1652 = !lean_is_exclusive(x_1571);
if (x_1652 == 0)
{
return x_1571;
}
else
{
lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; 
x_1653 = lean_ctor_get(x_1571, 0);
x_1654 = lean_ctor_get(x_1571, 1);
lean_inc(x_1654);
lean_inc(x_1653);
lean_dec(x_1571);
x_1655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1655, 0, x_1653);
lean_ctor_set(x_1655, 1, x_1654);
return x_1655;
}
}
}
}
else
{
uint8_t x_1670; 
lean_dec(x_1559);
lean_dec(x_1548);
lean_dec(x_1544);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1670 = !lean_is_exclusive(x_1561);
if (x_1670 == 0)
{
return x_1561;
}
else
{
lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; 
x_1671 = lean_ctor_get(x_1561, 0);
x_1672 = lean_ctor_get(x_1561, 1);
lean_inc(x_1672);
lean_inc(x_1671);
lean_dec(x_1561);
x_1673 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1673, 0, x_1671);
lean_ctor_set(x_1673, 1, x_1672);
return x_1673;
}
}
}
else
{
uint8_t x_1674; 
lean_dec(x_1548);
lean_dec(x_1544);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1674 = !lean_is_exclusive(x_1558);
if (x_1674 == 0)
{
return x_1558;
}
else
{
lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; 
x_1675 = lean_ctor_get(x_1558, 0);
x_1676 = lean_ctor_get(x_1558, 1);
lean_inc(x_1676);
lean_inc(x_1675);
lean_dec(x_1558);
x_1677 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1677, 0, x_1675);
lean_ctor_set(x_1677, 1, x_1676);
return x_1677;
}
}
}
else
{
uint8_t x_1678; 
lean_dec(x_1544);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1678 = !lean_is_exclusive(x_1545);
if (x_1678 == 0)
{
return x_1545;
}
else
{
lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; 
x_1679 = lean_ctor_get(x_1545, 0);
x_1680 = lean_ctor_get(x_1545, 1);
lean_inc(x_1680);
lean_inc(x_1679);
lean_dec(x_1545);
x_1681 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1681, 0, x_1679);
lean_ctor_set(x_1681, 1, x_1680);
return x_1681;
}
}
}
}
}
}
lean_object* l_Lean_Meta_induction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_1);
x_15 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_19 = l_Lean_Meta_mkRecursorInfo(x_2, x_18, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_LocalDecl_type(x_16);
lean_dec(x_16);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_22);
x_24 = l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(x_22, x_23, x_10, x_11, x_12, x_13, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(x_3, x_22, x_10, x_11, x_12, x_13, x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
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
lean_inc(x_29);
x_36 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12(x_3, x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_20, x_23, x_29, x_29, x_33, x_35, x_10, x_11, x_12, x_13, x_28);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
return x_19;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_19, 0);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_19);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_15);
if (x_45 == 0)
{
return x_15;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_15, 0);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_15);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Meta_induction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__2;
x_14 = l___private_Lean_Meta_Basic_13__forallTelescopeReducingAuxAux___main___rarg___closed__3;
x_15 = l_Lean_Meta_getParamNamesImpl___closed__1;
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_induction___lambda__1___boxed), 14, 8);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_3);
lean_closure_set(x_16, 2, x_1);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_13);
lean_closure_set(x_16, 5, x_14);
lean_closure_set(x_16, 6, x_15);
lean_closure_set(x_16, 7, x_11);
x_17 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_17, 0, x_12);
lean_closure_set(x_17, 1, x_16);
x_18 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 4);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_21, x_22, x_17, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
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
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
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
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
return x_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_induction___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_List_elem___main___at_Lean_Meta_induction___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___main___at_Lean_Meta_induction___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_16;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
return x_14;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_foldlM___main___at_Lean_Meta_induction___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___boxed(lean_object** _args) {
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
x_23 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11(x_1, x_2, x_3, x_4, x_5, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_23;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed(lean_object** _args) {
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
x_21 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_21;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___boxed(lean_object** _args) {
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
lean_object* x_20; 
x_20 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_20;
}
}
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_induction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
lean_object* l_Lean_Meta_induction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_induction(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
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
l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1 = _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1();
lean_mark_persistent(l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1);
l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2 = _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2();
lean_mark_persistent(l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2);
l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3 = _init_l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3();
lean_mark_persistent(l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__2);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__7);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8);
l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9 = _init_l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9();
lean_mark_persistent(l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__3);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__5);
l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6 = _init_l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__6);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__2);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__4);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__7);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__9 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__9();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__9);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__2 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__2);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__3 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__3);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__5 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__5);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__6 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__6();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__6);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__7 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__7();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__7);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__8 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__8();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__8);
res = l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
