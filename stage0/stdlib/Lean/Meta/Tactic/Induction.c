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
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_induction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize___main(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity(lean_object*);
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_induction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3;
lean_object* l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__1;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___boxed(lean_object**);
lean_object* l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__2;
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_elem___main___at_Lean_Meta_induction___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__1;
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__4;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__4;
lean_object* l_Lean_WHNF_whnfEasyCases___main___at_Lean_Meta_induction___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2;
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_5__finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity___main(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__7;
uint8_t l_Lean_Expr_isHeadBetaTarget(lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__1;
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_getParamNamesImpl___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__1;
lean_object* l_List_forM___main___at_Lean_Meta_induction___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_Lean_Meta_induction___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed(lean_object*, lean_object*);
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
extern lean_object* l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed(lean_object**);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3;
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___boxed(lean_object**);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__3;
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
lean_inc(x_16);
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
lean_inc(x_16);
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
lean_inc(x_3);
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
lean_inc(x_11);
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
x_58 = l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3;
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
lean_inc(x_17);
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
lean_inc(x_17);
x_64 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_63, x_12, x_17, x_18, x_19, x_20, x_61);
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
lean_inc(x_17);
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
lean_inc(x_17);
x_104 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_103, x_12, x_17, x_18, x_19, x_20, x_101);
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
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after revert&intro");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__3;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__4;
x_5 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
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
lean_inc(x_15);
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
x_1 = lean_mk_string("' does not support dependent elimination, but conclusion depends on major premise");
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
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
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
x_19 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_6, x_9, x_11, x_18, x_13, x_14, x_15, x_16, x_17);
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
x_31 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
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
lean_object* x_109; uint8_t x_110; 
x_109 = l_Lean_MetavarContext_exprDependsOn(x_24, x_37, x_2);
x_110 = lean_unbox(x_109);
lean_dec(x_109);
if (x_110 == 0)
{
x_40 = x_38;
goto block_108;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_111 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_111, 0, x_3);
x_112 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_113 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
x_114 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_115 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_box(0);
x_117 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_115, x_116, x_13, x_14, x_15, x_16, x_38);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
return x_117;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_117);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_24);
x_40 = x_38;
goto block_108;
}
block_108:
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
lean_inc(x_13);
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
lean_inc(x_13);
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
lean_inc(x_13);
x_59 = l_Lean_Meta_intro1(x_58, x_53, x_13, x_14, x_15, x_16, x_56);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
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
x_65 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_34, x_57, x_34, x_30, x_64);
lean_dec(x_34);
lean_inc(x_63);
x_66 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_66, 0, x_63);
x_67 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_68 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_67, x_66, x_13, x_14, x_15, x_16, x_61);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = x_57;
x_71 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_30, x_70);
x_72 = x_71;
lean_inc(x_62);
x_73 = l_Lean_mkFVar(x_62);
lean_inc(x_63);
x_74 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_74, 0, x_63);
x_75 = lean_box(x_39);
lean_inc(x_63);
x_76 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_76, 0, x_62);
lean_closure_set(x_76, 1, x_8);
lean_closure_set(x_76, 2, x_63);
lean_closure_set(x_76, 3, x_3);
lean_closure_set(x_76, 4, x_4);
lean_closure_set(x_76, 5, x_6);
lean_closure_set(x_76, 6, x_7);
lean_closure_set(x_76, 7, x_18);
lean_closure_set(x_76, 8, x_75);
lean_closure_set(x_76, 9, x_49);
lean_closure_set(x_76, 10, x_65);
lean_closure_set(x_76, 11, x_72);
lean_closure_set(x_76, 12, x_73);
x_77 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_77, 0, x_74);
lean_closure_set(x_77, 1, x_76);
x_78 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_63, x_13, x_14, x_15, x_16, x_69);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 4);
lean_inc(x_82);
lean_dec(x_79);
x_83 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_81, x_82, x_77, x_13, x_14, x_15, x_16, x_80);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
return x_83;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_83);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_83);
if (x_88 == 0)
{
return x_83;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_83, 0);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_83);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_77);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_92 = !lean_is_exclusive(x_78);
if (x_92 == 0)
{
return x_78;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_78, 0);
x_94 = lean_ctor_get(x_78, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_78);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
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
x_96 = !lean_is_exclusive(x_59);
if (x_96 == 0)
{
return x_59;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_59, 0);
x_98 = lean_ctor_get(x_59, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_59);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
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
x_100 = !lean_is_exclusive(x_54);
if (x_100 == 0)
{
return x_54;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_54, 0);
x_102 = lean_ctor_get(x_54, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_54);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
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
x_104 = !lean_is_exclusive(x_46);
if (x_104 == 0)
{
return x_46;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_46, 0);
x_106 = lean_ctor_get(x_46, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_46);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
else
{
uint8_t x_122; 
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
x_122 = !lean_is_exclusive(x_36);
if (x_122 == 0)
{
return x_36;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_36, 0);
x_124 = lean_ctor_get(x_36, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_36);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
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
x_126 = !lean_is_exclusive(x_33);
if (x_126 == 0)
{
return x_33;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_33, 0);
x_128 = lean_ctor_get(x_33, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_33);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
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
x_130 = !lean_is_exclusive(x_19);
if (x_130 == 0)
{
return x_19;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_19, 0);
x_132 = lean_ctor_get(x_19, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_19);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
case 1:
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_12);
lean_dec(x_10);
x_134 = lean_ctor_get(x_7, 5);
lean_inc(x_134);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_135 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_6, x_9, x_11, x_134, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_st_ref_get(x_14, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_ctor_get(x_7, 6);
lean_inc(x_141);
x_142 = l_List_redLength___main___rarg(x_141);
x_143 = lean_mk_empty_array_with_capacity(x_142);
lean_dec(x_142);
lean_inc(x_141);
x_144 = l_List_toArrayAux___main___rarg(x_141, x_143);
x_145 = x_144;
x_146 = lean_unsigned_to_nat(0u);
lean_inc(x_140);
lean_inc(x_6);
lean_inc(x_1);
x_147 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_147, 0, x_1);
lean_closure_set(x_147, 1, x_6);
lean_closure_set(x_147, 2, x_9);
lean_closure_set(x_147, 3, x_11);
lean_closure_set(x_147, 4, x_140);
lean_closure_set(x_147, 5, x_141);
lean_closure_set(x_147, 6, x_146);
lean_closure_set(x_147, 7, x_145);
x_148 = x_147;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_149 = lean_apply_5(x_148, x_13, x_14, x_15, x_16, x_139);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
lean_inc(x_1);
x_152 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_155 == 0)
{
lean_object* x_225; uint8_t x_226; 
x_225 = l_Lean_MetavarContext_exprDependsOn(x_140, x_153, x_2);
x_226 = lean_unbox(x_225);
lean_dec(x_225);
if (x_226 == 0)
{
x_156 = x_154;
goto block_224;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
lean_dec(x_150);
lean_dec(x_134);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_227 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_227, 0, x_3);
x_228 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_229 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
x_230 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_231 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_box(0);
x_233 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_231, x_232, x_13, x_14, x_15, x_16, x_154);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_234 = !lean_is_exclusive(x_233);
if (x_234 == 0)
{
return x_233;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_233, 0);
x_236 = lean_ctor_get(x_233, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_233);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
else
{
lean_dec(x_153);
lean_dec(x_140);
x_156 = x_154;
goto block_224;
}
block_224:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; 
lean_inc(x_150);
x_157 = x_150;
x_158 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_146, x_157);
x_159 = x_158;
x_160 = lean_array_push(x_159, x_2);
x_161 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_162 = l_Lean_Meta_revert(x_1, x_160, x_161, x_13, x_14, x_15, x_16, x_156);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = lean_array_get_size(x_150);
x_168 = lean_box(0);
x_169 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_170 = l_Lean_Meta_introN(x_166, x_167, x_168, x_169, x_13, x_14, x_15, x_16, x_164);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_175 = l_Lean_Meta_intro1(x_174, x_169, x_13, x_14, x_15, x_16, x_172);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
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
x_180 = lean_box(0);
x_181 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_150, x_173, x_150, x_146, x_180);
lean_dec(x_150);
lean_inc(x_179);
x_182 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_182, 0, x_179);
x_183 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_184 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_183, x_182, x_13, x_14, x_15, x_16, x_177);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec(x_184);
x_186 = x_173;
x_187 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_146, x_186);
x_188 = x_187;
lean_inc(x_178);
x_189 = l_Lean_mkFVar(x_178);
lean_inc(x_179);
x_190 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_190, 0, x_179);
x_191 = lean_box(x_155);
lean_inc(x_179);
x_192 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_192, 0, x_178);
lean_closure_set(x_192, 1, x_8);
lean_closure_set(x_192, 2, x_179);
lean_closure_set(x_192, 3, x_3);
lean_closure_set(x_192, 4, x_4);
lean_closure_set(x_192, 5, x_6);
lean_closure_set(x_192, 6, x_7);
lean_closure_set(x_192, 7, x_134);
lean_closure_set(x_192, 8, x_191);
lean_closure_set(x_192, 9, x_165);
lean_closure_set(x_192, 10, x_181);
lean_closure_set(x_192, 11, x_188);
lean_closure_set(x_192, 12, x_189);
x_193 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_193, 0, x_190);
lean_closure_set(x_193, 1, x_192);
x_194 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_179, x_13, x_14, x_15, x_16, x_185);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_195, 4);
lean_inc(x_198);
lean_dec(x_195);
x_199 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_197, x_198, x_193, x_13, x_14, x_15, x_16, x_196);
if (lean_obj_tag(x_199) == 0)
{
uint8_t x_200; 
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
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_199);
if (x_204 == 0)
{
return x_199;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_199, 0);
x_206 = lean_ctor_get(x_199, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_199);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_193);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_208 = !lean_is_exclusive(x_194);
if (x_208 == 0)
{
return x_194;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_194, 0);
x_210 = lean_ctor_get(x_194, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_194);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
else
{
uint8_t x_212; 
lean_dec(x_173);
lean_dec(x_165);
lean_dec(x_150);
lean_dec(x_134);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_212 = !lean_is_exclusive(x_175);
if (x_212 == 0)
{
return x_175;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_175, 0);
x_214 = lean_ctor_get(x_175, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_175);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_165);
lean_dec(x_150);
lean_dec(x_134);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_216 = !lean_is_exclusive(x_170);
if (x_216 == 0)
{
return x_170;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_170, 0);
x_218 = lean_ctor_get(x_170, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_170);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
else
{
uint8_t x_220; 
lean_dec(x_150);
lean_dec(x_134);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_220 = !lean_is_exclusive(x_162);
if (x_220 == 0)
{
return x_162;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_162, 0);
x_222 = lean_ctor_get(x_162, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_162);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_150);
lean_dec(x_140);
lean_dec(x_134);
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
x_238 = !lean_is_exclusive(x_152);
if (x_238 == 0)
{
return x_152;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_152, 0);
x_240 = lean_ctor_get(x_152, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_152);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_140);
lean_dec(x_134);
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
x_242 = !lean_is_exclusive(x_149);
if (x_242 == 0)
{
return x_149;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_149, 0);
x_244 = lean_ctor_get(x_149, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_149);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
else
{
uint8_t x_246; 
lean_dec(x_134);
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
x_246 = !lean_is_exclusive(x_135);
if (x_246 == 0)
{
return x_135;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_135, 0);
x_248 = lean_ctor_get(x_135, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_135);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
case 2:
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_12);
lean_dec(x_10);
x_250 = lean_ctor_get(x_7, 5);
lean_inc(x_250);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_251 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_6, x_9, x_11, x_250, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
lean_dec(x_251);
x_253 = lean_st_ref_get(x_14, x_252);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_ctor_get(x_254, 0);
lean_inc(x_256);
lean_dec(x_254);
x_257 = lean_ctor_get(x_7, 6);
lean_inc(x_257);
x_258 = l_List_redLength___main___rarg(x_257);
x_259 = lean_mk_empty_array_with_capacity(x_258);
lean_dec(x_258);
lean_inc(x_257);
x_260 = l_List_toArrayAux___main___rarg(x_257, x_259);
x_261 = x_260;
x_262 = lean_unsigned_to_nat(0u);
lean_inc(x_256);
lean_inc(x_6);
lean_inc(x_1);
x_263 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_263, 0, x_1);
lean_closure_set(x_263, 1, x_6);
lean_closure_set(x_263, 2, x_9);
lean_closure_set(x_263, 3, x_11);
lean_closure_set(x_263, 4, x_256);
lean_closure_set(x_263, 5, x_257);
lean_closure_set(x_263, 6, x_262);
lean_closure_set(x_263, 7, x_261);
x_264 = x_263;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_265 = lean_apply_5(x_264, x_13, x_14, x_15, x_16, x_255);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
lean_inc(x_1);
x_268 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_267);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_271 == 0)
{
lean_object* x_341; uint8_t x_342; 
x_341 = l_Lean_MetavarContext_exprDependsOn(x_256, x_269, x_2);
x_342 = lean_unbox(x_341);
lean_dec(x_341);
if (x_342 == 0)
{
x_272 = x_270;
goto block_340;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; 
lean_dec(x_266);
lean_dec(x_250);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_343 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_343, 0, x_3);
x_344 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_345 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_343);
x_346 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_347 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
x_348 = lean_box(0);
x_349 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_347, x_348, x_13, x_14, x_15, x_16, x_270);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
return x_349;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_349, 0);
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_349);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
return x_353;
}
}
}
else
{
lean_dec(x_269);
lean_dec(x_256);
x_272 = x_270;
goto block_340;
}
block_340:
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; 
lean_inc(x_266);
x_273 = x_266;
x_274 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_262, x_273);
x_275 = x_274;
x_276 = lean_array_push(x_275, x_2);
x_277 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_278 = l_Lean_Meta_revert(x_1, x_276, x_277, x_13, x_14, x_15, x_16, x_272);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
x_281 = lean_ctor_get(x_279, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_279, 1);
lean_inc(x_282);
lean_dec(x_279);
x_283 = lean_array_get_size(x_266);
x_284 = lean_box(0);
x_285 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_286 = l_Lean_Meta_introN(x_282, x_283, x_284, x_285, x_13, x_14, x_15, x_16, x_280);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_ctor_get(x_287, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_287, 1);
lean_inc(x_290);
lean_dec(x_287);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_291 = l_Lean_Meta_intro1(x_290, x_285, x_13, x_14, x_15, x_16, x_288);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
x_294 = lean_ctor_get(x_292, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_292, 1);
lean_inc(x_295);
lean_dec(x_292);
x_296 = lean_box(0);
x_297 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_266, x_289, x_266, x_262, x_296);
lean_dec(x_266);
lean_inc(x_295);
x_298 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_298, 0, x_295);
x_299 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_300 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_299, x_298, x_13, x_14, x_15, x_16, x_293);
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
lean_dec(x_300);
x_302 = x_289;
x_303 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_262, x_302);
x_304 = x_303;
lean_inc(x_294);
x_305 = l_Lean_mkFVar(x_294);
lean_inc(x_295);
x_306 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_306, 0, x_295);
x_307 = lean_box(x_271);
lean_inc(x_295);
x_308 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_308, 0, x_294);
lean_closure_set(x_308, 1, x_8);
lean_closure_set(x_308, 2, x_295);
lean_closure_set(x_308, 3, x_3);
lean_closure_set(x_308, 4, x_4);
lean_closure_set(x_308, 5, x_6);
lean_closure_set(x_308, 6, x_7);
lean_closure_set(x_308, 7, x_250);
lean_closure_set(x_308, 8, x_307);
lean_closure_set(x_308, 9, x_281);
lean_closure_set(x_308, 10, x_297);
lean_closure_set(x_308, 11, x_304);
lean_closure_set(x_308, 12, x_305);
x_309 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_309, 0, x_306);
lean_closure_set(x_309, 1, x_308);
x_310 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_295, x_13, x_14, x_15, x_16, x_301);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
x_314 = lean_ctor_get(x_311, 4);
lean_inc(x_314);
lean_dec(x_311);
x_315 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_313, x_314, x_309, x_13, x_14, x_15, x_16, x_312);
if (lean_obj_tag(x_315) == 0)
{
uint8_t x_316; 
x_316 = !lean_is_exclusive(x_315);
if (x_316 == 0)
{
return x_315;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_315, 0);
x_318 = lean_ctor_get(x_315, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_315);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
}
else
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_315);
if (x_320 == 0)
{
return x_315;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_315, 0);
x_322 = lean_ctor_get(x_315, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_315);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
return x_323;
}
}
}
else
{
uint8_t x_324; 
lean_dec(x_309);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_324 = !lean_is_exclusive(x_310);
if (x_324 == 0)
{
return x_310;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_310, 0);
x_326 = lean_ctor_get(x_310, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_310);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
}
else
{
uint8_t x_328; 
lean_dec(x_289);
lean_dec(x_281);
lean_dec(x_266);
lean_dec(x_250);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_328 = !lean_is_exclusive(x_291);
if (x_328 == 0)
{
return x_291;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_291, 0);
x_330 = lean_ctor_get(x_291, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_291);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
return x_331;
}
}
}
else
{
uint8_t x_332; 
lean_dec(x_281);
lean_dec(x_266);
lean_dec(x_250);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_332 = !lean_is_exclusive(x_286);
if (x_332 == 0)
{
return x_286;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_286, 0);
x_334 = lean_ctor_get(x_286, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_286);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
return x_335;
}
}
}
else
{
uint8_t x_336; 
lean_dec(x_266);
lean_dec(x_250);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_336 = !lean_is_exclusive(x_278);
if (x_336 == 0)
{
return x_278;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_278, 0);
x_338 = lean_ctor_get(x_278, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_278);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
}
}
else
{
uint8_t x_354; 
lean_dec(x_266);
lean_dec(x_256);
lean_dec(x_250);
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
x_354 = !lean_is_exclusive(x_268);
if (x_354 == 0)
{
return x_268;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_268, 0);
x_356 = lean_ctor_get(x_268, 1);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_268);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
}
}
else
{
uint8_t x_358; 
lean_dec(x_256);
lean_dec(x_250);
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
x_358 = !lean_is_exclusive(x_265);
if (x_358 == 0)
{
return x_265;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_265, 0);
x_360 = lean_ctor_get(x_265, 1);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_265);
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
lean_dec(x_250);
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
x_362 = !lean_is_exclusive(x_251);
if (x_362 == 0)
{
return x_251;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_251, 0);
x_364 = lean_ctor_get(x_251, 1);
lean_inc(x_364);
lean_inc(x_363);
lean_dec(x_251);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
return x_365;
}
}
}
case 3:
{
lean_object* x_366; lean_object* x_367; 
lean_dec(x_12);
lean_dec(x_10);
x_366 = lean_ctor_get(x_7, 5);
lean_inc(x_366);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_367 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_6, x_9, x_11, x_366, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_368 = lean_ctor_get(x_367, 1);
lean_inc(x_368);
lean_dec(x_367);
x_369 = lean_st_ref_get(x_14, x_368);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec(x_369);
x_372 = lean_ctor_get(x_370, 0);
lean_inc(x_372);
lean_dec(x_370);
x_373 = lean_ctor_get(x_7, 6);
lean_inc(x_373);
x_374 = l_List_redLength___main___rarg(x_373);
x_375 = lean_mk_empty_array_with_capacity(x_374);
lean_dec(x_374);
lean_inc(x_373);
x_376 = l_List_toArrayAux___main___rarg(x_373, x_375);
x_377 = x_376;
x_378 = lean_unsigned_to_nat(0u);
lean_inc(x_372);
lean_inc(x_6);
lean_inc(x_1);
x_379 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_379, 0, x_1);
lean_closure_set(x_379, 1, x_6);
lean_closure_set(x_379, 2, x_9);
lean_closure_set(x_379, 3, x_11);
lean_closure_set(x_379, 4, x_372);
lean_closure_set(x_379, 5, x_373);
lean_closure_set(x_379, 6, x_378);
lean_closure_set(x_379, 7, x_377);
x_380 = x_379;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_381 = lean_apply_5(x_380, x_13, x_14, x_15, x_16, x_371);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
lean_inc(x_1);
x_384 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_383);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
lean_dec(x_384);
x_387 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_387 == 0)
{
lean_object* x_457; uint8_t x_458; 
x_457 = l_Lean_MetavarContext_exprDependsOn(x_372, x_385, x_2);
x_458 = lean_unbox(x_457);
lean_dec(x_457);
if (x_458 == 0)
{
x_388 = x_386;
goto block_456;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; 
lean_dec(x_382);
lean_dec(x_366);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_459 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_459, 0, x_3);
x_460 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_461 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_459);
x_462 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_463 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_463, 0, x_461);
lean_ctor_set(x_463, 1, x_462);
x_464 = lean_box(0);
x_465 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_463, x_464, x_13, x_14, x_15, x_16, x_386);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_466 = !lean_is_exclusive(x_465);
if (x_466 == 0)
{
return x_465;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_465, 0);
x_468 = lean_ctor_get(x_465, 1);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_465);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
return x_469;
}
}
}
else
{
lean_dec(x_385);
lean_dec(x_372);
x_388 = x_386;
goto block_456;
}
block_456:
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; 
lean_inc(x_382);
x_389 = x_382;
x_390 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_378, x_389);
x_391 = x_390;
x_392 = lean_array_push(x_391, x_2);
x_393 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_394 = l_Lean_Meta_revert(x_1, x_392, x_393, x_13, x_14, x_15, x_16, x_388);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; lean_object* x_402; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
lean_dec(x_394);
x_397 = lean_ctor_get(x_395, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_395, 1);
lean_inc(x_398);
lean_dec(x_395);
x_399 = lean_array_get_size(x_382);
x_400 = lean_box(0);
x_401 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_402 = l_Lean_Meta_introN(x_398, x_399, x_400, x_401, x_13, x_14, x_15, x_16, x_396);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
x_405 = lean_ctor_get(x_403, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_403, 1);
lean_inc(x_406);
lean_dec(x_403);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_407 = l_Lean_Meta_intro1(x_406, x_401, x_13, x_14, x_15, x_16, x_404);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_410 = lean_ctor_get(x_408, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_408, 1);
lean_inc(x_411);
lean_dec(x_408);
x_412 = lean_box(0);
x_413 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_382, x_405, x_382, x_378, x_412);
lean_dec(x_382);
lean_inc(x_411);
x_414 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_414, 0, x_411);
x_415 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_416 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_415, x_414, x_13, x_14, x_15, x_16, x_409);
x_417 = lean_ctor_get(x_416, 1);
lean_inc(x_417);
lean_dec(x_416);
x_418 = x_405;
x_419 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_378, x_418);
x_420 = x_419;
lean_inc(x_410);
x_421 = l_Lean_mkFVar(x_410);
lean_inc(x_411);
x_422 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_422, 0, x_411);
x_423 = lean_box(x_387);
lean_inc(x_411);
x_424 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_424, 0, x_410);
lean_closure_set(x_424, 1, x_8);
lean_closure_set(x_424, 2, x_411);
lean_closure_set(x_424, 3, x_3);
lean_closure_set(x_424, 4, x_4);
lean_closure_set(x_424, 5, x_6);
lean_closure_set(x_424, 6, x_7);
lean_closure_set(x_424, 7, x_366);
lean_closure_set(x_424, 8, x_423);
lean_closure_set(x_424, 9, x_397);
lean_closure_set(x_424, 10, x_413);
lean_closure_set(x_424, 11, x_420);
lean_closure_set(x_424, 12, x_421);
x_425 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_425, 0, x_422);
lean_closure_set(x_425, 1, x_424);
x_426 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_411, x_13, x_14, x_15, x_16, x_417);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
x_430 = lean_ctor_get(x_427, 4);
lean_inc(x_430);
lean_dec(x_427);
x_431 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_429, x_430, x_425, x_13, x_14, x_15, x_16, x_428);
if (lean_obj_tag(x_431) == 0)
{
uint8_t x_432; 
x_432 = !lean_is_exclusive(x_431);
if (x_432 == 0)
{
return x_431;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_433 = lean_ctor_get(x_431, 0);
x_434 = lean_ctor_get(x_431, 1);
lean_inc(x_434);
lean_inc(x_433);
lean_dec(x_431);
x_435 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set(x_435, 1, x_434);
return x_435;
}
}
else
{
uint8_t x_436; 
x_436 = !lean_is_exclusive(x_431);
if (x_436 == 0)
{
return x_431;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_437 = lean_ctor_get(x_431, 0);
x_438 = lean_ctor_get(x_431, 1);
lean_inc(x_438);
lean_inc(x_437);
lean_dec(x_431);
x_439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_439, 0, x_437);
lean_ctor_set(x_439, 1, x_438);
return x_439;
}
}
}
else
{
uint8_t x_440; 
lean_dec(x_425);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_440 = !lean_is_exclusive(x_426);
if (x_440 == 0)
{
return x_426;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_426, 0);
x_442 = lean_ctor_get(x_426, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_426);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
return x_443;
}
}
}
else
{
uint8_t x_444; 
lean_dec(x_405);
lean_dec(x_397);
lean_dec(x_382);
lean_dec(x_366);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_444 = !lean_is_exclusive(x_407);
if (x_444 == 0)
{
return x_407;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_407, 0);
x_446 = lean_ctor_get(x_407, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_407);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
}
else
{
uint8_t x_448; 
lean_dec(x_397);
lean_dec(x_382);
lean_dec(x_366);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_448 = !lean_is_exclusive(x_402);
if (x_448 == 0)
{
return x_402;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_402, 0);
x_450 = lean_ctor_get(x_402, 1);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_402);
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_450);
return x_451;
}
}
}
else
{
uint8_t x_452; 
lean_dec(x_382);
lean_dec(x_366);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_452 = !lean_is_exclusive(x_394);
if (x_452 == 0)
{
return x_394;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_394, 0);
x_454 = lean_ctor_get(x_394, 1);
lean_inc(x_454);
lean_inc(x_453);
lean_dec(x_394);
x_455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_454);
return x_455;
}
}
}
}
else
{
uint8_t x_470; 
lean_dec(x_382);
lean_dec(x_372);
lean_dec(x_366);
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
x_470 = !lean_is_exclusive(x_384);
if (x_470 == 0)
{
return x_384;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_384, 0);
x_472 = lean_ctor_get(x_384, 1);
lean_inc(x_472);
lean_inc(x_471);
lean_dec(x_384);
x_473 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set(x_473, 1, x_472);
return x_473;
}
}
}
else
{
uint8_t x_474; 
lean_dec(x_372);
lean_dec(x_366);
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
x_474 = !lean_is_exclusive(x_381);
if (x_474 == 0)
{
return x_381;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_381, 0);
x_476 = lean_ctor_get(x_381, 1);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_381);
x_477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_476);
return x_477;
}
}
}
else
{
uint8_t x_478; 
lean_dec(x_366);
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
x_478 = !lean_is_exclusive(x_367);
if (x_478 == 0)
{
return x_367;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_367, 0);
x_480 = lean_ctor_get(x_367, 1);
lean_inc(x_480);
lean_inc(x_479);
lean_dec(x_367);
x_481 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_481, 0, x_479);
lean_ctor_set(x_481, 1, x_480);
return x_481;
}
}
}
case 4:
{
lean_object* x_482; lean_object* x_483; 
lean_dec(x_12);
lean_dec(x_10);
x_482 = lean_ctor_get(x_7, 5);
lean_inc(x_482);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_483 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_6, x_9, x_11, x_482, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_484 = lean_ctor_get(x_483, 1);
lean_inc(x_484);
lean_dec(x_483);
x_485 = lean_st_ref_get(x_14, x_484);
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
lean_dec(x_485);
x_488 = lean_ctor_get(x_486, 0);
lean_inc(x_488);
lean_dec(x_486);
x_489 = lean_ctor_get(x_7, 6);
lean_inc(x_489);
x_490 = l_List_redLength___main___rarg(x_489);
x_491 = lean_mk_empty_array_with_capacity(x_490);
lean_dec(x_490);
lean_inc(x_489);
x_492 = l_List_toArrayAux___main___rarg(x_489, x_491);
x_493 = x_492;
x_494 = lean_unsigned_to_nat(0u);
lean_inc(x_488);
lean_inc(x_6);
lean_inc(x_1);
x_495 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_495, 0, x_1);
lean_closure_set(x_495, 1, x_6);
lean_closure_set(x_495, 2, x_9);
lean_closure_set(x_495, 3, x_11);
lean_closure_set(x_495, 4, x_488);
lean_closure_set(x_495, 5, x_489);
lean_closure_set(x_495, 6, x_494);
lean_closure_set(x_495, 7, x_493);
x_496 = x_495;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_497 = lean_apply_5(x_496, x_13, x_14, x_15, x_16, x_487);
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
lean_dec(x_497);
lean_inc(x_1);
x_500 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_499);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; uint8_t x_503; lean_object* x_504; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_503 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_503 == 0)
{
lean_object* x_573; uint8_t x_574; 
x_573 = l_Lean_MetavarContext_exprDependsOn(x_488, x_501, x_2);
x_574 = lean_unbox(x_573);
lean_dec(x_573);
if (x_574 == 0)
{
x_504 = x_502;
goto block_572;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; uint8_t x_582; 
lean_dec(x_498);
lean_dec(x_482);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_575 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_575, 0, x_3);
x_576 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_577 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_577, 0, x_576);
lean_ctor_set(x_577, 1, x_575);
x_578 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_579 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_579, 0, x_577);
lean_ctor_set(x_579, 1, x_578);
x_580 = lean_box(0);
x_581 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_579, x_580, x_13, x_14, x_15, x_16, x_502);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_582 = !lean_is_exclusive(x_581);
if (x_582 == 0)
{
return x_581;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_581, 0);
x_584 = lean_ctor_get(x_581, 1);
lean_inc(x_584);
lean_inc(x_583);
lean_dec(x_581);
x_585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set(x_585, 1, x_584);
return x_585;
}
}
}
else
{
lean_dec(x_501);
lean_dec(x_488);
x_504 = x_502;
goto block_572;
}
block_572:
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; 
lean_inc(x_498);
x_505 = x_498;
x_506 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_494, x_505);
x_507 = x_506;
x_508 = lean_array_push(x_507, x_2);
x_509 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_510 = l_Lean_Meta_revert(x_1, x_508, x_509, x_13, x_14, x_15, x_16, x_504);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; lean_object* x_518; 
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
lean_dec(x_510);
x_513 = lean_ctor_get(x_511, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_511, 1);
lean_inc(x_514);
lean_dec(x_511);
x_515 = lean_array_get_size(x_498);
x_516 = lean_box(0);
x_517 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_518 = l_Lean_Meta_introN(x_514, x_515, x_516, x_517, x_13, x_14, x_15, x_16, x_512);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
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
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_523 = l_Lean_Meta_intro1(x_522, x_517, x_13, x_14, x_15, x_16, x_520);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_523, 1);
lean_inc(x_525);
lean_dec(x_523);
x_526 = lean_ctor_get(x_524, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_524, 1);
lean_inc(x_527);
lean_dec(x_524);
x_528 = lean_box(0);
x_529 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_498, x_521, x_498, x_494, x_528);
lean_dec(x_498);
lean_inc(x_527);
x_530 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_530, 0, x_527);
x_531 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_532 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_531, x_530, x_13, x_14, x_15, x_16, x_525);
x_533 = lean_ctor_get(x_532, 1);
lean_inc(x_533);
lean_dec(x_532);
x_534 = x_521;
x_535 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_494, x_534);
x_536 = x_535;
lean_inc(x_526);
x_537 = l_Lean_mkFVar(x_526);
lean_inc(x_527);
x_538 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_538, 0, x_527);
x_539 = lean_box(x_503);
lean_inc(x_527);
x_540 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_540, 0, x_526);
lean_closure_set(x_540, 1, x_8);
lean_closure_set(x_540, 2, x_527);
lean_closure_set(x_540, 3, x_3);
lean_closure_set(x_540, 4, x_4);
lean_closure_set(x_540, 5, x_6);
lean_closure_set(x_540, 6, x_7);
lean_closure_set(x_540, 7, x_482);
lean_closure_set(x_540, 8, x_539);
lean_closure_set(x_540, 9, x_513);
lean_closure_set(x_540, 10, x_529);
lean_closure_set(x_540, 11, x_536);
lean_closure_set(x_540, 12, x_537);
x_541 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_541, 0, x_538);
lean_closure_set(x_541, 1, x_540);
x_542 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_527, x_13, x_14, x_15, x_16, x_533);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_542, 1);
lean_inc(x_544);
lean_dec(x_542);
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
x_546 = lean_ctor_get(x_543, 4);
lean_inc(x_546);
lean_dec(x_543);
x_547 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_545, x_546, x_541, x_13, x_14, x_15, x_16, x_544);
if (lean_obj_tag(x_547) == 0)
{
uint8_t x_548; 
x_548 = !lean_is_exclusive(x_547);
if (x_548 == 0)
{
return x_547;
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_549 = lean_ctor_get(x_547, 0);
x_550 = lean_ctor_get(x_547, 1);
lean_inc(x_550);
lean_inc(x_549);
lean_dec(x_547);
x_551 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_551, 0, x_549);
lean_ctor_set(x_551, 1, x_550);
return x_551;
}
}
else
{
uint8_t x_552; 
x_552 = !lean_is_exclusive(x_547);
if (x_552 == 0)
{
return x_547;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_547, 0);
x_554 = lean_ctor_get(x_547, 1);
lean_inc(x_554);
lean_inc(x_553);
lean_dec(x_547);
x_555 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_555, 0, x_553);
lean_ctor_set(x_555, 1, x_554);
return x_555;
}
}
}
else
{
uint8_t x_556; 
lean_dec(x_541);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_556 = !lean_is_exclusive(x_542);
if (x_556 == 0)
{
return x_542;
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_557 = lean_ctor_get(x_542, 0);
x_558 = lean_ctor_get(x_542, 1);
lean_inc(x_558);
lean_inc(x_557);
lean_dec(x_542);
x_559 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_559, 0, x_557);
lean_ctor_set(x_559, 1, x_558);
return x_559;
}
}
}
else
{
uint8_t x_560; 
lean_dec(x_521);
lean_dec(x_513);
lean_dec(x_498);
lean_dec(x_482);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_560 = !lean_is_exclusive(x_523);
if (x_560 == 0)
{
return x_523;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_561 = lean_ctor_get(x_523, 0);
x_562 = lean_ctor_get(x_523, 1);
lean_inc(x_562);
lean_inc(x_561);
lean_dec(x_523);
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
lean_dec(x_513);
lean_dec(x_498);
lean_dec(x_482);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_564 = !lean_is_exclusive(x_518);
if (x_564 == 0)
{
return x_518;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_565 = lean_ctor_get(x_518, 0);
x_566 = lean_ctor_get(x_518, 1);
lean_inc(x_566);
lean_inc(x_565);
lean_dec(x_518);
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
lean_dec(x_498);
lean_dec(x_482);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_568 = !lean_is_exclusive(x_510);
if (x_568 == 0)
{
return x_510;
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_569 = lean_ctor_get(x_510, 0);
x_570 = lean_ctor_get(x_510, 1);
lean_inc(x_570);
lean_inc(x_569);
lean_dec(x_510);
x_571 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_571, 0, x_569);
lean_ctor_set(x_571, 1, x_570);
return x_571;
}
}
}
}
else
{
uint8_t x_586; 
lean_dec(x_498);
lean_dec(x_488);
lean_dec(x_482);
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
x_586 = !lean_is_exclusive(x_500);
if (x_586 == 0)
{
return x_500;
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_500, 0);
x_588 = lean_ctor_get(x_500, 1);
lean_inc(x_588);
lean_inc(x_587);
lean_dec(x_500);
x_589 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_589, 0, x_587);
lean_ctor_set(x_589, 1, x_588);
return x_589;
}
}
}
else
{
uint8_t x_590; 
lean_dec(x_488);
lean_dec(x_482);
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
x_590 = !lean_is_exclusive(x_497);
if (x_590 == 0)
{
return x_497;
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_591 = lean_ctor_get(x_497, 0);
x_592 = lean_ctor_get(x_497, 1);
lean_inc(x_592);
lean_inc(x_591);
lean_dec(x_497);
x_593 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_593, 0, x_591);
lean_ctor_set(x_593, 1, x_592);
return x_593;
}
}
}
else
{
uint8_t x_594; 
lean_dec(x_482);
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
x_594 = !lean_is_exclusive(x_483);
if (x_594 == 0)
{
return x_483;
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_595 = lean_ctor_get(x_483, 0);
x_596 = lean_ctor_get(x_483, 1);
lean_inc(x_596);
lean_inc(x_595);
lean_dec(x_483);
x_597 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_597, 0, x_595);
lean_ctor_set(x_597, 1, x_596);
return x_597;
}
}
}
case 5:
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_598 = lean_ctor_get(x_10, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_10, 1);
lean_inc(x_599);
lean_dec(x_10);
x_600 = lean_array_set(x_11, x_12, x_599);
x_601 = lean_unsigned_to_nat(1u);
x_602 = lean_nat_sub(x_12, x_601);
lean_dec(x_12);
x_10 = x_598;
x_11 = x_600;
x_12 = x_602;
goto _start;
}
case 6:
{
lean_object* x_604; lean_object* x_605; 
lean_dec(x_12);
lean_dec(x_10);
x_604 = lean_ctor_get(x_7, 5);
lean_inc(x_604);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_605 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_6, x_9, x_11, x_604, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_606 = lean_ctor_get(x_605, 1);
lean_inc(x_606);
lean_dec(x_605);
x_607 = lean_st_ref_get(x_14, x_606);
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_607, 1);
lean_inc(x_609);
lean_dec(x_607);
x_610 = lean_ctor_get(x_608, 0);
lean_inc(x_610);
lean_dec(x_608);
x_611 = lean_ctor_get(x_7, 6);
lean_inc(x_611);
x_612 = l_List_redLength___main___rarg(x_611);
x_613 = lean_mk_empty_array_with_capacity(x_612);
lean_dec(x_612);
lean_inc(x_611);
x_614 = l_List_toArrayAux___main___rarg(x_611, x_613);
x_615 = x_614;
x_616 = lean_unsigned_to_nat(0u);
lean_inc(x_610);
lean_inc(x_6);
lean_inc(x_1);
x_617 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_617, 0, x_1);
lean_closure_set(x_617, 1, x_6);
lean_closure_set(x_617, 2, x_9);
lean_closure_set(x_617, 3, x_11);
lean_closure_set(x_617, 4, x_610);
lean_closure_set(x_617, 5, x_611);
lean_closure_set(x_617, 6, x_616);
lean_closure_set(x_617, 7, x_615);
x_618 = x_617;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_619 = lean_apply_5(x_618, x_13, x_14, x_15, x_16, x_609);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_619, 1);
lean_inc(x_621);
lean_dec(x_619);
lean_inc(x_1);
x_622 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_621);
if (lean_obj_tag(x_622) == 0)
{
lean_object* x_623; lean_object* x_624; uint8_t x_625; lean_object* x_626; 
x_623 = lean_ctor_get(x_622, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_622, 1);
lean_inc(x_624);
lean_dec(x_622);
x_625 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_625 == 0)
{
lean_object* x_695; uint8_t x_696; 
x_695 = l_Lean_MetavarContext_exprDependsOn(x_610, x_623, x_2);
x_696 = lean_unbox(x_695);
lean_dec(x_695);
if (x_696 == 0)
{
x_626 = x_624;
goto block_694;
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; uint8_t x_704; 
lean_dec(x_620);
lean_dec(x_604);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_697 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_697, 0, x_3);
x_698 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_699 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_699, 0, x_698);
lean_ctor_set(x_699, 1, x_697);
x_700 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_701 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_701, 0, x_699);
lean_ctor_set(x_701, 1, x_700);
x_702 = lean_box(0);
x_703 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_701, x_702, x_13, x_14, x_15, x_16, x_624);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
lean_dec(x_623);
lean_dec(x_610);
x_626 = x_624;
goto block_694;
}
block_694:
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; lean_object* x_632; 
lean_inc(x_620);
x_627 = x_620;
x_628 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_616, x_627);
x_629 = x_628;
x_630 = lean_array_push(x_629, x_2);
x_631 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_632 = l_Lean_Meta_revert(x_1, x_630, x_631, x_13, x_14, x_15, x_16, x_626);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; uint8_t x_639; lean_object* x_640; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
lean_dec(x_632);
x_635 = lean_ctor_get(x_633, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_633, 1);
lean_inc(x_636);
lean_dec(x_633);
x_637 = lean_array_get_size(x_620);
x_638 = lean_box(0);
x_639 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_640 = l_Lean_Meta_introN(x_636, x_637, x_638, x_639, x_13, x_14, x_15, x_16, x_634);
if (lean_obj_tag(x_640) == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_641 = lean_ctor_get(x_640, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_640, 1);
lean_inc(x_642);
lean_dec(x_640);
x_643 = lean_ctor_get(x_641, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_641, 1);
lean_inc(x_644);
lean_dec(x_641);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_645 = l_Lean_Meta_intro1(x_644, x_639, x_13, x_14, x_15, x_16, x_642);
if (lean_obj_tag(x_645) == 0)
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
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
x_650 = lean_box(0);
x_651 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_620, x_643, x_620, x_616, x_650);
lean_dec(x_620);
lean_inc(x_649);
x_652 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_652, 0, x_649);
x_653 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_654 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_653, x_652, x_13, x_14, x_15, x_16, x_647);
x_655 = lean_ctor_get(x_654, 1);
lean_inc(x_655);
lean_dec(x_654);
x_656 = x_643;
x_657 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_616, x_656);
x_658 = x_657;
lean_inc(x_648);
x_659 = l_Lean_mkFVar(x_648);
lean_inc(x_649);
x_660 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_660, 0, x_649);
x_661 = lean_box(x_625);
lean_inc(x_649);
x_662 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_662, 0, x_648);
lean_closure_set(x_662, 1, x_8);
lean_closure_set(x_662, 2, x_649);
lean_closure_set(x_662, 3, x_3);
lean_closure_set(x_662, 4, x_4);
lean_closure_set(x_662, 5, x_6);
lean_closure_set(x_662, 6, x_7);
lean_closure_set(x_662, 7, x_604);
lean_closure_set(x_662, 8, x_661);
lean_closure_set(x_662, 9, x_635);
lean_closure_set(x_662, 10, x_651);
lean_closure_set(x_662, 11, x_658);
lean_closure_set(x_662, 12, x_659);
x_663 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_663, 0, x_660);
lean_closure_set(x_663, 1, x_662);
x_664 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_649, x_13, x_14, x_15, x_16, x_655);
if (lean_obj_tag(x_664) == 0)
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_664, 1);
lean_inc(x_666);
lean_dec(x_664);
x_667 = lean_ctor_get(x_665, 1);
lean_inc(x_667);
x_668 = lean_ctor_get(x_665, 4);
lean_inc(x_668);
lean_dec(x_665);
x_669 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_667, x_668, x_663, x_13, x_14, x_15, x_16, x_666);
if (lean_obj_tag(x_669) == 0)
{
uint8_t x_670; 
x_670 = !lean_is_exclusive(x_669);
if (x_670 == 0)
{
return x_669;
}
else
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_671 = lean_ctor_get(x_669, 0);
x_672 = lean_ctor_get(x_669, 1);
lean_inc(x_672);
lean_inc(x_671);
lean_dec(x_669);
x_673 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_673, 0, x_671);
lean_ctor_set(x_673, 1, x_672);
return x_673;
}
}
else
{
uint8_t x_674; 
x_674 = !lean_is_exclusive(x_669);
if (x_674 == 0)
{
return x_669;
}
else
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_675 = lean_ctor_get(x_669, 0);
x_676 = lean_ctor_get(x_669, 1);
lean_inc(x_676);
lean_inc(x_675);
lean_dec(x_669);
x_677 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_677, 0, x_675);
lean_ctor_set(x_677, 1, x_676);
return x_677;
}
}
}
else
{
uint8_t x_678; 
lean_dec(x_663);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_678 = !lean_is_exclusive(x_664);
if (x_678 == 0)
{
return x_664;
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_679 = lean_ctor_get(x_664, 0);
x_680 = lean_ctor_get(x_664, 1);
lean_inc(x_680);
lean_inc(x_679);
lean_dec(x_664);
x_681 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_681, 0, x_679);
lean_ctor_set(x_681, 1, x_680);
return x_681;
}
}
}
else
{
uint8_t x_682; 
lean_dec(x_643);
lean_dec(x_635);
lean_dec(x_620);
lean_dec(x_604);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_682 = !lean_is_exclusive(x_645);
if (x_682 == 0)
{
return x_645;
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_683 = lean_ctor_get(x_645, 0);
x_684 = lean_ctor_get(x_645, 1);
lean_inc(x_684);
lean_inc(x_683);
lean_dec(x_645);
x_685 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_685, 0, x_683);
lean_ctor_set(x_685, 1, x_684);
return x_685;
}
}
}
else
{
uint8_t x_686; 
lean_dec(x_635);
lean_dec(x_620);
lean_dec(x_604);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_686 = !lean_is_exclusive(x_640);
if (x_686 == 0)
{
return x_640;
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_687 = lean_ctor_get(x_640, 0);
x_688 = lean_ctor_get(x_640, 1);
lean_inc(x_688);
lean_inc(x_687);
lean_dec(x_640);
x_689 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_689, 0, x_687);
lean_ctor_set(x_689, 1, x_688);
return x_689;
}
}
}
else
{
uint8_t x_690; 
lean_dec(x_620);
lean_dec(x_604);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_690 = !lean_is_exclusive(x_632);
if (x_690 == 0)
{
return x_632;
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_691 = lean_ctor_get(x_632, 0);
x_692 = lean_ctor_get(x_632, 1);
lean_inc(x_692);
lean_inc(x_691);
lean_dec(x_632);
x_693 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_693, 0, x_691);
lean_ctor_set(x_693, 1, x_692);
return x_693;
}
}
}
}
else
{
uint8_t x_708; 
lean_dec(x_620);
lean_dec(x_610);
lean_dec(x_604);
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
x_708 = !lean_is_exclusive(x_622);
if (x_708 == 0)
{
return x_622;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = lean_ctor_get(x_622, 0);
x_710 = lean_ctor_get(x_622, 1);
lean_inc(x_710);
lean_inc(x_709);
lean_dec(x_622);
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
lean_dec(x_610);
lean_dec(x_604);
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
x_712 = !lean_is_exclusive(x_619);
if (x_712 == 0)
{
return x_619;
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_713 = lean_ctor_get(x_619, 0);
x_714 = lean_ctor_get(x_619, 1);
lean_inc(x_714);
lean_inc(x_713);
lean_dec(x_619);
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
lean_dec(x_604);
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
x_716 = !lean_is_exclusive(x_605);
if (x_716 == 0)
{
return x_605;
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_717 = lean_ctor_get(x_605, 0);
x_718 = lean_ctor_get(x_605, 1);
lean_inc(x_718);
lean_inc(x_717);
lean_dec(x_605);
x_719 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_719, 0, x_717);
lean_ctor_set(x_719, 1, x_718);
return x_719;
}
}
}
case 7:
{
lean_object* x_720; lean_object* x_721; 
lean_dec(x_12);
lean_dec(x_10);
x_720 = lean_ctor_get(x_7, 5);
lean_inc(x_720);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_721 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_6, x_9, x_11, x_720, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
x_722 = lean_ctor_get(x_721, 1);
lean_inc(x_722);
lean_dec(x_721);
x_723 = lean_st_ref_get(x_14, x_722);
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
lean_dec(x_723);
x_726 = lean_ctor_get(x_724, 0);
lean_inc(x_726);
lean_dec(x_724);
x_727 = lean_ctor_get(x_7, 6);
lean_inc(x_727);
x_728 = l_List_redLength___main___rarg(x_727);
x_729 = lean_mk_empty_array_with_capacity(x_728);
lean_dec(x_728);
lean_inc(x_727);
x_730 = l_List_toArrayAux___main___rarg(x_727, x_729);
x_731 = x_730;
x_732 = lean_unsigned_to_nat(0u);
lean_inc(x_726);
lean_inc(x_6);
lean_inc(x_1);
x_733 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_733, 0, x_1);
lean_closure_set(x_733, 1, x_6);
lean_closure_set(x_733, 2, x_9);
lean_closure_set(x_733, 3, x_11);
lean_closure_set(x_733, 4, x_726);
lean_closure_set(x_733, 5, x_727);
lean_closure_set(x_733, 6, x_732);
lean_closure_set(x_733, 7, x_731);
x_734 = x_733;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_735 = lean_apply_5(x_734, x_13, x_14, x_15, x_16, x_725);
if (lean_obj_tag(x_735) == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_736 = lean_ctor_get(x_735, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_735, 1);
lean_inc(x_737);
lean_dec(x_735);
lean_inc(x_1);
x_738 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_737);
if (lean_obj_tag(x_738) == 0)
{
lean_object* x_739; lean_object* x_740; uint8_t x_741; lean_object* x_742; 
x_739 = lean_ctor_get(x_738, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_738, 1);
lean_inc(x_740);
lean_dec(x_738);
x_741 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_741 == 0)
{
lean_object* x_811; uint8_t x_812; 
x_811 = l_Lean_MetavarContext_exprDependsOn(x_726, x_739, x_2);
x_812 = lean_unbox(x_811);
lean_dec(x_811);
if (x_812 == 0)
{
x_742 = x_740;
goto block_810;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; uint8_t x_820; 
lean_dec(x_736);
lean_dec(x_720);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_813 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_813, 0, x_3);
x_814 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_815 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_815, 0, x_814);
lean_ctor_set(x_815, 1, x_813);
x_816 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_817 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_817, 0, x_815);
lean_ctor_set(x_817, 1, x_816);
x_818 = lean_box(0);
x_819 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_817, x_818, x_13, x_14, x_15, x_16, x_740);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_820 = !lean_is_exclusive(x_819);
if (x_820 == 0)
{
return x_819;
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_821 = lean_ctor_get(x_819, 0);
x_822 = lean_ctor_get(x_819, 1);
lean_inc(x_822);
lean_inc(x_821);
lean_dec(x_819);
x_823 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_823, 0, x_821);
lean_ctor_set(x_823, 1, x_822);
return x_823;
}
}
}
else
{
lean_dec(x_739);
lean_dec(x_726);
x_742 = x_740;
goto block_810;
}
block_810:
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; uint8_t x_747; lean_object* x_748; 
lean_inc(x_736);
x_743 = x_736;
x_744 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_732, x_743);
x_745 = x_744;
x_746 = lean_array_push(x_745, x_2);
x_747 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_748 = l_Lean_Meta_revert(x_1, x_746, x_747, x_13, x_14, x_15, x_16, x_742);
if (lean_obj_tag(x_748) == 0)
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; uint8_t x_755; lean_object* x_756; 
x_749 = lean_ctor_get(x_748, 0);
lean_inc(x_749);
x_750 = lean_ctor_get(x_748, 1);
lean_inc(x_750);
lean_dec(x_748);
x_751 = lean_ctor_get(x_749, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_749, 1);
lean_inc(x_752);
lean_dec(x_749);
x_753 = lean_array_get_size(x_736);
x_754 = lean_box(0);
x_755 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_756 = l_Lean_Meta_introN(x_752, x_753, x_754, x_755, x_13, x_14, x_15, x_16, x_750);
if (lean_obj_tag(x_756) == 0)
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
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
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_761 = l_Lean_Meta_intro1(x_760, x_755, x_13, x_14, x_15, x_16, x_758);
if (lean_obj_tag(x_761) == 0)
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_762 = lean_ctor_get(x_761, 0);
lean_inc(x_762);
x_763 = lean_ctor_get(x_761, 1);
lean_inc(x_763);
lean_dec(x_761);
x_764 = lean_ctor_get(x_762, 0);
lean_inc(x_764);
x_765 = lean_ctor_get(x_762, 1);
lean_inc(x_765);
lean_dec(x_762);
x_766 = lean_box(0);
x_767 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_736, x_759, x_736, x_732, x_766);
lean_dec(x_736);
lean_inc(x_765);
x_768 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_768, 0, x_765);
x_769 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_770 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_769, x_768, x_13, x_14, x_15, x_16, x_763);
x_771 = lean_ctor_get(x_770, 1);
lean_inc(x_771);
lean_dec(x_770);
x_772 = x_759;
x_773 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_732, x_772);
x_774 = x_773;
lean_inc(x_764);
x_775 = l_Lean_mkFVar(x_764);
lean_inc(x_765);
x_776 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_776, 0, x_765);
x_777 = lean_box(x_741);
lean_inc(x_765);
x_778 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_778, 0, x_764);
lean_closure_set(x_778, 1, x_8);
lean_closure_set(x_778, 2, x_765);
lean_closure_set(x_778, 3, x_3);
lean_closure_set(x_778, 4, x_4);
lean_closure_set(x_778, 5, x_6);
lean_closure_set(x_778, 6, x_7);
lean_closure_set(x_778, 7, x_720);
lean_closure_set(x_778, 8, x_777);
lean_closure_set(x_778, 9, x_751);
lean_closure_set(x_778, 10, x_767);
lean_closure_set(x_778, 11, x_774);
lean_closure_set(x_778, 12, x_775);
x_779 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_779, 0, x_776);
lean_closure_set(x_779, 1, x_778);
x_780 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_765, x_13, x_14, x_15, x_16, x_771);
if (lean_obj_tag(x_780) == 0)
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_780, 1);
lean_inc(x_782);
lean_dec(x_780);
x_783 = lean_ctor_get(x_781, 1);
lean_inc(x_783);
x_784 = lean_ctor_get(x_781, 4);
lean_inc(x_784);
lean_dec(x_781);
x_785 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_783, x_784, x_779, x_13, x_14, x_15, x_16, x_782);
if (lean_obj_tag(x_785) == 0)
{
uint8_t x_786; 
x_786 = !lean_is_exclusive(x_785);
if (x_786 == 0)
{
return x_785;
}
else
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_787 = lean_ctor_get(x_785, 0);
x_788 = lean_ctor_get(x_785, 1);
lean_inc(x_788);
lean_inc(x_787);
lean_dec(x_785);
x_789 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_789, 0, x_787);
lean_ctor_set(x_789, 1, x_788);
return x_789;
}
}
else
{
uint8_t x_790; 
x_790 = !lean_is_exclusive(x_785);
if (x_790 == 0)
{
return x_785;
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_791 = lean_ctor_get(x_785, 0);
x_792 = lean_ctor_get(x_785, 1);
lean_inc(x_792);
lean_inc(x_791);
lean_dec(x_785);
x_793 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_793, 0, x_791);
lean_ctor_set(x_793, 1, x_792);
return x_793;
}
}
}
else
{
uint8_t x_794; 
lean_dec(x_779);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_794 = !lean_is_exclusive(x_780);
if (x_794 == 0)
{
return x_780;
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_795 = lean_ctor_get(x_780, 0);
x_796 = lean_ctor_get(x_780, 1);
lean_inc(x_796);
lean_inc(x_795);
lean_dec(x_780);
x_797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_797, 0, x_795);
lean_ctor_set(x_797, 1, x_796);
return x_797;
}
}
}
else
{
uint8_t x_798; 
lean_dec(x_759);
lean_dec(x_751);
lean_dec(x_736);
lean_dec(x_720);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_798 = !lean_is_exclusive(x_761);
if (x_798 == 0)
{
return x_761;
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_799 = lean_ctor_get(x_761, 0);
x_800 = lean_ctor_get(x_761, 1);
lean_inc(x_800);
lean_inc(x_799);
lean_dec(x_761);
x_801 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_801, 0, x_799);
lean_ctor_set(x_801, 1, x_800);
return x_801;
}
}
}
else
{
uint8_t x_802; 
lean_dec(x_751);
lean_dec(x_736);
lean_dec(x_720);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_802 = !lean_is_exclusive(x_756);
if (x_802 == 0)
{
return x_756;
}
else
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; 
x_803 = lean_ctor_get(x_756, 0);
x_804 = lean_ctor_get(x_756, 1);
lean_inc(x_804);
lean_inc(x_803);
lean_dec(x_756);
x_805 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_805, 0, x_803);
lean_ctor_set(x_805, 1, x_804);
return x_805;
}
}
}
else
{
uint8_t x_806; 
lean_dec(x_736);
lean_dec(x_720);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_806 = !lean_is_exclusive(x_748);
if (x_806 == 0)
{
return x_748;
}
else
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; 
x_807 = lean_ctor_get(x_748, 0);
x_808 = lean_ctor_get(x_748, 1);
lean_inc(x_808);
lean_inc(x_807);
lean_dec(x_748);
x_809 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_809, 0, x_807);
lean_ctor_set(x_809, 1, x_808);
return x_809;
}
}
}
}
else
{
uint8_t x_824; 
lean_dec(x_736);
lean_dec(x_726);
lean_dec(x_720);
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
x_824 = !lean_is_exclusive(x_738);
if (x_824 == 0)
{
return x_738;
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_825 = lean_ctor_get(x_738, 0);
x_826 = lean_ctor_get(x_738, 1);
lean_inc(x_826);
lean_inc(x_825);
lean_dec(x_738);
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
lean_dec(x_726);
lean_dec(x_720);
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
x_828 = !lean_is_exclusive(x_735);
if (x_828 == 0)
{
return x_735;
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; 
x_829 = lean_ctor_get(x_735, 0);
x_830 = lean_ctor_get(x_735, 1);
lean_inc(x_830);
lean_inc(x_829);
lean_dec(x_735);
x_831 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_831, 0, x_829);
lean_ctor_set(x_831, 1, x_830);
return x_831;
}
}
}
else
{
uint8_t x_832; 
lean_dec(x_720);
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
x_832 = !lean_is_exclusive(x_721);
if (x_832 == 0)
{
return x_721;
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; 
x_833 = lean_ctor_get(x_721, 0);
x_834 = lean_ctor_get(x_721, 1);
lean_inc(x_834);
lean_inc(x_833);
lean_dec(x_721);
x_835 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_835, 0, x_833);
lean_ctor_set(x_835, 1, x_834);
return x_835;
}
}
}
case 8:
{
lean_object* x_836; lean_object* x_837; 
lean_dec(x_12);
lean_dec(x_10);
x_836 = lean_ctor_get(x_7, 5);
lean_inc(x_836);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_837 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_6, x_9, x_11, x_836, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_837) == 0)
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_838 = lean_ctor_get(x_837, 1);
lean_inc(x_838);
lean_dec(x_837);
x_839 = lean_st_ref_get(x_14, x_838);
x_840 = lean_ctor_get(x_839, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_839, 1);
lean_inc(x_841);
lean_dec(x_839);
x_842 = lean_ctor_get(x_840, 0);
lean_inc(x_842);
lean_dec(x_840);
x_843 = lean_ctor_get(x_7, 6);
lean_inc(x_843);
x_844 = l_List_redLength___main___rarg(x_843);
x_845 = lean_mk_empty_array_with_capacity(x_844);
lean_dec(x_844);
lean_inc(x_843);
x_846 = l_List_toArrayAux___main___rarg(x_843, x_845);
x_847 = x_846;
x_848 = lean_unsigned_to_nat(0u);
lean_inc(x_842);
lean_inc(x_6);
lean_inc(x_1);
x_849 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_849, 0, x_1);
lean_closure_set(x_849, 1, x_6);
lean_closure_set(x_849, 2, x_9);
lean_closure_set(x_849, 3, x_11);
lean_closure_set(x_849, 4, x_842);
lean_closure_set(x_849, 5, x_843);
lean_closure_set(x_849, 6, x_848);
lean_closure_set(x_849, 7, x_847);
x_850 = x_849;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_851 = lean_apply_5(x_850, x_13, x_14, x_15, x_16, x_841);
if (lean_obj_tag(x_851) == 0)
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; 
x_852 = lean_ctor_get(x_851, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_851, 1);
lean_inc(x_853);
lean_dec(x_851);
lean_inc(x_1);
x_854 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_853);
if (lean_obj_tag(x_854) == 0)
{
lean_object* x_855; lean_object* x_856; uint8_t x_857; lean_object* x_858; 
x_855 = lean_ctor_get(x_854, 0);
lean_inc(x_855);
x_856 = lean_ctor_get(x_854, 1);
lean_inc(x_856);
lean_dec(x_854);
x_857 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_857 == 0)
{
lean_object* x_927; uint8_t x_928; 
x_927 = l_Lean_MetavarContext_exprDependsOn(x_842, x_855, x_2);
x_928 = lean_unbox(x_927);
lean_dec(x_927);
if (x_928 == 0)
{
x_858 = x_856;
goto block_926;
}
else
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; uint8_t x_936; 
lean_dec(x_852);
lean_dec(x_836);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_929 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_929, 0, x_3);
x_930 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_931 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_931, 0, x_930);
lean_ctor_set(x_931, 1, x_929);
x_932 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_933 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_933, 0, x_931);
lean_ctor_set(x_933, 1, x_932);
x_934 = lean_box(0);
x_935 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_933, x_934, x_13, x_14, x_15, x_16, x_856);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_936 = !lean_is_exclusive(x_935);
if (x_936 == 0)
{
return x_935;
}
else
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; 
x_937 = lean_ctor_get(x_935, 0);
x_938 = lean_ctor_get(x_935, 1);
lean_inc(x_938);
lean_inc(x_937);
lean_dec(x_935);
x_939 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_939, 0, x_937);
lean_ctor_set(x_939, 1, x_938);
return x_939;
}
}
}
else
{
lean_dec(x_855);
lean_dec(x_842);
x_858 = x_856;
goto block_926;
}
block_926:
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; uint8_t x_863; lean_object* x_864; 
lean_inc(x_852);
x_859 = x_852;
x_860 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_848, x_859);
x_861 = x_860;
x_862 = lean_array_push(x_861, x_2);
x_863 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_864 = l_Lean_Meta_revert(x_1, x_862, x_863, x_13, x_14, x_15, x_16, x_858);
if (lean_obj_tag(x_864) == 0)
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; uint8_t x_871; lean_object* x_872; 
x_865 = lean_ctor_get(x_864, 0);
lean_inc(x_865);
x_866 = lean_ctor_get(x_864, 1);
lean_inc(x_866);
lean_dec(x_864);
x_867 = lean_ctor_get(x_865, 0);
lean_inc(x_867);
x_868 = lean_ctor_get(x_865, 1);
lean_inc(x_868);
lean_dec(x_865);
x_869 = lean_array_get_size(x_852);
x_870 = lean_box(0);
x_871 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_872 = l_Lean_Meta_introN(x_868, x_869, x_870, x_871, x_13, x_14, x_15, x_16, x_866);
if (lean_obj_tag(x_872) == 0)
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; 
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_872, 1);
lean_inc(x_874);
lean_dec(x_872);
x_875 = lean_ctor_get(x_873, 0);
lean_inc(x_875);
x_876 = lean_ctor_get(x_873, 1);
lean_inc(x_876);
lean_dec(x_873);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_877 = l_Lean_Meta_intro1(x_876, x_871, x_13, x_14, x_15, x_16, x_874);
if (lean_obj_tag(x_877) == 0)
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; 
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
x_882 = lean_box(0);
x_883 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_852, x_875, x_852, x_848, x_882);
lean_dec(x_852);
lean_inc(x_881);
x_884 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_884, 0, x_881);
x_885 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_886 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_885, x_884, x_13, x_14, x_15, x_16, x_879);
x_887 = lean_ctor_get(x_886, 1);
lean_inc(x_887);
lean_dec(x_886);
x_888 = x_875;
x_889 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_848, x_888);
x_890 = x_889;
lean_inc(x_880);
x_891 = l_Lean_mkFVar(x_880);
lean_inc(x_881);
x_892 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_892, 0, x_881);
x_893 = lean_box(x_857);
lean_inc(x_881);
x_894 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_894, 0, x_880);
lean_closure_set(x_894, 1, x_8);
lean_closure_set(x_894, 2, x_881);
lean_closure_set(x_894, 3, x_3);
lean_closure_set(x_894, 4, x_4);
lean_closure_set(x_894, 5, x_6);
lean_closure_set(x_894, 6, x_7);
lean_closure_set(x_894, 7, x_836);
lean_closure_set(x_894, 8, x_893);
lean_closure_set(x_894, 9, x_867);
lean_closure_set(x_894, 10, x_883);
lean_closure_set(x_894, 11, x_890);
lean_closure_set(x_894, 12, x_891);
x_895 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_895, 0, x_892);
lean_closure_set(x_895, 1, x_894);
x_896 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_881, x_13, x_14, x_15, x_16, x_887);
if (lean_obj_tag(x_896) == 0)
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; 
x_897 = lean_ctor_get(x_896, 0);
lean_inc(x_897);
x_898 = lean_ctor_get(x_896, 1);
lean_inc(x_898);
lean_dec(x_896);
x_899 = lean_ctor_get(x_897, 1);
lean_inc(x_899);
x_900 = lean_ctor_get(x_897, 4);
lean_inc(x_900);
lean_dec(x_897);
x_901 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_899, x_900, x_895, x_13, x_14, x_15, x_16, x_898);
if (lean_obj_tag(x_901) == 0)
{
uint8_t x_902; 
x_902 = !lean_is_exclusive(x_901);
if (x_902 == 0)
{
return x_901;
}
else
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; 
x_903 = lean_ctor_get(x_901, 0);
x_904 = lean_ctor_get(x_901, 1);
lean_inc(x_904);
lean_inc(x_903);
lean_dec(x_901);
x_905 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_905, 0, x_903);
lean_ctor_set(x_905, 1, x_904);
return x_905;
}
}
else
{
uint8_t x_906; 
x_906 = !lean_is_exclusive(x_901);
if (x_906 == 0)
{
return x_901;
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; 
x_907 = lean_ctor_get(x_901, 0);
x_908 = lean_ctor_get(x_901, 1);
lean_inc(x_908);
lean_inc(x_907);
lean_dec(x_901);
x_909 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_909, 0, x_907);
lean_ctor_set(x_909, 1, x_908);
return x_909;
}
}
}
else
{
uint8_t x_910; 
lean_dec(x_895);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_910 = !lean_is_exclusive(x_896);
if (x_910 == 0)
{
return x_896;
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; 
x_911 = lean_ctor_get(x_896, 0);
x_912 = lean_ctor_get(x_896, 1);
lean_inc(x_912);
lean_inc(x_911);
lean_dec(x_896);
x_913 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_913, 0, x_911);
lean_ctor_set(x_913, 1, x_912);
return x_913;
}
}
}
else
{
uint8_t x_914; 
lean_dec(x_875);
lean_dec(x_867);
lean_dec(x_852);
lean_dec(x_836);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_914 = !lean_is_exclusive(x_877);
if (x_914 == 0)
{
return x_877;
}
else
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; 
x_915 = lean_ctor_get(x_877, 0);
x_916 = lean_ctor_get(x_877, 1);
lean_inc(x_916);
lean_inc(x_915);
lean_dec(x_877);
x_917 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_917, 0, x_915);
lean_ctor_set(x_917, 1, x_916);
return x_917;
}
}
}
else
{
uint8_t x_918; 
lean_dec(x_867);
lean_dec(x_852);
lean_dec(x_836);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_918 = !lean_is_exclusive(x_872);
if (x_918 == 0)
{
return x_872;
}
else
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; 
x_919 = lean_ctor_get(x_872, 0);
x_920 = lean_ctor_get(x_872, 1);
lean_inc(x_920);
lean_inc(x_919);
lean_dec(x_872);
x_921 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_921, 0, x_919);
lean_ctor_set(x_921, 1, x_920);
return x_921;
}
}
}
else
{
uint8_t x_922; 
lean_dec(x_852);
lean_dec(x_836);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_922 = !lean_is_exclusive(x_864);
if (x_922 == 0)
{
return x_864;
}
else
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; 
x_923 = lean_ctor_get(x_864, 0);
x_924 = lean_ctor_get(x_864, 1);
lean_inc(x_924);
lean_inc(x_923);
lean_dec(x_864);
x_925 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_925, 0, x_923);
lean_ctor_set(x_925, 1, x_924);
return x_925;
}
}
}
}
else
{
uint8_t x_940; 
lean_dec(x_852);
lean_dec(x_842);
lean_dec(x_836);
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
x_940 = !lean_is_exclusive(x_854);
if (x_940 == 0)
{
return x_854;
}
else
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; 
x_941 = lean_ctor_get(x_854, 0);
x_942 = lean_ctor_get(x_854, 1);
lean_inc(x_942);
lean_inc(x_941);
lean_dec(x_854);
x_943 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_943, 0, x_941);
lean_ctor_set(x_943, 1, x_942);
return x_943;
}
}
}
else
{
uint8_t x_944; 
lean_dec(x_842);
lean_dec(x_836);
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
x_944 = !lean_is_exclusive(x_851);
if (x_944 == 0)
{
return x_851;
}
else
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; 
x_945 = lean_ctor_get(x_851, 0);
x_946 = lean_ctor_get(x_851, 1);
lean_inc(x_946);
lean_inc(x_945);
lean_dec(x_851);
x_947 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_947, 0, x_945);
lean_ctor_set(x_947, 1, x_946);
return x_947;
}
}
}
else
{
uint8_t x_948; 
lean_dec(x_836);
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
x_948 = !lean_is_exclusive(x_837);
if (x_948 == 0)
{
return x_837;
}
else
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; 
x_949 = lean_ctor_get(x_837, 0);
x_950 = lean_ctor_get(x_837, 1);
lean_inc(x_950);
lean_inc(x_949);
lean_dec(x_837);
x_951 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_951, 0, x_949);
lean_ctor_set(x_951, 1, x_950);
return x_951;
}
}
}
case 9:
{
lean_object* x_952; lean_object* x_953; 
lean_dec(x_12);
lean_dec(x_10);
x_952 = lean_ctor_get(x_7, 5);
lean_inc(x_952);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_953 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_6, x_9, x_11, x_952, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_953) == 0)
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; 
x_954 = lean_ctor_get(x_953, 1);
lean_inc(x_954);
lean_dec(x_953);
x_955 = lean_st_ref_get(x_14, x_954);
x_956 = lean_ctor_get(x_955, 0);
lean_inc(x_956);
x_957 = lean_ctor_get(x_955, 1);
lean_inc(x_957);
lean_dec(x_955);
x_958 = lean_ctor_get(x_956, 0);
lean_inc(x_958);
lean_dec(x_956);
x_959 = lean_ctor_get(x_7, 6);
lean_inc(x_959);
x_960 = l_List_redLength___main___rarg(x_959);
x_961 = lean_mk_empty_array_with_capacity(x_960);
lean_dec(x_960);
lean_inc(x_959);
x_962 = l_List_toArrayAux___main___rarg(x_959, x_961);
x_963 = x_962;
x_964 = lean_unsigned_to_nat(0u);
lean_inc(x_958);
lean_inc(x_6);
lean_inc(x_1);
x_965 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_965, 0, x_1);
lean_closure_set(x_965, 1, x_6);
lean_closure_set(x_965, 2, x_9);
lean_closure_set(x_965, 3, x_11);
lean_closure_set(x_965, 4, x_958);
lean_closure_set(x_965, 5, x_959);
lean_closure_set(x_965, 6, x_964);
lean_closure_set(x_965, 7, x_963);
x_966 = x_965;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_967 = lean_apply_5(x_966, x_13, x_14, x_15, x_16, x_957);
if (lean_obj_tag(x_967) == 0)
{
lean_object* x_968; lean_object* x_969; lean_object* x_970; 
x_968 = lean_ctor_get(x_967, 0);
lean_inc(x_968);
x_969 = lean_ctor_get(x_967, 1);
lean_inc(x_969);
lean_dec(x_967);
lean_inc(x_1);
x_970 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_969);
if (lean_obj_tag(x_970) == 0)
{
lean_object* x_971; lean_object* x_972; uint8_t x_973; lean_object* x_974; 
x_971 = lean_ctor_get(x_970, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_970, 1);
lean_inc(x_972);
lean_dec(x_970);
x_973 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_973 == 0)
{
lean_object* x_1043; uint8_t x_1044; 
x_1043 = l_Lean_MetavarContext_exprDependsOn(x_958, x_971, x_2);
x_1044 = lean_unbox(x_1043);
lean_dec(x_1043);
if (x_1044 == 0)
{
x_974 = x_972;
goto block_1042;
}
else
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; uint8_t x_1052; 
lean_dec(x_968);
lean_dec(x_952);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_1045 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1045, 0, x_3);
x_1046 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_1047 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1047, 0, x_1046);
lean_ctor_set(x_1047, 1, x_1045);
x_1048 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_1049 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1049, 0, x_1047);
lean_ctor_set(x_1049, 1, x_1048);
x_1050 = lean_box(0);
x_1051 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1049, x_1050, x_13, x_14, x_15, x_16, x_972);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1052 = !lean_is_exclusive(x_1051);
if (x_1052 == 0)
{
return x_1051;
}
else
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
x_1053 = lean_ctor_get(x_1051, 0);
x_1054 = lean_ctor_get(x_1051, 1);
lean_inc(x_1054);
lean_inc(x_1053);
lean_dec(x_1051);
x_1055 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1055, 0, x_1053);
lean_ctor_set(x_1055, 1, x_1054);
return x_1055;
}
}
}
else
{
lean_dec(x_971);
lean_dec(x_958);
x_974 = x_972;
goto block_1042;
}
block_1042:
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; uint8_t x_979; lean_object* x_980; 
lean_inc(x_968);
x_975 = x_968;
x_976 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_964, x_975);
x_977 = x_976;
x_978 = lean_array_push(x_977, x_2);
x_979 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_980 = l_Lean_Meta_revert(x_1, x_978, x_979, x_13, x_14, x_15, x_16, x_974);
if (lean_obj_tag(x_980) == 0)
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; uint8_t x_987; lean_object* x_988; 
x_981 = lean_ctor_get(x_980, 0);
lean_inc(x_981);
x_982 = lean_ctor_get(x_980, 1);
lean_inc(x_982);
lean_dec(x_980);
x_983 = lean_ctor_get(x_981, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_981, 1);
lean_inc(x_984);
lean_dec(x_981);
x_985 = lean_array_get_size(x_968);
x_986 = lean_box(0);
x_987 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_988 = l_Lean_Meta_introN(x_984, x_985, x_986, x_987, x_13, x_14, x_15, x_16, x_982);
if (lean_obj_tag(x_988) == 0)
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; 
x_989 = lean_ctor_get(x_988, 0);
lean_inc(x_989);
x_990 = lean_ctor_get(x_988, 1);
lean_inc(x_990);
lean_dec(x_988);
x_991 = lean_ctor_get(x_989, 0);
lean_inc(x_991);
x_992 = lean_ctor_get(x_989, 1);
lean_inc(x_992);
lean_dec(x_989);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_993 = l_Lean_Meta_intro1(x_992, x_987, x_13, x_14, x_15, x_16, x_990);
if (lean_obj_tag(x_993) == 0)
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
x_994 = lean_ctor_get(x_993, 0);
lean_inc(x_994);
x_995 = lean_ctor_get(x_993, 1);
lean_inc(x_995);
lean_dec(x_993);
x_996 = lean_ctor_get(x_994, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_994, 1);
lean_inc(x_997);
lean_dec(x_994);
x_998 = lean_box(0);
x_999 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_968, x_991, x_968, x_964, x_998);
lean_dec(x_968);
lean_inc(x_997);
x_1000 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_1000, 0, x_997);
x_1001 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1002 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_1001, x_1000, x_13, x_14, x_15, x_16, x_995);
x_1003 = lean_ctor_get(x_1002, 1);
lean_inc(x_1003);
lean_dec(x_1002);
x_1004 = x_991;
x_1005 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_964, x_1004);
x_1006 = x_1005;
lean_inc(x_996);
x_1007 = l_Lean_mkFVar(x_996);
lean_inc(x_997);
x_1008 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1008, 0, x_997);
x_1009 = lean_box(x_973);
lean_inc(x_997);
x_1010 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_1010, 0, x_996);
lean_closure_set(x_1010, 1, x_8);
lean_closure_set(x_1010, 2, x_997);
lean_closure_set(x_1010, 3, x_3);
lean_closure_set(x_1010, 4, x_4);
lean_closure_set(x_1010, 5, x_6);
lean_closure_set(x_1010, 6, x_7);
lean_closure_set(x_1010, 7, x_952);
lean_closure_set(x_1010, 8, x_1009);
lean_closure_set(x_1010, 9, x_983);
lean_closure_set(x_1010, 10, x_999);
lean_closure_set(x_1010, 11, x_1006);
lean_closure_set(x_1010, 12, x_1007);
x_1011 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_1011, 0, x_1008);
lean_closure_set(x_1011, 1, x_1010);
x_1012 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_997, x_13, x_14, x_15, x_16, x_1003);
if (lean_obj_tag(x_1012) == 0)
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
x_1013 = lean_ctor_get(x_1012, 0);
lean_inc(x_1013);
x_1014 = lean_ctor_get(x_1012, 1);
lean_inc(x_1014);
lean_dec(x_1012);
x_1015 = lean_ctor_get(x_1013, 1);
lean_inc(x_1015);
x_1016 = lean_ctor_get(x_1013, 4);
lean_inc(x_1016);
lean_dec(x_1013);
x_1017 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_1015, x_1016, x_1011, x_13, x_14, x_15, x_16, x_1014);
if (lean_obj_tag(x_1017) == 0)
{
uint8_t x_1018; 
x_1018 = !lean_is_exclusive(x_1017);
if (x_1018 == 0)
{
return x_1017;
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
x_1019 = lean_ctor_get(x_1017, 0);
x_1020 = lean_ctor_get(x_1017, 1);
lean_inc(x_1020);
lean_inc(x_1019);
lean_dec(x_1017);
x_1021 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1021, 0, x_1019);
lean_ctor_set(x_1021, 1, x_1020);
return x_1021;
}
}
else
{
uint8_t x_1022; 
x_1022 = !lean_is_exclusive(x_1017);
if (x_1022 == 0)
{
return x_1017;
}
else
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
x_1023 = lean_ctor_get(x_1017, 0);
x_1024 = lean_ctor_get(x_1017, 1);
lean_inc(x_1024);
lean_inc(x_1023);
lean_dec(x_1017);
x_1025 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1025, 0, x_1023);
lean_ctor_set(x_1025, 1, x_1024);
return x_1025;
}
}
}
else
{
uint8_t x_1026; 
lean_dec(x_1011);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1026 = !lean_is_exclusive(x_1012);
if (x_1026 == 0)
{
return x_1012;
}
else
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
x_1027 = lean_ctor_get(x_1012, 0);
x_1028 = lean_ctor_get(x_1012, 1);
lean_inc(x_1028);
lean_inc(x_1027);
lean_dec(x_1012);
x_1029 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1029, 0, x_1027);
lean_ctor_set(x_1029, 1, x_1028);
return x_1029;
}
}
}
else
{
uint8_t x_1030; 
lean_dec(x_991);
lean_dec(x_983);
lean_dec(x_968);
lean_dec(x_952);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1030 = !lean_is_exclusive(x_993);
if (x_1030 == 0)
{
return x_993;
}
else
{
lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; 
x_1031 = lean_ctor_get(x_993, 0);
x_1032 = lean_ctor_get(x_993, 1);
lean_inc(x_1032);
lean_inc(x_1031);
lean_dec(x_993);
x_1033 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1033, 0, x_1031);
lean_ctor_set(x_1033, 1, x_1032);
return x_1033;
}
}
}
else
{
uint8_t x_1034; 
lean_dec(x_983);
lean_dec(x_968);
lean_dec(x_952);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1034 = !lean_is_exclusive(x_988);
if (x_1034 == 0)
{
return x_988;
}
else
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; 
x_1035 = lean_ctor_get(x_988, 0);
x_1036 = lean_ctor_get(x_988, 1);
lean_inc(x_1036);
lean_inc(x_1035);
lean_dec(x_988);
x_1037 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1037, 0, x_1035);
lean_ctor_set(x_1037, 1, x_1036);
return x_1037;
}
}
}
else
{
uint8_t x_1038; 
lean_dec(x_968);
lean_dec(x_952);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1038 = !lean_is_exclusive(x_980);
if (x_1038 == 0)
{
return x_980;
}
else
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1039 = lean_ctor_get(x_980, 0);
x_1040 = lean_ctor_get(x_980, 1);
lean_inc(x_1040);
lean_inc(x_1039);
lean_dec(x_980);
x_1041 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1041, 0, x_1039);
lean_ctor_set(x_1041, 1, x_1040);
return x_1041;
}
}
}
}
else
{
uint8_t x_1056; 
lean_dec(x_968);
lean_dec(x_958);
lean_dec(x_952);
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
x_1056 = !lean_is_exclusive(x_970);
if (x_1056 == 0)
{
return x_970;
}
else
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; 
x_1057 = lean_ctor_get(x_970, 0);
x_1058 = lean_ctor_get(x_970, 1);
lean_inc(x_1058);
lean_inc(x_1057);
lean_dec(x_970);
x_1059 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1059, 0, x_1057);
lean_ctor_set(x_1059, 1, x_1058);
return x_1059;
}
}
}
else
{
uint8_t x_1060; 
lean_dec(x_958);
lean_dec(x_952);
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
x_1060 = !lean_is_exclusive(x_967);
if (x_1060 == 0)
{
return x_967;
}
else
{
lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; 
x_1061 = lean_ctor_get(x_967, 0);
x_1062 = lean_ctor_get(x_967, 1);
lean_inc(x_1062);
lean_inc(x_1061);
lean_dec(x_967);
x_1063 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1063, 0, x_1061);
lean_ctor_set(x_1063, 1, x_1062);
return x_1063;
}
}
}
else
{
uint8_t x_1064; 
lean_dec(x_952);
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
x_1064 = !lean_is_exclusive(x_953);
if (x_1064 == 0)
{
return x_953;
}
else
{
lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; 
x_1065 = lean_ctor_get(x_953, 0);
x_1066 = lean_ctor_get(x_953, 1);
lean_inc(x_1066);
lean_inc(x_1065);
lean_dec(x_953);
x_1067 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1067, 0, x_1065);
lean_ctor_set(x_1067, 1, x_1066);
return x_1067;
}
}
}
case 10:
{
lean_object* x_1068; lean_object* x_1069; 
lean_dec(x_12);
lean_dec(x_10);
x_1068 = lean_ctor_get(x_7, 5);
lean_inc(x_1068);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1069 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_6, x_9, x_11, x_1068, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_1069) == 0)
{
lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
x_1070 = lean_ctor_get(x_1069, 1);
lean_inc(x_1070);
lean_dec(x_1069);
x_1071 = lean_st_ref_get(x_14, x_1070);
x_1072 = lean_ctor_get(x_1071, 0);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_1071, 1);
lean_inc(x_1073);
lean_dec(x_1071);
x_1074 = lean_ctor_get(x_1072, 0);
lean_inc(x_1074);
lean_dec(x_1072);
x_1075 = lean_ctor_get(x_7, 6);
lean_inc(x_1075);
x_1076 = l_List_redLength___main___rarg(x_1075);
x_1077 = lean_mk_empty_array_with_capacity(x_1076);
lean_dec(x_1076);
lean_inc(x_1075);
x_1078 = l_List_toArrayAux___main___rarg(x_1075, x_1077);
x_1079 = x_1078;
x_1080 = lean_unsigned_to_nat(0u);
lean_inc(x_1074);
lean_inc(x_6);
lean_inc(x_1);
x_1081 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_1081, 0, x_1);
lean_closure_set(x_1081, 1, x_6);
lean_closure_set(x_1081, 2, x_9);
lean_closure_set(x_1081, 3, x_11);
lean_closure_set(x_1081, 4, x_1074);
lean_closure_set(x_1081, 5, x_1075);
lean_closure_set(x_1081, 6, x_1080);
lean_closure_set(x_1081, 7, x_1079);
x_1082 = x_1081;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_1083 = lean_apply_5(x_1082, x_13, x_14, x_15, x_16, x_1073);
if (lean_obj_tag(x_1083) == 0)
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; 
x_1084 = lean_ctor_get(x_1083, 0);
lean_inc(x_1084);
x_1085 = lean_ctor_get(x_1083, 1);
lean_inc(x_1085);
lean_dec(x_1083);
lean_inc(x_1);
x_1086 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_1085);
if (lean_obj_tag(x_1086) == 0)
{
lean_object* x_1087; lean_object* x_1088; uint8_t x_1089; lean_object* x_1090; 
x_1087 = lean_ctor_get(x_1086, 0);
lean_inc(x_1087);
x_1088 = lean_ctor_get(x_1086, 1);
lean_inc(x_1088);
lean_dec(x_1086);
x_1089 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_1089 == 0)
{
lean_object* x_1159; uint8_t x_1160; 
x_1159 = l_Lean_MetavarContext_exprDependsOn(x_1074, x_1087, x_2);
x_1160 = lean_unbox(x_1159);
lean_dec(x_1159);
if (x_1160 == 0)
{
x_1090 = x_1088;
goto block_1158;
}
else
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; uint8_t x_1168; 
lean_dec(x_1084);
lean_dec(x_1068);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_1161 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1161, 0, x_3);
x_1162 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_1163 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1163, 0, x_1162);
lean_ctor_set(x_1163, 1, x_1161);
x_1164 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_1165 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1165, 0, x_1163);
lean_ctor_set(x_1165, 1, x_1164);
x_1166 = lean_box(0);
x_1167 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1165, x_1166, x_13, x_14, x_15, x_16, x_1088);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1168 = !lean_is_exclusive(x_1167);
if (x_1168 == 0)
{
return x_1167;
}
else
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; 
x_1169 = lean_ctor_get(x_1167, 0);
x_1170 = lean_ctor_get(x_1167, 1);
lean_inc(x_1170);
lean_inc(x_1169);
lean_dec(x_1167);
x_1171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1171, 0, x_1169);
lean_ctor_set(x_1171, 1, x_1170);
return x_1171;
}
}
}
else
{
lean_dec(x_1087);
lean_dec(x_1074);
x_1090 = x_1088;
goto block_1158;
}
block_1158:
{
lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; uint8_t x_1095; lean_object* x_1096; 
lean_inc(x_1084);
x_1091 = x_1084;
x_1092 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1080, x_1091);
x_1093 = x_1092;
x_1094 = lean_array_push(x_1093, x_2);
x_1095 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_1096 = l_Lean_Meta_revert(x_1, x_1094, x_1095, x_13, x_14, x_15, x_16, x_1090);
if (lean_obj_tag(x_1096) == 0)
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; uint8_t x_1103; lean_object* x_1104; 
x_1097 = lean_ctor_get(x_1096, 0);
lean_inc(x_1097);
x_1098 = lean_ctor_get(x_1096, 1);
lean_inc(x_1098);
lean_dec(x_1096);
x_1099 = lean_ctor_get(x_1097, 0);
lean_inc(x_1099);
x_1100 = lean_ctor_get(x_1097, 1);
lean_inc(x_1100);
lean_dec(x_1097);
x_1101 = lean_array_get_size(x_1084);
x_1102 = lean_box(0);
x_1103 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_1104 = l_Lean_Meta_introN(x_1100, x_1101, x_1102, x_1103, x_13, x_14, x_15, x_16, x_1098);
if (lean_obj_tag(x_1104) == 0)
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; 
x_1105 = lean_ctor_get(x_1104, 0);
lean_inc(x_1105);
x_1106 = lean_ctor_get(x_1104, 1);
lean_inc(x_1106);
lean_dec(x_1104);
x_1107 = lean_ctor_get(x_1105, 0);
lean_inc(x_1107);
x_1108 = lean_ctor_get(x_1105, 1);
lean_inc(x_1108);
lean_dec(x_1105);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_1109 = l_Lean_Meta_intro1(x_1108, x_1103, x_13, x_14, x_15, x_16, x_1106);
if (lean_obj_tag(x_1109) == 0)
{
lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; 
x_1110 = lean_ctor_get(x_1109, 0);
lean_inc(x_1110);
x_1111 = lean_ctor_get(x_1109, 1);
lean_inc(x_1111);
lean_dec(x_1109);
x_1112 = lean_ctor_get(x_1110, 0);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_1110, 1);
lean_inc(x_1113);
lean_dec(x_1110);
x_1114 = lean_box(0);
x_1115 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1084, x_1107, x_1084, x_1080, x_1114);
lean_dec(x_1084);
lean_inc(x_1113);
x_1116 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_1116, 0, x_1113);
x_1117 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1118 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_1117, x_1116, x_13, x_14, x_15, x_16, x_1111);
x_1119 = lean_ctor_get(x_1118, 1);
lean_inc(x_1119);
lean_dec(x_1118);
x_1120 = x_1107;
x_1121 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1080, x_1120);
x_1122 = x_1121;
lean_inc(x_1112);
x_1123 = l_Lean_mkFVar(x_1112);
lean_inc(x_1113);
x_1124 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1124, 0, x_1113);
x_1125 = lean_box(x_1089);
lean_inc(x_1113);
x_1126 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_1126, 0, x_1112);
lean_closure_set(x_1126, 1, x_8);
lean_closure_set(x_1126, 2, x_1113);
lean_closure_set(x_1126, 3, x_3);
lean_closure_set(x_1126, 4, x_4);
lean_closure_set(x_1126, 5, x_6);
lean_closure_set(x_1126, 6, x_7);
lean_closure_set(x_1126, 7, x_1068);
lean_closure_set(x_1126, 8, x_1125);
lean_closure_set(x_1126, 9, x_1099);
lean_closure_set(x_1126, 10, x_1115);
lean_closure_set(x_1126, 11, x_1122);
lean_closure_set(x_1126, 12, x_1123);
x_1127 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_1127, 0, x_1124);
lean_closure_set(x_1127, 1, x_1126);
x_1128 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_1113, x_13, x_14, x_15, x_16, x_1119);
if (lean_obj_tag(x_1128) == 0)
{
lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; 
x_1129 = lean_ctor_get(x_1128, 0);
lean_inc(x_1129);
x_1130 = lean_ctor_get(x_1128, 1);
lean_inc(x_1130);
lean_dec(x_1128);
x_1131 = lean_ctor_get(x_1129, 1);
lean_inc(x_1131);
x_1132 = lean_ctor_get(x_1129, 4);
lean_inc(x_1132);
lean_dec(x_1129);
x_1133 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_1131, x_1132, x_1127, x_13, x_14, x_15, x_16, x_1130);
if (lean_obj_tag(x_1133) == 0)
{
uint8_t x_1134; 
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
x_1137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1137, 0, x_1135);
lean_ctor_set(x_1137, 1, x_1136);
return x_1137;
}
}
else
{
uint8_t x_1138; 
x_1138 = !lean_is_exclusive(x_1133);
if (x_1138 == 0)
{
return x_1133;
}
else
{
lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; 
x_1139 = lean_ctor_get(x_1133, 0);
x_1140 = lean_ctor_get(x_1133, 1);
lean_inc(x_1140);
lean_inc(x_1139);
lean_dec(x_1133);
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
lean_dec(x_1127);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1142 = !lean_is_exclusive(x_1128);
if (x_1142 == 0)
{
return x_1128;
}
else
{
lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; 
x_1143 = lean_ctor_get(x_1128, 0);
x_1144 = lean_ctor_get(x_1128, 1);
lean_inc(x_1144);
lean_inc(x_1143);
lean_dec(x_1128);
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
lean_dec(x_1107);
lean_dec(x_1099);
lean_dec(x_1084);
lean_dec(x_1068);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1146 = !lean_is_exclusive(x_1109);
if (x_1146 == 0)
{
return x_1109;
}
else
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; 
x_1147 = lean_ctor_get(x_1109, 0);
x_1148 = lean_ctor_get(x_1109, 1);
lean_inc(x_1148);
lean_inc(x_1147);
lean_dec(x_1109);
x_1149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1149, 0, x_1147);
lean_ctor_set(x_1149, 1, x_1148);
return x_1149;
}
}
}
else
{
uint8_t x_1150; 
lean_dec(x_1099);
lean_dec(x_1084);
lean_dec(x_1068);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1150 = !lean_is_exclusive(x_1104);
if (x_1150 == 0)
{
return x_1104;
}
else
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; 
x_1151 = lean_ctor_get(x_1104, 0);
x_1152 = lean_ctor_get(x_1104, 1);
lean_inc(x_1152);
lean_inc(x_1151);
lean_dec(x_1104);
x_1153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1153, 0, x_1151);
lean_ctor_set(x_1153, 1, x_1152);
return x_1153;
}
}
}
else
{
uint8_t x_1154; 
lean_dec(x_1084);
lean_dec(x_1068);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1154 = !lean_is_exclusive(x_1096);
if (x_1154 == 0)
{
return x_1096;
}
else
{
lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; 
x_1155 = lean_ctor_get(x_1096, 0);
x_1156 = lean_ctor_get(x_1096, 1);
lean_inc(x_1156);
lean_inc(x_1155);
lean_dec(x_1096);
x_1157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1157, 0, x_1155);
lean_ctor_set(x_1157, 1, x_1156);
return x_1157;
}
}
}
}
else
{
uint8_t x_1172; 
lean_dec(x_1084);
lean_dec(x_1074);
lean_dec(x_1068);
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
x_1172 = !lean_is_exclusive(x_1086);
if (x_1172 == 0)
{
return x_1086;
}
else
{
lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; 
x_1173 = lean_ctor_get(x_1086, 0);
x_1174 = lean_ctor_get(x_1086, 1);
lean_inc(x_1174);
lean_inc(x_1173);
lean_dec(x_1086);
x_1175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1175, 0, x_1173);
lean_ctor_set(x_1175, 1, x_1174);
return x_1175;
}
}
}
else
{
uint8_t x_1176; 
lean_dec(x_1074);
lean_dec(x_1068);
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
x_1176 = !lean_is_exclusive(x_1083);
if (x_1176 == 0)
{
return x_1083;
}
else
{
lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; 
x_1177 = lean_ctor_get(x_1083, 0);
x_1178 = lean_ctor_get(x_1083, 1);
lean_inc(x_1178);
lean_inc(x_1177);
lean_dec(x_1083);
x_1179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1179, 0, x_1177);
lean_ctor_set(x_1179, 1, x_1178);
return x_1179;
}
}
}
else
{
uint8_t x_1180; 
lean_dec(x_1068);
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
x_1180 = !lean_is_exclusive(x_1069);
if (x_1180 == 0)
{
return x_1069;
}
else
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; 
x_1181 = lean_ctor_get(x_1069, 0);
x_1182 = lean_ctor_get(x_1069, 1);
lean_inc(x_1182);
lean_inc(x_1181);
lean_dec(x_1069);
x_1183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1183, 0, x_1181);
lean_ctor_set(x_1183, 1, x_1182);
return x_1183;
}
}
}
case 11:
{
lean_object* x_1184; lean_object* x_1185; 
lean_dec(x_12);
lean_dec(x_10);
x_1184 = lean_ctor_get(x_7, 5);
lean_inc(x_1184);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1185 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_6, x_9, x_11, x_1184, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_1185) == 0)
{
lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; 
x_1186 = lean_ctor_get(x_1185, 1);
lean_inc(x_1186);
lean_dec(x_1185);
x_1187 = lean_st_ref_get(x_14, x_1186);
x_1188 = lean_ctor_get(x_1187, 0);
lean_inc(x_1188);
x_1189 = lean_ctor_get(x_1187, 1);
lean_inc(x_1189);
lean_dec(x_1187);
x_1190 = lean_ctor_get(x_1188, 0);
lean_inc(x_1190);
lean_dec(x_1188);
x_1191 = lean_ctor_get(x_7, 6);
lean_inc(x_1191);
x_1192 = l_List_redLength___main___rarg(x_1191);
x_1193 = lean_mk_empty_array_with_capacity(x_1192);
lean_dec(x_1192);
lean_inc(x_1191);
x_1194 = l_List_toArrayAux___main___rarg(x_1191, x_1193);
x_1195 = x_1194;
x_1196 = lean_unsigned_to_nat(0u);
lean_inc(x_1190);
lean_inc(x_6);
lean_inc(x_1);
x_1197 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_1197, 0, x_1);
lean_closure_set(x_1197, 1, x_6);
lean_closure_set(x_1197, 2, x_9);
lean_closure_set(x_1197, 3, x_11);
lean_closure_set(x_1197, 4, x_1190);
lean_closure_set(x_1197, 5, x_1191);
lean_closure_set(x_1197, 6, x_1196);
lean_closure_set(x_1197, 7, x_1195);
x_1198 = x_1197;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_1199 = lean_apply_5(x_1198, x_13, x_14, x_15, x_16, x_1189);
if (lean_obj_tag(x_1199) == 0)
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
x_1200 = lean_ctor_get(x_1199, 0);
lean_inc(x_1200);
x_1201 = lean_ctor_get(x_1199, 1);
lean_inc(x_1201);
lean_dec(x_1199);
lean_inc(x_1);
x_1202 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_1201);
if (lean_obj_tag(x_1202) == 0)
{
lean_object* x_1203; lean_object* x_1204; uint8_t x_1205; lean_object* x_1206; 
x_1203 = lean_ctor_get(x_1202, 0);
lean_inc(x_1203);
x_1204 = lean_ctor_get(x_1202, 1);
lean_inc(x_1204);
lean_dec(x_1202);
x_1205 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_1205 == 0)
{
lean_object* x_1275; uint8_t x_1276; 
x_1275 = l_Lean_MetavarContext_exprDependsOn(x_1190, x_1203, x_2);
x_1276 = lean_unbox(x_1275);
lean_dec(x_1275);
if (x_1276 == 0)
{
x_1206 = x_1204;
goto block_1274;
}
else
{
lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; uint8_t x_1284; 
lean_dec(x_1200);
lean_dec(x_1184);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_1277 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1277, 0, x_3);
x_1278 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_1279 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1279, 0, x_1278);
lean_ctor_set(x_1279, 1, x_1277);
x_1280 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_1281 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1281, 0, x_1279);
lean_ctor_set(x_1281, 1, x_1280);
x_1282 = lean_box(0);
x_1283 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1281, x_1282, x_13, x_14, x_15, x_16, x_1204);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1284 = !lean_is_exclusive(x_1283);
if (x_1284 == 0)
{
return x_1283;
}
else
{
lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; 
x_1285 = lean_ctor_get(x_1283, 0);
x_1286 = lean_ctor_get(x_1283, 1);
lean_inc(x_1286);
lean_inc(x_1285);
lean_dec(x_1283);
x_1287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1287, 0, x_1285);
lean_ctor_set(x_1287, 1, x_1286);
return x_1287;
}
}
}
else
{
lean_dec(x_1203);
lean_dec(x_1190);
x_1206 = x_1204;
goto block_1274;
}
block_1274:
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; uint8_t x_1211; lean_object* x_1212; 
lean_inc(x_1200);
x_1207 = x_1200;
x_1208 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1196, x_1207);
x_1209 = x_1208;
x_1210 = lean_array_push(x_1209, x_2);
x_1211 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_1212 = l_Lean_Meta_revert(x_1, x_1210, x_1211, x_13, x_14, x_15, x_16, x_1206);
if (lean_obj_tag(x_1212) == 0)
{
lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; uint8_t x_1219; lean_object* x_1220; 
x_1213 = lean_ctor_get(x_1212, 0);
lean_inc(x_1213);
x_1214 = lean_ctor_get(x_1212, 1);
lean_inc(x_1214);
lean_dec(x_1212);
x_1215 = lean_ctor_get(x_1213, 0);
lean_inc(x_1215);
x_1216 = lean_ctor_get(x_1213, 1);
lean_inc(x_1216);
lean_dec(x_1213);
x_1217 = lean_array_get_size(x_1200);
x_1218 = lean_box(0);
x_1219 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_1220 = l_Lean_Meta_introN(x_1216, x_1217, x_1218, x_1219, x_13, x_14, x_15, x_16, x_1214);
if (lean_obj_tag(x_1220) == 0)
{
lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; 
x_1221 = lean_ctor_get(x_1220, 0);
lean_inc(x_1221);
x_1222 = lean_ctor_get(x_1220, 1);
lean_inc(x_1222);
lean_dec(x_1220);
x_1223 = lean_ctor_get(x_1221, 0);
lean_inc(x_1223);
x_1224 = lean_ctor_get(x_1221, 1);
lean_inc(x_1224);
lean_dec(x_1221);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_1225 = l_Lean_Meta_intro1(x_1224, x_1219, x_13, x_14, x_15, x_16, x_1222);
if (lean_obj_tag(x_1225) == 0)
{
lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; 
x_1226 = lean_ctor_get(x_1225, 0);
lean_inc(x_1226);
x_1227 = lean_ctor_get(x_1225, 1);
lean_inc(x_1227);
lean_dec(x_1225);
x_1228 = lean_ctor_get(x_1226, 0);
lean_inc(x_1228);
x_1229 = lean_ctor_get(x_1226, 1);
lean_inc(x_1229);
lean_dec(x_1226);
x_1230 = lean_box(0);
x_1231 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1200, x_1223, x_1200, x_1196, x_1230);
lean_dec(x_1200);
lean_inc(x_1229);
x_1232 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_1232, 0, x_1229);
x_1233 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1234 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_1233, x_1232, x_13, x_14, x_15, x_16, x_1227);
x_1235 = lean_ctor_get(x_1234, 1);
lean_inc(x_1235);
lean_dec(x_1234);
x_1236 = x_1223;
x_1237 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1196, x_1236);
x_1238 = x_1237;
lean_inc(x_1228);
x_1239 = l_Lean_mkFVar(x_1228);
lean_inc(x_1229);
x_1240 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1240, 0, x_1229);
x_1241 = lean_box(x_1205);
lean_inc(x_1229);
x_1242 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_1242, 0, x_1228);
lean_closure_set(x_1242, 1, x_8);
lean_closure_set(x_1242, 2, x_1229);
lean_closure_set(x_1242, 3, x_3);
lean_closure_set(x_1242, 4, x_4);
lean_closure_set(x_1242, 5, x_6);
lean_closure_set(x_1242, 6, x_7);
lean_closure_set(x_1242, 7, x_1184);
lean_closure_set(x_1242, 8, x_1241);
lean_closure_set(x_1242, 9, x_1215);
lean_closure_set(x_1242, 10, x_1231);
lean_closure_set(x_1242, 11, x_1238);
lean_closure_set(x_1242, 12, x_1239);
x_1243 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_1243, 0, x_1240);
lean_closure_set(x_1243, 1, x_1242);
x_1244 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_1229, x_13, x_14, x_15, x_16, x_1235);
if (lean_obj_tag(x_1244) == 0)
{
lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; 
x_1245 = lean_ctor_get(x_1244, 0);
lean_inc(x_1245);
x_1246 = lean_ctor_get(x_1244, 1);
lean_inc(x_1246);
lean_dec(x_1244);
x_1247 = lean_ctor_get(x_1245, 1);
lean_inc(x_1247);
x_1248 = lean_ctor_get(x_1245, 4);
lean_inc(x_1248);
lean_dec(x_1245);
x_1249 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_1247, x_1248, x_1243, x_13, x_14, x_15, x_16, x_1246);
if (lean_obj_tag(x_1249) == 0)
{
uint8_t x_1250; 
x_1250 = !lean_is_exclusive(x_1249);
if (x_1250 == 0)
{
return x_1249;
}
else
{
lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; 
x_1251 = lean_ctor_get(x_1249, 0);
x_1252 = lean_ctor_get(x_1249, 1);
lean_inc(x_1252);
lean_inc(x_1251);
lean_dec(x_1249);
x_1253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1253, 0, x_1251);
lean_ctor_set(x_1253, 1, x_1252);
return x_1253;
}
}
else
{
uint8_t x_1254; 
x_1254 = !lean_is_exclusive(x_1249);
if (x_1254 == 0)
{
return x_1249;
}
else
{
lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; 
x_1255 = lean_ctor_get(x_1249, 0);
x_1256 = lean_ctor_get(x_1249, 1);
lean_inc(x_1256);
lean_inc(x_1255);
lean_dec(x_1249);
x_1257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1257, 0, x_1255);
lean_ctor_set(x_1257, 1, x_1256);
return x_1257;
}
}
}
else
{
uint8_t x_1258; 
lean_dec(x_1243);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1258 = !lean_is_exclusive(x_1244);
if (x_1258 == 0)
{
return x_1244;
}
else
{
lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; 
x_1259 = lean_ctor_get(x_1244, 0);
x_1260 = lean_ctor_get(x_1244, 1);
lean_inc(x_1260);
lean_inc(x_1259);
lean_dec(x_1244);
x_1261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1261, 0, x_1259);
lean_ctor_set(x_1261, 1, x_1260);
return x_1261;
}
}
}
else
{
uint8_t x_1262; 
lean_dec(x_1223);
lean_dec(x_1215);
lean_dec(x_1200);
lean_dec(x_1184);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1262 = !lean_is_exclusive(x_1225);
if (x_1262 == 0)
{
return x_1225;
}
else
{
lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; 
x_1263 = lean_ctor_get(x_1225, 0);
x_1264 = lean_ctor_get(x_1225, 1);
lean_inc(x_1264);
lean_inc(x_1263);
lean_dec(x_1225);
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
lean_dec(x_1215);
lean_dec(x_1200);
lean_dec(x_1184);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1266 = !lean_is_exclusive(x_1220);
if (x_1266 == 0)
{
return x_1220;
}
else
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
x_1267 = lean_ctor_get(x_1220, 0);
x_1268 = lean_ctor_get(x_1220, 1);
lean_inc(x_1268);
lean_inc(x_1267);
lean_dec(x_1220);
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
lean_dec(x_1200);
lean_dec(x_1184);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1270 = !lean_is_exclusive(x_1212);
if (x_1270 == 0)
{
return x_1212;
}
else
{
lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; 
x_1271 = lean_ctor_get(x_1212, 0);
x_1272 = lean_ctor_get(x_1212, 1);
lean_inc(x_1272);
lean_inc(x_1271);
lean_dec(x_1212);
x_1273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1273, 0, x_1271);
lean_ctor_set(x_1273, 1, x_1272);
return x_1273;
}
}
}
}
else
{
uint8_t x_1288; 
lean_dec(x_1200);
lean_dec(x_1190);
lean_dec(x_1184);
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
x_1288 = !lean_is_exclusive(x_1202);
if (x_1288 == 0)
{
return x_1202;
}
else
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; 
x_1289 = lean_ctor_get(x_1202, 0);
x_1290 = lean_ctor_get(x_1202, 1);
lean_inc(x_1290);
lean_inc(x_1289);
lean_dec(x_1202);
x_1291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1291, 0, x_1289);
lean_ctor_set(x_1291, 1, x_1290);
return x_1291;
}
}
}
else
{
uint8_t x_1292; 
lean_dec(x_1190);
lean_dec(x_1184);
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
x_1292 = !lean_is_exclusive(x_1199);
if (x_1292 == 0)
{
return x_1199;
}
else
{
lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; 
x_1293 = lean_ctor_get(x_1199, 0);
x_1294 = lean_ctor_get(x_1199, 1);
lean_inc(x_1294);
lean_inc(x_1293);
lean_dec(x_1199);
x_1295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1295, 0, x_1293);
lean_ctor_set(x_1295, 1, x_1294);
return x_1295;
}
}
}
else
{
uint8_t x_1296; 
lean_dec(x_1184);
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
x_1296 = !lean_is_exclusive(x_1185);
if (x_1296 == 0)
{
return x_1185;
}
else
{
lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; 
x_1297 = lean_ctor_get(x_1185, 0);
x_1298 = lean_ctor_get(x_1185, 1);
lean_inc(x_1298);
lean_inc(x_1297);
lean_dec(x_1185);
x_1299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1299, 0, x_1297);
lean_ctor_set(x_1299, 1, x_1298);
return x_1299;
}
}
}
default: 
{
lean_object* x_1300; lean_object* x_1301; 
lean_dec(x_12);
lean_dec(x_10);
x_1300 = lean_ctor_get(x_7, 5);
lean_inc(x_1300);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_1);
x_1301 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_6, x_9, x_11, x_1300, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_1301) == 0)
{
lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; 
x_1302 = lean_ctor_get(x_1301, 1);
lean_inc(x_1302);
lean_dec(x_1301);
x_1303 = lean_st_ref_get(x_14, x_1302);
x_1304 = lean_ctor_get(x_1303, 0);
lean_inc(x_1304);
x_1305 = lean_ctor_get(x_1303, 1);
lean_inc(x_1305);
lean_dec(x_1303);
x_1306 = lean_ctor_get(x_1304, 0);
lean_inc(x_1306);
lean_dec(x_1304);
x_1307 = lean_ctor_get(x_7, 6);
lean_inc(x_1307);
x_1308 = l_List_redLength___main___rarg(x_1307);
x_1309 = lean_mk_empty_array_with_capacity(x_1308);
lean_dec(x_1308);
lean_inc(x_1307);
x_1310 = l_List_toArrayAux___main___rarg(x_1307, x_1309);
x_1311 = x_1310;
x_1312 = lean_unsigned_to_nat(0u);
lean_inc(x_1306);
lean_inc(x_6);
lean_inc(x_1);
x_1313 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_1313, 0, x_1);
lean_closure_set(x_1313, 1, x_6);
lean_closure_set(x_1313, 2, x_9);
lean_closure_set(x_1313, 3, x_11);
lean_closure_set(x_1313, 4, x_1306);
lean_closure_set(x_1313, 5, x_1307);
lean_closure_set(x_1313, 6, x_1312);
lean_closure_set(x_1313, 7, x_1311);
x_1314 = x_1313;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_1315 = lean_apply_5(x_1314, x_13, x_14, x_15, x_16, x_1305);
if (lean_obj_tag(x_1315) == 0)
{
lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; 
x_1316 = lean_ctor_get(x_1315, 0);
lean_inc(x_1316);
x_1317 = lean_ctor_get(x_1315, 1);
lean_inc(x_1317);
lean_dec(x_1315);
lean_inc(x_1);
x_1318 = l_Lean_Meta_getMVarType(x_1, x_13, x_14, x_15, x_16, x_1317);
if (lean_obj_tag(x_1318) == 0)
{
lean_object* x_1319; lean_object* x_1320; uint8_t x_1321; lean_object* x_1322; 
x_1319 = lean_ctor_get(x_1318, 0);
lean_inc(x_1319);
x_1320 = lean_ctor_get(x_1318, 1);
lean_inc(x_1320);
lean_dec(x_1318);
x_1321 = lean_ctor_get_uint8(x_7, sizeof(void*)*8);
if (x_1321 == 0)
{
lean_object* x_1391; uint8_t x_1392; 
x_1391 = l_Lean_MetavarContext_exprDependsOn(x_1306, x_1319, x_2);
x_1392 = lean_unbox(x_1391);
lean_dec(x_1391);
if (x_1392 == 0)
{
x_1322 = x_1320;
goto block_1390;
}
else
{
lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; uint8_t x_1400; 
lean_dec(x_1316);
lean_dec(x_1300);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_1393 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1393, 0, x_3);
x_1394 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_1395 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1395, 0, x_1394);
lean_ctor_set(x_1395, 1, x_1393);
x_1396 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_1397 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1397, 0, x_1395);
lean_ctor_set(x_1397, 1, x_1396);
x_1398 = lean_box(0);
x_1399 = l_Lean_Meta_throwTacticEx___rarg(x_6, x_1, x_1397, x_1398, x_13, x_14, x_15, x_16, x_1320);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1400 = !lean_is_exclusive(x_1399);
if (x_1400 == 0)
{
return x_1399;
}
else
{
lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
x_1401 = lean_ctor_get(x_1399, 0);
x_1402 = lean_ctor_get(x_1399, 1);
lean_inc(x_1402);
lean_inc(x_1401);
lean_dec(x_1399);
x_1403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1403, 0, x_1401);
lean_ctor_set(x_1403, 1, x_1402);
return x_1403;
}
}
}
else
{
lean_dec(x_1319);
lean_dec(x_1306);
x_1322 = x_1320;
goto block_1390;
}
block_1390:
{
lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; uint8_t x_1327; lean_object* x_1328; 
lean_inc(x_1316);
x_1323 = x_1316;
x_1324 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__5(x_1312, x_1323);
x_1325 = x_1324;
x_1326 = lean_array_push(x_1325, x_2);
x_1327 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_1328 = l_Lean_Meta_revert(x_1, x_1326, x_1327, x_13, x_14, x_15, x_16, x_1322);
if (lean_obj_tag(x_1328) == 0)
{
lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; uint8_t x_1335; lean_object* x_1336; 
x_1329 = lean_ctor_get(x_1328, 0);
lean_inc(x_1329);
x_1330 = lean_ctor_get(x_1328, 1);
lean_inc(x_1330);
lean_dec(x_1328);
x_1331 = lean_ctor_get(x_1329, 0);
lean_inc(x_1331);
x_1332 = lean_ctor_get(x_1329, 1);
lean_inc(x_1332);
lean_dec(x_1329);
x_1333 = lean_array_get_size(x_1316);
x_1334 = lean_box(0);
x_1335 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_1336 = l_Lean_Meta_introN(x_1332, x_1333, x_1334, x_1335, x_13, x_14, x_15, x_16, x_1330);
if (lean_obj_tag(x_1336) == 0)
{
lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; 
x_1337 = lean_ctor_get(x_1336, 0);
lean_inc(x_1337);
x_1338 = lean_ctor_get(x_1336, 1);
lean_inc(x_1338);
lean_dec(x_1336);
x_1339 = lean_ctor_get(x_1337, 0);
lean_inc(x_1339);
x_1340 = lean_ctor_get(x_1337, 1);
lean_inc(x_1340);
lean_dec(x_1337);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_1341 = l_Lean_Meta_intro1(x_1340, x_1335, x_13, x_14, x_15, x_16, x_1338);
if (lean_obj_tag(x_1341) == 0)
{
lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; 
x_1342 = lean_ctor_get(x_1341, 0);
lean_inc(x_1342);
x_1343 = lean_ctor_get(x_1341, 1);
lean_inc(x_1343);
lean_dec(x_1341);
x_1344 = lean_ctor_get(x_1342, 0);
lean_inc(x_1344);
x_1345 = lean_ctor_get(x_1342, 1);
lean_inc(x_1345);
lean_dec(x_1342);
x_1346 = lean_box(0);
x_1347 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1316, x_1339, x_1316, x_1312, x_1346);
lean_dec(x_1316);
lean_inc(x_1345);
x_1348 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_1348, 0, x_1345);
x_1349 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1350 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_1349, x_1348, x_13, x_14, x_15, x_16, x_1343);
x_1351 = lean_ctor_get(x_1350, 1);
lean_inc(x_1351);
lean_dec(x_1350);
x_1352 = x_1339;
x_1353 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1312, x_1352);
x_1354 = x_1353;
lean_inc(x_1344);
x_1355 = l_Lean_mkFVar(x_1344);
lean_inc(x_1345);
x_1356 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1356, 0, x_1345);
x_1357 = lean_box(x_1321);
lean_inc(x_1345);
x_1358 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_1358, 0, x_1344);
lean_closure_set(x_1358, 1, x_8);
lean_closure_set(x_1358, 2, x_1345);
lean_closure_set(x_1358, 3, x_3);
lean_closure_set(x_1358, 4, x_4);
lean_closure_set(x_1358, 5, x_6);
lean_closure_set(x_1358, 6, x_7);
lean_closure_set(x_1358, 7, x_1300);
lean_closure_set(x_1358, 8, x_1357);
lean_closure_set(x_1358, 9, x_1331);
lean_closure_set(x_1358, 10, x_1347);
lean_closure_set(x_1358, 11, x_1354);
lean_closure_set(x_1358, 12, x_1355);
x_1359 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_1359, 0, x_1356);
lean_closure_set(x_1359, 1, x_1358);
x_1360 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_1345, x_13, x_14, x_15, x_16, x_1351);
if (lean_obj_tag(x_1360) == 0)
{
lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; 
x_1361 = lean_ctor_get(x_1360, 0);
lean_inc(x_1361);
x_1362 = lean_ctor_get(x_1360, 1);
lean_inc(x_1362);
lean_dec(x_1360);
x_1363 = lean_ctor_get(x_1361, 1);
lean_inc(x_1363);
x_1364 = lean_ctor_get(x_1361, 4);
lean_inc(x_1364);
lean_dec(x_1361);
x_1365 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_1363, x_1364, x_1359, x_13, x_14, x_15, x_16, x_1362);
if (lean_obj_tag(x_1365) == 0)
{
uint8_t x_1366; 
x_1366 = !lean_is_exclusive(x_1365);
if (x_1366 == 0)
{
return x_1365;
}
else
{
lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; 
x_1367 = lean_ctor_get(x_1365, 0);
x_1368 = lean_ctor_get(x_1365, 1);
lean_inc(x_1368);
lean_inc(x_1367);
lean_dec(x_1365);
x_1369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1369, 0, x_1367);
lean_ctor_set(x_1369, 1, x_1368);
return x_1369;
}
}
else
{
uint8_t x_1370; 
x_1370 = !lean_is_exclusive(x_1365);
if (x_1370 == 0)
{
return x_1365;
}
else
{
lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; 
x_1371 = lean_ctor_get(x_1365, 0);
x_1372 = lean_ctor_get(x_1365, 1);
lean_inc(x_1372);
lean_inc(x_1371);
lean_dec(x_1365);
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
lean_dec(x_1359);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1374 = !lean_is_exclusive(x_1360);
if (x_1374 == 0)
{
return x_1360;
}
else
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
x_1375 = lean_ctor_get(x_1360, 0);
x_1376 = lean_ctor_get(x_1360, 1);
lean_inc(x_1376);
lean_inc(x_1375);
lean_dec(x_1360);
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
lean_dec(x_1339);
lean_dec(x_1331);
lean_dec(x_1316);
lean_dec(x_1300);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1378 = !lean_is_exclusive(x_1341);
if (x_1378 == 0)
{
return x_1341;
}
else
{
lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
x_1379 = lean_ctor_get(x_1341, 0);
x_1380 = lean_ctor_get(x_1341, 1);
lean_inc(x_1380);
lean_inc(x_1379);
lean_dec(x_1341);
x_1381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1381, 0, x_1379);
lean_ctor_set(x_1381, 1, x_1380);
return x_1381;
}
}
}
else
{
uint8_t x_1382; 
lean_dec(x_1331);
lean_dec(x_1316);
lean_dec(x_1300);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1382 = !lean_is_exclusive(x_1336);
if (x_1382 == 0)
{
return x_1336;
}
else
{
lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; 
x_1383 = lean_ctor_get(x_1336, 0);
x_1384 = lean_ctor_get(x_1336, 1);
lean_inc(x_1384);
lean_inc(x_1383);
lean_dec(x_1336);
x_1385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1385, 0, x_1383);
lean_ctor_set(x_1385, 1, x_1384);
return x_1385;
}
}
}
else
{
uint8_t x_1386; 
lean_dec(x_1316);
lean_dec(x_1300);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_1386 = !lean_is_exclusive(x_1328);
if (x_1386 == 0)
{
return x_1328;
}
else
{
lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; 
x_1387 = lean_ctor_get(x_1328, 0);
x_1388 = lean_ctor_get(x_1328, 1);
lean_inc(x_1388);
lean_inc(x_1387);
lean_dec(x_1328);
x_1389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1389, 0, x_1387);
lean_ctor_set(x_1389, 1, x_1388);
return x_1389;
}
}
}
}
else
{
uint8_t x_1404; 
lean_dec(x_1316);
lean_dec(x_1306);
lean_dec(x_1300);
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
x_1404 = !lean_is_exclusive(x_1318);
if (x_1404 == 0)
{
return x_1318;
}
else
{
lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; 
x_1405 = lean_ctor_get(x_1318, 0);
x_1406 = lean_ctor_get(x_1318, 1);
lean_inc(x_1406);
lean_inc(x_1405);
lean_dec(x_1318);
x_1407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1407, 0, x_1405);
lean_ctor_set(x_1407, 1, x_1406);
return x_1407;
}
}
}
else
{
uint8_t x_1408; 
lean_dec(x_1306);
lean_dec(x_1300);
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
x_1408 = !lean_is_exclusive(x_1315);
if (x_1408 == 0)
{
return x_1315;
}
else
{
lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; 
x_1409 = lean_ctor_get(x_1315, 0);
x_1410 = lean_ctor_get(x_1315, 1);
lean_inc(x_1410);
lean_inc(x_1409);
lean_dec(x_1315);
x_1411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1411, 0, x_1409);
lean_ctor_set(x_1411, 1, x_1410);
return x_1411;
}
}
}
else
{
uint8_t x_1412; 
lean_dec(x_1300);
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
x_1412 = !lean_is_exclusive(x_1301);
if (x_1412 == 0)
{
return x_1301;
}
else
{
lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; 
x_1413 = lean_ctor_get(x_1301, 0);
x_1414 = lean_ctor_get(x_1301, 1);
lean_inc(x_1414);
lean_inc(x_1413);
lean_dec(x_1301);
x_1415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1415, 0, x_1413);
lean_ctor_set(x_1415, 1, x_1414);
return x_1415;
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
x_13 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_1, x_8, x_9, x_10, x_11, x_12);
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
x_22 = l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(x_20, x_21, x_8, x_9, x_10, x_11, x_19);
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
x_34 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12(x_3, x_1, x_2, x_4, x_5, x_6, x_18, x_21, x_27, x_27, x_31, x_33, x_8, x_9, x_10, x_11, x_26);
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
x_13 = l_Lean_Meta_getParamNamesImpl___closed__1;
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_induction___lambda__1___boxed), 12, 6);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_13);
lean_closure_set(x_14, 5, x_11);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
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
x_21 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_19, x_20, x_15, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
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
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed(lean_object** _args) {
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
x_21 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
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
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
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
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
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
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__1 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__1);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__2 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__2);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__3 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__3);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__4 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___closed__4);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__2 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__2);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__3 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__3);
l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4 = _init_l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4);
res = l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
