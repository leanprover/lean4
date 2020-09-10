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
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at_Lean_Meta_induction___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize___main(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_1__getTargetArity(lean_object*);
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_7__regTraceClasses(lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__8;
lean_object* l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_induction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3;
lean_object* l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at_Lean_Meta_induction___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__2;
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Meta_normalizeLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__3;
lean_object* l_Lean_Meta_normalizeLevel___at_Lean_Meta_induction___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_3__getTypeBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__8;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__5;
lean_object* l_Lean_MetavarContext_localDeclDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___closed__4;
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__4;
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
lean_object* l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__3;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_2__addRecParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__6;
uint8_t l_Lean_Level_isZero(lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed(lean_object**);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__3;
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___at___private_Lean_Meta_Tactic_Induction_4__finalizeAux___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__3;
lean_object* l_Lean_Meta_InductionSubgoal_inhabited;
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__5;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__5;
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
x_7 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_16__isClassExpensive_x3f___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_13 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_4, x_5, x_6, x_7, x_8, x_9);
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
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_8, x_9, x_10, x_11, x_12, x_16);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_indentExpr(x_2);
x_9 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg___closed__3;
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
x_12 = lean_box(0);
x_13 = l_Lean_Meta_throwTacticEx___rarg(x_11, x_1, x_10, x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
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
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at_Lean_Meta_induction___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
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
lean_inc(x_11);
x_12 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_13, 4);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_13, sizeof(void*)*5);
lean_dec(x_13);
x_21 = l_Lean_Meta_getConfig___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__3(x_3, x_4, x_5, x_6, x_18);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
if (x_20 == 0)
{
lean_object* x_49; 
lean_free_object(x_21);
lean_dec(x_2);
x_49 = lean_box(0);
x_25 = x_49;
goto block_48;
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_23, 6);
if (x_50 == 0)
{
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_21, 0, x_2);
return x_21;
}
else
{
lean_object* x_51; 
lean_free_object(x_21);
lean_dec(x_2);
x_51 = lean_box(0);
x_25 = x_51;
goto block_48;
}
}
block_48:
{
uint8_t x_26; 
lean_dec(x_25);
x_26 = lean_ctor_get_uint8(x_23, 7);
lean_dec(x_23);
if (x_26 == 0)
{
lean_dec(x_11);
x_2 = x_19;
x_7 = x_24;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_st_ref_take(x_4, x_24);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_29, 3);
x_33 = lean_box(0);
x_34 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_32, x_11, x_33);
lean_ctor_set(x_29, 3, x_34);
x_35 = lean_st_ref_set(x_4, x_29, x_30);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_2 = x_19;
x_7 = x_36;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
x_40 = lean_ctor_get(x_29, 2);
x_41 = lean_ctor_get(x_29, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_42 = lean_box(0);
x_43 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_41, x_11, x_42);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_44, 2, x_40);
lean_ctor_set(x_44, 3, x_43);
x_45 = lean_st_ref_set(x_4, x_44, x_30);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_2 = x_19;
x_7 = x_46;
goto _start;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_21, 0);
x_53 = lean_ctor_get(x_21, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_21);
if (x_20 == 0)
{
lean_object* x_72; 
lean_dec(x_2);
x_72 = lean_box(0);
x_54 = x_72;
goto block_71;
}
else
{
uint8_t x_73; 
x_73 = lean_ctor_get_uint8(x_52, 6);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_52);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_2);
lean_ctor_set(x_74, 1, x_53);
return x_74;
}
else
{
lean_object* x_75; 
lean_dec(x_2);
x_75 = lean_box(0);
x_54 = x_75;
goto block_71;
}
}
block_71:
{
uint8_t x_55; 
lean_dec(x_54);
x_55 = lean_ctor_get_uint8(x_52, 7);
lean_dec(x_52);
if (x_55 == 0)
{
lean_dec(x_11);
x_2 = x_19;
x_7 = x_53;
goto _start;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_57 = lean_st_ref_take(x_4, x_53);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_58, 3);
lean_inc(x_63);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 x_64 = x_58;
} else {
 lean_dec_ref(x_58);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
x_66 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_63, x_11, x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 4, 0);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_61);
lean_ctor_set(x_67, 2, x_62);
lean_ctor_set(x_67, 3, x_66);
x_68 = lean_st_ref_set(x_4, x_67, x_59);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_2 = x_19;
x_7 = x_69;
goto _start;
}
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_12);
if (x_76 == 0)
{
return x_12;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_12, 0);
x_78 = lean_ctor_get(x_12, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_12);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
case 2:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_2, 0);
lean_inc(x_80);
x_81 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1(x_80, x_3, x_4, x_5, x_6, x_7);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
lean_ctor_set(x_81, 0, x_2);
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_2);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_2);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_dec(x_81);
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
lean_dec(x_82);
x_2 = x_88;
x_7 = x_87;
goto _start;
}
}
case 4:
{
lean_object* x_90; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_90 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
x_94 = l_Lean_Expr_isAppOf(x_92, x_1);
if (x_94 == 0)
{
lean_object* x_95; 
lean_free_object(x_90);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_92);
x_95 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_92, x_3, x_4, x_5, x_6, x_93);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_95, 0);
lean_dec(x_98);
lean_ctor_set(x_95, 0, x_92);
return x_95;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
lean_dec(x_95);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_92);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_92);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
lean_dec(x_95);
x_102 = lean_ctor_get(x_96, 0);
lean_inc(x_102);
lean_dec(x_96);
x_2 = x_102;
x_7 = x_101;
goto _start;
}
}
else
{
uint8_t x_104; 
lean_dec(x_92);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_104 = !lean_is_exclusive(x_95);
if (x_104 == 0)
{
return x_95;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_95, 0);
x_106 = lean_ctor_get(x_95, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_95);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_90;
}
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_90, 0);
x_109 = lean_ctor_get(x_90, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_90);
x_110 = l_Lean_Expr_isAppOf(x_108, x_1);
if (x_110 == 0)
{
lean_object* x_111; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_108);
x_111 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_108, x_3, x_4, x_5, x_6, x_109);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_108);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_108);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
lean_dec(x_111);
x_117 = lean_ctor_get(x_112, 0);
lean_inc(x_117);
lean_dec(x_112);
x_2 = x_117;
x_7 = x_116;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_108);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_119 = lean_ctor_get(x_111, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_111, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_121 = x_111;
} else {
 lean_dec_ref(x_111);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
lean_object* x_123; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_108);
lean_ctor_set(x_123, 1, x_109);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_124 = !lean_is_exclusive(x_90);
if (x_124 == 0)
{
return x_90;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_90, 0);
x_126 = lean_ctor_get(x_90, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_90);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
case 5:
{
lean_object* x_128; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_128 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_ctor_get(x_128, 1);
x_132 = l_Lean_Expr_isAppOf(x_130, x_1);
if (x_132 == 0)
{
lean_object* x_133; 
lean_free_object(x_128);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_130);
x_133 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_130, x_3, x_4, x_5, x_6, x_131);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
uint8_t x_135; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_135 = !lean_is_exclusive(x_133);
if (x_135 == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_133, 0);
lean_dec(x_136);
lean_ctor_set(x_133, 0, x_130);
return x_133;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_133, 1);
lean_inc(x_137);
lean_dec(x_133);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_130);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_130);
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
lean_dec(x_133);
x_140 = lean_ctor_get(x_134, 0);
lean_inc(x_140);
lean_dec(x_134);
x_2 = x_140;
x_7 = x_139;
goto _start;
}
}
else
{
uint8_t x_142; 
lean_dec(x_130);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_142 = !lean_is_exclusive(x_133);
if (x_142 == 0)
{
return x_133;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_133, 0);
x_144 = lean_ctor_get(x_133, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_133);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_128;
}
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = lean_ctor_get(x_128, 0);
x_147 = lean_ctor_get(x_128, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_128);
x_148 = l_Lean_Expr_isAppOf(x_146, x_1);
if (x_148 == 0)
{
lean_object* x_149; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_146);
x_149 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_146, x_3, x_4, x_5, x_6, x_147);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_146);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_146);
x_154 = lean_ctor_get(x_149, 1);
lean_inc(x_154);
lean_dec(x_149);
x_155 = lean_ctor_get(x_150, 0);
lean_inc(x_155);
lean_dec(x_150);
x_2 = x_155;
x_7 = x_154;
goto _start;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_146);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_157 = lean_ctor_get(x_149, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_149, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_159 = x_149;
} else {
 lean_dec_ref(x_149);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
else
{
lean_object* x_161; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_146);
lean_ctor_set(x_161, 1, x_147);
return x_161;
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_162 = !lean_is_exclusive(x_128);
if (x_162 == 0)
{
return x_128;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_128, 0);
x_164 = lean_ctor_get(x_128, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_128);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
case 8:
{
lean_object* x_166; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_166 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_166) == 0)
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = lean_ctor_get(x_166, 1);
x_170 = l_Lean_Expr_isAppOf(x_168, x_1);
if (x_170 == 0)
{
lean_object* x_171; 
lean_free_object(x_166);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_168);
x_171 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_168, x_3, x_4, x_5, x_6, x_169);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_obj_tag(x_172) == 0)
{
uint8_t x_173; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_173 = !lean_is_exclusive(x_171);
if (x_173 == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_171, 0);
lean_dec(x_174);
lean_ctor_set(x_171, 0, x_168);
return x_171;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_171, 1);
lean_inc(x_175);
lean_dec(x_171);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_168);
x_177 = lean_ctor_get(x_171, 1);
lean_inc(x_177);
lean_dec(x_171);
x_178 = lean_ctor_get(x_172, 0);
lean_inc(x_178);
lean_dec(x_172);
x_2 = x_178;
x_7 = x_177;
goto _start;
}
}
else
{
uint8_t x_180; 
lean_dec(x_168);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_180 = !lean_is_exclusive(x_171);
if (x_180 == 0)
{
return x_171;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_171, 0);
x_182 = lean_ctor_get(x_171, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_171);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_166;
}
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_166, 0);
x_185 = lean_ctor_get(x_166, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_166);
x_186 = l_Lean_Expr_isAppOf(x_184, x_1);
if (x_186 == 0)
{
lean_object* x_187; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_184);
x_187 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_184, x_3, x_4, x_5, x_6, x_185);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_190 = x_187;
} else {
 lean_dec_ref(x_187);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_184);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_184);
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
lean_dec(x_187);
x_193 = lean_ctor_get(x_188, 0);
lean_inc(x_193);
lean_dec(x_188);
x_2 = x_193;
x_7 = x_192;
goto _start;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_184);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_195 = lean_ctor_get(x_187, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_187, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_197 = x_187;
} else {
 lean_dec_ref(x_187);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
else
{
lean_object* x_199; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_184);
lean_ctor_set(x_199, 1, x_185);
return x_199;
}
}
}
else
{
uint8_t x_200; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_200 = !lean_is_exclusive(x_166);
if (x_200 == 0)
{
return x_166;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_166, 0);
x_202 = lean_ctor_get(x_166, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_166);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
case 10:
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_2, 1);
lean_inc(x_204);
lean_dec(x_2);
x_2 = x_204;
goto _start;
}
case 11:
{
lean_object* x_206; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_206 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_206) == 0)
{
uint8_t x_207; 
x_207 = !lean_is_exclusive(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = lean_ctor_get(x_206, 0);
x_209 = lean_ctor_get(x_206, 1);
x_210 = l_Lean_Expr_isAppOf(x_208, x_1);
if (x_210 == 0)
{
lean_object* x_211; 
lean_free_object(x_206);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_208);
x_211 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_208, x_3, x_4, x_5, x_6, x_209);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
if (lean_obj_tag(x_212) == 0)
{
uint8_t x_213; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_213 = !lean_is_exclusive(x_211);
if (x_213 == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_211, 0);
lean_dec(x_214);
lean_ctor_set(x_211, 0, x_208);
return x_211;
}
else
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_211, 1);
lean_inc(x_215);
lean_dec(x_211);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_208);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_208);
x_217 = lean_ctor_get(x_211, 1);
lean_inc(x_217);
lean_dec(x_211);
x_218 = lean_ctor_get(x_212, 0);
lean_inc(x_218);
lean_dec(x_212);
x_2 = x_218;
x_7 = x_217;
goto _start;
}
}
else
{
uint8_t x_220; 
lean_dec(x_208);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_220 = !lean_is_exclusive(x_211);
if (x_220 == 0)
{
return x_211;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_211, 0);
x_222 = lean_ctor_get(x_211, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_211);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_206;
}
}
else
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_224 = lean_ctor_get(x_206, 0);
x_225 = lean_ctor_get(x_206, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_206);
x_226 = l_Lean_Expr_isAppOf(x_224, x_1);
if (x_226 == 0)
{
lean_object* x_227; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_224);
x_227 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_224, x_3, x_4, x_5, x_6, x_225);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_230 = x_227;
} else {
 lean_dec_ref(x_227);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_224);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_224);
x_232 = lean_ctor_get(x_227, 1);
lean_inc(x_232);
lean_dec(x_227);
x_233 = lean_ctor_get(x_228, 0);
lean_inc(x_233);
lean_dec(x_228);
x_2 = x_233;
x_7 = x_232;
goto _start;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_224);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_235 = lean_ctor_get(x_227, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_227, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_237 = x_227;
} else {
 lean_dec_ref(x_227);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(1, 2, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_236);
return x_238;
}
}
else
{
lean_object* x_239; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_224);
lean_ctor_set(x_239, 1, x_225);
return x_239;
}
}
}
else
{
uint8_t x_240; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_240 = !lean_is_exclusive(x_206);
if (x_240 == 0)
{
return x_206;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_206, 0);
x_242 = lean_ctor_get(x_206, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_206);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
}
case 12:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_2);
x_244 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
x_245 = l_unreachable_x21___rarg(x_244);
x_246 = lean_apply_5(x_245, x_3, x_4, x_5, x_6, x_7);
return x_246;
}
default: 
{
lean_object* x_247; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_2);
lean_ctor_set(x_247, 1, x_7);
return x_247;
}
}
}
}
lean_object* l_Lean_Meta_whnfHeadPredAux___main___at_Lean_Meta_induction___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at_Lean_Meta_induction___spec__3(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = l_Lean_indentExpr(x_3);
x_22 = l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3;
x_23 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_box(0);
x_25 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_23, x_24, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_60; uint8_t x_79; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_10, x_18);
lean_dec(x_10);
x_20 = lean_nat_sub(x_9, x_19);
x_21 = lean_nat_sub(x_20, x_18);
lean_dec(x_20);
x_22 = l_Lean_Expr_Inhabited;
x_23 = lean_array_get(x_22, x_4, x_21);
x_79 = lean_nat_dec_eq(x_21, x_7);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = lean_expr_eqv(x_23, x_8);
if (x_80 == 0)
{
x_60 = x_15;
goto block_78;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_5);
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_8);
x_82 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_83 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Nat_forMAux___main___at_Lean_Meta_induction___spec__6___closed__9;
x_85 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_indentExpr(x_3);
x_87 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_box(0);
x_89 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_87, x_88, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_11);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
return x_89;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_89);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
x_60 = x_15;
goto block_78;
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
block_78:
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
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
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
x_70 = l_Lean_indentExpr(x_3);
x_71 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_box(0);
x_73 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_71, x_72, x_11, x_12, x_13, x_14, x_60);
lean_dec(x_11);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
return x_73;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_73);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_15);
return x_95;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_54; 
x_18 = lean_array_fget(x_8, x_7);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_fset(x_8, x_7, x_19);
x_21 = x_18;
x_22 = lean_array_get_size(x_4);
x_54 = lean_nat_dec_le(x_22, x_21);
if (x_54 == 0)
{
x_23 = x_13;
goto block_53;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_5);
x_55 = l_Lean_indentExpr(x_3);
x_56 = l_List_forM___main___at_Lean_Meta_induction___spec__4___closed__3;
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_box(0);
x_59 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_57, x_58, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
return x_59;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
block_53:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_39; 
x_24 = l_Lean_Expr_Inhabited;
x_25 = lean_array_get(x_24, x_4, x_21);
x_39 = l_Lean_Expr_isFVar(x_25);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
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
x_45 = l_Lean_indentExpr(x_3);
x_46 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_box(0);
x_48 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_46, x_47, x_9, x_10, x_11, x_12, x_23);
lean_dec(x_9);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_48);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
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
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_9);
x_17 = lean_ctor_get(x_6, 5);
lean_inc(x_17);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_18 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_17, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_13, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_6, 6);
lean_inc(x_24);
x_25 = l_List_redLength___main___rarg(x_24);
x_26 = lean_mk_empty_array_with_capacity(x_25);
lean_dec(x_25);
lean_inc(x_24);
x_27 = l_List_toArrayAux___main___rarg(x_24, x_26);
x_28 = x_27;
x_29 = lean_unsigned_to_nat(0u);
lean_inc(x_23);
lean_inc(x_5);
lean_inc(x_1);
x_30 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_5);
lean_closure_set(x_30, 2, x_8);
lean_closure_set(x_30, 3, x_10);
lean_closure_set(x_30, 4, x_23);
lean_closure_set(x_30, 5, x_24);
lean_closure_set(x_30, 6, x_29);
lean_closure_set(x_30, 7, x_28);
x_31 = x_30;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_32 = lean_apply_5(x_31, x_12, x_13, x_14, x_15, x_22);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_1);
x_35 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_38 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = l_Lean_MetavarContext_exprDependsOn(x_23, x_36, x_2);
x_92 = lean_unbox(x_91);
lean_dec(x_91);
if (x_92 == 0)
{
x_39 = x_37;
goto block_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_93 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_93, 0, x_3);
x_94 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_95 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_97 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_box(0);
x_99 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_97, x_98, x_12, x_13, x_14, x_15, x_37);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
return x_99;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_99);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_dec(x_36);
lean_dec(x_23);
x_39 = x_37;
goto block_90;
}
block_90:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
lean_inc(x_33);
x_40 = x_33;
x_41 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(x_29, x_40);
x_42 = x_41;
x_43 = lean_array_push(x_42, x_2);
x_44 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_45 = l_Lean_Meta_revert(x_1, x_43, x_44, x_12, x_13, x_14, x_15, x_39);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_array_get_size(x_33);
x_51 = lean_box(0);
x_52 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_53 = l_Lean_Meta_introN(x_49, x_50, x_51, x_52, x_12, x_13, x_14, x_15, x_47);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
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
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_58 = l_Lean_Meta_intro1(x_57, x_52, x_12, x_13, x_14, x_15, x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_box(0);
x_64 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_33, x_56, x_33, x_29, x_63);
lean_dec(x_33);
lean_inc(x_62);
x_65 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_65, 0, x_62);
x_66 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_67 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_66, x_65, x_12, x_13, x_14, x_15, x_60);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = x_56;
x_70 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_29, x_69);
x_71 = x_70;
lean_inc(x_61);
x_72 = l_Lean_mkFVar(x_61);
lean_inc(x_62);
x_73 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_73, 0, x_62);
x_74 = lean_box(x_38);
lean_inc(x_62);
x_75 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_75, 0, x_61);
lean_closure_set(x_75, 1, x_7);
lean_closure_set(x_75, 2, x_62);
lean_closure_set(x_75, 3, x_3);
lean_closure_set(x_75, 4, x_4);
lean_closure_set(x_75, 5, x_5);
lean_closure_set(x_75, 6, x_6);
lean_closure_set(x_75, 7, x_17);
lean_closure_set(x_75, 8, x_74);
lean_closure_set(x_75, 9, x_48);
lean_closure_set(x_75, 10, x_64);
lean_closure_set(x_75, 11, x_71);
lean_closure_set(x_75, 12, x_72);
x_76 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_76, 0, x_73);
lean_closure_set(x_76, 1, x_75);
x_77 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_62, x_76, x_12, x_13, x_14, x_15, x_68);
return x_77;
}
else
{
uint8_t x_78; 
lean_dec(x_56);
lean_dec(x_48);
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_58);
if (x_78 == 0)
{
return x_58;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_58, 0);
x_80 = lean_ctor_get(x_58, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_58);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_48);
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_53);
if (x_82 == 0)
{
return x_53;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_53, 0);
x_84 = lean_ctor_get(x_53, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_53);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_45);
if (x_86 == 0)
{
return x_45;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_45, 0);
x_88 = lean_ctor_get(x_45, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_45);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_33);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_35);
if (x_104 == 0)
{
return x_35;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_35, 0);
x_106 = lean_ctor_get(x_35, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_35);
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
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_32);
if (x_108 == 0)
{
return x_32;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_32, 0);
x_110 = lean_ctor_get(x_32, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_32);
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
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
x_112 = !lean_is_exclusive(x_18);
if (x_112 == 0)
{
return x_18;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_18, 0);
x_114 = lean_ctor_get(x_18, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_18);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
case 1:
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_11);
lean_dec(x_9);
x_116 = lean_ctor_get(x_6, 5);
lean_inc(x_116);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_117 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_116, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_st_ref_get(x_13, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_ctor_get(x_6, 6);
lean_inc(x_123);
x_124 = l_List_redLength___main___rarg(x_123);
x_125 = lean_mk_empty_array_with_capacity(x_124);
lean_dec(x_124);
lean_inc(x_123);
x_126 = l_List_toArrayAux___main___rarg(x_123, x_125);
x_127 = x_126;
x_128 = lean_unsigned_to_nat(0u);
lean_inc(x_122);
lean_inc(x_5);
lean_inc(x_1);
x_129 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_129, 0, x_1);
lean_closure_set(x_129, 1, x_5);
lean_closure_set(x_129, 2, x_8);
lean_closure_set(x_129, 3, x_10);
lean_closure_set(x_129, 4, x_122);
lean_closure_set(x_129, 5, x_123);
lean_closure_set(x_129, 6, x_128);
lean_closure_set(x_129, 7, x_127);
x_130 = x_129;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_131 = lean_apply_5(x_130, x_12, x_13, x_14, x_15, x_121);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
lean_inc(x_1);
x_134 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_137 == 0)
{
lean_object* x_190; uint8_t x_191; 
x_190 = l_Lean_MetavarContext_exprDependsOn(x_122, x_135, x_2);
x_191 = lean_unbox(x_190);
lean_dec(x_190);
if (x_191 == 0)
{
x_138 = x_136;
goto block_189;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_dec(x_132);
lean_dec(x_116);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_192 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_192, 0, x_3);
x_193 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_194 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_196 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_box(0);
x_198 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_196, x_197, x_12, x_13, x_14, x_15, x_136);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
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
}
else
{
lean_dec(x_135);
lean_dec(x_122);
x_138 = x_136;
goto block_189;
}
block_189:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; 
lean_inc(x_132);
x_139 = x_132;
x_140 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(x_128, x_139);
x_141 = x_140;
x_142 = lean_array_push(x_141, x_2);
x_143 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_144 = l_Lean_Meta_revert(x_1, x_142, x_143, x_12, x_13, x_14, x_15, x_138);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_ctor_get(x_145, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_149 = lean_array_get_size(x_132);
x_150 = lean_box(0);
x_151 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_152 = l_Lean_Meta_introN(x_148, x_149, x_150, x_151, x_12, x_13, x_14, x_15, x_146);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
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
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_157 = l_Lean_Meta_intro1(x_156, x_151, x_12, x_13, x_14, x_15, x_154);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
lean_dec(x_158);
x_162 = lean_box(0);
x_163 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_132, x_155, x_132, x_128, x_162);
lean_dec(x_132);
lean_inc(x_161);
x_164 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_164, 0, x_161);
x_165 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_166 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_165, x_164, x_12, x_13, x_14, x_15, x_159);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = x_155;
x_169 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_128, x_168);
x_170 = x_169;
lean_inc(x_160);
x_171 = l_Lean_mkFVar(x_160);
lean_inc(x_161);
x_172 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_172, 0, x_161);
x_173 = lean_box(x_137);
lean_inc(x_161);
x_174 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_174, 0, x_160);
lean_closure_set(x_174, 1, x_7);
lean_closure_set(x_174, 2, x_161);
lean_closure_set(x_174, 3, x_3);
lean_closure_set(x_174, 4, x_4);
lean_closure_set(x_174, 5, x_5);
lean_closure_set(x_174, 6, x_6);
lean_closure_set(x_174, 7, x_116);
lean_closure_set(x_174, 8, x_173);
lean_closure_set(x_174, 9, x_147);
lean_closure_set(x_174, 10, x_163);
lean_closure_set(x_174, 11, x_170);
lean_closure_set(x_174, 12, x_171);
x_175 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_175, 0, x_172);
lean_closure_set(x_175, 1, x_174);
x_176 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_161, x_175, x_12, x_13, x_14, x_15, x_167);
return x_176;
}
else
{
uint8_t x_177; 
lean_dec(x_155);
lean_dec(x_147);
lean_dec(x_132);
lean_dec(x_116);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_177 = !lean_is_exclusive(x_157);
if (x_177 == 0)
{
return x_157;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_157, 0);
x_179 = lean_ctor_get(x_157, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_157);
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
lean_dec(x_147);
lean_dec(x_132);
lean_dec(x_116);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_181 = !lean_is_exclusive(x_152);
if (x_181 == 0)
{
return x_152;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_152, 0);
x_183 = lean_ctor_get(x_152, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_152);
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
lean_dec(x_132);
lean_dec(x_116);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_185 = !lean_is_exclusive(x_144);
if (x_185 == 0)
{
return x_144;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_144, 0);
x_187 = lean_ctor_get(x_144, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_144);
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
uint8_t x_203; 
lean_dec(x_132);
lean_dec(x_122);
lean_dec(x_116);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_203 = !lean_is_exclusive(x_134);
if (x_203 == 0)
{
return x_134;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_134, 0);
x_205 = lean_ctor_get(x_134, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_134);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
uint8_t x_207; 
lean_dec(x_122);
lean_dec(x_116);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_207 = !lean_is_exclusive(x_131);
if (x_207 == 0)
{
return x_131;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_131, 0);
x_209 = lean_ctor_get(x_131, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_131);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_116);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
x_211 = !lean_is_exclusive(x_117);
if (x_211 == 0)
{
return x_117;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_117, 0);
x_213 = lean_ctor_get(x_117, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_117);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
case 2:
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_11);
lean_dec(x_9);
x_215 = lean_ctor_get(x_6, 5);
lean_inc(x_215);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_216 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_215, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
x_218 = lean_st_ref_get(x_13, x_217);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_ctor_get(x_6, 6);
lean_inc(x_222);
x_223 = l_List_redLength___main___rarg(x_222);
x_224 = lean_mk_empty_array_with_capacity(x_223);
lean_dec(x_223);
lean_inc(x_222);
x_225 = l_List_toArrayAux___main___rarg(x_222, x_224);
x_226 = x_225;
x_227 = lean_unsigned_to_nat(0u);
lean_inc(x_221);
lean_inc(x_5);
lean_inc(x_1);
x_228 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_228, 0, x_1);
lean_closure_set(x_228, 1, x_5);
lean_closure_set(x_228, 2, x_8);
lean_closure_set(x_228, 3, x_10);
lean_closure_set(x_228, 4, x_221);
lean_closure_set(x_228, 5, x_222);
lean_closure_set(x_228, 6, x_227);
lean_closure_set(x_228, 7, x_226);
x_229 = x_228;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_230 = lean_apply_5(x_229, x_12, x_13, x_14, x_15, x_220);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
lean_inc(x_1);
x_233 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_232);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_236 == 0)
{
lean_object* x_289; uint8_t x_290; 
x_289 = l_Lean_MetavarContext_exprDependsOn(x_221, x_234, x_2);
x_290 = lean_unbox(x_289);
lean_dec(x_289);
if (x_290 == 0)
{
x_237 = x_235;
goto block_288;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
lean_dec(x_231);
lean_dec(x_215);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_291 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_291, 0, x_3);
x_292 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_293 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_291);
x_294 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_295 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
x_296 = lean_box(0);
x_297 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_295, x_296, x_12, x_13, x_14, x_15, x_235);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
lean_dec(x_234);
lean_dec(x_221);
x_237 = x_235;
goto block_288;
}
block_288:
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; 
lean_inc(x_231);
x_238 = x_231;
x_239 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(x_227, x_238);
x_240 = x_239;
x_241 = lean_array_push(x_240, x_2);
x_242 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_243 = l_Lean_Meta_revert(x_1, x_241, x_242, x_12, x_13, x_14, x_15, x_237);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_ctor_get(x_244, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_244, 1);
lean_inc(x_247);
lean_dec(x_244);
x_248 = lean_array_get_size(x_231);
x_249 = lean_box(0);
x_250 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_251 = l_Lean_Meta_introN(x_247, x_248, x_249, x_250, x_12, x_13, x_14, x_15, x_245);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = lean_ctor_get(x_252, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_252, 1);
lean_inc(x_255);
lean_dec(x_252);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_256 = l_Lean_Meta_intro1(x_255, x_250, x_12, x_13, x_14, x_15, x_253);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_ctor_get(x_257, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_257, 1);
lean_inc(x_260);
lean_dec(x_257);
x_261 = lean_box(0);
x_262 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_231, x_254, x_231, x_227, x_261);
lean_dec(x_231);
lean_inc(x_260);
x_263 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_263, 0, x_260);
x_264 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_265 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_264, x_263, x_12, x_13, x_14, x_15, x_258);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
lean_dec(x_265);
x_267 = x_254;
x_268 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_227, x_267);
x_269 = x_268;
lean_inc(x_259);
x_270 = l_Lean_mkFVar(x_259);
lean_inc(x_260);
x_271 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_271, 0, x_260);
x_272 = lean_box(x_236);
lean_inc(x_260);
x_273 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_273, 0, x_259);
lean_closure_set(x_273, 1, x_7);
lean_closure_set(x_273, 2, x_260);
lean_closure_set(x_273, 3, x_3);
lean_closure_set(x_273, 4, x_4);
lean_closure_set(x_273, 5, x_5);
lean_closure_set(x_273, 6, x_6);
lean_closure_set(x_273, 7, x_215);
lean_closure_set(x_273, 8, x_272);
lean_closure_set(x_273, 9, x_246);
lean_closure_set(x_273, 10, x_262);
lean_closure_set(x_273, 11, x_269);
lean_closure_set(x_273, 12, x_270);
x_274 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_274, 0, x_271);
lean_closure_set(x_274, 1, x_273);
x_275 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_260, x_274, x_12, x_13, x_14, x_15, x_266);
return x_275;
}
else
{
uint8_t x_276; 
lean_dec(x_254);
lean_dec(x_246);
lean_dec(x_231);
lean_dec(x_215);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_276 = !lean_is_exclusive(x_256);
if (x_276 == 0)
{
return x_256;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_256, 0);
x_278 = lean_ctor_get(x_256, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_256);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
else
{
uint8_t x_280; 
lean_dec(x_246);
lean_dec(x_231);
lean_dec(x_215);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_280 = !lean_is_exclusive(x_251);
if (x_280 == 0)
{
return x_251;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_251, 0);
x_282 = lean_ctor_get(x_251, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_251);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
return x_283;
}
}
}
else
{
uint8_t x_284; 
lean_dec(x_231);
lean_dec(x_215);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_284 = !lean_is_exclusive(x_243);
if (x_284 == 0)
{
return x_243;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_285 = lean_ctor_get(x_243, 0);
x_286 = lean_ctor_get(x_243, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_243);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
return x_287;
}
}
}
}
else
{
uint8_t x_302; 
lean_dec(x_231);
lean_dec(x_221);
lean_dec(x_215);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_302 = !lean_is_exclusive(x_233);
if (x_302 == 0)
{
return x_233;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_233, 0);
x_304 = lean_ctor_get(x_233, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_233);
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
lean_dec(x_221);
lean_dec(x_215);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_306 = !lean_is_exclusive(x_230);
if (x_306 == 0)
{
return x_230;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_230, 0);
x_308 = lean_ctor_get(x_230, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_230);
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
lean_dec(x_215);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
x_310 = !lean_is_exclusive(x_216);
if (x_310 == 0)
{
return x_216;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_216, 0);
x_312 = lean_ctor_get(x_216, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_216);
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
x_315 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_314, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
lean_dec(x_315);
x_317 = lean_st_ref_get(x_13, x_316);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_320 = lean_ctor_get(x_318, 0);
lean_inc(x_320);
lean_dec(x_318);
x_321 = lean_ctor_get(x_6, 6);
lean_inc(x_321);
x_322 = l_List_redLength___main___rarg(x_321);
x_323 = lean_mk_empty_array_with_capacity(x_322);
lean_dec(x_322);
lean_inc(x_321);
x_324 = l_List_toArrayAux___main___rarg(x_321, x_323);
x_325 = x_324;
x_326 = lean_unsigned_to_nat(0u);
lean_inc(x_320);
lean_inc(x_5);
lean_inc(x_1);
x_327 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_327, 0, x_1);
lean_closure_set(x_327, 1, x_5);
lean_closure_set(x_327, 2, x_8);
lean_closure_set(x_327, 3, x_10);
lean_closure_set(x_327, 4, x_320);
lean_closure_set(x_327, 5, x_321);
lean_closure_set(x_327, 6, x_326);
lean_closure_set(x_327, 7, x_325);
x_328 = x_327;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_329 = lean_apply_5(x_328, x_12, x_13, x_14, x_15, x_319);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec(x_329);
lean_inc(x_1);
x_332 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_331);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_335 == 0)
{
lean_object* x_388; uint8_t x_389; 
x_388 = l_Lean_MetavarContext_exprDependsOn(x_320, x_333, x_2);
x_389 = lean_unbox(x_388);
lean_dec(x_388);
if (x_389 == 0)
{
x_336 = x_334;
goto block_387;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; 
lean_dec(x_330);
lean_dec(x_314);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_390 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_390, 0, x_3);
x_391 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_392 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_390);
x_393 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_394 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_393);
x_395 = lean_box(0);
x_396 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_394, x_395, x_12, x_13, x_14, x_15, x_334);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_397 = !lean_is_exclusive(x_396);
if (x_397 == 0)
{
return x_396;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_396, 0);
x_399 = lean_ctor_get(x_396, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_396);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
}
else
{
lean_dec(x_333);
lean_dec(x_320);
x_336 = x_334;
goto block_387;
}
block_387:
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; lean_object* x_342; 
lean_inc(x_330);
x_337 = x_330;
x_338 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(x_326, x_337);
x_339 = x_338;
x_340 = lean_array_push(x_339, x_2);
x_341 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_342 = l_Lean_Meta_revert(x_1, x_340, x_341, x_12, x_13, x_14, x_15, x_336);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; lean_object* x_350; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_ctor_get(x_343, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_343, 1);
lean_inc(x_346);
lean_dec(x_343);
x_347 = lean_array_get_size(x_330);
x_348 = lean_box(0);
x_349 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_350 = l_Lean_Meta_introN(x_346, x_347, x_348, x_349, x_12, x_13, x_14, x_15, x_344);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_353 = lean_ctor_get(x_351, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_351, 1);
lean_inc(x_354);
lean_dec(x_351);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_355 = l_Lean_Meta_intro1(x_354, x_349, x_12, x_13, x_14, x_15, x_352);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_358 = lean_ctor_get(x_356, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_356, 1);
lean_inc(x_359);
lean_dec(x_356);
x_360 = lean_box(0);
x_361 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_330, x_353, x_330, x_326, x_360);
lean_dec(x_330);
lean_inc(x_359);
x_362 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_362, 0, x_359);
x_363 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_364 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_363, x_362, x_12, x_13, x_14, x_15, x_357);
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
lean_dec(x_364);
x_366 = x_353;
x_367 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_326, x_366);
x_368 = x_367;
lean_inc(x_358);
x_369 = l_Lean_mkFVar(x_358);
lean_inc(x_359);
x_370 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_370, 0, x_359);
x_371 = lean_box(x_335);
lean_inc(x_359);
x_372 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_372, 0, x_358);
lean_closure_set(x_372, 1, x_7);
lean_closure_set(x_372, 2, x_359);
lean_closure_set(x_372, 3, x_3);
lean_closure_set(x_372, 4, x_4);
lean_closure_set(x_372, 5, x_5);
lean_closure_set(x_372, 6, x_6);
lean_closure_set(x_372, 7, x_314);
lean_closure_set(x_372, 8, x_371);
lean_closure_set(x_372, 9, x_345);
lean_closure_set(x_372, 10, x_361);
lean_closure_set(x_372, 11, x_368);
lean_closure_set(x_372, 12, x_369);
x_373 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_373, 0, x_370);
lean_closure_set(x_373, 1, x_372);
x_374 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_359, x_373, x_12, x_13, x_14, x_15, x_365);
return x_374;
}
else
{
uint8_t x_375; 
lean_dec(x_353);
lean_dec(x_345);
lean_dec(x_330);
lean_dec(x_314);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_375 = !lean_is_exclusive(x_355);
if (x_375 == 0)
{
return x_355;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_355, 0);
x_377 = lean_ctor_get(x_355, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_355);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
}
else
{
uint8_t x_379; 
lean_dec(x_345);
lean_dec(x_330);
lean_dec(x_314);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_379 = !lean_is_exclusive(x_350);
if (x_379 == 0)
{
return x_350;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_350, 0);
x_381 = lean_ctor_get(x_350, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_350);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
else
{
uint8_t x_383; 
lean_dec(x_330);
lean_dec(x_314);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_383 = !lean_is_exclusive(x_342);
if (x_383 == 0)
{
return x_342;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_384 = lean_ctor_get(x_342, 0);
x_385 = lean_ctor_get(x_342, 1);
lean_inc(x_385);
lean_inc(x_384);
lean_dec(x_342);
x_386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set(x_386, 1, x_385);
return x_386;
}
}
}
}
else
{
uint8_t x_401; 
lean_dec(x_330);
lean_dec(x_320);
lean_dec(x_314);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_401 = !lean_is_exclusive(x_332);
if (x_401 == 0)
{
return x_332;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_332, 0);
x_403 = lean_ctor_get(x_332, 1);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_332);
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_403);
return x_404;
}
}
}
else
{
uint8_t x_405; 
lean_dec(x_320);
lean_dec(x_314);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_405 = !lean_is_exclusive(x_329);
if (x_405 == 0)
{
return x_329;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_329, 0);
x_407 = lean_ctor_get(x_329, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_329);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
return x_408;
}
}
}
else
{
uint8_t x_409; 
lean_dec(x_314);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
x_409 = !lean_is_exclusive(x_315);
if (x_409 == 0)
{
return x_315;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_315, 0);
x_411 = lean_ctor_get(x_315, 1);
lean_inc(x_411);
lean_inc(x_410);
lean_dec(x_315);
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
return x_412;
}
}
}
case 4:
{
lean_object* x_413; lean_object* x_414; 
lean_dec(x_11);
lean_dec(x_9);
x_413 = lean_ctor_get(x_6, 5);
lean_inc(x_413);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_414 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_413, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_415 = lean_ctor_get(x_414, 1);
lean_inc(x_415);
lean_dec(x_414);
x_416 = lean_st_ref_get(x_13, x_415);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
x_419 = lean_ctor_get(x_417, 0);
lean_inc(x_419);
lean_dec(x_417);
x_420 = lean_ctor_get(x_6, 6);
lean_inc(x_420);
x_421 = l_List_redLength___main___rarg(x_420);
x_422 = lean_mk_empty_array_with_capacity(x_421);
lean_dec(x_421);
lean_inc(x_420);
x_423 = l_List_toArrayAux___main___rarg(x_420, x_422);
x_424 = x_423;
x_425 = lean_unsigned_to_nat(0u);
lean_inc(x_419);
lean_inc(x_5);
lean_inc(x_1);
x_426 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_426, 0, x_1);
lean_closure_set(x_426, 1, x_5);
lean_closure_set(x_426, 2, x_8);
lean_closure_set(x_426, 3, x_10);
lean_closure_set(x_426, 4, x_419);
lean_closure_set(x_426, 5, x_420);
lean_closure_set(x_426, 6, x_425);
lean_closure_set(x_426, 7, x_424);
x_427 = x_426;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_428 = lean_apply_5(x_427, x_12, x_13, x_14, x_15, x_418);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
lean_dec(x_428);
lean_inc(x_1);
x_431 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_430);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
x_434 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_434 == 0)
{
lean_object* x_487; uint8_t x_488; 
x_487 = l_Lean_MetavarContext_exprDependsOn(x_419, x_432, x_2);
x_488 = lean_unbox(x_487);
lean_dec(x_487);
if (x_488 == 0)
{
x_435 = x_433;
goto block_486;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; 
lean_dec(x_429);
lean_dec(x_413);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_489 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_489, 0, x_3);
x_490 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_491 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_491, 0, x_490);
lean_ctor_set(x_491, 1, x_489);
x_492 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_493 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_492);
x_494 = lean_box(0);
x_495 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_493, x_494, x_12, x_13, x_14, x_15, x_433);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
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
x_499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_499, 0, x_497);
lean_ctor_set(x_499, 1, x_498);
return x_499;
}
}
}
else
{
lean_dec(x_432);
lean_dec(x_419);
x_435 = x_433;
goto block_486;
}
block_486:
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; 
lean_inc(x_429);
x_436 = x_429;
x_437 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(x_425, x_436);
x_438 = x_437;
x_439 = lean_array_push(x_438, x_2);
x_440 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_441 = l_Lean_Meta_revert(x_1, x_439, x_440, x_12, x_13, x_14, x_15, x_435);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; uint8_t x_448; lean_object* x_449; 
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_441, 1);
lean_inc(x_443);
lean_dec(x_441);
x_444 = lean_ctor_get(x_442, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_442, 1);
lean_inc(x_445);
lean_dec(x_442);
x_446 = lean_array_get_size(x_429);
x_447 = lean_box(0);
x_448 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_449 = l_Lean_Meta_introN(x_445, x_446, x_447, x_448, x_12, x_13, x_14, x_15, x_443);
if (lean_obj_tag(x_449) == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_449, 1);
lean_inc(x_451);
lean_dec(x_449);
x_452 = lean_ctor_get(x_450, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_450, 1);
lean_inc(x_453);
lean_dec(x_450);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_454 = l_Lean_Meta_intro1(x_453, x_448, x_12, x_13, x_14, x_15, x_451);
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_454, 1);
lean_inc(x_456);
lean_dec(x_454);
x_457 = lean_ctor_get(x_455, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_455, 1);
lean_inc(x_458);
lean_dec(x_455);
x_459 = lean_box(0);
x_460 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_429, x_452, x_429, x_425, x_459);
lean_dec(x_429);
lean_inc(x_458);
x_461 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_461, 0, x_458);
x_462 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_463 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_462, x_461, x_12, x_13, x_14, x_15, x_456);
x_464 = lean_ctor_get(x_463, 1);
lean_inc(x_464);
lean_dec(x_463);
x_465 = x_452;
x_466 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_425, x_465);
x_467 = x_466;
lean_inc(x_457);
x_468 = l_Lean_mkFVar(x_457);
lean_inc(x_458);
x_469 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_469, 0, x_458);
x_470 = lean_box(x_434);
lean_inc(x_458);
x_471 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_471, 0, x_457);
lean_closure_set(x_471, 1, x_7);
lean_closure_set(x_471, 2, x_458);
lean_closure_set(x_471, 3, x_3);
lean_closure_set(x_471, 4, x_4);
lean_closure_set(x_471, 5, x_5);
lean_closure_set(x_471, 6, x_6);
lean_closure_set(x_471, 7, x_413);
lean_closure_set(x_471, 8, x_470);
lean_closure_set(x_471, 9, x_444);
lean_closure_set(x_471, 10, x_460);
lean_closure_set(x_471, 11, x_467);
lean_closure_set(x_471, 12, x_468);
x_472 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_472, 0, x_469);
lean_closure_set(x_472, 1, x_471);
x_473 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_458, x_472, x_12, x_13, x_14, x_15, x_464);
return x_473;
}
else
{
uint8_t x_474; 
lean_dec(x_452);
lean_dec(x_444);
lean_dec(x_429);
lean_dec(x_413);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_474 = !lean_is_exclusive(x_454);
if (x_474 == 0)
{
return x_454;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_454, 0);
x_476 = lean_ctor_get(x_454, 1);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_454);
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
lean_dec(x_444);
lean_dec(x_429);
lean_dec(x_413);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_478 = !lean_is_exclusive(x_449);
if (x_478 == 0)
{
return x_449;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_449, 0);
x_480 = lean_ctor_get(x_449, 1);
lean_inc(x_480);
lean_inc(x_479);
lean_dec(x_449);
x_481 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_481, 0, x_479);
lean_ctor_set(x_481, 1, x_480);
return x_481;
}
}
}
else
{
uint8_t x_482; 
lean_dec(x_429);
lean_dec(x_413);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_482 = !lean_is_exclusive(x_441);
if (x_482 == 0)
{
return x_441;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_483 = lean_ctor_get(x_441, 0);
x_484 = lean_ctor_get(x_441, 1);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_441);
x_485 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_484);
return x_485;
}
}
}
}
else
{
uint8_t x_500; 
lean_dec(x_429);
lean_dec(x_419);
lean_dec(x_413);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_500 = !lean_is_exclusive(x_431);
if (x_500 == 0)
{
return x_431;
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_501 = lean_ctor_get(x_431, 0);
x_502 = lean_ctor_get(x_431, 1);
lean_inc(x_502);
lean_inc(x_501);
lean_dec(x_431);
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
lean_dec(x_419);
lean_dec(x_413);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_504 = !lean_is_exclusive(x_428);
if (x_504 == 0)
{
return x_428;
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_505 = lean_ctor_get(x_428, 0);
x_506 = lean_ctor_get(x_428, 1);
lean_inc(x_506);
lean_inc(x_505);
lean_dec(x_428);
x_507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_507, 0, x_505);
lean_ctor_set(x_507, 1, x_506);
return x_507;
}
}
}
else
{
uint8_t x_508; 
lean_dec(x_413);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
x_508 = !lean_is_exclusive(x_414);
if (x_508 == 0)
{
return x_414;
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_509 = lean_ctor_get(x_414, 0);
x_510 = lean_ctor_get(x_414, 1);
lean_inc(x_510);
lean_inc(x_509);
lean_dec(x_414);
x_511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_511, 0, x_509);
lean_ctor_set(x_511, 1, x_510);
return x_511;
}
}
}
case 5:
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_512 = lean_ctor_get(x_9, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_9, 1);
lean_inc(x_513);
lean_dec(x_9);
x_514 = lean_array_set(x_10, x_11, x_513);
x_515 = lean_unsigned_to_nat(1u);
x_516 = lean_nat_sub(x_11, x_515);
lean_dec(x_11);
x_9 = x_512;
x_10 = x_514;
x_11 = x_516;
goto _start;
}
case 6:
{
lean_object* x_518; lean_object* x_519; 
lean_dec(x_11);
lean_dec(x_9);
x_518 = lean_ctor_get(x_6, 5);
lean_inc(x_518);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_519 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_518, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_520 = lean_ctor_get(x_519, 1);
lean_inc(x_520);
lean_dec(x_519);
x_521 = lean_st_ref_get(x_13, x_520);
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 1);
lean_inc(x_523);
lean_dec(x_521);
x_524 = lean_ctor_get(x_522, 0);
lean_inc(x_524);
lean_dec(x_522);
x_525 = lean_ctor_get(x_6, 6);
lean_inc(x_525);
x_526 = l_List_redLength___main___rarg(x_525);
x_527 = lean_mk_empty_array_with_capacity(x_526);
lean_dec(x_526);
lean_inc(x_525);
x_528 = l_List_toArrayAux___main___rarg(x_525, x_527);
x_529 = x_528;
x_530 = lean_unsigned_to_nat(0u);
lean_inc(x_524);
lean_inc(x_5);
lean_inc(x_1);
x_531 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_531, 0, x_1);
lean_closure_set(x_531, 1, x_5);
lean_closure_set(x_531, 2, x_8);
lean_closure_set(x_531, 3, x_10);
lean_closure_set(x_531, 4, x_524);
lean_closure_set(x_531, 5, x_525);
lean_closure_set(x_531, 6, x_530);
lean_closure_set(x_531, 7, x_529);
x_532 = x_531;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_533 = lean_apply_5(x_532, x_12, x_13, x_14, x_15, x_523);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
lean_dec(x_533);
lean_inc(x_1);
x_536 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_535);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; 
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
lean_dec(x_536);
x_539 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_539 == 0)
{
lean_object* x_592; uint8_t x_593; 
x_592 = l_Lean_MetavarContext_exprDependsOn(x_524, x_537, x_2);
x_593 = lean_unbox(x_592);
lean_dec(x_592);
if (x_593 == 0)
{
x_540 = x_538;
goto block_591;
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; uint8_t x_601; 
lean_dec(x_534);
lean_dec(x_518);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_594 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_594, 0, x_3);
x_595 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_596 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_596, 0, x_595);
lean_ctor_set(x_596, 1, x_594);
x_597 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_598 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_598, 0, x_596);
lean_ctor_set(x_598, 1, x_597);
x_599 = lean_box(0);
x_600 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_598, x_599, x_12, x_13, x_14, x_15, x_538);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_601 = !lean_is_exclusive(x_600);
if (x_601 == 0)
{
return x_600;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_600, 0);
x_603 = lean_ctor_get(x_600, 1);
lean_inc(x_603);
lean_inc(x_602);
lean_dec(x_600);
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_603);
return x_604;
}
}
}
else
{
lean_dec(x_537);
lean_dec(x_524);
x_540 = x_538;
goto block_591;
}
block_591:
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; uint8_t x_545; lean_object* x_546; 
lean_inc(x_534);
x_541 = x_534;
x_542 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(x_530, x_541);
x_543 = x_542;
x_544 = lean_array_push(x_543, x_2);
x_545 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_546 = l_Lean_Meta_revert(x_1, x_544, x_545, x_12, x_13, x_14, x_15, x_540);
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
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_554 = l_Lean_Meta_introN(x_550, x_551, x_552, x_553, x_12, x_13, x_14, x_15, x_548);
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
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_559 = l_Lean_Meta_intro1(x_558, x_553, x_12, x_13, x_14, x_15, x_556);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
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
x_565 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_534, x_557, x_534, x_530, x_564);
lean_dec(x_534);
lean_inc(x_563);
x_566 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_566, 0, x_563);
x_567 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_568 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_567, x_566, x_12, x_13, x_14, x_15, x_561);
x_569 = lean_ctor_get(x_568, 1);
lean_inc(x_569);
lean_dec(x_568);
x_570 = x_557;
x_571 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_530, x_570);
x_572 = x_571;
lean_inc(x_562);
x_573 = l_Lean_mkFVar(x_562);
lean_inc(x_563);
x_574 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_574, 0, x_563);
x_575 = lean_box(x_539);
lean_inc(x_563);
x_576 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_576, 0, x_562);
lean_closure_set(x_576, 1, x_7);
lean_closure_set(x_576, 2, x_563);
lean_closure_set(x_576, 3, x_3);
lean_closure_set(x_576, 4, x_4);
lean_closure_set(x_576, 5, x_5);
lean_closure_set(x_576, 6, x_6);
lean_closure_set(x_576, 7, x_518);
lean_closure_set(x_576, 8, x_575);
lean_closure_set(x_576, 9, x_549);
lean_closure_set(x_576, 10, x_565);
lean_closure_set(x_576, 11, x_572);
lean_closure_set(x_576, 12, x_573);
x_577 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_577, 0, x_574);
lean_closure_set(x_577, 1, x_576);
x_578 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_563, x_577, x_12, x_13, x_14, x_15, x_569);
return x_578;
}
else
{
uint8_t x_579; 
lean_dec(x_557);
lean_dec(x_549);
lean_dec(x_534);
lean_dec(x_518);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_579 = !lean_is_exclusive(x_559);
if (x_579 == 0)
{
return x_559;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_580 = lean_ctor_get(x_559, 0);
x_581 = lean_ctor_get(x_559, 1);
lean_inc(x_581);
lean_inc(x_580);
lean_dec(x_559);
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
lean_dec(x_549);
lean_dec(x_534);
lean_dec(x_518);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_583 = !lean_is_exclusive(x_554);
if (x_583 == 0)
{
return x_554;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_554, 0);
x_585 = lean_ctor_get(x_554, 1);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_554);
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
lean_dec(x_534);
lean_dec(x_518);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_587 = !lean_is_exclusive(x_546);
if (x_587 == 0)
{
return x_546;
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_588 = lean_ctor_get(x_546, 0);
x_589 = lean_ctor_get(x_546, 1);
lean_inc(x_589);
lean_inc(x_588);
lean_dec(x_546);
x_590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_590, 0, x_588);
lean_ctor_set(x_590, 1, x_589);
return x_590;
}
}
}
}
else
{
uint8_t x_605; 
lean_dec(x_534);
lean_dec(x_524);
lean_dec(x_518);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_605 = !lean_is_exclusive(x_536);
if (x_605 == 0)
{
return x_536;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_606 = lean_ctor_get(x_536, 0);
x_607 = lean_ctor_get(x_536, 1);
lean_inc(x_607);
lean_inc(x_606);
lean_dec(x_536);
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
lean_dec(x_524);
lean_dec(x_518);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_609 = !lean_is_exclusive(x_533);
if (x_609 == 0)
{
return x_533;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_610 = lean_ctor_get(x_533, 0);
x_611 = lean_ctor_get(x_533, 1);
lean_inc(x_611);
lean_inc(x_610);
lean_dec(x_533);
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
lean_dec(x_518);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
x_613 = !lean_is_exclusive(x_519);
if (x_613 == 0)
{
return x_519;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = lean_ctor_get(x_519, 0);
x_615 = lean_ctor_get(x_519, 1);
lean_inc(x_615);
lean_inc(x_614);
lean_dec(x_519);
x_616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_616, 0, x_614);
lean_ctor_set(x_616, 1, x_615);
return x_616;
}
}
}
case 7:
{
lean_object* x_617; lean_object* x_618; 
lean_dec(x_11);
lean_dec(x_9);
x_617 = lean_ctor_get(x_6, 5);
lean_inc(x_617);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_618 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_617, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_619 = lean_ctor_get(x_618, 1);
lean_inc(x_619);
lean_dec(x_618);
x_620 = lean_st_ref_get(x_13, x_619);
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 1);
lean_inc(x_622);
lean_dec(x_620);
x_623 = lean_ctor_get(x_621, 0);
lean_inc(x_623);
lean_dec(x_621);
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
x_630 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_630, 0, x_1);
lean_closure_set(x_630, 1, x_5);
lean_closure_set(x_630, 2, x_8);
lean_closure_set(x_630, 3, x_10);
lean_closure_set(x_630, 4, x_623);
lean_closure_set(x_630, 5, x_624);
lean_closure_set(x_630, 6, x_629);
lean_closure_set(x_630, 7, x_628);
x_631 = x_630;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_632 = lean_apply_5(x_631, x_12, x_13, x_14, x_15, x_622);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_633 = lean_ctor_get(x_632, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_634);
lean_dec(x_632);
lean_inc(x_1);
x_635 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_634);
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
lean_object* x_691; uint8_t x_692; 
x_691 = l_Lean_MetavarContext_exprDependsOn(x_623, x_636, x_2);
x_692 = lean_unbox(x_691);
lean_dec(x_691);
if (x_692 == 0)
{
x_639 = x_637;
goto block_690;
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; uint8_t x_700; 
lean_dec(x_633);
lean_dec(x_617);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_693 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_693, 0, x_3);
x_694 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_695 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_695, 0, x_694);
lean_ctor_set(x_695, 1, x_693);
x_696 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_697 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_697, 0, x_695);
lean_ctor_set(x_697, 1, x_696);
x_698 = lean_box(0);
x_699 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_697, x_698, x_12, x_13, x_14, x_15, x_637);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_700 = !lean_is_exclusive(x_699);
if (x_700 == 0)
{
return x_699;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_701 = lean_ctor_get(x_699, 0);
x_702 = lean_ctor_get(x_699, 1);
lean_inc(x_702);
lean_inc(x_701);
lean_dec(x_699);
x_703 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_703, 0, x_701);
lean_ctor_set(x_703, 1, x_702);
return x_703;
}
}
}
else
{
lean_dec(x_636);
lean_dec(x_623);
x_639 = x_637;
goto block_690;
}
block_690:
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; uint8_t x_644; lean_object* x_645; 
lean_inc(x_633);
x_640 = x_633;
x_641 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(x_629, x_640);
x_642 = x_641;
x_643 = lean_array_push(x_642, x_2);
x_644 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_645 = l_Lean_Meta_revert(x_1, x_643, x_644, x_12, x_13, x_14, x_15, x_639);
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
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_653 = l_Lean_Meta_introN(x_649, x_650, x_651, x_652, x_12, x_13, x_14, x_15, x_647);
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
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_658 = l_Lean_Meta_intro1(x_657, x_652, x_12, x_13, x_14, x_15, x_655);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; 
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
x_664 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_633, x_656, x_633, x_629, x_663);
lean_dec(x_633);
lean_inc(x_662);
x_665 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_665, 0, x_662);
x_666 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_667 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_666, x_665, x_12, x_13, x_14, x_15, x_660);
x_668 = lean_ctor_get(x_667, 1);
lean_inc(x_668);
lean_dec(x_667);
x_669 = x_656;
x_670 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_629, x_669);
x_671 = x_670;
lean_inc(x_661);
x_672 = l_Lean_mkFVar(x_661);
lean_inc(x_662);
x_673 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_673, 0, x_662);
x_674 = lean_box(x_638);
lean_inc(x_662);
x_675 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_675, 0, x_661);
lean_closure_set(x_675, 1, x_7);
lean_closure_set(x_675, 2, x_662);
lean_closure_set(x_675, 3, x_3);
lean_closure_set(x_675, 4, x_4);
lean_closure_set(x_675, 5, x_5);
lean_closure_set(x_675, 6, x_6);
lean_closure_set(x_675, 7, x_617);
lean_closure_set(x_675, 8, x_674);
lean_closure_set(x_675, 9, x_648);
lean_closure_set(x_675, 10, x_664);
lean_closure_set(x_675, 11, x_671);
lean_closure_set(x_675, 12, x_672);
x_676 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_676, 0, x_673);
lean_closure_set(x_676, 1, x_675);
x_677 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_662, x_676, x_12, x_13, x_14, x_15, x_668);
return x_677;
}
else
{
uint8_t x_678; 
lean_dec(x_656);
lean_dec(x_648);
lean_dec(x_633);
lean_dec(x_617);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_678 = !lean_is_exclusive(x_658);
if (x_678 == 0)
{
return x_658;
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_679 = lean_ctor_get(x_658, 0);
x_680 = lean_ctor_get(x_658, 1);
lean_inc(x_680);
lean_inc(x_679);
lean_dec(x_658);
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
lean_dec(x_648);
lean_dec(x_633);
lean_dec(x_617);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_682 = !lean_is_exclusive(x_653);
if (x_682 == 0)
{
return x_653;
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_683 = lean_ctor_get(x_653, 0);
x_684 = lean_ctor_get(x_653, 1);
lean_inc(x_684);
lean_inc(x_683);
lean_dec(x_653);
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
lean_dec(x_633);
lean_dec(x_617);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_686 = !lean_is_exclusive(x_645);
if (x_686 == 0)
{
return x_645;
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_687 = lean_ctor_get(x_645, 0);
x_688 = lean_ctor_get(x_645, 1);
lean_inc(x_688);
lean_inc(x_687);
lean_dec(x_645);
x_689 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_689, 0, x_687);
lean_ctor_set(x_689, 1, x_688);
return x_689;
}
}
}
}
else
{
uint8_t x_704; 
lean_dec(x_633);
lean_dec(x_623);
lean_dec(x_617);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_704 = !lean_is_exclusive(x_635);
if (x_704 == 0)
{
return x_635;
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_705 = lean_ctor_get(x_635, 0);
x_706 = lean_ctor_get(x_635, 1);
lean_inc(x_706);
lean_inc(x_705);
lean_dec(x_635);
x_707 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_707, 0, x_705);
lean_ctor_set(x_707, 1, x_706);
return x_707;
}
}
}
else
{
uint8_t x_708; 
lean_dec(x_623);
lean_dec(x_617);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_708 = !lean_is_exclusive(x_632);
if (x_708 == 0)
{
return x_632;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = lean_ctor_get(x_632, 0);
x_710 = lean_ctor_get(x_632, 1);
lean_inc(x_710);
lean_inc(x_709);
lean_dec(x_632);
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
lean_dec(x_617);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
x_712 = !lean_is_exclusive(x_618);
if (x_712 == 0)
{
return x_618;
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_713 = lean_ctor_get(x_618, 0);
x_714 = lean_ctor_get(x_618, 1);
lean_inc(x_714);
lean_inc(x_713);
lean_dec(x_618);
x_715 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_715, 0, x_713);
lean_ctor_set(x_715, 1, x_714);
return x_715;
}
}
}
case 8:
{
lean_object* x_716; lean_object* x_717; 
lean_dec(x_11);
lean_dec(x_9);
x_716 = lean_ctor_get(x_6, 5);
lean_inc(x_716);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_717 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_716, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_718 = lean_ctor_get(x_717, 1);
lean_inc(x_718);
lean_dec(x_717);
x_719 = lean_st_ref_get(x_13, x_718);
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_719, 1);
lean_inc(x_721);
lean_dec(x_719);
x_722 = lean_ctor_get(x_720, 0);
lean_inc(x_722);
lean_dec(x_720);
x_723 = lean_ctor_get(x_6, 6);
lean_inc(x_723);
x_724 = l_List_redLength___main___rarg(x_723);
x_725 = lean_mk_empty_array_with_capacity(x_724);
lean_dec(x_724);
lean_inc(x_723);
x_726 = l_List_toArrayAux___main___rarg(x_723, x_725);
x_727 = x_726;
x_728 = lean_unsigned_to_nat(0u);
lean_inc(x_722);
lean_inc(x_5);
lean_inc(x_1);
x_729 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_729, 0, x_1);
lean_closure_set(x_729, 1, x_5);
lean_closure_set(x_729, 2, x_8);
lean_closure_set(x_729, 3, x_10);
lean_closure_set(x_729, 4, x_722);
lean_closure_set(x_729, 5, x_723);
lean_closure_set(x_729, 6, x_728);
lean_closure_set(x_729, 7, x_727);
x_730 = x_729;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_731 = lean_apply_5(x_730, x_12, x_13, x_14, x_15, x_721);
if (lean_obj_tag(x_731) == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_732 = lean_ctor_get(x_731, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_731, 1);
lean_inc(x_733);
lean_dec(x_731);
lean_inc(x_1);
x_734 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_733);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; lean_object* x_736; uint8_t x_737; lean_object* x_738; 
x_735 = lean_ctor_get(x_734, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_734, 1);
lean_inc(x_736);
lean_dec(x_734);
x_737 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_737 == 0)
{
lean_object* x_790; uint8_t x_791; 
x_790 = l_Lean_MetavarContext_exprDependsOn(x_722, x_735, x_2);
x_791 = lean_unbox(x_790);
lean_dec(x_790);
if (x_791 == 0)
{
x_738 = x_736;
goto block_789;
}
else
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; uint8_t x_799; 
lean_dec(x_732);
lean_dec(x_716);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_792 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_792, 0, x_3);
x_793 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_794 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_794, 0, x_793);
lean_ctor_set(x_794, 1, x_792);
x_795 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_796 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_796, 0, x_794);
lean_ctor_set(x_796, 1, x_795);
x_797 = lean_box(0);
x_798 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_796, x_797, x_12, x_13, x_14, x_15, x_736);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_799 = !lean_is_exclusive(x_798);
if (x_799 == 0)
{
return x_798;
}
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; 
x_800 = lean_ctor_get(x_798, 0);
x_801 = lean_ctor_get(x_798, 1);
lean_inc(x_801);
lean_inc(x_800);
lean_dec(x_798);
x_802 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_802, 0, x_800);
lean_ctor_set(x_802, 1, x_801);
return x_802;
}
}
}
else
{
lean_dec(x_735);
lean_dec(x_722);
x_738 = x_736;
goto block_789;
}
block_789:
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; uint8_t x_743; lean_object* x_744; 
lean_inc(x_732);
x_739 = x_732;
x_740 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(x_728, x_739);
x_741 = x_740;
x_742 = lean_array_push(x_741, x_2);
x_743 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_744 = l_Lean_Meta_revert(x_1, x_742, x_743, x_12, x_13, x_14, x_15, x_738);
if (lean_obj_tag(x_744) == 0)
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; lean_object* x_752; 
x_745 = lean_ctor_get(x_744, 0);
lean_inc(x_745);
x_746 = lean_ctor_get(x_744, 1);
lean_inc(x_746);
lean_dec(x_744);
x_747 = lean_ctor_get(x_745, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_745, 1);
lean_inc(x_748);
lean_dec(x_745);
x_749 = lean_array_get_size(x_732);
x_750 = lean_box(0);
x_751 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_752 = l_Lean_Meta_introN(x_748, x_749, x_750, x_751, x_12, x_13, x_14, x_15, x_746);
if (lean_obj_tag(x_752) == 0)
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; 
x_753 = lean_ctor_get(x_752, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_752, 1);
lean_inc(x_754);
lean_dec(x_752);
x_755 = lean_ctor_get(x_753, 0);
lean_inc(x_755);
x_756 = lean_ctor_get(x_753, 1);
lean_inc(x_756);
lean_dec(x_753);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_757 = l_Lean_Meta_intro1(x_756, x_751, x_12, x_13, x_14, x_15, x_754);
if (lean_obj_tag(x_757) == 0)
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_758 = lean_ctor_get(x_757, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_757, 1);
lean_inc(x_759);
lean_dec(x_757);
x_760 = lean_ctor_get(x_758, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_758, 1);
lean_inc(x_761);
lean_dec(x_758);
x_762 = lean_box(0);
x_763 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_732, x_755, x_732, x_728, x_762);
lean_dec(x_732);
lean_inc(x_761);
x_764 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_764, 0, x_761);
x_765 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_766 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_765, x_764, x_12, x_13, x_14, x_15, x_759);
x_767 = lean_ctor_get(x_766, 1);
lean_inc(x_767);
lean_dec(x_766);
x_768 = x_755;
x_769 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_728, x_768);
x_770 = x_769;
lean_inc(x_760);
x_771 = l_Lean_mkFVar(x_760);
lean_inc(x_761);
x_772 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_772, 0, x_761);
x_773 = lean_box(x_737);
lean_inc(x_761);
x_774 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_774, 0, x_760);
lean_closure_set(x_774, 1, x_7);
lean_closure_set(x_774, 2, x_761);
lean_closure_set(x_774, 3, x_3);
lean_closure_set(x_774, 4, x_4);
lean_closure_set(x_774, 5, x_5);
lean_closure_set(x_774, 6, x_6);
lean_closure_set(x_774, 7, x_716);
lean_closure_set(x_774, 8, x_773);
lean_closure_set(x_774, 9, x_747);
lean_closure_set(x_774, 10, x_763);
lean_closure_set(x_774, 11, x_770);
lean_closure_set(x_774, 12, x_771);
x_775 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_775, 0, x_772);
lean_closure_set(x_775, 1, x_774);
x_776 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_761, x_775, x_12, x_13, x_14, x_15, x_767);
return x_776;
}
else
{
uint8_t x_777; 
lean_dec(x_755);
lean_dec(x_747);
lean_dec(x_732);
lean_dec(x_716);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_777 = !lean_is_exclusive(x_757);
if (x_777 == 0)
{
return x_757;
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_778 = lean_ctor_get(x_757, 0);
x_779 = lean_ctor_get(x_757, 1);
lean_inc(x_779);
lean_inc(x_778);
lean_dec(x_757);
x_780 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_780, 0, x_778);
lean_ctor_set(x_780, 1, x_779);
return x_780;
}
}
}
else
{
uint8_t x_781; 
lean_dec(x_747);
lean_dec(x_732);
lean_dec(x_716);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_781 = !lean_is_exclusive(x_752);
if (x_781 == 0)
{
return x_752;
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; 
x_782 = lean_ctor_get(x_752, 0);
x_783 = lean_ctor_get(x_752, 1);
lean_inc(x_783);
lean_inc(x_782);
lean_dec(x_752);
x_784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_784, 0, x_782);
lean_ctor_set(x_784, 1, x_783);
return x_784;
}
}
}
else
{
uint8_t x_785; 
lean_dec(x_732);
lean_dec(x_716);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_785 = !lean_is_exclusive(x_744);
if (x_785 == 0)
{
return x_744;
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_786 = lean_ctor_get(x_744, 0);
x_787 = lean_ctor_get(x_744, 1);
lean_inc(x_787);
lean_inc(x_786);
lean_dec(x_744);
x_788 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_788, 0, x_786);
lean_ctor_set(x_788, 1, x_787);
return x_788;
}
}
}
}
else
{
uint8_t x_803; 
lean_dec(x_732);
lean_dec(x_722);
lean_dec(x_716);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_803 = !lean_is_exclusive(x_734);
if (x_803 == 0)
{
return x_734;
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_804 = lean_ctor_get(x_734, 0);
x_805 = lean_ctor_get(x_734, 1);
lean_inc(x_805);
lean_inc(x_804);
lean_dec(x_734);
x_806 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_806, 0, x_804);
lean_ctor_set(x_806, 1, x_805);
return x_806;
}
}
}
else
{
uint8_t x_807; 
lean_dec(x_722);
lean_dec(x_716);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_807 = !lean_is_exclusive(x_731);
if (x_807 == 0)
{
return x_731;
}
else
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_808 = lean_ctor_get(x_731, 0);
x_809 = lean_ctor_get(x_731, 1);
lean_inc(x_809);
lean_inc(x_808);
lean_dec(x_731);
x_810 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_810, 0, x_808);
lean_ctor_set(x_810, 1, x_809);
return x_810;
}
}
}
else
{
uint8_t x_811; 
lean_dec(x_716);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
x_811 = !lean_is_exclusive(x_717);
if (x_811 == 0)
{
return x_717;
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_812 = lean_ctor_get(x_717, 0);
x_813 = lean_ctor_get(x_717, 1);
lean_inc(x_813);
lean_inc(x_812);
lean_dec(x_717);
x_814 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_814, 0, x_812);
lean_ctor_set(x_814, 1, x_813);
return x_814;
}
}
}
case 9:
{
lean_object* x_815; lean_object* x_816; 
lean_dec(x_11);
lean_dec(x_9);
x_815 = lean_ctor_get(x_6, 5);
lean_inc(x_815);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_816 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_815, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_816) == 0)
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; 
x_817 = lean_ctor_get(x_816, 1);
lean_inc(x_817);
lean_dec(x_816);
x_818 = lean_st_ref_get(x_13, x_817);
x_819 = lean_ctor_get(x_818, 0);
lean_inc(x_819);
x_820 = lean_ctor_get(x_818, 1);
lean_inc(x_820);
lean_dec(x_818);
x_821 = lean_ctor_get(x_819, 0);
lean_inc(x_821);
lean_dec(x_819);
x_822 = lean_ctor_get(x_6, 6);
lean_inc(x_822);
x_823 = l_List_redLength___main___rarg(x_822);
x_824 = lean_mk_empty_array_with_capacity(x_823);
lean_dec(x_823);
lean_inc(x_822);
x_825 = l_List_toArrayAux___main___rarg(x_822, x_824);
x_826 = x_825;
x_827 = lean_unsigned_to_nat(0u);
lean_inc(x_821);
lean_inc(x_5);
lean_inc(x_1);
x_828 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_828, 0, x_1);
lean_closure_set(x_828, 1, x_5);
lean_closure_set(x_828, 2, x_8);
lean_closure_set(x_828, 3, x_10);
lean_closure_set(x_828, 4, x_821);
lean_closure_set(x_828, 5, x_822);
lean_closure_set(x_828, 6, x_827);
lean_closure_set(x_828, 7, x_826);
x_829 = x_828;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_830 = lean_apply_5(x_829, x_12, x_13, x_14, x_15, x_820);
if (lean_obj_tag(x_830) == 0)
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_831 = lean_ctor_get(x_830, 0);
lean_inc(x_831);
x_832 = lean_ctor_get(x_830, 1);
lean_inc(x_832);
lean_dec(x_830);
lean_inc(x_1);
x_833 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_832);
if (lean_obj_tag(x_833) == 0)
{
lean_object* x_834; lean_object* x_835; uint8_t x_836; lean_object* x_837; 
x_834 = lean_ctor_get(x_833, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_833, 1);
lean_inc(x_835);
lean_dec(x_833);
x_836 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_836 == 0)
{
lean_object* x_889; uint8_t x_890; 
x_889 = l_Lean_MetavarContext_exprDependsOn(x_821, x_834, x_2);
x_890 = lean_unbox(x_889);
lean_dec(x_889);
if (x_890 == 0)
{
x_837 = x_835;
goto block_888;
}
else
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; uint8_t x_898; 
lean_dec(x_831);
lean_dec(x_815);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_891 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_891, 0, x_3);
x_892 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_893 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_893, 0, x_892);
lean_ctor_set(x_893, 1, x_891);
x_894 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_895 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_895, 0, x_893);
lean_ctor_set(x_895, 1, x_894);
x_896 = lean_box(0);
x_897 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_895, x_896, x_12, x_13, x_14, x_15, x_835);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_898 = !lean_is_exclusive(x_897);
if (x_898 == 0)
{
return x_897;
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; 
x_899 = lean_ctor_get(x_897, 0);
x_900 = lean_ctor_get(x_897, 1);
lean_inc(x_900);
lean_inc(x_899);
lean_dec(x_897);
x_901 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_901, 0, x_899);
lean_ctor_set(x_901, 1, x_900);
return x_901;
}
}
}
else
{
lean_dec(x_834);
lean_dec(x_821);
x_837 = x_835;
goto block_888;
}
block_888:
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; uint8_t x_842; lean_object* x_843; 
lean_inc(x_831);
x_838 = x_831;
x_839 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(x_827, x_838);
x_840 = x_839;
x_841 = lean_array_push(x_840, x_2);
x_842 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_843 = l_Lean_Meta_revert(x_1, x_841, x_842, x_12, x_13, x_14, x_15, x_837);
if (lean_obj_tag(x_843) == 0)
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; uint8_t x_850; lean_object* x_851; 
x_844 = lean_ctor_get(x_843, 0);
lean_inc(x_844);
x_845 = lean_ctor_get(x_843, 1);
lean_inc(x_845);
lean_dec(x_843);
x_846 = lean_ctor_get(x_844, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_844, 1);
lean_inc(x_847);
lean_dec(x_844);
x_848 = lean_array_get_size(x_831);
x_849 = lean_box(0);
x_850 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_851 = l_Lean_Meta_introN(x_847, x_848, x_849, x_850, x_12, x_13, x_14, x_15, x_845);
if (lean_obj_tag(x_851) == 0)
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
x_852 = lean_ctor_get(x_851, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_851, 1);
lean_inc(x_853);
lean_dec(x_851);
x_854 = lean_ctor_get(x_852, 0);
lean_inc(x_854);
x_855 = lean_ctor_get(x_852, 1);
lean_inc(x_855);
lean_dec(x_852);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_856 = l_Lean_Meta_intro1(x_855, x_850, x_12, x_13, x_14, x_15, x_853);
if (lean_obj_tag(x_856) == 0)
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_857 = lean_ctor_get(x_856, 0);
lean_inc(x_857);
x_858 = lean_ctor_get(x_856, 1);
lean_inc(x_858);
lean_dec(x_856);
x_859 = lean_ctor_get(x_857, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_857, 1);
lean_inc(x_860);
lean_dec(x_857);
x_861 = lean_box(0);
x_862 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_831, x_854, x_831, x_827, x_861);
lean_dec(x_831);
lean_inc(x_860);
x_863 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_863, 0, x_860);
x_864 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_865 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_864, x_863, x_12, x_13, x_14, x_15, x_858);
x_866 = lean_ctor_get(x_865, 1);
lean_inc(x_866);
lean_dec(x_865);
x_867 = x_854;
x_868 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_827, x_867);
x_869 = x_868;
lean_inc(x_859);
x_870 = l_Lean_mkFVar(x_859);
lean_inc(x_860);
x_871 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_871, 0, x_860);
x_872 = lean_box(x_836);
lean_inc(x_860);
x_873 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_873, 0, x_859);
lean_closure_set(x_873, 1, x_7);
lean_closure_set(x_873, 2, x_860);
lean_closure_set(x_873, 3, x_3);
lean_closure_set(x_873, 4, x_4);
lean_closure_set(x_873, 5, x_5);
lean_closure_set(x_873, 6, x_6);
lean_closure_set(x_873, 7, x_815);
lean_closure_set(x_873, 8, x_872);
lean_closure_set(x_873, 9, x_846);
lean_closure_set(x_873, 10, x_862);
lean_closure_set(x_873, 11, x_869);
lean_closure_set(x_873, 12, x_870);
x_874 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_874, 0, x_871);
lean_closure_set(x_874, 1, x_873);
x_875 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_860, x_874, x_12, x_13, x_14, x_15, x_866);
return x_875;
}
else
{
uint8_t x_876; 
lean_dec(x_854);
lean_dec(x_846);
lean_dec(x_831);
lean_dec(x_815);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_876 = !lean_is_exclusive(x_856);
if (x_876 == 0)
{
return x_856;
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_877 = lean_ctor_get(x_856, 0);
x_878 = lean_ctor_get(x_856, 1);
lean_inc(x_878);
lean_inc(x_877);
lean_dec(x_856);
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
lean_dec(x_846);
lean_dec(x_831);
lean_dec(x_815);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_880 = !lean_is_exclusive(x_851);
if (x_880 == 0)
{
return x_851;
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_881 = lean_ctor_get(x_851, 0);
x_882 = lean_ctor_get(x_851, 1);
lean_inc(x_882);
lean_inc(x_881);
lean_dec(x_851);
x_883 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_883, 0, x_881);
lean_ctor_set(x_883, 1, x_882);
return x_883;
}
}
}
else
{
uint8_t x_884; 
lean_dec(x_831);
lean_dec(x_815);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_884 = !lean_is_exclusive(x_843);
if (x_884 == 0)
{
return x_843;
}
else
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; 
x_885 = lean_ctor_get(x_843, 0);
x_886 = lean_ctor_get(x_843, 1);
lean_inc(x_886);
lean_inc(x_885);
lean_dec(x_843);
x_887 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_887, 0, x_885);
lean_ctor_set(x_887, 1, x_886);
return x_887;
}
}
}
}
else
{
uint8_t x_902; 
lean_dec(x_831);
lean_dec(x_821);
lean_dec(x_815);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_902 = !lean_is_exclusive(x_833);
if (x_902 == 0)
{
return x_833;
}
else
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; 
x_903 = lean_ctor_get(x_833, 0);
x_904 = lean_ctor_get(x_833, 1);
lean_inc(x_904);
lean_inc(x_903);
lean_dec(x_833);
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
lean_dec(x_821);
lean_dec(x_815);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_906 = !lean_is_exclusive(x_830);
if (x_906 == 0)
{
return x_830;
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; 
x_907 = lean_ctor_get(x_830, 0);
x_908 = lean_ctor_get(x_830, 1);
lean_inc(x_908);
lean_inc(x_907);
lean_dec(x_830);
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
lean_dec(x_815);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
x_910 = !lean_is_exclusive(x_816);
if (x_910 == 0)
{
return x_816;
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; 
x_911 = lean_ctor_get(x_816, 0);
x_912 = lean_ctor_get(x_816, 1);
lean_inc(x_912);
lean_inc(x_911);
lean_dec(x_816);
x_913 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_913, 0, x_911);
lean_ctor_set(x_913, 1, x_912);
return x_913;
}
}
}
case 10:
{
lean_object* x_914; lean_object* x_915; 
lean_dec(x_11);
lean_dec(x_9);
x_914 = lean_ctor_get(x_6, 5);
lean_inc(x_914);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_915 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_914, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_915) == 0)
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; 
x_916 = lean_ctor_get(x_915, 1);
lean_inc(x_916);
lean_dec(x_915);
x_917 = lean_st_ref_get(x_13, x_916);
x_918 = lean_ctor_get(x_917, 0);
lean_inc(x_918);
x_919 = lean_ctor_get(x_917, 1);
lean_inc(x_919);
lean_dec(x_917);
x_920 = lean_ctor_get(x_918, 0);
lean_inc(x_920);
lean_dec(x_918);
x_921 = lean_ctor_get(x_6, 6);
lean_inc(x_921);
x_922 = l_List_redLength___main___rarg(x_921);
x_923 = lean_mk_empty_array_with_capacity(x_922);
lean_dec(x_922);
lean_inc(x_921);
x_924 = l_List_toArrayAux___main___rarg(x_921, x_923);
x_925 = x_924;
x_926 = lean_unsigned_to_nat(0u);
lean_inc(x_920);
lean_inc(x_5);
lean_inc(x_1);
x_927 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_927, 0, x_1);
lean_closure_set(x_927, 1, x_5);
lean_closure_set(x_927, 2, x_8);
lean_closure_set(x_927, 3, x_10);
lean_closure_set(x_927, 4, x_920);
lean_closure_set(x_927, 5, x_921);
lean_closure_set(x_927, 6, x_926);
lean_closure_set(x_927, 7, x_925);
x_928 = x_927;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_929 = lean_apply_5(x_928, x_12, x_13, x_14, x_15, x_919);
if (lean_obj_tag(x_929) == 0)
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; 
x_930 = lean_ctor_get(x_929, 0);
lean_inc(x_930);
x_931 = lean_ctor_get(x_929, 1);
lean_inc(x_931);
lean_dec(x_929);
lean_inc(x_1);
x_932 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_931);
if (lean_obj_tag(x_932) == 0)
{
lean_object* x_933; lean_object* x_934; uint8_t x_935; lean_object* x_936; 
x_933 = lean_ctor_get(x_932, 0);
lean_inc(x_933);
x_934 = lean_ctor_get(x_932, 1);
lean_inc(x_934);
lean_dec(x_932);
x_935 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_935 == 0)
{
lean_object* x_988; uint8_t x_989; 
x_988 = l_Lean_MetavarContext_exprDependsOn(x_920, x_933, x_2);
x_989 = lean_unbox(x_988);
lean_dec(x_988);
if (x_989 == 0)
{
x_936 = x_934;
goto block_987;
}
else
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; uint8_t x_997; 
lean_dec(x_930);
lean_dec(x_914);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_990 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_990, 0, x_3);
x_991 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_992 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_992, 0, x_991);
lean_ctor_set(x_992, 1, x_990);
x_993 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_994 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_994, 0, x_992);
lean_ctor_set(x_994, 1, x_993);
x_995 = lean_box(0);
x_996 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_994, x_995, x_12, x_13, x_14, x_15, x_934);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_997 = !lean_is_exclusive(x_996);
if (x_997 == 0)
{
return x_996;
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
x_998 = lean_ctor_get(x_996, 0);
x_999 = lean_ctor_get(x_996, 1);
lean_inc(x_999);
lean_inc(x_998);
lean_dec(x_996);
x_1000 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1000, 0, x_998);
lean_ctor_set(x_1000, 1, x_999);
return x_1000;
}
}
}
else
{
lean_dec(x_933);
lean_dec(x_920);
x_936 = x_934;
goto block_987;
}
block_987:
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; uint8_t x_941; lean_object* x_942; 
lean_inc(x_930);
x_937 = x_930;
x_938 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(x_926, x_937);
x_939 = x_938;
x_940 = lean_array_push(x_939, x_2);
x_941 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_942 = l_Lean_Meta_revert(x_1, x_940, x_941, x_12, x_13, x_14, x_15, x_936);
if (lean_obj_tag(x_942) == 0)
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; uint8_t x_949; lean_object* x_950; 
x_943 = lean_ctor_get(x_942, 0);
lean_inc(x_943);
x_944 = lean_ctor_get(x_942, 1);
lean_inc(x_944);
lean_dec(x_942);
x_945 = lean_ctor_get(x_943, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_943, 1);
lean_inc(x_946);
lean_dec(x_943);
x_947 = lean_array_get_size(x_930);
x_948 = lean_box(0);
x_949 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_950 = l_Lean_Meta_introN(x_946, x_947, x_948, x_949, x_12, x_13, x_14, x_15, x_944);
if (lean_obj_tag(x_950) == 0)
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; 
x_951 = lean_ctor_get(x_950, 0);
lean_inc(x_951);
x_952 = lean_ctor_get(x_950, 1);
lean_inc(x_952);
lean_dec(x_950);
x_953 = lean_ctor_get(x_951, 0);
lean_inc(x_953);
x_954 = lean_ctor_get(x_951, 1);
lean_inc(x_954);
lean_dec(x_951);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_955 = l_Lean_Meta_intro1(x_954, x_949, x_12, x_13, x_14, x_15, x_952);
if (lean_obj_tag(x_955) == 0)
{
lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
x_956 = lean_ctor_get(x_955, 0);
lean_inc(x_956);
x_957 = lean_ctor_get(x_955, 1);
lean_inc(x_957);
lean_dec(x_955);
x_958 = lean_ctor_get(x_956, 0);
lean_inc(x_958);
x_959 = lean_ctor_get(x_956, 1);
lean_inc(x_959);
lean_dec(x_956);
x_960 = lean_box(0);
x_961 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_930, x_953, x_930, x_926, x_960);
lean_dec(x_930);
lean_inc(x_959);
x_962 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_962, 0, x_959);
x_963 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_964 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_963, x_962, x_12, x_13, x_14, x_15, x_957);
x_965 = lean_ctor_get(x_964, 1);
lean_inc(x_965);
lean_dec(x_964);
x_966 = x_953;
x_967 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_926, x_966);
x_968 = x_967;
lean_inc(x_958);
x_969 = l_Lean_mkFVar(x_958);
lean_inc(x_959);
x_970 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_970, 0, x_959);
x_971 = lean_box(x_935);
lean_inc(x_959);
x_972 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_972, 0, x_958);
lean_closure_set(x_972, 1, x_7);
lean_closure_set(x_972, 2, x_959);
lean_closure_set(x_972, 3, x_3);
lean_closure_set(x_972, 4, x_4);
lean_closure_set(x_972, 5, x_5);
lean_closure_set(x_972, 6, x_6);
lean_closure_set(x_972, 7, x_914);
lean_closure_set(x_972, 8, x_971);
lean_closure_set(x_972, 9, x_945);
lean_closure_set(x_972, 10, x_961);
lean_closure_set(x_972, 11, x_968);
lean_closure_set(x_972, 12, x_969);
x_973 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_973, 0, x_970);
lean_closure_set(x_973, 1, x_972);
x_974 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_959, x_973, x_12, x_13, x_14, x_15, x_965);
return x_974;
}
else
{
uint8_t x_975; 
lean_dec(x_953);
lean_dec(x_945);
lean_dec(x_930);
lean_dec(x_914);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_975 = !lean_is_exclusive(x_955);
if (x_975 == 0)
{
return x_955;
}
else
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; 
x_976 = lean_ctor_get(x_955, 0);
x_977 = lean_ctor_get(x_955, 1);
lean_inc(x_977);
lean_inc(x_976);
lean_dec(x_955);
x_978 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_978, 0, x_976);
lean_ctor_set(x_978, 1, x_977);
return x_978;
}
}
}
else
{
uint8_t x_979; 
lean_dec(x_945);
lean_dec(x_930);
lean_dec(x_914);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_979 = !lean_is_exclusive(x_950);
if (x_979 == 0)
{
return x_950;
}
else
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; 
x_980 = lean_ctor_get(x_950, 0);
x_981 = lean_ctor_get(x_950, 1);
lean_inc(x_981);
lean_inc(x_980);
lean_dec(x_950);
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
lean_dec(x_930);
lean_dec(x_914);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_983 = !lean_is_exclusive(x_942);
if (x_983 == 0)
{
return x_942;
}
else
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; 
x_984 = lean_ctor_get(x_942, 0);
x_985 = lean_ctor_get(x_942, 1);
lean_inc(x_985);
lean_inc(x_984);
lean_dec(x_942);
x_986 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_986, 0, x_984);
lean_ctor_set(x_986, 1, x_985);
return x_986;
}
}
}
}
else
{
uint8_t x_1001; 
lean_dec(x_930);
lean_dec(x_920);
lean_dec(x_914);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1001 = !lean_is_exclusive(x_932);
if (x_1001 == 0)
{
return x_932;
}
else
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
x_1002 = lean_ctor_get(x_932, 0);
x_1003 = lean_ctor_get(x_932, 1);
lean_inc(x_1003);
lean_inc(x_1002);
lean_dec(x_932);
x_1004 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1004, 0, x_1002);
lean_ctor_set(x_1004, 1, x_1003);
return x_1004;
}
}
}
else
{
uint8_t x_1005; 
lean_dec(x_920);
lean_dec(x_914);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1005 = !lean_is_exclusive(x_929);
if (x_1005 == 0)
{
return x_929;
}
else
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
x_1006 = lean_ctor_get(x_929, 0);
x_1007 = lean_ctor_get(x_929, 1);
lean_inc(x_1007);
lean_inc(x_1006);
lean_dec(x_929);
x_1008 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1008, 0, x_1006);
lean_ctor_set(x_1008, 1, x_1007);
return x_1008;
}
}
}
else
{
uint8_t x_1009; 
lean_dec(x_914);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
x_1009 = !lean_is_exclusive(x_915);
if (x_1009 == 0)
{
return x_915;
}
else
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1010 = lean_ctor_get(x_915, 0);
x_1011 = lean_ctor_get(x_915, 1);
lean_inc(x_1011);
lean_inc(x_1010);
lean_dec(x_915);
x_1012 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1012, 0, x_1010);
lean_ctor_set(x_1012, 1, x_1011);
return x_1012;
}
}
}
case 11:
{
lean_object* x_1013; lean_object* x_1014; 
lean_dec(x_11);
lean_dec(x_9);
x_1013 = lean_ctor_get(x_6, 5);
lean_inc(x_1013);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_1014 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_1013, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_1014) == 0)
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; 
x_1015 = lean_ctor_get(x_1014, 1);
lean_inc(x_1015);
lean_dec(x_1014);
x_1016 = lean_st_ref_get(x_13, x_1015);
x_1017 = lean_ctor_get(x_1016, 0);
lean_inc(x_1017);
x_1018 = lean_ctor_get(x_1016, 1);
lean_inc(x_1018);
lean_dec(x_1016);
x_1019 = lean_ctor_get(x_1017, 0);
lean_inc(x_1019);
lean_dec(x_1017);
x_1020 = lean_ctor_get(x_6, 6);
lean_inc(x_1020);
x_1021 = l_List_redLength___main___rarg(x_1020);
x_1022 = lean_mk_empty_array_with_capacity(x_1021);
lean_dec(x_1021);
lean_inc(x_1020);
x_1023 = l_List_toArrayAux___main___rarg(x_1020, x_1022);
x_1024 = x_1023;
x_1025 = lean_unsigned_to_nat(0u);
lean_inc(x_1019);
lean_inc(x_5);
lean_inc(x_1);
x_1026 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_1026, 0, x_1);
lean_closure_set(x_1026, 1, x_5);
lean_closure_set(x_1026, 2, x_8);
lean_closure_set(x_1026, 3, x_10);
lean_closure_set(x_1026, 4, x_1019);
lean_closure_set(x_1026, 5, x_1020);
lean_closure_set(x_1026, 6, x_1025);
lean_closure_set(x_1026, 7, x_1024);
x_1027 = x_1026;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_1028 = lean_apply_5(x_1027, x_12, x_13, x_14, x_15, x_1018);
if (lean_obj_tag(x_1028) == 0)
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
x_1029 = lean_ctor_get(x_1028, 0);
lean_inc(x_1029);
x_1030 = lean_ctor_get(x_1028, 1);
lean_inc(x_1030);
lean_dec(x_1028);
lean_inc(x_1);
x_1031 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_1030);
if (lean_obj_tag(x_1031) == 0)
{
lean_object* x_1032; lean_object* x_1033; uint8_t x_1034; lean_object* x_1035; 
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
x_1033 = lean_ctor_get(x_1031, 1);
lean_inc(x_1033);
lean_dec(x_1031);
x_1034 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_1034 == 0)
{
lean_object* x_1087; uint8_t x_1088; 
x_1087 = l_Lean_MetavarContext_exprDependsOn(x_1019, x_1032, x_2);
x_1088 = lean_unbox(x_1087);
lean_dec(x_1087);
if (x_1088 == 0)
{
x_1035 = x_1033;
goto block_1086;
}
else
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; uint8_t x_1096; 
lean_dec(x_1029);
lean_dec(x_1013);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1089 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1089, 0, x_3);
x_1090 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_1091 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1091, 0, x_1090);
lean_ctor_set(x_1091, 1, x_1089);
x_1092 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_1093 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1093, 0, x_1091);
lean_ctor_set(x_1093, 1, x_1092);
x_1094 = lean_box(0);
x_1095 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_1093, x_1094, x_12, x_13, x_14, x_15, x_1033);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_1096 = !lean_is_exclusive(x_1095);
if (x_1096 == 0)
{
return x_1095;
}
else
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; 
x_1097 = lean_ctor_get(x_1095, 0);
x_1098 = lean_ctor_get(x_1095, 1);
lean_inc(x_1098);
lean_inc(x_1097);
lean_dec(x_1095);
x_1099 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1099, 0, x_1097);
lean_ctor_set(x_1099, 1, x_1098);
return x_1099;
}
}
}
else
{
lean_dec(x_1032);
lean_dec(x_1019);
x_1035 = x_1033;
goto block_1086;
}
block_1086:
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; uint8_t x_1040; lean_object* x_1041; 
lean_inc(x_1029);
x_1036 = x_1029;
x_1037 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(x_1025, x_1036);
x_1038 = x_1037;
x_1039 = lean_array_push(x_1038, x_2);
x_1040 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_1041 = l_Lean_Meta_revert(x_1, x_1039, x_1040, x_12, x_13, x_14, x_15, x_1035);
if (lean_obj_tag(x_1041) == 0)
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; uint8_t x_1048; lean_object* x_1049; 
x_1042 = lean_ctor_get(x_1041, 0);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_1041, 1);
lean_inc(x_1043);
lean_dec(x_1041);
x_1044 = lean_ctor_get(x_1042, 0);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_1042, 1);
lean_inc(x_1045);
lean_dec(x_1042);
x_1046 = lean_array_get_size(x_1029);
x_1047 = lean_box(0);
x_1048 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_1049 = l_Lean_Meta_introN(x_1045, x_1046, x_1047, x_1048, x_12, x_13, x_14, x_15, x_1043);
if (lean_obj_tag(x_1049) == 0)
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
x_1050 = lean_ctor_get(x_1049, 0);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1049, 1);
lean_inc(x_1051);
lean_dec(x_1049);
x_1052 = lean_ctor_get(x_1050, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1050, 1);
lean_inc(x_1053);
lean_dec(x_1050);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_1054 = l_Lean_Meta_intro1(x_1053, x_1048, x_12, x_13, x_14, x_15, x_1051);
if (lean_obj_tag(x_1054) == 0)
{
lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; 
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
x_1059 = lean_box(0);
x_1060 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1029, x_1052, x_1029, x_1025, x_1059);
lean_dec(x_1029);
lean_inc(x_1058);
x_1061 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_1061, 0, x_1058);
x_1062 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1063 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_1062, x_1061, x_12, x_13, x_14, x_15, x_1056);
x_1064 = lean_ctor_get(x_1063, 1);
lean_inc(x_1064);
lean_dec(x_1063);
x_1065 = x_1052;
x_1066 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1025, x_1065);
x_1067 = x_1066;
lean_inc(x_1057);
x_1068 = l_Lean_mkFVar(x_1057);
lean_inc(x_1058);
x_1069 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1069, 0, x_1058);
x_1070 = lean_box(x_1034);
lean_inc(x_1058);
x_1071 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_1071, 0, x_1057);
lean_closure_set(x_1071, 1, x_7);
lean_closure_set(x_1071, 2, x_1058);
lean_closure_set(x_1071, 3, x_3);
lean_closure_set(x_1071, 4, x_4);
lean_closure_set(x_1071, 5, x_5);
lean_closure_set(x_1071, 6, x_6);
lean_closure_set(x_1071, 7, x_1013);
lean_closure_set(x_1071, 8, x_1070);
lean_closure_set(x_1071, 9, x_1044);
lean_closure_set(x_1071, 10, x_1060);
lean_closure_set(x_1071, 11, x_1067);
lean_closure_set(x_1071, 12, x_1068);
x_1072 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_1072, 0, x_1069);
lean_closure_set(x_1072, 1, x_1071);
x_1073 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1058, x_1072, x_12, x_13, x_14, x_15, x_1064);
return x_1073;
}
else
{
uint8_t x_1074; 
lean_dec(x_1052);
lean_dec(x_1044);
lean_dec(x_1029);
lean_dec(x_1013);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1074 = !lean_is_exclusive(x_1054);
if (x_1074 == 0)
{
return x_1054;
}
else
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; 
x_1075 = lean_ctor_get(x_1054, 0);
x_1076 = lean_ctor_get(x_1054, 1);
lean_inc(x_1076);
lean_inc(x_1075);
lean_dec(x_1054);
x_1077 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1077, 0, x_1075);
lean_ctor_set(x_1077, 1, x_1076);
return x_1077;
}
}
}
else
{
uint8_t x_1078; 
lean_dec(x_1044);
lean_dec(x_1029);
lean_dec(x_1013);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1078 = !lean_is_exclusive(x_1049);
if (x_1078 == 0)
{
return x_1049;
}
else
{
lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; 
x_1079 = lean_ctor_get(x_1049, 0);
x_1080 = lean_ctor_get(x_1049, 1);
lean_inc(x_1080);
lean_inc(x_1079);
lean_dec(x_1049);
x_1081 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1081, 0, x_1079);
lean_ctor_set(x_1081, 1, x_1080);
return x_1081;
}
}
}
else
{
uint8_t x_1082; 
lean_dec(x_1029);
lean_dec(x_1013);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1082 = !lean_is_exclusive(x_1041);
if (x_1082 == 0)
{
return x_1041;
}
else
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; 
x_1083 = lean_ctor_get(x_1041, 0);
x_1084 = lean_ctor_get(x_1041, 1);
lean_inc(x_1084);
lean_inc(x_1083);
lean_dec(x_1041);
x_1085 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1085, 0, x_1083);
lean_ctor_set(x_1085, 1, x_1084);
return x_1085;
}
}
}
}
else
{
uint8_t x_1100; 
lean_dec(x_1029);
lean_dec(x_1019);
lean_dec(x_1013);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1100 = !lean_is_exclusive(x_1031);
if (x_1100 == 0)
{
return x_1031;
}
else
{
lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
x_1101 = lean_ctor_get(x_1031, 0);
x_1102 = lean_ctor_get(x_1031, 1);
lean_inc(x_1102);
lean_inc(x_1101);
lean_dec(x_1031);
x_1103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1103, 0, x_1101);
lean_ctor_set(x_1103, 1, x_1102);
return x_1103;
}
}
}
else
{
uint8_t x_1104; 
lean_dec(x_1019);
lean_dec(x_1013);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1104 = !lean_is_exclusive(x_1028);
if (x_1104 == 0)
{
return x_1028;
}
else
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; 
x_1105 = lean_ctor_get(x_1028, 0);
x_1106 = lean_ctor_get(x_1028, 1);
lean_inc(x_1106);
lean_inc(x_1105);
lean_dec(x_1028);
x_1107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1107, 0, x_1105);
lean_ctor_set(x_1107, 1, x_1106);
return x_1107;
}
}
}
else
{
uint8_t x_1108; 
lean_dec(x_1013);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
x_1108 = !lean_is_exclusive(x_1014);
if (x_1108 == 0)
{
return x_1014;
}
else
{
lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; 
x_1109 = lean_ctor_get(x_1014, 0);
x_1110 = lean_ctor_get(x_1014, 1);
lean_inc(x_1110);
lean_inc(x_1109);
lean_dec(x_1014);
x_1111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1111, 0, x_1109);
lean_ctor_set(x_1111, 1, x_1110);
return x_1111;
}
}
}
default: 
{
lean_object* x_1112; lean_object* x_1113; 
lean_dec(x_11);
lean_dec(x_9);
x_1112 = lean_ctor_get(x_6, 5);
lean_inc(x_1112);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_1113 = l_List_forM___main___at_Lean_Meta_induction___spec__4(x_1, x_5, x_8, x_10, x_1112, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_1113) == 0)
{
lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; 
x_1114 = lean_ctor_get(x_1113, 1);
lean_inc(x_1114);
lean_dec(x_1113);
x_1115 = lean_st_ref_get(x_13, x_1114);
x_1116 = lean_ctor_get(x_1115, 0);
lean_inc(x_1116);
x_1117 = lean_ctor_get(x_1115, 1);
lean_inc(x_1117);
lean_dec(x_1115);
x_1118 = lean_ctor_get(x_1116, 0);
lean_inc(x_1118);
lean_dec(x_1116);
x_1119 = lean_ctor_get(x_6, 6);
lean_inc(x_1119);
x_1120 = l_List_redLength___main___rarg(x_1119);
x_1121 = lean_mk_empty_array_with_capacity(x_1120);
lean_dec(x_1120);
lean_inc(x_1119);
x_1122 = l_List_toArrayAux___main___rarg(x_1119, x_1121);
x_1123 = x_1122;
x_1124 = lean_unsigned_to_nat(0u);
lean_inc(x_1118);
lean_inc(x_5);
lean_inc(x_1);
x_1125 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_induction___spec__7___boxed), 13, 8);
lean_closure_set(x_1125, 0, x_1);
lean_closure_set(x_1125, 1, x_5);
lean_closure_set(x_1125, 2, x_8);
lean_closure_set(x_1125, 3, x_10);
lean_closure_set(x_1125, 4, x_1118);
lean_closure_set(x_1125, 5, x_1119);
lean_closure_set(x_1125, 6, x_1124);
lean_closure_set(x_1125, 7, x_1123);
x_1126 = x_1125;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_1127 = lean_apply_5(x_1126, x_12, x_13, x_14, x_15, x_1117);
if (lean_obj_tag(x_1127) == 0)
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; 
x_1128 = lean_ctor_get(x_1127, 0);
lean_inc(x_1128);
x_1129 = lean_ctor_get(x_1127, 1);
lean_inc(x_1129);
lean_dec(x_1127);
lean_inc(x_1);
x_1130 = l_Lean_Meta_getMVarType(x_1, x_12, x_13, x_14, x_15, x_1129);
if (lean_obj_tag(x_1130) == 0)
{
lean_object* x_1131; lean_object* x_1132; uint8_t x_1133; lean_object* x_1134; 
x_1131 = lean_ctor_get(x_1130, 0);
lean_inc(x_1131);
x_1132 = lean_ctor_get(x_1130, 1);
lean_inc(x_1132);
lean_dec(x_1130);
x_1133 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_1133 == 0)
{
lean_object* x_1186; uint8_t x_1187; 
x_1186 = l_Lean_MetavarContext_exprDependsOn(x_1118, x_1131, x_2);
x_1187 = lean_unbox(x_1186);
lean_dec(x_1186);
if (x_1187 == 0)
{
x_1134 = x_1132;
goto block_1185;
}
else
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; uint8_t x_1195; 
lean_dec(x_1128);
lean_dec(x_1112);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_1188 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1188, 0, x_3);
x_1189 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__11___closed__6;
x_1190 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1190, 0, x_1189);
lean_ctor_set(x_1190, 1, x_1188);
x_1191 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__4;
x_1192 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1192, 0, x_1190);
lean_ctor_set(x_1192, 1, x_1191);
x_1193 = lean_box(0);
x_1194 = l_Lean_Meta_throwTacticEx___rarg(x_5, x_1, x_1192, x_1193, x_12, x_13, x_14, x_15, x_1132);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_1195 = !lean_is_exclusive(x_1194);
if (x_1195 == 0)
{
return x_1194;
}
else
{
lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; 
x_1196 = lean_ctor_get(x_1194, 0);
x_1197 = lean_ctor_get(x_1194, 1);
lean_inc(x_1197);
lean_inc(x_1196);
lean_dec(x_1194);
x_1198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1198, 0, x_1196);
lean_ctor_set(x_1198, 1, x_1197);
return x_1198;
}
}
}
else
{
lean_dec(x_1131);
lean_dec(x_1118);
x_1134 = x_1132;
goto block_1185;
}
block_1185:
{
lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; uint8_t x_1139; lean_object* x_1140; 
lean_inc(x_1128);
x_1135 = x_1128;
x_1136 = l_Array_umapMAux___main___at_Lean_Meta_introN___spec__4(x_1124, x_1135);
x_1137 = x_1136;
x_1138 = lean_array_push(x_1137, x_2);
x_1139 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_1140 = l_Lean_Meta_revert(x_1, x_1138, x_1139, x_12, x_13, x_14, x_15, x_1134);
if (lean_obj_tag(x_1140) == 0)
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; uint8_t x_1147; lean_object* x_1148; 
x_1141 = lean_ctor_get(x_1140, 0);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1140, 1);
lean_inc(x_1142);
lean_dec(x_1140);
x_1143 = lean_ctor_get(x_1141, 0);
lean_inc(x_1143);
x_1144 = lean_ctor_get(x_1141, 1);
lean_inc(x_1144);
lean_dec(x_1141);
x_1145 = lean_array_get_size(x_1128);
x_1146 = lean_box(0);
x_1147 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_1148 = l_Lean_Meta_introN(x_1144, x_1145, x_1146, x_1147, x_12, x_13, x_14, x_15, x_1142);
if (lean_obj_tag(x_1148) == 0)
{
lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; 
x_1149 = lean_ctor_get(x_1148, 0);
lean_inc(x_1149);
x_1150 = lean_ctor_get(x_1148, 1);
lean_inc(x_1150);
lean_dec(x_1148);
x_1151 = lean_ctor_get(x_1149, 0);
lean_inc(x_1151);
x_1152 = lean_ctor_get(x_1149, 1);
lean_inc(x_1152);
lean_dec(x_1149);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_1153 = l_Lean_Meta_intro1(x_1152, x_1147, x_12, x_13, x_14, x_15, x_1150);
if (lean_obj_tag(x_1153) == 0)
{
lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
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
x_1158 = lean_box(0);
x_1159 = l_Array_iterateMAux___main___at_Lean_Meta_induction___spec__8(x_1128, x_1151, x_1128, x_1124, x_1158);
lean_dec(x_1128);
lean_inc(x_1157);
x_1160 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__1___boxed), 2, 1);
lean_closure_set(x_1160, 0, x_1157);
x_1161 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___closed__1;
x_1162 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_1161, x_1160, x_12, x_13, x_14, x_15, x_1155);
x_1163 = lean_ctor_get(x_1162, 1);
lean_inc(x_1163);
lean_dec(x_1162);
x_1164 = x_1151;
x_1165 = l_Array_umapMAux___main___at_Lean_LocalContext_getFVars___spec__1(x_1124, x_1164);
x_1166 = x_1165;
lean_inc(x_1156);
x_1167 = l_Lean_mkFVar(x_1156);
lean_inc(x_1157);
x_1168 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarType___boxed), 6, 1);
lean_closure_set(x_1168, 0, x_1157);
x_1169 = lean_box(x_1133);
lean_inc(x_1157);
x_1170 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12___lambda__2___boxed), 19, 13);
lean_closure_set(x_1170, 0, x_1156);
lean_closure_set(x_1170, 1, x_7);
lean_closure_set(x_1170, 2, x_1157);
lean_closure_set(x_1170, 3, x_3);
lean_closure_set(x_1170, 4, x_4);
lean_closure_set(x_1170, 5, x_5);
lean_closure_set(x_1170, 6, x_6);
lean_closure_set(x_1170, 7, x_1112);
lean_closure_set(x_1170, 8, x_1169);
lean_closure_set(x_1170, 9, x_1143);
lean_closure_set(x_1170, 10, x_1159);
lean_closure_set(x_1170, 11, x_1166);
lean_closure_set(x_1170, 12, x_1167);
x_1171 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_1171, 0, x_1168);
lean_closure_set(x_1171, 1, x_1170);
x_1172 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1157, x_1171, x_12, x_13, x_14, x_15, x_1163);
return x_1172;
}
else
{
uint8_t x_1173; 
lean_dec(x_1151);
lean_dec(x_1143);
lean_dec(x_1128);
lean_dec(x_1112);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1173 = !lean_is_exclusive(x_1153);
if (x_1173 == 0)
{
return x_1153;
}
else
{
lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; 
x_1174 = lean_ctor_get(x_1153, 0);
x_1175 = lean_ctor_get(x_1153, 1);
lean_inc(x_1175);
lean_inc(x_1174);
lean_dec(x_1153);
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
lean_dec(x_1143);
lean_dec(x_1128);
lean_dec(x_1112);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1177 = !lean_is_exclusive(x_1148);
if (x_1177 == 0)
{
return x_1148;
}
else
{
lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; 
x_1178 = lean_ctor_get(x_1148, 0);
x_1179 = lean_ctor_get(x_1148, 1);
lean_inc(x_1179);
lean_inc(x_1178);
lean_dec(x_1148);
x_1180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1180, 0, x_1178);
lean_ctor_set(x_1180, 1, x_1179);
return x_1180;
}
}
}
else
{
uint8_t x_1181; 
lean_dec(x_1128);
lean_dec(x_1112);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1181 = !lean_is_exclusive(x_1140);
if (x_1181 == 0)
{
return x_1140;
}
else
{
lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; 
x_1182 = lean_ctor_get(x_1140, 0);
x_1183 = lean_ctor_get(x_1140, 1);
lean_inc(x_1183);
lean_inc(x_1182);
lean_dec(x_1140);
x_1184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1184, 0, x_1182);
lean_ctor_set(x_1184, 1, x_1183);
return x_1184;
}
}
}
}
else
{
uint8_t x_1199; 
lean_dec(x_1128);
lean_dec(x_1118);
lean_dec(x_1112);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1199 = !lean_is_exclusive(x_1130);
if (x_1199 == 0)
{
return x_1130;
}
else
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
x_1200 = lean_ctor_get(x_1130, 0);
x_1201 = lean_ctor_get(x_1130, 1);
lean_inc(x_1201);
lean_inc(x_1200);
lean_dec(x_1130);
x_1202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1202, 0, x_1200);
lean_ctor_set(x_1202, 1, x_1201);
return x_1202;
}
}
}
else
{
uint8_t x_1203; 
lean_dec(x_1118);
lean_dec(x_1112);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1203 = !lean_is_exclusive(x_1127);
if (x_1203 == 0)
{
return x_1127;
}
else
{
lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; 
x_1204 = lean_ctor_get(x_1127, 0);
x_1205 = lean_ctor_get(x_1127, 1);
lean_inc(x_1205);
lean_inc(x_1204);
lean_dec(x_1127);
x_1206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1206, 0, x_1204);
lean_ctor_set(x_1206, 1, x_1205);
return x_1206;
}
}
}
else
{
uint8_t x_1207; 
lean_dec(x_1112);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
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
x_1207 = !lean_is_exclusive(x_1113);
if (x_1207 == 0)
{
return x_1113;
}
else
{
lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; 
x_1208 = lean_ctor_get(x_1113, 0);
x_1209 = lean_ctor_get(x_1113, 1);
lean_inc(x_1209);
lean_inc(x_1208);
lean_dec(x_1113);
x_1210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1210, 0, x_1208);
lean_ctor_set(x_1210, 1, x_1209);
return x_1210;
}
}
}
}
}
}
lean_object* l_Lean_Meta_induction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_7);
lean_inc(x_1);
x_12 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_16 = l_Lean_Meta_mkRecursorInfo(x_2, x_15, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_LocalDecl_type(x_13);
lean_dec(x_13);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_19);
x_21 = l_Lean_Meta_whnfUntil___at_Lean_Meta_induction___spec__1(x_19, x_20, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Meta_Tactic_Induction_6__throwUnexpectedMajorType___rarg(x_3, x_19, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_19);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_Expr_getAppNumArgsAux___main(x_26, x_27);
x_29 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_28);
x_30 = lean_mk_array(x_28, x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_sub(x_28, x_31);
lean_dec(x_28);
lean_inc(x_26);
x_33 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_induction___spec__12(x_3, x_1, x_2, x_4, x_5, x_17, x_20, x_26, x_26, x_30, x_32, x_7, x_8, x_9, x_10, x_25);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
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
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_12);
if (x_42 == 0)
{
return x_12;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_12, 0);
x_44 = lean_ctor_get(x_12, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_12);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l_Lean_Meta_induction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l___private_Lean_Meta_Tactic_Induction_2__addRecParams___main___closed__2;
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_checkNotAssigned___boxed), 7, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_induction___lambda__1___boxed), 11, 5);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_11);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_14, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at_Lean_Meta_induction___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at_Lean_Meta_induction___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Lean_Meta_induction___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_induction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
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
