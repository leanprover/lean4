// Lean compiler output
// Module: Lean.Elab.App
// Imports: Init Lean.Util.FindMVar Lean.Elab.Term Lean.Elab.Binders Lean.Elab.SyntheticMVars
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
lean_object* l_List_reverse___rarg(lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2;
lean_object* l___private_Lean_Elab_App_35__getSuccess(lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppArgs___closed__8;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__5;
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__25;
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppArgs___closed__4;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_16__finalize___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
extern lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__9;
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l___private_Lean_Elab_App_39__elabAppAux___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_List_tail_x21___rarg(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppArgs___closed__9;
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
lean_object* l___private_Lean_Elab_App_2__tryCoeFun___closed__7;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__3;
lean_object* l_Lean_Elab_logAt___at___private_Lean_Elab_App_14__propagateExpectedType___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_27__withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Syntax_getSepArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__5;
lean_object* l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at___private_Lean_Elab_App_14__propagateExpectedType___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppArgs___closed__2;
extern lean_object* l_Lean_fieldIdxKind___closed__2;
lean_object* l___private_Lean_Elab_App_29__addLValArg___main___closed__11;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_17__processExplictArg___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_30__elabAppLValsAux___main(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_36__toMessageData___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__processExplictArg___closed__3;
lean_object* l___private_Lean_Elab_App_38__mergeFailures(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_15__addEtaArg___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___boxed(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_26__resolveLValLoop___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__hasOptAutoParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_30__elabAppLValsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__10;
extern lean_object* l_Std_HashMap_inhabited___closed__1;
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__28;
lean_object* l___private_Lean_Elab_App_23__findMethod_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_31__elabAppLVals___closed__3;
lean_object* l___private_Lean_Elab_App_21__elabAppArgs___closed__1;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___closed__3;
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__3;
lean_object* l___private_Lean_Meta_InferType_22__isTypeFormerTypeImp___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__1;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__14;
lean_object* l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_5__normalizeFunType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__propagateExpectedType___closed__5;
lean_object* l___private_Lean_Elab_App_26__resolveLValLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandDollarProj(lean_object*);
lean_object* l___private_Lean_Elab_App_27__resolveLVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_15__addEtaArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__23;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__10;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_36__toMessageData___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__6;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__propagateExpectedType___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_App_34__isSuccess(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_16__finalize___closed__1;
lean_object* l___private_Lean_Elab_Util_2__evalSyntaxConstantUnsafe(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__2;
lean_object* l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__2;
extern lean_object* l_Lean_Elab_goalsToMessageData___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__21;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_hasToString(lean_object*);
lean_object* l___private_Lean_Elab_App_29__addLValArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_List_find_x3f___main___rarg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_29__addLValArg___main___closed__6;
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__22;
lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object*);
lean_object* l___private_Lean_Elab_App_3__addInstMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___main(lean_object*);
lean_object* l___private_Lean_Elab_App_7__getArgExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__8;
lean_object* l___private_Lean_Elab_App_39__elabAppAux___closed__1;
lean_object* l___private_Lean_Elab_App_28__mkBaseProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_InferType_4__getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__propagateExpectedType___closed__3;
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_29__addLValArg___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__6;
lean_object* l___private_Lean_Elab_App_28__mkBaseProjections___closed__2;
lean_object* l___private_Lean_Elab_App_16__finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_29__addLValArg___main___closed__12;
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_28__mkBaseProjections___closed__1;
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__4;
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__6;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef(lean_object*);
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_inhabited;
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__9;
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__1;
lean_object* l___private_Lean_Elab_App_14__propagateExpectedType___closed__7;
extern lean_object* l_Lean_mkAppStx___closed__8;
extern lean_object* l_Lean_mkAppStx___closed__7;
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__6;
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandDollarProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_2__tryCoeFun___closed__6;
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__16;
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_15__addEtaArg___spec__1(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv(lean_object*);
lean_object* l___private_Lean_Elab_App_39__elabAppAux___closed__3;
lean_object* l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_18__processImplicitArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__processExplictArg___closed__1;
extern lean_object* l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3;
lean_object* l___private_Lean_Elab_App_16__finalize___closed__3;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_ULift_HasRepr___rarg___closed__2;
lean_object* l___private_Lean_Elab_App_25__consumeImplicits___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_29__addLValArg___main___closed__10;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__1;
extern lean_object* l_Lean_Meta_isExprDefEq___rarg___closed__2;
uint8_t l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_16__finalize___closed__7;
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1;
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__11;
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_2__tryCoeFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_33__elabAppFn___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_Inhabited;
extern lean_object* l___private_Lean_Syntax_6__formatInfo___closed__1;
lean_object* l___private_Lean_Elab_App_11__hasOptAutoParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__processExplictArg___closed__2;
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__7;
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__3;
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__18;
lean_object* l___private_Lean_Elab_App_2__tryCoeFun___closed__4;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_32__elabAppFnId___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_2__tryCoeFun___closed__5;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyInfo(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__2;
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__15;
lean_object* l___private_Lean_Elab_App_3__addInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__3;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__throwLValError(lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_Arg_hasToString(lean_object*);
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__5;
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___main___rarg___closed__1;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1;
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__10;
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit(lean_object*);
extern lean_object* l_Lean_Meta_inferTypeRef;
lean_object* l___private_Lean_Elab_App_9__addNewArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Lean_Elab_App_7__getArgExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_18__processImplicitArg___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_37__toMessageList___boxed(lean_object*);
lean_object* l___private_Lean_Elab_App_23__findMethod_x3f___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__24;
lean_object* l___private_Lean_Elab_App_17__processExplictArg___closed__5;
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern(lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice(lean_object*);
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__7;
lean_object* l___private_Lean_Elab_App_14__propagateExpectedType___closed__12;
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__hasOptAutoParams___closed__1;
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__5;
lean_object* l___private_Lean_Elab_App_27__resolveLVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_2__tryCoeFun___closed__3;
lean_object* l___private_Lean_Elab_App_15__addEtaArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_26__resolveLValLoop___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_28__mkBaseProjections___closed__3;
lean_object* l___private_Lean_CoreM_1__mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l___private_Lean_Elab_App_13__getForallBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__7;
lean_object* l_Lean_Elab_Term_elabApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__processInstImplicitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_29__addLValArg___main___closed__3;
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___at___private_Lean_Elab_App_14__propagateExpectedType___spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_23__findMethod_x3f___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__2;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_18__processImplicitArg___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_elabChoice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAndAddNewArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_39__elabAppAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_20__forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandDollarProj___closed__1;
lean_object* l___private_Lean_Elab_App_2__tryCoeFun___closed__1;
lean_object* l___private_Lean_Elab_App_14__propagateExpectedType___closed__1;
lean_object* l___private_Lean_Elab_App_9__addNewArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_2__tryCoeFun___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_importModules___closed__1;
uint8_t l_Lean_Expr_isForall(lean_object*);
extern lean_object* l_Lean_formatEntry___closed__1;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_TermElabResult_inhabited;
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_17__processExplictArg___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Elab_App_14__propagateExpectedType___closed__11;
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj___closed__1;
lean_object* l___private_Lean_Elab_App_2__tryCoeFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAutoParam(lean_object*);
lean_object* l___private_Lean_Elab_App_22__throwLValError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabNamedPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_1__ensureArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
lean_object* l___private_Lean_Elab_App_16__finalize___closed__6;
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___main___boxed(lean_object*);
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__13;
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___boxed(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__19;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Term_elabProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_5__normalizeFunType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_41__regTraceClasses(lean_object*);
lean_object* l___private_Lean_Elab_App_20__hasArgsToProcess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_Lean_Elab_setMacroStackOption(lean_object*, uint8_t);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_16__finalize___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__11;
lean_object* l___private_Lean_Elab_App_29__addLValArg___main___closed__5;
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_32__elabAppFnId___spec__1___rarg(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_17__processExplictArg___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_App_20__hasArgsToProcess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppArgs___closed__3;
lean_object* l___private_Lean_Elab_App_8__isNextArgHole___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_1__ensureArgType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_15__runDefEqM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__5;
lean_object* l_Lean_Elab_Term_elabApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__20;
lean_object* l___private_Lean_Elab_App_21__elabAppArgs___closed__5;
lean_object* l___private_Lean_Elab_App_14__propagateExpectedType___closed__10;
lean_object* l_Lean_getParentStructures(lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__29;
lean_object* l___private_Lean_Elab_App_24__resolveLValAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l___private_Lean_Elab_App_2__tryCoeFun___closed__2;
extern lean_object* l_Lean_Elab_postponeExceptionId;
lean_object* l___private_Lean_Elab_App_21__elabAppArgs___closed__7;
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_App_33__elabAppFn___main___spec__1(lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_saveAllState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_38__mergeFailures___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_2__tryCoeFun___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_16__finalize___closed__5;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_40__elabAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__processExplictArg___closed__4;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1___closed__2;
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__26;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_33__elabAppFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1___closed__1;
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_whnfRef;
lean_object* l___private_Lean_Elab_App_13__getForallBody___main___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Exception_getRef(lean_object*);
lean_object* l___private_Lean_Elab_App_14__propagateExpectedType___closed__9;
lean_object* l___private_Lean_Elab_App_33__elabAppFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_App_35__getSuccess___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l___private_Lean_Elab_App_8__isNextArgHole(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__12;
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicitUnivs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_2__tryCoeFun___closed__8;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_32__elabAppFnId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1;
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_36__toMessageData___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__4;
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l___private_Lean_Elab_App_26__resolveLValLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_23__findMethod_x3f___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData___main(lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_36__toMessageData___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_34__isSuccess___boxed(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_App_16__finalize___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__1;
extern lean_object* l_Lean_KernelException_toMessageData___closed__12;
lean_object* l___private_Lean_Elab_App_26__resolveLValLoop___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_25__consumeImplicits___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__16;
lean_object* lean_array_pop(lean_object*);
lean_object* l___private_Lean_Elab_App_29__addLValArg___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__9;
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1;
lean_object* l_Lean_Elab_Term_registerSyntheticMVarWithCurrRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_15__addEtaArg___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
lean_object* l___private_Lean_Elab_App_17__processExplictArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_inhabited___closed__1;
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l_Lean_Elab_logException___at___private_Lean_Elab_Term_10__exceptionToSorry___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_29__addLValArg___main___closed__2;
lean_object* l___private_Lean_Elab_App_14__propagateExpectedType___closed__8;
lean_object* l___private_Lean_Elab_App_13__getForallBody(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__14;
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__13;
lean_object* l___private_Lean_Elab_App_29__addLValArg___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__propagateExpectedType___closed__4;
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main(lean_object*);
lean_object* l___private_Lean_Elab_App_14__propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_registerMVarErrorImplicitArgInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_16__finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_36__toMessageData___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_6__getBindingName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__15;
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__2;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_29__addLValArg___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__processExplictArg___closed__6;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Elab_App_36__toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__5;
lean_object* l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_6__getBindingName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_App_31__elabAppLVals___closed__2;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_26__resolveLValLoop___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_29__addLValArg___main___closed__8;
extern lean_object* l_Lean_Expr_ctorName___closed__11;
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_App_16__finalize___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__processImplicitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at___private_Lean_Elab_App_14__propagateExpectedType___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_25__consumeImplicits(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_15__addEtaArg___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Term_21__elabTermAux___main(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__8;
lean_object* l_Lean_Elab_Term_applyResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_39__elabAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__throwLValError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_36__toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__hasOptAutoParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_18__processImplicitArg___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_16__finalize___closed__4;
extern lean_object* l___private_Lean_Elab_Term_14__isExplicit___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
lean_object* l_Lean_Elab_Term_expandApp___closed__2;
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__4;
lean_object* l___private_Lean_Elab_App_25__consumeImplicits___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppArgs___closed__6;
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_App_31__elabAppLVals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1;
lean_object* l___private_Lean_Elab_App_16__finalize___closed__8;
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l___private_Lean_Elab_App_29__addLValArg___main___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__3;
lean_object* l___private_Lean_Elab_App_30__elabAppLValsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_App_13__getForallBody___main___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_29__addLValArg___main___closed__7;
lean_object* l_Lean_Elab_Term_ensureHasTypeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_16__finalize___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_33__elabAppFn___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_38__mergeFailures___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_28__mkBaseProjections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findField_x3f___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__1;
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l___private_Lean_Elab_App_30__elabAppLValsAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__17;
lean_object* l___private_Lean_Elab_App_29__addLValArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__4;
lean_object* l_Lean_Elab_Term_elabExplicitUnivs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_6__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_37__toMessageList(lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_31__elabAppLVals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_29__addLValArg___main___closed__4;
lean_object* l___private_Lean_Elab_App_31__elabAppLVals___closed__1;
extern lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2;
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___closed__12;
lean_object* l___private_Lean_Elab_App_29__addLValArg___main___closed__9;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l___private_Lean_Elab_App_32__elabAppFnId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___closed__27;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_inhabited;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_32__elabAppFnId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_12__fTypeHasOptAutoParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkArrow___rarg___closed__2;
lean_object* l___private_Lean_Elab_App_14__propagateExpectedType___closed__6;
static lean_object* _init_l_Lean_Elab_Term_Arg_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_Arg_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_Arg_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_Arg_hasToString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = 0;
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_formatStxAux___main(x_3, x_4, x_5, x_2);
x_7 = lean_box(0);
x_8 = l_Lean_Format_pretty(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
return x_10;
}
}
}
lean_object* l_Lean_Elab_Term_NamedArg_hasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_System_FilePath_dirName___closed__1;
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_2);
x_5 = l_Prod_HasRepr___rarg___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lean_formatEntry___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = 0;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_formatStxAux___main(x_11, x_12, x_13, x_10);
x_15 = lean_box(0);
x_16 = l_Lean_Format_pretty(x_14, x_15);
x_17 = lean_string_append(x_8, x_16);
lean_dec(x_16);
x_18 = l_ULift_HasRepr___rarg___closed__2;
x_19 = lean_string_append(x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_expr_dbg_to_string(x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_8, x_21);
lean_dec(x_21);
x_23 = l_ULift_HasRepr___rarg___closed__2;
x_24 = lean_string_append(x_22, x_23);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_NamedArg_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Arg_inhabited___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_NamedArg_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_NamedArg_inhabited___closed__1;
return x_1;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_5);
return x_11;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("argument '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' was already set");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(x_1, x_2, x_1, x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_array_push(x_1, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_System_FilePath_dirName___closed__1;
x_17 = l_Lean_Name_toStringWithSep___main(x_16, x_15);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_Elab_Term_addNamedArg___closed__3;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Elab_Term_addNamedArg___closed__6;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_addNamedArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_1__ensureArgType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_11 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Term_ensureHasTypeAux(x_14, x_12, x_2, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l___private_Lean_Elab_App_1__ensureArgType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_1__ensureArgType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_2__tryCoeFun___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_mkArrow___rarg___closed__2;
x_11 = l___private_Lean_CoreM_1__mkFreshNameImp(x_10, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = 0;
x_15 = l_Lean_mkForall(x_13, x_14, x_1, x_2);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = 0;
x_19 = l_Lean_mkForall(x_16, x_18, x_1, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_2__tryCoeFun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CoeFun");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_2__tryCoeFun___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_2__tryCoeFun___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_2__tryCoeFun___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("function expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_2__tryCoeFun___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_2__tryCoeFun___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_2__tryCoeFun___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_2__tryCoeFun___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_2__tryCoeFun___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeFun");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_2__tryCoeFun___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_2__tryCoeFun___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_2__tryCoeFun___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_2__tryCoeFun___closed__5;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_2__tryCoeFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_10 = l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2___rarg(x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_mkSort(x_11);
lean_inc(x_1);
x_14 = l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_2__tryCoeFun___spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = 0;
x_19 = lean_box(0);
lean_inc(x_5);
x_20 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_23 = l___private_Lean_Meta_InferType_4__getLevelImp(x_1, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_11);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
x_29 = l___private_Lean_Elab_App_2__tryCoeFun___closed__2;
lean_inc(x_28);
x_30 = l_Lean_mkConst(x_29, x_28);
x_31 = l_Lean_mkAppStx___closed__9;
lean_inc(x_1);
x_32 = lean_array_push(x_31, x_1);
lean_inc(x_21);
x_33 = lean_array_push(x_32, x_21);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_33, x_33, x_34, x_30);
lean_dec(x_33);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = 1;
lean_inc(x_5);
x_38 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_36, x_37, x_19, x_5, x_6, x_7, x_8, x_25);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = l_Lean_Expr_mvarId_x21(x_39);
x_57 = lean_ctor_get(x_7, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_7, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_7, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_7, 3);
lean_inc(x_60);
x_61 = 0;
x_62 = l_Lean_Elab_setMacroStackOption(x_57, x_61);
x_63 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_60);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_64 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_42, x_3, x_4, x_5, x_6, x_63, x_8, x_40);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unbox(x_65);
lean_dec(x_65);
x_43 = x_67;
x_44 = x_66;
goto block_56;
}
else
{
lean_object* x_68; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_dec(x_64);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l___private_Lean_Elab_App_2__tryCoeFun___closed__8;
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_68);
x_78 = lean_ctor_get(x_64, 1);
lean_inc(x_78);
lean_dec(x_64);
x_79 = l___private_Lean_Elab_App_2__tryCoeFun___closed__5;
x_80 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_78);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
return x_80;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_80);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
block_56:
{
if (x_43 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_2);
lean_dec(x_1);
x_45 = l___private_Lean_Elab_App_2__tryCoeFun___closed__5;
x_46 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_44);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_47 = l___private_Lean_Elab_App_2__tryCoeFun___closed__7;
x_48 = l_Lean_mkConst(x_47, x_28);
x_49 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_50 = lean_array_push(x_49, x_1);
x_51 = lean_array_push(x_50, x_21);
x_52 = lean_array_push(x_51, x_2);
x_53 = lean_array_push(x_52, x_39);
x_54 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_53, x_53, x_34, x_48);
lean_dec(x_53);
if (lean_is_scalar(x_41)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_41;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_44);
return x_55;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_23);
if (x_85 == 0)
{
return x_23;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_23, 0);
x_87 = lean_ctor_get(x_23, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_23);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_2__tryCoeFun___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_2__tryCoeFun___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_2__tryCoeFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_2__tryCoeFun(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_1, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_14);
x_15 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
lean_inc(x_7);
x_20 = l_Lean_Elab_Term_registerSyntheticMVarWithCurrRef(x_14, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
lean_dec(x_2);
x_2 = x_23;
x_9 = x_21;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_2, x_26);
lean_dec(x_2);
x_2 = x_27;
x_9 = x_25;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_synthesizeAppInstMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_3__addInstMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 7);
x_12 = lean_array_push(x_11, x_1);
lean_ctor_set(x_2, 7, x_12);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*9);
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
x_21 = lean_ctor_get(x_2, 4);
x_22 = lean_ctor_get(x_2, 5);
x_23 = lean_ctor_get(x_2, 6);
x_24 = lean_ctor_get(x_2, 7);
x_25 = lean_ctor_get(x_2, 8);
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*9 + 1);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_27 = lean_array_push(x_24, x_1);
x_28 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_28, 2, x_19);
lean_ctor_set(x_28, 3, x_20);
lean_ctor_set(x_28, 4, x_21);
lean_ctor_set(x_28, 5, x_22);
lean_ctor_set(x_28, 6, x_23);
lean_ctor_set(x_28, 7, x_27);
lean_ctor_set(x_28, 8, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*9, x_16);
lean_ctor_set_uint8(x_28, sizeof(void*)*9 + 1, x_26);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_9);
return x_31;
}
}
}
lean_object* l___private_Lean_Elab_App_3__addInstMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_3__addInstMVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 7);
x_11 = l_Array_empty___closed__1;
lean_ctor_set(x_1, 7, x_11);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_10, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*9);
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get(x_1, 2);
x_29 = lean_ctor_get(x_1, 3);
x_30 = lean_ctor_get(x_1, 4);
x_31 = lean_ctor_get(x_1, 5);
x_32 = lean_ctor_get(x_1, 6);
x_33 = lean_ctor_get(x_1, 7);
x_34 = lean_ctor_get(x_1, 8);
x_35 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 1);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_36 = l_Array_empty___closed__1;
x_37 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 3, x_29);
lean_ctor_set(x_37, 4, x_30);
lean_ctor_set(x_37, 5, x_31);
lean_ctor_set(x_37, 6, x_32);
lean_ctor_set(x_37, 7, x_36);
lean_ctor_set(x_37, 8, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*9, x_25);
lean_ctor_set_uint8(x_37, sizeof(void*)*9 + 1, x_35);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_33, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_33);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_37);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_37);
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_47 = x_39;
} else {
 lean_dec_ref(x_39);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 3);
lean_inc(x_13);
x_14 = lean_nat_dec_eq(x_11, x_12);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_7, 3);
lean_dec(x_16);
x_17 = lean_ctor_get(x_7, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_7, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_7, 0);
lean_dec(x_19);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_11, x_20);
lean_dec(x_11);
lean_ctor_set(x_7, 1, x_21);
x_22 = l_Lean_Meta_whnfRef;
x_23 = lean_st_ref_get(x_22, x_9);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_apply_6(x_24, x_1, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_2);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_7);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_11, x_38);
lean_dec(x_11);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_10);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_12);
lean_ctor_set(x_40, 3, x_13);
x_41 = l_Lean_Meta_whnfRef;
x_42 = lean_st_ref_get(x_41, x_9);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_apply_6(x_43, x_1, x_5, x_6, x_40, x_8, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_2);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_2);
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_53 = x_45;
} else {
 lean_dec_ref(x_45);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_55 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_56 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_55, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
}
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_Meta_whnf___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Expr_isForall(x_14);
if (x_15 == 0)
{
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_1);
return x_10;
}
else
{
lean_dec(x_1);
return x_10;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = l_Lean_Expr_isForall(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
else
{
lean_object* x_20; 
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
x_26 = l_Lean_Expr_isForall(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
if (lean_is_scalar(x_25)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_25;
}
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
return x_10;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_10, 0);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_10);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 3);
lean_inc(x_13);
x_14 = lean_nat_dec_eq(x_11, x_12);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_7, 3);
lean_dec(x_16);
x_17 = lean_ctor_get(x_7, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_7, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_7, 0);
lean_dec(x_19);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_11, x_20);
lean_dec(x_11);
lean_ctor_set(x_7, 1, x_21);
x_22 = l_Lean_Meta_inferTypeRef;
x_23 = lean_st_ref_get(x_22, x_9);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_apply_6(x_24, x_1, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_2);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_7);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_11, x_38);
lean_dec(x_11);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_10);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_12);
lean_ctor_set(x_40, 3, x_13);
x_41 = l_Lean_Meta_inferTypeRef;
x_42 = lean_st_ref_get(x_41, x_9);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_apply_6(x_43, x_1, x_5, x_6, x_40, x_8, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_2);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_2);
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_53 = x_45;
} else {
 lean_dec_ref(x_45);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_55 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_56 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_55, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
}
lean_object* l___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_9 = l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_12);
x_18 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__1(x_17, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
if (lean_obj_tag(x_23) == 7)
{
uint8_t x_89; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_24);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_24, 1);
lean_dec(x_90);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_20, 0, x_14);
return x_18;
}
else
{
uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
x_91 = lean_ctor_get_uint8(x_24, sizeof(void*)*9);
x_92 = lean_ctor_get(x_24, 0);
x_93 = lean_ctor_get(x_24, 2);
x_94 = lean_ctor_get(x_24, 3);
x_95 = lean_ctor_get(x_24, 4);
x_96 = lean_ctor_get(x_24, 5);
x_97 = lean_ctor_get(x_24, 6);
x_98 = lean_ctor_get(x_24, 7);
x_99 = lean_ctor_get(x_24, 8);
x_100 = lean_ctor_get_uint8(x_24, sizeof(void*)*9 + 1);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_24);
x_101 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_101, 0, x_92);
lean_ctor_set(x_101, 1, x_23);
lean_ctor_set(x_101, 2, x_93);
lean_ctor_set(x_101, 3, x_94);
lean_ctor_set(x_101, 4, x_95);
lean_ctor_set(x_101, 5, x_96);
lean_ctor_set(x_101, 6, x_97);
lean_ctor_set(x_101, 7, x_98);
lean_ctor_set(x_101, 8, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*9, x_91);
lean_ctor_set_uint8(x_101, sizeof(void*)*9 + 1, x_100);
lean_ctor_set(x_20, 1, x_101);
lean_ctor_set(x_20, 0, x_14);
return x_18;
}
}
else
{
lean_free_object(x_20);
lean_free_object(x_18);
x_25 = x_14;
goto block_88;
}
block_88:
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_25);
x_26 = lean_ctor_get(x_12, 0);
lean_inc(x_26);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_27 = l___private_Lean_Elab_App_2__tryCoeFun(x_23, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_28);
x_30 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__3(x_28, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_29);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_32, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_32, 0);
lean_dec(x_40);
lean_ctor_set(x_32, 1, x_36);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_31, 0, x_14);
return x_30;
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_41 = lean_ctor_get_uint8(x_32, sizeof(void*)*9);
x_42 = lean_ctor_get(x_32, 2);
x_43 = lean_ctor_get(x_32, 3);
x_44 = lean_ctor_get(x_32, 4);
x_45 = lean_ctor_get(x_32, 5);
x_46 = lean_ctor_get(x_32, 6);
x_47 = lean_ctor_get(x_32, 7);
x_48 = lean_ctor_get(x_32, 8);
x_49 = lean_ctor_get_uint8(x_32, sizeof(void*)*9 + 1);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_32);
x_50 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_50, 0, x_28);
lean_ctor_set(x_50, 1, x_36);
lean_ctor_set(x_50, 2, x_42);
lean_ctor_set(x_50, 3, x_43);
lean_ctor_set(x_50, 4, x_44);
lean_ctor_set(x_50, 5, x_45);
lean_ctor_set(x_50, 6, x_46);
lean_ctor_set(x_50, 7, x_47);
lean_ctor_set(x_50, 8, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*9, x_41);
lean_ctor_set_uint8(x_50, sizeof(void*)*9 + 1, x_49);
lean_ctor_set(x_31, 1, x_50);
lean_ctor_set(x_31, 0, x_14);
return x_30;
}
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_51 = lean_ctor_get(x_31, 0);
lean_inc(x_51);
lean_dec(x_31);
x_52 = lean_ctor_get_uint8(x_32, sizeof(void*)*9);
x_53 = lean_ctor_get(x_32, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_32, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_32, 4);
lean_inc(x_55);
x_56 = lean_ctor_get(x_32, 5);
lean_inc(x_56);
x_57 = lean_ctor_get(x_32, 6);
lean_inc(x_57);
x_58 = lean_ctor_get(x_32, 7);
lean_inc(x_58);
x_59 = lean_ctor_get(x_32, 8);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_32, sizeof(void*)*9 + 1);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 lean_ctor_release(x_32, 5);
 lean_ctor_release(x_32, 6);
 lean_ctor_release(x_32, 7);
 lean_ctor_release(x_32, 8);
 x_61 = x_32;
} else {
 lean_dec_ref(x_32);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 9, 2);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_28);
lean_ctor_set(x_62, 1, x_51);
lean_ctor_set(x_62, 2, x_53);
lean_ctor_set(x_62, 3, x_54);
lean_ctor_set(x_62, 4, x_55);
lean_ctor_set(x_62, 5, x_56);
lean_ctor_set(x_62, 6, x_57);
lean_ctor_set(x_62, 7, x_58);
lean_ctor_set(x_62, 8, x_59);
lean_ctor_set_uint8(x_62, sizeof(void*)*9, x_52);
lean_ctor_set_uint8(x_62, sizeof(void*)*9 + 1, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_14);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_30, 0, x_63);
return x_30;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_64 = lean_ctor_get(x_30, 1);
lean_inc(x_64);
lean_dec(x_30);
x_65 = lean_ctor_get(x_31, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_66 = x_31;
} else {
 lean_dec_ref(x_31);
 x_66 = lean_box(0);
}
x_67 = lean_ctor_get_uint8(x_32, sizeof(void*)*9);
x_68 = lean_ctor_get(x_32, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_32, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_32, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_32, 5);
lean_inc(x_71);
x_72 = lean_ctor_get(x_32, 6);
lean_inc(x_72);
x_73 = lean_ctor_get(x_32, 7);
lean_inc(x_73);
x_74 = lean_ctor_get(x_32, 8);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_32, sizeof(void*)*9 + 1);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 lean_ctor_release(x_32, 2);
 lean_ctor_release(x_32, 3);
 lean_ctor_release(x_32, 4);
 lean_ctor_release(x_32, 5);
 lean_ctor_release(x_32, 6);
 lean_ctor_release(x_32, 7);
 lean_ctor_release(x_32, 8);
 x_76 = x_32;
} else {
 lean_dec_ref(x_32);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 9, 2);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_28);
lean_ctor_set(x_77, 1, x_65);
lean_ctor_set(x_77, 2, x_68);
lean_ctor_set(x_77, 3, x_69);
lean_ctor_set(x_77, 4, x_70);
lean_ctor_set(x_77, 5, x_71);
lean_ctor_set(x_77, 6, x_72);
lean_ctor_set(x_77, 7, x_73);
lean_ctor_set(x_77, 8, x_74);
lean_ctor_set_uint8(x_77, sizeof(void*)*9, x_67);
lean_ctor_set_uint8(x_77, sizeof(void*)*9 + 1, x_75);
if (lean_is_scalar(x_66)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_66;
}
lean_ctor_set(x_78, 0, x_14);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_64);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_28);
x_80 = !lean_is_exclusive(x_30);
if (x_80 == 0)
{
return x_30;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_30, 0);
x_82 = lean_ctor_get(x_30, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_30);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_27);
if (x_84 == 0)
{
return x_27;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_27, 0);
x_86 = lean_ctor_get(x_27, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_27);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_18, 1);
x_103 = lean_ctor_get(x_20, 0);
x_104 = lean_ctor_get(x_20, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_20);
if (lean_obj_tag(x_103) == 7)
{
uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_139 = lean_ctor_get_uint8(x_104, sizeof(void*)*9);
x_140 = lean_ctor_get(x_104, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_104, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_104, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_104, 4);
lean_inc(x_143);
x_144 = lean_ctor_get(x_104, 5);
lean_inc(x_144);
x_145 = lean_ctor_get(x_104, 6);
lean_inc(x_145);
x_146 = lean_ctor_get(x_104, 7);
lean_inc(x_146);
x_147 = lean_ctor_get(x_104, 8);
lean_inc(x_147);
x_148 = lean_ctor_get_uint8(x_104, sizeof(void*)*9 + 1);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 lean_ctor_release(x_104, 2);
 lean_ctor_release(x_104, 3);
 lean_ctor_release(x_104, 4);
 lean_ctor_release(x_104, 5);
 lean_ctor_release(x_104, 6);
 lean_ctor_release(x_104, 7);
 lean_ctor_release(x_104, 8);
 x_149 = x_104;
} else {
 lean_dec_ref(x_104);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(0, 9, 2);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_140);
lean_ctor_set(x_150, 1, x_103);
lean_ctor_set(x_150, 2, x_141);
lean_ctor_set(x_150, 3, x_142);
lean_ctor_set(x_150, 4, x_143);
lean_ctor_set(x_150, 5, x_144);
lean_ctor_set(x_150, 6, x_145);
lean_ctor_set(x_150, 7, x_146);
lean_ctor_set(x_150, 8, x_147);
lean_ctor_set_uint8(x_150, sizeof(void*)*9, x_139);
lean_ctor_set_uint8(x_150, sizeof(void*)*9 + 1, x_148);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_14);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_18, 0, x_151);
return x_18;
}
else
{
lean_free_object(x_18);
x_105 = x_14;
goto block_138;
}
block_138:
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_105);
x_106 = lean_ctor_get(x_12, 0);
lean_inc(x_106);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_107 = l___private_Lean_Elab_App_2__tryCoeFun(x_103, x_106, x_2, x_3, x_4, x_5, x_6, x_7, x_102);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
lean_inc(x_108);
x_110 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__3(x_108, x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_109);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_114 = x_110;
} else {
 lean_dec_ref(x_110);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_116 = x_111;
} else {
 lean_dec_ref(x_111);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get_uint8(x_112, sizeof(void*)*9);
x_118 = lean_ctor_get(x_112, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_112, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_112, 4);
lean_inc(x_120);
x_121 = lean_ctor_get(x_112, 5);
lean_inc(x_121);
x_122 = lean_ctor_get(x_112, 6);
lean_inc(x_122);
x_123 = lean_ctor_get(x_112, 7);
lean_inc(x_123);
x_124 = lean_ctor_get(x_112, 8);
lean_inc(x_124);
x_125 = lean_ctor_get_uint8(x_112, sizeof(void*)*9 + 1);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 lean_ctor_release(x_112, 3);
 lean_ctor_release(x_112, 4);
 lean_ctor_release(x_112, 5);
 lean_ctor_release(x_112, 6);
 lean_ctor_release(x_112, 7);
 lean_ctor_release(x_112, 8);
 x_126 = x_112;
} else {
 lean_dec_ref(x_112);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(0, 9, 2);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_108);
lean_ctor_set(x_127, 1, x_115);
lean_ctor_set(x_127, 2, x_118);
lean_ctor_set(x_127, 3, x_119);
lean_ctor_set(x_127, 4, x_120);
lean_ctor_set(x_127, 5, x_121);
lean_ctor_set(x_127, 6, x_122);
lean_ctor_set(x_127, 7, x_123);
lean_ctor_set(x_127, 8, x_124);
lean_ctor_set_uint8(x_127, sizeof(void*)*9, x_117);
lean_ctor_set_uint8(x_127, sizeof(void*)*9 + 1, x_125);
if (lean_is_scalar(x_116)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_116;
}
lean_ctor_set(x_128, 0, x_14);
lean_ctor_set(x_128, 1, x_127);
if (lean_is_scalar(x_114)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_114;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_113);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_108);
x_130 = lean_ctor_get(x_110, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_110, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_132 = x_110;
} else {
 lean_dec_ref(x_110);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_104);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_134 = lean_ctor_get(x_107, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_107, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_136 = x_107;
} else {
 lean_dec_ref(x_107);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_152 = lean_ctor_get(x_18, 0);
x_153 = lean_ctor_get(x_18, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_18);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_156 = x_152;
} else {
 lean_dec_ref(x_152);
 x_156 = lean_box(0);
}
if (lean_obj_tag(x_154) == 7)
{
uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_191 = lean_ctor_get_uint8(x_155, sizeof(void*)*9);
x_192 = lean_ctor_get(x_155, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_155, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_155, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_155, 4);
lean_inc(x_195);
x_196 = lean_ctor_get(x_155, 5);
lean_inc(x_196);
x_197 = lean_ctor_get(x_155, 6);
lean_inc(x_197);
x_198 = lean_ctor_get(x_155, 7);
lean_inc(x_198);
x_199 = lean_ctor_get(x_155, 8);
lean_inc(x_199);
x_200 = lean_ctor_get_uint8(x_155, sizeof(void*)*9 + 1);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 lean_ctor_release(x_155, 2);
 lean_ctor_release(x_155, 3);
 lean_ctor_release(x_155, 4);
 lean_ctor_release(x_155, 5);
 lean_ctor_release(x_155, 6);
 lean_ctor_release(x_155, 7);
 lean_ctor_release(x_155, 8);
 x_201 = x_155;
} else {
 lean_dec_ref(x_155);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 9, 2);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_192);
lean_ctor_set(x_202, 1, x_154);
lean_ctor_set(x_202, 2, x_193);
lean_ctor_set(x_202, 3, x_194);
lean_ctor_set(x_202, 4, x_195);
lean_ctor_set(x_202, 5, x_196);
lean_ctor_set(x_202, 6, x_197);
lean_ctor_set(x_202, 7, x_198);
lean_ctor_set(x_202, 8, x_199);
lean_ctor_set_uint8(x_202, sizeof(void*)*9, x_191);
lean_ctor_set_uint8(x_202, sizeof(void*)*9 + 1, x_200);
if (lean_is_scalar(x_156)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_156;
}
lean_ctor_set(x_203, 0, x_14);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_153);
return x_204;
}
else
{
lean_dec(x_156);
x_157 = x_14;
goto block_190;
}
block_190:
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_157);
x_158 = lean_ctor_get(x_12, 0);
lean_inc(x_158);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_159 = l___private_Lean_Elab_App_2__tryCoeFun(x_154, x_158, x_2, x_3, x_4, x_5, x_6, x_7, x_153);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
lean_inc(x_160);
x_162 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__3(x_160, x_155, x_2, x_3, x_4, x_5, x_6, x_7, x_161);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_166 = x_162;
} else {
 lean_dec_ref(x_162);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_163, 0);
lean_inc(x_167);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_168 = x_163;
} else {
 lean_dec_ref(x_163);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get_uint8(x_164, sizeof(void*)*9);
x_170 = lean_ctor_get(x_164, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_164, 3);
lean_inc(x_171);
x_172 = lean_ctor_get(x_164, 4);
lean_inc(x_172);
x_173 = lean_ctor_get(x_164, 5);
lean_inc(x_173);
x_174 = lean_ctor_get(x_164, 6);
lean_inc(x_174);
x_175 = lean_ctor_get(x_164, 7);
lean_inc(x_175);
x_176 = lean_ctor_get(x_164, 8);
lean_inc(x_176);
x_177 = lean_ctor_get_uint8(x_164, sizeof(void*)*9 + 1);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 lean_ctor_release(x_164, 2);
 lean_ctor_release(x_164, 3);
 lean_ctor_release(x_164, 4);
 lean_ctor_release(x_164, 5);
 lean_ctor_release(x_164, 6);
 lean_ctor_release(x_164, 7);
 lean_ctor_release(x_164, 8);
 x_178 = x_164;
} else {
 lean_dec_ref(x_164);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(0, 9, 2);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_160);
lean_ctor_set(x_179, 1, x_167);
lean_ctor_set(x_179, 2, x_170);
lean_ctor_set(x_179, 3, x_171);
lean_ctor_set(x_179, 4, x_172);
lean_ctor_set(x_179, 5, x_173);
lean_ctor_set(x_179, 6, x_174);
lean_ctor_set(x_179, 7, x_175);
lean_ctor_set(x_179, 8, x_176);
lean_ctor_set_uint8(x_179, sizeof(void*)*9, x_169);
lean_ctor_set_uint8(x_179, sizeof(void*)*9 + 1, x_177);
if (lean_is_scalar(x_168)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_168;
}
lean_ctor_set(x_180, 0, x_14);
lean_ctor_set(x_180, 1, x_179);
if (lean_is_scalar(x_166)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_166;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_165);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_160);
x_182 = lean_ctor_get(x_162, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_162, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_184 = x_162;
} else {
 lean_dec_ref(x_162);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_155);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_186 = lean_ctor_get(x_159, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_159, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_188 = x_159;
} else {
 lean_dec_ref(x_159);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_205 = !lean_is_exclusive(x_18);
if (x_205 == 0)
{
return x_18;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_18, 0);
x_207 = lean_ctor_get(x_18, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_18);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
uint8_t x_209; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_209 = !lean_is_exclusive(x_15);
if (x_209 == 0)
{
return x_15;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_15, 0);
x_211 = lean_ctor_get(x_15, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_15);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_213 = !lean_is_exclusive(x_9);
if (x_213 == 0)
{
return x_9;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_9, 0);
x_215 = lean_ctor_get(x_9, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_9);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
}
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_whnf___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_5__normalizeFunType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__1(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_12, 1);
lean_dec(x_19);
lean_inc(x_16);
lean_ctor_set(x_12, 1, x_16);
return x_10;
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_20 = lean_ctor_get_uint8(x_12, sizeof(void*)*9);
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 2);
x_23 = lean_ctor_get(x_12, 3);
x_24 = lean_ctor_get(x_12, 4);
x_25 = lean_ctor_get(x_12, 5);
x_26 = lean_ctor_get(x_12, 6);
x_27 = lean_ctor_get(x_12, 7);
x_28 = lean_ctor_get(x_12, 8);
x_29 = lean_ctor_get_uint8(x_12, sizeof(void*)*9 + 1);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
lean_inc(x_16);
x_30 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_16);
lean_ctor_set(x_30, 2, x_22);
lean_ctor_set(x_30, 3, x_23);
lean_ctor_set(x_30, 4, x_24);
lean_ctor_set(x_30, 5, x_25);
lean_ctor_set(x_30, 6, x_26);
lean_ctor_set(x_30, 7, x_27);
lean_ctor_set(x_30, 8, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*9, x_20);
lean_ctor_set_uint8(x_30, sizeof(void*)*9 + 1, x_29);
lean_ctor_set(x_11, 1, x_30);
return x_10;
}
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
lean_dec(x_11);
x_32 = lean_ctor_get_uint8(x_12, sizeof(void*)*9);
x_33 = lean_ctor_get(x_12, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_12, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_12, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_12, 4);
lean_inc(x_36);
x_37 = lean_ctor_get(x_12, 5);
lean_inc(x_37);
x_38 = lean_ctor_get(x_12, 6);
lean_inc(x_38);
x_39 = lean_ctor_get(x_12, 7);
lean_inc(x_39);
x_40 = lean_ctor_get(x_12, 8);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_12, sizeof(void*)*9 + 1);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 lean_ctor_release(x_12, 5);
 lean_ctor_release(x_12, 6);
 lean_ctor_release(x_12, 7);
 lean_ctor_release(x_12, 8);
 x_42 = x_12;
} else {
 lean_dec_ref(x_12);
 x_42 = lean_box(0);
}
lean_inc(x_31);
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 9, 2);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_31);
lean_ctor_set(x_43, 2, x_34);
lean_ctor_set(x_43, 3, x_35);
lean_ctor_set(x_43, 4, x_36);
lean_ctor_set(x_43, 5, x_37);
lean_ctor_set(x_43, 6, x_38);
lean_ctor_set(x_43, 7, x_39);
lean_ctor_set(x_43, 8, x_40);
lean_ctor_set_uint8(x_43, sizeof(void*)*9, x_32);
lean_ctor_set_uint8(x_43, sizeof(void*)*9 + 1, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_31);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_10, 0, x_44);
return x_10;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_45 = lean_ctor_get(x_10, 1);
lean_inc(x_45);
lean_dec(x_10);
x_46 = lean_ctor_get(x_11, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_47 = x_11;
} else {
 lean_dec_ref(x_11);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get_uint8(x_12, sizeof(void*)*9);
x_49 = lean_ctor_get(x_12, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_12, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_12, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_12, 4);
lean_inc(x_52);
x_53 = lean_ctor_get(x_12, 5);
lean_inc(x_53);
x_54 = lean_ctor_get(x_12, 6);
lean_inc(x_54);
x_55 = lean_ctor_get(x_12, 7);
lean_inc(x_55);
x_56 = lean_ctor_get(x_12, 8);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_12, sizeof(void*)*9 + 1);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 lean_ctor_release(x_12, 5);
 lean_ctor_release(x_12, 6);
 lean_ctor_release(x_12, 7);
 lean_ctor_release(x_12, 8);
 x_58 = x_12;
} else {
 lean_dec_ref(x_12);
 x_58 = lean_box(0);
}
lean_inc(x_46);
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 9, 2);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_46);
lean_ctor_set(x_59, 2, x_50);
lean_ctor_set(x_59, 3, x_51);
lean_ctor_set(x_59, 4, x_52);
lean_ctor_set(x_59, 5, x_53);
lean_ctor_set(x_59, 6, x_54);
lean_ctor_set(x_59, 7, x_55);
lean_ctor_set(x_59, 8, x_56);
lean_ctor_set_uint8(x_59, sizeof(void*)*9, x_48);
lean_ctor_set_uint8(x_59, sizeof(void*)*9 + 1, x_57);
if (lean_is_scalar(x_47)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_47;
}
lean_ctor_set(x_60, 0, x_46);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_45);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_10);
if (x_62 == 0)
{
return x_10;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_10, 0);
x_64 = lean_ctor_get(x_10, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_10);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
lean_object* l___private_Lean_Elab_App_5__normalizeFunType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_5__normalizeFunType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_6__getBindingName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_Lean_Expr_bindingName_x21(x_9);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_6__getBindingName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_6__getBindingName(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_7__getArgExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_Lean_Expr_bindingDomain_x21(x_9);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_7__getArgExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_7__getArgExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_List_filterAux___main___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_name_eq(x_14, x_1);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_3);
x_2 = x_13;
x_3 = x_16;
goto _start;
}
else
{
lean_dec(x_12);
x_2 = x_13;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_List_filterAux___main___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_List_filterAux___main___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___main___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 3);
x_12 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(x_11, x_1);
lean_ctor_set(x_2, 3, x_12);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*9);
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get(x_2, 3);
x_21 = lean_ctor_get(x_2, 4);
x_22 = lean_ctor_get(x_2, 5);
x_23 = lean_ctor_get(x_2, 6);
x_24 = lean_ctor_get(x_2, 7);
x_25 = lean_ctor_get(x_2, 8);
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*9 + 1);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_27 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(x_20, x_1);
x_28 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_28, 2, x_19);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_21);
lean_ctor_set(x_28, 5, x_22);
lean_ctor_set(x_28, 6, x_23);
lean_ctor_set(x_28, 7, x_24);
lean_ctor_set(x_28, 8, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*9, x_16);
lean_ctor_set_uint8(x_28, sizeof(void*)*9 + 1, x_26);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_9);
return x_31;
}
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_8__isNextArgHole(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = l_Lean_mkAppStx___closed__1;
x_26 = lean_string_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_8);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_mkAppStx___closed__3;
x_32 = lean_string_dec_eq(x_23, x_31);
lean_dec(x_23);
if (x_32 == 0)
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
lean_dec(x_21);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_8);
return x_36;
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_mkAppStx___closed__5;
x_38 = lean_string_dec_eq(x_22, x_37);
lean_dec(x_22);
if (x_38 == 0)
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_21);
x_39 = 0;
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_1);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_8);
return x_42;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_mkHole___closed__1;
x_44 = lean_string_dec_eq(x_21, x_43);
lean_dec(x_21);
if (x_44 == 0)
{
uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = 0;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_8);
return x_48;
}
else
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = 1;
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_8);
return x_52;
}
}
}
}
}
else
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_53 = 0;
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_8);
return x_56;
}
}
else
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_57 = 0;
x_58 = lean_box(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_8);
return x_60;
}
}
else
{
uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_61 = 0;
x_62 = lean_box(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_1);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_8);
return x_64;
}
}
else
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_17);
lean_dec(x_16);
x_65 = 0;
x_66 = lean_box(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_1);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_8);
return x_68;
}
}
else
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_16);
x_69 = 0;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_1);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_8);
return x_72;
}
}
else
{
uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_15);
x_73 = 0;
x_74 = lean_box(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_1);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_8);
return x_76;
}
}
else
{
uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_14);
x_77 = 0;
x_78 = lean_box(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_1);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_8);
return x_80;
}
}
}
}
lean_object* l___private_Lean_Elab_App_8__isNextArgHole___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_8__isNextArgHole(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_9__addNewArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_13 = l_Lean_mkApp(x_11, x_1);
x_14 = l_Lean_Expr_bindingBody_x21(x_12);
lean_dec(x_12);
x_15 = lean_expr_instantiate1(x_14, x_1);
lean_dec(x_1);
lean_dec(x_14);
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set(x_2, 0, x_13);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*9);
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
x_24 = lean_ctor_get(x_2, 4);
x_25 = lean_ctor_get(x_2, 5);
x_26 = lean_ctor_get(x_2, 6);
x_27 = lean_ctor_get(x_2, 7);
x_28 = lean_ctor_get(x_2, 8);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*9 + 1);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
lean_inc(x_1);
x_30 = l_Lean_mkApp(x_20, x_1);
x_31 = l_Lean_Expr_bindingBody_x21(x_21);
lean_dec(x_21);
x_32 = lean_expr_instantiate1(x_31, x_1);
lean_dec(x_1);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set(x_33, 4, x_24);
lean_ctor_set(x_33, 5, x_25);
lean_ctor_set(x_33, 6, x_26);
lean_ctor_set(x_33, 7, x_27);
lean_ctor_set(x_33, 8, x_28);
lean_ctor_set_uint8(x_33, sizeof(void*)*9, x_19);
lean_ctor_set_uint8(x_33, sizeof(void*)*9 + 1, x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_9);
return x_36;
}
}
}
lean_object* l___private_Lean_Elab_App_9__addNewArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_9__addNewArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_10__elabAndAddNewArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_10 = l___private_Lean_Elab_App_7__getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
lean_inc(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_17 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Elab_Term_elabTerm(x_15, x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_22 = l___private_Lean_Elab_App_1__ensureArgType(x_21, x_19, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Elab_App_9__addNewArg(x_23, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
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
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_dec(x_10);
x_35 = lean_ctor_get(x_11, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_dec(x_11);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_39 = l___private_Lean_Elab_App_1__ensureArgType(x_38, x_37, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Lean_Elab_App_9__addNewArg(x_40, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_4, x_3);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_fget(x_2, x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__3(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
x_26 = l_Lean_Expr_getOptParamDefault_x3f(x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = l_Lean_Expr_getAutoParamTactic_x3f(x_24);
lean_dec(x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_21);
lean_free_object(x_19);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_4, x_28);
lean_dec(x_4);
x_4 = x_29;
x_5 = x_25;
x_12 = x_23;
goto _start;
}
else
{
uint8_t x_31; lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_31 = 1;
x_32 = lean_box(x_31);
lean_ctor_set(x_21, 0, x_32);
return x_19;
}
}
else
{
uint8_t x_33; lean_object* x_34; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_33 = 1;
x_34 = lean_box(x_33);
lean_ctor_set(x_21, 0, x_34);
return x_19;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_19, 1);
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = l_Lean_Expr_getOptParamDefault_x3f(x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = l_Lean_Expr_getAutoParamTactic_x3f(x_36);
lean_dec(x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_free_object(x_19);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_4, x_40);
lean_dec(x_4);
x_4 = x_41;
x_5 = x_37;
x_12 = x_35;
goto _start;
}
else
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_39);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_43 = 1;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_19, 0, x_45);
return x_19;
}
}
else
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_46 = 1;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_37);
lean_ctor_set(x_19, 0, x_48);
return x_19;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_19);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_53 = x_49;
} else {
 lean_dec_ref(x_49);
 x_53 = lean_box(0);
}
x_54 = l_Lean_Expr_getOptParamDefault_x3f(x_51);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = l_Lean_Expr_getAutoParamTactic_x3f(x_51);
lean_dec(x_51);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_53);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_4, x_56);
lean_dec(x_4);
x_4 = x_57;
x_5 = x_52;
x_12 = x_50;
goto _start;
}
else
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_55);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_59 = 1;
x_60 = lean_box(x_59);
if (lean_is_scalar(x_53)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_53;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_52);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_50);
return x_62;
}
}
else
{
uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_63 = 1;
x_64 = lean_box(x_63);
if (lean_is_scalar(x_53)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_53;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_52);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_50);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_19);
if (x_67 == 0)
{
return x_19;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_19, 0);
x_69 = lean_ctor_get(x_19, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_19);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_10(x_1, x_5, x_6, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__2___rarg___lambda__1), 11, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = l___private_Lean_Meta_Basic_20__forallTelescopeReducingImp___rarg(x_1, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_23 = x_19;
} else {
 lean_dec_ref(x_19);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__2___rarg), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_11__hasOptAutoParams___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__1(x_1, x_1, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_App_11__hasOptAutoParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_11__hasOptAutoParams___lambda__1___boxed), 10, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_App_11__hasOptAutoParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Elab_App_11__hasOptAutoParams___closed__1;
x_11 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__2___rarg(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_App_11__hasOptAutoParams___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_11__hasOptAutoParams___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_12__fTypeHasOptAutoParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l___private_Lean_Elab_App_11__hasOptAutoParams___closed__1;
x_11 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__2___rarg(x_9, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
uint8_t l___private_Lean_Elab_App_13__getForallBody___main___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_name_eq(x_3, x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_13__getForallBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_13__getForallBody___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_6);
lean_inc(x_2);
x_11 = l_List_find_x3f___main___rarg(x_10, x_2);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; uint8_t x_13; 
lean_dec(x_6);
x_12 = (uint8_t)((x_9 << 24) >> 61);
x_13 = l_Lean_BinderInfo_isExplicit(x_12);
if (x_13 == 0)
{
lean_dec(x_7);
lean_dec(x_3);
x_3 = x_8;
goto _start;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_4, x_1);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Expr_isAutoParam(x_7);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Expr_isOptParam(x_7);
lean_dec(x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_3);
return x_18;
}
else
{
lean_dec(x_3);
x_3 = x_8;
goto _start;
}
}
else
{
lean_dec(x_7);
lean_dec(x_3);
x_3 = x_8;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_3);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_1, x_21);
lean_dec(x_1);
x_1 = x_22;
x_3 = x_8;
goto _start;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_3);
x_24 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(x_2, x_6);
lean_dec(x_6);
x_2 = x_24;
x_3 = x_8;
goto _start;
}
}
else
{
lean_object* x_26; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(0);
return x_26;
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 2);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_27);
x_31 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_13__getForallBody___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_31, 0, x_27);
x_32 = l_List_find_x3f___main___rarg(x_31, x_2);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; uint8_t x_34; 
lean_dec(x_27);
x_33 = (uint8_t)((x_30 << 24) >> 61);
x_34 = l_Lean_BinderInfo_isExplicit(x_33);
if (x_34 == 0)
{
lean_dec(x_28);
lean_dec(x_3);
x_1 = x_4;
x_3 = x_29;
goto _start;
}
else
{
uint8_t x_36; 
x_36 = l_Lean_Expr_isAutoParam(x_28);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Expr_isOptParam(x_28);
lean_dec(x_28);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_3);
return x_38;
}
else
{
lean_dec(x_3);
x_1 = x_4;
x_3 = x_29;
goto _start;
}
}
else
{
lean_dec(x_28);
lean_dec(x_3);
x_1 = x_4;
x_3 = x_29;
goto _start;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_41 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(x_2, x_27);
lean_dec(x_27);
x_1 = x_4;
x_2 = x_41;
x_3 = x_29;
goto _start;
}
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_3);
return x_43;
}
}
else
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_3, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 2);
lean_inc(x_46);
x_47 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_44);
x_48 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_13__getForallBody___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_48, 0, x_44);
lean_inc(x_2);
x_49 = l_List_find_x3f___main___rarg(x_48, x_2);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; uint8_t x_51; 
lean_dec(x_44);
x_50 = (uint8_t)((x_47 << 24) >> 61);
x_51 = l_Lean_BinderInfo_isExplicit(x_50);
if (x_51 == 0)
{
lean_dec(x_45);
lean_dec(x_3);
x_1 = x_4;
x_3 = x_46;
goto _start;
}
else
{
uint8_t x_53; 
x_53 = l_Lean_Expr_isAutoParam(x_45);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = l_Lean_Expr_isOptParam(x_45);
lean_dec(x_45);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_46);
lean_dec(x_2);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_3);
return x_55;
}
else
{
lean_dec(x_3);
x_1 = x_4;
x_3 = x_46;
goto _start;
}
}
else
{
lean_dec(x_45);
lean_dec(x_3);
x_1 = x_4;
x_3 = x_46;
goto _start;
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_49);
lean_dec(x_45);
lean_dec(x_3);
x_58 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(x_2, x_44);
lean_dec(x_44);
x_1 = x_4;
x_2 = x_58;
x_3 = x_46;
goto _start;
}
}
else
{
lean_object* x_60; 
lean_dec(x_3);
lean_dec(x_2);
x_60 = lean_box(0);
return x_60;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_13__getForallBody___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_App_13__getForallBody___main___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_13__getForallBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_App_13__getForallBody___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__2(x_1, x_4);
if (x_5 == 0)
{
return x_3;
}
else
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
}
else
{
return x_3;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_Expr_hasMVar(x_7);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasMVar(x_8);
if (x_10 == 0)
{
return x_3;
}
else
{
x_2 = x_8;
goto _start;
}
}
else
{
lean_object* x_12; 
x_12 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__1(x_1, x_7, x_3);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Expr_hasMVar(x_8);
if (x_13 == 0)
{
return x_12;
}
else
{
x_2 = x_8;
x_3 = x_12;
goto _start;
}
}
else
{
return x_12;
}
}
}
else
{
return x_3;
}
}
case 6:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
x_17 = l_Lean_Expr_hasMVar(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_Expr_hasMVar(x_16);
if (x_18 == 0)
{
return x_3;
}
else
{
x_2 = x_16;
goto _start;
}
}
else
{
lean_object* x_20; 
x_20 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__1(x_1, x_15, x_3);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Expr_hasMVar(x_16);
if (x_21 == 0)
{
return x_20;
}
else
{
x_2 = x_16;
x_3 = x_20;
goto _start;
}
}
else
{
return x_20;
}
}
}
else
{
return x_3;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = l_Lean_Expr_hasMVar(x_23);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Expr_hasMVar(x_24);
if (x_26 == 0)
{
return x_3;
}
else
{
x_2 = x_24;
goto _start;
}
}
else
{
lean_object* x_28; 
x_28 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__1(x_1, x_23, x_3);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Expr_hasMVar(x_24);
if (x_29 == 0)
{
return x_28;
}
else
{
x_2 = x_24;
x_3 = x_28;
goto _start;
}
}
else
{
return x_28;
}
}
}
else
{
return x_3;
}
}
case 8:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_2, 1);
x_32 = lean_ctor_get(x_2, 2);
x_33 = lean_ctor_get(x_2, 3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_42; 
x_42 = l_Lean_Expr_hasMVar(x_31);
if (x_42 == 0)
{
x_34 = x_3;
goto block_41;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__1(x_1, x_31, x_3);
if (lean_obj_tag(x_43) == 0)
{
x_34 = x_43;
goto block_41;
}
else
{
return x_43;
}
}
}
else
{
return x_3;
}
block_41:
{
uint8_t x_35; 
x_35 = l_Lean_Expr_hasMVar(x_32);
if (x_35 == 0)
{
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Expr_hasMVar(x_33);
if (x_36 == 0)
{
return x_34;
}
else
{
x_2 = x_33;
x_3 = x_34;
goto _start;
}
}
else
{
return x_34;
}
}
else
{
lean_object* x_38; 
x_38 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__1(x_1, x_32, x_34);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = l_Lean_Expr_hasMVar(x_33);
if (x_39 == 0)
{
return x_38;
}
else
{
x_2 = x_33;
x_3 = x_38;
goto _start;
}
}
else
{
return x_38;
}
}
}
}
case 10:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_2, 1);
x_45 = l_Lean_Expr_hasMVar(x_44);
if (x_45 == 0)
{
return x_3;
}
else
{
x_2 = x_44;
goto _start;
}
}
else
{
return x_3;
}
}
case 11:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_2, 2);
x_48 = l_Lean_Expr_hasMVar(x_47);
if (x_48 == 0)
{
return x_3;
}
else
{
x_2 = x_47;
goto _start;
}
}
else
{
return x_3;
}
}
default: 
{
return x_3;
}
}
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__2(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
return x_3;
}
}
else
{
return x_3;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_Expr_hasMVar(x_7);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasMVar(x_8);
if (x_10 == 0)
{
return x_3;
}
else
{
x_2 = x_8;
goto _start;
}
}
else
{
lean_object* x_12; 
x_12 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__2(x_1, x_7, x_3);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Expr_hasMVar(x_8);
if (x_13 == 0)
{
return x_12;
}
else
{
x_2 = x_8;
x_3 = x_12;
goto _start;
}
}
else
{
return x_12;
}
}
}
else
{
return x_3;
}
}
case 6:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
x_17 = l_Lean_Expr_hasMVar(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_Expr_hasMVar(x_16);
if (x_18 == 0)
{
return x_3;
}
else
{
x_2 = x_16;
goto _start;
}
}
else
{
lean_object* x_20; 
x_20 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__2(x_1, x_15, x_3);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Expr_hasMVar(x_16);
if (x_21 == 0)
{
return x_20;
}
else
{
x_2 = x_16;
x_3 = x_20;
goto _start;
}
}
else
{
return x_20;
}
}
}
else
{
return x_3;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = l_Lean_Expr_hasMVar(x_23);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Expr_hasMVar(x_24);
if (x_26 == 0)
{
return x_3;
}
else
{
x_2 = x_24;
goto _start;
}
}
else
{
lean_object* x_28; 
x_28 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__2(x_1, x_23, x_3);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Expr_hasMVar(x_24);
if (x_29 == 0)
{
return x_28;
}
else
{
x_2 = x_24;
x_3 = x_28;
goto _start;
}
}
else
{
return x_28;
}
}
}
else
{
return x_3;
}
}
case 8:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_2, 1);
x_32 = lean_ctor_get(x_2, 2);
x_33 = lean_ctor_get(x_2, 3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_42; 
x_42 = l_Lean_Expr_hasMVar(x_31);
if (x_42 == 0)
{
x_34 = x_3;
goto block_41;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__2(x_1, x_31, x_3);
if (lean_obj_tag(x_43) == 0)
{
x_34 = x_43;
goto block_41;
}
else
{
return x_43;
}
}
}
else
{
return x_3;
}
block_41:
{
uint8_t x_35; 
x_35 = l_Lean_Expr_hasMVar(x_32);
if (x_35 == 0)
{
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Expr_hasMVar(x_33);
if (x_36 == 0)
{
return x_34;
}
else
{
x_2 = x_33;
x_3 = x_34;
goto _start;
}
}
else
{
return x_34;
}
}
else
{
lean_object* x_38; 
x_38 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__2(x_1, x_32, x_34);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = l_Lean_Expr_hasMVar(x_33);
if (x_39 == 0)
{
return x_38;
}
else
{
x_2 = x_33;
x_3 = x_38;
goto _start;
}
}
else
{
return x_38;
}
}
}
}
case 10:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_2, 1);
x_45 = l_Lean_Expr_hasMVar(x_44);
if (x_45 == 0)
{
return x_3;
}
else
{
x_2 = x_44;
goto _start;
}
}
else
{
return x_3;
}
}
case 11:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_2, 2);
x_48 = l_Lean_Expr_hasMVar(x_47);
if (x_48 == 0)
{
return x_3;
}
else
{
x_2 = x_47;
goto _start;
}
}
else
{
return x_3;
}
}
default: 
{
return x_3;
}
}
}
}
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
lean_inc(x_2);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux), 8, 2);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
x_210 = lean_st_ref_get(x_9, x_10);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_211, 3);
lean_inc(x_212);
lean_dec(x_211);
x_213 = lean_ctor_get_uint8(x_212, sizeof(void*)*1);
lean_dec(x_212);
if (x_213 == 0)
{
lean_object* x_214; uint8_t x_215; 
x_214 = lean_ctor_get(x_210, 1);
lean_inc(x_214);
lean_dec(x_210);
x_215 = 0;
x_25 = x_215;
x_26 = x_214;
goto block_209;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_216 = lean_ctor_get(x_210, 1);
lean_inc(x_216);
lean_dec(x_210);
x_217 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_218 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_217, x_6, x_7, x_8, x_9, x_216);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = lean_unbox(x_219);
lean_dec(x_219);
x_25 = x_221;
x_26 = x_220;
goto block_209;
}
block_23:
{
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_3);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
block_209:
{
if (x_25 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_27 = lean_st_ref_get(x_9, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 3);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_ctor_get_uint8(x_29, sizeof(void*)*1);
lean_dec(x_29);
x_66 = lean_st_ref_take(x_9, x_30);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_67, 3);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_68);
if (x_72 == 0)
{
uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = 0;
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_73);
x_74 = lean_st_ref_set(x_9, x_67, x_69);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_76 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_24, x_6, x_7, x_8, x_9, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_77);
x_79 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_79, 0, x_1);
lean_closure_set(x_79, 1, x_2);
lean_closure_set(x_79, 2, x_77);
x_80 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_81 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_80, x_79, x_6, x_7, x_8, x_9, x_78);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_st_ref_get(x_9, x_82);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_st_ref_take(x_9, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 3);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_86, 3);
lean_dec(x_90);
x_91 = !lean_is_exclusive(x_87);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_31);
x_92 = lean_st_ref_set(x_9, x_86, x_88);
lean_dec(x_9);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_92, 0);
lean_dec(x_94);
lean_ctor_set(x_92, 0, x_77);
x_11 = x_92;
goto block_23;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_77);
lean_ctor_set(x_96, 1, x_95);
x_11 = x_96;
goto block_23;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_87, 0);
lean_inc(x_97);
lean_dec(x_87);
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_31);
lean_ctor_set(x_86, 3, x_98);
x_99 = lean_st_ref_set(x_9, x_86, x_88);
lean_dec(x_9);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_77);
lean_ctor_set(x_102, 1, x_100);
x_11 = x_102;
goto block_23;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_103 = lean_ctor_get(x_86, 0);
x_104 = lean_ctor_get(x_86, 1);
x_105 = lean_ctor_get(x_86, 2);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_86);
x_106 = lean_ctor_get(x_87, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_107 = x_87;
} else {
 lean_dec_ref(x_87);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 1, 1);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set_uint8(x_108, sizeof(void*)*1, x_31);
x_109 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_109, 0, x_103);
lean_ctor_set(x_109, 1, x_104);
lean_ctor_set(x_109, 2, x_105);
lean_ctor_set(x_109, 3, x_108);
x_110 = lean_st_ref_set(x_9, x_109, x_88);
lean_dec(x_9);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_77);
lean_ctor_set(x_113, 1, x_111);
x_11 = x_113;
goto block_23;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_114 = lean_ctor_get(x_76, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_76, 1);
lean_inc(x_115);
lean_dec(x_76);
x_32 = x_114;
x_33 = x_115;
goto block_65;
}
}
else
{
lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_116 = lean_ctor_get(x_68, 0);
lean_inc(x_116);
lean_dec(x_68);
x_117 = 0;
x_118 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_117);
lean_ctor_set(x_67, 3, x_118);
x_119 = lean_st_ref_set(x_9, x_67, x_69);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_121 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_24, x_6, x_7, x_8, x_9, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
lean_inc(x_122);
x_124 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_124, 0, x_1);
lean_closure_set(x_124, 1, x_2);
lean_closure_set(x_124, 2, x_122);
x_125 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_126 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_125, x_124, x_6, x_7, x_8, x_9, x_123);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_128 = lean_st_ref_get(x_9, x_127);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_st_ref_take(x_9, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_131, 2);
lean_inc(x_136);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 x_137 = x_131;
} else {
 lean_dec_ref(x_131);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_132, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_139 = x_132;
} else {
 lean_dec_ref(x_132);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(0, 1, 1);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*1, x_31);
if (lean_is_scalar(x_137)) {
 x_141 = lean_alloc_ctor(0, 4, 0);
} else {
 x_141 = x_137;
}
lean_ctor_set(x_141, 0, x_134);
lean_ctor_set(x_141, 1, x_135);
lean_ctor_set(x_141, 2, x_136);
lean_ctor_set(x_141, 3, x_140);
x_142 = lean_st_ref_set(x_9, x_141, x_133);
lean_dec(x_9);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_144 = x_142;
} else {
 lean_dec_ref(x_142);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_122);
lean_ctor_set(x_145, 1, x_143);
x_11 = x_145;
goto block_23;
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_146 = lean_ctor_get(x_121, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_121, 1);
lean_inc(x_147);
lean_dec(x_121);
x_32 = x_146;
x_33 = x_147;
goto block_65;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_148 = lean_ctor_get(x_67, 0);
x_149 = lean_ctor_get(x_67, 1);
x_150 = lean_ctor_get(x_67, 2);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_67);
x_151 = lean_ctor_get(x_68, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_152 = x_68;
} else {
 lean_dec_ref(x_68);
 x_152 = lean_box(0);
}
x_153 = 0;
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(0, 1, 1);
} else {
 x_154 = x_152;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set_uint8(x_154, sizeof(void*)*1, x_153);
x_155 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_155, 0, x_148);
lean_ctor_set(x_155, 1, x_149);
lean_ctor_set(x_155, 2, x_150);
lean_ctor_set(x_155, 3, x_154);
x_156 = lean_st_ref_set(x_9, x_155, x_69);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_158 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_24, x_6, x_7, x_8, x_9, x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_159);
x_161 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_161, 0, x_1);
lean_closure_set(x_161, 1, x_2);
lean_closure_set(x_161, 2, x_159);
x_162 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_163 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_162, x_161, x_6, x_7, x_8, x_9, x_160);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_165 = lean_st_ref_get(x_9, x_164);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_167 = lean_st_ref_take(x_9, x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_168, 3);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
lean_dec(x_167);
x_171 = lean_ctor_get(x_168, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_168, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_168, 2);
lean_inc(x_173);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 lean_ctor_release(x_168, 3);
 x_174 = x_168;
} else {
 lean_dec_ref(x_168);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_169, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_176 = x_169;
} else {
 lean_dec_ref(x_169);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 1, 1);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set_uint8(x_177, sizeof(void*)*1, x_31);
if (lean_is_scalar(x_174)) {
 x_178 = lean_alloc_ctor(0, 4, 0);
} else {
 x_178 = x_174;
}
lean_ctor_set(x_178, 0, x_171);
lean_ctor_set(x_178, 1, x_172);
lean_ctor_set(x_178, 2, x_173);
lean_ctor_set(x_178, 3, x_177);
x_179 = lean_st_ref_set(x_9, x_178, x_170);
lean_dec(x_9);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_159);
lean_ctor_set(x_182, 1, x_180);
x_11 = x_182;
goto block_23;
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_183 = lean_ctor_get(x_158, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_158, 1);
lean_inc(x_184);
lean_dec(x_158);
x_32 = x_183;
x_33 = x_184;
goto block_65;
}
}
block_65:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_st_ref_get(x_9, x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_take(x_9, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_37, 3);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_31);
x_43 = lean_st_ref_set(x_9, x_37, x_39);
lean_dec(x_9);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 0, x_32);
x_11 = x_43;
goto block_23;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_32);
lean_ctor_set(x_47, 1, x_46);
x_11 = x_47;
goto block_23;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_31);
lean_ctor_set(x_37, 3, x_49);
x_50 = lean_st_ref_set(x_9, x_37, x_39);
lean_dec(x_9);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
 lean_ctor_set_tag(x_53, 1);
}
lean_ctor_set(x_53, 0, x_32);
lean_ctor_set(x_53, 1, x_51);
x_11 = x_53;
goto block_23;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_37, 0);
x_55 = lean_ctor_get(x_37, 1);
x_56 = lean_ctor_get(x_37, 2);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_37);
x_57 = lean_ctor_get(x_38, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_58 = x_38;
} else {
 lean_dec_ref(x_38);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 1, 1);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_31);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_56);
lean_ctor_set(x_60, 3, x_59);
x_61 = lean_st_ref_set(x_9, x_60, x_39);
lean_dec(x_9);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
 lean_ctor_set_tag(x_64, 1);
}
lean_ctor_set(x_64, 0, x_32);
lean_ctor_set(x_64, 1, x_62);
x_11 = x_64;
goto block_23;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_185 = lean_ctor_get(x_8, 3);
lean_inc(x_185);
x_186 = l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(x_9, x_26);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_189 = l___private_Lean_Meta_LevelDefEq_15__runDefEqM(x_24, x_6, x_7, x_8, x_9, x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
lean_inc(x_190);
x_192 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_192, 0, x_1);
lean_closure_set(x_192, 1, x_2);
lean_closure_set(x_192, 2, x_190);
x_193 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_194 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_193, x_192, x_6, x_7, x_8, x_9, x_191);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_196 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_187, x_193, x_185, x_6, x_7, x_8, x_9, x_195);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_197 = !lean_is_exclusive(x_196);
if (x_197 == 0)
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_196, 0);
lean_dec(x_198);
lean_ctor_set(x_196, 0, x_190);
x_11 = x_196;
goto block_23;
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_dec(x_196);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_190);
lean_ctor_set(x_200, 1, x_199);
x_11 = x_200;
goto block_23;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
lean_dec(x_2);
lean_dec(x_1);
x_201 = lean_ctor_get(x_189, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_189, 1);
lean_inc(x_202);
lean_dec(x_189);
x_203 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_204 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_187, x_203, x_185, x_6, x_7, x_8, x_9, x_202);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_205 = !lean_is_exclusive(x_204);
if (x_205 == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_204, 0);
lean_dec(x_206);
lean_ctor_set_tag(x_204, 1);
lean_ctor_set(x_204, 0, x_201);
x_11 = x_204;
goto block_23;
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_204, 1);
lean_inc(x_207);
lean_dec(x_204);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_201);
lean_ctor_set(x_208, 1, x_207);
x_11 = x_208;
goto block_23;
}
}
}
}
}
}
lean_object* l_Lean_Elab_logAt___at___private_Lean_Elab_App_14__propagateExpectedType___spec__6(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 3);
x_13 = l_Lean_replaceRef(x_1, x_12);
x_14 = l_Lean_Syntax_getPos(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
x_18 = lean_ctor_get(x_5, 5);
x_19 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_FileMap_toPosition(x_16, x_22);
x_24 = lean_box(0);
lean_inc(x_18);
lean_inc(x_17);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_18);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
x_27 = l_String_splitAux___main___closed__1;
lean_inc(x_15);
x_28 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*5, x_3);
x_29 = lean_st_ref_take(x_6, x_21);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_30, 2);
x_34 = l_Std_PersistentArray_push___rarg(x_33, x_28);
lean_ctor_set(x_30, 2, x_34);
x_35 = lean_st_ref_set(x_6, x_30, x_31);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_4);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_4);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
x_46 = lean_ctor_get(x_30, 2);
x_47 = lean_ctor_get(x_30, 3);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_48 = l_Std_PersistentArray_push___rarg(x_46, x_28);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_47);
x_50 = lean_st_ref_set(x_6, x_49, x_31);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_4);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_56 = lean_ctor_get(x_14, 0);
lean_inc(x_56);
lean_dec(x_14);
x_57 = lean_ctor_get(x_5, 0);
x_58 = lean_ctor_get(x_5, 1);
x_59 = lean_ctor_get(x_5, 2);
x_60 = lean_ctor_get(x_5, 5);
x_61 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_FileMap_toPosition(x_58, x_56);
x_65 = lean_box(0);
lean_inc(x_60);
lean_inc(x_59);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_59);
lean_ctor_set(x_66, 1, x_60);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
x_68 = l_String_splitAux___main___closed__1;
lean_inc(x_57);
x_69 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_69, 0, x_57);
lean_ctor_set(x_69, 1, x_64);
lean_ctor_set(x_69, 2, x_65);
lean_ctor_set(x_69, 3, x_68);
lean_ctor_set(x_69, 4, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*5, x_3);
x_70 = lean_st_ref_take(x_6, x_63);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_71, 2);
x_75 = l_Std_PersistentArray_push___rarg(x_74, x_69);
lean_ctor_set(x_71, 2, x_75);
x_76 = lean_st_ref_set(x_6, x_71, x_72);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_4);
lean_ctor_set(x_76, 0, x_80);
return x_76;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
lean_dec(x_76);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_4);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_85 = lean_ctor_get(x_71, 0);
x_86 = lean_ctor_get(x_71, 1);
x_87 = lean_ctor_get(x_71, 2);
x_88 = lean_ctor_get(x_71, 3);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_71);
x_89 = l_Std_PersistentArray_push___rarg(x_87, x_69);
x_90 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_90, 0, x_85);
lean_ctor_set(x_90, 1, x_86);
lean_ctor_set(x_90, 2, x_89);
lean_ctor_set(x_90, 3, x_88);
x_91 = lean_st_ref_set(x_6, x_90, x_72);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_4);
if (lean_is_scalar(x_93)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_93;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_92);
return x_96;
}
}
}
}
lean_object* l_Lean_Elab_log___at___private_Lean_Elab_App_14__propagateExpectedType___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_Elab_logAt___at___private_Lean_Elab_App_14__propagateExpectedType___spec__6(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
x_12 = 0;
x_13 = l_Lean_Elab_log___at___private_Lean_Elab_App_14__propagateExpectedType___spec__5(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_6__regTraceClasses___closed__1;
x_2 = l_Lean_mkAppStx___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("propagateExpectedType");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__1;
x_2 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("etaArgs.size: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", numRemainingArgs: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", fType: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_14__propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*9);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 6);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 7);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 8);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 1);
x_20 = l_Array_isEmpty___rarg(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
else
{
if (x_19 == 0)
{
uint8_t x_24; 
x_24 = l_Array_isEmpty___rarg(x_18);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_26 = lean_ctor_get(x_1, 8);
lean_dec(x_26);
x_27 = lean_ctor_get(x_1, 7);
lean_dec(x_27);
x_28 = lean_ctor_get(x_1, 6);
lean_dec(x_28);
x_29 = lean_ctor_get(x_1, 5);
lean_dec(x_29);
x_30 = lean_ctor_get(x_1, 4);
lean_dec(x_30);
x_31 = lean_ctor_get(x_1, 3);
lean_dec(x_31);
x_32 = lean_ctor_get(x_1, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_1, 0);
lean_dec(x_34);
x_35 = 1;
lean_inc(x_18);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_ctor_set_uint8(x_1, sizeof(void*)*9 + 1, x_35);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_8);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_39 = lean_ctor_get(x_14, 0);
lean_inc(x_39);
lean_dec(x_14);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_List_lengthAux___main___rarg(x_12, x_40);
lean_dec(x_12);
x_214 = lean_ctor_get(x_6, 0);
lean_inc(x_214);
x_215 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__3;
x_216 = l_Lean_checkTraceOption(x_214, x_215);
lean_dec(x_214);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_15);
x_217 = lean_box(0);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_1);
x_42 = x_218;
x_43 = x_8;
goto block_213;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_219 = lean_array_get_size(x_15);
lean_dec(x_15);
x_220 = l_Nat_repr(x_219);
x_221 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_221, 0, x_220);
x_222 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_222, 0, x_221);
x_223 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__6;
x_224 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_222);
x_225 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__9;
x_226 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
lean_inc(x_41);
x_227 = l_Nat_repr(x_41);
x_228 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_228, 0, x_227);
x_229 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_229, 0, x_228);
x_230 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_230, 0, x_226);
lean_ctor_set(x_230, 1, x_229);
x_231 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__12;
x_232 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
lean_inc(x_11);
x_233 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_233, 0, x_11);
x_234 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_215, x_234, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_42 = x_236;
x_43 = x_237;
goto block_213;
}
block_213:
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_42, 1);
x_46 = lean_ctor_get(x_42, 0);
lean_dec(x_46);
x_47 = l___private_Lean_Elab_App_13__getForallBody___main(x_41, x_13, x_11);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_39);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_box(0);
lean_ctor_set(x_42, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_43);
return x_49;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l_Lean_Expr_hasLooseBVars(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_box(0);
x_53 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__1(x_18, x_50, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_50);
lean_dec(x_39);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_box(0);
lean_ctor_set(x_42, 0, x_54);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_42);
lean_ctor_set(x_55, 1, x_43);
return x_55;
}
else
{
lean_object* x_56; 
lean_dec(x_53);
x_56 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__2(x_18, x_50, x_52);
lean_dec(x_18);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_free_object(x_42);
x_57 = l___private_Lean_Elab_App_11__hasOptAutoParams___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_50);
x_58 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__2___rarg(x_50, x_57, x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_43);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_ctor_get(x_6, 0);
lean_inc(x_64);
x_65 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__3;
x_66 = l_Lean_checkTraceOption(x_64, x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_39, x_50, x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_62);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
x_72 = lean_box(0);
lean_ctor_set(x_69, 0, x_72);
return x_67;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
lean_ctor_set(x_67, 0, x_75);
return x_67;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_ctor_get(x_67, 0);
x_77 = lean_ctor_get(x_67, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_67);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = lean_box(0);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_78);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_77);
return x_82;
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_67);
if (x_83 == 0)
{
return x_67;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_67, 0);
x_85 = lean_ctor_get(x_67, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_67);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_inc(x_39);
x_87 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_87, 0, x_39);
x_88 = l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__3;
x_89 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
lean_inc(x_50);
x_90 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_90, 0, x_50);
x_91 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_65, x_91, x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_62);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_39, x_50, x_95, x_2, x_3, x_4, x_5, x_6, x_7, x_94);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 0);
lean_dec(x_100);
x_101 = lean_box(0);
lean_ctor_set(x_98, 0, x_101);
return x_96;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_dec(x_98);
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
lean_ctor_set(x_96, 0, x_104);
return x_96;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_105 = lean_ctor_get(x_96, 0);
x_106 = lean_ctor_get(x_96, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_96);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_109 = lean_box(0);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_106);
return x_111;
}
}
else
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_96);
if (x_112 == 0)
{
return x_96;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_96, 0);
x_114 = lean_ctor_get(x_96, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_96);
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
lean_dec(x_50);
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_116 = !lean_is_exclusive(x_58);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_58, 0);
lean_dec(x_117);
x_118 = !lean_is_exclusive(x_59);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_59, 0);
lean_dec(x_119);
x_120 = lean_box(0);
lean_ctor_set(x_59, 0, x_120);
return x_58;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_59, 1);
lean_inc(x_121);
lean_dec(x_59);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
lean_ctor_set(x_58, 0, x_123);
return x_58;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_124 = lean_ctor_get(x_58, 1);
lean_inc(x_124);
lean_dec(x_58);
x_125 = lean_ctor_get(x_59, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_126 = x_59;
} else {
 lean_dec_ref(x_59);
 x_126 = lean_box(0);
}
x_127 = lean_box(0);
if (lean_is_scalar(x_126)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_126;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_124);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_50);
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_130 = !lean_is_exclusive(x_58);
if (x_130 == 0)
{
return x_58;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_58, 0);
x_132 = lean_ctor_get(x_58, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_58);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_56);
lean_dec(x_50);
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_134 = lean_box(0);
lean_ctor_set(x_42, 0, x_134);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_42);
lean_ctor_set(x_135, 1, x_43);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_50);
lean_dec(x_39);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_136 = lean_box(0);
lean_ctor_set(x_42, 0, x_136);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_42);
lean_ctor_set(x_137, 1, x_43);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_42, 1);
lean_inc(x_138);
lean_dec(x_42);
x_139 = l___private_Lean_Elab_App_13__getForallBody___main(x_41, x_13, x_11);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_39);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_138);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_43);
return x_142;
}
else
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_139, 0);
lean_inc(x_143);
lean_dec(x_139);
x_144 = l_Lean_Expr_hasLooseBVars(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_box(0);
x_146 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__1(x_18, x_143, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_143);
lean_dec(x_39);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_138);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_43);
return x_149;
}
else
{
lean_object* x_150; 
lean_dec(x_146);
x_150 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__2(x_18, x_143, x_145);
lean_dec(x_18);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = l___private_Lean_Elab_App_11__hasOptAutoParams___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_143);
x_152 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__2___rarg(x_143, x_151, x_138, x_2, x_3, x_4, x_5, x_6, x_7, x_43);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_unbox(x_154);
lean_dec(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_156 = lean_ctor_get(x_152, 1);
lean_inc(x_156);
lean_dec(x_152);
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
lean_dec(x_153);
x_158 = lean_ctor_get(x_6, 0);
lean_inc(x_158);
x_159 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__3;
x_160 = l_Lean_checkTraceOption(x_158, x_159);
lean_dec(x_158);
if (x_160 == 0)
{
lean_object* x_161; 
x_161 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_39, x_143, x_157, x_2, x_3, x_4, x_5, x_6, x_7, x_156);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_164 = x_161;
} else {
 lean_dec_ref(x_161);
 x_164 = lean_box(0);
}
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_166 = x_162;
} else {
 lean_dec_ref(x_162);
 x_166 = lean_box(0);
}
x_167 = lean_box(0);
if (lean_is_scalar(x_166)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_166;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_165);
if (lean_is_scalar(x_164)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_164;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_163);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_161, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_161, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_172 = x_161;
} else {
 lean_dec_ref(x_161);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_inc(x_39);
x_174 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_174, 0, x_39);
x_175 = l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__3;
x_176 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
lean_inc(x_143);
x_177 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_177, 0, x_143);
x_178 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_159, x_178, x_157, x_2, x_3, x_4, x_5, x_6, x_7, x_156);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_39, x_143, x_182, x_2, x_3, x_4, x_5, x_6, x_7, x_181);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_188 = x_184;
} else {
 lean_dec_ref(x_184);
 x_188 = lean_box(0);
}
x_189 = lean_box(0);
if (lean_is_scalar(x_188)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_188;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_187);
if (lean_is_scalar(x_186)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_186;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_185);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_ctor_get(x_183, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_183, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_194 = x_183;
} else {
 lean_dec_ref(x_183);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_143);
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_196 = lean_ctor_get(x_152, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_197 = x_152;
} else {
 lean_dec_ref(x_152);
 x_197 = lean_box(0);
}
x_198 = lean_ctor_get(x_153, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_199 = x_153;
} else {
 lean_dec_ref(x_153);
 x_199 = lean_box(0);
}
x_200 = lean_box(0);
if (lean_is_scalar(x_199)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_199;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_198);
if (lean_is_scalar(x_197)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_197;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_196);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_143);
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_203 = lean_ctor_get(x_152, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_152, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_205 = x_152;
} else {
 lean_dec_ref(x_152);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_150);
lean_dec(x_143);
lean_dec(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_207 = lean_box(0);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_138);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_43);
return x_209;
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_143);
lean_dec(x_39);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_210 = lean_box(0);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_138);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_43);
return x_212;
}
}
}
}
}
}
else
{
uint8_t x_238; lean_object* x_239; 
lean_dec(x_1);
x_238 = 1;
lean_inc(x_18);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_239 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_239, 0, x_10);
lean_ctor_set(x_239, 1, x_11);
lean_ctor_set(x_239, 2, x_12);
lean_ctor_set(x_239, 3, x_13);
lean_ctor_set(x_239, 4, x_14);
lean_ctor_set(x_239, 5, x_15);
lean_ctor_set(x_239, 6, x_16);
lean_ctor_set(x_239, 7, x_17);
lean_ctor_set(x_239, 8, x_18);
lean_ctor_set_uint8(x_239, sizeof(void*)*9, x_9);
lean_ctor_set_uint8(x_239, sizeof(void*)*9 + 1, x_238);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_240 = lean_box(0);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_8);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_243 = lean_ctor_get(x_14, 0);
lean_inc(x_243);
lean_dec(x_14);
x_244 = lean_unsigned_to_nat(0u);
x_245 = l_List_lengthAux___main___rarg(x_12, x_244);
lean_dec(x_12);
x_325 = lean_ctor_get(x_6, 0);
lean_inc(x_325);
x_326 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__3;
x_327 = l_Lean_checkTraceOption(x_325, x_326);
lean_dec(x_325);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; 
lean_dec(x_15);
x_328 = lean_box(0);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_239);
x_246 = x_329;
x_247 = x_8;
goto block_324;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_330 = lean_array_get_size(x_15);
lean_dec(x_15);
x_331 = l_Nat_repr(x_330);
x_332 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_332, 0, x_331);
x_333 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_333, 0, x_332);
x_334 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__6;
x_335 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_333);
x_336 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__9;
x_337 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
lean_inc(x_245);
x_338 = l_Nat_repr(x_245);
x_339 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_339, 0, x_338);
x_340 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_340, 0, x_339);
x_341 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_341, 0, x_337);
lean_ctor_set(x_341, 1, x_340);
x_342 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__12;
x_343 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
lean_inc(x_11);
x_344 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_344, 0, x_11);
x_345 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
x_346 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_326, x_345, x_239, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
x_246 = x_347;
x_247 = x_348;
goto block_324;
}
block_324:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_249 = x_246;
} else {
 lean_dec_ref(x_246);
 x_249 = lean_box(0);
}
x_250 = l___private_Lean_Elab_App_13__getForallBody___main(x_245, x_13, x_11);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_243);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_251 = lean_box(0);
if (lean_is_scalar(x_249)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_249;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_248);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_247);
return x_253;
}
else
{
lean_object* x_254; uint8_t x_255; 
x_254 = lean_ctor_get(x_250, 0);
lean_inc(x_254);
lean_dec(x_250);
x_255 = l_Lean_Expr_hasLooseBVars(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_box(0);
x_257 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__1(x_18, x_254, x_256);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_254);
lean_dec(x_243);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_258 = lean_box(0);
if (lean_is_scalar(x_249)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_249;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_248);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_247);
return x_260;
}
else
{
lean_object* x_261; 
lean_dec(x_257);
x_261 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__2(x_18, x_254, x_256);
lean_dec(x_18);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_249);
x_262 = l___private_Lean_Elab_App_11__hasOptAutoParams___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_254);
x_263 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_11__hasOptAutoParams___spec__2___rarg(x_254, x_262, x_248, x_2, x_3, x_4, x_5, x_6, x_7, x_247);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_unbox(x_265);
lean_dec(x_265);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_267 = lean_ctor_get(x_263, 1);
lean_inc(x_267);
lean_dec(x_263);
x_268 = lean_ctor_get(x_264, 1);
lean_inc(x_268);
lean_dec(x_264);
x_269 = lean_ctor_get(x_6, 0);
lean_inc(x_269);
x_270 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__3;
x_271 = l_Lean_checkTraceOption(x_269, x_270);
lean_dec(x_269);
if (x_271 == 0)
{
lean_object* x_272; 
x_272 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_243, x_254, x_268, x_2, x_3, x_4, x_5, x_6, x_7, x_267);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
x_276 = lean_ctor_get(x_273, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_277 = x_273;
} else {
 lean_dec_ref(x_273);
 x_277 = lean_box(0);
}
x_278 = lean_box(0);
if (lean_is_scalar(x_277)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_277;
}
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_276);
if (lean_is_scalar(x_275)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_275;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_274);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_281 = lean_ctor_get(x_272, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_272, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_283 = x_272;
} else {
 lean_dec_ref(x_272);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_inc(x_243);
x_285 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_285, 0, x_243);
x_286 = l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__3;
x_287 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
lean_inc(x_254);
x_288 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_288, 0, x_254);
x_289 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
x_290 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_270, x_289, x_268, x_2, x_3, x_4, x_5, x_6, x_7, x_267);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
x_294 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_243, x_254, x_293, x_2, x_3, x_4, x_5, x_6, x_7, x_292);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 x_297 = x_294;
} else {
 lean_dec_ref(x_294);
 x_297 = lean_box(0);
}
x_298 = lean_ctor_get(x_295, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_299 = x_295;
} else {
 lean_dec_ref(x_295);
 x_299 = lean_box(0);
}
x_300 = lean_box(0);
if (lean_is_scalar(x_299)) {
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_299;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_298);
if (lean_is_scalar(x_297)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_297;
}
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_296);
return x_302;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_303 = lean_ctor_get(x_294, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_294, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 x_305 = x_294;
} else {
 lean_dec_ref(x_294);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_304);
return x_306;
}
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_254);
lean_dec(x_243);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_307 = lean_ctor_get(x_263, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_308 = x_263;
} else {
 lean_dec_ref(x_263);
 x_308 = lean_box(0);
}
x_309 = lean_ctor_get(x_264, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_310 = x_264;
} else {
 lean_dec_ref(x_264);
 x_310 = lean_box(0);
}
x_311 = lean_box(0);
if (lean_is_scalar(x_310)) {
 x_312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_312 = x_310;
}
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_309);
if (lean_is_scalar(x_308)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_308;
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_307);
return x_313;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_254);
lean_dec(x_243);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_314 = lean_ctor_get(x_263, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_263, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_316 = x_263;
} else {
 lean_dec_ref(x_263);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_261);
lean_dec(x_254);
lean_dec(x_243);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_318 = lean_box(0);
if (lean_is_scalar(x_249)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_249;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_248);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_247);
return x_320;
}
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_254);
lean_dec(x_243);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_321 = lean_box(0);
if (lean_is_scalar(x_249)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_249;
}
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_248);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_247);
return x_323;
}
}
}
}
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_349 = lean_box(0);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_1);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_8);
return x_351;
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_352 = lean_box(0);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_1);
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_8);
return x_354;
}
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_355 = lean_box(0);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_1);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_8);
return x_357;
}
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_14__propagateExpectedType___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_Elab_logAt___at___private_Lean_Elab_App_14__propagateExpectedType___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Elab_logAt___at___private_Lean_Elab_App_14__propagateExpectedType___spec__6(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_Elab_log___at___private_Lean_Elab_App_14__propagateExpectedType___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Elab_log___at___private_Lean_Elab_App_14__propagateExpectedType___spec__5(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_15__addEtaArg___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_5, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_15__addEtaArg___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_15__addEtaArg___spec__1___rarg___lambda__1), 10, 4);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
x_14 = l___private_Lean_Meta_Basic_27__withLocalDeclImp___rarg(x_1, x_2, x_3, x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_15__addEtaArg___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_15__addEtaArg___spec__1___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_15__addEtaArg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_3, 5);
lean_inc(x_2);
x_13 = lean_array_push(x_12, x_2);
lean_ctor_set(x_3, 5, x_13);
x_14 = l___private_Lean_Elab_App_9__addNewArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_apply_9(x_1, x_18, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_19;
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*9);
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
x_26 = lean_ctor_get(x_3, 5);
x_27 = lean_ctor_get(x_3, 6);
x_28 = lean_ctor_get(x_3, 7);
x_29 = lean_ctor_get(x_3, 8);
x_30 = lean_ctor_get_uint8(x_3, sizeof(void*)*9 + 1);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
lean_inc(x_2);
x_31 = lean_array_push(x_26, x_2);
x_32 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_22);
lean_ctor_set(x_32, 2, x_23);
lean_ctor_set(x_32, 3, x_24);
lean_ctor_set(x_32, 4, x_25);
lean_ctor_set(x_32, 5, x_31);
lean_ctor_set(x_32, 6, x_27);
lean_ctor_set(x_32, 7, x_28);
lean_ctor_set(x_32, 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*9, x_20);
lean_ctor_set_uint8(x_32, sizeof(void*)*9 + 1, x_30);
x_33 = l___private_Lean_Elab_App_9__addNewArg(x_2, x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_box(0);
x_38 = lean_apply_9(x_1, x_37, x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_35);
return x_38;
}
}
}
lean_object* l___private_Lean_Elab_App_15__addEtaArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_10 = l___private_Lean_Elab_App_6__getBindingName(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l___private_Lean_Elab_App_7__getArgExpectedType(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_15__addEtaArg___lambda__1), 10, 1);
lean_closure_set(x_20, 0, x_1);
x_21 = 0;
x_22 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_15__addEtaArg___spec__1___rarg(x_13, x_21, x_18, x_20, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_22;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_15__addEtaArg___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_15__addEtaArg___spec__1___rarg(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_16__finalize___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_3);
x_14 = lean_nat_dec_lt(x_4, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
lean_inc(x_2);
x_19 = l_Lean_Elab_Term_registerMVarErrorImplicitArgInfo(x_18, x_2, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_4, x_21);
lean_dec(x_4);
x_4 = x_22;
x_12 = x_20;
goto _start;
}
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_App_16__finalize___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___rarg(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_12 = lean_st_ref_get(x_7, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_9, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 2);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
x_21 = l_Std_HashMap_inhabited___closed__1;
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_21);
x_23 = 1;
x_24 = 0;
x_25 = l_Lean_MetavarContext_MkBinding_mkBinding(x_23, x_20, x_1, x_2, x_24, x_24, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_26, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
x_31 = lean_st_ref_take(x_9, x_18);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_32, 2);
lean_dec(x_35);
lean_ctor_set(x_32, 2, x_30);
x_36 = lean_st_ref_set(x_9, x_32, x_33);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_27, 0);
lean_inc(x_38);
lean_dec(x_27);
x_39 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_38, x_6, x_7, x_8, x_9, x_37);
lean_dec(x_6);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_39, 0, x_26);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
lean_ctor_set(x_26, 1, x_3);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_26);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_44 = lean_ctor_get(x_32, 0);
x_45 = lean_ctor_get(x_32, 1);
x_46 = lean_ctor_get(x_32, 3);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_32);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_30);
lean_ctor_set(x_47, 3, x_46);
x_48 = lean_st_ref_set(x_9, x_47, x_33);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_27, 0);
lean_inc(x_50);
lean_dec(x_27);
x_51 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_50, x_6, x_7, x_8, x_9, x_49);
lean_dec(x_6);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
lean_ctor_set(x_26, 1, x_3);
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_26);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_55 = lean_ctor_get(x_26, 0);
lean_inc(x_55);
lean_dec(x_26);
x_56 = lean_ctor_get(x_27, 1);
lean_inc(x_56);
x_57 = lean_st_ref_take(x_9, x_18);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_58, 3);
lean_inc(x_62);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 lean_ctor_release(x_58, 2);
 lean_ctor_release(x_58, 3);
 x_63 = x_58;
} else {
 lean_dec_ref(x_58);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 4, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_56);
lean_ctor_set(x_64, 3, x_62);
x_65 = lean_st_ref_set(x_9, x_64, x_59);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_ctor_get(x_27, 0);
lean_inc(x_67);
lean_dec(x_27);
x_68 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_67, x_6, x_7, x_8, x_9, x_66);
lean_dec(x_6);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_55);
lean_ctor_set(x_71, 1, x_3);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_3);
x_73 = lean_ctor_get(x_25, 1);
lean_inc(x_73);
lean_dec(x_25);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(x_74, x_6, x_7, x_8, x_9, x_18);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = lean_st_ref_take(x_9, x_76);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_82 = lean_ctor_get(x_79, 2);
lean_dec(x_82);
lean_ctor_set(x_79, 2, x_77);
x_83 = lean_st_ref_set(x_9, x_79, x_80);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3;
x_86 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_85, x_6, x_7, x_8, x_9, x_84);
lean_dec(x_6);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
return x_86;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_86);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_91 = lean_ctor_get(x_79, 0);
x_92 = lean_ctor_get(x_79, 1);
x_93 = lean_ctor_get(x_79, 3);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_79);
x_94 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set(x_94, 2, x_77);
lean_ctor_set(x_94, 3, x_93);
x_95 = lean_st_ref_set(x_9, x_94, x_80);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3;
x_98 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_97, x_6, x_7, x_8, x_9, x_96);
lean_dec(x_6);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
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
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_6);
lean_dec(x_1);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_2);
lean_ctor_set(x_103, 1, x_3);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_10);
return x_104;
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_16__finalize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("finalize");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_16__finalize___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__1;
x_2 = l___private_Lean_Elab_App_16__finalize___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_16__finalize___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected type: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_16__finalize___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_16__finalize___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_16__finalize___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_16__finalize___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_16__finalize___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after etaArgs: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_16__finalize___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_16__finalize___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_16__finalize___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_16__finalize___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_16__finalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_551; lean_object* x_552; uint8_t x_553; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_551 = lean_ctor_get(x_6, 0);
lean_inc(x_551);
x_552 = l___private_Lean_Elab_App_16__finalize___closed__2;
x_553 = l_Lean_checkTraceOption(x_551, x_552);
lean_dec(x_551);
if (x_553 == 0)
{
lean_object* x_554; lean_object* x_555; 
x_554 = lean_box(0);
lean_inc(x_1);
x_555 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_555, 0, x_554);
lean_ctor_set(x_555, 1, x_1);
x_11 = x_555;
x_12 = x_8;
goto block_550;
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
lean_inc(x_9);
x_556 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_556, 0, x_9);
lean_inc(x_1);
x_557 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_552, x_556, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
lean_dec(x_557);
x_11 = x_558;
x_12 = x_559;
goto block_550;
}
block_550:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 6);
lean_inc(x_15);
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
x_17 = l_Array_forMAux___main___at___private_Lean_Elab_App_16__finalize___spec__1(x_9, x_14, x_15, x_16, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 5);
lean_inc(x_23);
x_24 = l_Array_isEmpty___rarg(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_free_object(x_18);
lean_dec(x_10);
lean_inc(x_4);
x_25 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_App_16__finalize___spec__2(x_23, x_9, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_28);
x_30 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__3(x_28, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 1);
x_155 = lean_ctor_get(x_6, 0);
lean_inc(x_155);
x_156 = l___private_Lean_Elab_App_16__finalize___closed__2;
x_157 = l_Lean_checkTraceOption(x_155, x_156);
lean_dec(x_155);
if (x_157 == 0)
{
lean_object* x_158; 
x_158 = lean_box(0);
lean_ctor_set(x_31, 0, x_158);
x_36 = x_31;
x_37 = x_32;
goto block_154;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_free_object(x_31);
lean_inc(x_28);
x_159 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_159, 0, x_28);
x_160 = l___private_Lean_Elab_App_16__finalize___closed__8;
x_161 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_159);
x_162 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_163 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
lean_inc(x_34);
x_164 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_164, 0, x_34);
x_165 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_156, x_165, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_32);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_36 = x_167;
x_37 = x_168;
goto block_154;
}
block_154:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_62; 
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_ctor_get(x_36, 0);
lean_dec(x_40);
x_62 = lean_ctor_get(x_1, 4);
lean_inc(x_62);
lean_dec(x_1);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
lean_dec(x_34);
x_63 = lean_box(0);
lean_ctor_set(x_36, 0, x_63);
x_41 = x_36;
x_42 = x_37;
goto block_61;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_free_object(x_36);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_6, 0);
lean_inc(x_65);
x_66 = l___private_Lean_Elab_App_16__finalize___closed__2;
x_67 = l_Lean_checkTraceOption(x_65, x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_68 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_64, x_34, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_37);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_69, 0);
lean_dec(x_72);
x_73 = lean_box(0);
lean_ctor_set(x_69, 0, x_73);
x_41 = x_69;
x_42 = x_70;
goto block_61;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_dec(x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_41 = x_76;
x_42 = x_70;
goto block_61;
}
}
else
{
uint8_t x_77; 
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_68);
if (x_77 == 0)
{
return x_68;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_68, 0);
x_79 = lean_ctor_get(x_68, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_68);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_inc(x_64);
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_64);
x_82 = l___private_Lean_Elab_App_16__finalize___closed__5;
x_83 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_66, x_83, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_37);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_88 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_64, x_34, x_87, x_2, x_3, x_4, x_5, x_6, x_7, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = !lean_is_exclusive(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 0);
lean_dec(x_92);
x_93 = lean_box(0);
lean_ctor_set(x_89, 0, x_93);
x_41 = x_89;
x_42 = x_90;
goto block_61;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_dec(x_89);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_41 = x_96;
x_42 = x_90;
goto block_61;
}
}
else
{
uint8_t x_97; 
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_88);
if (x_97 == 0)
{
return x_88;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_88, 0);
x_99 = lean_ctor_get(x_88, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_88);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
block_61:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_42);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_28);
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_28);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_44, 0, x_50);
return x_44;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_44, 0);
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_44);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_28);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_28);
x_57 = !lean_is_exclusive(x_44);
if (x_57 == 0)
{
return x_44;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_44, 0);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_44);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_118; 
x_101 = lean_ctor_get(x_36, 1);
lean_inc(x_101);
lean_dec(x_36);
x_118 = lean_ctor_get(x_1, 4);
lean_inc(x_118);
lean_dec(x_1);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_34);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_101);
x_102 = x_120;
x_103 = x_37;
goto block_117;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_ctor_get(x_6, 0);
lean_inc(x_122);
x_123 = l___private_Lean_Elab_App_16__finalize___closed__2;
x_124 = l_Lean_checkTraceOption(x_122, x_123);
lean_dec(x_122);
if (x_124 == 0)
{
lean_object* x_125; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_125 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_121, x_34, x_101, x_2, x_3, x_4, x_5, x_6, x_7, x_37);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
x_130 = lean_box(0);
if (lean_is_scalar(x_129)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_129;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_128);
x_102 = x_131;
x_103 = x_127;
goto block_117;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_132 = lean_ctor_get(x_125, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_125, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_134 = x_125;
} else {
 lean_dec_ref(x_125);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_inc(x_121);
x_136 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_136, 0, x_121);
x_137 = l___private_Lean_Elab_App_16__finalize___closed__5;
x_138 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
x_139 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_123, x_138, x_101, x_2, x_3, x_4, x_5, x_6, x_7, x_37);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_143 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_121, x_34, x_142, x_2, x_3, x_4, x_5, x_6, x_7, x_141);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
x_148 = lean_box(0);
if (lean_is_scalar(x_147)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_147;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
x_102 = x_149;
x_103 = x_145;
goto block_117;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_150 = lean_ctor_get(x_143, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_143, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_152 = x_143;
} else {
 lean_dec_ref(x_143);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
}
block_117:
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_110 = x_106;
} else {
 lean_dec_ref(x_106);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_28);
lean_ctor_set(x_111, 1, x_109);
if (lean_is_scalar(x_108)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_108;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_107);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_28);
x_113 = lean_ctor_get(x_105, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_105, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_115 = x_105;
} else {
 lean_dec_ref(x_105);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_169 = lean_ctor_get(x_31, 0);
x_170 = lean_ctor_get(x_31, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_31);
x_228 = lean_ctor_get(x_6, 0);
lean_inc(x_228);
x_229 = l___private_Lean_Elab_App_16__finalize___closed__2;
x_230 = l_Lean_checkTraceOption(x_228, x_229);
lean_dec(x_228);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_box(0);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_170);
x_171 = x_232;
x_172 = x_32;
goto block_227;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_inc(x_28);
x_233 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_233, 0, x_28);
x_234 = l___private_Lean_Elab_App_16__finalize___closed__8;
x_235 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_233);
x_236 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_237 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
lean_inc(x_169);
x_238 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_238, 0, x_169);
x_239 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
x_240 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_229, x_239, x_170, x_2, x_3, x_4, x_5, x_6, x_7, x_32);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_171 = x_241;
x_172 = x_242;
goto block_227;
}
block_227:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_191; 
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_174 = x_171;
} else {
 lean_dec_ref(x_171);
 x_174 = lean_box(0);
}
x_191 = lean_ctor_get(x_1, 4);
lean_inc(x_191);
lean_dec(x_1);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_169);
x_192 = lean_box(0);
if (lean_is_scalar(x_174)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_174;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_173);
x_175 = x_193;
x_176 = x_172;
goto block_190;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
lean_dec(x_174);
x_194 = lean_ctor_get(x_191, 0);
lean_inc(x_194);
lean_dec(x_191);
x_195 = lean_ctor_get(x_6, 0);
lean_inc(x_195);
x_196 = l___private_Lean_Elab_App_16__finalize___closed__2;
x_197 = l_Lean_checkTraceOption(x_195, x_196);
lean_dec(x_195);
if (x_197 == 0)
{
lean_object* x_198; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_198 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_194, x_169, x_173, x_2, x_3, x_4, x_5, x_6, x_7, x_172);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_202 = x_199;
} else {
 lean_dec_ref(x_199);
 x_202 = lean_box(0);
}
x_203 = lean_box(0);
if (lean_is_scalar(x_202)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_202;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_201);
x_175 = x_204;
x_176 = x_200;
goto block_190;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_205 = lean_ctor_get(x_198, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_198, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_207 = x_198;
} else {
 lean_dec_ref(x_198);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_inc(x_194);
x_209 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_209, 0, x_194);
x_210 = l___private_Lean_Elab_App_16__finalize___closed__5;
x_211 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
x_212 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_196, x_211, x_173, x_2, x_3, x_4, x_5, x_6, x_7, x_172);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_216 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_194, x_169, x_215, x_2, x_3, x_4, x_5, x_6, x_7, x_214);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_220 = x_217;
} else {
 lean_dec_ref(x_217);
 x_220 = lean_box(0);
}
x_221 = lean_box(0);
if (lean_is_scalar(x_220)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_220;
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_219);
x_175 = x_222;
x_176 = x_218;
goto block_190;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_223 = lean_ctor_get(x_216, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_216, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_225 = x_216;
} else {
 lean_dec_ref(x_216);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
}
block_190:
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(x_177, x_2, x_3, x_4, x_5, x_6, x_7, x_176);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_183 = x_179;
} else {
 lean_dec_ref(x_179);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_28);
lean_ctor_set(x_184, 1, x_182);
if (lean_is_scalar(x_181)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_181;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_180);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_28);
x_186 = lean_ctor_get(x_178, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_178, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_188 = x_178;
} else {
 lean_dec_ref(x_178);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
}
}
}
else
{
uint8_t x_243; 
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_243 = !lean_is_exclusive(x_30);
if (x_243 == 0)
{
return x_30;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_30, 0);
x_245 = lean_ctor_get(x_30, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_30);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
else
{
uint8_t x_247; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_247 = !lean_is_exclusive(x_25);
if (x_247 == 0)
{
return x_25;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_25, 0);
x_249 = lean_ctor_get(x_25, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_25);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_370; lean_object* x_371; uint8_t x_372; 
lean_dec(x_23);
x_370 = lean_ctor_get(x_6, 0);
lean_inc(x_370);
x_371 = l___private_Lean_Elab_App_16__finalize___closed__2;
x_372 = l_Lean_checkTraceOption(x_370, x_371);
lean_dec(x_370);
if (x_372 == 0)
{
lean_object* x_373; 
x_373 = lean_box(0);
lean_ctor_set(x_18, 0, x_373);
x_251 = x_18;
x_252 = x_19;
goto block_369;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
lean_free_object(x_18);
lean_inc(x_9);
x_374 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_374, 0, x_9);
x_375 = l___private_Lean_Elab_App_16__finalize___closed__8;
x_376 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_374);
x_377 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_378 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
lean_inc(x_10);
x_379 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_379, 0, x_10);
x_380 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
x_381 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_371, x_380, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
x_251 = x_382;
x_252 = x_383;
goto block_369;
}
block_369:
{
uint8_t x_253; 
x_253 = !lean_is_exclusive(x_251);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_277; 
x_254 = lean_ctor_get(x_251, 1);
x_255 = lean_ctor_get(x_251, 0);
lean_dec(x_255);
x_277 = lean_ctor_get(x_1, 4);
lean_inc(x_277);
lean_dec(x_1);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; 
lean_dec(x_10);
x_278 = lean_box(0);
lean_ctor_set(x_251, 0, x_278);
x_256 = x_251;
x_257 = x_252;
goto block_276;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
lean_free_object(x_251);
x_279 = lean_ctor_get(x_277, 0);
lean_inc(x_279);
lean_dec(x_277);
x_280 = lean_ctor_get(x_6, 0);
lean_inc(x_280);
x_281 = l___private_Lean_Elab_App_16__finalize___closed__2;
x_282 = l_Lean_checkTraceOption(x_280, x_281);
lean_dec(x_280);
if (x_282 == 0)
{
lean_object* x_283; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_283 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_279, x_10, x_254, x_2, x_3, x_4, x_5, x_6, x_7, x_252);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_286 = !lean_is_exclusive(x_284);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_284, 0);
lean_dec(x_287);
x_288 = lean_box(0);
lean_ctor_set(x_284, 0, x_288);
x_256 = x_284;
x_257 = x_285;
goto block_276;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_284, 1);
lean_inc(x_289);
lean_dec(x_284);
x_290 = lean_box(0);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_289);
x_256 = x_291;
x_257 = x_285;
goto block_276;
}
}
else
{
uint8_t x_292; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_292 = !lean_is_exclusive(x_283);
if (x_292 == 0)
{
return x_283;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_283, 0);
x_294 = lean_ctor_get(x_283, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_283);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_inc(x_279);
x_296 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_296, 0, x_279);
x_297 = l___private_Lean_Elab_App_16__finalize___closed__5;
x_298 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_296);
x_299 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_281, x_298, x_254, x_2, x_3, x_4, x_5, x_6, x_7, x_252);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_303 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_279, x_10, x_302, x_2, x_3, x_4, x_5, x_6, x_7, x_301);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = !lean_is_exclusive(x_304);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_ctor_get(x_304, 0);
lean_dec(x_307);
x_308 = lean_box(0);
lean_ctor_set(x_304, 0, x_308);
x_256 = x_304;
x_257 = x_305;
goto block_276;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_304, 1);
lean_inc(x_309);
lean_dec(x_304);
x_310 = lean_box(0);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_309);
x_256 = x_311;
x_257 = x_305;
goto block_276;
}
}
else
{
uint8_t x_312; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_312 = !lean_is_exclusive(x_303);
if (x_312 == 0)
{
return x_303;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_303, 0);
x_314 = lean_ctor_get(x_303, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_303);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
return x_315;
}
}
}
}
block_276:
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(x_258, x_2, x_3, x_4, x_5, x_6, x_7, x_257);
if (lean_obj_tag(x_259) == 0)
{
uint8_t x_260; 
x_260 = !lean_is_exclusive(x_259);
if (x_260 == 0)
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_ctor_get(x_259, 0);
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
lean_object* x_263; 
x_263 = lean_ctor_get(x_261, 0);
lean_dec(x_263);
lean_ctor_set(x_261, 0, x_9);
return x_259;
}
else
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_261, 1);
lean_inc(x_264);
lean_dec(x_261);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_9);
lean_ctor_set(x_265, 1, x_264);
lean_ctor_set(x_259, 0, x_265);
return x_259;
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_266 = lean_ctor_get(x_259, 0);
x_267 = lean_ctor_get(x_259, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_259);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_269 = x_266;
} else {
 lean_dec_ref(x_266);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_9);
lean_ctor_set(x_270, 1, x_268);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_267);
return x_271;
}
}
else
{
uint8_t x_272; 
lean_dec(x_9);
x_272 = !lean_is_exclusive(x_259);
if (x_272 == 0)
{
return x_259;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_259, 0);
x_274 = lean_ctor_get(x_259, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_259);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
}
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_333; 
x_316 = lean_ctor_get(x_251, 1);
lean_inc(x_316);
lean_dec(x_251);
x_333 = lean_ctor_get(x_1, 4);
lean_inc(x_333);
lean_dec(x_1);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; 
lean_dec(x_10);
x_334 = lean_box(0);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_316);
x_317 = x_335;
x_318 = x_252;
goto block_332;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_336 = lean_ctor_get(x_333, 0);
lean_inc(x_336);
lean_dec(x_333);
x_337 = lean_ctor_get(x_6, 0);
lean_inc(x_337);
x_338 = l___private_Lean_Elab_App_16__finalize___closed__2;
x_339 = l_Lean_checkTraceOption(x_337, x_338);
lean_dec(x_337);
if (x_339 == 0)
{
lean_object* x_340; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_340 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_336, x_10, x_316, x_2, x_3, x_4, x_5, x_6, x_7, x_252);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
lean_dec(x_340);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_344 = x_341;
} else {
 lean_dec_ref(x_341);
 x_344 = lean_box(0);
}
x_345 = lean_box(0);
if (lean_is_scalar(x_344)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_344;
}
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_343);
x_317 = x_346;
x_318 = x_342;
goto block_332;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_347 = lean_ctor_get(x_340, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_340, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_349 = x_340;
} else {
 lean_dec_ref(x_340);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_348);
return x_350;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_inc(x_336);
x_351 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_351, 0, x_336);
x_352 = l___private_Lean_Elab_App_16__finalize___closed__5;
x_353 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_351);
x_354 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_338, x_353, x_316, x_2, x_3, x_4, x_5, x_6, x_7, x_252);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
lean_dec(x_354);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_358 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_336, x_10, x_357, x_2, x_3, x_4, x_5, x_6, x_7, x_356);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_362 = x_359;
} else {
 lean_dec_ref(x_359);
 x_362 = lean_box(0);
}
x_363 = lean_box(0);
if (lean_is_scalar(x_362)) {
 x_364 = lean_alloc_ctor(0, 2, 0);
} else {
 x_364 = x_362;
}
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_361);
x_317 = x_364;
x_318 = x_360;
goto block_332;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_365 = lean_ctor_get(x_358, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_358, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_367 = x_358;
} else {
 lean_dec_ref(x_358);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(1, 2, 0);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_365);
lean_ctor_set(x_368, 1, x_366);
return x_368;
}
}
}
block_332:
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_320 = l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(x_319, x_2, x_3, x_4, x_5, x_6, x_7, x_318);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_323 = x_320;
} else {
 lean_dec_ref(x_320);
 x_323 = lean_box(0);
}
x_324 = lean_ctor_get(x_321, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_325 = x_321;
} else {
 lean_dec_ref(x_321);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_9);
lean_ctor_set(x_326, 1, x_324);
if (lean_is_scalar(x_323)) {
 x_327 = lean_alloc_ctor(0, 2, 0);
} else {
 x_327 = x_323;
}
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_322);
return x_327;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_9);
x_328 = lean_ctor_get(x_320, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_320, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_330 = x_320;
} else {
 lean_dec_ref(x_320);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(1, 2, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_328);
lean_ctor_set(x_331, 1, x_329);
return x_331;
}
}
}
}
}
}
else
{
lean_object* x_384; lean_object* x_385; uint8_t x_386; 
x_384 = lean_ctor_get(x_18, 1);
lean_inc(x_384);
lean_dec(x_18);
x_385 = lean_ctor_get(x_1, 5);
lean_inc(x_385);
x_386 = l_Array_isEmpty___rarg(x_385);
if (x_386 == 0)
{
lean_object* x_387; 
lean_dec(x_10);
lean_inc(x_4);
x_387 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_App_16__finalize___spec__2(x_385, x_9, x_384, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec(x_387);
x_390 = lean_ctor_get(x_388, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_388, 1);
lean_inc(x_391);
lean_dec(x_388);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_390);
x_392 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType___spec__3(x_390, x_391, x_2, x_3, x_4, x_5, x_6, x_7, x_389);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_455; lean_object* x_456; uint8_t x_457; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
x_395 = lean_ctor_get(x_393, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_393, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_397 = x_393;
} else {
 lean_dec_ref(x_393);
 x_397 = lean_box(0);
}
x_455 = lean_ctor_get(x_6, 0);
lean_inc(x_455);
x_456 = l___private_Lean_Elab_App_16__finalize___closed__2;
x_457 = l_Lean_checkTraceOption(x_455, x_456);
lean_dec(x_455);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; 
x_458 = lean_box(0);
if (lean_is_scalar(x_397)) {
 x_459 = lean_alloc_ctor(0, 2, 0);
} else {
 x_459 = x_397;
}
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_396);
x_398 = x_459;
x_399 = x_394;
goto block_454;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_dec(x_397);
lean_inc(x_390);
x_460 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_460, 0, x_390);
x_461 = l___private_Lean_Elab_App_16__finalize___closed__8;
x_462 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set(x_462, 1, x_460);
x_463 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_464 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_464, 0, x_462);
lean_ctor_set(x_464, 1, x_463);
lean_inc(x_395);
x_465 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_465, 0, x_395);
x_466 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
x_467 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_456, x_466, x_396, x_2, x_3, x_4, x_5, x_6, x_7, x_394);
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec(x_467);
x_398 = x_468;
x_399 = x_469;
goto block_454;
}
block_454:
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_418; 
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_401 = x_398;
} else {
 lean_dec_ref(x_398);
 x_401 = lean_box(0);
}
x_418 = lean_ctor_get(x_1, 4);
lean_inc(x_418);
lean_dec(x_1);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; 
lean_dec(x_395);
x_419 = lean_box(0);
if (lean_is_scalar(x_401)) {
 x_420 = lean_alloc_ctor(0, 2, 0);
} else {
 x_420 = x_401;
}
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_400);
x_402 = x_420;
x_403 = x_399;
goto block_417;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
lean_dec(x_401);
x_421 = lean_ctor_get(x_418, 0);
lean_inc(x_421);
lean_dec(x_418);
x_422 = lean_ctor_get(x_6, 0);
lean_inc(x_422);
x_423 = l___private_Lean_Elab_App_16__finalize___closed__2;
x_424 = l_Lean_checkTraceOption(x_422, x_423);
lean_dec(x_422);
if (x_424 == 0)
{
lean_object* x_425; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_425 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_421, x_395, x_400, x_2, x_3, x_4, x_5, x_6, x_7, x_399);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec(x_425);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_429 = x_426;
} else {
 lean_dec_ref(x_426);
 x_429 = lean_box(0);
}
x_430 = lean_box(0);
if (lean_is_scalar(x_429)) {
 x_431 = lean_alloc_ctor(0, 2, 0);
} else {
 x_431 = x_429;
}
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_428);
x_402 = x_431;
x_403 = x_427;
goto block_417;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_390);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_432 = lean_ctor_get(x_425, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_425, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 x_434 = x_425;
} else {
 lean_dec_ref(x_425);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(1, 2, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_432);
lean_ctor_set(x_435, 1, x_433);
return x_435;
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_inc(x_421);
x_436 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_436, 0, x_421);
x_437 = l___private_Lean_Elab_App_16__finalize___closed__5;
x_438 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_436);
x_439 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_423, x_438, x_400, x_2, x_3, x_4, x_5, x_6, x_7, x_399);
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec(x_440);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_443 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_421, x_395, x_442, x_2, x_3, x_4, x_5, x_6, x_7, x_441);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec(x_443);
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_447 = x_444;
} else {
 lean_dec_ref(x_444);
 x_447 = lean_box(0);
}
x_448 = lean_box(0);
if (lean_is_scalar(x_447)) {
 x_449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_449 = x_447;
}
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_446);
x_402 = x_449;
x_403 = x_445;
goto block_417;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_390);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_450 = lean_ctor_get(x_443, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_443, 1);
lean_inc(x_451);
if (lean_is_exclusive(x_443)) {
 lean_ctor_release(x_443, 0);
 lean_ctor_release(x_443, 1);
 x_452 = x_443;
} else {
 lean_dec_ref(x_443);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(1, 2, 0);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_450);
lean_ctor_set(x_453, 1, x_451);
return x_453;
}
}
}
block_417:
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
x_405 = l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(x_404, x_2, x_3, x_4, x_5, x_6, x_7, x_403);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_408 = x_405;
} else {
 lean_dec_ref(x_405);
 x_408 = lean_box(0);
}
x_409 = lean_ctor_get(x_406, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 x_410 = x_406;
} else {
 lean_dec_ref(x_406);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(0, 2, 0);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_390);
lean_ctor_set(x_411, 1, x_409);
if (lean_is_scalar(x_408)) {
 x_412 = lean_alloc_ctor(0, 2, 0);
} else {
 x_412 = x_408;
}
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_407);
return x_412;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
lean_dec(x_390);
x_413 = lean_ctor_get(x_405, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_405, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_415 = x_405;
} else {
 lean_dec_ref(x_405);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(1, 2, 0);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_414);
return x_416;
}
}
}
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_dec(x_390);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_470 = lean_ctor_get(x_392, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_392, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_472 = x_392;
} else {
 lean_dec_ref(x_392);
 x_472 = lean_box(0);
}
if (lean_is_scalar(x_472)) {
 x_473 = lean_alloc_ctor(1, 2, 0);
} else {
 x_473 = x_472;
}
lean_ctor_set(x_473, 0, x_470);
lean_ctor_set(x_473, 1, x_471);
return x_473;
}
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_474 = lean_ctor_get(x_387, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_387, 1);
lean_inc(x_475);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_476 = x_387;
} else {
 lean_dec_ref(x_387);
 x_476 = lean_box(0);
}
if (lean_is_scalar(x_476)) {
 x_477 = lean_alloc_ctor(1, 2, 0);
} else {
 x_477 = x_476;
}
lean_ctor_set(x_477, 0, x_474);
lean_ctor_set(x_477, 1, x_475);
return x_477;
}
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_535; lean_object* x_536; uint8_t x_537; 
lean_dec(x_385);
x_535 = lean_ctor_get(x_6, 0);
lean_inc(x_535);
x_536 = l___private_Lean_Elab_App_16__finalize___closed__2;
x_537 = l_Lean_checkTraceOption(x_535, x_536);
lean_dec(x_535);
if (x_537 == 0)
{
lean_object* x_538; lean_object* x_539; 
x_538 = lean_box(0);
x_539 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_384);
x_478 = x_539;
x_479 = x_19;
goto block_534;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_inc(x_9);
x_540 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_540, 0, x_9);
x_541 = l___private_Lean_Elab_App_16__finalize___closed__8;
x_542 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_542, 0, x_541);
lean_ctor_set(x_542, 1, x_540);
x_543 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_544 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_543);
lean_inc(x_10);
x_545 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_545, 0, x_10);
x_546 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_546, 0, x_544);
lean_ctor_set(x_546, 1, x_545);
x_547 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_536, x_546, x_384, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_547, 1);
lean_inc(x_549);
lean_dec(x_547);
x_478 = x_548;
x_479 = x_549;
goto block_534;
}
block_534:
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_498; 
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_481 = x_478;
} else {
 lean_dec_ref(x_478);
 x_481 = lean_box(0);
}
x_498 = lean_ctor_get(x_1, 4);
lean_inc(x_498);
lean_dec(x_1);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; 
lean_dec(x_10);
x_499 = lean_box(0);
if (lean_is_scalar(x_481)) {
 x_500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_500 = x_481;
}
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_480);
x_482 = x_500;
x_483 = x_479;
goto block_497;
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; 
lean_dec(x_481);
x_501 = lean_ctor_get(x_498, 0);
lean_inc(x_501);
lean_dec(x_498);
x_502 = lean_ctor_get(x_6, 0);
lean_inc(x_502);
x_503 = l___private_Lean_Elab_App_16__finalize___closed__2;
x_504 = l_Lean_checkTraceOption(x_502, x_503);
lean_dec(x_502);
if (x_504 == 0)
{
lean_object* x_505; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_505 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_501, x_10, x_480, x_2, x_3, x_4, x_5, x_6, x_7, x_479);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
if (lean_is_exclusive(x_506)) {
 lean_ctor_release(x_506, 0);
 lean_ctor_release(x_506, 1);
 x_509 = x_506;
} else {
 lean_dec_ref(x_506);
 x_509 = lean_box(0);
}
x_510 = lean_box(0);
if (lean_is_scalar(x_509)) {
 x_511 = lean_alloc_ctor(0, 2, 0);
} else {
 x_511 = x_509;
}
lean_ctor_set(x_511, 0, x_510);
lean_ctor_set(x_511, 1, x_508);
x_482 = x_511;
x_483 = x_507;
goto block_497;
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_512 = lean_ctor_get(x_505, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_505, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_514 = x_505;
} else {
 lean_dec_ref(x_505);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(1, 2, 0);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_512);
lean_ctor_set(x_515, 1, x_513);
return x_515;
}
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
lean_inc(x_501);
x_516 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_516, 0, x_501);
x_517 = l___private_Lean_Elab_App_16__finalize___closed__5;
x_518 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_516);
x_519 = l_Lean_Elab_logTrace___at___private_Lean_Elab_App_14__propagateExpectedType___spec__4(x_503, x_518, x_480, x_2, x_3, x_4, x_5, x_6, x_7, x_479);
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_519, 1);
lean_inc(x_521);
lean_dec(x_519);
x_522 = lean_ctor_get(x_520, 1);
lean_inc(x_522);
lean_dec(x_520);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_523 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_14__propagateExpectedType___spec__3(x_501, x_10, x_522, x_2, x_3, x_4, x_5, x_6, x_7, x_521);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_523, 1);
lean_inc(x_525);
lean_dec(x_523);
x_526 = lean_ctor_get(x_524, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 x_527 = x_524;
} else {
 lean_dec_ref(x_524);
 x_527 = lean_box(0);
}
x_528 = lean_box(0);
if (lean_is_scalar(x_527)) {
 x_529 = lean_alloc_ctor(0, 2, 0);
} else {
 x_529 = x_527;
}
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set(x_529, 1, x_526);
x_482 = x_529;
x_483 = x_525;
goto block_497;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_530 = lean_ctor_get(x_523, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_523, 1);
lean_inc(x_531);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 x_532 = x_523;
} else {
 lean_dec_ref(x_523);
 x_532 = lean_box(0);
}
if (lean_is_scalar(x_532)) {
 x_533 = lean_alloc_ctor(1, 2, 0);
} else {
 x_533 = x_532;
}
lean_ctor_set(x_533, 0, x_530);
lean_ctor_set(x_533, 1, x_531);
return x_533;
}
}
}
block_497:
{
lean_object* x_484; lean_object* x_485; 
x_484 = lean_ctor_get(x_482, 1);
lean_inc(x_484);
lean_dec(x_482);
x_485 = l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(x_484, x_2, x_3, x_4, x_5, x_6, x_7, x_483);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 lean_ctor_release(x_485, 1);
 x_488 = x_485;
} else {
 lean_dec_ref(x_485);
 x_488 = lean_box(0);
}
x_489 = lean_ctor_get(x_486, 1);
lean_inc(x_489);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_490 = x_486;
} else {
 lean_dec_ref(x_486);
 x_490 = lean_box(0);
}
if (lean_is_scalar(x_490)) {
 x_491 = lean_alloc_ctor(0, 2, 0);
} else {
 x_491 = x_490;
}
lean_ctor_set(x_491, 0, x_9);
lean_ctor_set(x_491, 1, x_489);
if (lean_is_scalar(x_488)) {
 x_492 = lean_alloc_ctor(0, 2, 0);
} else {
 x_492 = x_488;
}
lean_ctor_set(x_492, 0, x_491);
lean_ctor_set(x_492, 1, x_487);
return x_492;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_9);
x_493 = lean_ctor_get(x_485, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_485, 1);
lean_inc(x_494);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 lean_ctor_release(x_485, 1);
 x_495 = x_485;
} else {
 lean_dec_ref(x_485);
 x_495 = lean_box(0);
}
if (lean_is_scalar(x_495)) {
 x_496 = lean_alloc_ctor(1, 2, 0);
} else {
 x_496 = x_495;
}
lean_ctor_set(x_496, 0, x_493);
lean_ctor_set(x_496, 1, x_494);
return x_496;
}
}
}
}
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_16__finalize___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forMAux___main___at___private_Lean_Elab_App_16__finalize___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_App_16__finalize___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_App_16__finalize___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_16__finalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_16__finalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_17__processExplictArg___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_17__processExplictArg___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_App_17__processExplictArg___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_17__processExplictArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid autoParam, argument must be a constant");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_17__processExplictArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_17__processExplictArg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_17__processExplictArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_17__processExplictArg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_17__processExplictArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("by");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_17__processExplictArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Lean_Elab_App_17__processExplictArg___closed__4;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_17__processExplictArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_App_17__processExplictArg___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_17__processExplictArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_2);
x_11 = l___private_Lean_Elab_App_7__getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = l_Lean_Expr_getOptParamDefault_x3f(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = l_Lean_Expr_getAutoParamTactic_x3f(x_15);
lean_dec(x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_2, 3);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_List_isEmpty___rarg(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = l___private_Lean_Elab_App_15__addEtaArg(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_21;
}
else
{
lean_object* x_22; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l___private_Lean_Elab_App_12__fTypeHasOptAutoParams(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l___private_Lean_Elab_App_16__finalize(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_4);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_dec(x_23);
x_31 = l___private_Lean_Elab_App_15__addEtaArg(x_1, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_18, 0);
lean_inc(x_36);
lean_dec(x_18);
if (lean_obj_tag(x_36) == 4)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_st_ref_get(x_8, x_14);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Lean_Elab_Util_2__evalSyntaxConstantUnsafe(x_41, x_37);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_1);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Lean_throwError___at___private_Lean_Elab_App_17__processExplictArg___spec__1___rarg(x_45, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_16);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
lean_dec(x_42);
x_48 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_40);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_49);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_Lean_Syntax_getArgs(x_47);
lean_dec(x_47);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Array_empty___closed__1;
x_55 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_52, x_52, x_53, x_54);
lean_dec(x_52);
x_56 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
x_57 = lean_array_push(x_55, x_56);
x_58 = l_Lean_nullKind___closed__2;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_array_push(x_54, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__4;
x_63 = lean_array_push(x_62, x_61);
x_64 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__29;
x_65 = lean_array_push(x_63, x_64);
x_66 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_array_push(x_54, x_67);
x_69 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2;
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l___private_Lean_Elab_App_17__processExplictArg___closed__6;
x_72 = lean_array_push(x_71, x_70);
x_73 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_ctor_get(x_7, 3);
lean_inc(x_75);
x_76 = l_Lean_Syntax_copyInfo(x_74, x_75);
lean_dec(x_75);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_77 = l___private_Lean_Elab_App_14__propagateExpectedType(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_51);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_76);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_82 = l___private_Lean_Elab_App_10__elabAndAddNewArg(x_81, x_80, x_3, x_4, x_5, x_6, x_7, x_8, x_79);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_box(0);
x_87 = lean_apply_9(x_1, x_86, x_85, x_3, x_4, x_5, x_6, x_7, x_8, x_84);
return x_87;
}
else
{
uint8_t x_88; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_82);
if (x_88 == 0)
{
return x_82;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_82, 0);
x_90 = lean_ctor_get(x_82, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_82);
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
lean_dec(x_76);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_77);
if (x_92 == 0)
{
return x_77;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_77, 0);
x_94 = lean_ctor_get(x_77, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_77);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_36);
lean_dec(x_1);
x_96 = l___private_Lean_Elab_App_17__processExplictArg___closed__3;
x_97 = l_Lean_throwError___at___private_Lean_Elab_App_17__processExplictArg___spec__1___rarg(x_96, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_16);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_15);
lean_dec(x_2);
x_98 = lean_ctor_get(x_17, 0);
lean_inc(x_98);
lean_dec(x_17);
x_99 = l___private_Lean_Elab_App_9__addNewArg(x_98, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_box(0);
x_104 = lean_apply_9(x_1, x_103, x_102, x_3, x_4, x_5, x_6, x_7, x_8, x_101);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_11, 1);
lean_inc(x_105);
lean_dec(x_11);
x_106 = lean_ctor_get(x_12, 1);
lean_inc(x_106);
lean_dec(x_12);
x_107 = lean_ctor_get(x_2, 3);
lean_inc(x_107);
lean_dec(x_2);
x_108 = l_List_isEmpty___rarg(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = l___private_Lean_Elab_App_15__addEtaArg(x_1, x_106, x_3, x_4, x_5, x_6, x_7, x_8, x_105);
return x_109;
}
else
{
lean_object* x_110; 
lean_dec(x_1);
x_110 = l___private_Lean_Elab_App_16__finalize(x_106, x_3, x_4, x_5, x_6, x_7, x_8, x_105);
lean_dec(x_4);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_10, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_10, 1);
lean_inc(x_112);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_113 = l___private_Lean_Elab_App_14__propagateExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = !lean_is_exclusive(x_115);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_115, 2);
lean_dec(x_118);
lean_ctor_set(x_115, 2, x_112);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_119 = l___private_Lean_Elab_App_10__elabAndAddNewArg(x_111, x_115, x_3, x_4, x_5, x_6, x_7, x_8, x_116);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_box(0);
x_124 = lean_apply_9(x_1, x_123, x_122, x_3, x_4, x_5, x_6, x_7, x_8, x_121);
return x_124;
}
else
{
uint8_t x_125; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_119);
if (x_125 == 0)
{
return x_119;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_119, 0);
x_127 = lean_ctor_get(x_119, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_119);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; 
x_129 = lean_ctor_get_uint8(x_115, sizeof(void*)*9);
x_130 = lean_ctor_get(x_115, 0);
x_131 = lean_ctor_get(x_115, 1);
x_132 = lean_ctor_get(x_115, 3);
x_133 = lean_ctor_get(x_115, 4);
x_134 = lean_ctor_get(x_115, 5);
x_135 = lean_ctor_get(x_115, 6);
x_136 = lean_ctor_get(x_115, 7);
x_137 = lean_ctor_get(x_115, 8);
x_138 = lean_ctor_get_uint8(x_115, sizeof(void*)*9 + 1);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_115);
x_139 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_139, 0, x_130);
lean_ctor_set(x_139, 1, x_131);
lean_ctor_set(x_139, 2, x_112);
lean_ctor_set(x_139, 3, x_132);
lean_ctor_set(x_139, 4, x_133);
lean_ctor_set(x_139, 5, x_134);
lean_ctor_set(x_139, 6, x_135);
lean_ctor_set(x_139, 7, x_136);
lean_ctor_set(x_139, 8, x_137);
lean_ctor_set_uint8(x_139, sizeof(void*)*9, x_129);
lean_ctor_set_uint8(x_139, sizeof(void*)*9 + 1, x_138);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_140 = l___private_Lean_Elab_App_10__elabAndAddNewArg(x_111, x_139, x_3, x_4, x_5, x_6, x_7, x_8, x_116);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_box(0);
x_145 = lean_apply_9(x_1, x_144, x_143, x_3, x_4, x_5, x_6, x_7, x_8, x_142);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_146 = lean_ctor_get(x_140, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_140, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_148 = x_140;
} else {
 lean_dec_ref(x_140);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_113);
if (x_150 == 0)
{
return x_113;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_113, 0);
x_152 = lean_ctor_get(x_113, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_113);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_17__processExplictArg___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_App_17__processExplictArg___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_18__processImplicitArg___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_18__processImplicitArg___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_InferType_22__isTypeFormerTypeImp___main(x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l___private_Lean_Elab_App_18__processImplicitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = l___private_Lean_Elab_App_7__getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = 0;
x_18 = lean_box(0);
lean_inc(x_5);
x_19 = l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_18__processImplicitArg___spec__1(x_16, x_17, x_18, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
x_24 = l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_18__processImplicitArg___spec__2(x_22, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l___private_Lean_Elab_App_9__addNewArg(x_22, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = lean_apply_9(x_1, x_34, x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_dec(x_25);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_dec(x_24);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_ctor_get(x_36, 6);
x_40 = lean_ctor_get(x_36, 8);
x_41 = l_Lean_Expr_mvarId_x21(x_22);
lean_inc(x_41);
x_42 = lean_array_push(x_39, x_41);
x_43 = lean_array_push(x_40, x_41);
lean_ctor_set(x_36, 8, x_43);
lean_ctor_set(x_36, 6, x_42);
x_44 = l___private_Lean_Elab_App_9__addNewArg(x_22, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_box(0);
x_49 = lean_apply_9(x_1, x_48, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_46);
return x_49;
}
else
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_50 = lean_ctor_get_uint8(x_36, sizeof(void*)*9);
x_51 = lean_ctor_get(x_36, 0);
x_52 = lean_ctor_get(x_36, 1);
x_53 = lean_ctor_get(x_36, 2);
x_54 = lean_ctor_get(x_36, 3);
x_55 = lean_ctor_get(x_36, 4);
x_56 = lean_ctor_get(x_36, 5);
x_57 = lean_ctor_get(x_36, 6);
x_58 = lean_ctor_get(x_36, 7);
x_59 = lean_ctor_get(x_36, 8);
x_60 = lean_ctor_get_uint8(x_36, sizeof(void*)*9 + 1);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_36);
x_61 = l_Lean_Expr_mvarId_x21(x_22);
lean_inc(x_61);
x_62 = lean_array_push(x_57, x_61);
x_63 = lean_array_push(x_59, x_61);
x_64 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_64, 0, x_51);
lean_ctor_set(x_64, 1, x_52);
lean_ctor_set(x_64, 2, x_53);
lean_ctor_set(x_64, 3, x_54);
lean_ctor_set(x_64, 4, x_55);
lean_ctor_set(x_64, 5, x_56);
lean_ctor_set(x_64, 6, x_62);
lean_ctor_set(x_64, 7, x_58);
lean_ctor_set(x_64, 8, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*9, x_50);
lean_ctor_set_uint8(x_64, sizeof(void*)*9 + 1, x_60);
x_65 = l___private_Lean_Elab_App_9__addNewArg(x_22, x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_box(0);
x_70 = lean_apply_9(x_1, x_69, x_68, x_3, x_4, x_5, x_6, x_7, x_8, x_67);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_24);
if (x_71 == 0)
{
return x_24;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_24, 0);
x_73 = lean_ctor_get(x_24, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_24);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; 
x_75 = l___private_Lean_Elab_App_17__processExplictArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_75;
}
}
}
lean_object* l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_18__processImplicitArg___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_18__processImplicitArg___spec__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_18__processImplicitArg___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_18__processImplicitArg___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_19__processInstImplicitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_2);
x_10 = l___private_Lean_Elab_App_7__getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*9);
lean_dec(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = 1;
x_18 = lean_box(0);
lean_inc(x_5);
x_19 = l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_18__processImplicitArg___spec__1(x_16, x_17, x_18, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_Expr_mvarId_x21(x_22);
x_25 = l___private_Lean_Elab_App_3__addInstMVar(x_24, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Elab_App_9__addNewArg(x_22, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = lean_apply_9(x_1, x_33, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_ctor_get(x_11, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_dec(x_11);
x_38 = l___private_Lean_Elab_App_8__isNextArgHole(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_36);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l___private_Lean_Elab_App_17__processExplictArg(x_1, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_dec(x_39);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_36);
x_48 = 1;
x_49 = lean_box(0);
lean_inc(x_5);
x_50 = l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_18__processImplicitArg___spec__1(x_47, x_48, x_49, x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_45);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec(x_51);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_56 = lean_ctor_get(x_52, 2);
x_57 = l_List_tail_x21___rarg(x_56);
lean_dec(x_56);
lean_ctor_set(x_52, 2, x_57);
x_58 = l_Lean_Expr_mvarId_x21(x_54);
x_59 = l___private_Lean_Elab_App_3__addInstMVar(x_58, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_53);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l___private_Lean_Elab_App_9__addNewArg(x_54, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_61);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_box(0);
x_68 = lean_apply_9(x_1, x_67, x_66, x_3, x_4, x_5, x_6, x_7, x_8, x_65);
return x_68;
}
else
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_69 = lean_ctor_get_uint8(x_52, sizeof(void*)*9);
x_70 = lean_ctor_get(x_52, 0);
x_71 = lean_ctor_get(x_52, 1);
x_72 = lean_ctor_get(x_52, 2);
x_73 = lean_ctor_get(x_52, 3);
x_74 = lean_ctor_get(x_52, 4);
x_75 = lean_ctor_get(x_52, 5);
x_76 = lean_ctor_get(x_52, 6);
x_77 = lean_ctor_get(x_52, 7);
x_78 = lean_ctor_get(x_52, 8);
x_79 = lean_ctor_get_uint8(x_52, sizeof(void*)*9 + 1);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_52);
x_80 = l_List_tail_x21___rarg(x_72);
lean_dec(x_72);
x_81 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_81, 0, x_70);
lean_ctor_set(x_81, 1, x_71);
lean_ctor_set(x_81, 2, x_80);
lean_ctor_set(x_81, 3, x_73);
lean_ctor_set(x_81, 4, x_74);
lean_ctor_set(x_81, 5, x_75);
lean_ctor_set(x_81, 6, x_76);
lean_ctor_set(x_81, 7, x_77);
lean_ctor_set(x_81, 8, x_78);
lean_ctor_set_uint8(x_81, sizeof(void*)*9, x_69);
lean_ctor_set_uint8(x_81, sizeof(void*)*9 + 1, x_79);
x_82 = l_Lean_Expr_mvarId_x21(x_54);
x_83 = l___private_Lean_Elab_App_3__addInstMVar(x_82, x_81, x_3, x_4, x_5, x_6, x_7, x_8, x_53);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l___private_Lean_Elab_App_9__addNewArg(x_54, x_86, x_3, x_4, x_5, x_6, x_7, x_8, x_85);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_box(0);
x_92 = lean_apply_9(x_1, x_91, x_90, x_3, x_4, x_5, x_6, x_7, x_8, x_89);
return x_92;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_20__hasArgsToProcess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = l_List_isEmpty___rarg(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = l_List_isEmpty___rarg(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 1;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_8);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Elab_App_20__hasArgsToProcess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_20__hasArgsToProcess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Term_ElabAppArgs_main___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ElabAppArgs_main___main___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l___private_Lean_Elab_App_5__normalizeFunType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 7)
{
lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_12, sizeof(void*)*3);
lean_dec(x_12);
lean_inc(x_34);
x_36 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_13__getForallBody___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_36, 0, x_34);
x_37 = lean_ctor_get(x_13, 3);
lean_inc(x_37);
x_38 = l_List_find_x3f___main___rarg(x_36, x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; lean_object* x_40; 
lean_dec(x_34);
x_39 = (uint8_t)((x_35 << 24) >> 61);
x_40 = lean_box(x_39);
switch (lean_obj_tag(x_40)) {
case 1:
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_Elab_Term_ElabAppArgs_main___main___rarg___closed__1;
x_42 = l___private_Lean_Elab_App_18__processImplicitArg(x_41, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_42;
}
case 3:
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Lean_Elab_Term_ElabAppArgs_main___main___rarg___closed__1;
x_44 = l___private_Lean_Elab_App_19__processInstImplicitArg(x_43, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_44;
}
default: 
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_40);
x_45 = l_Lean_Elab_Term_ElabAppArgs_main___main___rarg___closed__1;
x_46 = l___private_Lean_Elab_App_17__processExplictArg(x_45, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_38, 0);
lean_inc(x_47);
lean_dec(x_38);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_48 = l___private_Lean_Elab_App_14__propagateExpectedType(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg(x_34, x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_50);
lean_dec(x_34);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_dec(x_47);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_57 = l___private_Lean_Elab_App_10__elabAndAddNewArg(x_56, x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_1 = x_60;
x_8 = x_59;
goto _start;
}
else
{
uint8_t x_62; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_57);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_47);
lean_dec(x_34);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_48);
if (x_66 == 0)
{
return x_48;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_48, 0);
x_68 = lean_ctor_get(x_48, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_48);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
lean_object* x_70; 
lean_dec(x_12);
x_70 = lean_box(0);
x_14 = x_70;
goto block_33;
}
block_33:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_14);
x_15 = l___private_Lean_Elab_App_20__hasArgsToProcess(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l___private_Lean_Elab_App_16__finalize(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_App_4__synthesizePendingAndNormalizeFunType(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_1 = x_27;
x_8 = x_26;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_9);
if (x_71 == 0)
{
return x_9;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_9, 0);
x_73 = lean_ctor_get(x_9, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_9);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ElabAppArgs_main___main___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_ElabAppArgs_main___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_ElabAppArgs_main___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ElabAppArgs_main___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_ElabAppArgs_main(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("args");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__1;
x_2 = l___private_Lean_Elab_App_21__elabAppArgs___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_21__elabAppArgs___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_21__elabAppArgs___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_21__elabAppArgs___closed__5;
x_2 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__9;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_21__elabAppArgs___closed__6;
x_2 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_21__elabAppArgs___closed__5;
x_2 = l___private_Lean_Elab_SyntheticMVars_7__synthesizeSyntheticMVarsStep___closed__10;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_21__elabAppArgs___closed__8;
x_2 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_21__elabAppArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_13 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_86 = lean_ctor_get(x_10, 0);
lean_inc(x_86);
x_87 = l___private_Lean_Elab_App_21__elabAppArgs___closed__2;
x_88 = l_Lean_checkTraceOption(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
x_19 = x_18;
goto block_85;
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_inc(x_1);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_1);
lean_inc(x_17);
x_90 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_90, 0, x_17);
if (x_5 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = l___private_Lean_Elab_App_21__elabAppArgs___closed__7;
x_92 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
x_93 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_94 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_90);
x_96 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_87, x_95, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_19 = x_97;
goto block_85;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = l___private_Lean_Elab_App_21__elabAppArgs___closed__9;
x_99 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_89);
x_100 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_90);
x_103 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_87, x_102, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_19 = x_104;
goto block_85;
}
}
block_85:
{
uint8_t x_20; 
x_20 = l_Array_isEmpty___rarg(x_2);
if (x_20 == 0)
{
lean_object* x_21; 
lean_inc(x_17);
x_21 = l_Lean_Elab_Term_tryPostponeIfMVar(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Array_toList___rarg(x_3);
x_24 = l_Array_toList___rarg(x_2);
x_25 = l_Array_empty___closed__1;
x_26 = 0;
x_27 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_24);
lean_ctor_set(x_27, 4, x_4);
lean_ctor_set(x_27, 5, x_25);
lean_ctor_set(x_27, 6, x_25);
lean_ctor_set(x_27, 7, x_25);
lean_ctor_set(x_27, 8, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*9, x_5);
lean_ctor_set_uint8(x_27, sizeof(void*)*9 + 1, x_26);
x_28 = l_Lean_Elab_Term_ElabAppArgs_main___main___rarg(x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
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
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_21);
if (x_40 == 0)
{
return x_21;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_21, 0);
x_42 = lean_ctor_get(x_21, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_21);
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
x_44 = l_Array_isEmpty___rarg(x_3);
if (x_44 == 0)
{
lean_object* x_45; 
lean_inc(x_17);
x_45 = l_Lean_Elab_Term_tryPostponeIfMVar(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Array_toList___rarg(x_3);
x_48 = l_Array_toList___rarg(x_2);
x_49 = l_Array_empty___closed__1;
x_50 = 0;
x_51 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_17);
lean_ctor_set(x_51, 2, x_47);
lean_ctor_set(x_51, 3, x_48);
lean_ctor_set(x_51, 4, x_4);
lean_ctor_set(x_51, 5, x_49);
lean_ctor_set(x_51, 6, x_49);
lean_ctor_set(x_51, 7, x_49);
lean_ctor_set(x_51, 8, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*9, x_5);
lean_ctor_set_uint8(x_51, sizeof(void*)*9 + 1, x_50);
x_52 = l_Lean_Elab_Term_ElabAppArgs_main___main___rarg(x_51, x_6, x_7, x_8, x_9, x_10, x_11, x_46);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_52, 0);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_52);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_52);
if (x_60 == 0)
{
return x_52;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_52, 0);
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_52);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_45);
if (x_64 == 0)
{
return x_45;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_45, 0);
x_66 = lean_ctor_get(x_45, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_45);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_68 = l_Array_toList___rarg(x_3);
x_69 = l_Array_toList___rarg(x_2);
x_70 = l_Array_empty___closed__1;
x_71 = 0;
x_72 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_17);
lean_ctor_set(x_72, 2, x_68);
lean_ctor_set(x_72, 3, x_69);
lean_ctor_set(x_72, 4, x_4);
lean_ctor_set(x_72, 5, x_70);
lean_ctor_set(x_72, 6, x_70);
lean_ctor_set(x_72, 7, x_70);
lean_ctor_set(x_72, 8, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*9, x_5);
lean_ctor_set_uint8(x_72, sizeof(void*)*9 + 1, x_71);
x_73 = l_Lean_Elab_Term_ElabAppArgs_main___main___rarg(x_72, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
lean_ctor_set(x_73, 0, x_76);
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_73, 0);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_73);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_73);
if (x_81 == 0)
{
return x_73;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_73, 0);
x_83 = lean_ctor_get(x_73, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_73);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_13);
if (x_105 == 0)
{
return x_13;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_13, 0);
x_107 = lean_ctor_get(x_13, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_13);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
lean_object* l___private_Lean_Elab_App_21__elabAppArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l___private_Lean_Elab_App_21__elabAppArgs(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
lean_object* l___private_Lean_Elab_App_22__throwLValError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = l_Lean_indentExpr(x_1);
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_MessageData_ofList___closed__3;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_KernelException_toMessageData___closed__12;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_indentExpr(x_2);
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
}
lean_object* l___private_Lean_Elab_App_22__throwLValError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_22__throwLValError___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_22__throwLValError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_22__throwLValError___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_23__findMethod_x3f___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l___private_Lean_Elab_App_23__findMethod_x3f___main(x_1, x_8, x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
}
}
lean_object* l___private_Lean_Elab_App_23__findMethod_x3f___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_3);
x_4 = l_Lean_Name_append___main(x_2, x_3);
lean_inc(x_4);
lean_inc(x_1);
x_5 = lean_environment_find(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_6 = l_Lean_mkPrivateName(x_1, x_4);
lean_inc(x_6);
lean_inc(x_1);
x_7 = lean_environment_find(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_isStructureLike(x_1, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_10 = l_Lean_getParentStructures(x_1, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_findSomeMAux___main___at___private_Lean_Elab_App_23__findMethod_x3f___main___spec__1(x_1, x_3, x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 0);
lean_dec(x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_6);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_6);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_3);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_5, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_5, 0, x_20);
return x_5;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_4);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_23__findMethod_x3f___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeMAux___main___at___private_Lean_Elab_App_23__findMethod_x3f___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_23__findMethod_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_App_23__findMethod_x3f___main(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, type is not of the form (C ...) where C is a constant");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [..] notation, type is not of the form (C ...) where C is a constant");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure has only ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" field(s)");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, index must be greater than 0");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__20;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a valid \"field\" because environment does not contain '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__22;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__23;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("getOp");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [..] notation because environment does not contain '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__26;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_24__resolveLValAux___closed__27;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_24__resolveLValAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_17; 
x_17 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_17) == 4)
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_48; 
x_22 = lean_st_ref_get(x_9, x_10);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
lean_inc(x_18);
lean_inc(x_26);
x_48 = l_Lean_isStructureLike(x_26, x_18);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_18);
x_49 = l___private_Lean_Elab_App_24__resolveLValAux___closed__15;
x_50 = l___private_Lean_Elab_App_22__throwLValError___rarg(x_1, x_2, x_49, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
lean_dec(x_6);
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
else
{
x_27 = x_24;
goto block_47;
}
block_47:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_inc(x_18);
lean_inc(x_26);
x_28 = l_Lean_getStructureFields(x_26, x_18);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_19, x_29);
lean_dec(x_19);
x_31 = lean_array_get_size(x_28);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_18);
x_33 = l_Nat_repr(x_31);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l___private_Lean_Elab_App_24__resolveLValAux___closed__9;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l___private_Lean_Elab_App_24__resolveLValAux___closed__12;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Elab_App_22__throwLValError___rarg(x_1, x_2, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
lean_dec(x_6);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_18);
x_41 = l_Lean_isStructure(x_26, x_18);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_28);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_18);
lean_ctor_set(x_42, 1, x_30);
if (lean_is_scalar(x_25)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_25;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_27);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_array_fget(x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
lean_inc(x_18);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_18);
lean_ctor_set(x_45, 1, x_18);
lean_ctor_set(x_45, 2, x_44);
if (lean_is_scalar(x_25)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_25;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_27);
return x_46;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_55 = l___private_Lean_Elab_App_24__resolveLValAux___closed__18;
x_56 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
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
}
case 1:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_17, 0);
lean_inc(x_61);
lean_dec(x_17);
x_62 = lean_ctor_get(x_3, 0);
lean_inc(x_62);
lean_dec(x_3);
x_63 = lean_st_ref_get(x_9, x_10);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_61);
lean_inc(x_67);
x_68 = l_Lean_isStructure(x_67, x_61);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_box(0);
lean_inc(x_62);
x_70 = lean_name_mk_string(x_69, x_62);
lean_inc(x_70);
x_71 = l_Lean_Name_append___main(x_61, x_70);
x_72 = lean_ctor_get(x_4, 2);
lean_inc(x_72);
lean_inc(x_71);
x_73 = l_Lean_Name_replacePrefix___main(x_71, x_72, x_69);
lean_dec(x_72);
x_74 = lean_ctor_get(x_6, 1);
lean_inc(x_74);
x_75 = lean_local_ctx_find_from_user_name(x_74, x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
lean_inc(x_61);
x_76 = l___private_Lean_Elab_App_23__findMethod_x3f___main(x_67, x_61, x_70);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_free_object(x_63);
lean_dec(x_61);
x_77 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_77, 0, x_62);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = l___private_Lean_Elab_App_24__resolveLValAux___closed__21;
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l___private_Lean_Elab_App_24__resolveLValAux___closed__24;
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_83, 0, x_71);
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_86 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l___private_Lean_Elab_App_22__throwLValError___rarg(x_1, x_2, x_86, x_4, x_5, x_6, x_7, x_8, x_9, x_66);
lean_dec(x_6);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_71);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_88 = lean_ctor_get(x_76, 0);
lean_inc(x_88);
lean_dec(x_76);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_61);
lean_ctor_set(x_91, 2, x_90);
lean_ctor_set(x_63, 0, x_91);
return x_63;
}
}
else
{
lean_object* x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; 
x_92 = lean_ctor_get(x_75, 0);
lean_inc(x_92);
lean_dec(x_75);
x_93 = l_Lean_LocalDecl_binderInfo(x_92);
x_94 = 4;
x_95 = l_Lean_BinderInfo_beq(x_93, x_94);
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_92);
lean_inc(x_61);
x_96 = l___private_Lean_Elab_App_23__findMethod_x3f___main(x_67, x_61, x_70);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_free_object(x_63);
lean_dec(x_61);
x_97 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_97, 0, x_62);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = l___private_Lean_Elab_App_24__resolveLValAux___closed__21;
x_100 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = l___private_Lean_Elab_App_24__resolveLValAux___closed__24;
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_103, 0, x_71);
x_104 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_106 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l___private_Lean_Elab_App_22__throwLValError___rarg(x_1, x_2, x_106, x_4, x_5, x_6, x_7, x_8, x_9, x_66);
lean_dec(x_6);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_71);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_108 = lean_ctor_get(x_96, 0);
lean_inc(x_108);
lean_dec(x_96);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_61);
lean_ctor_set(x_111, 2, x_110);
lean_ctor_set(x_63, 0, x_111);
return x_63;
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_112 = l_Lean_LocalDecl_toExpr(x_92);
lean_dec(x_92);
x_113 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_113, 0, x_61);
lean_ctor_set(x_113, 1, x_71);
lean_ctor_set(x_113, 2, x_112);
lean_ctor_set(x_63, 0, x_113);
return x_63;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_box(0);
lean_inc(x_62);
x_115 = lean_name_mk_string(x_114, x_62);
lean_inc(x_61);
lean_inc(x_67);
x_116 = l_Lean_findField_x3f___main(x_67, x_61, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_inc(x_115);
x_117 = l_Lean_Name_append___main(x_61, x_115);
x_118 = lean_ctor_get(x_4, 2);
lean_inc(x_118);
lean_inc(x_117);
x_119 = l_Lean_Name_replacePrefix___main(x_117, x_118, x_114);
lean_dec(x_118);
x_120 = lean_ctor_get(x_6, 1);
lean_inc(x_120);
x_121 = lean_local_ctx_find_from_user_name(x_120, x_119);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
lean_inc(x_61);
x_122 = l___private_Lean_Elab_App_23__findMethod_x3f___main(x_67, x_61, x_115);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_free_object(x_63);
lean_dec(x_61);
x_123 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_123, 0, x_62);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = l___private_Lean_Elab_App_24__resolveLValAux___closed__21;
x_126 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = l___private_Lean_Elab_App_24__resolveLValAux___closed__24;
x_128 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_129, 0, x_117);
x_130 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_132 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = l___private_Lean_Elab_App_22__throwLValError___rarg(x_1, x_2, x_132, x_4, x_5, x_6, x_7, x_8, x_9, x_66);
lean_dec(x_6);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_117);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_134 = lean_ctor_get(x_122, 0);
lean_inc(x_134);
lean_dec(x_122);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_61);
lean_ctor_set(x_137, 2, x_136);
lean_ctor_set(x_63, 0, x_137);
return x_63;
}
}
else
{
lean_object* x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; 
x_138 = lean_ctor_get(x_121, 0);
lean_inc(x_138);
lean_dec(x_121);
x_139 = l_Lean_LocalDecl_binderInfo(x_138);
x_140 = 4;
x_141 = l_Lean_BinderInfo_beq(x_139, x_140);
if (x_141 == 0)
{
lean_object* x_142; 
lean_dec(x_138);
lean_inc(x_61);
x_142 = l___private_Lean_Elab_App_23__findMethod_x3f___main(x_67, x_61, x_115);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_free_object(x_63);
lean_dec(x_61);
x_143 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_143, 0, x_62);
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_145 = l___private_Lean_Elab_App_24__resolveLValAux___closed__21;
x_146 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = l___private_Lean_Elab_App_24__resolveLValAux___closed__24;
x_148 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_149, 0, x_117);
x_150 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_152 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = l___private_Lean_Elab_App_22__throwLValError___rarg(x_1, x_2, x_152, x_4, x_5, x_6, x_7, x_8, x_9, x_66);
lean_dec(x_6);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_117);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_154 = lean_ctor_get(x_142, 0);
lean_inc(x_154);
lean_dec(x_142);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_61);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_63, 0, x_157);
return x_63;
}
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_115);
lean_dec(x_67);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_158 = l_Lean_LocalDecl_toExpr(x_138);
lean_dec(x_138);
x_159 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_159, 0, x_61);
lean_ctor_set(x_159, 1, x_117);
lean_ctor_set(x_159, 2, x_158);
lean_ctor_set(x_63, 0, x_159);
return x_63;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_67);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_160 = lean_ctor_get(x_116, 0);
lean_inc(x_160);
lean_dec(x_116);
x_161 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_61);
lean_ctor_set(x_161, 2, x_115);
lean_ctor_set(x_63, 0, x_161);
return x_63;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_162 = lean_ctor_get(x_63, 0);
x_163 = lean_ctor_get(x_63, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_63);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
lean_dec(x_162);
lean_inc(x_61);
lean_inc(x_164);
x_165 = l_Lean_isStructure(x_164, x_61);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_166 = lean_box(0);
lean_inc(x_62);
x_167 = lean_name_mk_string(x_166, x_62);
lean_inc(x_167);
x_168 = l_Lean_Name_append___main(x_61, x_167);
x_169 = lean_ctor_get(x_4, 2);
lean_inc(x_169);
lean_inc(x_168);
x_170 = l_Lean_Name_replacePrefix___main(x_168, x_169, x_166);
lean_dec(x_169);
x_171 = lean_ctor_get(x_6, 1);
lean_inc(x_171);
x_172 = lean_local_ctx_find_from_user_name(x_171, x_170);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
lean_inc(x_61);
x_173 = l___private_Lean_Elab_App_23__findMethod_x3f___main(x_164, x_61, x_167);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_61);
x_174 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_174, 0, x_62);
x_175 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_175, 0, x_174);
x_176 = l___private_Lean_Elab_App_24__resolveLValAux___closed__21;
x_177 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
x_178 = l___private_Lean_Elab_App_24__resolveLValAux___closed__24;
x_179 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_180, 0, x_168);
x_181 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_183 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = l___private_Lean_Elab_App_22__throwLValError___rarg(x_1, x_2, x_183, x_4, x_5, x_6, x_7, x_8, x_9, x_163);
lean_dec(x_6);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_168);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_185 = lean_ctor_get(x_173, 0);
lean_inc(x_185);
lean_dec(x_173);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_61);
lean_ctor_set(x_188, 2, x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_163);
return x_189;
}
}
else
{
lean_object* x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_172, 0);
lean_inc(x_190);
lean_dec(x_172);
x_191 = l_Lean_LocalDecl_binderInfo(x_190);
x_192 = 4;
x_193 = l_Lean_BinderInfo_beq(x_191, x_192);
if (x_193 == 0)
{
lean_object* x_194; 
lean_dec(x_190);
lean_inc(x_61);
x_194 = l___private_Lean_Elab_App_23__findMethod_x3f___main(x_164, x_61, x_167);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_61);
x_195 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_195, 0, x_62);
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_195);
x_197 = l___private_Lean_Elab_App_24__resolveLValAux___closed__21;
x_198 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
x_199 = l___private_Lean_Elab_App_24__resolveLValAux___closed__24;
x_200 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_201, 0, x_168);
x_202 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_203 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_204 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
x_205 = l___private_Lean_Elab_App_22__throwLValError___rarg(x_1, x_2, x_204, x_4, x_5, x_6, x_7, x_8, x_9, x_163);
lean_dec(x_6);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_168);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_206 = lean_ctor_get(x_194, 0);
lean_inc(x_206);
lean_dec(x_194);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_61);
lean_ctor_set(x_209, 2, x_208);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_163);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_167);
lean_dec(x_164);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_211 = l_Lean_LocalDecl_toExpr(x_190);
lean_dec(x_190);
x_212 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_212, 0, x_61);
lean_ctor_set(x_212, 1, x_168);
lean_ctor_set(x_212, 2, x_211);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_163);
return x_213;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_box(0);
lean_inc(x_62);
x_215 = lean_name_mk_string(x_214, x_62);
lean_inc(x_61);
lean_inc(x_164);
x_216 = l_Lean_findField_x3f___main(x_164, x_61, x_215);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_inc(x_215);
x_217 = l_Lean_Name_append___main(x_61, x_215);
x_218 = lean_ctor_get(x_4, 2);
lean_inc(x_218);
lean_inc(x_217);
x_219 = l_Lean_Name_replacePrefix___main(x_217, x_218, x_214);
lean_dec(x_218);
x_220 = lean_ctor_get(x_6, 1);
lean_inc(x_220);
x_221 = lean_local_ctx_find_from_user_name(x_220, x_219);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; 
lean_inc(x_61);
x_222 = l___private_Lean_Elab_App_23__findMethod_x3f___main(x_164, x_61, x_215);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_61);
x_223 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_223, 0, x_62);
x_224 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_224, 0, x_223);
x_225 = l___private_Lean_Elab_App_24__resolveLValAux___closed__21;
x_226 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_224);
x_227 = l___private_Lean_Elab_App_24__resolveLValAux___closed__24;
x_228 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_229, 0, x_217);
x_230 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
x_231 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_232 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = l___private_Lean_Elab_App_22__throwLValError___rarg(x_1, x_2, x_232, x_4, x_5, x_6, x_7, x_8, x_9, x_163);
lean_dec(x_6);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_217);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_234 = lean_ctor_get(x_222, 0);
lean_inc(x_234);
lean_dec(x_222);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_61);
lean_ctor_set(x_237, 2, x_236);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_163);
return x_238;
}
}
else
{
lean_object* x_239; uint8_t x_240; uint8_t x_241; uint8_t x_242; 
x_239 = lean_ctor_get(x_221, 0);
lean_inc(x_239);
lean_dec(x_221);
x_240 = l_Lean_LocalDecl_binderInfo(x_239);
x_241 = 4;
x_242 = l_Lean_BinderInfo_beq(x_240, x_241);
if (x_242 == 0)
{
lean_object* x_243; 
lean_dec(x_239);
lean_inc(x_61);
x_243 = l___private_Lean_Elab_App_23__findMethod_x3f___main(x_164, x_61, x_215);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_61);
x_244 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_244, 0, x_62);
x_245 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_245, 0, x_244);
x_246 = l___private_Lean_Elab_App_24__resolveLValAux___closed__21;
x_247 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_245);
x_248 = l___private_Lean_Elab_App_24__resolveLValAux___closed__24;
x_249 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_250, 0, x_217);
x_251 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_253 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
x_254 = l___private_Lean_Elab_App_22__throwLValError___rarg(x_1, x_2, x_253, x_4, x_5, x_6, x_7, x_8, x_9, x_163);
lean_dec(x_6);
return x_254;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_217);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_255 = lean_ctor_get(x_243, 0);
lean_inc(x_255);
lean_dec(x_243);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_61);
lean_ctor_set(x_258, 2, x_257);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_163);
return x_259;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_215);
lean_dec(x_164);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_260 = l_Lean_LocalDecl_toExpr(x_239);
lean_dec(x_239);
x_261 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_261, 0, x_61);
lean_ctor_set(x_261, 1, x_217);
lean_ctor_set(x_261, 2, x_260);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_163);
return x_262;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_164);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_263 = lean_ctor_get(x_216, 0);
lean_inc(x_263);
lean_dec(x_216);
x_264 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_61);
lean_ctor_set(x_264, 2, x_215);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_163);
return x_265;
}
}
}
}
default: 
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_266 = lean_ctor_get(x_17, 0);
lean_inc(x_266);
lean_dec(x_17);
x_267 = lean_ctor_get(x_3, 0);
lean_inc(x_267);
lean_dec(x_3);
x_268 = lean_st_ref_get(x_9, x_10);
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_270 = lean_ctor_get(x_268, 0);
x_271 = lean_ctor_get(x_268, 1);
x_272 = lean_ctor_get(x_270, 0);
lean_inc(x_272);
lean_dec(x_270);
x_273 = l___private_Lean_Elab_App_24__resolveLValAux___closed__25;
x_274 = lean_name_mk_string(x_266, x_273);
lean_inc(x_274);
x_275 = lean_environment_find(x_272, x_274);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_free_object(x_268);
lean_dec(x_267);
x_276 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_276, 0, x_274);
x_277 = l___private_Lean_Elab_App_24__resolveLValAux___closed__28;
x_278 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_276);
x_279 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_280 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
x_281 = l___private_Lean_Elab_App_22__throwLValError___rarg(x_1, x_2, x_280, x_4, x_5, x_6, x_7, x_8, x_9, x_271);
lean_dec(x_6);
return x_281;
}
else
{
lean_object* x_282; 
lean_dec(x_275);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_282 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_282, 0, x_274);
lean_ctor_set(x_282, 1, x_267);
lean_ctor_set(x_268, 0, x_282);
return x_268;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_283 = lean_ctor_get(x_268, 0);
x_284 = lean_ctor_get(x_268, 1);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_268);
x_285 = lean_ctor_get(x_283, 0);
lean_inc(x_285);
lean_dec(x_283);
x_286 = l___private_Lean_Elab_App_24__resolveLValAux___closed__25;
x_287 = lean_name_mk_string(x_266, x_286);
lean_inc(x_287);
x_288 = lean_environment_find(x_285, x_287);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_267);
x_289 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_289, 0, x_287);
x_290 = l___private_Lean_Elab_App_24__resolveLValAux___closed__28;
x_291 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_289);
x_292 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_293 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
x_294 = l___private_Lean_Elab_App_22__throwLValError___rarg(x_1, x_2, x_293, x_4, x_5, x_6, x_7, x_8, x_9, x_284);
lean_dec(x_6);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_288);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_295 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_295, 0, x_287);
lean_ctor_set(x_295, 1, x_267);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_284);
return x_296;
}
}
}
}
}
else
{
lean_object* x_297; 
lean_dec(x_17);
x_297 = lean_box(0);
x_11 = x_297;
goto block_16;
}
block_16:
{
lean_dec(x_11);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = l___private_Lean_Elab_App_24__resolveLValAux___closed__6;
x_13 = l___private_Lean_Elab_App_22__throwLValError___rarg(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_14 = l___private_Lean_Elab_App_24__resolveLValAux___closed__3;
x_15 = l___private_Lean_Elab_App_22__throwLValError___rarg(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_15;
}
}
}
}
lean_object* l___private_Lean_Elab_App_24__resolveLValAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_24__resolveLValAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_25__consumeImplicits___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 7)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; uint8_t x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 2);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_11, sizeof(void*)*3);
x_18 = (uint8_t)((x_17 << 24) >> 61);
x_19 = l_Lean_BinderInfo_isExplicit(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_10);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_21 = 0;
x_22 = lean_box(0);
lean_inc(x_5);
x_23 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_20, x_21, x_22, x_5, x_6, x_7, x_8, x_13);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_24);
x_26 = l_Lean_mkApp(x_1, x_24);
x_27 = lean_expr_instantiate1(x_16, x_24);
lean_dec(x_24);
lean_dec(x_16);
x_1 = x_26;
x_2 = x_27;
x_9 = x_25;
goto _start;
}
else
{
lean_object* x_29; 
x_29 = l_Lean_Expr_getOptParamDefault_x3f(x_15);
lean_dec(x_15);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_11);
lean_ctor_set(x_10, 0, x_30);
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_free_object(x_10);
lean_dec(x_11);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_31);
x_32 = l_Lean_mkApp(x_1, x_31);
x_33 = lean_expr_instantiate1(x_16, x_31);
lean_dec(x_31);
lean_dec(x_16);
x_1 = x_32;
x_2 = x_33;
x_9 = x_13;
goto _start;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_38; uint8_t x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_11, 2);
lean_inc(x_37);
x_38 = lean_ctor_get_uint64(x_11, sizeof(void*)*3);
x_39 = (uint8_t)((x_38 << 24) >> 61);
x_40 = l_Lean_BinderInfo_isExplicit(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_11);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_42 = 0;
x_43 = lean_box(0);
lean_inc(x_5);
x_44 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_41, x_42, x_43, x_5, x_6, x_7, x_8, x_35);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_45);
x_47 = l_Lean_mkApp(x_1, x_45);
x_48 = lean_expr_instantiate1(x_37, x_45);
lean_dec(x_45);
lean_dec(x_37);
x_1 = x_47;
x_2 = x_48;
x_9 = x_46;
goto _start;
}
else
{
lean_object* x_50; 
x_50 = l_Lean_Expr_getOptParamDefault_x3f(x_36);
lean_dec(x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_11);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_35);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_11);
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
lean_dec(x_50);
lean_inc(x_53);
x_54 = l_Lean_mkApp(x_1, x_53);
x_55 = lean_expr_instantiate1(x_37, x_53);
lean_dec(x_53);
lean_dec(x_37);
x_1 = x_54;
x_2 = x_55;
x_9 = x_35;
goto _start;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_57 = !lean_is_exclusive(x_10);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_10, 0);
lean_dec(x_58);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_11);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_10, 1);
lean_inc(x_60);
lean_dec(x_10);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_11);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_10);
if (x_63 == 0)
{
return x_10;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_10, 0);
x_65 = lean_ctor_get(x_10, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_10);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
lean_object* l___private_Lean_Elab_App_25__consumeImplicits___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_25__consumeImplicits___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_25__consumeImplicits(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_25__consumeImplicits___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_25__consumeImplicits___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_25__consumeImplicits(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_26__resolveLValLoop___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_1, x_2);
x_15 = l_Lean_Elab_logException___at___private_Lean_Elab_Term_10__exceptionToSorry___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_2);
x_2 = x_18;
x_9 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_26__resolveLValLoop___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l___private_Lean_Elab_App_25__consumeImplicits___main(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
x_18 = l_Lean_Elab_Term_tryPostponeIfMVar(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_17);
lean_inc(x_16);
x_20 = l___private_Lean_Elab_App_24__resolveLValAux(x_16, x_17, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_20, 0, x_13);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_13, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_13);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_28 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_17, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_16);
lean_dec(x_1);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Array_forMAux___main___at___private_Lean_Elab_App_26__resolveLValLoop___main___spec__1(x_4, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_26);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_26);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_dec(x_28);
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
lean_dec(x_29);
x_43 = lean_array_push(x_4, x_26);
x_2 = x_16;
x_3 = x_42;
x_4 = x_43;
x_11 = x_41;
goto _start;
}
}
else
{
uint8_t x_45; 
lean_dec(x_26);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_28);
if (x_45 == 0)
{
return x_28;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_28, 0);
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_28);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_free_object(x_13);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_18);
if (x_49 == 0)
{
return x_18;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_18, 0);
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_18);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_13, 0);
x_54 = lean_ctor_get(x_13, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_13);
lean_inc(x_54);
x_55 = l_Lean_Elab_Term_tryPostponeIfMVar(x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_54);
lean_inc(x_53);
x_57 = l___private_Lean_Elab_App_24__resolveLValAux(x_53, x_54, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_54);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_58);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_dec(x_57);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_65 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_54, x_7, x_8, x_9, x_10, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_53);
lean_dec(x_1);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Array_forMAux___main___at___private_Lean_Elab_App_26__resolveLValLoop___main___spec__1(x_4, x_68, x_5, x_6, x_7, x_8, x_9, x_10, x_67);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
 lean_ctor_set_tag(x_72, 1);
}
lean_ctor_set(x_72, 0, x_63);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_63);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_75 = x_69;
} else {
 lean_dec_ref(x_69);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_65, 1);
lean_inc(x_77);
lean_dec(x_65);
x_78 = lean_ctor_get(x_66, 0);
lean_inc(x_78);
lean_dec(x_66);
x_79 = lean_array_push(x_4, x_63);
x_2 = x_53;
x_3 = x_78;
x_4 = x_79;
x_11 = x_77;
goto _start;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_63);
lean_dec(x_53);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_81 = lean_ctor_get(x_65, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_65, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_83 = x_65;
} else {
 lean_dec_ref(x_65);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_85 = lean_ctor_get(x_55, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_55, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_87 = x_55;
} else {
 lean_dec_ref(x_55);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_12);
if (x_89 == 0)
{
return x_12;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_12, 0);
x_91 = lean_ctor_get(x_12, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_12);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_26__resolveLValLoop___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forMAux___main___at___private_Lean_Elab_App_26__resolveLValLoop___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_26__resolveLValLoop___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_App_26__resolveLValLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_26__resolveLValLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_App_26__resolveLValLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_26__resolveLValLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_App_26__resolveLValLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_27__resolveLVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Array_empty___closed__1;
x_14 = l___private_Lean_Elab_App_26__resolveLValLoop___main(x_2, x_1, x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l___private_Lean_Elab_App_27__resolveLVal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_27__resolveLVal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("self");
return x_1;
}
}
static lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_box(0);
lean_inc(x_3);
x_14 = l_Lean_Elab_Term_mkConst(x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1___closed__2;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_mkOptionalNode___closed__2;
x_21 = lean_array_push(x_20, x_19);
x_22 = lean_box(0);
x_23 = l_Array_empty___closed__1;
x_24 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l___private_Lean_Elab_App_21__elabAppArgs(x_15, x_21, x_23, x_22, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
lean_dec(x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_1 = x_26;
x_2 = x_12;
x_9 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_28__mkBaseProjections___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to access field in parent structure");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_28__mkBaseProjections___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_28__mkBaseProjections___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_28__mkBaseProjections___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_28__mkBaseProjections___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_28__mkBaseProjections(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_getPathToBaseStructure_x3f(x_14, x_1, x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_16 = l___private_Lean_Elab_App_28__mkBaseProjections___closed__3;
x_17 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1(x_3, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_19;
}
}
}
lean_object* l___private_Lean_Elab_App_28__mkBaseProjections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_28__mkBaseProjections(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_29__addLValArg___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_3);
return x_13;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, function '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_29__addLValArg___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_29__addLValArg___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not have explicit argument with type (");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_29__addLValArg___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_29__addLValArg___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ...)");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_29__addLValArg___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_29__addLValArg___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, insufficient number of arguments for '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_29__addLValArg___main___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_29__addLValArg___main___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_29__addLValArg___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
if (lean_obj_tag(x_7) == 7)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; uint8_t x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
x_29 = lean_ctor_get(x_7, 2);
x_30 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
x_31 = (uint8_t)((x_30 << 24) >> 61);
x_32 = l_Lean_BinderInfo_isExplicit(x_31);
if (x_32 == 0)
{
x_7 = x_29;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_29__addLValArg___main___spec__1(x_27, x_6, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Expr_consumeMData___main(x_28);
x_37 = l_Lean_Expr_isAppOf(x_36, x_1);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_array_get_size(x_4);
x_39 = lean_nat_dec_lt(x_5, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_40, 0, x_2);
x_41 = l___private_Lean_Elab_App_29__addLValArg___main___closed__12;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_44, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_5, x_46);
lean_dec(x_5);
x_5 = x_47;
x_7 = x_29;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_3);
x_50 = l_Array_insertAt___rarg(x_4, x_5, x_49);
lean_dec(x_5);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_14);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_35, 0);
lean_inc(x_52);
lean_dec(x_35);
x_53 = l_Array_eraseIdx___rarg(x_6, x_52);
lean_dec(x_52);
x_6 = x_53;
x_7 = x_29;
goto _start;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = lean_box(0);
x_15 = x_55;
goto block_26;
}
block_26:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_2);
x_17 = l___private_Lean_Elab_App_29__addLValArg___main___closed__3;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l___private_Lean_Elab_App_29__addLValArg___main___closed__6;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Lean_Elab_App_29__addLValArg___main___closed__9;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_25;
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_29__addLValArg___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_29__addLValArg___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_29__addLValArg___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_App_29__addLValArg___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_15;
}
}
lean_object* l___private_Lean_Elab_App_29__addLValArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_App_29__addLValArg___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
lean_object* l___private_Lean_Elab_App_29__addLValArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_App_29__addLValArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("idx");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_30__elabAppLValsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_App_21__elabAppArgs(x_5, x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
x_17 = l___private_Lean_Elab_App_27__resolveLVal(x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 2);
lean_inc(x_24);
lean_dec(x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = l___private_Lean_Elab_App_28__mkBaseProjections(x_22, x_23, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Name_append___main(x_22, x_24);
lean_dec(x_22);
x_29 = lean_box(0);
lean_inc(x_7);
x_30 = l_Lean_Elab_Term_mkConst(x_28, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_List_isEmpty___rarg(x_16);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_26);
x_35 = l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1___closed__2;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_mkOptionalNode___closed__2;
x_38 = lean_array_push(x_37, x_36);
x_39 = lean_box(0);
x_40 = l_Array_empty___closed__1;
x_41 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_42 = l___private_Lean_Elab_App_21__elabAppArgs(x_31, x_38, x_40, x_39, x_41, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
lean_dec(x_38);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_5 = x_43;
x_6 = x_16;
x_13 = x_44;
goto _start;
}
else
{
uint8_t x_46; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_16);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_26);
x_51 = l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1___closed__2;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_inc(x_7);
x_53 = l_Lean_Elab_Term_addNamedArg(x_1, x_52, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l___private_Lean_Elab_App_21__elabAppArgs(x_31, x_54, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_55);
lean_dec(x_2);
lean_dec(x_54);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 0);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_53);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_26);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_30);
if (x_61 == 0)
{
return x_30;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_30, 0);
x_63 = lean_ctor_get(x_30, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_30);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_25);
if (x_65 == 0)
{
return x_25;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_25, 0);
x_67 = lean_ctor_get(x_25, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_25);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
case 1:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_17, 1);
lean_inc(x_69);
lean_dec(x_17);
x_70 = lean_ctor_get(x_18, 0);
lean_inc(x_70);
lean_dec(x_18);
x_71 = lean_ctor_get(x_19, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_19, 1);
lean_inc(x_72);
lean_dec(x_19);
x_73 = l_Lean_mkProj(x_71, x_72, x_70);
x_5 = x_73;
x_6 = x_16;
x_13 = x_69;
goto _start;
}
case 2:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_17, 1);
lean_inc(x_75);
lean_dec(x_17);
x_76 = lean_ctor_get(x_18, 0);
lean_inc(x_76);
lean_dec(x_18);
x_77 = lean_ctor_get(x_19, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_19, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_19, 2);
lean_inc(x_79);
lean_dec(x_19);
x_80 = lean_name_eq(x_77, x_78);
if (x_80 == 0)
{
lean_object* x_81; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_81 = l___private_Lean_Elab_App_28__mkBaseProjections(x_77, x_78, x_76, x_7, x_8, x_9, x_10, x_11, x_12, x_75);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_box(0);
lean_inc(x_7);
lean_inc(x_79);
x_85 = l_Lean_Elab_Term_mkConst(x_79, x_84, x_7, x_8, x_9, x_10, x_11, x_12, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_List_isEmpty___rarg(x_16);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; 
lean_dec(x_79);
lean_dec(x_77);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_82);
x_90 = l_Lean_mkOptionalNode___closed__2;
x_91 = lean_array_push(x_90, x_89);
x_92 = lean_box(0);
x_93 = l_Array_empty___closed__1;
x_94 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_95 = l___private_Lean_Elab_App_21__elabAppArgs(x_86, x_93, x_91, x_92, x_94, x_7, x_8, x_9, x_10, x_11, x_12, x_87);
lean_dec(x_91);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_5 = x_96;
x_6 = x_16;
x_13 = x_97;
goto _start;
}
else
{
uint8_t x_99; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_95);
if (x_99 == 0)
{
return x_95;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_95, 0);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_95);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; 
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_86);
x_103 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_86, x_7, x_8, x_9, x_10, x_11, x_12, x_87);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_1);
x_107 = l___private_Lean_Elab_App_29__addLValArg___main(x_77, x_79, x_82, x_2, x_106, x_1, x_104, x_7, x_8, x_9, x_10, x_11, x_12, x_105);
lean_dec(x_104);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l___private_Lean_Elab_App_21__elabAppArgs(x_86, x_1, x_108, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_109);
lean_dec(x_108);
lean_dec(x_1);
return x_110;
}
else
{
uint8_t x_111; 
lean_dec(x_86);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_107);
if (x_111 == 0)
{
return x_107;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_107, 0);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_107);
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
lean_dec(x_86);
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_103);
if (x_115 == 0)
{
return x_103;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_103, 0);
x_117 = lean_ctor_get(x_103, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_103);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_85);
if (x_119 == 0)
{
return x_85;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_85, 0);
x_121 = lean_ctor_get(x_85, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_85);
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
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_81);
if (x_123 == 0)
{
return x_81;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_81, 0);
x_125 = lean_ctor_get(x_81, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_81);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_78);
x_127 = lean_box(0);
lean_inc(x_7);
lean_inc(x_79);
x_128 = l_Lean_Elab_Term_mkConst(x_79, x_127, x_7, x_8, x_9, x_10, x_11, x_12, x_75);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_List_isEmpty___rarg(x_16);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; 
lean_dec(x_79);
lean_dec(x_77);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_76);
x_133 = l_Lean_mkOptionalNode___closed__2;
x_134 = lean_array_push(x_133, x_132);
x_135 = lean_box(0);
x_136 = l_Array_empty___closed__1;
x_137 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_138 = l___private_Lean_Elab_App_21__elabAppArgs(x_129, x_136, x_134, x_135, x_137, x_7, x_8, x_9, x_10, x_11, x_12, x_130);
lean_dec(x_134);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_5 = x_139;
x_6 = x_16;
x_13 = x_140;
goto _start;
}
else
{
uint8_t x_142; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_138);
if (x_142 == 0)
{
return x_138;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_138, 0);
x_144 = lean_ctor_get(x_138, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_138);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
lean_object* x_146; 
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_129);
x_146 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_129, x_7, x_8, x_9, x_10, x_11, x_12, x_130);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_1);
x_150 = l___private_Lean_Elab_App_29__addLValArg___main(x_77, x_79, x_76, x_2, x_149, x_1, x_147, x_7, x_8, x_9, x_10, x_11, x_12, x_148);
lean_dec(x_147);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = l___private_Lean_Elab_App_21__elabAppArgs(x_129, x_1, x_151, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_152);
lean_dec(x_151);
lean_dec(x_1);
return x_153;
}
else
{
uint8_t x_154; 
lean_dec(x_129);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_154 = !lean_is_exclusive(x_150);
if (x_154 == 0)
{
return x_150;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_150, 0);
x_156 = lean_ctor_get(x_150, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_150);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_129);
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_146);
if (x_158 == 0)
{
return x_146;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_146, 0);
x_160 = lean_ctor_get(x_146, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_146);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_79);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
case 3:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_166 = lean_ctor_get(x_17, 1);
lean_inc(x_166);
lean_dec(x_17);
x_167 = lean_ctor_get(x_18, 0);
lean_inc(x_167);
lean_dec(x_18);
x_168 = lean_ctor_get(x_19, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_19, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_19, 2);
lean_inc(x_170);
lean_dec(x_19);
x_171 = l_List_isEmpty___rarg(x_16);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; 
lean_dec(x_169);
lean_dec(x_168);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_167);
x_173 = l_Lean_mkOptionalNode___closed__2;
x_174 = lean_array_push(x_173, x_172);
x_175 = lean_box(0);
x_176 = l_Array_empty___closed__1;
x_177 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_178 = l___private_Lean_Elab_App_21__elabAppArgs(x_170, x_176, x_174, x_175, x_177, x_7, x_8, x_9, x_10, x_11, x_12, x_166);
lean_dec(x_174);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_5 = x_179;
x_6 = x_16;
x_13 = x_180;
goto _start;
}
else
{
uint8_t x_182; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_178);
if (x_182 == 0)
{
return x_178;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_178, 0);
x_184 = lean_ctor_get(x_178, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_178);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
else
{
lean_object* x_186; 
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_170);
x_186 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_170, x_7, x_8, x_9, x_10, x_11, x_12, x_166);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_1);
x_190 = l___private_Lean_Elab_App_29__addLValArg___main(x_168, x_169, x_167, x_2, x_189, x_1, x_187, x_7, x_8, x_9, x_10, x_11, x_12, x_188);
lean_dec(x_187);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = l___private_Lean_Elab_App_21__elabAppArgs(x_170, x_1, x_191, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_192);
lean_dec(x_191);
lean_dec(x_1);
return x_193;
}
else
{
uint8_t x_194; 
lean_dec(x_170);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_194 = !lean_is_exclusive(x_190);
if (x_194 == 0)
{
return x_190;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_190, 0);
x_196 = lean_ctor_get(x_190, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_190);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_186);
if (x_198 == 0)
{
return x_186;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_186, 0);
x_200 = lean_ctor_get(x_186, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_186);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
}
default: 
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_202 = lean_ctor_get(x_17, 1);
lean_inc(x_202);
lean_dec(x_17);
x_203 = lean_ctor_get(x_18, 0);
lean_inc(x_203);
lean_dec(x_18);
x_204 = lean_ctor_get(x_19, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_19, 1);
lean_inc(x_205);
lean_dec(x_19);
x_206 = lean_box(0);
lean_inc(x_7);
x_207 = l_Lean_Elab_Term_mkConst(x_204, x_206, x_7, x_8, x_9, x_10, x_11, x_12, x_202);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = l_List_isEmpty___rarg(x_16);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; 
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_203);
x_212 = l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1___closed__2;
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
x_214 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_214, 0, x_205);
x_215 = l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__2;
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
x_217 = l_Lean_mkAppStx___closed__9;
x_218 = lean_array_push(x_217, x_213);
x_219 = lean_array_push(x_218, x_216);
x_220 = lean_box(0);
x_221 = l_Array_empty___closed__1;
x_222 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_223 = l___private_Lean_Elab_App_21__elabAppArgs(x_208, x_219, x_221, x_220, x_222, x_7, x_8, x_9, x_10, x_11, x_12, x_209);
lean_dec(x_219);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_5 = x_224;
x_6 = x_16;
x_13 = x_225;
goto _start;
}
else
{
uint8_t x_227; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_227 = !lean_is_exclusive(x_223);
if (x_227 == 0)
{
return x_223;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_223, 0);
x_229 = lean_ctor_get(x_223, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_223);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_16);
x_231 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_231, 0, x_203);
x_232 = l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1___closed__2;
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
lean_inc(x_7);
x_234 = l_Lean_Elab_Term_addNamedArg(x_1, x_233, x_7, x_8, x_9, x_10, x_11, x_12, x_209);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_237, 0, x_205);
x_238 = l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__2;
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_237);
lean_inc(x_7);
x_240 = l_Lean_Elab_Term_addNamedArg(x_235, x_239, x_7, x_8, x_9, x_10, x_11, x_12, x_236);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = l___private_Lean_Elab_App_21__elabAppArgs(x_208, x_241, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_242);
lean_dec(x_2);
lean_dec(x_241);
return x_243;
}
else
{
uint8_t x_244; 
lean_dec(x_208);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_244 = !lean_is_exclusive(x_240);
if (x_244 == 0)
{
return x_240;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_240, 0);
x_246 = lean_ctor_get(x_240, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_240);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
}
}
else
{
uint8_t x_248; 
lean_dec(x_208);
lean_dec(x_205);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_248 = !lean_is_exclusive(x_234);
if (x_248 == 0)
{
return x_234;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_234, 0);
x_250 = lean_ctor_get(x_234, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_234);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
}
}
else
{
uint8_t x_252; 
lean_dec(x_205);
lean_dec(x_203);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_252 = !lean_is_exclusive(x_207);
if (x_252 == 0)
{
return x_207;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_207, 0);
x_254 = lean_ctor_get(x_207, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_207);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
}
}
else
{
uint8_t x_256; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_256 = !lean_is_exclusive(x_17);
if (x_256 == 0)
{
return x_17;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_17, 0);
x_258 = lean_ctor_get(x_17, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_17);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_30__elabAppLValsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Elab_App_30__elabAppLValsAux___main(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l___private_Lean_Elab_App_30__elabAppLValsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_App_30__elabAppLValsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
lean_object* l___private_Lean_Elab_App_30__elabAppLValsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Elab_App_30__elabAppLValsAux(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Elab_App_31__elabAppLVals___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of field notation with `@` modifier");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_31__elabAppLVals___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_31__elabAppLVals___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_31__elabAppLVals___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_31__elabAppLVals___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_31__elabAppLVals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = l_List_isEmpty___rarg(x_2);
if (x_14 == 0)
{
if (x_6 == 0)
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_App_30__elabAppLValsAux___main(x_3, x_4, x_5, x_6, x_1, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l___private_Lean_Elab_App_31__elabAppLVals___closed__3;
x_17 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; 
x_22 = l___private_Lean_Elab_App_30__elabAppLValsAux___main(x_3, x_4, x_5, x_6, x_1, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_22;
}
}
}
lean_object* l___private_Lean_Elab_App_31__elabAppLVals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l___private_Lean_Elab_App_31__elabAppLVals(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_3, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_3, x_15);
lean_dec(x_3);
x_17 = lean_array_fget(x_2, x_16);
x_18 = l_Lean_Elab_Term_elabLevel(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_5);
x_3 = x_16;
x_4 = lean_box(0);
x_5 = x_21;
x_12 = x_20;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_16);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_3);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_12);
return x_27;
}
}
}
lean_object* l_Lean_Elab_Term_elabExplicitUnivs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = lean_array_get_size(x_1);
x_11 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(x_1, x_1, x_10, lean_box(0), x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_elabExplicitUnivs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_elabExplicitUnivs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_32__elabAppFnId___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_32__elabAppFnId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_32__elabAppFnId___spec__1___rarg), 1, 0);
return x_7;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__2(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_52; 
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_List_map___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__2(x_20);
lean_inc(x_1);
x_22 = l_List_append___rarg(x_21, x_1);
x_23 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_52 = l___private_Lean_Elab_App_31__elabAppLVals(x_19, x_22, x_2, x_3, x_4, x_5, x_9, x_10, x_11, x_12, x_13, x_14, x_25);
if (lean_obj_tag(x_52) == 0)
{
if (x_6 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_26);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Elab_Term_SavedState_restore(x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_57);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 1);
x_61 = lean_ctor_get(x_58, 0);
lean_dec(x_61);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_58, 0, x_53);
x_62 = lean_array_push(x_7, x_58);
x_7 = x_62;
x_8 = x_18;
x_15 = x_60;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_53);
lean_ctor_set(x_65, 1, x_56);
x_66 = lean_array_push(x_7, x_65);
x_7 = x_66;
x_8 = x_18;
x_15 = x_64;
goto _start;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_52, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
x_70 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_4);
x_71 = l_Lean_Elab_Term_ensureHasType(x_4, x_68, x_70, x_9, x_10, x_11, x_12, x_13, x_14, x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_26);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Elab_Term_SavedState_restore(x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_76);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_77, 1);
x_80 = lean_ctor_get(x_77, 0);
lean_dec(x_80);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_77, 0, x_72);
x_81 = lean_array_push(x_7, x_77);
x_7 = x_81;
x_8 = x_18;
x_15 = x_79;
goto _start;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
lean_dec(x_77);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_72);
lean_ctor_set(x_84, 1, x_75);
x_85 = lean_array_push(x_7, x_84);
x_7 = x_85;
x_8 = x_18;
x_15 = x_83;
goto _start;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_71, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_71, 1);
lean_inc(x_88);
lean_dec(x_71);
x_27 = x_87;
x_28 = x_88;
goto block_51;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_52, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_52, 1);
lean_inc(x_90);
lean_dec(x_52);
x_27 = x_89;
x_28 = x_90;
goto block_51;
}
block_51:
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_26);
x_29 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_Term_SavedState_restore(x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_31);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 1);
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 0, x_27);
x_36 = lean_array_push(x_7, x_32);
x_7 = x_36;
x_8 = x_18;
x_15 = x_34;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_30);
x_40 = lean_array_push(x_7, x_39);
x_7 = x_40;
x_8 = x_18;
x_15 = x_38;
goto _start;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_ctor_get(x_27, 0);
lean_inc(x_42);
x_43 = l_Lean_Elab_postponeExceptionId;
x_44 = lean_nat_dec_eq(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_26)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_26;
 lean_ctor_set_tag(x_45, 1);
}
lean_ctor_set(x_45, 0, x_27);
lean_ctor_set(x_45, 1, x_28);
return x_45;
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_26);
x_46 = l_Lean_Elab_Term_SavedState_restore(x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 0, x_27);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_27);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_52; 
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_List_map___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__2(x_20);
lean_inc(x_1);
x_22 = l_List_append___rarg(x_21, x_1);
x_23 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_52 = l___private_Lean_Elab_App_31__elabAppLVals(x_19, x_22, x_2, x_3, x_4, x_5, x_9, x_10, x_11, x_12, x_13, x_14, x_25);
if (lean_obj_tag(x_52) == 0)
{
if (x_6 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_26);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Elab_Term_SavedState_restore(x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_57);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 1);
x_61 = lean_ctor_get(x_58, 0);
lean_dec(x_61);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_58, 0, x_53);
x_62 = lean_array_push(x_7, x_58);
x_7 = x_62;
x_8 = x_18;
x_15 = x_60;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_53);
lean_ctor_set(x_65, 1, x_56);
x_66 = lean_array_push(x_7, x_65);
x_7 = x_66;
x_8 = x_18;
x_15 = x_64;
goto _start;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_52, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
x_70 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_4);
x_71 = l_Lean_Elab_Term_ensureHasType(x_4, x_68, x_70, x_9, x_10, x_11, x_12, x_13, x_14, x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_26);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Elab_Term_SavedState_restore(x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_76);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_77, 1);
x_80 = lean_ctor_get(x_77, 0);
lean_dec(x_80);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_77, 0, x_72);
x_81 = lean_array_push(x_7, x_77);
x_7 = x_81;
x_8 = x_18;
x_15 = x_79;
goto _start;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
lean_dec(x_77);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_72);
lean_ctor_set(x_84, 1, x_75);
x_85 = lean_array_push(x_7, x_84);
x_7 = x_85;
x_8 = x_18;
x_15 = x_83;
goto _start;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_71, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_71, 1);
lean_inc(x_88);
lean_dec(x_71);
x_27 = x_87;
x_28 = x_88;
goto block_51;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_52, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_52, 1);
lean_inc(x_90);
lean_dec(x_52);
x_27 = x_89;
x_28 = x_90;
goto block_51;
}
block_51:
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_26);
x_29 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_Term_SavedState_restore(x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_31);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 1);
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 0, x_27);
x_36 = lean_array_push(x_7, x_32);
x_7 = x_36;
x_8 = x_18;
x_15 = x_34;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_30);
x_40 = lean_array_push(x_7, x_39);
x_7 = x_40;
x_8 = x_18;
x_15 = x_38;
goto _start;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_ctor_get(x_27, 0);
lean_inc(x_42);
x_43 = l_Lean_Elab_postponeExceptionId;
x_44 = lean_nat_dec_eq(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_26)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_26;
 lean_ctor_set_tag(x_45, 1);
}
lean_ctor_set(x_45, 0, x_27);
lean_ctor_set(x_45, 1, x_28);
return x_45;
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_26);
x_46 = l_Lean_Elab_Term_SavedState_restore(x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 0, x_27);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_27);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_32__elabAppFnId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_14, 3);
lean_inc(x_22);
x_23 = l_Lean_replaceRef(x_1, x_22);
lean_dec(x_1);
x_24 = l_Lean_replaceRef(x_23, x_22);
lean_dec(x_23);
x_25 = l_Lean_replaceRef(x_24, x_22);
lean_dec(x_22);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_25);
lean_inc(x_12);
lean_inc(x_10);
x_27 = l_Lean_Elab_Term_resolveName(x_17, x_18, x_2, x_10, x_11, x_12, x_13, x_26, x_15, x_16);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_10, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_10, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_10, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_10, 5);
lean_inc(x_35);
x_36 = lean_ctor_get(x_10, 6);
lean_inc(x_36);
x_37 = lean_ctor_get(x_10, 7);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_10, sizeof(void*)*8);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_List_lengthAux___main___rarg(x_28, x_39);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_dec_eq(x_40, x_41);
if (x_8 == 0)
{
uint8_t x_72; 
x_72 = lean_nat_dec_lt(x_41, x_40);
lean_dec(x_40);
x_43 = x_72;
goto block_71;
}
else
{
uint8_t x_73; 
lean_dec(x_40);
x_73 = 1;
x_43 = x_73;
goto block_71;
}
block_71:
{
if (x_42 == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_10);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_10, 7);
lean_dec(x_45);
x_46 = lean_ctor_get(x_10, 6);
lean_dec(x_46);
x_47 = lean_ctor_get(x_10, 5);
lean_dec(x_47);
x_48 = lean_ctor_get(x_10, 4);
lean_dec(x_48);
x_49 = lean_ctor_get(x_10, 3);
lean_dec(x_49);
x_50 = lean_ctor_get(x_10, 2);
lean_dec(x_50);
x_51 = lean_ctor_get(x_10, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_10, 0);
lean_dec(x_52);
x_53 = 0;
lean_ctor_set_uint8(x_10, sizeof(void*)*8 + 1, x_53);
x_54 = l_List_foldlM___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_43, x_9, x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_29);
return x_54;
}
else
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_10);
x_55 = 0;
x_56 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_56, 0, x_30);
lean_ctor_set(x_56, 1, x_31);
lean_ctor_set(x_56, 2, x_32);
lean_ctor_set(x_56, 3, x_33);
lean_ctor_set(x_56, 4, x_34);
lean_ctor_set(x_56, 5, x_35);
lean_ctor_set(x_56, 6, x_36);
lean_ctor_set(x_56, 7, x_37);
lean_ctor_set_uint8(x_56, sizeof(void*)*8, x_38);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 1, x_55);
x_57 = l_List_foldlM___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_43, x_9, x_28, x_56, x_11, x_12, x_13, x_14, x_15, x_29);
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_10);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_10, 7);
lean_dec(x_59);
x_60 = lean_ctor_get(x_10, 6);
lean_dec(x_60);
x_61 = lean_ctor_get(x_10, 5);
lean_dec(x_61);
x_62 = lean_ctor_get(x_10, 4);
lean_dec(x_62);
x_63 = lean_ctor_get(x_10, 3);
lean_dec(x_63);
x_64 = lean_ctor_get(x_10, 2);
lean_dec(x_64);
x_65 = lean_ctor_get(x_10, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_10, 0);
lean_dec(x_66);
x_67 = l_List_foldlM___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__4(x_3, x_4, x_5, x_6, x_7, x_43, x_9, x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_29);
return x_67;
}
else
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get_uint8(x_10, sizeof(void*)*8 + 1);
lean_dec(x_10);
x_69 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_69, 0, x_30);
lean_ctor_set(x_69, 1, x_31);
lean_ctor_set(x_69, 2, x_32);
lean_ctor_set(x_69, 3, x_33);
lean_ctor_set(x_69, 4, x_34);
lean_ctor_set(x_69, 5, x_35);
lean_ctor_set(x_69, 6, x_36);
lean_ctor_set(x_69, 7, x_37);
lean_ctor_set_uint8(x_69, sizeof(void*)*8, x_38);
lean_ctor_set_uint8(x_69, sizeof(void*)*8 + 1, x_68);
x_70 = l_List_foldlM___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__4(x_3, x_4, x_5, x_6, x_7, x_43, x_9, x_28, x_69, x_11, x_12, x_13, x_14, x_15, x_29);
return x_70;
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_27);
if (x_74 == 0)
{
return x_27;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_27, 0);
x_76 = lean_ctor_get(x_27, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_27);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_32__elabAppFnId___spec__1___rarg(x_16);
return x_78;
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_32__elabAppFnId___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_32__elabAppFnId___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_List_foldlM___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__3(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_List_foldlM___main___at___private_Lean_Elab_App_32__elabAppFnId___spec__4(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
lean_object* l___private_Lean_Elab_App_32__elabAppFnId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = lean_unbox(x_8);
lean_dec(x_8);
x_19 = l___private_Lean_Elab_App_32__elabAppFnId(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_App_33__elabAppFn___main___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_System_FilePath_dirName___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_List_map___main___at___private_Lean_Elab_App_33__elabAppFn___main___spec__1(x_5);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_System_FilePath_dirName___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_10);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_List_map___main___at___private_Lean_Elab_App_33__elabAppFn___main___spec__1(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_33__elabAppFn___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_7);
x_18 = lean_nat_dec_lt(x_8, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_array_fget(x_7, x_8);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_8, x_21);
lean_dec(x_8);
x_23 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = l___private_Lean_Elab_App_33__elabAppFn___main(x_20, x_2, x_3, x_4, x_5, x_6, x_23, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_8 = x_22;
x_9 = x_25;
x_16 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("placeholders '_' cannot be used where a function is expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicitUniv");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected occurrence of named pattern");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Expr_ctorName___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("arrayRef");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namedPattern");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_System_FilePath_dirName___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dollarProj");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_382; lean_object* x_383; uint8_t x_384; 
lean_inc(x_1);
x_382 = l_Lean_Syntax_getKind(x_1);
x_383 = l_Lean_choiceKind;
x_384 = lean_name_eq(x_382, x_383);
lean_dec(x_382);
if (x_384 == 0)
{
uint8_t x_385; uint8_t x_1183; uint8_t x_1226; lean_object* x_1623; uint8_t x_1624; 
x_1623 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__9;
lean_inc(x_1);
x_1624 = l_Lean_Syntax_isOfKind(x_1, x_1623);
if (x_1624 == 0)
{
uint8_t x_1625; 
x_1625 = 0;
x_1226 = x_1625;
goto block_1622;
}
else
{
lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; uint8_t x_1629; 
x_1626 = l_Lean_Syntax_getArgs(x_1);
x_1627 = lean_array_get_size(x_1626);
lean_dec(x_1626);
x_1628 = lean_unsigned_to_nat(3u);
x_1629 = lean_nat_dec_eq(x_1627, x_1628);
lean_dec(x_1627);
x_1226 = x_1629;
goto block_1622;
}
block_1182:
{
if (x_385 == 0)
{
lean_object* x_386; uint8_t x_387; 
x_386 = l_Lean_identKind___closed__2;
lean_inc(x_1);
x_387 = l_Lean_Syntax_isOfKind(x_1, x_386);
if (x_387 == 0)
{
uint8_t x_388; uint8_t x_418; lean_object* x_805; uint8_t x_806; 
x_805 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__5;
lean_inc(x_1);
x_806 = l_Lean_Syntax_isOfKind(x_1, x_805);
if (x_806 == 0)
{
uint8_t x_807; 
x_807 = 0;
x_418 = x_807;
goto block_804;
}
else
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; uint8_t x_811; 
x_808 = l_Lean_Syntax_getArgs(x_1);
x_809 = lean_array_get_size(x_808);
lean_dec(x_808);
x_810 = lean_unsigned_to_nat(4u);
x_811 = lean_nat_dec_eq(x_809, x_810);
lean_dec(x_809);
x_418 = x_811;
goto block_804;
}
block_417:
{
if (x_388 == 0)
{
lean_object* x_389; uint8_t x_390; 
x_389 = l_Lean_mkHole___closed__2;
lean_inc(x_1);
x_390 = l_Lean_Syntax_isOfKind(x_1, x_389);
if (x_390 == 0)
{
uint8_t x_391; 
x_391 = 0;
x_16 = x_391;
goto block_381;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; 
x_392 = l_Lean_Syntax_getArgs(x_1);
x_393 = lean_array_get_size(x_392);
lean_dec(x_392);
x_394 = lean_unsigned_to_nat(1u);
x_395 = lean_nat_dec_eq(x_393, x_394);
lean_dec(x_393);
x_16 = x_395;
goto block_381;
}
}
else
{
lean_object* x_396; lean_object* x_397; uint8_t x_398; uint8_t x_407; 
x_396 = lean_unsigned_to_nat(1u);
x_397 = l_Lean_Syntax_getArg(x_1, x_396);
lean_dec(x_1);
lean_inc(x_397);
x_407 = l_Lean_Syntax_isOfKind(x_397, x_386);
if (x_407 == 0)
{
lean_object* x_408; uint8_t x_409; 
x_408 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__5;
lean_inc(x_397);
x_409 = l_Lean_Syntax_isOfKind(x_397, x_408);
if (x_409 == 0)
{
uint8_t x_410; 
x_410 = 0;
x_398 = x_410;
goto block_406;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; 
x_411 = l_Lean_Syntax_getArgs(x_397);
x_412 = lean_array_get_size(x_411);
lean_dec(x_411);
x_413 = lean_unsigned_to_nat(4u);
x_414 = lean_nat_dec_eq(x_412, x_413);
lean_dec(x_412);
x_398 = x_414;
goto block_406;
}
}
else
{
uint8_t x_415; 
x_415 = 1;
x_1 = x_397;
x_6 = x_415;
goto _start;
}
block_406:
{
if (x_398 == 0)
{
lean_object* x_399; 
lean_dec(x_397);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_399 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_32__elabAppFnId___spec__1___rarg(x_15);
return x_399;
}
else
{
lean_object* x_400; lean_object* x_401; uint8_t x_402; 
x_400 = lean_unsigned_to_nat(0u);
x_401 = l_Lean_Syntax_getArg(x_397, x_400);
x_402 = l_Lean_Syntax_isOfKind(x_401, x_386);
if (x_402 == 0)
{
lean_object* x_403; 
lean_dec(x_397);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_403 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_32__elabAppFnId___spec__1___rarg(x_15);
return x_403;
}
else
{
uint8_t x_404; 
x_404 = 1;
x_1 = x_397;
x_6 = x_404;
goto _start;
}
}
}
}
}
block_804:
{
if (x_418 == 0)
{
lean_object* x_419; uint8_t x_420; 
x_419 = l___private_Lean_Elab_Term_14__isExplicit___closed__2;
lean_inc(x_1);
x_420 = l_Lean_Syntax_isOfKind(x_1, x_419);
if (x_420 == 0)
{
uint8_t x_421; 
x_421 = 0;
x_388 = x_421;
goto block_417;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; 
x_422 = l_Lean_Syntax_getArgs(x_1);
x_423 = lean_array_get_size(x_422);
lean_dec(x_422);
x_424 = lean_unsigned_to_nat(2u);
x_425 = lean_nat_dec_eq(x_423, x_424);
lean_dec(x_423);
x_388 = x_425;
goto block_417;
}
}
else
{
lean_object* x_426; lean_object* x_427; uint8_t x_428; 
x_426 = lean_unsigned_to_nat(0u);
x_427 = l_Lean_Syntax_getArg(x_1, x_426);
lean_inc(x_427);
x_428 = l_Lean_Syntax_isOfKind(x_427, x_386);
if (x_428 == 0)
{
uint8_t x_429; uint8_t x_430; 
lean_dec(x_427);
x_429 = l_List_isEmpty___rarg(x_2);
if (x_7 == 0)
{
uint8_t x_789; 
x_789 = 1;
x_430 = x_789;
goto block_788;
}
else
{
uint8_t x_790; 
x_790 = 0;
x_430 = x_790;
goto block_788;
}
block_788:
{
if (x_429 == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_468; lean_object* x_469; lean_object* x_491; 
x_431 = lean_box(0);
x_432 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_435 = x_432;
} else {
 lean_dec_ref(x_432);
 x_435 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_491 = l_Lean_Elab_Term_elabTerm(x_1, x_431, x_430, x_9, x_10, x_11, x_12, x_13, x_14, x_434);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_491, 1);
lean_inc(x_493);
lean_dec(x_491);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_494 = l___private_Lean_Elab_App_31__elabAppLVals(x_492, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_493);
if (lean_obj_tag(x_494) == 0)
{
if (x_7 == 0)
{
lean_object* x_495; lean_object* x_496; 
lean_dec(x_435);
lean_dec(x_5);
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
x_468 = x_495;
x_469 = x_496;
goto block_490;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_497 = lean_ctor_get(x_494, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_494, 1);
lean_inc(x_498);
lean_dec(x_494);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_499 = l_Lean_Elab_Term_ensureHasType(x_5, x_497, x_431, x_9, x_10, x_11, x_12, x_13, x_14, x_498);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; 
lean_dec(x_435);
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_499, 1);
lean_inc(x_501);
lean_dec(x_499);
x_468 = x_500;
x_469 = x_501;
goto block_490;
}
else
{
lean_object* x_502; lean_object* x_503; 
x_502 = lean_ctor_get(x_499, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_499, 1);
lean_inc(x_503);
lean_dec(x_499);
x_436 = x_502;
x_437 = x_503;
goto block_467;
}
}
}
else
{
lean_object* x_504; lean_object* x_505; 
lean_dec(x_5);
x_504 = lean_ctor_get(x_494, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_494, 1);
lean_inc(x_505);
lean_dec(x_494);
x_436 = x_504;
x_437 = x_505;
goto block_467;
}
}
else
{
lean_object* x_506; lean_object* x_507; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_506 = lean_ctor_get(x_491, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_491, 1);
lean_inc(x_507);
lean_dec(x_491);
x_436 = x_506;
x_437 = x_507;
goto block_467;
}
block_467:
{
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_438; uint8_t x_439; 
lean_dec(x_435);
x_438 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_437);
x_439 = !lean_is_exclusive(x_438);
if (x_439 == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; 
x_440 = lean_ctor_get(x_438, 0);
x_441 = lean_ctor_get(x_438, 1);
x_442 = l_Lean_Elab_Term_SavedState_restore(x_433, x_9, x_10, x_11, x_12, x_13, x_14, x_441);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_443 = !lean_is_exclusive(x_442);
if (x_443 == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_442, 1);
x_445 = lean_ctor_get(x_442, 0);
lean_dec(x_445);
lean_ctor_set_tag(x_442, 1);
lean_ctor_set(x_442, 1, x_440);
lean_ctor_set(x_442, 0, x_436);
x_446 = lean_array_push(x_8, x_442);
lean_ctor_set(x_438, 1, x_444);
lean_ctor_set(x_438, 0, x_446);
return x_438;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_ctor_get(x_442, 1);
lean_inc(x_447);
lean_dec(x_442);
x_448 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_448, 0, x_436);
lean_ctor_set(x_448, 1, x_440);
x_449 = lean_array_push(x_8, x_448);
lean_ctor_set(x_438, 1, x_447);
lean_ctor_set(x_438, 0, x_449);
return x_438;
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_450 = lean_ctor_get(x_438, 0);
x_451 = lean_ctor_get(x_438, 1);
lean_inc(x_451);
lean_inc(x_450);
lean_dec(x_438);
x_452 = l_Lean_Elab_Term_SavedState_restore(x_433, x_9, x_10, x_11, x_12, x_13, x_14, x_451);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_453 = lean_ctor_get(x_452, 1);
lean_inc(x_453);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_454 = x_452;
} else {
 lean_dec_ref(x_452);
 x_454 = lean_box(0);
}
if (lean_is_scalar(x_454)) {
 x_455 = lean_alloc_ctor(1, 2, 0);
} else {
 x_455 = x_454;
 lean_ctor_set_tag(x_455, 1);
}
lean_ctor_set(x_455, 0, x_436);
lean_ctor_set(x_455, 1, x_450);
x_456 = lean_array_push(x_8, x_455);
x_457 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_457, 0, x_456);
lean_ctor_set(x_457, 1, x_453);
return x_457;
}
}
else
{
lean_object* x_458; lean_object* x_459; uint8_t x_460; 
lean_dec(x_8);
x_458 = lean_ctor_get(x_436, 0);
lean_inc(x_458);
x_459 = l_Lean_Elab_postponeExceptionId;
x_460 = lean_nat_dec_eq(x_458, x_459);
lean_dec(x_458);
if (x_460 == 0)
{
lean_object* x_461; 
lean_dec(x_433);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_435)) {
 x_461 = lean_alloc_ctor(1, 2, 0);
} else {
 x_461 = x_435;
 lean_ctor_set_tag(x_461, 1);
}
lean_ctor_set(x_461, 0, x_436);
lean_ctor_set(x_461, 1, x_437);
return x_461;
}
else
{
lean_object* x_462; uint8_t x_463; 
lean_dec(x_435);
x_462 = l_Lean_Elab_Term_SavedState_restore(x_433, x_9, x_10, x_11, x_12, x_13, x_14, x_437);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_463 = !lean_is_exclusive(x_462);
if (x_463 == 0)
{
lean_object* x_464; 
x_464 = lean_ctor_get(x_462, 0);
lean_dec(x_464);
lean_ctor_set_tag(x_462, 1);
lean_ctor_set(x_462, 0, x_436);
return x_462;
}
else
{
lean_object* x_465; lean_object* x_466; 
x_465 = lean_ctor_get(x_462, 1);
lean_inc(x_465);
lean_dec(x_462);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_436);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
}
}
}
block_490:
{
lean_object* x_470; uint8_t x_471; 
x_470 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_469);
x_471 = !lean_is_exclusive(x_470);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; 
x_472 = lean_ctor_get(x_470, 0);
x_473 = lean_ctor_get(x_470, 1);
x_474 = l_Lean_Elab_Term_SavedState_restore(x_433, x_9, x_10, x_11, x_12, x_13, x_14, x_473);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_475 = !lean_is_exclusive(x_474);
if (x_475 == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_474, 1);
x_477 = lean_ctor_get(x_474, 0);
lean_dec(x_477);
lean_ctor_set(x_474, 1, x_472);
lean_ctor_set(x_474, 0, x_468);
x_478 = lean_array_push(x_8, x_474);
lean_ctor_set(x_470, 1, x_476);
lean_ctor_set(x_470, 0, x_478);
return x_470;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_474, 1);
lean_inc(x_479);
lean_dec(x_474);
x_480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_480, 0, x_468);
lean_ctor_set(x_480, 1, x_472);
x_481 = lean_array_push(x_8, x_480);
lean_ctor_set(x_470, 1, x_479);
lean_ctor_set(x_470, 0, x_481);
return x_470;
}
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_482 = lean_ctor_get(x_470, 0);
x_483 = lean_ctor_get(x_470, 1);
lean_inc(x_483);
lean_inc(x_482);
lean_dec(x_470);
x_484 = l_Lean_Elab_Term_SavedState_restore(x_433, x_9, x_10, x_11, x_12, x_13, x_14, x_483);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_485 = lean_ctor_get(x_484, 1);
lean_inc(x_485);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 x_486 = x_484;
} else {
 lean_dec_ref(x_484);
 x_486 = lean_box(0);
}
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(0, 2, 0);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_468);
lean_ctor_set(x_487, 1, x_482);
x_488 = lean_array_push(x_8, x_487);
x_489 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_485);
return x_489;
}
}
}
else
{
uint8_t x_508; 
x_508 = l_Array_isEmpty___rarg(x_3);
if (x_508 == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_546; lean_object* x_547; lean_object* x_569; 
x_509 = lean_box(0);
x_510 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
if (lean_is_exclusive(x_510)) {
 lean_ctor_release(x_510, 0);
 lean_ctor_release(x_510, 1);
 x_513 = x_510;
} else {
 lean_dec_ref(x_510);
 x_513 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_569 = l_Lean_Elab_Term_elabTerm(x_1, x_509, x_430, x_9, x_10, x_11, x_12, x_13, x_14, x_512);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
lean_dec(x_569);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_572 = l___private_Lean_Elab_App_31__elabAppLVals(x_570, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_571);
if (lean_obj_tag(x_572) == 0)
{
if (x_7 == 0)
{
lean_object* x_573; lean_object* x_574; 
lean_dec(x_513);
lean_dec(x_5);
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
lean_dec(x_572);
x_546 = x_573;
x_547 = x_574;
goto block_568;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_575 = lean_ctor_get(x_572, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_572, 1);
lean_inc(x_576);
lean_dec(x_572);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_577 = l_Lean_Elab_Term_ensureHasType(x_5, x_575, x_509, x_9, x_10, x_11, x_12, x_13, x_14, x_576);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; 
lean_dec(x_513);
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_577, 1);
lean_inc(x_579);
lean_dec(x_577);
x_546 = x_578;
x_547 = x_579;
goto block_568;
}
else
{
lean_object* x_580; lean_object* x_581; 
x_580 = lean_ctor_get(x_577, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_577, 1);
lean_inc(x_581);
lean_dec(x_577);
x_514 = x_580;
x_515 = x_581;
goto block_545;
}
}
}
else
{
lean_object* x_582; lean_object* x_583; 
lean_dec(x_5);
x_582 = lean_ctor_get(x_572, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_572, 1);
lean_inc(x_583);
lean_dec(x_572);
x_514 = x_582;
x_515 = x_583;
goto block_545;
}
}
else
{
lean_object* x_584; lean_object* x_585; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_584 = lean_ctor_get(x_569, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_569, 1);
lean_inc(x_585);
lean_dec(x_569);
x_514 = x_584;
x_515 = x_585;
goto block_545;
}
block_545:
{
if (lean_obj_tag(x_514) == 0)
{
lean_object* x_516; uint8_t x_517; 
lean_dec(x_513);
x_516 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_515);
x_517 = !lean_is_exclusive(x_516);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; uint8_t x_521; 
x_518 = lean_ctor_get(x_516, 0);
x_519 = lean_ctor_get(x_516, 1);
x_520 = l_Lean_Elab_Term_SavedState_restore(x_511, x_9, x_10, x_11, x_12, x_13, x_14, x_519);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_521 = !lean_is_exclusive(x_520);
if (x_521 == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_522 = lean_ctor_get(x_520, 1);
x_523 = lean_ctor_get(x_520, 0);
lean_dec(x_523);
lean_ctor_set_tag(x_520, 1);
lean_ctor_set(x_520, 1, x_518);
lean_ctor_set(x_520, 0, x_514);
x_524 = lean_array_push(x_8, x_520);
lean_ctor_set(x_516, 1, x_522);
lean_ctor_set(x_516, 0, x_524);
return x_516;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_525 = lean_ctor_get(x_520, 1);
lean_inc(x_525);
lean_dec(x_520);
x_526 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_526, 0, x_514);
lean_ctor_set(x_526, 1, x_518);
x_527 = lean_array_push(x_8, x_526);
lean_ctor_set(x_516, 1, x_525);
lean_ctor_set(x_516, 0, x_527);
return x_516;
}
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_528 = lean_ctor_get(x_516, 0);
x_529 = lean_ctor_get(x_516, 1);
lean_inc(x_529);
lean_inc(x_528);
lean_dec(x_516);
x_530 = l_Lean_Elab_Term_SavedState_restore(x_511, x_9, x_10, x_11, x_12, x_13, x_14, x_529);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_531 = lean_ctor_get(x_530, 1);
lean_inc(x_531);
if (lean_is_exclusive(x_530)) {
 lean_ctor_release(x_530, 0);
 lean_ctor_release(x_530, 1);
 x_532 = x_530;
} else {
 lean_dec_ref(x_530);
 x_532 = lean_box(0);
}
if (lean_is_scalar(x_532)) {
 x_533 = lean_alloc_ctor(1, 2, 0);
} else {
 x_533 = x_532;
 lean_ctor_set_tag(x_533, 1);
}
lean_ctor_set(x_533, 0, x_514);
lean_ctor_set(x_533, 1, x_528);
x_534 = lean_array_push(x_8, x_533);
x_535 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_535, 0, x_534);
lean_ctor_set(x_535, 1, x_531);
return x_535;
}
}
else
{
lean_object* x_536; lean_object* x_537; uint8_t x_538; 
lean_dec(x_8);
x_536 = lean_ctor_get(x_514, 0);
lean_inc(x_536);
x_537 = l_Lean_Elab_postponeExceptionId;
x_538 = lean_nat_dec_eq(x_536, x_537);
lean_dec(x_536);
if (x_538 == 0)
{
lean_object* x_539; 
lean_dec(x_511);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_513)) {
 x_539 = lean_alloc_ctor(1, 2, 0);
} else {
 x_539 = x_513;
 lean_ctor_set_tag(x_539, 1);
}
lean_ctor_set(x_539, 0, x_514);
lean_ctor_set(x_539, 1, x_515);
return x_539;
}
else
{
lean_object* x_540; uint8_t x_541; 
lean_dec(x_513);
x_540 = l_Lean_Elab_Term_SavedState_restore(x_511, x_9, x_10, x_11, x_12, x_13, x_14, x_515);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_541 = !lean_is_exclusive(x_540);
if (x_541 == 0)
{
lean_object* x_542; 
x_542 = lean_ctor_get(x_540, 0);
lean_dec(x_542);
lean_ctor_set_tag(x_540, 1);
lean_ctor_set(x_540, 0, x_514);
return x_540;
}
else
{
lean_object* x_543; lean_object* x_544; 
x_543 = lean_ctor_get(x_540, 1);
lean_inc(x_543);
lean_dec(x_540);
x_544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_544, 0, x_514);
lean_ctor_set(x_544, 1, x_543);
return x_544;
}
}
}
}
block_568:
{
lean_object* x_548; uint8_t x_549; 
x_548 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_547);
x_549 = !lean_is_exclusive(x_548);
if (x_549 == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; uint8_t x_553; 
x_550 = lean_ctor_get(x_548, 0);
x_551 = lean_ctor_get(x_548, 1);
x_552 = l_Lean_Elab_Term_SavedState_restore(x_511, x_9, x_10, x_11, x_12, x_13, x_14, x_551);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_553 = !lean_is_exclusive(x_552);
if (x_553 == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_554 = lean_ctor_get(x_552, 1);
x_555 = lean_ctor_get(x_552, 0);
lean_dec(x_555);
lean_ctor_set(x_552, 1, x_550);
lean_ctor_set(x_552, 0, x_546);
x_556 = lean_array_push(x_8, x_552);
lean_ctor_set(x_548, 1, x_554);
lean_ctor_set(x_548, 0, x_556);
return x_548;
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_557 = lean_ctor_get(x_552, 1);
lean_inc(x_557);
lean_dec(x_552);
x_558 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_558, 0, x_546);
lean_ctor_set(x_558, 1, x_550);
x_559 = lean_array_push(x_8, x_558);
lean_ctor_set(x_548, 1, x_557);
lean_ctor_set(x_548, 0, x_559);
return x_548;
}
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_560 = lean_ctor_get(x_548, 0);
x_561 = lean_ctor_get(x_548, 1);
lean_inc(x_561);
lean_inc(x_560);
lean_dec(x_548);
x_562 = l_Lean_Elab_Term_SavedState_restore(x_511, x_9, x_10, x_11, x_12, x_13, x_14, x_561);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_563 = lean_ctor_get(x_562, 1);
lean_inc(x_563);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_564 = x_562;
} else {
 lean_dec_ref(x_562);
 x_564 = lean_box(0);
}
if (lean_is_scalar(x_564)) {
 x_565 = lean_alloc_ctor(0, 2, 0);
} else {
 x_565 = x_564;
}
lean_ctor_set(x_565, 0, x_546);
lean_ctor_set(x_565, 1, x_560);
x_566 = lean_array_push(x_8, x_565);
x_567 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_563);
return x_567;
}
}
}
else
{
uint8_t x_586; 
x_586 = l_Array_isEmpty___rarg(x_4);
if (x_586 == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_624; lean_object* x_625; lean_object* x_647; 
x_587 = lean_box(0);
x_588 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_588, 1);
lean_inc(x_590);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 lean_ctor_release(x_588, 1);
 x_591 = x_588;
} else {
 lean_dec_ref(x_588);
 x_591 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_647 = l_Lean_Elab_Term_elabTerm(x_1, x_587, x_430, x_9, x_10, x_11, x_12, x_13, x_14, x_590);
if (lean_obj_tag(x_647) == 0)
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_648 = lean_ctor_get(x_647, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_647, 1);
lean_inc(x_649);
lean_dec(x_647);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_650 = l___private_Lean_Elab_App_31__elabAppLVals(x_648, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_649);
if (lean_obj_tag(x_650) == 0)
{
if (x_7 == 0)
{
lean_object* x_651; lean_object* x_652; 
lean_dec(x_591);
lean_dec(x_5);
x_651 = lean_ctor_get(x_650, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_650, 1);
lean_inc(x_652);
lean_dec(x_650);
x_624 = x_651;
x_625 = x_652;
goto block_646;
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_653 = lean_ctor_get(x_650, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_650, 1);
lean_inc(x_654);
lean_dec(x_650);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_655 = l_Lean_Elab_Term_ensureHasType(x_5, x_653, x_587, x_9, x_10, x_11, x_12, x_13, x_14, x_654);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; 
lean_dec(x_591);
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
lean_dec(x_655);
x_624 = x_656;
x_625 = x_657;
goto block_646;
}
else
{
lean_object* x_658; lean_object* x_659; 
x_658 = lean_ctor_get(x_655, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_655, 1);
lean_inc(x_659);
lean_dec(x_655);
x_592 = x_658;
x_593 = x_659;
goto block_623;
}
}
}
else
{
lean_object* x_660; lean_object* x_661; 
lean_dec(x_5);
x_660 = lean_ctor_get(x_650, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_650, 1);
lean_inc(x_661);
lean_dec(x_650);
x_592 = x_660;
x_593 = x_661;
goto block_623;
}
}
else
{
lean_object* x_662; lean_object* x_663; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_662 = lean_ctor_get(x_647, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_647, 1);
lean_inc(x_663);
lean_dec(x_647);
x_592 = x_662;
x_593 = x_663;
goto block_623;
}
block_623:
{
if (lean_obj_tag(x_592) == 0)
{
lean_object* x_594; uint8_t x_595; 
lean_dec(x_591);
x_594 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_593);
x_595 = !lean_is_exclusive(x_594);
if (x_595 == 0)
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; uint8_t x_599; 
x_596 = lean_ctor_get(x_594, 0);
x_597 = lean_ctor_get(x_594, 1);
x_598 = l_Lean_Elab_Term_SavedState_restore(x_589, x_9, x_10, x_11, x_12, x_13, x_14, x_597);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_599 = !lean_is_exclusive(x_598);
if (x_599 == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_600 = lean_ctor_get(x_598, 1);
x_601 = lean_ctor_get(x_598, 0);
lean_dec(x_601);
lean_ctor_set_tag(x_598, 1);
lean_ctor_set(x_598, 1, x_596);
lean_ctor_set(x_598, 0, x_592);
x_602 = lean_array_push(x_8, x_598);
lean_ctor_set(x_594, 1, x_600);
lean_ctor_set(x_594, 0, x_602);
return x_594;
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_603 = lean_ctor_get(x_598, 1);
lean_inc(x_603);
lean_dec(x_598);
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_592);
lean_ctor_set(x_604, 1, x_596);
x_605 = lean_array_push(x_8, x_604);
lean_ctor_set(x_594, 1, x_603);
lean_ctor_set(x_594, 0, x_605);
return x_594;
}
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_606 = lean_ctor_get(x_594, 0);
x_607 = lean_ctor_get(x_594, 1);
lean_inc(x_607);
lean_inc(x_606);
lean_dec(x_594);
x_608 = l_Lean_Elab_Term_SavedState_restore(x_589, x_9, x_10, x_11, x_12, x_13, x_14, x_607);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_609 = lean_ctor_get(x_608, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_608)) {
 lean_ctor_release(x_608, 0);
 lean_ctor_release(x_608, 1);
 x_610 = x_608;
} else {
 lean_dec_ref(x_608);
 x_610 = lean_box(0);
}
if (lean_is_scalar(x_610)) {
 x_611 = lean_alloc_ctor(1, 2, 0);
} else {
 x_611 = x_610;
 lean_ctor_set_tag(x_611, 1);
}
lean_ctor_set(x_611, 0, x_592);
lean_ctor_set(x_611, 1, x_606);
x_612 = lean_array_push(x_8, x_611);
x_613 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_609);
return x_613;
}
}
else
{
lean_object* x_614; lean_object* x_615; uint8_t x_616; 
lean_dec(x_8);
x_614 = lean_ctor_get(x_592, 0);
lean_inc(x_614);
x_615 = l_Lean_Elab_postponeExceptionId;
x_616 = lean_nat_dec_eq(x_614, x_615);
lean_dec(x_614);
if (x_616 == 0)
{
lean_object* x_617; 
lean_dec(x_589);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_591)) {
 x_617 = lean_alloc_ctor(1, 2, 0);
} else {
 x_617 = x_591;
 lean_ctor_set_tag(x_617, 1);
}
lean_ctor_set(x_617, 0, x_592);
lean_ctor_set(x_617, 1, x_593);
return x_617;
}
else
{
lean_object* x_618; uint8_t x_619; 
lean_dec(x_591);
x_618 = l_Lean_Elab_Term_SavedState_restore(x_589, x_9, x_10, x_11, x_12, x_13, x_14, x_593);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_619 = !lean_is_exclusive(x_618);
if (x_619 == 0)
{
lean_object* x_620; 
x_620 = lean_ctor_get(x_618, 0);
lean_dec(x_620);
lean_ctor_set_tag(x_618, 1);
lean_ctor_set(x_618, 0, x_592);
return x_618;
}
else
{
lean_object* x_621; lean_object* x_622; 
x_621 = lean_ctor_get(x_618, 1);
lean_inc(x_621);
lean_dec(x_618);
x_622 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_622, 0, x_592);
lean_ctor_set(x_622, 1, x_621);
return x_622;
}
}
}
}
block_646:
{
lean_object* x_626; uint8_t x_627; 
x_626 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_625);
x_627 = !lean_is_exclusive(x_626);
if (x_627 == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; 
x_628 = lean_ctor_get(x_626, 0);
x_629 = lean_ctor_get(x_626, 1);
x_630 = l_Lean_Elab_Term_SavedState_restore(x_589, x_9, x_10, x_11, x_12, x_13, x_14, x_629);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_631 = !lean_is_exclusive(x_630);
if (x_631 == 0)
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_632 = lean_ctor_get(x_630, 1);
x_633 = lean_ctor_get(x_630, 0);
lean_dec(x_633);
lean_ctor_set(x_630, 1, x_628);
lean_ctor_set(x_630, 0, x_624);
x_634 = lean_array_push(x_8, x_630);
lean_ctor_set(x_626, 1, x_632);
lean_ctor_set(x_626, 0, x_634);
return x_626;
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_635 = lean_ctor_get(x_630, 1);
lean_inc(x_635);
lean_dec(x_630);
x_636 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_636, 0, x_624);
lean_ctor_set(x_636, 1, x_628);
x_637 = lean_array_push(x_8, x_636);
lean_ctor_set(x_626, 1, x_635);
lean_ctor_set(x_626, 0, x_637);
return x_626;
}
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_638 = lean_ctor_get(x_626, 0);
x_639 = lean_ctor_get(x_626, 1);
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_626);
x_640 = l_Lean_Elab_Term_SavedState_restore(x_589, x_9, x_10, x_11, x_12, x_13, x_14, x_639);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_641 = lean_ctor_get(x_640, 1);
lean_inc(x_641);
if (lean_is_exclusive(x_640)) {
 lean_ctor_release(x_640, 0);
 lean_ctor_release(x_640, 1);
 x_642 = x_640;
} else {
 lean_dec_ref(x_640);
 x_642 = lean_box(0);
}
if (lean_is_scalar(x_642)) {
 x_643 = lean_alloc_ctor(0, 2, 0);
} else {
 x_643 = x_642;
}
lean_ctor_set(x_643, 0, x_624);
lean_ctor_set(x_643, 1, x_638);
x_644 = lean_array_push(x_8, x_643);
x_645 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_641);
return x_645;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_7 == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; uint8_t x_700; lean_object* x_701; 
x_664 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_664, 1);
lean_inc(x_666);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 lean_ctor_release(x_664, 1);
 x_667 = x_664;
} else {
 lean_dec_ref(x_664);
 x_667 = lean_box(0);
}
x_700 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_701 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_700, x_9, x_10, x_11, x_12, x_13, x_14, x_666);
if (lean_obj_tag(x_701) == 0)
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; uint8_t x_705; 
lean_dec(x_667);
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_701, 1);
lean_inc(x_703);
lean_dec(x_701);
x_704 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_703);
x_705 = !lean_is_exclusive(x_704);
if (x_705 == 0)
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; uint8_t x_709; 
x_706 = lean_ctor_get(x_704, 0);
x_707 = lean_ctor_get(x_704, 1);
x_708 = l_Lean_Elab_Term_SavedState_restore(x_665, x_9, x_10, x_11, x_12, x_13, x_14, x_707);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_709 = !lean_is_exclusive(x_708);
if (x_709 == 0)
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; 
x_710 = lean_ctor_get(x_708, 1);
x_711 = lean_ctor_get(x_708, 0);
lean_dec(x_711);
lean_ctor_set(x_708, 1, x_706);
lean_ctor_set(x_708, 0, x_702);
x_712 = lean_array_push(x_8, x_708);
lean_ctor_set(x_704, 1, x_710);
lean_ctor_set(x_704, 0, x_712);
return x_704;
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_713 = lean_ctor_get(x_708, 1);
lean_inc(x_713);
lean_dec(x_708);
x_714 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_714, 0, x_702);
lean_ctor_set(x_714, 1, x_706);
x_715 = lean_array_push(x_8, x_714);
lean_ctor_set(x_704, 1, x_713);
lean_ctor_set(x_704, 0, x_715);
return x_704;
}
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_716 = lean_ctor_get(x_704, 0);
x_717 = lean_ctor_get(x_704, 1);
lean_inc(x_717);
lean_inc(x_716);
lean_dec(x_704);
x_718 = l_Lean_Elab_Term_SavedState_restore(x_665, x_9, x_10, x_11, x_12, x_13, x_14, x_717);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_719 = lean_ctor_get(x_718, 1);
lean_inc(x_719);
if (lean_is_exclusive(x_718)) {
 lean_ctor_release(x_718, 0);
 lean_ctor_release(x_718, 1);
 x_720 = x_718;
} else {
 lean_dec_ref(x_718);
 x_720 = lean_box(0);
}
if (lean_is_scalar(x_720)) {
 x_721 = lean_alloc_ctor(0, 2, 0);
} else {
 x_721 = x_720;
}
lean_ctor_set(x_721, 0, x_702);
lean_ctor_set(x_721, 1, x_716);
x_722 = lean_array_push(x_8, x_721);
x_723 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set(x_723, 1, x_719);
return x_723;
}
}
else
{
lean_object* x_724; lean_object* x_725; 
x_724 = lean_ctor_get(x_701, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_701, 1);
lean_inc(x_725);
lean_dec(x_701);
x_668 = x_724;
x_669 = x_725;
goto block_699;
}
block_699:
{
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_670; uint8_t x_671; 
lean_dec(x_667);
x_670 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_669);
x_671 = !lean_is_exclusive(x_670);
if (x_671 == 0)
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; uint8_t x_675; 
x_672 = lean_ctor_get(x_670, 0);
x_673 = lean_ctor_get(x_670, 1);
x_674 = l_Lean_Elab_Term_SavedState_restore(x_665, x_9, x_10, x_11, x_12, x_13, x_14, x_673);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_675 = !lean_is_exclusive(x_674);
if (x_675 == 0)
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_676 = lean_ctor_get(x_674, 1);
x_677 = lean_ctor_get(x_674, 0);
lean_dec(x_677);
lean_ctor_set_tag(x_674, 1);
lean_ctor_set(x_674, 1, x_672);
lean_ctor_set(x_674, 0, x_668);
x_678 = lean_array_push(x_8, x_674);
lean_ctor_set(x_670, 1, x_676);
lean_ctor_set(x_670, 0, x_678);
return x_670;
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_679 = lean_ctor_get(x_674, 1);
lean_inc(x_679);
lean_dec(x_674);
x_680 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_680, 0, x_668);
lean_ctor_set(x_680, 1, x_672);
x_681 = lean_array_push(x_8, x_680);
lean_ctor_set(x_670, 1, x_679);
lean_ctor_set(x_670, 0, x_681);
return x_670;
}
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_682 = lean_ctor_get(x_670, 0);
x_683 = lean_ctor_get(x_670, 1);
lean_inc(x_683);
lean_inc(x_682);
lean_dec(x_670);
x_684 = l_Lean_Elab_Term_SavedState_restore(x_665, x_9, x_10, x_11, x_12, x_13, x_14, x_683);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_685 = lean_ctor_get(x_684, 1);
lean_inc(x_685);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 x_686 = x_684;
} else {
 lean_dec_ref(x_684);
 x_686 = lean_box(0);
}
if (lean_is_scalar(x_686)) {
 x_687 = lean_alloc_ctor(1, 2, 0);
} else {
 x_687 = x_686;
 lean_ctor_set_tag(x_687, 1);
}
lean_ctor_set(x_687, 0, x_668);
lean_ctor_set(x_687, 1, x_682);
x_688 = lean_array_push(x_8, x_687);
x_689 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_689, 0, x_688);
lean_ctor_set(x_689, 1, x_685);
return x_689;
}
}
else
{
lean_object* x_690; lean_object* x_691; uint8_t x_692; 
lean_dec(x_8);
x_690 = lean_ctor_get(x_668, 0);
lean_inc(x_690);
x_691 = l_Lean_Elab_postponeExceptionId;
x_692 = lean_nat_dec_eq(x_690, x_691);
lean_dec(x_690);
if (x_692 == 0)
{
lean_object* x_693; 
lean_dec(x_665);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_667)) {
 x_693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_693 = x_667;
 lean_ctor_set_tag(x_693, 1);
}
lean_ctor_set(x_693, 0, x_668);
lean_ctor_set(x_693, 1, x_669);
return x_693;
}
else
{
lean_object* x_694; uint8_t x_695; 
lean_dec(x_667);
x_694 = l_Lean_Elab_Term_SavedState_restore(x_665, x_9, x_10, x_11, x_12, x_13, x_14, x_669);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_695 = !lean_is_exclusive(x_694);
if (x_695 == 0)
{
lean_object* x_696; 
x_696 = lean_ctor_get(x_694, 0);
lean_dec(x_696);
lean_ctor_set_tag(x_694, 1);
lean_ctor_set(x_694, 0, x_668);
return x_694;
}
else
{
lean_object* x_697; lean_object* x_698; 
x_697 = lean_ctor_get(x_694, 1);
lean_inc(x_697);
lean_dec(x_694);
x_698 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_698, 0, x_668);
lean_ctor_set(x_698, 1, x_697);
return x_698;
}
}
}
}
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_763; 
x_726 = lean_box(0);
x_727 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_727, 1);
lean_inc(x_729);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 lean_ctor_release(x_727, 1);
 x_730 = x_727;
} else {
 lean_dec_ref(x_727);
 x_730 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_763 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_430, x_726, x_9, x_10, x_11, x_12, x_13, x_14, x_729);
if (lean_obj_tag(x_763) == 0)
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; uint8_t x_767; 
lean_dec(x_730);
x_764 = lean_ctor_get(x_763, 0);
lean_inc(x_764);
x_765 = lean_ctor_get(x_763, 1);
lean_inc(x_765);
lean_dec(x_763);
x_766 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_765);
x_767 = !lean_is_exclusive(x_766);
if (x_767 == 0)
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; uint8_t x_771; 
x_768 = lean_ctor_get(x_766, 0);
x_769 = lean_ctor_get(x_766, 1);
x_770 = l_Lean_Elab_Term_SavedState_restore(x_728, x_9, x_10, x_11, x_12, x_13, x_14, x_769);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_771 = !lean_is_exclusive(x_770);
if (x_771 == 0)
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_772 = lean_ctor_get(x_770, 1);
x_773 = lean_ctor_get(x_770, 0);
lean_dec(x_773);
lean_ctor_set(x_770, 1, x_768);
lean_ctor_set(x_770, 0, x_764);
x_774 = lean_array_push(x_8, x_770);
lean_ctor_set(x_766, 1, x_772);
lean_ctor_set(x_766, 0, x_774);
return x_766;
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; 
x_775 = lean_ctor_get(x_770, 1);
lean_inc(x_775);
lean_dec(x_770);
x_776 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_776, 0, x_764);
lean_ctor_set(x_776, 1, x_768);
x_777 = lean_array_push(x_8, x_776);
lean_ctor_set(x_766, 1, x_775);
lean_ctor_set(x_766, 0, x_777);
return x_766;
}
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_778 = lean_ctor_get(x_766, 0);
x_779 = lean_ctor_get(x_766, 1);
lean_inc(x_779);
lean_inc(x_778);
lean_dec(x_766);
x_780 = l_Lean_Elab_Term_SavedState_restore(x_728, x_9, x_10, x_11, x_12, x_13, x_14, x_779);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_781 = lean_ctor_get(x_780, 1);
lean_inc(x_781);
if (lean_is_exclusive(x_780)) {
 lean_ctor_release(x_780, 0);
 lean_ctor_release(x_780, 1);
 x_782 = x_780;
} else {
 lean_dec_ref(x_780);
 x_782 = lean_box(0);
}
if (lean_is_scalar(x_782)) {
 x_783 = lean_alloc_ctor(0, 2, 0);
} else {
 x_783 = x_782;
}
lean_ctor_set(x_783, 0, x_764);
lean_ctor_set(x_783, 1, x_778);
x_784 = lean_array_push(x_8, x_783);
x_785 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_785, 0, x_784);
lean_ctor_set(x_785, 1, x_781);
return x_785;
}
}
else
{
lean_object* x_786; lean_object* x_787; 
x_786 = lean_ctor_get(x_763, 0);
lean_inc(x_786);
x_787 = lean_ctor_get(x_763, 1);
lean_inc(x_787);
lean_dec(x_763);
x_731 = x_786;
x_732 = x_787;
goto block_762;
}
block_762:
{
if (lean_obj_tag(x_731) == 0)
{
lean_object* x_733; uint8_t x_734; 
lean_dec(x_730);
x_733 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_732);
x_734 = !lean_is_exclusive(x_733);
if (x_734 == 0)
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; uint8_t x_738; 
x_735 = lean_ctor_get(x_733, 0);
x_736 = lean_ctor_get(x_733, 1);
x_737 = l_Lean_Elab_Term_SavedState_restore(x_728, x_9, x_10, x_11, x_12, x_13, x_14, x_736);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_738 = !lean_is_exclusive(x_737);
if (x_738 == 0)
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; 
x_739 = lean_ctor_get(x_737, 1);
x_740 = lean_ctor_get(x_737, 0);
lean_dec(x_740);
lean_ctor_set_tag(x_737, 1);
lean_ctor_set(x_737, 1, x_735);
lean_ctor_set(x_737, 0, x_731);
x_741 = lean_array_push(x_8, x_737);
lean_ctor_set(x_733, 1, x_739);
lean_ctor_set(x_733, 0, x_741);
return x_733;
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_742 = lean_ctor_get(x_737, 1);
lean_inc(x_742);
lean_dec(x_737);
x_743 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_743, 0, x_731);
lean_ctor_set(x_743, 1, x_735);
x_744 = lean_array_push(x_8, x_743);
lean_ctor_set(x_733, 1, x_742);
lean_ctor_set(x_733, 0, x_744);
return x_733;
}
}
else
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_745 = lean_ctor_get(x_733, 0);
x_746 = lean_ctor_get(x_733, 1);
lean_inc(x_746);
lean_inc(x_745);
lean_dec(x_733);
x_747 = l_Lean_Elab_Term_SavedState_restore(x_728, x_9, x_10, x_11, x_12, x_13, x_14, x_746);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_748 = lean_ctor_get(x_747, 1);
lean_inc(x_748);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 lean_ctor_release(x_747, 1);
 x_749 = x_747;
} else {
 lean_dec_ref(x_747);
 x_749 = lean_box(0);
}
if (lean_is_scalar(x_749)) {
 x_750 = lean_alloc_ctor(1, 2, 0);
} else {
 x_750 = x_749;
 lean_ctor_set_tag(x_750, 1);
}
lean_ctor_set(x_750, 0, x_731);
lean_ctor_set(x_750, 1, x_745);
x_751 = lean_array_push(x_8, x_750);
x_752 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_752, 0, x_751);
lean_ctor_set(x_752, 1, x_748);
return x_752;
}
}
else
{
lean_object* x_753; lean_object* x_754; uint8_t x_755; 
lean_dec(x_8);
x_753 = lean_ctor_get(x_731, 0);
lean_inc(x_753);
x_754 = l_Lean_Elab_postponeExceptionId;
x_755 = lean_nat_dec_eq(x_753, x_754);
lean_dec(x_753);
if (x_755 == 0)
{
lean_object* x_756; 
lean_dec(x_728);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_730)) {
 x_756 = lean_alloc_ctor(1, 2, 0);
} else {
 x_756 = x_730;
 lean_ctor_set_tag(x_756, 1);
}
lean_ctor_set(x_756, 0, x_731);
lean_ctor_set(x_756, 1, x_732);
return x_756;
}
else
{
lean_object* x_757; uint8_t x_758; 
lean_dec(x_730);
x_757 = l_Lean_Elab_Term_SavedState_restore(x_728, x_9, x_10, x_11, x_12, x_13, x_14, x_732);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_758 = !lean_is_exclusive(x_757);
if (x_758 == 0)
{
lean_object* x_759; 
x_759 = lean_ctor_get(x_757, 0);
lean_dec(x_759);
lean_ctor_set_tag(x_757, 1);
lean_ctor_set(x_757, 0, x_731);
return x_757;
}
else
{
lean_object* x_760; lean_object* x_761; 
x_760 = lean_ctor_get(x_757, 1);
lean_inc(x_760);
lean_dec(x_757);
x_761 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_761, 0, x_731);
lean_ctor_set(x_761, 1, x_760);
return x_761;
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
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; 
x_791 = lean_unsigned_to_nat(2u);
x_792 = l_Lean_Syntax_getArg(x_1, x_791);
lean_dec(x_1);
x_793 = l_Lean_Syntax_getArgs(x_792);
lean_dec(x_792);
x_794 = l_Array_empty___closed__1;
x_795 = l_Array_foldlStepMAux___main___at_Lean_Syntax_getSepArgs___spec__1(x_791, x_793, x_426, x_794);
lean_dec(x_793);
x_796 = l_Lean_Elab_Term_elabExplicitUnivs(x_795, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_795);
if (lean_obj_tag(x_796) == 0)
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; 
x_797 = lean_ctor_get(x_796, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_796, 1);
lean_inc(x_798);
lean_dec(x_796);
x_799 = l___private_Lean_Elab_App_32__elabAppFnId(x_427, x_797, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_798);
return x_799;
}
else
{
uint8_t x_800; 
lean_dec(x_427);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_800 = !lean_is_exclusive(x_796);
if (x_800 == 0)
{
return x_796;
}
else
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; 
x_801 = lean_ctor_get(x_796, 0);
x_802 = lean_ctor_get(x_796, 1);
lean_inc(x_802);
lean_inc(x_801);
lean_dec(x_796);
x_803 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_803, 0, x_801);
lean_ctor_set(x_803, 1, x_802);
return x_803;
}
}
}
}
}
}
else
{
lean_object* x_812; lean_object* x_813; 
x_812 = lean_box(0);
x_813 = l___private_Lean_Elab_App_32__elabAppFnId(x_1, x_812, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_813;
}
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; uint8_t x_817; 
x_814 = lean_unsigned_to_nat(0u);
x_815 = l_Lean_Syntax_getArg(x_1, x_814);
x_816 = l_Lean_identKind___closed__2;
x_817 = l_Lean_Syntax_isOfKind(x_815, x_816);
if (x_817 == 0)
{
uint8_t x_818; uint8_t x_819; 
x_818 = l_List_isEmpty___rarg(x_2);
if (x_7 == 0)
{
uint8_t x_1178; 
x_1178 = 1;
x_819 = x_1178;
goto block_1177;
}
else
{
uint8_t x_1179; 
x_1179 = 0;
x_819 = x_1179;
goto block_1177;
}
block_1177:
{
if (x_818 == 0)
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_857; lean_object* x_858; lean_object* x_880; 
x_820 = lean_box(0);
x_821 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_822 = lean_ctor_get(x_821, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_821, 1);
lean_inc(x_823);
if (lean_is_exclusive(x_821)) {
 lean_ctor_release(x_821, 0);
 lean_ctor_release(x_821, 1);
 x_824 = x_821;
} else {
 lean_dec_ref(x_821);
 x_824 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_880 = l_Lean_Elab_Term_elabTerm(x_1, x_820, x_819, x_9, x_10, x_11, x_12, x_13, x_14, x_823);
if (lean_obj_tag(x_880) == 0)
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_881 = lean_ctor_get(x_880, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_880, 1);
lean_inc(x_882);
lean_dec(x_880);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_883 = l___private_Lean_Elab_App_31__elabAppLVals(x_881, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_882);
if (lean_obj_tag(x_883) == 0)
{
if (x_7 == 0)
{
lean_object* x_884; lean_object* x_885; 
lean_dec(x_824);
lean_dec(x_5);
x_884 = lean_ctor_get(x_883, 0);
lean_inc(x_884);
x_885 = lean_ctor_get(x_883, 1);
lean_inc(x_885);
lean_dec(x_883);
x_857 = x_884;
x_858 = x_885;
goto block_879;
}
else
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; 
x_886 = lean_ctor_get(x_883, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_883, 1);
lean_inc(x_887);
lean_dec(x_883);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_888 = l_Lean_Elab_Term_ensureHasType(x_5, x_886, x_820, x_9, x_10, x_11, x_12, x_13, x_14, x_887);
if (lean_obj_tag(x_888) == 0)
{
lean_object* x_889; lean_object* x_890; 
lean_dec(x_824);
x_889 = lean_ctor_get(x_888, 0);
lean_inc(x_889);
x_890 = lean_ctor_get(x_888, 1);
lean_inc(x_890);
lean_dec(x_888);
x_857 = x_889;
x_858 = x_890;
goto block_879;
}
else
{
lean_object* x_891; lean_object* x_892; 
x_891 = lean_ctor_get(x_888, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_888, 1);
lean_inc(x_892);
lean_dec(x_888);
x_825 = x_891;
x_826 = x_892;
goto block_856;
}
}
}
else
{
lean_object* x_893; lean_object* x_894; 
lean_dec(x_5);
x_893 = lean_ctor_get(x_883, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_883, 1);
lean_inc(x_894);
lean_dec(x_883);
x_825 = x_893;
x_826 = x_894;
goto block_856;
}
}
else
{
lean_object* x_895; lean_object* x_896; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_895 = lean_ctor_get(x_880, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_880, 1);
lean_inc(x_896);
lean_dec(x_880);
x_825 = x_895;
x_826 = x_896;
goto block_856;
}
block_856:
{
if (lean_obj_tag(x_825) == 0)
{
lean_object* x_827; uint8_t x_828; 
lean_dec(x_824);
x_827 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_826);
x_828 = !lean_is_exclusive(x_827);
if (x_828 == 0)
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; uint8_t x_832; 
x_829 = lean_ctor_get(x_827, 0);
x_830 = lean_ctor_get(x_827, 1);
x_831 = l_Lean_Elab_Term_SavedState_restore(x_822, x_9, x_10, x_11, x_12, x_13, x_14, x_830);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_832 = !lean_is_exclusive(x_831);
if (x_832 == 0)
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; 
x_833 = lean_ctor_get(x_831, 1);
x_834 = lean_ctor_get(x_831, 0);
lean_dec(x_834);
lean_ctor_set_tag(x_831, 1);
lean_ctor_set(x_831, 1, x_829);
lean_ctor_set(x_831, 0, x_825);
x_835 = lean_array_push(x_8, x_831);
lean_ctor_set(x_827, 1, x_833);
lean_ctor_set(x_827, 0, x_835);
return x_827;
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; 
x_836 = lean_ctor_get(x_831, 1);
lean_inc(x_836);
lean_dec(x_831);
x_837 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_837, 0, x_825);
lean_ctor_set(x_837, 1, x_829);
x_838 = lean_array_push(x_8, x_837);
lean_ctor_set(x_827, 1, x_836);
lean_ctor_set(x_827, 0, x_838);
return x_827;
}
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; 
x_839 = lean_ctor_get(x_827, 0);
x_840 = lean_ctor_get(x_827, 1);
lean_inc(x_840);
lean_inc(x_839);
lean_dec(x_827);
x_841 = l_Lean_Elab_Term_SavedState_restore(x_822, x_9, x_10, x_11, x_12, x_13, x_14, x_840);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_842 = lean_ctor_get(x_841, 1);
lean_inc(x_842);
if (lean_is_exclusive(x_841)) {
 lean_ctor_release(x_841, 0);
 lean_ctor_release(x_841, 1);
 x_843 = x_841;
} else {
 lean_dec_ref(x_841);
 x_843 = lean_box(0);
}
if (lean_is_scalar(x_843)) {
 x_844 = lean_alloc_ctor(1, 2, 0);
} else {
 x_844 = x_843;
 lean_ctor_set_tag(x_844, 1);
}
lean_ctor_set(x_844, 0, x_825);
lean_ctor_set(x_844, 1, x_839);
x_845 = lean_array_push(x_8, x_844);
x_846 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_846, 0, x_845);
lean_ctor_set(x_846, 1, x_842);
return x_846;
}
}
else
{
lean_object* x_847; lean_object* x_848; uint8_t x_849; 
lean_dec(x_8);
x_847 = lean_ctor_get(x_825, 0);
lean_inc(x_847);
x_848 = l_Lean_Elab_postponeExceptionId;
x_849 = lean_nat_dec_eq(x_847, x_848);
lean_dec(x_847);
if (x_849 == 0)
{
lean_object* x_850; 
lean_dec(x_822);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_824)) {
 x_850 = lean_alloc_ctor(1, 2, 0);
} else {
 x_850 = x_824;
 lean_ctor_set_tag(x_850, 1);
}
lean_ctor_set(x_850, 0, x_825);
lean_ctor_set(x_850, 1, x_826);
return x_850;
}
else
{
lean_object* x_851; uint8_t x_852; 
lean_dec(x_824);
x_851 = l_Lean_Elab_Term_SavedState_restore(x_822, x_9, x_10, x_11, x_12, x_13, x_14, x_826);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_852 = !lean_is_exclusive(x_851);
if (x_852 == 0)
{
lean_object* x_853; 
x_853 = lean_ctor_get(x_851, 0);
lean_dec(x_853);
lean_ctor_set_tag(x_851, 1);
lean_ctor_set(x_851, 0, x_825);
return x_851;
}
else
{
lean_object* x_854; lean_object* x_855; 
x_854 = lean_ctor_get(x_851, 1);
lean_inc(x_854);
lean_dec(x_851);
x_855 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_855, 0, x_825);
lean_ctor_set(x_855, 1, x_854);
return x_855;
}
}
}
}
block_879:
{
lean_object* x_859; uint8_t x_860; 
x_859 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_858);
x_860 = !lean_is_exclusive(x_859);
if (x_860 == 0)
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; uint8_t x_864; 
x_861 = lean_ctor_get(x_859, 0);
x_862 = lean_ctor_get(x_859, 1);
x_863 = l_Lean_Elab_Term_SavedState_restore(x_822, x_9, x_10, x_11, x_12, x_13, x_14, x_862);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_864 = !lean_is_exclusive(x_863);
if (x_864 == 0)
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; 
x_865 = lean_ctor_get(x_863, 1);
x_866 = lean_ctor_get(x_863, 0);
lean_dec(x_866);
lean_ctor_set(x_863, 1, x_861);
lean_ctor_set(x_863, 0, x_857);
x_867 = lean_array_push(x_8, x_863);
lean_ctor_set(x_859, 1, x_865);
lean_ctor_set(x_859, 0, x_867);
return x_859;
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_868 = lean_ctor_get(x_863, 1);
lean_inc(x_868);
lean_dec(x_863);
x_869 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_869, 0, x_857);
lean_ctor_set(x_869, 1, x_861);
x_870 = lean_array_push(x_8, x_869);
lean_ctor_set(x_859, 1, x_868);
lean_ctor_set(x_859, 0, x_870);
return x_859;
}
}
else
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; 
x_871 = lean_ctor_get(x_859, 0);
x_872 = lean_ctor_get(x_859, 1);
lean_inc(x_872);
lean_inc(x_871);
lean_dec(x_859);
x_873 = l_Lean_Elab_Term_SavedState_restore(x_822, x_9, x_10, x_11, x_12, x_13, x_14, x_872);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_874 = lean_ctor_get(x_873, 1);
lean_inc(x_874);
if (lean_is_exclusive(x_873)) {
 lean_ctor_release(x_873, 0);
 lean_ctor_release(x_873, 1);
 x_875 = x_873;
} else {
 lean_dec_ref(x_873);
 x_875 = lean_box(0);
}
if (lean_is_scalar(x_875)) {
 x_876 = lean_alloc_ctor(0, 2, 0);
} else {
 x_876 = x_875;
}
lean_ctor_set(x_876, 0, x_857);
lean_ctor_set(x_876, 1, x_871);
x_877 = lean_array_push(x_8, x_876);
x_878 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_878, 0, x_877);
lean_ctor_set(x_878, 1, x_874);
return x_878;
}
}
}
else
{
uint8_t x_897; 
x_897 = l_Array_isEmpty___rarg(x_3);
if (x_897 == 0)
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_935; lean_object* x_936; lean_object* x_958; 
x_898 = lean_box(0);
x_899 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_900 = lean_ctor_get(x_899, 0);
lean_inc(x_900);
x_901 = lean_ctor_get(x_899, 1);
lean_inc(x_901);
if (lean_is_exclusive(x_899)) {
 lean_ctor_release(x_899, 0);
 lean_ctor_release(x_899, 1);
 x_902 = x_899;
} else {
 lean_dec_ref(x_899);
 x_902 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_958 = l_Lean_Elab_Term_elabTerm(x_1, x_898, x_819, x_9, x_10, x_11, x_12, x_13, x_14, x_901);
if (lean_obj_tag(x_958) == 0)
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; 
x_959 = lean_ctor_get(x_958, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_958, 1);
lean_inc(x_960);
lean_dec(x_958);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_961 = l___private_Lean_Elab_App_31__elabAppLVals(x_959, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_960);
if (lean_obj_tag(x_961) == 0)
{
if (x_7 == 0)
{
lean_object* x_962; lean_object* x_963; 
lean_dec(x_902);
lean_dec(x_5);
x_962 = lean_ctor_get(x_961, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_961, 1);
lean_inc(x_963);
lean_dec(x_961);
x_935 = x_962;
x_936 = x_963;
goto block_957;
}
else
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; 
x_964 = lean_ctor_get(x_961, 0);
lean_inc(x_964);
x_965 = lean_ctor_get(x_961, 1);
lean_inc(x_965);
lean_dec(x_961);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_966 = l_Lean_Elab_Term_ensureHasType(x_5, x_964, x_898, x_9, x_10, x_11, x_12, x_13, x_14, x_965);
if (lean_obj_tag(x_966) == 0)
{
lean_object* x_967; lean_object* x_968; 
lean_dec(x_902);
x_967 = lean_ctor_get(x_966, 0);
lean_inc(x_967);
x_968 = lean_ctor_get(x_966, 1);
lean_inc(x_968);
lean_dec(x_966);
x_935 = x_967;
x_936 = x_968;
goto block_957;
}
else
{
lean_object* x_969; lean_object* x_970; 
x_969 = lean_ctor_get(x_966, 0);
lean_inc(x_969);
x_970 = lean_ctor_get(x_966, 1);
lean_inc(x_970);
lean_dec(x_966);
x_903 = x_969;
x_904 = x_970;
goto block_934;
}
}
}
else
{
lean_object* x_971; lean_object* x_972; 
lean_dec(x_5);
x_971 = lean_ctor_get(x_961, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_961, 1);
lean_inc(x_972);
lean_dec(x_961);
x_903 = x_971;
x_904 = x_972;
goto block_934;
}
}
else
{
lean_object* x_973; lean_object* x_974; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_973 = lean_ctor_get(x_958, 0);
lean_inc(x_973);
x_974 = lean_ctor_get(x_958, 1);
lean_inc(x_974);
lean_dec(x_958);
x_903 = x_973;
x_904 = x_974;
goto block_934;
}
block_934:
{
if (lean_obj_tag(x_903) == 0)
{
lean_object* x_905; uint8_t x_906; 
lean_dec(x_902);
x_905 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_904);
x_906 = !lean_is_exclusive(x_905);
if (x_906 == 0)
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; uint8_t x_910; 
x_907 = lean_ctor_get(x_905, 0);
x_908 = lean_ctor_get(x_905, 1);
x_909 = l_Lean_Elab_Term_SavedState_restore(x_900, x_9, x_10, x_11, x_12, x_13, x_14, x_908);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_910 = !lean_is_exclusive(x_909);
if (x_910 == 0)
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; 
x_911 = lean_ctor_get(x_909, 1);
x_912 = lean_ctor_get(x_909, 0);
lean_dec(x_912);
lean_ctor_set_tag(x_909, 1);
lean_ctor_set(x_909, 1, x_907);
lean_ctor_set(x_909, 0, x_903);
x_913 = lean_array_push(x_8, x_909);
lean_ctor_set(x_905, 1, x_911);
lean_ctor_set(x_905, 0, x_913);
return x_905;
}
else
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; 
x_914 = lean_ctor_get(x_909, 1);
lean_inc(x_914);
lean_dec(x_909);
x_915 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_915, 0, x_903);
lean_ctor_set(x_915, 1, x_907);
x_916 = lean_array_push(x_8, x_915);
lean_ctor_set(x_905, 1, x_914);
lean_ctor_set(x_905, 0, x_916);
return x_905;
}
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; 
x_917 = lean_ctor_get(x_905, 0);
x_918 = lean_ctor_get(x_905, 1);
lean_inc(x_918);
lean_inc(x_917);
lean_dec(x_905);
x_919 = l_Lean_Elab_Term_SavedState_restore(x_900, x_9, x_10, x_11, x_12, x_13, x_14, x_918);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_920 = lean_ctor_get(x_919, 1);
lean_inc(x_920);
if (lean_is_exclusive(x_919)) {
 lean_ctor_release(x_919, 0);
 lean_ctor_release(x_919, 1);
 x_921 = x_919;
} else {
 lean_dec_ref(x_919);
 x_921 = lean_box(0);
}
if (lean_is_scalar(x_921)) {
 x_922 = lean_alloc_ctor(1, 2, 0);
} else {
 x_922 = x_921;
 lean_ctor_set_tag(x_922, 1);
}
lean_ctor_set(x_922, 0, x_903);
lean_ctor_set(x_922, 1, x_917);
x_923 = lean_array_push(x_8, x_922);
x_924 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_924, 0, x_923);
lean_ctor_set(x_924, 1, x_920);
return x_924;
}
}
else
{
lean_object* x_925; lean_object* x_926; uint8_t x_927; 
lean_dec(x_8);
x_925 = lean_ctor_get(x_903, 0);
lean_inc(x_925);
x_926 = l_Lean_Elab_postponeExceptionId;
x_927 = lean_nat_dec_eq(x_925, x_926);
lean_dec(x_925);
if (x_927 == 0)
{
lean_object* x_928; 
lean_dec(x_900);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_902)) {
 x_928 = lean_alloc_ctor(1, 2, 0);
} else {
 x_928 = x_902;
 lean_ctor_set_tag(x_928, 1);
}
lean_ctor_set(x_928, 0, x_903);
lean_ctor_set(x_928, 1, x_904);
return x_928;
}
else
{
lean_object* x_929; uint8_t x_930; 
lean_dec(x_902);
x_929 = l_Lean_Elab_Term_SavedState_restore(x_900, x_9, x_10, x_11, x_12, x_13, x_14, x_904);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_930 = !lean_is_exclusive(x_929);
if (x_930 == 0)
{
lean_object* x_931; 
x_931 = lean_ctor_get(x_929, 0);
lean_dec(x_931);
lean_ctor_set_tag(x_929, 1);
lean_ctor_set(x_929, 0, x_903);
return x_929;
}
else
{
lean_object* x_932; lean_object* x_933; 
x_932 = lean_ctor_get(x_929, 1);
lean_inc(x_932);
lean_dec(x_929);
x_933 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_933, 0, x_903);
lean_ctor_set(x_933, 1, x_932);
return x_933;
}
}
}
}
block_957:
{
lean_object* x_937; uint8_t x_938; 
x_937 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_936);
x_938 = !lean_is_exclusive(x_937);
if (x_938 == 0)
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; uint8_t x_942; 
x_939 = lean_ctor_get(x_937, 0);
x_940 = lean_ctor_get(x_937, 1);
x_941 = l_Lean_Elab_Term_SavedState_restore(x_900, x_9, x_10, x_11, x_12, x_13, x_14, x_940);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_942 = !lean_is_exclusive(x_941);
if (x_942 == 0)
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; 
x_943 = lean_ctor_get(x_941, 1);
x_944 = lean_ctor_get(x_941, 0);
lean_dec(x_944);
lean_ctor_set(x_941, 1, x_939);
lean_ctor_set(x_941, 0, x_935);
x_945 = lean_array_push(x_8, x_941);
lean_ctor_set(x_937, 1, x_943);
lean_ctor_set(x_937, 0, x_945);
return x_937;
}
else
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; 
x_946 = lean_ctor_get(x_941, 1);
lean_inc(x_946);
lean_dec(x_941);
x_947 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_947, 0, x_935);
lean_ctor_set(x_947, 1, x_939);
x_948 = lean_array_push(x_8, x_947);
lean_ctor_set(x_937, 1, x_946);
lean_ctor_set(x_937, 0, x_948);
return x_937;
}
}
else
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; 
x_949 = lean_ctor_get(x_937, 0);
x_950 = lean_ctor_get(x_937, 1);
lean_inc(x_950);
lean_inc(x_949);
lean_dec(x_937);
x_951 = l_Lean_Elab_Term_SavedState_restore(x_900, x_9, x_10, x_11, x_12, x_13, x_14, x_950);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_952 = lean_ctor_get(x_951, 1);
lean_inc(x_952);
if (lean_is_exclusive(x_951)) {
 lean_ctor_release(x_951, 0);
 lean_ctor_release(x_951, 1);
 x_953 = x_951;
} else {
 lean_dec_ref(x_951);
 x_953 = lean_box(0);
}
if (lean_is_scalar(x_953)) {
 x_954 = lean_alloc_ctor(0, 2, 0);
} else {
 x_954 = x_953;
}
lean_ctor_set(x_954, 0, x_935);
lean_ctor_set(x_954, 1, x_949);
x_955 = lean_array_push(x_8, x_954);
x_956 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_956, 0, x_955);
lean_ctor_set(x_956, 1, x_952);
return x_956;
}
}
}
else
{
uint8_t x_975; 
x_975 = l_Array_isEmpty___rarg(x_4);
if (x_975 == 0)
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_1013; lean_object* x_1014; lean_object* x_1036; 
x_976 = lean_box(0);
x_977 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_978 = lean_ctor_get(x_977, 0);
lean_inc(x_978);
x_979 = lean_ctor_get(x_977, 1);
lean_inc(x_979);
if (lean_is_exclusive(x_977)) {
 lean_ctor_release(x_977, 0);
 lean_ctor_release(x_977, 1);
 x_980 = x_977;
} else {
 lean_dec_ref(x_977);
 x_980 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1036 = l_Lean_Elab_Term_elabTerm(x_1, x_976, x_819, x_9, x_10, x_11, x_12, x_13, x_14, x_979);
if (lean_obj_tag(x_1036) == 0)
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; 
x_1037 = lean_ctor_get(x_1036, 0);
lean_inc(x_1037);
x_1038 = lean_ctor_get(x_1036, 1);
lean_inc(x_1038);
lean_dec(x_1036);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_1039 = l___private_Lean_Elab_App_31__elabAppLVals(x_1037, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_1038);
if (lean_obj_tag(x_1039) == 0)
{
if (x_7 == 0)
{
lean_object* x_1040; lean_object* x_1041; 
lean_dec(x_980);
lean_dec(x_5);
x_1040 = lean_ctor_get(x_1039, 0);
lean_inc(x_1040);
x_1041 = lean_ctor_get(x_1039, 1);
lean_inc(x_1041);
lean_dec(x_1039);
x_1013 = x_1040;
x_1014 = x_1041;
goto block_1035;
}
else
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
x_1042 = lean_ctor_get(x_1039, 0);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_1039, 1);
lean_inc(x_1043);
lean_dec(x_1039);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_1044 = l_Lean_Elab_Term_ensureHasType(x_5, x_1042, x_976, x_9, x_10, x_11, x_12, x_13, x_14, x_1043);
if (lean_obj_tag(x_1044) == 0)
{
lean_object* x_1045; lean_object* x_1046; 
lean_dec(x_980);
x_1045 = lean_ctor_get(x_1044, 0);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_1044, 1);
lean_inc(x_1046);
lean_dec(x_1044);
x_1013 = x_1045;
x_1014 = x_1046;
goto block_1035;
}
else
{
lean_object* x_1047; lean_object* x_1048; 
x_1047 = lean_ctor_get(x_1044, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1044, 1);
lean_inc(x_1048);
lean_dec(x_1044);
x_981 = x_1047;
x_982 = x_1048;
goto block_1012;
}
}
}
else
{
lean_object* x_1049; lean_object* x_1050; 
lean_dec(x_5);
x_1049 = lean_ctor_get(x_1039, 0);
lean_inc(x_1049);
x_1050 = lean_ctor_get(x_1039, 1);
lean_inc(x_1050);
lean_dec(x_1039);
x_981 = x_1049;
x_982 = x_1050;
goto block_1012;
}
}
else
{
lean_object* x_1051; lean_object* x_1052; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1051 = lean_ctor_get(x_1036, 0);
lean_inc(x_1051);
x_1052 = lean_ctor_get(x_1036, 1);
lean_inc(x_1052);
lean_dec(x_1036);
x_981 = x_1051;
x_982 = x_1052;
goto block_1012;
}
block_1012:
{
if (lean_obj_tag(x_981) == 0)
{
lean_object* x_983; uint8_t x_984; 
lean_dec(x_980);
x_983 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_982);
x_984 = !lean_is_exclusive(x_983);
if (x_984 == 0)
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; uint8_t x_988; 
x_985 = lean_ctor_get(x_983, 0);
x_986 = lean_ctor_get(x_983, 1);
x_987 = l_Lean_Elab_Term_SavedState_restore(x_978, x_9, x_10, x_11, x_12, x_13, x_14, x_986);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_988 = !lean_is_exclusive(x_987);
if (x_988 == 0)
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; 
x_989 = lean_ctor_get(x_987, 1);
x_990 = lean_ctor_get(x_987, 0);
lean_dec(x_990);
lean_ctor_set_tag(x_987, 1);
lean_ctor_set(x_987, 1, x_985);
lean_ctor_set(x_987, 0, x_981);
x_991 = lean_array_push(x_8, x_987);
lean_ctor_set(x_983, 1, x_989);
lean_ctor_set(x_983, 0, x_991);
return x_983;
}
else
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; 
x_992 = lean_ctor_get(x_987, 1);
lean_inc(x_992);
lean_dec(x_987);
x_993 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_993, 0, x_981);
lean_ctor_set(x_993, 1, x_985);
x_994 = lean_array_push(x_8, x_993);
lean_ctor_set(x_983, 1, x_992);
lean_ctor_set(x_983, 0, x_994);
return x_983;
}
}
else
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
x_995 = lean_ctor_get(x_983, 0);
x_996 = lean_ctor_get(x_983, 1);
lean_inc(x_996);
lean_inc(x_995);
lean_dec(x_983);
x_997 = l_Lean_Elab_Term_SavedState_restore(x_978, x_9, x_10, x_11, x_12, x_13, x_14, x_996);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_998 = lean_ctor_get(x_997, 1);
lean_inc(x_998);
if (lean_is_exclusive(x_997)) {
 lean_ctor_release(x_997, 0);
 lean_ctor_release(x_997, 1);
 x_999 = x_997;
} else {
 lean_dec_ref(x_997);
 x_999 = lean_box(0);
}
if (lean_is_scalar(x_999)) {
 x_1000 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1000 = x_999;
 lean_ctor_set_tag(x_1000, 1);
}
lean_ctor_set(x_1000, 0, x_981);
lean_ctor_set(x_1000, 1, x_995);
x_1001 = lean_array_push(x_8, x_1000);
x_1002 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1002, 0, x_1001);
lean_ctor_set(x_1002, 1, x_998);
return x_1002;
}
}
else
{
lean_object* x_1003; lean_object* x_1004; uint8_t x_1005; 
lean_dec(x_8);
x_1003 = lean_ctor_get(x_981, 0);
lean_inc(x_1003);
x_1004 = l_Lean_Elab_postponeExceptionId;
x_1005 = lean_nat_dec_eq(x_1003, x_1004);
lean_dec(x_1003);
if (x_1005 == 0)
{
lean_object* x_1006; 
lean_dec(x_978);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_980)) {
 x_1006 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1006 = x_980;
 lean_ctor_set_tag(x_1006, 1);
}
lean_ctor_set(x_1006, 0, x_981);
lean_ctor_set(x_1006, 1, x_982);
return x_1006;
}
else
{
lean_object* x_1007; uint8_t x_1008; 
lean_dec(x_980);
x_1007 = l_Lean_Elab_Term_SavedState_restore(x_978, x_9, x_10, x_11, x_12, x_13, x_14, x_982);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1008 = !lean_is_exclusive(x_1007);
if (x_1008 == 0)
{
lean_object* x_1009; 
x_1009 = lean_ctor_get(x_1007, 0);
lean_dec(x_1009);
lean_ctor_set_tag(x_1007, 1);
lean_ctor_set(x_1007, 0, x_981);
return x_1007;
}
else
{
lean_object* x_1010; lean_object* x_1011; 
x_1010 = lean_ctor_get(x_1007, 1);
lean_inc(x_1010);
lean_dec(x_1007);
x_1011 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1011, 0, x_981);
lean_ctor_set(x_1011, 1, x_1010);
return x_1011;
}
}
}
}
block_1035:
{
lean_object* x_1015; uint8_t x_1016; 
x_1015 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1014);
x_1016 = !lean_is_exclusive(x_1015);
if (x_1016 == 0)
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; uint8_t x_1020; 
x_1017 = lean_ctor_get(x_1015, 0);
x_1018 = lean_ctor_get(x_1015, 1);
x_1019 = l_Lean_Elab_Term_SavedState_restore(x_978, x_9, x_10, x_11, x_12, x_13, x_14, x_1018);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1020 = !lean_is_exclusive(x_1019);
if (x_1020 == 0)
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
x_1021 = lean_ctor_get(x_1019, 1);
x_1022 = lean_ctor_get(x_1019, 0);
lean_dec(x_1022);
lean_ctor_set(x_1019, 1, x_1017);
lean_ctor_set(x_1019, 0, x_1013);
x_1023 = lean_array_push(x_8, x_1019);
lean_ctor_set(x_1015, 1, x_1021);
lean_ctor_set(x_1015, 0, x_1023);
return x_1015;
}
else
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
x_1024 = lean_ctor_get(x_1019, 1);
lean_inc(x_1024);
lean_dec(x_1019);
x_1025 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1025, 0, x_1013);
lean_ctor_set(x_1025, 1, x_1017);
x_1026 = lean_array_push(x_8, x_1025);
lean_ctor_set(x_1015, 1, x_1024);
lean_ctor_set(x_1015, 0, x_1026);
return x_1015;
}
}
else
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
x_1027 = lean_ctor_get(x_1015, 0);
x_1028 = lean_ctor_get(x_1015, 1);
lean_inc(x_1028);
lean_inc(x_1027);
lean_dec(x_1015);
x_1029 = l_Lean_Elab_Term_SavedState_restore(x_978, x_9, x_10, x_11, x_12, x_13, x_14, x_1028);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1030 = lean_ctor_get(x_1029, 1);
lean_inc(x_1030);
if (lean_is_exclusive(x_1029)) {
 lean_ctor_release(x_1029, 0);
 lean_ctor_release(x_1029, 1);
 x_1031 = x_1029;
} else {
 lean_dec_ref(x_1029);
 x_1031 = lean_box(0);
}
if (lean_is_scalar(x_1031)) {
 x_1032 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1032 = x_1031;
}
lean_ctor_set(x_1032, 0, x_1013);
lean_ctor_set(x_1032, 1, x_1027);
x_1033 = lean_array_push(x_8, x_1032);
x_1034 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1034, 0, x_1033);
lean_ctor_set(x_1034, 1, x_1030);
return x_1034;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_7 == 0)
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; uint8_t x_1089; lean_object* x_1090; 
x_1053 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1054 = lean_ctor_get(x_1053, 0);
lean_inc(x_1054);
x_1055 = lean_ctor_get(x_1053, 1);
lean_inc(x_1055);
if (lean_is_exclusive(x_1053)) {
 lean_ctor_release(x_1053, 0);
 lean_ctor_release(x_1053, 1);
 x_1056 = x_1053;
} else {
 lean_dec_ref(x_1053);
 x_1056 = lean_box(0);
}
x_1089 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1090 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_1089, x_9, x_10, x_11, x_12, x_13, x_14, x_1055);
if (lean_obj_tag(x_1090) == 0)
{
lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; uint8_t x_1094; 
lean_dec(x_1056);
x_1091 = lean_ctor_get(x_1090, 0);
lean_inc(x_1091);
x_1092 = lean_ctor_get(x_1090, 1);
lean_inc(x_1092);
lean_dec(x_1090);
x_1093 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1092);
x_1094 = !lean_is_exclusive(x_1093);
if (x_1094 == 0)
{
lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; uint8_t x_1098; 
x_1095 = lean_ctor_get(x_1093, 0);
x_1096 = lean_ctor_get(x_1093, 1);
x_1097 = l_Lean_Elab_Term_SavedState_restore(x_1054, x_9, x_10, x_11, x_12, x_13, x_14, x_1096);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1098 = !lean_is_exclusive(x_1097);
if (x_1098 == 0)
{
lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; 
x_1099 = lean_ctor_get(x_1097, 1);
x_1100 = lean_ctor_get(x_1097, 0);
lean_dec(x_1100);
lean_ctor_set(x_1097, 1, x_1095);
lean_ctor_set(x_1097, 0, x_1091);
x_1101 = lean_array_push(x_8, x_1097);
lean_ctor_set(x_1093, 1, x_1099);
lean_ctor_set(x_1093, 0, x_1101);
return x_1093;
}
else
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; 
x_1102 = lean_ctor_get(x_1097, 1);
lean_inc(x_1102);
lean_dec(x_1097);
x_1103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1103, 0, x_1091);
lean_ctor_set(x_1103, 1, x_1095);
x_1104 = lean_array_push(x_8, x_1103);
lean_ctor_set(x_1093, 1, x_1102);
lean_ctor_set(x_1093, 0, x_1104);
return x_1093;
}
}
else
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; 
x_1105 = lean_ctor_get(x_1093, 0);
x_1106 = lean_ctor_get(x_1093, 1);
lean_inc(x_1106);
lean_inc(x_1105);
lean_dec(x_1093);
x_1107 = l_Lean_Elab_Term_SavedState_restore(x_1054, x_9, x_10, x_11, x_12, x_13, x_14, x_1106);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1108 = lean_ctor_get(x_1107, 1);
lean_inc(x_1108);
if (lean_is_exclusive(x_1107)) {
 lean_ctor_release(x_1107, 0);
 lean_ctor_release(x_1107, 1);
 x_1109 = x_1107;
} else {
 lean_dec_ref(x_1107);
 x_1109 = lean_box(0);
}
if (lean_is_scalar(x_1109)) {
 x_1110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1110 = x_1109;
}
lean_ctor_set(x_1110, 0, x_1091);
lean_ctor_set(x_1110, 1, x_1105);
x_1111 = lean_array_push(x_8, x_1110);
x_1112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1112, 0, x_1111);
lean_ctor_set(x_1112, 1, x_1108);
return x_1112;
}
}
else
{
lean_object* x_1113; lean_object* x_1114; 
x_1113 = lean_ctor_get(x_1090, 0);
lean_inc(x_1113);
x_1114 = lean_ctor_get(x_1090, 1);
lean_inc(x_1114);
lean_dec(x_1090);
x_1057 = x_1113;
x_1058 = x_1114;
goto block_1088;
}
block_1088:
{
if (lean_obj_tag(x_1057) == 0)
{
lean_object* x_1059; uint8_t x_1060; 
lean_dec(x_1056);
x_1059 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1058);
x_1060 = !lean_is_exclusive(x_1059);
if (x_1060 == 0)
{
lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; uint8_t x_1064; 
x_1061 = lean_ctor_get(x_1059, 0);
x_1062 = lean_ctor_get(x_1059, 1);
x_1063 = l_Lean_Elab_Term_SavedState_restore(x_1054, x_9, x_10, x_11, x_12, x_13, x_14, x_1062);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1064 = !lean_is_exclusive(x_1063);
if (x_1064 == 0)
{
lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; 
x_1065 = lean_ctor_get(x_1063, 1);
x_1066 = lean_ctor_get(x_1063, 0);
lean_dec(x_1066);
lean_ctor_set_tag(x_1063, 1);
lean_ctor_set(x_1063, 1, x_1061);
lean_ctor_set(x_1063, 0, x_1057);
x_1067 = lean_array_push(x_8, x_1063);
lean_ctor_set(x_1059, 1, x_1065);
lean_ctor_set(x_1059, 0, x_1067);
return x_1059;
}
else
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
x_1068 = lean_ctor_get(x_1063, 1);
lean_inc(x_1068);
lean_dec(x_1063);
x_1069 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1069, 0, x_1057);
lean_ctor_set(x_1069, 1, x_1061);
x_1070 = lean_array_push(x_8, x_1069);
lean_ctor_set(x_1059, 1, x_1068);
lean_ctor_set(x_1059, 0, x_1070);
return x_1059;
}
}
else
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; 
x_1071 = lean_ctor_get(x_1059, 0);
x_1072 = lean_ctor_get(x_1059, 1);
lean_inc(x_1072);
lean_inc(x_1071);
lean_dec(x_1059);
x_1073 = l_Lean_Elab_Term_SavedState_restore(x_1054, x_9, x_10, x_11, x_12, x_13, x_14, x_1072);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1074 = lean_ctor_get(x_1073, 1);
lean_inc(x_1074);
if (lean_is_exclusive(x_1073)) {
 lean_ctor_release(x_1073, 0);
 lean_ctor_release(x_1073, 1);
 x_1075 = x_1073;
} else {
 lean_dec_ref(x_1073);
 x_1075 = lean_box(0);
}
if (lean_is_scalar(x_1075)) {
 x_1076 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1076 = x_1075;
 lean_ctor_set_tag(x_1076, 1);
}
lean_ctor_set(x_1076, 0, x_1057);
lean_ctor_set(x_1076, 1, x_1071);
x_1077 = lean_array_push(x_8, x_1076);
x_1078 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1078, 0, x_1077);
lean_ctor_set(x_1078, 1, x_1074);
return x_1078;
}
}
else
{
lean_object* x_1079; lean_object* x_1080; uint8_t x_1081; 
lean_dec(x_8);
x_1079 = lean_ctor_get(x_1057, 0);
lean_inc(x_1079);
x_1080 = l_Lean_Elab_postponeExceptionId;
x_1081 = lean_nat_dec_eq(x_1079, x_1080);
lean_dec(x_1079);
if (x_1081 == 0)
{
lean_object* x_1082; 
lean_dec(x_1054);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1056)) {
 x_1082 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1082 = x_1056;
 lean_ctor_set_tag(x_1082, 1);
}
lean_ctor_set(x_1082, 0, x_1057);
lean_ctor_set(x_1082, 1, x_1058);
return x_1082;
}
else
{
lean_object* x_1083; uint8_t x_1084; 
lean_dec(x_1056);
x_1083 = l_Lean_Elab_Term_SavedState_restore(x_1054, x_9, x_10, x_11, x_12, x_13, x_14, x_1058);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1084 = !lean_is_exclusive(x_1083);
if (x_1084 == 0)
{
lean_object* x_1085; 
x_1085 = lean_ctor_get(x_1083, 0);
lean_dec(x_1085);
lean_ctor_set_tag(x_1083, 1);
lean_ctor_set(x_1083, 0, x_1057);
return x_1083;
}
else
{
lean_object* x_1086; lean_object* x_1087; 
x_1086 = lean_ctor_get(x_1083, 1);
lean_inc(x_1086);
lean_dec(x_1083);
x_1087 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1087, 0, x_1057);
lean_ctor_set(x_1087, 1, x_1086);
return x_1087;
}
}
}
}
}
else
{
lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1152; 
x_1115 = lean_box(0);
x_1116 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1117 = lean_ctor_get(x_1116, 0);
lean_inc(x_1117);
x_1118 = lean_ctor_get(x_1116, 1);
lean_inc(x_1118);
if (lean_is_exclusive(x_1116)) {
 lean_ctor_release(x_1116, 0);
 lean_ctor_release(x_1116, 1);
 x_1119 = x_1116;
} else {
 lean_dec_ref(x_1116);
 x_1119 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1152 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_819, x_1115, x_9, x_10, x_11, x_12, x_13, x_14, x_1118);
if (lean_obj_tag(x_1152) == 0)
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; uint8_t x_1156; 
lean_dec(x_1119);
x_1153 = lean_ctor_get(x_1152, 0);
lean_inc(x_1153);
x_1154 = lean_ctor_get(x_1152, 1);
lean_inc(x_1154);
lean_dec(x_1152);
x_1155 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1154);
x_1156 = !lean_is_exclusive(x_1155);
if (x_1156 == 0)
{
lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; uint8_t x_1160; 
x_1157 = lean_ctor_get(x_1155, 0);
x_1158 = lean_ctor_get(x_1155, 1);
x_1159 = l_Lean_Elab_Term_SavedState_restore(x_1117, x_9, x_10, x_11, x_12, x_13, x_14, x_1158);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1160 = !lean_is_exclusive(x_1159);
if (x_1160 == 0)
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; 
x_1161 = lean_ctor_get(x_1159, 1);
x_1162 = lean_ctor_get(x_1159, 0);
lean_dec(x_1162);
lean_ctor_set(x_1159, 1, x_1157);
lean_ctor_set(x_1159, 0, x_1153);
x_1163 = lean_array_push(x_8, x_1159);
lean_ctor_set(x_1155, 1, x_1161);
lean_ctor_set(x_1155, 0, x_1163);
return x_1155;
}
else
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; 
x_1164 = lean_ctor_get(x_1159, 1);
lean_inc(x_1164);
lean_dec(x_1159);
x_1165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1165, 0, x_1153);
lean_ctor_set(x_1165, 1, x_1157);
x_1166 = lean_array_push(x_8, x_1165);
lean_ctor_set(x_1155, 1, x_1164);
lean_ctor_set(x_1155, 0, x_1166);
return x_1155;
}
}
else
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; 
x_1167 = lean_ctor_get(x_1155, 0);
x_1168 = lean_ctor_get(x_1155, 1);
lean_inc(x_1168);
lean_inc(x_1167);
lean_dec(x_1155);
x_1169 = l_Lean_Elab_Term_SavedState_restore(x_1117, x_9, x_10, x_11, x_12, x_13, x_14, x_1168);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1170 = lean_ctor_get(x_1169, 1);
lean_inc(x_1170);
if (lean_is_exclusive(x_1169)) {
 lean_ctor_release(x_1169, 0);
 lean_ctor_release(x_1169, 1);
 x_1171 = x_1169;
} else {
 lean_dec_ref(x_1169);
 x_1171 = lean_box(0);
}
if (lean_is_scalar(x_1171)) {
 x_1172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1172 = x_1171;
}
lean_ctor_set(x_1172, 0, x_1153);
lean_ctor_set(x_1172, 1, x_1167);
x_1173 = lean_array_push(x_8, x_1172);
x_1174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1174, 0, x_1173);
lean_ctor_set(x_1174, 1, x_1170);
return x_1174;
}
}
else
{
lean_object* x_1175; lean_object* x_1176; 
x_1175 = lean_ctor_get(x_1152, 0);
lean_inc(x_1175);
x_1176 = lean_ctor_get(x_1152, 1);
lean_inc(x_1176);
lean_dec(x_1152);
x_1120 = x_1175;
x_1121 = x_1176;
goto block_1151;
}
block_1151:
{
if (lean_obj_tag(x_1120) == 0)
{
lean_object* x_1122; uint8_t x_1123; 
lean_dec(x_1119);
x_1122 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1121);
x_1123 = !lean_is_exclusive(x_1122);
if (x_1123 == 0)
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; uint8_t x_1127; 
x_1124 = lean_ctor_get(x_1122, 0);
x_1125 = lean_ctor_get(x_1122, 1);
x_1126 = l_Lean_Elab_Term_SavedState_restore(x_1117, x_9, x_10, x_11, x_12, x_13, x_14, x_1125);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1127 = !lean_is_exclusive(x_1126);
if (x_1127 == 0)
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; 
x_1128 = lean_ctor_get(x_1126, 1);
x_1129 = lean_ctor_get(x_1126, 0);
lean_dec(x_1129);
lean_ctor_set_tag(x_1126, 1);
lean_ctor_set(x_1126, 1, x_1124);
lean_ctor_set(x_1126, 0, x_1120);
x_1130 = lean_array_push(x_8, x_1126);
lean_ctor_set(x_1122, 1, x_1128);
lean_ctor_set(x_1122, 0, x_1130);
return x_1122;
}
else
{
lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; 
x_1131 = lean_ctor_get(x_1126, 1);
lean_inc(x_1131);
lean_dec(x_1126);
x_1132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1132, 0, x_1120);
lean_ctor_set(x_1132, 1, x_1124);
x_1133 = lean_array_push(x_8, x_1132);
lean_ctor_set(x_1122, 1, x_1131);
lean_ctor_set(x_1122, 0, x_1133);
return x_1122;
}
}
else
{
lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; 
x_1134 = lean_ctor_get(x_1122, 0);
x_1135 = lean_ctor_get(x_1122, 1);
lean_inc(x_1135);
lean_inc(x_1134);
lean_dec(x_1122);
x_1136 = l_Lean_Elab_Term_SavedState_restore(x_1117, x_9, x_10, x_11, x_12, x_13, x_14, x_1135);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1137 = lean_ctor_get(x_1136, 1);
lean_inc(x_1137);
if (lean_is_exclusive(x_1136)) {
 lean_ctor_release(x_1136, 0);
 lean_ctor_release(x_1136, 1);
 x_1138 = x_1136;
} else {
 lean_dec_ref(x_1136);
 x_1138 = lean_box(0);
}
if (lean_is_scalar(x_1138)) {
 x_1139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1139 = x_1138;
 lean_ctor_set_tag(x_1139, 1);
}
lean_ctor_set(x_1139, 0, x_1120);
lean_ctor_set(x_1139, 1, x_1134);
x_1140 = lean_array_push(x_8, x_1139);
x_1141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1141, 0, x_1140);
lean_ctor_set(x_1141, 1, x_1137);
return x_1141;
}
}
else
{
lean_object* x_1142; lean_object* x_1143; uint8_t x_1144; 
lean_dec(x_8);
x_1142 = lean_ctor_get(x_1120, 0);
lean_inc(x_1142);
x_1143 = l_Lean_Elab_postponeExceptionId;
x_1144 = lean_nat_dec_eq(x_1142, x_1143);
lean_dec(x_1142);
if (x_1144 == 0)
{
lean_object* x_1145; 
lean_dec(x_1117);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1119)) {
 x_1145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1145 = x_1119;
 lean_ctor_set_tag(x_1145, 1);
}
lean_ctor_set(x_1145, 0, x_1120);
lean_ctor_set(x_1145, 1, x_1121);
return x_1145;
}
else
{
lean_object* x_1146; uint8_t x_1147; 
lean_dec(x_1119);
x_1146 = l_Lean_Elab_Term_SavedState_restore(x_1117, x_9, x_10, x_11, x_12, x_13, x_14, x_1121);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1147 = !lean_is_exclusive(x_1146);
if (x_1147 == 0)
{
lean_object* x_1148; 
x_1148 = lean_ctor_get(x_1146, 0);
lean_dec(x_1148);
lean_ctor_set_tag(x_1146, 1);
lean_ctor_set(x_1146, 0, x_1120);
return x_1146;
}
else
{
lean_object* x_1149; lean_object* x_1150; 
x_1149 = lean_ctor_get(x_1146, 1);
lean_inc(x_1149);
lean_dec(x_1146);
x_1150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1150, 0, x_1120);
lean_ctor_set(x_1150, 1, x_1149);
return x_1150;
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
lean_object* x_1180; lean_object* x_1181; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1180 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__8;
x_1181 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1180, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1181;
}
}
}
block_1225:
{
if (x_1183 == 0)
{
lean_object* x_1184; uint8_t x_1185; 
x_1184 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__11;
lean_inc(x_1);
x_1185 = l_Lean_Syntax_isOfKind(x_1, x_1184);
if (x_1185 == 0)
{
lean_object* x_1186; uint8_t x_1187; 
x_1186 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__13;
lean_inc(x_1);
x_1187 = l_Lean_Syntax_isOfKind(x_1, x_1186);
if (x_1187 == 0)
{
uint8_t x_1188; 
x_1188 = 0;
x_385 = x_1188;
goto block_1182;
}
else
{
lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; uint8_t x_1192; 
x_1189 = l_Lean_Syntax_getArgs(x_1);
x_1190 = lean_array_get_size(x_1189);
lean_dec(x_1189);
x_1191 = lean_unsigned_to_nat(3u);
x_1192 = lean_nat_dec_eq(x_1190, x_1191);
lean_dec(x_1190);
x_385 = x_1192;
goto block_1182;
}
}
else
{
lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; uint8_t x_1196; 
x_1193 = l_Lean_Syntax_getArgs(x_1);
x_1194 = lean_array_get_size(x_1193);
lean_dec(x_1193);
x_1195 = lean_unsigned_to_nat(4u);
x_1196 = lean_nat_dec_eq(x_1194, x_1195);
if (x_1196 == 0)
{
lean_object* x_1197; uint8_t x_1198; 
x_1197 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__13;
lean_inc(x_1);
x_1198 = l_Lean_Syntax_isOfKind(x_1, x_1197);
if (x_1198 == 0)
{
uint8_t x_1199; 
lean_dec(x_1194);
x_1199 = 0;
x_385 = x_1199;
goto block_1182;
}
else
{
lean_object* x_1200; uint8_t x_1201; 
x_1200 = lean_unsigned_to_nat(3u);
x_1201 = lean_nat_dec_eq(x_1194, x_1200);
lean_dec(x_1194);
x_385 = x_1201;
goto block_1182;
}
}
else
{
lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; 
lean_dec(x_1194);
x_1202 = lean_unsigned_to_nat(0u);
x_1203 = l_Lean_Syntax_getArg(x_1, x_1202);
x_1204 = lean_unsigned_to_nat(2u);
x_1205 = l_Lean_Syntax_getArg(x_1, x_1204);
lean_dec(x_1);
x_1206 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1206, 0, x_1205);
x_1207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1207, 0, x_1206);
lean_ctor_set(x_1207, 1, x_2);
x_1 = x_1203;
x_2 = x_1207;
goto _start;
}
}
}
else
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; 
x_1209 = lean_unsigned_to_nat(0u);
x_1210 = l_Lean_Syntax_getArg(x_1, x_1209);
x_1211 = lean_unsigned_to_nat(2u);
x_1212 = l_Lean_Syntax_getArg(x_1, x_1211);
lean_dec(x_1);
x_1213 = l_Lean_Elab_Term_getCurrMacroScope(x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_1214 = lean_ctor_get(x_1213, 1);
lean_inc(x_1214);
lean_dec(x_1213);
x_1215 = l_Lean_Elab_Term_getMainModule___rarg(x_14, x_1214);
x_1216 = lean_ctor_get(x_1215, 1);
lean_inc(x_1216);
lean_dec(x_1215);
x_1217 = l_Array_empty___closed__1;
x_1218 = lean_array_push(x_1217, x_1210);
x_1219 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__14;
x_1220 = lean_array_push(x_1218, x_1219);
x_1221 = lean_array_push(x_1220, x_1212);
x_1222 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__9;
x_1223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1223, 0, x_1222);
lean_ctor_set(x_1223, 1, x_1221);
x_1 = x_1223;
x_15 = x_1216;
goto _start;
}
}
block_1622:
{
if (x_1226 == 0)
{
lean_object* x_1227; uint8_t x_1228; 
x_1227 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__16;
lean_inc(x_1);
x_1228 = l_Lean_Syntax_isOfKind(x_1, x_1227);
if (x_1228 == 0)
{
uint8_t x_1229; 
x_1229 = 0;
x_1183 = x_1229;
goto block_1225;
}
else
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; uint8_t x_1233; 
x_1230 = l_Lean_Syntax_getArgs(x_1);
x_1231 = lean_array_get_size(x_1230);
lean_dec(x_1230);
x_1232 = lean_unsigned_to_nat(3u);
x_1233 = lean_nat_dec_eq(x_1231, x_1232);
lean_dec(x_1231);
x_1183 = x_1233;
goto block_1225;
}
}
else
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; uint8_t x_1239; 
x_1234 = lean_unsigned_to_nat(0u);
x_1235 = l_Lean_Syntax_getArg(x_1, x_1234);
x_1236 = lean_unsigned_to_nat(2u);
x_1237 = l_Lean_Syntax_getArg(x_1, x_1236);
x_1238 = l_Lean_fieldIdxKind___closed__2;
lean_inc(x_1237);
x_1239 = l_Lean_Syntax_isOfKind(x_1237, x_1238);
if (x_1239 == 0)
{
lean_object* x_1240; uint8_t x_1241; 
x_1240 = l_Lean_identKind___closed__2;
lean_inc(x_1237);
x_1241 = l_Lean_Syntax_isOfKind(x_1237, x_1240);
if (x_1241 == 0)
{
uint8_t x_1242; uint8_t x_1243; 
lean_dec(x_1237);
lean_dec(x_1235);
x_1242 = l_List_isEmpty___rarg(x_2);
if (x_7 == 0)
{
uint8_t x_1602; 
x_1602 = 1;
x_1243 = x_1602;
goto block_1601;
}
else
{
uint8_t x_1603; 
x_1603 = 0;
x_1243 = x_1603;
goto block_1601;
}
block_1601:
{
if (x_1242 == 0)
{
lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1281; lean_object* x_1282; lean_object* x_1304; 
x_1244 = lean_box(0);
x_1245 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1246 = lean_ctor_get(x_1245, 0);
lean_inc(x_1246);
x_1247 = lean_ctor_get(x_1245, 1);
lean_inc(x_1247);
if (lean_is_exclusive(x_1245)) {
 lean_ctor_release(x_1245, 0);
 lean_ctor_release(x_1245, 1);
 x_1248 = x_1245;
} else {
 lean_dec_ref(x_1245);
 x_1248 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1304 = l_Lean_Elab_Term_elabTerm(x_1, x_1244, x_1243, x_9, x_10, x_11, x_12, x_13, x_14, x_1247);
if (lean_obj_tag(x_1304) == 0)
{
lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; 
x_1305 = lean_ctor_get(x_1304, 0);
lean_inc(x_1305);
x_1306 = lean_ctor_get(x_1304, 1);
lean_inc(x_1306);
lean_dec(x_1304);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_1307 = l___private_Lean_Elab_App_31__elabAppLVals(x_1305, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_1306);
if (lean_obj_tag(x_1307) == 0)
{
if (x_7 == 0)
{
lean_object* x_1308; lean_object* x_1309; 
lean_dec(x_1248);
lean_dec(x_5);
x_1308 = lean_ctor_get(x_1307, 0);
lean_inc(x_1308);
x_1309 = lean_ctor_get(x_1307, 1);
lean_inc(x_1309);
lean_dec(x_1307);
x_1281 = x_1308;
x_1282 = x_1309;
goto block_1303;
}
else
{
lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; 
x_1310 = lean_ctor_get(x_1307, 0);
lean_inc(x_1310);
x_1311 = lean_ctor_get(x_1307, 1);
lean_inc(x_1311);
lean_dec(x_1307);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_1312 = l_Lean_Elab_Term_ensureHasType(x_5, x_1310, x_1244, x_9, x_10, x_11, x_12, x_13, x_14, x_1311);
if (lean_obj_tag(x_1312) == 0)
{
lean_object* x_1313; lean_object* x_1314; 
lean_dec(x_1248);
x_1313 = lean_ctor_get(x_1312, 0);
lean_inc(x_1313);
x_1314 = lean_ctor_get(x_1312, 1);
lean_inc(x_1314);
lean_dec(x_1312);
x_1281 = x_1313;
x_1282 = x_1314;
goto block_1303;
}
else
{
lean_object* x_1315; lean_object* x_1316; 
x_1315 = lean_ctor_get(x_1312, 0);
lean_inc(x_1315);
x_1316 = lean_ctor_get(x_1312, 1);
lean_inc(x_1316);
lean_dec(x_1312);
x_1249 = x_1315;
x_1250 = x_1316;
goto block_1280;
}
}
}
else
{
lean_object* x_1317; lean_object* x_1318; 
lean_dec(x_5);
x_1317 = lean_ctor_get(x_1307, 0);
lean_inc(x_1317);
x_1318 = lean_ctor_get(x_1307, 1);
lean_inc(x_1318);
lean_dec(x_1307);
x_1249 = x_1317;
x_1250 = x_1318;
goto block_1280;
}
}
else
{
lean_object* x_1319; lean_object* x_1320; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1319 = lean_ctor_get(x_1304, 0);
lean_inc(x_1319);
x_1320 = lean_ctor_get(x_1304, 1);
lean_inc(x_1320);
lean_dec(x_1304);
x_1249 = x_1319;
x_1250 = x_1320;
goto block_1280;
}
block_1280:
{
if (lean_obj_tag(x_1249) == 0)
{
lean_object* x_1251; uint8_t x_1252; 
lean_dec(x_1248);
x_1251 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1250);
x_1252 = !lean_is_exclusive(x_1251);
if (x_1252 == 0)
{
lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; uint8_t x_1256; 
x_1253 = lean_ctor_get(x_1251, 0);
x_1254 = lean_ctor_get(x_1251, 1);
x_1255 = l_Lean_Elab_Term_SavedState_restore(x_1246, x_9, x_10, x_11, x_12, x_13, x_14, x_1254);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1256 = !lean_is_exclusive(x_1255);
if (x_1256 == 0)
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; 
x_1257 = lean_ctor_get(x_1255, 1);
x_1258 = lean_ctor_get(x_1255, 0);
lean_dec(x_1258);
lean_ctor_set_tag(x_1255, 1);
lean_ctor_set(x_1255, 1, x_1253);
lean_ctor_set(x_1255, 0, x_1249);
x_1259 = lean_array_push(x_8, x_1255);
lean_ctor_set(x_1251, 1, x_1257);
lean_ctor_set(x_1251, 0, x_1259);
return x_1251;
}
else
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; 
x_1260 = lean_ctor_get(x_1255, 1);
lean_inc(x_1260);
lean_dec(x_1255);
x_1261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1261, 0, x_1249);
lean_ctor_set(x_1261, 1, x_1253);
x_1262 = lean_array_push(x_8, x_1261);
lean_ctor_set(x_1251, 1, x_1260);
lean_ctor_set(x_1251, 0, x_1262);
return x_1251;
}
}
else
{
lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; 
x_1263 = lean_ctor_get(x_1251, 0);
x_1264 = lean_ctor_get(x_1251, 1);
lean_inc(x_1264);
lean_inc(x_1263);
lean_dec(x_1251);
x_1265 = l_Lean_Elab_Term_SavedState_restore(x_1246, x_9, x_10, x_11, x_12, x_13, x_14, x_1264);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1266 = lean_ctor_get(x_1265, 1);
lean_inc(x_1266);
if (lean_is_exclusive(x_1265)) {
 lean_ctor_release(x_1265, 0);
 lean_ctor_release(x_1265, 1);
 x_1267 = x_1265;
} else {
 lean_dec_ref(x_1265);
 x_1267 = lean_box(0);
}
if (lean_is_scalar(x_1267)) {
 x_1268 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1268 = x_1267;
 lean_ctor_set_tag(x_1268, 1);
}
lean_ctor_set(x_1268, 0, x_1249);
lean_ctor_set(x_1268, 1, x_1263);
x_1269 = lean_array_push(x_8, x_1268);
x_1270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1270, 0, x_1269);
lean_ctor_set(x_1270, 1, x_1266);
return x_1270;
}
}
else
{
lean_object* x_1271; lean_object* x_1272; uint8_t x_1273; 
lean_dec(x_8);
x_1271 = lean_ctor_get(x_1249, 0);
lean_inc(x_1271);
x_1272 = l_Lean_Elab_postponeExceptionId;
x_1273 = lean_nat_dec_eq(x_1271, x_1272);
lean_dec(x_1271);
if (x_1273 == 0)
{
lean_object* x_1274; 
lean_dec(x_1246);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1248)) {
 x_1274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1274 = x_1248;
 lean_ctor_set_tag(x_1274, 1);
}
lean_ctor_set(x_1274, 0, x_1249);
lean_ctor_set(x_1274, 1, x_1250);
return x_1274;
}
else
{
lean_object* x_1275; uint8_t x_1276; 
lean_dec(x_1248);
x_1275 = l_Lean_Elab_Term_SavedState_restore(x_1246, x_9, x_10, x_11, x_12, x_13, x_14, x_1250);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1276 = !lean_is_exclusive(x_1275);
if (x_1276 == 0)
{
lean_object* x_1277; 
x_1277 = lean_ctor_get(x_1275, 0);
lean_dec(x_1277);
lean_ctor_set_tag(x_1275, 1);
lean_ctor_set(x_1275, 0, x_1249);
return x_1275;
}
else
{
lean_object* x_1278; lean_object* x_1279; 
x_1278 = lean_ctor_get(x_1275, 1);
lean_inc(x_1278);
lean_dec(x_1275);
x_1279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1279, 0, x_1249);
lean_ctor_set(x_1279, 1, x_1278);
return x_1279;
}
}
}
}
block_1303:
{
lean_object* x_1283; uint8_t x_1284; 
x_1283 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1282);
x_1284 = !lean_is_exclusive(x_1283);
if (x_1284 == 0)
{
lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; uint8_t x_1288; 
x_1285 = lean_ctor_get(x_1283, 0);
x_1286 = lean_ctor_get(x_1283, 1);
x_1287 = l_Lean_Elab_Term_SavedState_restore(x_1246, x_9, x_10, x_11, x_12, x_13, x_14, x_1286);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1288 = !lean_is_exclusive(x_1287);
if (x_1288 == 0)
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; 
x_1289 = lean_ctor_get(x_1287, 1);
x_1290 = lean_ctor_get(x_1287, 0);
lean_dec(x_1290);
lean_ctor_set(x_1287, 1, x_1285);
lean_ctor_set(x_1287, 0, x_1281);
x_1291 = lean_array_push(x_8, x_1287);
lean_ctor_set(x_1283, 1, x_1289);
lean_ctor_set(x_1283, 0, x_1291);
return x_1283;
}
else
{
lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; 
x_1292 = lean_ctor_get(x_1287, 1);
lean_inc(x_1292);
lean_dec(x_1287);
x_1293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1293, 0, x_1281);
lean_ctor_set(x_1293, 1, x_1285);
x_1294 = lean_array_push(x_8, x_1293);
lean_ctor_set(x_1283, 1, x_1292);
lean_ctor_set(x_1283, 0, x_1294);
return x_1283;
}
}
else
{
lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; 
x_1295 = lean_ctor_get(x_1283, 0);
x_1296 = lean_ctor_get(x_1283, 1);
lean_inc(x_1296);
lean_inc(x_1295);
lean_dec(x_1283);
x_1297 = l_Lean_Elab_Term_SavedState_restore(x_1246, x_9, x_10, x_11, x_12, x_13, x_14, x_1296);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1298 = lean_ctor_get(x_1297, 1);
lean_inc(x_1298);
if (lean_is_exclusive(x_1297)) {
 lean_ctor_release(x_1297, 0);
 lean_ctor_release(x_1297, 1);
 x_1299 = x_1297;
} else {
 lean_dec_ref(x_1297);
 x_1299 = lean_box(0);
}
if (lean_is_scalar(x_1299)) {
 x_1300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1300 = x_1299;
}
lean_ctor_set(x_1300, 0, x_1281);
lean_ctor_set(x_1300, 1, x_1295);
x_1301 = lean_array_push(x_8, x_1300);
x_1302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1302, 0, x_1301);
lean_ctor_set(x_1302, 1, x_1298);
return x_1302;
}
}
}
else
{
uint8_t x_1321; 
x_1321 = l_Array_isEmpty___rarg(x_3);
if (x_1321 == 0)
{
lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1359; lean_object* x_1360; lean_object* x_1382; 
x_1322 = lean_box(0);
x_1323 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1324 = lean_ctor_get(x_1323, 0);
lean_inc(x_1324);
x_1325 = lean_ctor_get(x_1323, 1);
lean_inc(x_1325);
if (lean_is_exclusive(x_1323)) {
 lean_ctor_release(x_1323, 0);
 lean_ctor_release(x_1323, 1);
 x_1326 = x_1323;
} else {
 lean_dec_ref(x_1323);
 x_1326 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1382 = l_Lean_Elab_Term_elabTerm(x_1, x_1322, x_1243, x_9, x_10, x_11, x_12, x_13, x_14, x_1325);
if (lean_obj_tag(x_1382) == 0)
{
lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; 
x_1383 = lean_ctor_get(x_1382, 0);
lean_inc(x_1383);
x_1384 = lean_ctor_get(x_1382, 1);
lean_inc(x_1384);
lean_dec(x_1382);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_1385 = l___private_Lean_Elab_App_31__elabAppLVals(x_1383, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_1384);
if (lean_obj_tag(x_1385) == 0)
{
if (x_7 == 0)
{
lean_object* x_1386; lean_object* x_1387; 
lean_dec(x_1326);
lean_dec(x_5);
x_1386 = lean_ctor_get(x_1385, 0);
lean_inc(x_1386);
x_1387 = lean_ctor_get(x_1385, 1);
lean_inc(x_1387);
lean_dec(x_1385);
x_1359 = x_1386;
x_1360 = x_1387;
goto block_1381;
}
else
{
lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; 
x_1388 = lean_ctor_get(x_1385, 0);
lean_inc(x_1388);
x_1389 = lean_ctor_get(x_1385, 1);
lean_inc(x_1389);
lean_dec(x_1385);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_1390 = l_Lean_Elab_Term_ensureHasType(x_5, x_1388, x_1322, x_9, x_10, x_11, x_12, x_13, x_14, x_1389);
if (lean_obj_tag(x_1390) == 0)
{
lean_object* x_1391; lean_object* x_1392; 
lean_dec(x_1326);
x_1391 = lean_ctor_get(x_1390, 0);
lean_inc(x_1391);
x_1392 = lean_ctor_get(x_1390, 1);
lean_inc(x_1392);
lean_dec(x_1390);
x_1359 = x_1391;
x_1360 = x_1392;
goto block_1381;
}
else
{
lean_object* x_1393; lean_object* x_1394; 
x_1393 = lean_ctor_get(x_1390, 0);
lean_inc(x_1393);
x_1394 = lean_ctor_get(x_1390, 1);
lean_inc(x_1394);
lean_dec(x_1390);
x_1327 = x_1393;
x_1328 = x_1394;
goto block_1358;
}
}
}
else
{
lean_object* x_1395; lean_object* x_1396; 
lean_dec(x_5);
x_1395 = lean_ctor_get(x_1385, 0);
lean_inc(x_1395);
x_1396 = lean_ctor_get(x_1385, 1);
lean_inc(x_1396);
lean_dec(x_1385);
x_1327 = x_1395;
x_1328 = x_1396;
goto block_1358;
}
}
else
{
lean_object* x_1397; lean_object* x_1398; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1397 = lean_ctor_get(x_1382, 0);
lean_inc(x_1397);
x_1398 = lean_ctor_get(x_1382, 1);
lean_inc(x_1398);
lean_dec(x_1382);
x_1327 = x_1397;
x_1328 = x_1398;
goto block_1358;
}
block_1358:
{
if (lean_obj_tag(x_1327) == 0)
{
lean_object* x_1329; uint8_t x_1330; 
lean_dec(x_1326);
x_1329 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1328);
x_1330 = !lean_is_exclusive(x_1329);
if (x_1330 == 0)
{
lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; uint8_t x_1334; 
x_1331 = lean_ctor_get(x_1329, 0);
x_1332 = lean_ctor_get(x_1329, 1);
x_1333 = l_Lean_Elab_Term_SavedState_restore(x_1324, x_9, x_10, x_11, x_12, x_13, x_14, x_1332);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1334 = !lean_is_exclusive(x_1333);
if (x_1334 == 0)
{
lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; 
x_1335 = lean_ctor_get(x_1333, 1);
x_1336 = lean_ctor_get(x_1333, 0);
lean_dec(x_1336);
lean_ctor_set_tag(x_1333, 1);
lean_ctor_set(x_1333, 1, x_1331);
lean_ctor_set(x_1333, 0, x_1327);
x_1337 = lean_array_push(x_8, x_1333);
lean_ctor_set(x_1329, 1, x_1335);
lean_ctor_set(x_1329, 0, x_1337);
return x_1329;
}
else
{
lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; 
x_1338 = lean_ctor_get(x_1333, 1);
lean_inc(x_1338);
lean_dec(x_1333);
x_1339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1339, 0, x_1327);
lean_ctor_set(x_1339, 1, x_1331);
x_1340 = lean_array_push(x_8, x_1339);
lean_ctor_set(x_1329, 1, x_1338);
lean_ctor_set(x_1329, 0, x_1340);
return x_1329;
}
}
else
{
lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; 
x_1341 = lean_ctor_get(x_1329, 0);
x_1342 = lean_ctor_get(x_1329, 1);
lean_inc(x_1342);
lean_inc(x_1341);
lean_dec(x_1329);
x_1343 = l_Lean_Elab_Term_SavedState_restore(x_1324, x_9, x_10, x_11, x_12, x_13, x_14, x_1342);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1344 = lean_ctor_get(x_1343, 1);
lean_inc(x_1344);
if (lean_is_exclusive(x_1343)) {
 lean_ctor_release(x_1343, 0);
 lean_ctor_release(x_1343, 1);
 x_1345 = x_1343;
} else {
 lean_dec_ref(x_1343);
 x_1345 = lean_box(0);
}
if (lean_is_scalar(x_1345)) {
 x_1346 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1346 = x_1345;
 lean_ctor_set_tag(x_1346, 1);
}
lean_ctor_set(x_1346, 0, x_1327);
lean_ctor_set(x_1346, 1, x_1341);
x_1347 = lean_array_push(x_8, x_1346);
x_1348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1348, 0, x_1347);
lean_ctor_set(x_1348, 1, x_1344);
return x_1348;
}
}
else
{
lean_object* x_1349; lean_object* x_1350; uint8_t x_1351; 
lean_dec(x_8);
x_1349 = lean_ctor_get(x_1327, 0);
lean_inc(x_1349);
x_1350 = l_Lean_Elab_postponeExceptionId;
x_1351 = lean_nat_dec_eq(x_1349, x_1350);
lean_dec(x_1349);
if (x_1351 == 0)
{
lean_object* x_1352; 
lean_dec(x_1324);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1326)) {
 x_1352 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1352 = x_1326;
 lean_ctor_set_tag(x_1352, 1);
}
lean_ctor_set(x_1352, 0, x_1327);
lean_ctor_set(x_1352, 1, x_1328);
return x_1352;
}
else
{
lean_object* x_1353; uint8_t x_1354; 
lean_dec(x_1326);
x_1353 = l_Lean_Elab_Term_SavedState_restore(x_1324, x_9, x_10, x_11, x_12, x_13, x_14, x_1328);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1354 = !lean_is_exclusive(x_1353);
if (x_1354 == 0)
{
lean_object* x_1355; 
x_1355 = lean_ctor_get(x_1353, 0);
lean_dec(x_1355);
lean_ctor_set_tag(x_1353, 1);
lean_ctor_set(x_1353, 0, x_1327);
return x_1353;
}
else
{
lean_object* x_1356; lean_object* x_1357; 
x_1356 = lean_ctor_get(x_1353, 1);
lean_inc(x_1356);
lean_dec(x_1353);
x_1357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1357, 0, x_1327);
lean_ctor_set(x_1357, 1, x_1356);
return x_1357;
}
}
}
}
block_1381:
{
lean_object* x_1361; uint8_t x_1362; 
x_1361 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1360);
x_1362 = !lean_is_exclusive(x_1361);
if (x_1362 == 0)
{
lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; uint8_t x_1366; 
x_1363 = lean_ctor_get(x_1361, 0);
x_1364 = lean_ctor_get(x_1361, 1);
x_1365 = l_Lean_Elab_Term_SavedState_restore(x_1324, x_9, x_10, x_11, x_12, x_13, x_14, x_1364);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1366 = !lean_is_exclusive(x_1365);
if (x_1366 == 0)
{
lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; 
x_1367 = lean_ctor_get(x_1365, 1);
x_1368 = lean_ctor_get(x_1365, 0);
lean_dec(x_1368);
lean_ctor_set(x_1365, 1, x_1363);
lean_ctor_set(x_1365, 0, x_1359);
x_1369 = lean_array_push(x_8, x_1365);
lean_ctor_set(x_1361, 1, x_1367);
lean_ctor_set(x_1361, 0, x_1369);
return x_1361;
}
else
{
lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; 
x_1370 = lean_ctor_get(x_1365, 1);
lean_inc(x_1370);
lean_dec(x_1365);
x_1371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1371, 0, x_1359);
lean_ctor_set(x_1371, 1, x_1363);
x_1372 = lean_array_push(x_8, x_1371);
lean_ctor_set(x_1361, 1, x_1370);
lean_ctor_set(x_1361, 0, x_1372);
return x_1361;
}
}
else
{
lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; 
x_1373 = lean_ctor_get(x_1361, 0);
x_1374 = lean_ctor_get(x_1361, 1);
lean_inc(x_1374);
lean_inc(x_1373);
lean_dec(x_1361);
x_1375 = l_Lean_Elab_Term_SavedState_restore(x_1324, x_9, x_10, x_11, x_12, x_13, x_14, x_1374);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1376 = lean_ctor_get(x_1375, 1);
lean_inc(x_1376);
if (lean_is_exclusive(x_1375)) {
 lean_ctor_release(x_1375, 0);
 lean_ctor_release(x_1375, 1);
 x_1377 = x_1375;
} else {
 lean_dec_ref(x_1375);
 x_1377 = lean_box(0);
}
if (lean_is_scalar(x_1377)) {
 x_1378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1378 = x_1377;
}
lean_ctor_set(x_1378, 0, x_1359);
lean_ctor_set(x_1378, 1, x_1373);
x_1379 = lean_array_push(x_8, x_1378);
x_1380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1380, 0, x_1379);
lean_ctor_set(x_1380, 1, x_1376);
return x_1380;
}
}
}
else
{
uint8_t x_1399; 
x_1399 = l_Array_isEmpty___rarg(x_4);
if (x_1399 == 0)
{
lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1437; lean_object* x_1438; lean_object* x_1460; 
x_1400 = lean_box(0);
x_1401 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1402 = lean_ctor_get(x_1401, 0);
lean_inc(x_1402);
x_1403 = lean_ctor_get(x_1401, 1);
lean_inc(x_1403);
if (lean_is_exclusive(x_1401)) {
 lean_ctor_release(x_1401, 0);
 lean_ctor_release(x_1401, 1);
 x_1404 = x_1401;
} else {
 lean_dec_ref(x_1401);
 x_1404 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1460 = l_Lean_Elab_Term_elabTerm(x_1, x_1400, x_1243, x_9, x_10, x_11, x_12, x_13, x_14, x_1403);
if (lean_obj_tag(x_1460) == 0)
{
lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; 
x_1461 = lean_ctor_get(x_1460, 0);
lean_inc(x_1461);
x_1462 = lean_ctor_get(x_1460, 1);
lean_inc(x_1462);
lean_dec(x_1460);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_1463 = l___private_Lean_Elab_App_31__elabAppLVals(x_1461, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_1462);
if (lean_obj_tag(x_1463) == 0)
{
if (x_7 == 0)
{
lean_object* x_1464; lean_object* x_1465; 
lean_dec(x_1404);
lean_dec(x_5);
x_1464 = lean_ctor_get(x_1463, 0);
lean_inc(x_1464);
x_1465 = lean_ctor_get(x_1463, 1);
lean_inc(x_1465);
lean_dec(x_1463);
x_1437 = x_1464;
x_1438 = x_1465;
goto block_1459;
}
else
{
lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; 
x_1466 = lean_ctor_get(x_1463, 0);
lean_inc(x_1466);
x_1467 = lean_ctor_get(x_1463, 1);
lean_inc(x_1467);
lean_dec(x_1463);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_1468 = l_Lean_Elab_Term_ensureHasType(x_5, x_1466, x_1400, x_9, x_10, x_11, x_12, x_13, x_14, x_1467);
if (lean_obj_tag(x_1468) == 0)
{
lean_object* x_1469; lean_object* x_1470; 
lean_dec(x_1404);
x_1469 = lean_ctor_get(x_1468, 0);
lean_inc(x_1469);
x_1470 = lean_ctor_get(x_1468, 1);
lean_inc(x_1470);
lean_dec(x_1468);
x_1437 = x_1469;
x_1438 = x_1470;
goto block_1459;
}
else
{
lean_object* x_1471; lean_object* x_1472; 
x_1471 = lean_ctor_get(x_1468, 0);
lean_inc(x_1471);
x_1472 = lean_ctor_get(x_1468, 1);
lean_inc(x_1472);
lean_dec(x_1468);
x_1405 = x_1471;
x_1406 = x_1472;
goto block_1436;
}
}
}
else
{
lean_object* x_1473; lean_object* x_1474; 
lean_dec(x_5);
x_1473 = lean_ctor_get(x_1463, 0);
lean_inc(x_1473);
x_1474 = lean_ctor_get(x_1463, 1);
lean_inc(x_1474);
lean_dec(x_1463);
x_1405 = x_1473;
x_1406 = x_1474;
goto block_1436;
}
}
else
{
lean_object* x_1475; lean_object* x_1476; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1475 = lean_ctor_get(x_1460, 0);
lean_inc(x_1475);
x_1476 = lean_ctor_get(x_1460, 1);
lean_inc(x_1476);
lean_dec(x_1460);
x_1405 = x_1475;
x_1406 = x_1476;
goto block_1436;
}
block_1436:
{
if (lean_obj_tag(x_1405) == 0)
{
lean_object* x_1407; uint8_t x_1408; 
lean_dec(x_1404);
x_1407 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1406);
x_1408 = !lean_is_exclusive(x_1407);
if (x_1408 == 0)
{
lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; uint8_t x_1412; 
x_1409 = lean_ctor_get(x_1407, 0);
x_1410 = lean_ctor_get(x_1407, 1);
x_1411 = l_Lean_Elab_Term_SavedState_restore(x_1402, x_9, x_10, x_11, x_12, x_13, x_14, x_1410);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1412 = !lean_is_exclusive(x_1411);
if (x_1412 == 0)
{
lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; 
x_1413 = lean_ctor_get(x_1411, 1);
x_1414 = lean_ctor_get(x_1411, 0);
lean_dec(x_1414);
lean_ctor_set_tag(x_1411, 1);
lean_ctor_set(x_1411, 1, x_1409);
lean_ctor_set(x_1411, 0, x_1405);
x_1415 = lean_array_push(x_8, x_1411);
lean_ctor_set(x_1407, 1, x_1413);
lean_ctor_set(x_1407, 0, x_1415);
return x_1407;
}
else
{
lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; 
x_1416 = lean_ctor_get(x_1411, 1);
lean_inc(x_1416);
lean_dec(x_1411);
x_1417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1417, 0, x_1405);
lean_ctor_set(x_1417, 1, x_1409);
x_1418 = lean_array_push(x_8, x_1417);
lean_ctor_set(x_1407, 1, x_1416);
lean_ctor_set(x_1407, 0, x_1418);
return x_1407;
}
}
else
{
lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; 
x_1419 = lean_ctor_get(x_1407, 0);
x_1420 = lean_ctor_get(x_1407, 1);
lean_inc(x_1420);
lean_inc(x_1419);
lean_dec(x_1407);
x_1421 = l_Lean_Elab_Term_SavedState_restore(x_1402, x_9, x_10, x_11, x_12, x_13, x_14, x_1420);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1422 = lean_ctor_get(x_1421, 1);
lean_inc(x_1422);
if (lean_is_exclusive(x_1421)) {
 lean_ctor_release(x_1421, 0);
 lean_ctor_release(x_1421, 1);
 x_1423 = x_1421;
} else {
 lean_dec_ref(x_1421);
 x_1423 = lean_box(0);
}
if (lean_is_scalar(x_1423)) {
 x_1424 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1424 = x_1423;
 lean_ctor_set_tag(x_1424, 1);
}
lean_ctor_set(x_1424, 0, x_1405);
lean_ctor_set(x_1424, 1, x_1419);
x_1425 = lean_array_push(x_8, x_1424);
x_1426 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1426, 0, x_1425);
lean_ctor_set(x_1426, 1, x_1422);
return x_1426;
}
}
else
{
lean_object* x_1427; lean_object* x_1428; uint8_t x_1429; 
lean_dec(x_8);
x_1427 = lean_ctor_get(x_1405, 0);
lean_inc(x_1427);
x_1428 = l_Lean_Elab_postponeExceptionId;
x_1429 = lean_nat_dec_eq(x_1427, x_1428);
lean_dec(x_1427);
if (x_1429 == 0)
{
lean_object* x_1430; 
lean_dec(x_1402);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1404)) {
 x_1430 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1430 = x_1404;
 lean_ctor_set_tag(x_1430, 1);
}
lean_ctor_set(x_1430, 0, x_1405);
lean_ctor_set(x_1430, 1, x_1406);
return x_1430;
}
else
{
lean_object* x_1431; uint8_t x_1432; 
lean_dec(x_1404);
x_1431 = l_Lean_Elab_Term_SavedState_restore(x_1402, x_9, x_10, x_11, x_12, x_13, x_14, x_1406);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1432 = !lean_is_exclusive(x_1431);
if (x_1432 == 0)
{
lean_object* x_1433; 
x_1433 = lean_ctor_get(x_1431, 0);
lean_dec(x_1433);
lean_ctor_set_tag(x_1431, 1);
lean_ctor_set(x_1431, 0, x_1405);
return x_1431;
}
else
{
lean_object* x_1434; lean_object* x_1435; 
x_1434 = lean_ctor_get(x_1431, 1);
lean_inc(x_1434);
lean_dec(x_1431);
x_1435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1435, 0, x_1405);
lean_ctor_set(x_1435, 1, x_1434);
return x_1435;
}
}
}
}
block_1459:
{
lean_object* x_1439; uint8_t x_1440; 
x_1439 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1438);
x_1440 = !lean_is_exclusive(x_1439);
if (x_1440 == 0)
{
lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; uint8_t x_1444; 
x_1441 = lean_ctor_get(x_1439, 0);
x_1442 = lean_ctor_get(x_1439, 1);
x_1443 = l_Lean_Elab_Term_SavedState_restore(x_1402, x_9, x_10, x_11, x_12, x_13, x_14, x_1442);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1444 = !lean_is_exclusive(x_1443);
if (x_1444 == 0)
{
lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; 
x_1445 = lean_ctor_get(x_1443, 1);
x_1446 = lean_ctor_get(x_1443, 0);
lean_dec(x_1446);
lean_ctor_set(x_1443, 1, x_1441);
lean_ctor_set(x_1443, 0, x_1437);
x_1447 = lean_array_push(x_8, x_1443);
lean_ctor_set(x_1439, 1, x_1445);
lean_ctor_set(x_1439, 0, x_1447);
return x_1439;
}
else
{
lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; 
x_1448 = lean_ctor_get(x_1443, 1);
lean_inc(x_1448);
lean_dec(x_1443);
x_1449 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1449, 0, x_1437);
lean_ctor_set(x_1449, 1, x_1441);
x_1450 = lean_array_push(x_8, x_1449);
lean_ctor_set(x_1439, 1, x_1448);
lean_ctor_set(x_1439, 0, x_1450);
return x_1439;
}
}
else
{
lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; 
x_1451 = lean_ctor_get(x_1439, 0);
x_1452 = lean_ctor_get(x_1439, 1);
lean_inc(x_1452);
lean_inc(x_1451);
lean_dec(x_1439);
x_1453 = l_Lean_Elab_Term_SavedState_restore(x_1402, x_9, x_10, x_11, x_12, x_13, x_14, x_1452);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1454 = lean_ctor_get(x_1453, 1);
lean_inc(x_1454);
if (lean_is_exclusive(x_1453)) {
 lean_ctor_release(x_1453, 0);
 lean_ctor_release(x_1453, 1);
 x_1455 = x_1453;
} else {
 lean_dec_ref(x_1453);
 x_1455 = lean_box(0);
}
if (lean_is_scalar(x_1455)) {
 x_1456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1456 = x_1455;
}
lean_ctor_set(x_1456, 0, x_1437);
lean_ctor_set(x_1456, 1, x_1451);
x_1457 = lean_array_push(x_8, x_1456);
x_1458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1458, 0, x_1457);
lean_ctor_set(x_1458, 1, x_1454);
return x_1458;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_7 == 0)
{
lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; uint8_t x_1513; lean_object* x_1514; 
x_1477 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1478 = lean_ctor_get(x_1477, 0);
lean_inc(x_1478);
x_1479 = lean_ctor_get(x_1477, 1);
lean_inc(x_1479);
if (lean_is_exclusive(x_1477)) {
 lean_ctor_release(x_1477, 0);
 lean_ctor_release(x_1477, 1);
 x_1480 = x_1477;
} else {
 lean_dec_ref(x_1477);
 x_1480 = lean_box(0);
}
x_1513 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1514 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_1513, x_9, x_10, x_11, x_12, x_13, x_14, x_1479);
if (lean_obj_tag(x_1514) == 0)
{
lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; uint8_t x_1518; 
lean_dec(x_1480);
x_1515 = lean_ctor_get(x_1514, 0);
lean_inc(x_1515);
x_1516 = lean_ctor_get(x_1514, 1);
lean_inc(x_1516);
lean_dec(x_1514);
x_1517 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1516);
x_1518 = !lean_is_exclusive(x_1517);
if (x_1518 == 0)
{
lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; uint8_t x_1522; 
x_1519 = lean_ctor_get(x_1517, 0);
x_1520 = lean_ctor_get(x_1517, 1);
x_1521 = l_Lean_Elab_Term_SavedState_restore(x_1478, x_9, x_10, x_11, x_12, x_13, x_14, x_1520);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1522 = !lean_is_exclusive(x_1521);
if (x_1522 == 0)
{
lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; 
x_1523 = lean_ctor_get(x_1521, 1);
x_1524 = lean_ctor_get(x_1521, 0);
lean_dec(x_1524);
lean_ctor_set(x_1521, 1, x_1519);
lean_ctor_set(x_1521, 0, x_1515);
x_1525 = lean_array_push(x_8, x_1521);
lean_ctor_set(x_1517, 1, x_1523);
lean_ctor_set(x_1517, 0, x_1525);
return x_1517;
}
else
{
lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; 
x_1526 = lean_ctor_get(x_1521, 1);
lean_inc(x_1526);
lean_dec(x_1521);
x_1527 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1527, 0, x_1515);
lean_ctor_set(x_1527, 1, x_1519);
x_1528 = lean_array_push(x_8, x_1527);
lean_ctor_set(x_1517, 1, x_1526);
lean_ctor_set(x_1517, 0, x_1528);
return x_1517;
}
}
else
{
lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; 
x_1529 = lean_ctor_get(x_1517, 0);
x_1530 = lean_ctor_get(x_1517, 1);
lean_inc(x_1530);
lean_inc(x_1529);
lean_dec(x_1517);
x_1531 = l_Lean_Elab_Term_SavedState_restore(x_1478, x_9, x_10, x_11, x_12, x_13, x_14, x_1530);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1532 = lean_ctor_get(x_1531, 1);
lean_inc(x_1532);
if (lean_is_exclusive(x_1531)) {
 lean_ctor_release(x_1531, 0);
 lean_ctor_release(x_1531, 1);
 x_1533 = x_1531;
} else {
 lean_dec_ref(x_1531);
 x_1533 = lean_box(0);
}
if (lean_is_scalar(x_1533)) {
 x_1534 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1534 = x_1533;
}
lean_ctor_set(x_1534, 0, x_1515);
lean_ctor_set(x_1534, 1, x_1529);
x_1535 = lean_array_push(x_8, x_1534);
x_1536 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1536, 0, x_1535);
lean_ctor_set(x_1536, 1, x_1532);
return x_1536;
}
}
else
{
lean_object* x_1537; lean_object* x_1538; 
x_1537 = lean_ctor_get(x_1514, 0);
lean_inc(x_1537);
x_1538 = lean_ctor_get(x_1514, 1);
lean_inc(x_1538);
lean_dec(x_1514);
x_1481 = x_1537;
x_1482 = x_1538;
goto block_1512;
}
block_1512:
{
if (lean_obj_tag(x_1481) == 0)
{
lean_object* x_1483; uint8_t x_1484; 
lean_dec(x_1480);
x_1483 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1482);
x_1484 = !lean_is_exclusive(x_1483);
if (x_1484 == 0)
{
lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; uint8_t x_1488; 
x_1485 = lean_ctor_get(x_1483, 0);
x_1486 = lean_ctor_get(x_1483, 1);
x_1487 = l_Lean_Elab_Term_SavedState_restore(x_1478, x_9, x_10, x_11, x_12, x_13, x_14, x_1486);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1488 = !lean_is_exclusive(x_1487);
if (x_1488 == 0)
{
lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; 
x_1489 = lean_ctor_get(x_1487, 1);
x_1490 = lean_ctor_get(x_1487, 0);
lean_dec(x_1490);
lean_ctor_set_tag(x_1487, 1);
lean_ctor_set(x_1487, 1, x_1485);
lean_ctor_set(x_1487, 0, x_1481);
x_1491 = lean_array_push(x_8, x_1487);
lean_ctor_set(x_1483, 1, x_1489);
lean_ctor_set(x_1483, 0, x_1491);
return x_1483;
}
else
{
lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; 
x_1492 = lean_ctor_get(x_1487, 1);
lean_inc(x_1492);
lean_dec(x_1487);
x_1493 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1493, 0, x_1481);
lean_ctor_set(x_1493, 1, x_1485);
x_1494 = lean_array_push(x_8, x_1493);
lean_ctor_set(x_1483, 1, x_1492);
lean_ctor_set(x_1483, 0, x_1494);
return x_1483;
}
}
else
{
lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; 
x_1495 = lean_ctor_get(x_1483, 0);
x_1496 = lean_ctor_get(x_1483, 1);
lean_inc(x_1496);
lean_inc(x_1495);
lean_dec(x_1483);
x_1497 = l_Lean_Elab_Term_SavedState_restore(x_1478, x_9, x_10, x_11, x_12, x_13, x_14, x_1496);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1498 = lean_ctor_get(x_1497, 1);
lean_inc(x_1498);
if (lean_is_exclusive(x_1497)) {
 lean_ctor_release(x_1497, 0);
 lean_ctor_release(x_1497, 1);
 x_1499 = x_1497;
} else {
 lean_dec_ref(x_1497);
 x_1499 = lean_box(0);
}
if (lean_is_scalar(x_1499)) {
 x_1500 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1500 = x_1499;
 lean_ctor_set_tag(x_1500, 1);
}
lean_ctor_set(x_1500, 0, x_1481);
lean_ctor_set(x_1500, 1, x_1495);
x_1501 = lean_array_push(x_8, x_1500);
x_1502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1502, 0, x_1501);
lean_ctor_set(x_1502, 1, x_1498);
return x_1502;
}
}
else
{
lean_object* x_1503; lean_object* x_1504; uint8_t x_1505; 
lean_dec(x_8);
x_1503 = lean_ctor_get(x_1481, 0);
lean_inc(x_1503);
x_1504 = l_Lean_Elab_postponeExceptionId;
x_1505 = lean_nat_dec_eq(x_1503, x_1504);
lean_dec(x_1503);
if (x_1505 == 0)
{
lean_object* x_1506; 
lean_dec(x_1478);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1480)) {
 x_1506 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1506 = x_1480;
 lean_ctor_set_tag(x_1506, 1);
}
lean_ctor_set(x_1506, 0, x_1481);
lean_ctor_set(x_1506, 1, x_1482);
return x_1506;
}
else
{
lean_object* x_1507; uint8_t x_1508; 
lean_dec(x_1480);
x_1507 = l_Lean_Elab_Term_SavedState_restore(x_1478, x_9, x_10, x_11, x_12, x_13, x_14, x_1482);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1508 = !lean_is_exclusive(x_1507);
if (x_1508 == 0)
{
lean_object* x_1509; 
x_1509 = lean_ctor_get(x_1507, 0);
lean_dec(x_1509);
lean_ctor_set_tag(x_1507, 1);
lean_ctor_set(x_1507, 0, x_1481);
return x_1507;
}
else
{
lean_object* x_1510; lean_object* x_1511; 
x_1510 = lean_ctor_get(x_1507, 1);
lean_inc(x_1510);
lean_dec(x_1507);
x_1511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1511, 0, x_1481);
lean_ctor_set(x_1511, 1, x_1510);
return x_1511;
}
}
}
}
}
else
{
lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1576; 
x_1539 = lean_box(0);
x_1540 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1541 = lean_ctor_get(x_1540, 0);
lean_inc(x_1541);
x_1542 = lean_ctor_get(x_1540, 1);
lean_inc(x_1542);
if (lean_is_exclusive(x_1540)) {
 lean_ctor_release(x_1540, 0);
 lean_ctor_release(x_1540, 1);
 x_1543 = x_1540;
} else {
 lean_dec_ref(x_1540);
 x_1543 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1576 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_1243, x_1539, x_9, x_10, x_11, x_12, x_13, x_14, x_1542);
if (lean_obj_tag(x_1576) == 0)
{
lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; uint8_t x_1580; 
lean_dec(x_1543);
x_1577 = lean_ctor_get(x_1576, 0);
lean_inc(x_1577);
x_1578 = lean_ctor_get(x_1576, 1);
lean_inc(x_1578);
lean_dec(x_1576);
x_1579 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1578);
x_1580 = !lean_is_exclusive(x_1579);
if (x_1580 == 0)
{
lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; uint8_t x_1584; 
x_1581 = lean_ctor_get(x_1579, 0);
x_1582 = lean_ctor_get(x_1579, 1);
x_1583 = l_Lean_Elab_Term_SavedState_restore(x_1541, x_9, x_10, x_11, x_12, x_13, x_14, x_1582);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1584 = !lean_is_exclusive(x_1583);
if (x_1584 == 0)
{
lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; 
x_1585 = lean_ctor_get(x_1583, 1);
x_1586 = lean_ctor_get(x_1583, 0);
lean_dec(x_1586);
lean_ctor_set(x_1583, 1, x_1581);
lean_ctor_set(x_1583, 0, x_1577);
x_1587 = lean_array_push(x_8, x_1583);
lean_ctor_set(x_1579, 1, x_1585);
lean_ctor_set(x_1579, 0, x_1587);
return x_1579;
}
else
{
lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; 
x_1588 = lean_ctor_get(x_1583, 1);
lean_inc(x_1588);
lean_dec(x_1583);
x_1589 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1589, 0, x_1577);
lean_ctor_set(x_1589, 1, x_1581);
x_1590 = lean_array_push(x_8, x_1589);
lean_ctor_set(x_1579, 1, x_1588);
lean_ctor_set(x_1579, 0, x_1590);
return x_1579;
}
}
else
{
lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; 
x_1591 = lean_ctor_get(x_1579, 0);
x_1592 = lean_ctor_get(x_1579, 1);
lean_inc(x_1592);
lean_inc(x_1591);
lean_dec(x_1579);
x_1593 = l_Lean_Elab_Term_SavedState_restore(x_1541, x_9, x_10, x_11, x_12, x_13, x_14, x_1592);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1594 = lean_ctor_get(x_1593, 1);
lean_inc(x_1594);
if (lean_is_exclusive(x_1593)) {
 lean_ctor_release(x_1593, 0);
 lean_ctor_release(x_1593, 1);
 x_1595 = x_1593;
} else {
 lean_dec_ref(x_1593);
 x_1595 = lean_box(0);
}
if (lean_is_scalar(x_1595)) {
 x_1596 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1596 = x_1595;
}
lean_ctor_set(x_1596, 0, x_1577);
lean_ctor_set(x_1596, 1, x_1591);
x_1597 = lean_array_push(x_8, x_1596);
x_1598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1598, 0, x_1597);
lean_ctor_set(x_1598, 1, x_1594);
return x_1598;
}
}
else
{
lean_object* x_1599; lean_object* x_1600; 
x_1599 = lean_ctor_get(x_1576, 0);
lean_inc(x_1599);
x_1600 = lean_ctor_get(x_1576, 1);
lean_inc(x_1600);
lean_dec(x_1576);
x_1544 = x_1599;
x_1545 = x_1600;
goto block_1575;
}
block_1575:
{
if (lean_obj_tag(x_1544) == 0)
{
lean_object* x_1546; uint8_t x_1547; 
lean_dec(x_1543);
x_1546 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1545);
x_1547 = !lean_is_exclusive(x_1546);
if (x_1547 == 0)
{
lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; uint8_t x_1551; 
x_1548 = lean_ctor_get(x_1546, 0);
x_1549 = lean_ctor_get(x_1546, 1);
x_1550 = l_Lean_Elab_Term_SavedState_restore(x_1541, x_9, x_10, x_11, x_12, x_13, x_14, x_1549);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1551 = !lean_is_exclusive(x_1550);
if (x_1551 == 0)
{
lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; 
x_1552 = lean_ctor_get(x_1550, 1);
x_1553 = lean_ctor_get(x_1550, 0);
lean_dec(x_1553);
lean_ctor_set_tag(x_1550, 1);
lean_ctor_set(x_1550, 1, x_1548);
lean_ctor_set(x_1550, 0, x_1544);
x_1554 = lean_array_push(x_8, x_1550);
lean_ctor_set(x_1546, 1, x_1552);
lean_ctor_set(x_1546, 0, x_1554);
return x_1546;
}
else
{
lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; 
x_1555 = lean_ctor_get(x_1550, 1);
lean_inc(x_1555);
lean_dec(x_1550);
x_1556 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1556, 0, x_1544);
lean_ctor_set(x_1556, 1, x_1548);
x_1557 = lean_array_push(x_8, x_1556);
lean_ctor_set(x_1546, 1, x_1555);
lean_ctor_set(x_1546, 0, x_1557);
return x_1546;
}
}
else
{
lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; 
x_1558 = lean_ctor_get(x_1546, 0);
x_1559 = lean_ctor_get(x_1546, 1);
lean_inc(x_1559);
lean_inc(x_1558);
lean_dec(x_1546);
x_1560 = l_Lean_Elab_Term_SavedState_restore(x_1541, x_9, x_10, x_11, x_12, x_13, x_14, x_1559);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1561 = lean_ctor_get(x_1560, 1);
lean_inc(x_1561);
if (lean_is_exclusive(x_1560)) {
 lean_ctor_release(x_1560, 0);
 lean_ctor_release(x_1560, 1);
 x_1562 = x_1560;
} else {
 lean_dec_ref(x_1560);
 x_1562 = lean_box(0);
}
if (lean_is_scalar(x_1562)) {
 x_1563 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1563 = x_1562;
 lean_ctor_set_tag(x_1563, 1);
}
lean_ctor_set(x_1563, 0, x_1544);
lean_ctor_set(x_1563, 1, x_1558);
x_1564 = lean_array_push(x_8, x_1563);
x_1565 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1565, 0, x_1564);
lean_ctor_set(x_1565, 1, x_1561);
return x_1565;
}
}
else
{
lean_object* x_1566; lean_object* x_1567; uint8_t x_1568; 
lean_dec(x_8);
x_1566 = lean_ctor_get(x_1544, 0);
lean_inc(x_1566);
x_1567 = l_Lean_Elab_postponeExceptionId;
x_1568 = lean_nat_dec_eq(x_1566, x_1567);
lean_dec(x_1566);
if (x_1568 == 0)
{
lean_object* x_1569; 
lean_dec(x_1541);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1543)) {
 x_1569 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1569 = x_1543;
 lean_ctor_set_tag(x_1569, 1);
}
lean_ctor_set(x_1569, 0, x_1544);
lean_ctor_set(x_1569, 1, x_1545);
return x_1569;
}
else
{
lean_object* x_1570; uint8_t x_1571; 
lean_dec(x_1543);
x_1570 = l_Lean_Elab_Term_SavedState_restore(x_1541, x_9, x_10, x_11, x_12, x_13, x_14, x_1545);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1571 = !lean_is_exclusive(x_1570);
if (x_1571 == 0)
{
lean_object* x_1572; 
x_1572 = lean_ctor_get(x_1570, 0);
lean_dec(x_1572);
lean_ctor_set_tag(x_1570, 1);
lean_ctor_set(x_1570, 0, x_1544);
return x_1570;
}
else
{
lean_object* x_1573; lean_object* x_1574; 
x_1573 = lean_ctor_get(x_1570, 1);
lean_inc(x_1573);
lean_dec(x_1570);
x_1574 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1574, 0, x_1544);
lean_ctor_set(x_1574, 1, x_1573);
return x_1574;
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
lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; 
lean_dec(x_1);
x_1604 = l_Lean_Syntax_getId(x_1237);
lean_dec(x_1237);
x_1605 = l_Lean_Name_eraseMacroScopes(x_1604);
lean_dec(x_1604);
x_1606 = l_Lean_Name_components(x_1605);
x_1607 = l_List_map___main___at___private_Lean_Elab_App_33__elabAppFn___main___spec__1(x_1606);
x_1608 = l_List_append___rarg(x_1607, x_2);
x_1 = x_1235;
x_2 = x_1608;
goto _start;
}
}
else
{
lean_object* x_1610; lean_object* x_1611; 
lean_dec(x_1);
x_1610 = l_Lean_fieldIdxKind;
x_1611 = l_Lean_Syntax_isNatLitAux(x_1610, x_1237);
lean_dec(x_1237);
if (lean_obj_tag(x_1611) == 0)
{
lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; 
x_1612 = l_Nat_Inhabited;
x_1613 = l_Option_get_x21___rarg___closed__3;
x_1614 = lean_panic_fn(x_1612, x_1613);
x_1615 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1615, 0, x_1614);
x_1616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1616, 0, x_1615);
lean_ctor_set(x_1616, 1, x_2);
x_1 = x_1235;
x_2 = x_1616;
goto _start;
}
else
{
lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; 
x_1618 = lean_ctor_get(x_1611, 0);
lean_inc(x_1618);
lean_dec(x_1611);
x_1619 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1619, 0, x_1618);
x_1620 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1620, 0, x_1619);
lean_ctor_set(x_1620, 1, x_2);
x_1 = x_1235;
x_2 = x_1620;
goto _start;
}
}
}
}
}
else
{
lean_object* x_1630; uint8_t x_1631; 
x_1630 = l_Lean_Syntax_getArgs(x_1);
x_1631 = !lean_is_exclusive(x_9);
if (x_1631 == 0)
{
uint8_t x_1632; lean_object* x_1633; lean_object* x_1634; 
x_1632 = 0;
lean_ctor_set_uint8(x_9, sizeof(void*)*8 + 1, x_1632);
x_1633 = lean_unsigned_to_nat(0u);
x_1634 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_33__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_1630, x_1633, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1630);
lean_dec(x_1);
return x_1634;
}
else
{
lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; uint8_t x_1643; uint8_t x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; 
x_1635 = lean_ctor_get(x_9, 0);
x_1636 = lean_ctor_get(x_9, 1);
x_1637 = lean_ctor_get(x_9, 2);
x_1638 = lean_ctor_get(x_9, 3);
x_1639 = lean_ctor_get(x_9, 4);
x_1640 = lean_ctor_get(x_9, 5);
x_1641 = lean_ctor_get(x_9, 6);
x_1642 = lean_ctor_get(x_9, 7);
x_1643 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
lean_inc(x_1642);
lean_inc(x_1641);
lean_inc(x_1640);
lean_inc(x_1639);
lean_inc(x_1638);
lean_inc(x_1637);
lean_inc(x_1636);
lean_inc(x_1635);
lean_dec(x_9);
x_1644 = 0;
x_1645 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1645, 0, x_1635);
lean_ctor_set(x_1645, 1, x_1636);
lean_ctor_set(x_1645, 2, x_1637);
lean_ctor_set(x_1645, 3, x_1638);
lean_ctor_set(x_1645, 4, x_1639);
lean_ctor_set(x_1645, 5, x_1640);
lean_ctor_set(x_1645, 6, x_1641);
lean_ctor_set(x_1645, 7, x_1642);
lean_ctor_set_uint8(x_1645, sizeof(void*)*8, x_1643);
lean_ctor_set_uint8(x_1645, sizeof(void*)*8 + 1, x_1644);
x_1646 = lean_unsigned_to_nat(0u);
x_1647 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_33__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_1630, x_1646, x_8, x_1645, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1630);
lean_dec(x_1);
return x_1647;
}
}
block_381:
{
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; 
x_17 = l_List_isEmpty___rarg(x_2);
if (x_7 == 0)
{
uint8_t x_377; 
x_377 = 1;
x_18 = x_377;
goto block_376;
}
else
{
uint8_t x_378; 
x_378 = 0;
x_18 = x_378;
goto block_376;
}
block_376:
{
if (x_17 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_56; lean_object* x_57; lean_object* x_79; 
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_79 = l_Lean_Elab_Term_elabTerm(x_1, x_19, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_22);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_82 = l___private_Lean_Elab_App_31__elabAppLVals(x_80, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_81);
if (lean_obj_tag(x_82) == 0)
{
if (x_7 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_23);
lean_dec(x_5);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_56 = x_83;
x_57 = x_84;
goto block_78;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_87 = l_Lean_Elab_Term_ensureHasType(x_5, x_85, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_23);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_56 = x_88;
x_57 = x_89;
goto block_78;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_dec(x_87);
x_24 = x_90;
x_25 = x_91;
goto block_55;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_5);
x_92 = lean_ctor_get(x_82, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_82, 1);
lean_inc(x_93);
lean_dec(x_82);
x_24 = x_92;
x_25 = x_93;
goto block_55;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = lean_ctor_get(x_79, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_79, 1);
lean_inc(x_95);
lean_dec(x_79);
x_24 = x_94;
x_25 = x_95;
goto block_55;
}
block_55:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_23);
x_26 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = l_Lean_Elab_Term_SavedState_restore(x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_29);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 1);
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 0, x_24);
x_34 = lean_array_push(x_8, x_30);
lean_ctor_set(x_26, 1, x_32);
lean_ctor_set(x_26, 0, x_34);
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_28);
x_37 = lean_array_push(x_8, x_36);
lean_ctor_set(x_26, 1, x_35);
lean_ctor_set(x_26, 0, x_37);
return x_26;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_26);
x_40 = l_Lean_Elab_Term_SavedState_restore(x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_39);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
 lean_ctor_set_tag(x_43, 1);
}
lean_ctor_set(x_43, 0, x_24);
lean_ctor_set(x_43, 1, x_38);
x_44 = lean_array_push(x_8, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_8);
x_46 = lean_ctor_get(x_24, 0);
lean_inc(x_46);
x_47 = l_Lean_Elab_postponeExceptionId;
x_48 = lean_nat_dec_eq(x_46, x_47);
lean_dec(x_46);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_23)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_23;
 lean_ctor_set_tag(x_49, 1);
}
lean_ctor_set(x_49, 0, x_24);
lean_ctor_set(x_49, 1, x_25);
return x_49;
}
else
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_23);
x_50 = l_Lean_Elab_Term_SavedState_restore(x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set_tag(x_50, 1);
lean_ctor_set(x_50, 0, x_24);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_24);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
block_78:
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_57);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
x_62 = l_Lean_Elab_Term_SavedState_restore(x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_61);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_62, 1);
x_65 = lean_ctor_get(x_62, 0);
lean_dec(x_65);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_62, 0, x_56);
x_66 = lean_array_push(x_8, x_62);
lean_ctor_set(x_58, 1, x_64);
lean_ctor_set(x_58, 0, x_66);
return x_58;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_dec(x_62);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_56);
lean_ctor_set(x_68, 1, x_60);
x_69 = lean_array_push(x_8, x_68);
lean_ctor_set(x_58, 1, x_67);
lean_ctor_set(x_58, 0, x_69);
return x_58;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_58, 0);
x_71 = lean_ctor_get(x_58, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_58);
x_72 = l_Lean_Elab_Term_SavedState_restore(x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_71);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_74 = x_72;
} else {
 lean_dec_ref(x_72);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_56);
lean_ctor_set(x_75, 1, x_70);
x_76 = lean_array_push(x_8, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
return x_77;
}
}
}
else
{
uint8_t x_96; 
x_96 = l_Array_isEmpty___rarg(x_3);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_134; lean_object* x_135; lean_object* x_157; 
x_97 = lean_box(0);
x_98 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
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
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_157 = l_Lean_Elab_Term_elabTerm(x_1, x_97, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_100);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_160 = l___private_Lean_Elab_App_31__elabAppLVals(x_158, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_159);
if (lean_obj_tag(x_160) == 0)
{
if (x_7 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_101);
lean_dec(x_5);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_134 = x_161;
x_135 = x_162;
goto block_156;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_160, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
lean_dec(x_160);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_165 = l_Lean_Elab_Term_ensureHasType(x_5, x_163, x_97, x_9, x_10, x_11, x_12, x_13, x_14, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_101);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_134 = x_166;
x_135 = x_167;
goto block_156;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_165, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_165, 1);
lean_inc(x_169);
lean_dec(x_165);
x_102 = x_168;
x_103 = x_169;
goto block_133;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_5);
x_170 = lean_ctor_get(x_160, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_160, 1);
lean_inc(x_171);
lean_dec(x_160);
x_102 = x_170;
x_103 = x_171;
goto block_133;
}
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_172 = lean_ctor_get(x_157, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_157, 1);
lean_inc(x_173);
lean_dec(x_157);
x_102 = x_172;
x_103 = x_173;
goto block_133;
}
block_133:
{
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_104; uint8_t x_105; 
lean_dec(x_101);
x_104 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_103);
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = lean_ctor_get(x_104, 0);
x_107 = lean_ctor_get(x_104, 1);
x_108 = l_Lean_Elab_Term_SavedState_restore(x_99, x_9, x_10, x_11, x_12, x_13, x_14, x_107);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_108, 1);
x_111 = lean_ctor_get(x_108, 0);
lean_dec(x_111);
lean_ctor_set_tag(x_108, 1);
lean_ctor_set(x_108, 1, x_106);
lean_ctor_set(x_108, 0, x_102);
x_112 = lean_array_push(x_8, x_108);
lean_ctor_set(x_104, 1, x_110);
lean_ctor_set(x_104, 0, x_112);
return x_104;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_dec(x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_102);
lean_ctor_set(x_114, 1, x_106);
x_115 = lean_array_push(x_8, x_114);
lean_ctor_set(x_104, 1, x_113);
lean_ctor_set(x_104, 0, x_115);
return x_104;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_116 = lean_ctor_get(x_104, 0);
x_117 = lean_ctor_get(x_104, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_104);
x_118 = l_Lean_Elab_Term_SavedState_restore(x_99, x_9, x_10, x_11, x_12, x_13, x_14, x_117);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
 lean_ctor_set_tag(x_121, 1);
}
lean_ctor_set(x_121, 0, x_102);
lean_ctor_set(x_121, 1, x_116);
x_122 = lean_array_push(x_8, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_119);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_8);
x_124 = lean_ctor_get(x_102, 0);
lean_inc(x_124);
x_125 = l_Lean_Elab_postponeExceptionId;
x_126 = lean_nat_dec_eq(x_124, x_125);
lean_dec(x_124);
if (x_126 == 0)
{
lean_object* x_127; 
lean_dec(x_99);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_101)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_101;
 lean_ctor_set_tag(x_127, 1);
}
lean_ctor_set(x_127, 0, x_102);
lean_ctor_set(x_127, 1, x_103);
return x_127;
}
else
{
lean_object* x_128; uint8_t x_129; 
lean_dec(x_101);
x_128 = l_Lean_Elab_Term_SavedState_restore(x_99, x_9, x_10, x_11, x_12, x_13, x_14, x_103);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_128, 0);
lean_dec(x_130);
lean_ctor_set_tag(x_128, 1);
lean_ctor_set(x_128, 0, x_102);
return x_128;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_102);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
block_156:
{
lean_object* x_136; uint8_t x_137; 
x_136 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_135);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_ctor_get(x_136, 1);
x_140 = l_Lean_Elab_Term_SavedState_restore(x_99, x_9, x_10, x_11, x_12, x_13, x_14, x_139);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_140, 1);
x_143 = lean_ctor_get(x_140, 0);
lean_dec(x_143);
lean_ctor_set(x_140, 1, x_138);
lean_ctor_set(x_140, 0, x_134);
x_144 = lean_array_push(x_8, x_140);
lean_ctor_set(x_136, 1, x_142);
lean_ctor_set(x_136, 0, x_144);
return x_136;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_140, 1);
lean_inc(x_145);
lean_dec(x_140);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_134);
lean_ctor_set(x_146, 1, x_138);
x_147 = lean_array_push(x_8, x_146);
lean_ctor_set(x_136, 1, x_145);
lean_ctor_set(x_136, 0, x_147);
return x_136;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_148 = lean_ctor_get(x_136, 0);
x_149 = lean_ctor_get(x_136, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_136);
x_150 = l_Lean_Elab_Term_SavedState_restore(x_99, x_9, x_10, x_11, x_12, x_13, x_14, x_149);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_134);
lean_ctor_set(x_153, 1, x_148);
x_154 = lean_array_push(x_8, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_151);
return x_155;
}
}
}
else
{
uint8_t x_174; 
x_174 = l_Array_isEmpty___rarg(x_4);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_212; lean_object* x_213; lean_object* x_235; 
x_175 = lean_box(0);
x_176 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
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
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_235 = l_Lean_Elab_Term_elabTerm(x_1, x_175, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_178);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_238 = l___private_Lean_Elab_App_31__elabAppLVals(x_236, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_237);
if (lean_obj_tag(x_238) == 0)
{
if (x_7 == 0)
{
lean_object* x_239; lean_object* x_240; 
lean_dec(x_179);
lean_dec(x_5);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_212 = x_239;
x_213 = x_240;
goto block_234;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_238, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_238, 1);
lean_inc(x_242);
lean_dec(x_238);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_243 = l_Lean_Elab_Term_ensureHasType(x_5, x_241, x_175, x_9, x_10, x_11, x_12, x_13, x_14, x_242);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; 
lean_dec(x_179);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_212 = x_244;
x_213 = x_245;
goto block_234;
}
else
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_243, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_243, 1);
lean_inc(x_247);
lean_dec(x_243);
x_180 = x_246;
x_181 = x_247;
goto block_211;
}
}
}
else
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_5);
x_248 = lean_ctor_get(x_238, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_238, 1);
lean_inc(x_249);
lean_dec(x_238);
x_180 = x_248;
x_181 = x_249;
goto block_211;
}
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_250 = lean_ctor_get(x_235, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_235, 1);
lean_inc(x_251);
lean_dec(x_235);
x_180 = x_250;
x_181 = x_251;
goto block_211;
}
block_211:
{
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_182; uint8_t x_183; 
lean_dec(x_179);
x_182 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_181);
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_184 = lean_ctor_get(x_182, 0);
x_185 = lean_ctor_get(x_182, 1);
x_186 = l_Lean_Elab_Term_SavedState_restore(x_177, x_9, x_10, x_11, x_12, x_13, x_14, x_185);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_186, 1);
x_189 = lean_ctor_get(x_186, 0);
lean_dec(x_189);
lean_ctor_set_tag(x_186, 1);
lean_ctor_set(x_186, 1, x_184);
lean_ctor_set(x_186, 0, x_180);
x_190 = lean_array_push(x_8, x_186);
lean_ctor_set(x_182, 1, x_188);
lean_ctor_set(x_182, 0, x_190);
return x_182;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_186, 1);
lean_inc(x_191);
lean_dec(x_186);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_180);
lean_ctor_set(x_192, 1, x_184);
x_193 = lean_array_push(x_8, x_192);
lean_ctor_set(x_182, 1, x_191);
lean_ctor_set(x_182, 0, x_193);
return x_182;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_194 = lean_ctor_get(x_182, 0);
x_195 = lean_ctor_get(x_182, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_182);
x_196 = l_Lean_Elab_Term_SavedState_restore(x_177, x_9, x_10, x_11, x_12, x_13, x_14, x_195);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
 lean_ctor_set_tag(x_199, 1);
}
lean_ctor_set(x_199, 0, x_180);
lean_ctor_set(x_199, 1, x_194);
x_200 = lean_array_push(x_8, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_197);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; 
lean_dec(x_8);
x_202 = lean_ctor_get(x_180, 0);
lean_inc(x_202);
x_203 = l_Lean_Elab_postponeExceptionId;
x_204 = lean_nat_dec_eq(x_202, x_203);
lean_dec(x_202);
if (x_204 == 0)
{
lean_object* x_205; 
lean_dec(x_177);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_179)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_179;
 lean_ctor_set_tag(x_205, 1);
}
lean_ctor_set(x_205, 0, x_180);
lean_ctor_set(x_205, 1, x_181);
return x_205;
}
else
{
lean_object* x_206; uint8_t x_207; 
lean_dec(x_179);
x_206 = l_Lean_Elab_Term_SavedState_restore(x_177, x_9, x_10, x_11, x_12, x_13, x_14, x_181);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_207 = !lean_is_exclusive(x_206);
if (x_207 == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_206, 0);
lean_dec(x_208);
lean_ctor_set_tag(x_206, 1);
lean_ctor_set(x_206, 0, x_180);
return x_206;
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
lean_dec(x_206);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_180);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
}
block_234:
{
lean_object* x_214; uint8_t x_215; 
x_214 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_213);
x_215 = !lean_is_exclusive(x_214);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_216 = lean_ctor_get(x_214, 0);
x_217 = lean_ctor_get(x_214, 1);
x_218 = l_Lean_Elab_Term_SavedState_restore(x_177, x_9, x_10, x_11, x_12, x_13, x_14, x_217);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_219 = !lean_is_exclusive(x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_218, 1);
x_221 = lean_ctor_get(x_218, 0);
lean_dec(x_221);
lean_ctor_set(x_218, 1, x_216);
lean_ctor_set(x_218, 0, x_212);
x_222 = lean_array_push(x_8, x_218);
lean_ctor_set(x_214, 1, x_220);
lean_ctor_set(x_214, 0, x_222);
return x_214;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_218, 1);
lean_inc(x_223);
lean_dec(x_218);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_212);
lean_ctor_set(x_224, 1, x_216);
x_225 = lean_array_push(x_8, x_224);
lean_ctor_set(x_214, 1, x_223);
lean_ctor_set(x_214, 0, x_225);
return x_214;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_226 = lean_ctor_get(x_214, 0);
x_227 = lean_ctor_get(x_214, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_214);
x_228 = l_Lean_Elab_Term_SavedState_restore(x_177, x_9, x_10, x_11, x_12, x_13, x_14, x_227);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_230 = x_228;
} else {
 lean_dec_ref(x_228);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_212);
lean_ctor_set(x_231, 1, x_226);
x_232 = lean_array_push(x_8, x_231);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_229);
return x_233;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_7 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_288; lean_object* x_289; 
x_252 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_255 = x_252;
} else {
 lean_dec_ref(x_252);
 x_255 = lean_box(0);
}
x_288 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_289 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_288, x_9, x_10, x_11, x_12, x_13, x_14, x_254);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
lean_dec(x_255);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec(x_289);
x_292 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_291);
x_293 = !lean_is_exclusive(x_292);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_294 = lean_ctor_get(x_292, 0);
x_295 = lean_ctor_get(x_292, 1);
x_296 = l_Lean_Elab_Term_SavedState_restore(x_253, x_9, x_10, x_11, x_12, x_13, x_14, x_295);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_297 = !lean_is_exclusive(x_296);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_296, 1);
x_299 = lean_ctor_get(x_296, 0);
lean_dec(x_299);
lean_ctor_set(x_296, 1, x_294);
lean_ctor_set(x_296, 0, x_290);
x_300 = lean_array_push(x_8, x_296);
lean_ctor_set(x_292, 1, x_298);
lean_ctor_set(x_292, 0, x_300);
return x_292;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_296, 1);
lean_inc(x_301);
lean_dec(x_296);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_290);
lean_ctor_set(x_302, 1, x_294);
x_303 = lean_array_push(x_8, x_302);
lean_ctor_set(x_292, 1, x_301);
lean_ctor_set(x_292, 0, x_303);
return x_292;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_304 = lean_ctor_get(x_292, 0);
x_305 = lean_ctor_get(x_292, 1);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_292);
x_306 = l_Lean_Elab_Term_SavedState_restore(x_253, x_9, x_10, x_11, x_12, x_13, x_14, x_305);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_307 = lean_ctor_get(x_306, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_308 = x_306;
} else {
 lean_dec_ref(x_306);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_290);
lean_ctor_set(x_309, 1, x_304);
x_310 = lean_array_push(x_8, x_309);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_307);
return x_311;
}
}
else
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_ctor_get(x_289, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_289, 1);
lean_inc(x_313);
lean_dec(x_289);
x_256 = x_312;
x_257 = x_313;
goto block_287;
}
block_287:
{
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_258; uint8_t x_259; 
lean_dec(x_255);
x_258 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_257);
x_259 = !lean_is_exclusive(x_258);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_260 = lean_ctor_get(x_258, 0);
x_261 = lean_ctor_get(x_258, 1);
x_262 = l_Lean_Elab_Term_SavedState_restore(x_253, x_9, x_10, x_11, x_12, x_13, x_14, x_261);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_262, 1);
x_265 = lean_ctor_get(x_262, 0);
lean_dec(x_265);
lean_ctor_set_tag(x_262, 1);
lean_ctor_set(x_262, 1, x_260);
lean_ctor_set(x_262, 0, x_256);
x_266 = lean_array_push(x_8, x_262);
lean_ctor_set(x_258, 1, x_264);
lean_ctor_set(x_258, 0, x_266);
return x_258;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_262, 1);
lean_inc(x_267);
lean_dec(x_262);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_256);
lean_ctor_set(x_268, 1, x_260);
x_269 = lean_array_push(x_8, x_268);
lean_ctor_set(x_258, 1, x_267);
lean_ctor_set(x_258, 0, x_269);
return x_258;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_270 = lean_ctor_get(x_258, 0);
x_271 = lean_ctor_get(x_258, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_258);
x_272 = l_Lean_Elab_Term_SavedState_restore(x_253, x_9, x_10, x_11, x_12, x_13, x_14, x_271);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_274 = x_272;
} else {
 lean_dec_ref(x_272);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
 lean_ctor_set_tag(x_275, 1);
}
lean_ctor_set(x_275, 0, x_256);
lean_ctor_set(x_275, 1, x_270);
x_276 = lean_array_push(x_8, x_275);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_273);
return x_277;
}
}
else
{
lean_object* x_278; lean_object* x_279; uint8_t x_280; 
lean_dec(x_8);
x_278 = lean_ctor_get(x_256, 0);
lean_inc(x_278);
x_279 = l_Lean_Elab_postponeExceptionId;
x_280 = lean_nat_dec_eq(x_278, x_279);
lean_dec(x_278);
if (x_280 == 0)
{
lean_object* x_281; 
lean_dec(x_253);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_255)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_255;
 lean_ctor_set_tag(x_281, 1);
}
lean_ctor_set(x_281, 0, x_256);
lean_ctor_set(x_281, 1, x_257);
return x_281;
}
else
{
lean_object* x_282; uint8_t x_283; 
lean_dec(x_255);
x_282 = l_Lean_Elab_Term_SavedState_restore(x_253, x_9, x_10, x_11, x_12, x_13, x_14, x_257);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_283 = !lean_is_exclusive(x_282);
if (x_283 == 0)
{
lean_object* x_284; 
x_284 = lean_ctor_get(x_282, 0);
lean_dec(x_284);
lean_ctor_set_tag(x_282, 1);
lean_ctor_set(x_282, 0, x_256);
return x_282;
}
else
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_282, 1);
lean_inc(x_285);
lean_dec(x_282);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_256);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_351; 
x_314 = lean_box(0);
x_315 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_318 = x_315;
} else {
 lean_dec_ref(x_315);
 x_318 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_351 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_18, x_314, x_9, x_10, x_11, x_12, x_13, x_14, x_317);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; 
lean_dec(x_318);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_353);
x_355 = !lean_is_exclusive(x_354);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; 
x_356 = lean_ctor_get(x_354, 0);
x_357 = lean_ctor_get(x_354, 1);
x_358 = l_Lean_Elab_Term_SavedState_restore(x_316, x_9, x_10, x_11, x_12, x_13, x_14, x_357);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_359 = !lean_is_exclusive(x_358);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_358, 1);
x_361 = lean_ctor_get(x_358, 0);
lean_dec(x_361);
lean_ctor_set(x_358, 1, x_356);
lean_ctor_set(x_358, 0, x_352);
x_362 = lean_array_push(x_8, x_358);
lean_ctor_set(x_354, 1, x_360);
lean_ctor_set(x_354, 0, x_362);
return x_354;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_358, 1);
lean_inc(x_363);
lean_dec(x_358);
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_352);
lean_ctor_set(x_364, 1, x_356);
x_365 = lean_array_push(x_8, x_364);
lean_ctor_set(x_354, 1, x_363);
lean_ctor_set(x_354, 0, x_365);
return x_354;
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_366 = lean_ctor_get(x_354, 0);
x_367 = lean_ctor_get(x_354, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_354);
x_368 = l_Lean_Elab_Term_SavedState_restore(x_316, x_9, x_10, x_11, x_12, x_13, x_14, x_367);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_370 = x_368;
} else {
 lean_dec_ref(x_368);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_352);
lean_ctor_set(x_371, 1, x_366);
x_372 = lean_array_push(x_8, x_371);
x_373 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_369);
return x_373;
}
}
else
{
lean_object* x_374; lean_object* x_375; 
x_374 = lean_ctor_get(x_351, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_351, 1);
lean_inc(x_375);
lean_dec(x_351);
x_319 = x_374;
x_320 = x_375;
goto block_350;
}
block_350:
{
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_321; uint8_t x_322; 
lean_dec(x_318);
x_321 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_320);
x_322 = !lean_is_exclusive(x_321);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_323 = lean_ctor_get(x_321, 0);
x_324 = lean_ctor_get(x_321, 1);
x_325 = l_Lean_Elab_Term_SavedState_restore(x_316, x_9, x_10, x_11, x_12, x_13, x_14, x_324);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_326 = !lean_is_exclusive(x_325);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_325, 1);
x_328 = lean_ctor_get(x_325, 0);
lean_dec(x_328);
lean_ctor_set_tag(x_325, 1);
lean_ctor_set(x_325, 1, x_323);
lean_ctor_set(x_325, 0, x_319);
x_329 = lean_array_push(x_8, x_325);
lean_ctor_set(x_321, 1, x_327);
lean_ctor_set(x_321, 0, x_329);
return x_321;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_325, 1);
lean_inc(x_330);
lean_dec(x_325);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_319);
lean_ctor_set(x_331, 1, x_323);
x_332 = lean_array_push(x_8, x_331);
lean_ctor_set(x_321, 1, x_330);
lean_ctor_set(x_321, 0, x_332);
return x_321;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_333 = lean_ctor_get(x_321, 0);
x_334 = lean_ctor_get(x_321, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_321);
x_335 = l_Lean_Elab_Term_SavedState_restore(x_316, x_9, x_10, x_11, x_12, x_13, x_14, x_334);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_336 = lean_ctor_get(x_335, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_337 = x_335;
} else {
 lean_dec_ref(x_335);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_338 = x_337;
 lean_ctor_set_tag(x_338, 1);
}
lean_ctor_set(x_338, 0, x_319);
lean_ctor_set(x_338, 1, x_333);
x_339 = lean_array_push(x_8, x_338);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_336);
return x_340;
}
}
else
{
lean_object* x_341; lean_object* x_342; uint8_t x_343; 
lean_dec(x_8);
x_341 = lean_ctor_get(x_319, 0);
lean_inc(x_341);
x_342 = l_Lean_Elab_postponeExceptionId;
x_343 = lean_nat_dec_eq(x_341, x_342);
lean_dec(x_341);
if (x_343 == 0)
{
lean_object* x_344; 
lean_dec(x_316);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_318)) {
 x_344 = lean_alloc_ctor(1, 2, 0);
} else {
 x_344 = x_318;
 lean_ctor_set_tag(x_344, 1);
}
lean_ctor_set(x_344, 0, x_319);
lean_ctor_set(x_344, 1, x_320);
return x_344;
}
else
{
lean_object* x_345; uint8_t x_346; 
lean_dec(x_318);
x_345 = l_Lean_Elab_Term_SavedState_restore(x_316, x_9, x_10, x_11, x_12, x_13, x_14, x_320);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_346 = !lean_is_exclusive(x_345);
if (x_346 == 0)
{
lean_object* x_347; 
x_347 = lean_ctor_get(x_345, 0);
lean_dec(x_347);
lean_ctor_set_tag(x_345, 1);
lean_ctor_set(x_345, 0, x_319);
return x_345;
}
else
{
lean_object* x_348; lean_object* x_349; 
x_348 = lean_ctor_get(x_345, 1);
lean_inc(x_348);
lean_dec(x_345);
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_319);
lean_ctor_set(x_349, 1, x_348);
return x_349;
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
lean_object* x_379; lean_object* x_380; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_379 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__3;
x_380 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_379, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_380;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_33__elabAppFn___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_33__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_1);
return x_18;
}
}
lean_object* l___private_Lean_Elab_App_33__elabAppFn___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = l___private_Lean_Elab_App_33__elabAppFn___main(x_1, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
lean_object* l___private_Lean_Elab_App_33__elabAppFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_App_33__elabAppFn___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
lean_object* l___private_Lean_Elab_App_33__elabAppFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = l___private_Lean_Elab_App_33__elabAppFn(x_1, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
uint8_t l___private_Lean_Elab_App_34__isSuccess(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l___private_Lean_Elab_App_34__isSuccess___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_App_34__isSuccess(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_App_35__getSuccess___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = l_Array_shrink___main___rarg(x_1, x_3);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = l___private_Lean_Elab_App_34__isSuccess(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_2 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
lean_dec(x_2);
x_15 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_2 = x_14;
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_fswap(x_1, x_2, x_3);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
lean_dec(x_2);
x_20 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_1 = x_17;
x_2 = x_19;
x_3 = x_20;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_35__getSuccess(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_filterAux___main___at___private_Lean_Elab_App_35__getSuccess___spec__1(x_1, x_2, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_36__toMessageData___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = l_Lean_Syntax_getPos(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_36__toMessageData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_36__toMessageData___spec__1___rarg___boxed), 3, 0);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_App_36__toMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Syntax_6__formatInfo___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_36__toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_36__toMessageData___spec__1___rarg(x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_Exception_getRef(x_1);
x_13 = l_Lean_Syntax_getPos(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = l_Lean_Exception_toMessageData(x_1);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_nat_dec_eq(x_11, x_15);
lean_dec(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_17 = lean_ctor_get(x_2, 1);
x_18 = l_Lean_FileMap_toPosition(x_17, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = l_Nat_repr(x_19);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l___private_Lean_Elab_App_36__toMessageData___closed__1;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l_Nat_repr(x_25);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Exception_toMessageData(x_1);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_9, 0, x_33);
return x_9;
}
else
{
lean_object* x_34; 
lean_dec(x_15);
x_34 = l_Lean_Exception_toMessageData(x_1);
lean_ctor_set(x_9, 0, x_34);
return x_9;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_9, 0);
x_36 = lean_ctor_get(x_9, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_9);
x_37 = l_Lean_Exception_getRef(x_1);
x_38 = l_Lean_Syntax_getPos(x_37);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_35);
x_39 = l_Lean_Exception_toMessageData(x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_nat_dec_eq(x_35, x_41);
lean_dec(x_35);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_43 = lean_ctor_get(x_2, 1);
x_44 = l_Lean_FileMap_toPosition(x_43, x_41);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = l_Nat_repr(x_45);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l___private_Lean_Elab_App_36__toMessageData___closed__1;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_dec(x_44);
x_52 = l_Nat_repr(x_51);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Exception_toMessageData(x_1);
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_36);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
x_61 = l_Lean_Exception_toMessageData(x_1);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_36);
return x_62;
}
}
}
}
}
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_36__toMessageData___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_36__toMessageData___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_36__toMessageData___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_36__toMessageData___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_36__toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_36__toMessageData(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_37__toMessageList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Array_toList___rarg(x_1);
x_3 = l_Lean_Elab_goalsToMessageData___closed__1;
x_4 = l_Lean_MessageData_joinSep___main(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_indentD(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_37__toMessageList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_App_37__toMessageList(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_38__mergeFailures___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = x_2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_fget(x_2, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fset(x_2, x_1, x_15);
x_17 = x_14;
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
x_18 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_19 = l_unreachable_x21___rarg(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = lean_apply_7(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_1, x_23);
x_25 = x_21;
x_26 = lean_array_fset(x_16, x_1, x_25);
lean_dec(x_1);
x_1 = x_24;
x_2 = x_26;
x_9 = x_22;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = l___private_Lean_Elab_App_36__toMessageData(x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_1, x_36);
x_38 = x_34;
x_39 = lean_array_fset(x_16, x_1, x_38);
lean_dec(x_1);
x_1 = x_37;
x_2 = x_39;
x_9 = x_35;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("overloaded, errors ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_38__mergeFailures___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = x_1;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_App_38__mergeFailures___spec__1), 9, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
x_12 = x_11;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = lean_apply_7(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_App_37__toMessageList(x_14);
lean_dec(x_14);
x_17 = l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__3;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l___private_Lean_Elab_App_38__mergeFailures(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_38__mergeFailures___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_39__elabAppAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = x_4;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_fget(x_4, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_fset(x_4, x_3, x_9);
x_11 = x_8;
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_2);
lean_inc(x_1);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_1);
lean_ctor_set(x_20, 3, x_2);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_22 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = x_22;
x_24 = lean_array_fset(x_10, x_3, x_23);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
x_26 = l_Lean_MessageData_Inhabited;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = x_27;
x_29 = lean_array_fset(x_10, x_3, x_28);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_29;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_39__elabAppAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous, possible interpretations ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_39__elabAppAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_39__elabAppAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_39__elabAppAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_39__elabAppAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_39__elabAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_box(0);
x_13 = 0;
x_14 = l_Array_empty___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_15 = l___private_Lean_Elab_App_33__elabAppFn___main(x_1, x_12, x_2, x_3, x_4, x_13, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_get_size(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_unsigned_to_nat(0u);
lean_inc(x_16);
x_22 = l_Array_filterAux___main___at___private_Lean_Elab_App_35__getSuccess___spec__1(x_16, x_21, x_21);
x_23 = lean_array_get_size(x_22);
x_24 = lean_nat_dec_eq(x_23, x_19);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_nat_dec_lt(x_19, x_23);
lean_dec(x_23);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_22);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_9, 3);
x_28 = l_Lean_replaceRef(x_1, x_27);
lean_dec(x_1);
x_29 = l_Lean_replaceRef(x_28, x_27);
lean_dec(x_28);
x_30 = l_Lean_replaceRef(x_29, x_27);
lean_dec(x_27);
lean_dec(x_29);
lean_ctor_set(x_9, 3, x_30);
x_31 = l___private_Lean_Elab_App_38__mergeFailures___rarg(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
x_34 = lean_ctor_get(x_9, 2);
x_35 = lean_ctor_get(x_9, 3);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_36 = l_Lean_replaceRef(x_1, x_35);
lean_dec(x_1);
x_37 = l_Lean_replaceRef(x_36, x_35);
lean_dec(x_36);
x_38 = l_Lean_replaceRef(x_37, x_35);
lean_dec(x_35);
lean_dec(x_37);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_34);
lean_ctor_set(x_39, 3, x_38);
x_40 = l___private_Lean_Elab_App_38__mergeFailures___rarg(x_16, x_5, x_6, x_7, x_8, x_39, x_10, x_17);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_16);
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_9, 0);
lean_inc(x_42);
x_43 = x_22;
x_44 = l_Array_umapMAux___main___at___private_Lean_Elab_App_39__elabAppAux___spec__1(x_41, x_42, x_21, x_43);
x_45 = x_44;
x_46 = l___private_Lean_Elab_App_37__toMessageList(x_45);
lean_dec(x_45);
x_47 = l___private_Lean_Elab_App_39__elabAppAux___closed__3;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_1, x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_1);
x_50 = l_Lean_Elab_Term_TermElabResult_inhabited;
x_51 = lean_array_get(x_50, x_22, x_21);
lean_dec(x_22);
x_52 = l_Lean_Elab_Term_applyResult(x_51, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
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
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_52);
if (x_57 == 0)
{
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_1);
x_61 = l_Lean_Elab_Term_TermElabResult_inhabited;
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_array_get(x_61, x_16, x_62);
lean_dec(x_16);
x_64 = l_Lean_Elab_Term_applyResult(x_63, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_15);
if (x_65 == 0)
{
return x_15;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_15, 0);
x_67 = lean_ctor_get(x_15, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_15);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
static lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namedArgument");
return x_1;
}
}
static lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ellipsis");
return x_1;
}
}
static lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected '..'");
return x_1;
}
}
static lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_array_fget(x_2, x_3);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_21 = l_Lean_Syntax_getKind(x_15);
x_22 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
x_23 = lean_name_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
x_25 = lean_name_eq(x_21, x_24);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_15);
x_27 = lean_array_push(x_20, x_26);
lean_ctor_set(x_4, 1, x_27);
x_3 = x_17;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
x_29 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__7;
x_30 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_15, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_21);
x_35 = l_Lean_Syntax_getArg(x_15, x_16);
x_36 = l_Lean_Syntax_getId(x_35);
lean_dec(x_35);
x_37 = l_Lean_Name_eraseMacroScopes(x_36);
lean_dec(x_36);
x_38 = lean_unsigned_to_nat(3u);
x_39 = l_Lean_Syntax_getArg(x_15, x_38);
lean_dec(x_15);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_5);
x_42 = l_Lean_Elab_Term_addNamedArg(x_19, x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_ctor_set(x_4, 0, x_43);
x_3 = x_17;
x_11 = x_44;
goto _start;
}
else
{
uint8_t x_46; 
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_4, 0);
x_51 = lean_ctor_get(x_4, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_4);
lean_inc(x_15);
x_52 = l_Lean_Syntax_getKind(x_15);
x_53 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
x_54 = lean_name_eq(x_52, x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
x_56 = lean_name_eq(x_52, x_55);
lean_dec(x_52);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_15);
x_58 = lean_array_push(x_51, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_58);
x_3 = x_17;
x_4 = x_59;
goto _start;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_17);
x_61 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__7;
x_62 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_15, x_61, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_52);
x_67 = l_Lean_Syntax_getArg(x_15, x_16);
x_68 = l_Lean_Syntax_getId(x_67);
lean_dec(x_67);
x_69 = l_Lean_Name_eraseMacroScopes(x_68);
lean_dec(x_68);
x_70 = lean_unsigned_to_nat(3u);
x_71 = l_Lean_Syntax_getArg(x_15, x_70);
lean_dec(x_15);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_5);
x_74 = l_Lean_Elab_Term_addNamedArg(x_50, x_73, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_51);
x_3 = x_17;
x_4 = x_77;
x_11 = x_76;
goto _start;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_51);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_5);
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_81 = x_74;
} else {
 lean_dec_ref(x_74);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_array_fget(x_2, x_3);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_21 = l_Lean_Syntax_getKind(x_15);
x_22 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
x_23 = lean_name_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
x_25 = lean_name_eq(x_21, x_24);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_15);
x_27 = lean_array_push(x_20, x_26);
lean_ctor_set(x_4, 1, x_27);
x_3 = x_17;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
x_29 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__7;
x_30 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_15, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_21);
x_35 = l_Lean_Syntax_getArg(x_15, x_16);
x_36 = l_Lean_Syntax_getId(x_35);
lean_dec(x_35);
x_37 = l_Lean_Name_eraseMacroScopes(x_36);
lean_dec(x_36);
x_38 = lean_unsigned_to_nat(3u);
x_39 = l_Lean_Syntax_getArg(x_15, x_38);
lean_dec(x_15);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_5);
x_42 = l_Lean_Elab_Term_addNamedArg(x_19, x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_ctor_set(x_4, 0, x_43);
x_3 = x_17;
x_11 = x_44;
goto _start;
}
else
{
uint8_t x_46; 
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_4, 0);
x_51 = lean_ctor_get(x_4, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_4);
lean_inc(x_15);
x_52 = l_Lean_Syntax_getKind(x_15);
x_53 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
x_54 = lean_name_eq(x_52, x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
x_56 = lean_name_eq(x_52, x_55);
lean_dec(x_52);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_15);
x_58 = lean_array_push(x_51, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_58);
x_3 = x_17;
x_4 = x_59;
goto _start;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_17);
x_61 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__7;
x_62 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_15, x_61, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_52);
x_67 = l_Lean_Syntax_getArg(x_15, x_16);
x_68 = l_Lean_Syntax_getId(x_67);
lean_dec(x_67);
x_69 = l_Lean_Name_eraseMacroScopes(x_68);
lean_dec(x_68);
x_70 = lean_unsigned_to_nat(3u);
x_71 = l_Lean_Syntax_getArg(x_15, x_70);
lean_dec(x_15);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_5);
x_74 = l_Lean_Elab_Term_addNamedArg(x_50, x_73, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_51);
x_3 = x_17;
x_4 = x_77;
x_11 = x_76;
goto _start;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_51);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_5);
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_81 = x_74;
} else {
 lean_dec_ref(x_74);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_array_fget(x_2, x_3);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
x_21 = l_Lean_Syntax_getKind(x_15);
x_22 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
x_23 = lean_name_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
x_25 = lean_name_eq(x_21, x_24);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_15);
x_27 = lean_array_push(x_20, x_26);
lean_ctor_set(x_4, 1, x_27);
x_3 = x_17;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
x_29 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__7;
x_30 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_15, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_21);
x_35 = l_Lean_Syntax_getArg(x_15, x_16);
x_36 = l_Lean_Syntax_getId(x_35);
lean_dec(x_35);
x_37 = l_Lean_Name_eraseMacroScopes(x_36);
lean_dec(x_36);
x_38 = lean_unsigned_to_nat(3u);
x_39 = l_Lean_Syntax_getArg(x_15, x_38);
lean_dec(x_15);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_5);
x_42 = l_Lean_Elab_Term_addNamedArg(x_19, x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_ctor_set(x_4, 0, x_43);
x_3 = x_17;
x_11 = x_44;
goto _start;
}
else
{
uint8_t x_46; 
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_4, 0);
x_51 = lean_ctor_get(x_4, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_4);
lean_inc(x_15);
x_52 = l_Lean_Syntax_getKind(x_15);
x_53 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
x_54 = lean_name_eq(x_52, x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
x_56 = lean_name_eq(x_52, x_55);
lean_dec(x_52);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_15);
x_58 = lean_array_push(x_51, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_58);
x_3 = x_17;
x_4 = x_59;
goto _start;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_17);
x_61 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__7;
x_62 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_15, x_61, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_52);
x_67 = l_Lean_Syntax_getArg(x_15, x_16);
x_68 = l_Lean_Syntax_getId(x_67);
lean_dec(x_67);
x_69 = l_Lean_Name_eraseMacroScopes(x_68);
lean_dec(x_68);
x_70 = lean_unsigned_to_nat(3u);
x_71 = l_Lean_Syntax_getArg(x_15, x_70);
lean_dec(x_15);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_5);
x_74 = l_Lean_Elab_Term_addNamedArg(x_50, x_73, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_51);
x_3 = x_17;
x_4 = x_77;
x_11 = x_76;
goto _start;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_51);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_5);
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_81 = x_74;
} else {
 lean_dec_ref(x_74);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_expandApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'..' is only allowed in patterns");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandApp___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandApp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandApp___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandApp(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_82 = lean_unsigned_to_nat(1u);
x_83 = l_Lean_Syntax_getArg(x_1, x_82);
x_84 = l_Lean_Syntax_getArgs(x_83);
lean_dec(x_83);
x_85 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_84);
x_86 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
x_87 = l_Lean_Syntax_isOfKind(x_85, x_86);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = 0;
x_12 = x_84;
x_13 = x_88;
goto block_81;
}
else
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_array_pop(x_84);
x_90 = 1;
x_12 = x_89;
x_13 = x_90;
goto block_81;
}
block_81:
{
if (x_2 == 0)
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_importModules___closed__1;
x_15 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1(x_12, x_12, x_10, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_box(x_13);
lean_ctor_set(x_17, 1, x_21);
lean_ctor_set(x_17, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_15, 0, x_23);
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_box(x_13);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_34 = x_30;
} else {
 lean_dec_ref(x_30);
 x_34 = lean_box(0);
}
x_35 = lean_box(x_13);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_11);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_31);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
x_40 = !lean_is_exclusive(x_15);
if (x_40 == 0)
{
return x_15;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
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
lean_dec(x_11);
x_44 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_12);
lean_dec(x_12);
x_45 = l_Lean_Elab_Term_expandApp___closed__3;
x_46 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_44, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_44);
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
lean_object* x_51; lean_object* x_52; 
x_51 = l_Lean_importModules___closed__1;
x_52 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__3(x_12, x_12, x_10, x_51, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
x_58 = lean_box(x_13);
lean_ctor_set(x_54, 1, x_58);
lean_ctor_set(x_54, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_54);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_11);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_52, 0, x_60);
return x_52;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_54, 0);
x_62 = lean_ctor_get(x_54, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_54);
x_63 = lean_box(x_13);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_11);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_52, 0, x_66);
return x_52;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_52, 0);
x_68 = lean_ctor_get(x_52, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_52);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_71 = x_67;
} else {
 lean_dec_ref(x_67);
 x_71 = lean_box(0);
}
x_72 = lean_box(x_13);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_11);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_68);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_11);
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
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_expandApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Elab_Term_expandApp(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
lean_inc(x_7);
lean_inc(x_3);
x_11 = l_Lean_Elab_Term_expandApp(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l___private_Lean_Elab_App_39__elabAppAux(x_16, x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_elabApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabApp___boxed), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_mkAppStx___closed__8;
x_4 = l___regBuiltin_Lean_Elab_Term_elabApp___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_40__elabAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Array_empty___closed__1;
x_11 = l___private_Lean_Elab_App_39__elabAppAux(x_1, x_10, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_40__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabIdent), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_identKind___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabNamedPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_40__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabNamedPattern), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__13;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_40__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabExplicitUniv), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandDollarProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_40__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_expandDollarProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandDollarProj), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_expandDollarProj(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__16;
x_4 = l___regBuiltin_Lean_Elab_Term_expandDollarProj___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_77; uint8_t x_78; 
x_77 = l___private_Lean_Elab_Term_14__isExplicit___closed__2;
lean_inc(x_1);
x_78 = l_Lean_Syntax_isOfKind(x_1, x_77);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = 0;
x_10 = x_79;
goto block_76;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = l_Lean_Syntax_getArgs(x_1);
x_81 = lean_array_get_size(x_80);
lean_dec(x_80);
x_82 = lean_unsigned_to_nat(2u);
x_83 = lean_nat_dec_eq(x_81, x_82);
lean_dec(x_81);
x_10 = x_83;
goto block_76;
}
block_76:
{
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_48; uint8_t x_49; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_48 = l_Lean_identKind___closed__2;
lean_inc(x_13);
x_49 = l_Lean_Syntax_isOfKind(x_13, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__5;
lean_inc(x_13);
x_51 = l_Lean_Syntax_isOfKind(x_13, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_1);
x_52 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
lean_inc(x_13);
x_53 = l_Lean_Syntax_isOfKind(x_13, x_52);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = 0;
x_14 = x_54;
goto block_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = l_Lean_Syntax_getArgs(x_13);
x_56 = lean_array_get_size(x_55);
lean_dec(x_55);
x_57 = lean_unsigned_to_nat(3u);
x_58 = lean_nat_dec_eq(x_56, x_57);
lean_dec(x_56);
x_14 = x_58;
goto block_47;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = l_Lean_Syntax_getArgs(x_13);
x_60 = lean_array_get_size(x_59);
lean_dec(x_59);
x_61 = lean_unsigned_to_nat(4u);
x_62 = lean_nat_dec_eq(x_60, x_61);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
lean_dec(x_1);
x_63 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
lean_inc(x_13);
x_64 = l_Lean_Syntax_isOfKind(x_13, x_63);
if (x_64 == 0)
{
uint8_t x_65; 
lean_dec(x_60);
x_65 = 0;
x_14 = x_65;
goto block_47;
}
else
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_unsigned_to_nat(3u);
x_67 = lean_nat_dec_eq(x_60, x_66);
lean_dec(x_60);
x_14 = x_67;
goto block_47;
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_60);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Lean_Syntax_getArg(x_13, x_68);
x_70 = l_Lean_Syntax_isOfKind(x_69, x_48);
if (x_70 == 0)
{
uint8_t x_71; uint8_t x_72; lean_object* x_73; 
lean_dec(x_1);
x_71 = 1;
x_72 = 0;
x_73 = l___private_Lean_Elab_Term_21__elabTermAux___main(x_2, x_71, x_72, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_73;
}
else
{
lean_object* x_74; 
lean_dec(x_13);
x_74 = l___private_Lean_Elab_App_40__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_74;
}
}
}
}
else
{
lean_object* x_75; 
lean_dec(x_13);
x_75 = l___private_Lean_Elab_App_40__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_75;
}
block_47:
{
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = 1;
x_16 = 0;
x_17 = l___private_Lean_Elab_Term_21__elabTermAux___main(x_2, x_15, x_16, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Syntax_getArg(x_13, x_12);
x_19 = l_Lean_nullKind___closed__2;
lean_inc(x_18);
x_20 = l_Lean_Syntax_isOfKind(x_18, x_19);
if (x_20 == 0)
{
uint8_t x_21; uint8_t x_22; lean_object* x_23; 
lean_dec(x_18);
x_21 = 1;
x_22 = 0;
x_23 = l___private_Lean_Elab_Term_21__elabTermAux___main(x_2, x_21, x_22, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = l_Lean_Syntax_getArgs(x_18);
x_25 = lean_array_get_size(x_24);
lean_dec(x_24);
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_nat_dec_eq(x_25, x_26);
lean_dec(x_25);
if (x_27 == 0)
{
uint8_t x_28; uint8_t x_29; lean_object* x_30; 
lean_dec(x_18);
x_28 = 1;
x_29 = 0;
x_30 = l___private_Lean_Elab_Term_21__elabTermAux___main(x_2, x_28, x_29, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Lean_Syntax_getArg(x_18, x_31);
x_33 = l_Lean_Syntax_getArg(x_18, x_12);
lean_dec(x_18);
lean_inc(x_33);
x_34 = l_Lean_Syntax_isOfKind(x_33, x_19);
if (x_34 == 0)
{
uint8_t x_35; uint8_t x_36; lean_object* x_37; 
lean_dec(x_33);
lean_dec(x_32);
x_35 = 1;
x_36 = 0;
x_37 = l___private_Lean_Elab_Term_21__elabTermAux___main(x_2, x_35, x_36, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = l_Lean_Syntax_getArgs(x_33);
lean_dec(x_33);
x_39 = lean_array_get_size(x_38);
lean_dec(x_38);
x_40 = lean_nat_dec_eq(x_39, x_31);
lean_dec(x_39);
if (x_40 == 0)
{
uint8_t x_41; uint8_t x_42; lean_object* x_43; 
lean_dec(x_32);
x_41 = 1;
x_42 = 0;
x_43 = l___private_Lean_Elab_Term_21__elabTermAux___main(x_2, x_41, x_42, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_43;
}
else
{
uint8_t x_44; uint8_t x_45; lean_object* x_46; 
lean_dec(x_13);
x_44 = 1;
x_45 = 0;
x_46 = l___private_Lean_Elab_Term_21__elabTermAux___main(x_2, x_44, x_45, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_46;
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabExplicit), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___private_Lean_Elab_Term_14__isExplicit___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_40__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabChoice), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_choiceKind___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_40__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabProj), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__9;
x_4 = l___regBuiltin_Lean_Elab_Term_elabProj___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_40__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabArrayRef), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___private_Lean_Elab_App_33__elabAppFn___main___closed__11;
x_4 = l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_41__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_App_14__propagateExpectedType___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_FindMVar(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_App(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindMVar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_Arg_inhabited___closed__1 = _init_l_Lean_Elab_Term_Arg_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Arg_inhabited___closed__1);
l_Lean_Elab_Term_Arg_inhabited = _init_l_Lean_Elab_Term_Arg_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_Arg_inhabited);
l_Lean_Elab_Term_NamedArg_inhabited___closed__1 = _init_l_Lean_Elab_Term_NamedArg_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_NamedArg_inhabited___closed__1);
l_Lean_Elab_Term_NamedArg_inhabited = _init_l_Lean_Elab_Term_NamedArg_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_NamedArg_inhabited);
l_Lean_Elab_Term_addNamedArg___closed__1 = _init_l_Lean_Elab_Term_addNamedArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__1);
l_Lean_Elab_Term_addNamedArg___closed__2 = _init_l_Lean_Elab_Term_addNamedArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__2);
l_Lean_Elab_Term_addNamedArg___closed__3 = _init_l_Lean_Elab_Term_addNamedArg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__3);
l_Lean_Elab_Term_addNamedArg___closed__4 = _init_l_Lean_Elab_Term_addNamedArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__4);
l_Lean_Elab_Term_addNamedArg___closed__5 = _init_l_Lean_Elab_Term_addNamedArg___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__5);
l_Lean_Elab_Term_addNamedArg___closed__6 = _init_l_Lean_Elab_Term_addNamedArg___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__6);
l___private_Lean_Elab_App_2__tryCoeFun___closed__1 = _init_l___private_Lean_Elab_App_2__tryCoeFun___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_2__tryCoeFun___closed__1);
l___private_Lean_Elab_App_2__tryCoeFun___closed__2 = _init_l___private_Lean_Elab_App_2__tryCoeFun___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_2__tryCoeFun___closed__2);
l___private_Lean_Elab_App_2__tryCoeFun___closed__3 = _init_l___private_Lean_Elab_App_2__tryCoeFun___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_2__tryCoeFun___closed__3);
l___private_Lean_Elab_App_2__tryCoeFun___closed__4 = _init_l___private_Lean_Elab_App_2__tryCoeFun___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_2__tryCoeFun___closed__4);
l___private_Lean_Elab_App_2__tryCoeFun___closed__5 = _init_l___private_Lean_Elab_App_2__tryCoeFun___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_2__tryCoeFun___closed__5);
l___private_Lean_Elab_App_2__tryCoeFun___closed__6 = _init_l___private_Lean_Elab_App_2__tryCoeFun___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_2__tryCoeFun___closed__6);
l___private_Lean_Elab_App_2__tryCoeFun___closed__7 = _init_l___private_Lean_Elab_App_2__tryCoeFun___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_2__tryCoeFun___closed__7);
l___private_Lean_Elab_App_2__tryCoeFun___closed__8 = _init_l___private_Lean_Elab_App_2__tryCoeFun___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_2__tryCoeFun___closed__8);
l___private_Lean_Elab_App_11__hasOptAutoParams___closed__1 = _init_l___private_Lean_Elab_App_11__hasOptAutoParams___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_11__hasOptAutoParams___closed__1);
l___private_Lean_Elab_App_14__propagateExpectedType___closed__1 = _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_14__propagateExpectedType___closed__1);
l___private_Lean_Elab_App_14__propagateExpectedType___closed__2 = _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_14__propagateExpectedType___closed__2);
l___private_Lean_Elab_App_14__propagateExpectedType___closed__3 = _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_14__propagateExpectedType___closed__3);
l___private_Lean_Elab_App_14__propagateExpectedType___closed__4 = _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_14__propagateExpectedType___closed__4);
l___private_Lean_Elab_App_14__propagateExpectedType___closed__5 = _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_14__propagateExpectedType___closed__5);
l___private_Lean_Elab_App_14__propagateExpectedType___closed__6 = _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_14__propagateExpectedType___closed__6);
l___private_Lean_Elab_App_14__propagateExpectedType___closed__7 = _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_14__propagateExpectedType___closed__7);
l___private_Lean_Elab_App_14__propagateExpectedType___closed__8 = _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_14__propagateExpectedType___closed__8);
l___private_Lean_Elab_App_14__propagateExpectedType___closed__9 = _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_14__propagateExpectedType___closed__9);
l___private_Lean_Elab_App_14__propagateExpectedType___closed__10 = _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_14__propagateExpectedType___closed__10);
l___private_Lean_Elab_App_14__propagateExpectedType___closed__11 = _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_14__propagateExpectedType___closed__11);
l___private_Lean_Elab_App_14__propagateExpectedType___closed__12 = _init_l___private_Lean_Elab_App_14__propagateExpectedType___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_14__propagateExpectedType___closed__12);
l___private_Lean_Elab_App_16__finalize___closed__1 = _init_l___private_Lean_Elab_App_16__finalize___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_16__finalize___closed__1);
l___private_Lean_Elab_App_16__finalize___closed__2 = _init_l___private_Lean_Elab_App_16__finalize___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_16__finalize___closed__2);
l___private_Lean_Elab_App_16__finalize___closed__3 = _init_l___private_Lean_Elab_App_16__finalize___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_16__finalize___closed__3);
l___private_Lean_Elab_App_16__finalize___closed__4 = _init_l___private_Lean_Elab_App_16__finalize___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_16__finalize___closed__4);
l___private_Lean_Elab_App_16__finalize___closed__5 = _init_l___private_Lean_Elab_App_16__finalize___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_16__finalize___closed__5);
l___private_Lean_Elab_App_16__finalize___closed__6 = _init_l___private_Lean_Elab_App_16__finalize___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_16__finalize___closed__6);
l___private_Lean_Elab_App_16__finalize___closed__7 = _init_l___private_Lean_Elab_App_16__finalize___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_16__finalize___closed__7);
l___private_Lean_Elab_App_16__finalize___closed__8 = _init_l___private_Lean_Elab_App_16__finalize___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_16__finalize___closed__8);
l___private_Lean_Elab_App_17__processExplictArg___closed__1 = _init_l___private_Lean_Elab_App_17__processExplictArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_17__processExplictArg___closed__1);
l___private_Lean_Elab_App_17__processExplictArg___closed__2 = _init_l___private_Lean_Elab_App_17__processExplictArg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_17__processExplictArg___closed__2);
l___private_Lean_Elab_App_17__processExplictArg___closed__3 = _init_l___private_Lean_Elab_App_17__processExplictArg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_17__processExplictArg___closed__3);
l___private_Lean_Elab_App_17__processExplictArg___closed__4 = _init_l___private_Lean_Elab_App_17__processExplictArg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_17__processExplictArg___closed__4);
l___private_Lean_Elab_App_17__processExplictArg___closed__5 = _init_l___private_Lean_Elab_App_17__processExplictArg___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_17__processExplictArg___closed__5);
l___private_Lean_Elab_App_17__processExplictArg___closed__6 = _init_l___private_Lean_Elab_App_17__processExplictArg___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_17__processExplictArg___closed__6);
l_Lean_Elab_Term_ElabAppArgs_main___main___rarg___closed__1 = _init_l_Lean_Elab_Term_ElabAppArgs_main___main___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_ElabAppArgs_main___main___rarg___closed__1);
l___private_Lean_Elab_App_21__elabAppArgs___closed__1 = _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_21__elabAppArgs___closed__1);
l___private_Lean_Elab_App_21__elabAppArgs___closed__2 = _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_21__elabAppArgs___closed__2);
l___private_Lean_Elab_App_21__elabAppArgs___closed__3 = _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_21__elabAppArgs___closed__3);
l___private_Lean_Elab_App_21__elabAppArgs___closed__4 = _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_21__elabAppArgs___closed__4);
l___private_Lean_Elab_App_21__elabAppArgs___closed__5 = _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_21__elabAppArgs___closed__5);
l___private_Lean_Elab_App_21__elabAppArgs___closed__6 = _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_21__elabAppArgs___closed__6);
l___private_Lean_Elab_App_21__elabAppArgs___closed__7 = _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_21__elabAppArgs___closed__7);
l___private_Lean_Elab_App_21__elabAppArgs___closed__8 = _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_21__elabAppArgs___closed__8);
l___private_Lean_Elab_App_21__elabAppArgs___closed__9 = _init_l___private_Lean_Elab_App_21__elabAppArgs___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_21__elabAppArgs___closed__9);
l___private_Lean_Elab_App_24__resolveLValAux___closed__1 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__1);
l___private_Lean_Elab_App_24__resolveLValAux___closed__2 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__2);
l___private_Lean_Elab_App_24__resolveLValAux___closed__3 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__3);
l___private_Lean_Elab_App_24__resolveLValAux___closed__4 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__4);
l___private_Lean_Elab_App_24__resolveLValAux___closed__5 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__5);
l___private_Lean_Elab_App_24__resolveLValAux___closed__6 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__6);
l___private_Lean_Elab_App_24__resolveLValAux___closed__7 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__7);
l___private_Lean_Elab_App_24__resolveLValAux___closed__8 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__8);
l___private_Lean_Elab_App_24__resolveLValAux___closed__9 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__9);
l___private_Lean_Elab_App_24__resolveLValAux___closed__10 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__10);
l___private_Lean_Elab_App_24__resolveLValAux___closed__11 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__11);
l___private_Lean_Elab_App_24__resolveLValAux___closed__12 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__12);
l___private_Lean_Elab_App_24__resolveLValAux___closed__13 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__13();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__13);
l___private_Lean_Elab_App_24__resolveLValAux___closed__14 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__14();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__14);
l___private_Lean_Elab_App_24__resolveLValAux___closed__15 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__15();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__15);
l___private_Lean_Elab_App_24__resolveLValAux___closed__16 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__16();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__16);
l___private_Lean_Elab_App_24__resolveLValAux___closed__17 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__17();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__17);
l___private_Lean_Elab_App_24__resolveLValAux___closed__18 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__18();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__18);
l___private_Lean_Elab_App_24__resolveLValAux___closed__19 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__19();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__19);
l___private_Lean_Elab_App_24__resolveLValAux___closed__20 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__20();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__20);
l___private_Lean_Elab_App_24__resolveLValAux___closed__21 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__21();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__21);
l___private_Lean_Elab_App_24__resolveLValAux___closed__22 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__22();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__22);
l___private_Lean_Elab_App_24__resolveLValAux___closed__23 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__23();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__23);
l___private_Lean_Elab_App_24__resolveLValAux___closed__24 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__24();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__24);
l___private_Lean_Elab_App_24__resolveLValAux___closed__25 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__25();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__25);
l___private_Lean_Elab_App_24__resolveLValAux___closed__26 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__26();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__26);
l___private_Lean_Elab_App_24__resolveLValAux___closed__27 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__27();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__27);
l___private_Lean_Elab_App_24__resolveLValAux___closed__28 = _init_l___private_Lean_Elab_App_24__resolveLValAux___closed__28();
lean_mark_persistent(l___private_Lean_Elab_App_24__resolveLValAux___closed__28);
l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1___closed__1 = _init_l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1___closed__1);
l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1___closed__2 = _init_l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1___closed__2();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_App_28__mkBaseProjections___spec__1___closed__2);
l___private_Lean_Elab_App_28__mkBaseProjections___closed__1 = _init_l___private_Lean_Elab_App_28__mkBaseProjections___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_28__mkBaseProjections___closed__1);
l___private_Lean_Elab_App_28__mkBaseProjections___closed__2 = _init_l___private_Lean_Elab_App_28__mkBaseProjections___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_28__mkBaseProjections___closed__2);
l___private_Lean_Elab_App_28__mkBaseProjections___closed__3 = _init_l___private_Lean_Elab_App_28__mkBaseProjections___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_28__mkBaseProjections___closed__3);
l___private_Lean_Elab_App_29__addLValArg___main___closed__1 = _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_29__addLValArg___main___closed__1);
l___private_Lean_Elab_App_29__addLValArg___main___closed__2 = _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_29__addLValArg___main___closed__2);
l___private_Lean_Elab_App_29__addLValArg___main___closed__3 = _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_29__addLValArg___main___closed__3);
l___private_Lean_Elab_App_29__addLValArg___main___closed__4 = _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_29__addLValArg___main___closed__4);
l___private_Lean_Elab_App_29__addLValArg___main___closed__5 = _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_29__addLValArg___main___closed__5);
l___private_Lean_Elab_App_29__addLValArg___main___closed__6 = _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_29__addLValArg___main___closed__6);
l___private_Lean_Elab_App_29__addLValArg___main___closed__7 = _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_29__addLValArg___main___closed__7);
l___private_Lean_Elab_App_29__addLValArg___main___closed__8 = _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_29__addLValArg___main___closed__8);
l___private_Lean_Elab_App_29__addLValArg___main___closed__9 = _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_29__addLValArg___main___closed__9);
l___private_Lean_Elab_App_29__addLValArg___main___closed__10 = _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_29__addLValArg___main___closed__10);
l___private_Lean_Elab_App_29__addLValArg___main___closed__11 = _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_29__addLValArg___main___closed__11);
l___private_Lean_Elab_App_29__addLValArg___main___closed__12 = _init_l___private_Lean_Elab_App_29__addLValArg___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_29__addLValArg___main___closed__12);
l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__1 = _init_l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__1);
l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__2 = _init_l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_30__elabAppLValsAux___main___closed__2);
l___private_Lean_Elab_App_31__elabAppLVals___closed__1 = _init_l___private_Lean_Elab_App_31__elabAppLVals___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_31__elabAppLVals___closed__1);
l___private_Lean_Elab_App_31__elabAppLVals___closed__2 = _init_l___private_Lean_Elab_App_31__elabAppLVals___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_31__elabAppLVals___closed__2);
l___private_Lean_Elab_App_31__elabAppLVals___closed__3 = _init_l___private_Lean_Elab_App_31__elabAppLVals___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_31__elabAppLVals___closed__3);
l___private_Lean_Elab_App_33__elabAppFn___main___closed__1 = _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_33__elabAppFn___main___closed__1);
l___private_Lean_Elab_App_33__elabAppFn___main___closed__2 = _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_33__elabAppFn___main___closed__2);
l___private_Lean_Elab_App_33__elabAppFn___main___closed__3 = _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_33__elabAppFn___main___closed__3);
l___private_Lean_Elab_App_33__elabAppFn___main___closed__4 = _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_33__elabAppFn___main___closed__4);
l___private_Lean_Elab_App_33__elabAppFn___main___closed__5 = _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_33__elabAppFn___main___closed__5);
l___private_Lean_Elab_App_33__elabAppFn___main___closed__6 = _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_33__elabAppFn___main___closed__6);
l___private_Lean_Elab_App_33__elabAppFn___main___closed__7 = _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_33__elabAppFn___main___closed__7);
l___private_Lean_Elab_App_33__elabAppFn___main___closed__8 = _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_33__elabAppFn___main___closed__8);
l___private_Lean_Elab_App_33__elabAppFn___main___closed__9 = _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_33__elabAppFn___main___closed__9);
l___private_Lean_Elab_App_33__elabAppFn___main___closed__10 = _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_33__elabAppFn___main___closed__10);
l___private_Lean_Elab_App_33__elabAppFn___main___closed__11 = _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_33__elabAppFn___main___closed__11);
l___private_Lean_Elab_App_33__elabAppFn___main___closed__12 = _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_33__elabAppFn___main___closed__12);
l___private_Lean_Elab_App_33__elabAppFn___main___closed__13 = _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__13();
lean_mark_persistent(l___private_Lean_Elab_App_33__elabAppFn___main___closed__13);
l___private_Lean_Elab_App_33__elabAppFn___main___closed__14 = _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__14();
lean_mark_persistent(l___private_Lean_Elab_App_33__elabAppFn___main___closed__14);
l___private_Lean_Elab_App_33__elabAppFn___main___closed__15 = _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__15();
lean_mark_persistent(l___private_Lean_Elab_App_33__elabAppFn___main___closed__15);
l___private_Lean_Elab_App_33__elabAppFn___main___closed__16 = _init_l___private_Lean_Elab_App_33__elabAppFn___main___closed__16();
lean_mark_persistent(l___private_Lean_Elab_App_33__elabAppFn___main___closed__16);
l___private_Lean_Elab_App_36__toMessageData___closed__1 = _init_l___private_Lean_Elab_App_36__toMessageData___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_36__toMessageData___closed__1);
l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__1 = _init_l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__1);
l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__2 = _init_l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__2);
l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__3 = _init_l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_38__mergeFailures___rarg___closed__3);
l___private_Lean_Elab_App_39__elabAppAux___closed__1 = _init_l___private_Lean_Elab_App_39__elabAppAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_39__elabAppAux___closed__1);
l___private_Lean_Elab_App_39__elabAppAux___closed__2 = _init_l___private_Lean_Elab_App_39__elabAppAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_39__elabAppAux___closed__2);
l___private_Lean_Elab_App_39__elabAppAux___closed__3 = _init_l___private_Lean_Elab_App_39__elabAppAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_39__elabAppAux___closed__3);
l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1);
l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2);
l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__3 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__3();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__3);
l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4);
l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__5 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__5();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__5);
l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__6 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__6();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__6);
l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__7 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__7();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__7);
l_Lean_Elab_Term_expandApp___closed__1 = _init_l_Lean_Elab_Term_expandApp___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandApp___closed__1);
l_Lean_Elab_Term_expandApp___closed__2 = _init_l_Lean_Elab_Term_expandApp___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandApp___closed__2);
l_Lean_Elab_Term_expandApp___closed__3 = _init_l_Lean_Elab_Term_expandApp___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandApp___closed__3);
l___regBuiltin_Lean_Elab_Term_elabApp___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabApp___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabApp___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabApp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabIdent(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabNamedPattern(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabExplicitUniv(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_expandDollarProj___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_expandDollarProj___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_expandDollarProj___closed__1);
res = l___regBuiltin_Lean_Elab_Term_expandDollarProj(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabExplicit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabChoice(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabProj___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabProj___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabProj___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabProj(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1);
res = l___regBuiltin_Lean_Elab_Term_elabArrayRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_App_41__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
