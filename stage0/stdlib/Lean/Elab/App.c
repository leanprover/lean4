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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1___rarg(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2;
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeFormerTypeImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
lean_object* l_List_tail_x21___rarg(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__4;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__6;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Syntax_getSepArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isTypeApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2;
extern lean_object* l_Lean_fieldIdxKind___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__3(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__15;
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___closed__1;
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__11;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__2___rarg(lean_object*, lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l_List_map___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(lean_object*);
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_inhabited___closed__1;
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__2(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandDollarProj(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_State_typeMVars___default;
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12;
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasArgsToProcess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp_match__2(lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_904____spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_match__1(lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__3(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_goalsToMessageData___closed__1;
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6;
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__1;
lean_object* l_Lean_Elab_Term_elabApp_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__3;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getBindingName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess___boxed(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess(lean_object*);
lean_object* l_List_find_x3f___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__2(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__2;
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__3(lean_object*);
lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___closed__1;
uint8_t l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__4___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__2;
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__10;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures(lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__4;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp_match__1(lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__2;
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandDollarProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__1;
uint8_t l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_fTypeHasOptAutoParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__7;
lean_object* l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object*, lean_object*, lean_object*);
extern lean_object* l_ULift_HasRepr___rarg___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__3;
lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__3;
extern lean_object* l_Lean_Meta_isExprDefEq___rarg___closed__2;
uint8_t l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEqAux___closed__6;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__4;
extern lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getBindingName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__2_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__1(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__2;
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3;
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind___closed__2;
uint8_t l_Lean_Elab_Term_ElabAppArgs_State_ellipsis___default;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__2;
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__1___closed__1;
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_visit(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyInfo(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageList___boxed(lean_object*);
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__3(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processInstImplicitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__1(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___boxed(lean_object**);
lean_object* l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1;
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__2_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_expandApp_match__3___rarg(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___lambda__4___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11;
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_isLevelDefEq___spec__3___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__7;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__16;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__3___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___boxed(lean_object**);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__4___closed__1;
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_State_instMVars___default;
lean_object* l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData_match__1(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern(lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice(lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_processAssignmentFOApprox_loop___closed__3;
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasArgsToProcess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__1;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_State_toSetErrorCtx___default;
lean_object* l_Lean_Elab_Term_elabIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_Elab_Term_elabApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__13;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__1;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__1(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__5;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_elabChoice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___rarg___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__2(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3;
extern lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__8;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2;
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__15;
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandDollarProj___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__16;
extern lean_object* l_Lean_importModules___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__1(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__6;
extern lean_object* l_Lean_formatEntry___closed__1;
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__3;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__1;
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections_match__1(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj___closed__1;
uint8_t l_Lean_Expr_isAutoParam(lean_object*);
lean_object* l_Lean_Elab_Term_elabNamedPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageList(lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__14;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__3(uint8_t);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Term_elabProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_Lean_Meta_Basic___instance__10___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__5(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_Lean_Elab_setMacroStackOption(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__4;
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__4(lean_object*);
extern lean_object* l_ReaderT_monadControl___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__1;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__5;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Elab_Term_expandApp_match__3(lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2(lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3___boxed(lean_object**);
lean_object* l_Lean_getParentStructures(lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__29;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess_match__1(lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
extern lean_object* l_Lean_Elab_postponeExceptionId;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures_match__1(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__3(lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_saveAllState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__1(lean_object*);
lean_object* l_Lean_Meta_throwUnknownFVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj(lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__5;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__6;
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
extern lean_object* l_Lean_Init_LeanInit___instance__8___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___boxed(lean_object**);
lean_object* l_Lean_Elab_Term_ElabAppArgs_State_etaArgs___default;
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_isExplicit___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2(lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__1(lean_object*);
lean_object* l_Lean_Exception_getRef(lean_object*);
extern lean_object* l_Lean_Meta_throwFunctionExpected___rarg___closed__1;
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__6;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicitUnivs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__4(lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_7244_(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__2(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___rarg(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__9;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__1;
extern lean_object* l_Lean_Elab_Term_Lean_Elab_Term___instance__4;
lean_object* l_monadControlTrans___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1;
lean_object* l_Lean_Elab_Term_registerSyntheticMVarWithCurrRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__3(lean_object*);
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabApp_match__1(lean_object*);
lean_object* l_Lean_Meta_inferType___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
lean_object* l_Lean_Elab_Term_registerMVarErrorImplicitArgInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_isLevelDefEq___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__8;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__2;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__2;
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__1;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole_match__1(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1(lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_runDefEqM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__11;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_applyResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__9;
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ensureArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_899____closed__1;
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
lean_object* l_Lean_Elab_Term_expandApp___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__2;
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__4;
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__6;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__14;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__1;
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__2;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__5;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2;
lean_object* l_Lean_Elab_Term_ensureHasTypeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_ElabAppArgs_State_alreadyPropagated___default;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__4;
lean_object* l_Lean_Name_components(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__3;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_2__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__5;
lean_object* l_Lean_Elab_Term_elabExplicitUnivs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__8;
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__5;
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_Lean_Message___instance__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__3(lean_object*);
extern lean_object* l_Lean_Meta_mkArrow___rarg___closed__2;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__3___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Term_Lean_Elab_App___instance__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_Lean_Elab_App___instance__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_Lean_Elab_App___instance__1___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__2_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__2_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Lean_Elab_App___instance__2_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__2(lean_object* x_1) {
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
x_6 = l_Lean_Syntax_formatStxAux(x_3, x_4, x_5, x_2);
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
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_System_FilePath_dirName___closed__1;
x_4 = l_Lean_Name_toStringWithSep(x_3, x_2);
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
x_14 = l_Lean_Syntax_formatStxAux(x_11, x_12, x_13, x_10);
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
static lean_object* _init_l_Lean_Elab_Term_Lean_Elab_App___instance__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Lean_Elab_App___instance__1___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Lean_Elab_App___instance__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_Lean_Elab_App___instance__4___closed__1;
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
lean_object* l_Lean_Elab_Term_addNamedArg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_push(x_1, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
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
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' was already set");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
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
x_13 = lean_box(0);
x_14 = l_Lean_Elab_Term_addNamedArg___lambda__1(x_1, x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Term_addNamedArg___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Elab_Term_addNamedArg___closed__4;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
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
lean_object* l_Lean_Elab_Term_addNamedArg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_addNamedArg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ensureArgType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_11 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_dec(x_5);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_mkArrow___rarg___closed__2;
x_11 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_10, x_7, x_8, x_9);
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
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_throwFunctionExpected___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeFun");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (x_6 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__2;
x_15 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__4;
x_17 = l_Lean_mkConst(x_16, x_1);
x_18 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_19 = lean_array_push(x_18, x_2);
x_20 = lean_array_push(x_19, x_3);
x_21 = lean_array_push(x_20, x_4);
x_22 = lean_array_push(x_21, x_5);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_22, x_22, x_23, x_17);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_13);
return x_25;
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CoeFun");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("function expected\n");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_14 = l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
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
x_20 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_16);
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
x_23 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_1, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
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
x_29 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__2;
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
x_38 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_36, x_37, x_19, x_5, x_6, x_7, x_8, x_25);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Expr_mvarId_x21(x_39);
x_42 = lean_ctor_get(x_7, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_7, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_7, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_7, 3);
lean_inc(x_45);
x_46 = 0;
x_47 = l_Lean_Elab_setMacroStackOption(x_42, x_46);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_44);
lean_ctor_set(x_48, 3, x_45);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_49 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_41, x_3, x_4, x_5, x_6, x_48, x_8, x_40);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_unbox(x_50);
lean_dec(x_50);
x_53 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1(x_28, x_1, x_21, x_2, x_39, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_51);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_53;
}
else
{
lean_object* x_54; 
lean_dec(x_39);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__4;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_55);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_54);
x_66 = lean_ctor_get(x_49, 1);
lean_inc(x_66);
lean_dec(x_49);
x_67 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__2;
x_68 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_66);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
return x_68;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_68);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_23);
if (x_73 == 0)
{
return x_23;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_23, 0);
x_75 = lean_ctor_get(x_23, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_23);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_15;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 < x_2;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_15 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
lean_inc(x_9);
x_20 = l_Lean_Elab_Term_registerSyntheticMVarWithCurrRef(x_14, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = x_3 + x_22;
x_24 = lean_box(0);
x_3 = x_23;
x_4 = x_24;
x_11 = x_21;
goto _start;
}
else
{
lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
lean_dec(x_14);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = 1;
x_28 = x_3 + x_27;
x_29 = lean_box(0);
x_3 = x_28;
x_4 = x_29;
x_11 = x_26;
goto _start;
}
}
else
{
uint8_t x_31; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_box(0);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_1, x_10, x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_synthesizeAppInstMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
static uint8_t _init_l_Lean_Elab_Term_ElabAppArgs_State_ellipsis___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_ElabAppArgs_State_etaArgs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_ElabAppArgs_State_toSetErrorCtx___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_ElabAppArgs_State_instMVars___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_ElabAppArgs_State_typeMVars___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static uint8_t _init_l_Lean_Elab_Term_ElabAppArgs_State_alreadyPropagated___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 7);
x_15 = lean_array_push(x_14, x_1);
lean_ctor_set(x_11, 7, x_15);
x_16 = lean_st_ref_set(x_2, x_11, x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get_uint8(x_11, sizeof(void*)*9);
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 2);
x_27 = lean_ctor_get(x_11, 3);
x_28 = lean_ctor_get_uint8(x_11, sizeof(void*)*9 + 1);
x_29 = lean_ctor_get(x_11, 4);
x_30 = lean_ctor_get(x_11, 5);
x_31 = lean_ctor_get(x_11, 6);
x_32 = lean_ctor_get(x_11, 7);
x_33 = lean_ctor_get(x_11, 8);
x_34 = lean_ctor_get_uint8(x_11, sizeof(void*)*9 + 2);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_35 = lean_array_push(x_32, x_1);
x_36 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_25);
lean_ctor_set(x_36, 2, x_26);
lean_ctor_set(x_36, 3, x_27);
lean_ctor_set(x_36, 4, x_29);
lean_ctor_set(x_36, 5, x_30);
lean_ctor_set(x_36, 6, x_31);
lean_ctor_set(x_36, 7, x_35);
lean_ctor_set(x_36, 8, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*9, x_23);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 1, x_28);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 2, x_34);
x_37 = lean_st_ref_set(x_2, x_36, x_12);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 7);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_take(x_1, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_14, 7);
lean_dec(x_17);
x_18 = l_Array_empty___closed__1;
lean_ctor_set(x_14, 7, x_18);
x_19 = lean_st_ref_set(x_1, x_14, x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Elab_Term_synthesizeAppInstMVars(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_12);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_22 = lean_ctor_get_uint8(x_14, sizeof(void*)*9);
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 2);
x_26 = lean_ctor_get(x_14, 3);
x_27 = lean_ctor_get_uint8(x_14, sizeof(void*)*9 + 1);
x_28 = lean_ctor_get(x_14, 4);
x_29 = lean_ctor_get(x_14, 5);
x_30 = lean_ctor_get(x_14, 6);
x_31 = lean_ctor_get(x_14, 8);
x_32 = lean_ctor_get_uint8(x_14, sizeof(void*)*9 + 2);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_33 = l_Array_empty___closed__1;
x_34 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_24);
lean_ctor_set(x_34, 2, x_25);
lean_ctor_set(x_34, 3, x_26);
lean_ctor_set(x_34, 4, x_28);
lean_ctor_set(x_34, 5, x_29);
lean_ctor_set(x_34, 6, x_30);
lean_ctor_set(x_34, 7, x_33);
lean_ctor_set(x_34, 8, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*9, x_22);
lean_ctor_set_uint8(x_34, sizeof(void*)*9 + 1, x_27);
lean_ctor_set_uint8(x_34, sizeof(void*)*9 + 2, x_32);
x_35 = lean_st_ref_set(x_1, x_34, x_15);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Elab_Term_synthesizeAppInstMVars(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_36);
lean_dec(x_12);
return x_37;
}
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 2);
lean_inc(x_11);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Meta_whnf___rarg___lambda__2(x_10, x_1, x_13, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_1);
x_15 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_16 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_904____spec__1___rarg(x_15, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_Meta_whnf___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Expr_isForall(x_12);
if (x_13 == 0)
{
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_1);
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
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l_Lean_Expr_isForall(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 2);
lean_inc(x_11);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Meta_inferType___rarg___lambda__1(x_10, x_1, x_13, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_1);
x_15 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_16 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_904____spec__1___rarg(x_15, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_1, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__1(x_18, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 7)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_take(x_1, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_23, 1);
lean_dec(x_26);
lean_ctor_set(x_23, 1, x_20);
x_27 = lean_st_ref_set(x_1, x_23, x_24);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_12);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_32 = lean_ctor_get_uint8(x_23, sizeof(void*)*9);
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_ctor_get(x_23, 2);
x_35 = lean_ctor_get(x_23, 3);
x_36 = lean_ctor_get_uint8(x_23, sizeof(void*)*9 + 1);
x_37 = lean_ctor_get(x_23, 4);
x_38 = lean_ctor_get(x_23, 5);
x_39 = lean_ctor_get(x_23, 6);
x_40 = lean_ctor_get(x_23, 7);
x_41 = lean_ctor_get(x_23, 8);
x_42 = lean_ctor_get_uint8(x_23, sizeof(void*)*9 + 2);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_23);
x_43 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_20);
lean_ctor_set(x_43, 2, x_34);
lean_ctor_set(x_43, 3, x_35);
lean_ctor_set(x_43, 4, x_37);
lean_ctor_set(x_43, 5, x_38);
lean_ctor_set(x_43, 6, x_39);
lean_ctor_set(x_43, 7, x_40);
lean_ctor_set(x_43, 8, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*9, x_32);
lean_ctor_set_uint8(x_43, sizeof(void*)*9 + 1, x_36);
lean_ctor_set_uint8(x_43, sizeof(void*)*9 + 2, x_42);
x_44 = lean_st_ref_set(x_1, x_43, x_24);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_12);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_dec(x_19);
x_49 = lean_ctor_get(x_16, 0);
lean_inc(x_49);
lean_dec(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_50 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun(x_20, x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_51);
x_53 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3(x_51, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_52);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_st_ref_take(x_1, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 0, x_51);
x_62 = lean_st_ref_set(x_1, x_57, x_58);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
lean_ctor_set(x_62, 0, x_12);
return x_62;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_12);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
uint8_t x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_67 = lean_ctor_get_uint8(x_57, sizeof(void*)*9);
x_68 = lean_ctor_get(x_57, 2);
x_69 = lean_ctor_get(x_57, 3);
x_70 = lean_ctor_get_uint8(x_57, sizeof(void*)*9 + 1);
x_71 = lean_ctor_get(x_57, 4);
x_72 = lean_ctor_get(x_57, 5);
x_73 = lean_ctor_get(x_57, 6);
x_74 = lean_ctor_get(x_57, 7);
x_75 = lean_ctor_get(x_57, 8);
x_76 = lean_ctor_get_uint8(x_57, sizeof(void*)*9 + 2);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_57);
x_77 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_77, 0, x_51);
lean_ctor_set(x_77, 1, x_54);
lean_ctor_set(x_77, 2, x_68);
lean_ctor_set(x_77, 3, x_69);
lean_ctor_set(x_77, 4, x_71);
lean_ctor_set(x_77, 5, x_72);
lean_ctor_set(x_77, 6, x_73);
lean_ctor_set(x_77, 7, x_74);
lean_ctor_set(x_77, 8, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*9, x_67);
lean_ctor_set_uint8(x_77, sizeof(void*)*9 + 1, x_70);
lean_ctor_set_uint8(x_77, sizeof(void*)*9 + 2, x_76);
x_78 = lean_st_ref_set(x_1, x_77, x_58);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_12);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_51);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_50);
if (x_86 == 0)
{
return x_50;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_50, 0);
x_88 = lean_ctor_get(x_50, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_50);
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
uint8_t x_90; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_19);
if (x_90 == 0)
{
return x_19;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_19, 0);
x_92 = lean_ctor_get(x_19, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_19);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_13);
if (x_94 == 0)
{
return x_13;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_13, 0);
x_96 = lean_ctor_get(x_13, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_13);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_9);
if (x_98 == 0)
{
return x_9;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_9, 0);
x_100 = lean_ctor_get(x_9, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_9);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_whnf___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__1(x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_1, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_17, 1);
lean_dec(x_20);
lean_inc(x_14);
lean_ctor_set(x_17, 1, x_14);
x_21 = lean_st_ref_set(x_1, x_17, x_18);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_26 = lean_ctor_get_uint8(x_17, sizeof(void*)*9);
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 2);
x_29 = lean_ctor_get(x_17, 3);
x_30 = lean_ctor_get_uint8(x_17, sizeof(void*)*9 + 1);
x_31 = lean_ctor_get(x_17, 4);
x_32 = lean_ctor_get(x_17, 5);
x_33 = lean_ctor_get(x_17, 6);
x_34 = lean_ctor_get(x_17, 7);
x_35 = lean_ctor_get(x_17, 8);
x_36 = lean_ctor_get_uint8(x_17, sizeof(void*)*9 + 2);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
lean_inc(x_14);
x_37 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_14);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 3, x_29);
lean_ctor_set(x_37, 4, x_31);
lean_ctor_set(x_37, 5, x_32);
lean_ctor_set(x_37, 6, x_33);
lean_ctor_set(x_37, 7, x_34);
lean_ctor_set(x_37, 8, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*9, x_26);
lean_ctor_set_uint8(x_37, sizeof(void*)*9 + 1, x_30);
lean_ctor_set_uint8(x_37, sizeof(void*)*9 + 2, x_36);
x_38 = lean_st_ref_set(x_1, x_37, x_18);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_14);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_13);
if (x_42 == 0)
{
return x_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_13);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getBindingName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Expr_bindingName_x21(x_12);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_bindingName_x21(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getBindingName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getBindingName(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Expr_bindingDomain_x21(x_12);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_bindingDomain_x21(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 3);
x_15 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(x_14, x_1);
lean_ctor_set(x_11, 3, x_15);
x_16 = lean_st_ref_set(x_2, x_11, x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get_uint8(x_11, sizeof(void*)*9);
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 2);
x_27 = lean_ctor_get(x_11, 3);
x_28 = lean_ctor_get_uint8(x_11, sizeof(void*)*9 + 1);
x_29 = lean_ctor_get(x_11, 4);
x_30 = lean_ctor_get(x_11, 5);
x_31 = lean_ctor_get(x_11, 6);
x_32 = lean_ctor_get(x_11, 7);
x_33 = lean_ctor_get(x_11, 8);
x_34 = lean_ctor_get_uint8(x_11, sizeof(void*)*9 + 2);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_35 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(x_27, x_1);
x_36 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_25);
lean_ctor_set(x_36, 2, x_26);
lean_ctor_set(x_36, 3, x_35);
lean_ctor_set(x_36, 4, x_29);
lean_ctor_set(x_36, 5, x_30);
lean_ctor_set(x_36, 6, x_31);
lean_ctor_set(x_36, 7, x_32);
lean_ctor_set(x_36, 8, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*9, x_23);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 1, x_28);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 2, x_34);
x_37 = lean_st_ref_set(x_2, x_36, x_12);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
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
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get_usize(x_8, 2);
x_20 = lean_ctor_get(x_8, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
lean_object* x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get_usize(x_9, 2);
x_24 = lean_ctor_get(x_9, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
lean_object* x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_10, 1);
x_27 = lean_ctor_get_usize(x_10, 2);
x_28 = lean_ctor_get(x_10, 0);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_11, 1);
x_31 = lean_ctor_get_usize(x_11, 2);
x_32 = lean_ctor_get(x_11, 0);
lean_dec(x_32);
x_33 = l_Lean_mkAppStx___closed__1;
x_34 = lean_string_dec_eq(x_30, x_33);
lean_dec(x_30);
if (x_34 == 0)
{
lean_object* x_35; 
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_26);
lean_free_object(x_9);
lean_dec(x_22);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_dec(x_15);
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_2);
x_35 = lean_apply_1(x_3, x_1);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_1);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_1, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_1, 0);
lean_dec(x_38);
x_39 = l_Lean_mkAppStx___closed__3;
x_40 = lean_string_dec_eq(x_26, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_33);
x_41 = lean_apply_1(x_3, x_1);
return x_41;
}
else
{
lean_object* x_42; uint8_t x_43; 
lean_dec(x_26);
x_42 = l_Lean_mkAppStx___closed__5;
x_43 = lean_string_dec_eq(x_22, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_33);
lean_ctor_set(x_10, 1, x_39);
x_44 = lean_apply_1(x_3, x_1);
return x_44;
}
else
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_22);
x_45 = l_Lean_mkHole___closed__1;
x_46 = lean_string_dec_eq(x_18, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_33);
lean_ctor_set(x_10, 1, x_39);
lean_ctor_set(x_9, 1, x_42);
x_47 = lean_apply_1(x_3, x_1);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_free_object(x_1);
lean_free_object(x_11);
lean_free_object(x_10);
lean_free_object(x_9);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_free_object(x_5);
lean_dec(x_3);
x_48 = lean_box_usize(x_31);
x_49 = lean_box_usize(x_27);
x_50 = lean_box_usize(x_23);
x_51 = lean_box_usize(x_19);
x_52 = lean_apply_6(x_2, x_15, x_13, x_48, x_49, x_50, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_53; uint8_t x_54; 
lean_dec(x_1);
x_53 = l_Lean_mkAppStx___closed__3;
x_54 = lean_string_dec_eq(x_26, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_33);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_5);
lean_ctor_set(x_55, 1, x_13);
x_56 = lean_apply_1(x_3, x_55);
return x_56;
}
else
{
lean_object* x_57; uint8_t x_58; 
lean_dec(x_26);
x_57 = l_Lean_mkAppStx___closed__5;
x_58 = lean_string_dec_eq(x_22, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_33);
lean_ctor_set(x_10, 1, x_53);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_5);
lean_ctor_set(x_59, 1, x_13);
x_60 = lean_apply_1(x_3, x_59);
return x_60;
}
else
{
lean_object* x_61; uint8_t x_62; 
lean_dec(x_22);
x_61 = l_Lean_mkHole___closed__1;
x_62 = lean_string_dec_eq(x_18, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_2);
lean_ctor_set(x_11, 1, x_33);
lean_ctor_set(x_10, 1, x_53);
lean_ctor_set(x_9, 1, x_57);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_5);
lean_ctor_set(x_63, 1, x_13);
x_64 = lean_apply_1(x_3, x_63);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_11);
lean_free_object(x_10);
lean_free_object(x_9);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_free_object(x_5);
lean_dec(x_3);
x_65 = lean_box_usize(x_31);
x_66 = lean_box_usize(x_27);
x_67 = lean_box_usize(x_23);
x_68 = lean_box_usize(x_19);
x_69 = lean_apply_6(x_2, x_15, x_13, x_65, x_66, x_67, x_68);
return x_69;
}
}
}
}
}
}
else
{
lean_object* x_70; size_t x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_11, 1);
x_71 = lean_ctor_get_usize(x_11, 2);
lean_inc(x_70);
lean_dec(x_11);
x_72 = l_Lean_mkAppStx___closed__1;
x_73 = lean_string_dec_eq(x_70, x_72);
lean_dec(x_70);
if (x_73 == 0)
{
lean_object* x_74; 
lean_free_object(x_10);
lean_dec(x_26);
lean_free_object(x_9);
lean_dec(x_22);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_dec(x_15);
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_2);
x_74 = lean_apply_1(x_3, x_1);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_75 = x_1;
} else {
 lean_dec_ref(x_1);
 x_75 = lean_box(0);
}
x_76 = l_Lean_mkAppStx___closed__3;
x_77 = lean_string_dec_eq(x_26, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_2);
x_78 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_78, 0, x_12);
lean_ctor_set(x_78, 1, x_72);
lean_ctor_set_usize(x_78, 2, x_71);
lean_ctor_set(x_10, 0, x_78);
if (lean_is_scalar(x_75)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_75;
}
lean_ctor_set(x_79, 0, x_5);
lean_ctor_set(x_79, 1, x_13);
x_80 = lean_apply_1(x_3, x_79);
return x_80;
}
else
{
lean_object* x_81; uint8_t x_82; 
lean_dec(x_26);
x_81 = l_Lean_mkAppStx___closed__5;
x_82 = lean_string_dec_eq(x_22, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_2);
x_83 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_83, 0, x_12);
lean_ctor_set(x_83, 1, x_72);
lean_ctor_set_usize(x_83, 2, x_71);
lean_ctor_set(x_10, 1, x_76);
lean_ctor_set(x_10, 0, x_83);
if (lean_is_scalar(x_75)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_75;
}
lean_ctor_set(x_84, 0, x_5);
lean_ctor_set(x_84, 1, x_13);
x_85 = lean_apply_1(x_3, x_84);
return x_85;
}
else
{
lean_object* x_86; uint8_t x_87; 
lean_dec(x_22);
x_86 = l_Lean_mkHole___closed__1;
x_87 = lean_string_dec_eq(x_18, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_2);
x_88 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_88, 0, x_12);
lean_ctor_set(x_88, 1, x_72);
lean_ctor_set_usize(x_88, 2, x_71);
lean_ctor_set(x_10, 1, x_76);
lean_ctor_set(x_10, 0, x_88);
lean_ctor_set(x_9, 1, x_81);
if (lean_is_scalar(x_75)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_75;
}
lean_ctor_set(x_89, 0, x_5);
lean_ctor_set(x_89, 1, x_13);
x_90 = lean_apply_1(x_3, x_89);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_75);
lean_free_object(x_10);
lean_free_object(x_9);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_free_object(x_5);
lean_dec(x_3);
x_91 = lean_box_usize(x_71);
x_92 = lean_box_usize(x_27);
x_93 = lean_box_usize(x_23);
x_94 = lean_box_usize(x_19);
x_95 = lean_apply_6(x_2, x_15, x_13, x_91, x_92, x_93, x_94);
return x_95;
}
}
}
}
}
}
else
{
lean_object* x_96; size_t x_97; lean_object* x_98; size_t x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_96 = lean_ctor_get(x_10, 1);
x_97 = lean_ctor_get_usize(x_10, 2);
lean_inc(x_96);
lean_dec(x_10);
x_98 = lean_ctor_get(x_11, 1);
lean_inc(x_98);
x_99 = lean_ctor_get_usize(x_11, 2);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_100 = x_11;
} else {
 lean_dec_ref(x_11);
 x_100 = lean_box(0);
}
x_101 = l_Lean_mkAppStx___closed__1;
x_102 = lean_string_dec_eq(x_98, x_101);
lean_dec(x_98);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_100);
lean_dec(x_96);
lean_free_object(x_9);
lean_dec(x_22);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_dec(x_15);
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_2);
x_103 = lean_apply_1(x_3, x_1);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_104 = x_1;
} else {
 lean_dec_ref(x_1);
 x_104 = lean_box(0);
}
x_105 = l_Lean_mkAppStx___closed__3;
x_106 = lean_string_dec_eq(x_96, x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_2);
if (lean_is_scalar(x_100)) {
 x_107 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_107 = x_100;
}
lean_ctor_set(x_107, 0, x_12);
lean_ctor_set(x_107, 1, x_101);
lean_ctor_set_usize(x_107, 2, x_99);
x_108 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_96);
lean_ctor_set_usize(x_108, 2, x_97);
lean_ctor_set(x_9, 0, x_108);
if (lean_is_scalar(x_104)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_104;
}
lean_ctor_set(x_109, 0, x_5);
lean_ctor_set(x_109, 1, x_13);
x_110 = lean_apply_1(x_3, x_109);
return x_110;
}
else
{
lean_object* x_111; uint8_t x_112; 
lean_dec(x_96);
x_111 = l_Lean_mkAppStx___closed__5;
x_112 = lean_string_dec_eq(x_22, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_2);
if (lean_is_scalar(x_100)) {
 x_113 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_113 = x_100;
}
lean_ctor_set(x_113, 0, x_12);
lean_ctor_set(x_113, 1, x_101);
lean_ctor_set_usize(x_113, 2, x_99);
x_114 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_105);
lean_ctor_set_usize(x_114, 2, x_97);
lean_ctor_set(x_9, 0, x_114);
if (lean_is_scalar(x_104)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_104;
}
lean_ctor_set(x_115, 0, x_5);
lean_ctor_set(x_115, 1, x_13);
x_116 = lean_apply_1(x_3, x_115);
return x_116;
}
else
{
lean_object* x_117; uint8_t x_118; 
lean_dec(x_22);
x_117 = l_Lean_mkHole___closed__1;
x_118 = lean_string_dec_eq(x_18, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_2);
if (lean_is_scalar(x_100)) {
 x_119 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_119 = x_100;
}
lean_ctor_set(x_119, 0, x_12);
lean_ctor_set(x_119, 1, x_101);
lean_ctor_set_usize(x_119, 2, x_99);
x_120 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_105);
lean_ctor_set_usize(x_120, 2, x_97);
lean_ctor_set(x_9, 1, x_111);
lean_ctor_set(x_9, 0, x_120);
if (lean_is_scalar(x_104)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_104;
}
lean_ctor_set(x_121, 0, x_5);
lean_ctor_set(x_121, 1, x_13);
x_122 = lean_apply_1(x_3, x_121);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_104);
lean_dec(x_100);
lean_free_object(x_9);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_free_object(x_5);
lean_dec(x_3);
x_123 = lean_box_usize(x_99);
x_124 = lean_box_usize(x_97);
x_125 = lean_box_usize(x_23);
x_126 = lean_box_usize(x_19);
x_127 = lean_apply_6(x_2, x_15, x_13, x_123, x_124, x_125, x_126);
return x_127;
}
}
}
}
}
}
else
{
lean_object* x_128; size_t x_129; lean_object* x_130; size_t x_131; lean_object* x_132; lean_object* x_133; size_t x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_128 = lean_ctor_get(x_9, 1);
x_129 = lean_ctor_get_usize(x_9, 2);
lean_inc(x_128);
lean_dec(x_9);
x_130 = lean_ctor_get(x_10, 1);
lean_inc(x_130);
x_131 = lean_ctor_get_usize(x_10, 2);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_132 = x_10;
} else {
 lean_dec_ref(x_10);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_11, 1);
lean_inc(x_133);
x_134 = lean_ctor_get_usize(x_11, 2);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_135 = x_11;
} else {
 lean_dec_ref(x_11);
 x_135 = lean_box(0);
}
x_136 = l_Lean_mkAppStx___closed__1;
x_137 = lean_string_dec_eq(x_133, x_136);
lean_dec(x_133);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_135);
lean_dec(x_132);
lean_dec(x_130);
lean_dec(x_128);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_dec(x_15);
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_2);
x_138 = lean_apply_1(x_3, x_1);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_139 = x_1;
} else {
 lean_dec_ref(x_1);
 x_139 = lean_box(0);
}
x_140 = l_Lean_mkAppStx___closed__3;
x_141 = lean_string_dec_eq(x_130, x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_2);
if (lean_is_scalar(x_135)) {
 x_142 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_142 = x_135;
}
lean_ctor_set(x_142, 0, x_12);
lean_ctor_set(x_142, 1, x_136);
lean_ctor_set_usize(x_142, 2, x_134);
if (lean_is_scalar(x_132)) {
 x_143 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_143 = x_132;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_130);
lean_ctor_set_usize(x_143, 2, x_131);
x_144 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_128);
lean_ctor_set_usize(x_144, 2, x_129);
lean_ctor_set(x_8, 0, x_144);
if (lean_is_scalar(x_139)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_139;
}
lean_ctor_set(x_145, 0, x_5);
lean_ctor_set(x_145, 1, x_13);
x_146 = lean_apply_1(x_3, x_145);
return x_146;
}
else
{
lean_object* x_147; uint8_t x_148; 
lean_dec(x_130);
x_147 = l_Lean_mkAppStx___closed__5;
x_148 = lean_string_dec_eq(x_128, x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_2);
if (lean_is_scalar(x_135)) {
 x_149 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_149 = x_135;
}
lean_ctor_set(x_149, 0, x_12);
lean_ctor_set(x_149, 1, x_136);
lean_ctor_set_usize(x_149, 2, x_134);
if (lean_is_scalar(x_132)) {
 x_150 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_150 = x_132;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_140);
lean_ctor_set_usize(x_150, 2, x_131);
x_151 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_128);
lean_ctor_set_usize(x_151, 2, x_129);
lean_ctor_set(x_8, 0, x_151);
if (lean_is_scalar(x_139)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_139;
}
lean_ctor_set(x_152, 0, x_5);
lean_ctor_set(x_152, 1, x_13);
x_153 = lean_apply_1(x_3, x_152);
return x_153;
}
else
{
lean_object* x_154; uint8_t x_155; 
lean_dec(x_128);
x_154 = l_Lean_mkHole___closed__1;
x_155 = lean_string_dec_eq(x_18, x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_2);
if (lean_is_scalar(x_135)) {
 x_156 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_156 = x_135;
}
lean_ctor_set(x_156, 0, x_12);
lean_ctor_set(x_156, 1, x_136);
lean_ctor_set_usize(x_156, 2, x_134);
if (lean_is_scalar(x_132)) {
 x_157 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_157 = x_132;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_140);
lean_ctor_set_usize(x_157, 2, x_131);
x_158 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_147);
lean_ctor_set_usize(x_158, 2, x_129);
lean_ctor_set(x_8, 0, x_158);
if (lean_is_scalar(x_139)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_139;
}
lean_ctor_set(x_159, 0, x_5);
lean_ctor_set(x_159, 1, x_13);
x_160 = lean_apply_1(x_3, x_159);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_139);
lean_dec(x_135);
lean_dec(x_132);
lean_free_object(x_8);
lean_dec(x_18);
lean_free_object(x_7);
lean_free_object(x_5);
lean_dec(x_3);
x_161 = lean_box_usize(x_134);
x_162 = lean_box_usize(x_131);
x_163 = lean_box_usize(x_129);
x_164 = lean_box_usize(x_19);
x_165 = lean_apply_6(x_2, x_15, x_13, x_161, x_162, x_163, x_164);
return x_165;
}
}
}
}
}
}
else
{
lean_object* x_166; size_t x_167; lean_object* x_168; size_t x_169; lean_object* x_170; lean_object* x_171; size_t x_172; lean_object* x_173; lean_object* x_174; size_t x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_166 = lean_ctor_get(x_8, 1);
x_167 = lean_ctor_get_usize(x_8, 2);
lean_inc(x_166);
lean_dec(x_8);
x_168 = lean_ctor_get(x_9, 1);
lean_inc(x_168);
x_169 = lean_ctor_get_usize(x_9, 2);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_170 = x_9;
} else {
 lean_dec_ref(x_9);
 x_170 = lean_box(0);
}
x_171 = lean_ctor_get(x_10, 1);
lean_inc(x_171);
x_172 = lean_ctor_get_usize(x_10, 2);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_173 = x_10;
} else {
 lean_dec_ref(x_10);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_11, 1);
lean_inc(x_174);
x_175 = lean_ctor_get_usize(x_11, 2);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_176 = x_11;
} else {
 lean_dec_ref(x_11);
 x_176 = lean_box(0);
}
x_177 = l_Lean_mkAppStx___closed__1;
x_178 = lean_string_dec_eq(x_174, x_177);
lean_dec(x_174);
if (x_178 == 0)
{
lean_object* x_179; 
lean_dec(x_176);
lean_dec(x_173);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_168);
lean_dec(x_166);
lean_free_object(x_7);
lean_dec(x_15);
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_2);
x_179 = lean_apply_1(x_3, x_1);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_180 = x_1;
} else {
 lean_dec_ref(x_1);
 x_180 = lean_box(0);
}
x_181 = l_Lean_mkAppStx___closed__3;
x_182 = lean_string_dec_eq(x_171, x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_2);
if (lean_is_scalar(x_176)) {
 x_183 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_183 = x_176;
}
lean_ctor_set(x_183, 0, x_12);
lean_ctor_set(x_183, 1, x_177);
lean_ctor_set_usize(x_183, 2, x_175);
if (lean_is_scalar(x_173)) {
 x_184 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_184 = x_173;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_171);
lean_ctor_set_usize(x_184, 2, x_172);
if (lean_is_scalar(x_170)) {
 x_185 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_185 = x_170;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_168);
lean_ctor_set_usize(x_185, 2, x_169);
x_186 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_166);
lean_ctor_set_usize(x_186, 2, x_167);
lean_ctor_set(x_7, 0, x_186);
if (lean_is_scalar(x_180)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_180;
}
lean_ctor_set(x_187, 0, x_5);
lean_ctor_set(x_187, 1, x_13);
x_188 = lean_apply_1(x_3, x_187);
return x_188;
}
else
{
lean_object* x_189; uint8_t x_190; 
lean_dec(x_171);
x_189 = l_Lean_mkAppStx___closed__5;
x_190 = lean_string_dec_eq(x_168, x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_2);
if (lean_is_scalar(x_176)) {
 x_191 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_191 = x_176;
}
lean_ctor_set(x_191, 0, x_12);
lean_ctor_set(x_191, 1, x_177);
lean_ctor_set_usize(x_191, 2, x_175);
if (lean_is_scalar(x_173)) {
 x_192 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_192 = x_173;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_181);
lean_ctor_set_usize(x_192, 2, x_172);
if (lean_is_scalar(x_170)) {
 x_193 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_193 = x_170;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_168);
lean_ctor_set_usize(x_193, 2, x_169);
x_194 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_166);
lean_ctor_set_usize(x_194, 2, x_167);
lean_ctor_set(x_7, 0, x_194);
if (lean_is_scalar(x_180)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_180;
}
lean_ctor_set(x_195, 0, x_5);
lean_ctor_set(x_195, 1, x_13);
x_196 = lean_apply_1(x_3, x_195);
return x_196;
}
else
{
lean_object* x_197; uint8_t x_198; 
lean_dec(x_168);
x_197 = l_Lean_mkHole___closed__1;
x_198 = lean_string_dec_eq(x_166, x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_2);
if (lean_is_scalar(x_176)) {
 x_199 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_199 = x_176;
}
lean_ctor_set(x_199, 0, x_12);
lean_ctor_set(x_199, 1, x_177);
lean_ctor_set_usize(x_199, 2, x_175);
if (lean_is_scalar(x_173)) {
 x_200 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_200 = x_173;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_181);
lean_ctor_set_usize(x_200, 2, x_172);
if (lean_is_scalar(x_170)) {
 x_201 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_201 = x_170;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_189);
lean_ctor_set_usize(x_201, 2, x_169);
x_202 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_166);
lean_ctor_set_usize(x_202, 2, x_167);
lean_ctor_set(x_7, 0, x_202);
if (lean_is_scalar(x_180)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_180;
}
lean_ctor_set(x_203, 0, x_5);
lean_ctor_set(x_203, 1, x_13);
x_204 = lean_apply_1(x_3, x_203);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_180);
lean_dec(x_176);
lean_dec(x_173);
lean_dec(x_170);
lean_dec(x_166);
lean_free_object(x_7);
lean_free_object(x_5);
lean_dec(x_3);
x_205 = lean_box_usize(x_175);
x_206 = lean_box_usize(x_172);
x_207 = lean_box_usize(x_169);
x_208 = lean_box_usize(x_167);
x_209 = lean_apply_6(x_2, x_15, x_13, x_205, x_206, x_207, x_208);
return x_209;
}
}
}
}
}
}
else
{
lean_object* x_210; lean_object* x_211; size_t x_212; lean_object* x_213; lean_object* x_214; size_t x_215; lean_object* x_216; lean_object* x_217; size_t x_218; lean_object* x_219; lean_object* x_220; size_t x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_210 = lean_ctor_get(x_7, 1);
lean_inc(x_210);
lean_dec(x_7);
x_211 = lean_ctor_get(x_8, 1);
lean_inc(x_211);
x_212 = lean_ctor_get_usize(x_8, 2);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_213 = x_8;
} else {
 lean_dec_ref(x_8);
 x_213 = lean_box(0);
}
x_214 = lean_ctor_get(x_9, 1);
lean_inc(x_214);
x_215 = lean_ctor_get_usize(x_9, 2);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_216 = x_9;
} else {
 lean_dec_ref(x_9);
 x_216 = lean_box(0);
}
x_217 = lean_ctor_get(x_10, 1);
lean_inc(x_217);
x_218 = lean_ctor_get_usize(x_10, 2);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_219 = x_10;
} else {
 lean_dec_ref(x_10);
 x_219 = lean_box(0);
}
x_220 = lean_ctor_get(x_11, 1);
lean_inc(x_220);
x_221 = lean_ctor_get_usize(x_11, 2);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_222 = x_11;
} else {
 lean_dec_ref(x_11);
 x_222 = lean_box(0);
}
x_223 = l_Lean_mkAppStx___closed__1;
x_224 = lean_string_dec_eq(x_220, x_223);
lean_dec(x_220);
if (x_224 == 0)
{
lean_object* x_225; 
lean_dec(x_222);
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_2);
x_225 = lean_apply_1(x_3, x_1);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_226 = x_1;
} else {
 lean_dec_ref(x_1);
 x_226 = lean_box(0);
}
x_227 = l_Lean_mkAppStx___closed__3;
x_228 = lean_string_dec_eq(x_217, x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_2);
if (lean_is_scalar(x_222)) {
 x_229 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_229 = x_222;
}
lean_ctor_set(x_229, 0, x_12);
lean_ctor_set(x_229, 1, x_223);
lean_ctor_set_usize(x_229, 2, x_221);
if (lean_is_scalar(x_219)) {
 x_230 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_230 = x_219;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_217);
lean_ctor_set_usize(x_230, 2, x_218);
if (lean_is_scalar(x_216)) {
 x_231 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_231 = x_216;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_214);
lean_ctor_set_usize(x_231, 2, x_215);
if (lean_is_scalar(x_213)) {
 x_232 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_232 = x_213;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_211);
lean_ctor_set_usize(x_232, 2, x_212);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_210);
lean_ctor_set(x_5, 0, x_233);
if (lean_is_scalar(x_226)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_226;
}
lean_ctor_set(x_234, 0, x_5);
lean_ctor_set(x_234, 1, x_13);
x_235 = lean_apply_1(x_3, x_234);
return x_235;
}
else
{
lean_object* x_236; uint8_t x_237; 
lean_dec(x_217);
x_236 = l_Lean_mkAppStx___closed__5;
x_237 = lean_string_dec_eq(x_214, x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_2);
if (lean_is_scalar(x_222)) {
 x_238 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_238 = x_222;
}
lean_ctor_set(x_238, 0, x_12);
lean_ctor_set(x_238, 1, x_223);
lean_ctor_set_usize(x_238, 2, x_221);
if (lean_is_scalar(x_219)) {
 x_239 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_239 = x_219;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_227);
lean_ctor_set_usize(x_239, 2, x_218);
if (lean_is_scalar(x_216)) {
 x_240 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_240 = x_216;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_214);
lean_ctor_set_usize(x_240, 2, x_215);
if (lean_is_scalar(x_213)) {
 x_241 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_241 = x_213;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_211);
lean_ctor_set_usize(x_241, 2, x_212);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_210);
lean_ctor_set(x_5, 0, x_242);
if (lean_is_scalar(x_226)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_226;
}
lean_ctor_set(x_243, 0, x_5);
lean_ctor_set(x_243, 1, x_13);
x_244 = lean_apply_1(x_3, x_243);
return x_244;
}
else
{
lean_object* x_245; uint8_t x_246; 
lean_dec(x_214);
x_245 = l_Lean_mkHole___closed__1;
x_246 = lean_string_dec_eq(x_211, x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_2);
if (lean_is_scalar(x_222)) {
 x_247 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_247 = x_222;
}
lean_ctor_set(x_247, 0, x_12);
lean_ctor_set(x_247, 1, x_223);
lean_ctor_set_usize(x_247, 2, x_221);
if (lean_is_scalar(x_219)) {
 x_248 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_248 = x_219;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_227);
lean_ctor_set_usize(x_248, 2, x_218);
if (lean_is_scalar(x_216)) {
 x_249 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_249 = x_216;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_236);
lean_ctor_set_usize(x_249, 2, x_215);
if (lean_is_scalar(x_213)) {
 x_250 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_250 = x_213;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_211);
lean_ctor_set_usize(x_250, 2, x_212);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_210);
lean_ctor_set(x_5, 0, x_251);
if (lean_is_scalar(x_226)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_226;
}
lean_ctor_set(x_252, 0, x_5);
lean_ctor_set(x_252, 1, x_13);
x_253 = lean_apply_1(x_3, x_252);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_226);
lean_dec(x_222);
lean_dec(x_219);
lean_dec(x_216);
lean_dec(x_213);
lean_dec(x_211);
lean_free_object(x_5);
lean_dec(x_3);
x_254 = lean_box_usize(x_221);
x_255 = lean_box_usize(x_218);
x_256 = lean_box_usize(x_215);
x_257 = lean_box_usize(x_212);
x_258 = lean_apply_6(x_2, x_210, x_13, x_254, x_255, x_256, x_257);
return x_258;
}
}
}
}
}
}
else
{
lean_object* x_259; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_free_object(x_5);
lean_dec(x_7);
lean_dec(x_2);
x_259 = lean_apply_1(x_3, x_1);
return x_259;
}
}
else
{
lean_object* x_260; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_free_object(x_5);
lean_dec(x_7);
lean_dec(x_2);
x_260 = lean_apply_1(x_3, x_1);
return x_260;
}
}
else
{
lean_object* x_261; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_free_object(x_5);
lean_dec(x_7);
lean_dec(x_2);
x_261 = lean_apply_1(x_3, x_1);
return x_261;
}
}
else
{
lean_object* x_262; 
lean_dec(x_9);
lean_dec(x_8);
lean_free_object(x_5);
lean_dec(x_7);
lean_dec(x_2);
x_262 = lean_apply_1(x_3, x_1);
return x_262;
}
}
else
{
lean_object* x_263; 
lean_dec(x_8);
lean_free_object(x_5);
lean_dec(x_7);
lean_dec(x_2);
x_263 = lean_apply_1(x_3, x_1);
return x_263;
}
}
else
{
lean_object* x_264; 
lean_free_object(x_5);
lean_dec(x_7);
lean_dec(x_2);
x_264 = lean_apply_1(x_3, x_1);
return x_264;
}
}
else
{
lean_object* x_265; 
x_265 = lean_ctor_get(x_5, 0);
lean_inc(x_265);
lean_dec(x_5);
if (lean_obj_tag(x_265) == 1)
{
lean_object* x_266; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
if (lean_obj_tag(x_266) == 1)
{
lean_object* x_267; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
if (lean_obj_tag(x_267) == 1)
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
if (lean_obj_tag(x_268) == 1)
{
lean_object* x_269; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
if (lean_obj_tag(x_269) == 1)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; size_t x_275; lean_object* x_276; lean_object* x_277; size_t x_278; lean_object* x_279; lean_object* x_280; size_t x_281; lean_object* x_282; lean_object* x_283; size_t x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_271 = lean_ctor_get(x_1, 1);
lean_inc(x_271);
x_272 = lean_ctor_get(x_265, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_273 = x_265;
} else {
 lean_dec_ref(x_265);
 x_273 = lean_box(0);
}
x_274 = lean_ctor_get(x_266, 1);
lean_inc(x_274);
x_275 = lean_ctor_get_usize(x_266, 2);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_276 = x_266;
} else {
 lean_dec_ref(x_266);
 x_276 = lean_box(0);
}
x_277 = lean_ctor_get(x_267, 1);
lean_inc(x_277);
x_278 = lean_ctor_get_usize(x_267, 2);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_279 = x_267;
} else {
 lean_dec_ref(x_267);
 x_279 = lean_box(0);
}
x_280 = lean_ctor_get(x_268, 1);
lean_inc(x_280);
x_281 = lean_ctor_get_usize(x_268, 2);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_282 = x_268;
} else {
 lean_dec_ref(x_268);
 x_282 = lean_box(0);
}
x_283 = lean_ctor_get(x_269, 1);
lean_inc(x_283);
x_284 = lean_ctor_get_usize(x_269, 2);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_285 = x_269;
} else {
 lean_dec_ref(x_269);
 x_285 = lean_box(0);
}
x_286 = l_Lean_mkAppStx___closed__1;
x_287 = lean_string_dec_eq(x_283, x_286);
lean_dec(x_283);
if (x_287 == 0)
{
lean_object* x_288; 
lean_dec(x_285);
lean_dec(x_282);
lean_dec(x_280);
lean_dec(x_279);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_2);
x_288 = lean_apply_1(x_3, x_1);
return x_288;
}
else
{
lean_object* x_289; lean_object* x_290; uint8_t x_291; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_289 = x_1;
} else {
 lean_dec_ref(x_1);
 x_289 = lean_box(0);
}
x_290 = l_Lean_mkAppStx___closed__3;
x_291 = lean_string_dec_eq(x_280, x_290);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_2);
if (lean_is_scalar(x_285)) {
 x_292 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_292 = x_285;
}
lean_ctor_set(x_292, 0, x_270);
lean_ctor_set(x_292, 1, x_286);
lean_ctor_set_usize(x_292, 2, x_284);
if (lean_is_scalar(x_282)) {
 x_293 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_293 = x_282;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_280);
lean_ctor_set_usize(x_293, 2, x_281);
if (lean_is_scalar(x_279)) {
 x_294 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_294 = x_279;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_277);
lean_ctor_set_usize(x_294, 2, x_278);
if (lean_is_scalar(x_276)) {
 x_295 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_295 = x_276;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_274);
lean_ctor_set_usize(x_295, 2, x_275);
if (lean_is_scalar(x_273)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_273;
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_272);
x_297 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_297, 0, x_296);
if (lean_is_scalar(x_289)) {
 x_298 = lean_alloc_ctor(1, 2, 0);
} else {
 x_298 = x_289;
}
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_271);
x_299 = lean_apply_1(x_3, x_298);
return x_299;
}
else
{
lean_object* x_300; uint8_t x_301; 
lean_dec(x_280);
x_300 = l_Lean_mkAppStx___closed__5;
x_301 = lean_string_dec_eq(x_277, x_300);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_2);
if (lean_is_scalar(x_285)) {
 x_302 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_302 = x_285;
}
lean_ctor_set(x_302, 0, x_270);
lean_ctor_set(x_302, 1, x_286);
lean_ctor_set_usize(x_302, 2, x_284);
if (lean_is_scalar(x_282)) {
 x_303 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_303 = x_282;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_290);
lean_ctor_set_usize(x_303, 2, x_281);
if (lean_is_scalar(x_279)) {
 x_304 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_304 = x_279;
}
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_277);
lean_ctor_set_usize(x_304, 2, x_278);
if (lean_is_scalar(x_276)) {
 x_305 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_305 = x_276;
}
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_274);
lean_ctor_set_usize(x_305, 2, x_275);
if (lean_is_scalar(x_273)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_273;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_272);
x_307 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_307, 0, x_306);
if (lean_is_scalar(x_289)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_289;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_271);
x_309 = lean_apply_1(x_3, x_308);
return x_309;
}
else
{
lean_object* x_310; uint8_t x_311; 
lean_dec(x_277);
x_310 = l_Lean_mkHole___closed__1;
x_311 = lean_string_dec_eq(x_274, x_310);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_2);
if (lean_is_scalar(x_285)) {
 x_312 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_312 = x_285;
}
lean_ctor_set(x_312, 0, x_270);
lean_ctor_set(x_312, 1, x_286);
lean_ctor_set_usize(x_312, 2, x_284);
if (lean_is_scalar(x_282)) {
 x_313 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_313 = x_282;
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_290);
lean_ctor_set_usize(x_313, 2, x_281);
if (lean_is_scalar(x_279)) {
 x_314 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_314 = x_279;
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_300);
lean_ctor_set_usize(x_314, 2, x_278);
if (lean_is_scalar(x_276)) {
 x_315 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_315 = x_276;
}
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_274);
lean_ctor_set_usize(x_315, 2, x_275);
if (lean_is_scalar(x_273)) {
 x_316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_316 = x_273;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_272);
x_317 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_317, 0, x_316);
if (lean_is_scalar(x_289)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_289;
}
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_271);
x_319 = lean_apply_1(x_3, x_318);
return x_319;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_289);
lean_dec(x_285);
lean_dec(x_282);
lean_dec(x_279);
lean_dec(x_276);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_3);
x_320 = lean_box_usize(x_284);
x_321 = lean_box_usize(x_281);
x_322 = lean_box_usize(x_278);
x_323 = lean_box_usize(x_275);
x_324 = lean_apply_6(x_2, x_272, x_271, x_320, x_321, x_322, x_323);
return x_324;
}
}
}
}
}
else
{
lean_object* x_325; 
lean_dec(x_270);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_2);
x_325 = lean_apply_1(x_3, x_1);
return x_325;
}
}
else
{
lean_object* x_326; 
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_2);
x_326 = lean_apply_1(x_3, x_1);
return x_326;
}
}
else
{
lean_object* x_327; 
lean_dec(x_268);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_2);
x_327 = lean_apply_1(x_3, x_1);
return x_327;
}
}
else
{
lean_object* x_328; 
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_2);
x_328 = lean_apply_1(x_3, x_1);
return x_328;
}
}
else
{
lean_object* x_329; 
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_2);
x_329 = lean_apply_1(x_3, x_1);
return x_329;
}
}
else
{
lean_object* x_330; 
lean_dec(x_265);
lean_dec(x_2);
x_330 = lean_apply_1(x_3, x_1);
return x_330;
}
}
}
else
{
lean_object* x_331; 
lean_dec(x_5);
lean_dec(x_2);
x_331 = lean_apply_1(x_3, x_1);
return x_331;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_9, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_dec(x_23);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_33 = l_Lean_mkAppStx___closed__1;
x_34 = lean_string_dec_eq(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
x_35 = 0;
x_36 = lean_box(x_35);
lean_ctor_set(x_9, 0, x_36);
return x_9;
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_mkAppStx___closed__3;
x_38 = lean_string_dec_eq(x_31, x_37);
lean_dec(x_31);
if (x_38 == 0)
{
uint8_t x_39; lean_object* x_40; 
lean_dec(x_30);
lean_dec(x_29);
x_39 = 0;
x_40 = lean_box(x_39);
lean_ctor_set(x_9, 0, x_40);
return x_9;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_mkAppStx___closed__5;
x_42 = lean_string_dec_eq(x_30, x_41);
lean_dec(x_30);
if (x_42 == 0)
{
uint8_t x_43; lean_object* x_44; 
lean_dec(x_29);
x_43 = 0;
x_44 = lean_box(x_43);
lean_ctor_set(x_9, 0, x_44);
return x_9;
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_Lean_mkHole___closed__1;
x_46 = lean_string_dec_eq(x_29, x_45);
lean_dec(x_29);
if (x_46 == 0)
{
uint8_t x_47; lean_object* x_48; 
x_47 = 0;
x_48 = lean_box(x_47);
lean_ctor_set(x_9, 0, x_48);
return x_9;
}
else
{
uint8_t x_49; lean_object* x_50; 
x_49 = 1;
x_50 = lean_box(x_49);
lean_ctor_set(x_9, 0, x_50);
return x_9;
}
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_51 = lean_ctor_get(x_9, 1);
lean_inc(x_51);
lean_dec(x_9);
x_52 = lean_ctor_get(x_22, 1);
lean_inc(x_52);
lean_dec(x_22);
x_53 = lean_ctor_get(x_23, 1);
lean_inc(x_53);
lean_dec(x_23);
x_54 = lean_ctor_get(x_24, 1);
lean_inc(x_54);
lean_dec(x_24);
x_55 = lean_ctor_get(x_25, 1);
lean_inc(x_55);
lean_dec(x_25);
x_56 = l_Lean_mkAppStx___closed__1;
x_57 = lean_string_dec_eq(x_55, x_56);
lean_dec(x_55);
if (x_57 == 0)
{
uint8_t x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
x_58 = 0;
x_59 = lean_box(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_51);
return x_60;
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = l_Lean_mkAppStx___closed__3;
x_62 = lean_string_dec_eq(x_54, x_61);
lean_dec(x_54);
if (x_62 == 0)
{
uint8_t x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_53);
lean_dec(x_52);
x_63 = 0;
x_64 = lean_box(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_51);
return x_65;
}
else
{
lean_object* x_66; uint8_t x_67; 
x_66 = l_Lean_mkAppStx___closed__5;
x_67 = lean_string_dec_eq(x_53, x_66);
lean_dec(x_53);
if (x_67 == 0)
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_52);
x_68 = 0;
x_69 = lean_box(x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_51);
return x_70;
}
else
{
lean_object* x_71; uint8_t x_72; 
x_71 = l_Lean_mkHole___closed__1;
x_72 = lean_string_dec_eq(x_52, x_71);
lean_dec(x_52);
if (x_72 == 0)
{
uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_73 = 0;
x_74 = lean_box(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_51);
return x_75;
}
else
{
uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_76 = 1;
x_77 = lean_box(x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_51);
return x_78;
}
}
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_79 = !lean_is_exclusive(x_9);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_9, 0);
lean_dec(x_80);
x_81 = 0;
x_82 = lean_box(x_81);
lean_ctor_set(x_9, 0, x_82);
return x_9;
}
else
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_9, 1);
lean_inc(x_83);
lean_dec(x_9);
x_84 = 0;
x_85 = lean_box(x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_87 = !lean_is_exclusive(x_9);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_9, 0);
lean_dec(x_88);
x_89 = 0;
x_90 = lean_box(x_89);
lean_ctor_set(x_9, 0, x_90);
return x_9;
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_9, 1);
lean_inc(x_91);
lean_dec(x_9);
x_92 = 0;
x_93 = lean_box(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_95 = !lean_is_exclusive(x_9);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_9, 0);
lean_dec(x_96);
x_97 = 0;
x_98 = lean_box(x_97);
lean_ctor_set(x_9, 0, x_98);
return x_9;
}
else
{
lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_9, 1);
lean_inc(x_99);
lean_dec(x_9);
x_100 = 0;
x_101 = lean_box(x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_23);
lean_dec(x_22);
x_103 = !lean_is_exclusive(x_9);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_9, 0);
lean_dec(x_104);
x_105 = 0;
x_106 = lean_box(x_105);
lean_ctor_set(x_9, 0, x_106);
return x_9;
}
else
{
lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_9, 1);
lean_inc(x_107);
lean_dec(x_9);
x_108 = 0;
x_109 = lean_box(x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_22);
x_111 = !lean_is_exclusive(x_9);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_9, 0);
lean_dec(x_112);
x_113 = 0;
x_114 = lean_box(x_113);
lean_ctor_set(x_9, 0, x_114);
return x_9;
}
else
{
lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_9, 1);
lean_inc(x_115);
lean_dec(x_9);
x_116 = 0;
x_117 = lean_box(x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_21);
x_119 = !lean_is_exclusive(x_9);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_9, 0);
lean_dec(x_120);
x_121 = 0;
x_122 = lean_box(x_121);
lean_ctor_set(x_9, 0, x_122);
return x_9;
}
else
{
lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_9, 1);
lean_inc(x_123);
lean_dec(x_9);
x_124 = 0;
x_125 = lean_box(x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_123);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_20);
x_127 = !lean_is_exclusive(x_9);
if (x_127 == 0)
{
lean_object* x_128; uint8_t x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_9, 0);
lean_dec(x_128);
x_129 = 0;
x_130 = lean_box(x_129);
lean_ctor_set(x_9, 0, x_130);
return x_9;
}
else
{
lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_9, 1);
lean_inc(x_131);
lean_dec(x_9);
x_132 = 0;
x_133 = lean_box(x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_131);
return x_134;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_1);
x_16 = l_Lean_mkApp(x_14, x_1);
x_17 = l_Lean_Expr_bindingBody_x21(x_15);
lean_dec(x_15);
x_18 = lean_expr_instantiate1(x_17, x_1);
lean_dec(x_1);
lean_dec(x_17);
lean_ctor_set(x_11, 1, x_18);
lean_ctor_set(x_11, 0, x_16);
x_19 = lean_st_ref_set(x_2, x_11, x_12);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_26 = lean_ctor_get_uint8(x_11, sizeof(void*)*9);
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
x_29 = lean_ctor_get(x_11, 2);
x_30 = lean_ctor_get(x_11, 3);
x_31 = lean_ctor_get_uint8(x_11, sizeof(void*)*9 + 1);
x_32 = lean_ctor_get(x_11, 4);
x_33 = lean_ctor_get(x_11, 5);
x_34 = lean_ctor_get(x_11, 6);
x_35 = lean_ctor_get(x_11, 7);
x_36 = lean_ctor_get(x_11, 8);
x_37 = lean_ctor_get_uint8(x_11, sizeof(void*)*9 + 2);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
lean_inc(x_1);
x_38 = l_Lean_mkApp(x_27, x_1);
x_39 = l_Lean_Expr_bindingBody_x21(x_28);
lean_dec(x_28);
x_40 = lean_expr_instantiate1(x_39, x_1);
lean_dec(x_1);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_29);
lean_ctor_set(x_41, 3, x_30);
lean_ctor_set(x_41, 4, x_32);
lean_ctor_set(x_41, 5, x_33);
lean_ctor_set(x_41, 6, x_34);
lean_ctor_set(x_41, 7, x_35);
lean_ctor_set(x_41, 8, x_36);
lean_ctor_set_uint8(x_41, sizeof(void*)*9, x_26);
lean_ctor_set_uint8(x_41, sizeof(void*)*9 + 1, x_31);
lean_ctor_set_uint8(x_41, sizeof(void*)*9 + 2, x_37);
x_42 = lean_st_ref_set(x_2, x_41, x_12);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_box(0);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_18 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Elab_Term_elabTerm(x_16, x_17, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ensureArgType(x_22, x_20, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_13, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_dec(x_13);
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_ctor_get(x_11, 0);
lean_inc(x_38);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_39 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ensureArgType(x_38, x_37, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_4, x_3);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fget(x_2, x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = l_Lean_Expr_getOptParamDefault_x3f(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = l_Lean_Expr_getAutoParamTactic_x3f(x_20);
lean_dec(x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_18);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_4 = x_25;
x_12 = x_21;
goto _start;
}
else
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_27 = 1;
x_28 = lean_box(x_27);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
}
else
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_29 = 1;
x_30 = lean_box(x_29);
lean_ctor_set(x_18, 0, x_30);
return x_18;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_33 = l_Lean_Expr_getOptParamDefault_x3f(x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = l_Lean_Expr_getAutoParamTactic_x3f(x_31);
lean_dec(x_31);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_4 = x_36;
x_12 = x_32;
goto _start;
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_34);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_38 = 1;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_41 = 1;
x_42 = lean_box(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_32);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_18);
if (x_44 == 0)
{
return x_18;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_18, 0);
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_18);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_10(x_1, x_5, x_6, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg___lambda__1), 11, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(x_1, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1(x_1, x_1, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___lambda__1___boxed), 10, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
x_11 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_fTypeHasOptAutoParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
x_14 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(x_12, x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_14;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_dec(x_5);
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_7(x_4, x_1, x_2, x_3, x_9, x_10, x_11, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = lean_apply_3(x_6, x_1, x_2, x_3);
return x_15;
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_6);
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
x_19 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_20 = lean_box_uint64(x_19);
x_21 = lean_apply_7(x_4, x_7, x_2, x_3, x_16, x_17, x_18, x_20);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_4);
x_22 = lean_apply_1(x_5, x_3);
return x_22;
}
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
x_26 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_27 = lean_box_uint64(x_26);
x_28 = lean_apply_7(x_4, x_7, x_2, x_3, x_23, x_24, x_25, x_27);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_4);
x_29 = lean_apply_3(x_6, x_7, x_2, x_3);
return x_29;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__2___rarg), 6, 0);
return x_2;
}
}
uint8_t l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_name_eq(x_3, x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1___boxed), 2, 1);
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
x_31 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1___boxed), 2, 1);
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
x_48 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1___boxed), 2, 1);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__2___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_dec(x_4);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__2(x_1, x_5);
lean_dec(x_1);
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
}
case 5:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_4);
x_10 = l_Lean_FindMVar_visit(x_4, x_8, x_3);
x_11 = l_Lean_FindMVar_visit(x_4, x_9, x_10);
lean_dec(x_10);
return x_11;
}
case 6:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_4);
x_14 = l_Lean_FindMVar_visit(x_4, x_12, x_3);
x_15 = l_Lean_FindMVar_visit(x_4, x_13, x_14);
lean_dec(x_14);
return x_15;
}
case 7:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_4);
x_18 = l_Lean_FindMVar_visit(x_4, x_16, x_3);
x_19 = l_Lean_FindMVar_visit(x_4, x_17, x_18);
lean_dec(x_18);
return x_19;
}
case 8:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 3);
lean_inc(x_22);
lean_dec(x_2);
lean_inc(x_4);
x_23 = l_Lean_FindMVar_visit(x_4, x_20, x_3);
lean_inc(x_4);
x_24 = l_Lean_FindMVar_visit(x_4, x_21, x_23);
lean_dec(x_23);
x_25 = l_Lean_FindMVar_visit(x_4, x_22, x_24);
lean_dec(x_24);
return x_25;
}
case 10:
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
x_27 = l_Lean_FindMVar_visit(x_4, x_26, x_3);
return x_27;
}
case 11:
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_dec(x_2);
x_29 = l_Lean_FindMVar_visit(x_4, x_28, x_3);
return x_29;
}
default: 
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
}
}
}
uint8_t l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__2(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
lean_object* l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_dec(x_4);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__2(x_1, x_5);
lean_dec(x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_dec(x_5);
return x_3;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
}
case 5:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_4);
x_10 = l_Lean_FindMVar_visit(x_4, x_8, x_3);
x_11 = l_Lean_FindMVar_visit(x_4, x_9, x_10);
lean_dec(x_10);
return x_11;
}
case 6:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_4);
x_14 = l_Lean_FindMVar_visit(x_4, x_12, x_3);
x_15 = l_Lean_FindMVar_visit(x_4, x_13, x_14);
lean_dec(x_14);
return x_15;
}
case 7:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_4);
x_18 = l_Lean_FindMVar_visit(x_4, x_16, x_3);
x_19 = l_Lean_FindMVar_visit(x_4, x_17, x_18);
lean_dec(x_18);
return x_19;
}
case 8:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 3);
lean_inc(x_22);
lean_dec(x_2);
lean_inc(x_4);
x_23 = l_Lean_FindMVar_visit(x_4, x_20, x_3);
lean_inc(x_4);
x_24 = l_Lean_FindMVar_visit(x_4, x_21, x_23);
lean_dec(x_23);
x_25 = l_Lean_FindMVar_visit(x_4, x_22, x_24);
lean_dec(x_24);
return x_25;
}
case 10:
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
x_27 = l_Lean_FindMVar_visit(x_4, x_26, x_3);
return x_27;
}
case 11:
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_dec(x_2);
x_29 = l_Lean_FindMVar_visit(x_4, x_28, x_3);
return x_29;
}
default: 
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
}
}
}
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; 
lean_inc(x_2);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_isExprDefEqAux), 8, 2);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
x_422 = lean_st_ref_get(x_9, x_10);
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_423, 3);
lean_inc(x_424);
lean_dec(x_423);
x_425 = lean_ctor_get_uint8(x_424, sizeof(void*)*1);
lean_dec(x_424);
if (x_425 == 0)
{
lean_object* x_426; uint8_t x_427; 
x_426 = lean_ctor_get(x_422, 1);
lean_inc(x_426);
lean_dec(x_422);
x_427 = 0;
x_21 = x_427;
x_22 = x_426;
goto block_421;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; 
x_428 = lean_ctor_get(x_422, 1);
lean_inc(x_428);
lean_dec(x_422);
x_429 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_430 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_429, x_6, x_7, x_8, x_9, x_428);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
lean_dec(x_430);
x_433 = lean_unbox(x_431);
lean_dec(x_431);
x_21 = x_433;
x_22 = x_432;
goto block_421;
}
block_19:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
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
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
block_421:
{
if (x_21 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_st_ref_get(x_9, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 3);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get_uint8(x_25, sizeof(void*)*1);
lean_dec(x_25);
x_28 = lean_st_ref_take(x_9, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 3);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_87; 
x_35 = 0;
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_35);
x_36 = lean_st_ref_set(x_9, x_29, x_31);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_87 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_runDefEqM(x_20, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_118 = lean_st_ref_get(x_9, x_89);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_119, 3);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_ctor_get_uint8(x_120, sizeof(void*)*1);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
lean_dec(x_118);
x_90 = x_35;
x_91 = x_122;
goto block_117;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_123 = lean_ctor_get(x_118, 1);
lean_inc(x_123);
lean_dec(x_118);
x_124 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_125 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_124, x_6, x_7, x_8, x_9, x_123);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_unbox(x_126);
lean_dec(x_126);
x_90 = x_128;
x_91 = x_127;
goto block_117;
}
block_117:
{
if (x_90 == 0)
{
uint8_t x_92; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_92 = lean_unbox(x_88);
lean_dec(x_88);
x_38 = x_92;
x_39 = x_91;
goto block_86;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_93 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_93, 0, x_1);
x_94 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_95 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_97 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_98, 0, x_2);
x_99 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__2;
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_unbox(x_88);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_103 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__4;
x_104 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_94);
x_106 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_107 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_106, x_105, x_6, x_7, x_8, x_9, x_91);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_unbox(x_88);
lean_dec(x_88);
x_38 = x_109;
x_39 = x_108;
goto block_86;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_110 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6;
x_111 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_111, 0, x_101);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_94);
x_113 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_114 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_113, x_112, x_6, x_7, x_8, x_9, x_91);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_unbox(x_88);
lean_dec(x_88);
x_38 = x_116;
x_39 = x_115;
goto block_86;
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_129 = lean_ctor_get(x_87, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_87, 1);
lean_inc(x_130);
lean_dec(x_87);
x_131 = lean_st_ref_get(x_9, x_130);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_st_ref_take(x_9, x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_134, 3);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_137 = !lean_is_exclusive(x_134);
if (x_137 == 0)
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_134, 3);
lean_dec(x_138);
x_139 = !lean_is_exclusive(x_135);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; 
lean_ctor_set_uint8(x_135, sizeof(void*)*1, x_27);
x_140 = lean_st_ref_set(x_9, x_134, x_136);
lean_dec(x_9);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_140, 0);
lean_dec(x_142);
lean_ctor_set_tag(x_140, 1);
lean_ctor_set(x_140, 0, x_129);
return x_140;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_129);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_145 = lean_ctor_get(x_135, 0);
lean_inc(x_145);
lean_dec(x_135);
x_146 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set_uint8(x_146, sizeof(void*)*1, x_27);
lean_ctor_set(x_134, 3, x_146);
x_147 = lean_st_ref_set(x_9, x_134, x_136);
lean_dec(x_9);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_149 = x_147;
} else {
 lean_dec_ref(x_147);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
 lean_ctor_set_tag(x_150, 1);
}
lean_ctor_set(x_150, 0, x_129);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_151 = lean_ctor_get(x_134, 0);
x_152 = lean_ctor_get(x_134, 1);
x_153 = lean_ctor_get(x_134, 2);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_134);
x_154 = lean_ctor_get(x_135, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_155 = x_135;
} else {
 lean_dec_ref(x_135);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 1, 1);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_27);
x_157 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_157, 0, x_151);
lean_ctor_set(x_157, 1, x_152);
lean_ctor_set(x_157, 2, x_153);
lean_ctor_set(x_157, 3, x_156);
x_158 = lean_st_ref_set(x_9, x_157, x_136);
lean_dec(x_9);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_160 = x_158;
} else {
 lean_dec_ref(x_158);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
 lean_ctor_set_tag(x_161, 1);
}
lean_ctor_set(x_161, 0, x_129);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
block_86:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_40 = lean_st_ref_get(x_9, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 3);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get_uint8(x_43, sizeof(void*)*1);
lean_dec(x_43);
x_45 = lean_st_ref_take(x_9, x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_46, 3);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_27);
x_52 = lean_st_ref_set(x_9, x_46, x_48);
lean_dec(x_9);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
x_55 = lean_box(x_38);
x_56 = lean_box(x_44);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_52, 0, x_57);
x_11 = x_52;
goto block_19;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_dec(x_52);
x_59 = lean_box(x_38);
x_60 = lean_box(x_44);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
x_11 = x_62;
goto block_19;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_47, 0);
lean_inc(x_63);
lean_dec(x_47);
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_27);
lean_ctor_set(x_46, 3, x_64);
x_65 = lean_st_ref_set(x_9, x_46, x_48);
lean_dec(x_9);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(x_38);
x_69 = lean_box(x_44);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
if (lean_is_scalar(x_67)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_67;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_66);
x_11 = x_71;
goto block_19;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_72 = lean_ctor_get(x_46, 0);
x_73 = lean_ctor_get(x_46, 1);
x_74 = lean_ctor_get(x_46, 2);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_46);
x_75 = lean_ctor_get(x_47, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_76 = x_47;
} else {
 lean_dec_ref(x_47);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 1, 1);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_27);
x_78 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set(x_78, 1, x_73);
lean_ctor_set(x_78, 2, x_74);
lean_ctor_set(x_78, 3, x_77);
x_79 = lean_st_ref_set(x_9, x_78, x_48);
lean_dec(x_9);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_81 = x_79;
} else {
 lean_dec_ref(x_79);
 x_81 = lean_box(0);
}
x_82 = lean_box(x_38);
x_83 = lean_box(x_44);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
if (lean_is_scalar(x_81)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_81;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
x_11 = x_85;
goto block_19;
}
}
}
else
{
lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_194; 
x_162 = lean_ctor_get(x_30, 0);
lean_inc(x_162);
lean_dec(x_30);
x_163 = 0;
x_164 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*1, x_163);
lean_ctor_set(x_29, 3, x_164);
x_165 = lean_st_ref_set(x_9, x_29, x_31);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_194 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_runDefEqM(x_20, x_6, x_7, x_8, x_9, x_166);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_225 = lean_st_ref_get(x_9, x_196);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_226, 3);
lean_inc(x_227);
lean_dec(x_226);
x_228 = lean_ctor_get_uint8(x_227, sizeof(void*)*1);
lean_dec(x_227);
if (x_228 == 0)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_225, 1);
lean_inc(x_229);
lean_dec(x_225);
x_197 = x_163;
x_198 = x_229;
goto block_224;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_230 = lean_ctor_get(x_225, 1);
lean_inc(x_230);
lean_dec(x_225);
x_231 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_232 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_231, x_6, x_7, x_8, x_9, x_230);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_unbox(x_233);
lean_dec(x_233);
x_197 = x_235;
x_198 = x_234;
goto block_224;
}
block_224:
{
if (x_197 == 0)
{
uint8_t x_199; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_199 = lean_unbox(x_195);
lean_dec(x_195);
x_167 = x_199;
x_168 = x_198;
goto block_193;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_200 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_200, 0, x_1);
x_201 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_202 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_200);
x_203 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_204 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_205, 0, x_2);
x_206 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
x_207 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__2;
x_208 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_unbox(x_195);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_210 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__4;
x_211 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_201);
x_213 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_214 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_213, x_212, x_6, x_7, x_8, x_9, x_198);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
x_216 = lean_unbox(x_195);
lean_dec(x_195);
x_167 = x_216;
x_168 = x_215;
goto block_193;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_217 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6;
x_218 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_218, 0, x_208);
lean_ctor_set(x_218, 1, x_217);
x_219 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_201);
x_220 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_221 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_220, x_219, x_6, x_7, x_8, x_9, x_198);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
lean_dec(x_221);
x_223 = lean_unbox(x_195);
lean_dec(x_195);
x_167 = x_223;
x_168 = x_222;
goto block_193;
}
}
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_236 = lean_ctor_get(x_194, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_194, 1);
lean_inc(x_237);
lean_dec(x_194);
x_238 = lean_st_ref_get(x_9, x_237);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec(x_238);
x_240 = lean_st_ref_take(x_9, x_239);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_241, 3);
lean_inc(x_242);
x_243 = lean_ctor_get(x_240, 1);
lean_inc(x_243);
lean_dec(x_240);
x_244 = lean_ctor_get(x_241, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_241, 1);
lean_inc(x_245);
x_246 = lean_ctor_get(x_241, 2);
lean_inc(x_246);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 lean_ctor_release(x_241, 2);
 lean_ctor_release(x_241, 3);
 x_247 = x_241;
} else {
 lean_dec_ref(x_241);
 x_247 = lean_box(0);
}
x_248 = lean_ctor_get(x_242, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 x_249 = x_242;
} else {
 lean_dec_ref(x_242);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(0, 1, 1);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set_uint8(x_250, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_247)) {
 x_251 = lean_alloc_ctor(0, 4, 0);
} else {
 x_251 = x_247;
}
lean_ctor_set(x_251, 0, x_244);
lean_ctor_set(x_251, 1, x_245);
lean_ctor_set(x_251, 2, x_246);
lean_ctor_set(x_251, 3, x_250);
x_252 = lean_st_ref_set(x_9, x_251, x_243);
lean_dec(x_9);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_254 = x_252;
} else {
 lean_dec_ref(x_252);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_254;
 lean_ctor_set_tag(x_255, 1);
}
lean_ctor_set(x_255, 0, x_236);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
block_193:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_169 = lean_st_ref_get(x_9, x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_ctor_get(x_170, 3);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get_uint8(x_172, sizeof(void*)*1);
lean_dec(x_172);
x_174 = lean_st_ref_take(x_9, x_171);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_175, 3);
lean_inc(x_176);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
lean_dec(x_174);
x_178 = lean_ctor_get(x_175, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_175, 2);
lean_inc(x_180);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 lean_ctor_release(x_175, 2);
 lean_ctor_release(x_175, 3);
 x_181 = x_175;
} else {
 lean_dec_ref(x_175);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_176, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_183 = x_176;
} else {
 lean_dec_ref(x_176);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(0, 1, 1);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set_uint8(x_184, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_181)) {
 x_185 = lean_alloc_ctor(0, 4, 0);
} else {
 x_185 = x_181;
}
lean_ctor_set(x_185, 0, x_178);
lean_ctor_set(x_185, 1, x_179);
lean_ctor_set(x_185, 2, x_180);
lean_ctor_set(x_185, 3, x_184);
x_186 = lean_st_ref_set(x_9, x_185, x_177);
lean_dec(x_9);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_188 = x_186;
} else {
 lean_dec_ref(x_186);
 x_188 = lean_box(0);
}
x_189 = lean_box(x_167);
x_190 = lean_box(x_173);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
if (lean_is_scalar(x_188)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_188;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_187);
x_11 = x_192;
goto block_19;
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; lean_object* x_293; 
x_256 = lean_ctor_get(x_29, 0);
x_257 = lean_ctor_get(x_29, 1);
x_258 = lean_ctor_get(x_29, 2);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_29);
x_259 = lean_ctor_get(x_30, 0);
lean_inc(x_259);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_260 = x_30;
} else {
 lean_dec_ref(x_30);
 x_260 = lean_box(0);
}
x_261 = 0;
if (lean_is_scalar(x_260)) {
 x_262 = lean_alloc_ctor(0, 1, 1);
} else {
 x_262 = x_260;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set_uint8(x_262, sizeof(void*)*1, x_261);
x_263 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_263, 0, x_256);
lean_ctor_set(x_263, 1, x_257);
lean_ctor_set(x_263, 2, x_258);
lean_ctor_set(x_263, 3, x_262);
x_264 = lean_st_ref_set(x_9, x_263, x_31);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec(x_264);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_293 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_runDefEqM(x_20, x_6, x_7, x_8, x_9, x_265);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
x_324 = lean_st_ref_get(x_9, x_295);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_325, 3);
lean_inc(x_326);
lean_dec(x_325);
x_327 = lean_ctor_get_uint8(x_326, sizeof(void*)*1);
lean_dec(x_326);
if (x_327 == 0)
{
lean_object* x_328; 
x_328 = lean_ctor_get(x_324, 1);
lean_inc(x_328);
lean_dec(x_324);
x_296 = x_261;
x_297 = x_328;
goto block_323;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_329 = lean_ctor_get(x_324, 1);
lean_inc(x_329);
lean_dec(x_324);
x_330 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_331 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_330, x_6, x_7, x_8, x_9, x_329);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = lean_unbox(x_332);
lean_dec(x_332);
x_296 = x_334;
x_297 = x_333;
goto block_323;
}
block_323:
{
if (x_296 == 0)
{
uint8_t x_298; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_298 = lean_unbox(x_294);
lean_dec(x_294);
x_266 = x_298;
x_267 = x_297;
goto block_292;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_299 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_299, 0, x_1);
x_300 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_301 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_299);
x_302 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_303 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_304, 0, x_2);
x_305 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
x_306 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__2;
x_307 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_unbox(x_294);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_309 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__4;
x_310 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_300);
x_312 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_313 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_312, x_311, x_6, x_7, x_8, x_9, x_297);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec(x_313);
x_315 = lean_unbox(x_294);
lean_dec(x_294);
x_266 = x_315;
x_267 = x_314;
goto block_292;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
x_316 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6;
x_317 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_317, 0, x_307);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_300);
x_319 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_320 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_319, x_318, x_6, x_7, x_8, x_9, x_297);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
lean_dec(x_320);
x_322 = lean_unbox(x_294);
lean_dec(x_294);
x_266 = x_322;
x_267 = x_321;
goto block_292;
}
}
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_335 = lean_ctor_get(x_293, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_293, 1);
lean_inc(x_336);
lean_dec(x_293);
x_337 = lean_st_ref_get(x_9, x_336);
x_338 = lean_ctor_get(x_337, 1);
lean_inc(x_338);
lean_dec(x_337);
x_339 = lean_st_ref_take(x_9, x_338);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_340, 3);
lean_inc(x_341);
x_342 = lean_ctor_get(x_339, 1);
lean_inc(x_342);
lean_dec(x_339);
x_343 = lean_ctor_get(x_340, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_340, 1);
lean_inc(x_344);
x_345 = lean_ctor_get(x_340, 2);
lean_inc(x_345);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_346 = x_340;
} else {
 lean_dec_ref(x_340);
 x_346 = lean_box(0);
}
x_347 = lean_ctor_get(x_341, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 x_348 = x_341;
} else {
 lean_dec_ref(x_341);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(0, 1, 1);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set_uint8(x_349, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_346)) {
 x_350 = lean_alloc_ctor(0, 4, 0);
} else {
 x_350 = x_346;
}
lean_ctor_set(x_350, 0, x_343);
lean_ctor_set(x_350, 1, x_344);
lean_ctor_set(x_350, 2, x_345);
lean_ctor_set(x_350, 3, x_349);
x_351 = lean_st_ref_set(x_9, x_350, x_342);
lean_dec(x_9);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_353 = x_351;
} else {
 lean_dec_ref(x_351);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 2, 0);
} else {
 x_354 = x_353;
 lean_ctor_set_tag(x_354, 1);
}
lean_ctor_set(x_354, 0, x_335);
lean_ctor_set(x_354, 1, x_352);
return x_354;
}
block_292:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_268 = lean_st_ref_get(x_9, x_267);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = lean_ctor_get(x_269, 3);
lean_inc(x_271);
lean_dec(x_269);
x_272 = lean_ctor_get_uint8(x_271, sizeof(void*)*1);
lean_dec(x_271);
x_273 = lean_st_ref_take(x_9, x_270);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_274, 3);
lean_inc(x_275);
x_276 = lean_ctor_get(x_273, 1);
lean_inc(x_276);
lean_dec(x_273);
x_277 = lean_ctor_get(x_274, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_274, 1);
lean_inc(x_278);
x_279 = lean_ctor_get(x_274, 2);
lean_inc(x_279);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 lean_ctor_release(x_274, 2);
 lean_ctor_release(x_274, 3);
 x_280 = x_274;
} else {
 lean_dec_ref(x_274);
 x_280 = lean_box(0);
}
x_281 = lean_ctor_get(x_275, 0);
lean_inc(x_281);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 x_282 = x_275;
} else {
 lean_dec_ref(x_275);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(0, 1, 1);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set_uint8(x_283, sizeof(void*)*1, x_27);
if (lean_is_scalar(x_280)) {
 x_284 = lean_alloc_ctor(0, 4, 0);
} else {
 x_284 = x_280;
}
lean_ctor_set(x_284, 0, x_277);
lean_ctor_set(x_284, 1, x_278);
lean_ctor_set(x_284, 2, x_279);
lean_ctor_set(x_284, 3, x_283);
x_285 = lean_st_ref_set(x_9, x_284, x_276);
lean_dec(x_9);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_287 = x_285;
} else {
 lean_dec_ref(x_285);
 x_287 = lean_box(0);
}
x_288 = lean_box(x_266);
x_289 = lean_box(x_272);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
if (lean_is_scalar(x_287)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_287;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_286);
x_11 = x_291;
goto block_19;
}
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; lean_object* x_370; 
x_355 = lean_ctor_get(x_8, 3);
lean_inc(x_355);
x_356 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_isLevelDefEq___spec__3___rarg(x_9, x_22);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_370 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_runDefEqM(x_20, x_6, x_7, x_8, x_9, x_358);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_401 = lean_st_ref_get(x_9, x_372);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_402, 3);
lean_inc(x_403);
lean_dec(x_402);
x_404 = lean_ctor_get_uint8(x_403, sizeof(void*)*1);
lean_dec(x_403);
if (x_404 == 0)
{
lean_object* x_405; uint8_t x_406; 
x_405 = lean_ctor_get(x_401, 1);
lean_inc(x_405);
lean_dec(x_401);
x_406 = 0;
x_373 = x_406;
x_374 = x_405;
goto block_400;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; 
x_407 = lean_ctor_get(x_401, 1);
lean_inc(x_407);
lean_dec(x_401);
x_408 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_409 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_408, x_6, x_7, x_8, x_9, x_407);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
x_412 = lean_unbox(x_410);
lean_dec(x_410);
x_373 = x_412;
x_374 = x_411;
goto block_400;
}
block_400:
{
if (x_373 == 0)
{
uint8_t x_375; 
lean_dec(x_2);
lean_dec(x_1);
x_375 = lean_unbox(x_371);
lean_dec(x_371);
x_359 = x_375;
x_360 = x_374;
goto block_369;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_376 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_376, 0, x_1);
x_377 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_378 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_376);
x_379 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_380 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
x_381 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_381, 0, x_2);
x_382 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
x_383 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__2;
x_384 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
x_385 = lean_unbox(x_371);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; 
x_386 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__4;
x_387 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_386);
x_388 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_377);
x_389 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_390 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_389, x_388, x_6, x_7, x_8, x_9, x_374);
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
lean_dec(x_390);
x_392 = lean_unbox(x_371);
lean_dec(x_371);
x_359 = x_392;
x_360 = x_391;
goto block_369;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; 
x_393 = l_Lean_Meta_isLevelDefEq___rarg___lambda__3___closed__6;
x_394 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_394, 0, x_384);
lean_ctor_set(x_394, 1, x_393);
x_395 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_377);
x_396 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_397 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEq___spec__2(x_396, x_395, x_6, x_7, x_8, x_9, x_374);
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
lean_dec(x_397);
x_399 = lean_unbox(x_371);
lean_dec(x_371);
x_359 = x_399;
x_360 = x_398;
goto block_369;
}
}
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; 
lean_dec(x_2);
lean_dec(x_1);
x_413 = lean_ctor_get(x_370, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_370, 1);
lean_inc(x_414);
lean_dec(x_370);
x_415 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_416 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_isLevelDefEq___spec__4(x_357, x_415, x_355, x_6, x_7, x_8, x_9, x_414);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_417 = !lean_is_exclusive(x_416);
if (x_417 == 0)
{
lean_object* x_418; 
x_418 = lean_ctor_get(x_416, 0);
lean_dec(x_418);
lean_ctor_set_tag(x_416, 1);
lean_ctor_set(x_416, 0, x_413);
return x_416;
}
else
{
lean_object* x_419; lean_object* x_420; 
x_419 = lean_ctor_get(x_416, 1);
lean_inc(x_419);
lean_dec(x_416);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_413);
lean_ctor_set(x_420, 1, x_419);
return x_420;
}
}
block_369:
{
lean_object* x_361; lean_object* x_362; uint8_t x_363; 
x_361 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_362 = l___private_Lean_Util_Trace_0__Lean_addNode___at_Lean_Meta_isLevelDefEq___spec__4(x_357, x_361, x_355, x_6, x_7, x_8, x_9, x_360);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_363 = !lean_is_exclusive(x_362);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; 
x_364 = lean_ctor_get(x_362, 0);
lean_dec(x_364);
x_365 = lean_box(x_359);
lean_ctor_set(x_362, 0, x_365);
return x_362;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_362, 1);
lean_inc(x_366);
lean_dec(x_362);
x_367 = lean_box(x_359);
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_366);
return x_368;
}
}
}
}
}
}
lean_object* l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_Meta_Basic___instance__10___spec__1(x_2, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_9, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_16, 3);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_13);
lean_inc(x_11);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Std_PersistentArray_push___rarg(x_22, x_24);
lean_ctor_set(x_17, 0, x_25);
x_26 = lean_st_ref_set(x_9, x_16, x_18);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
x_34 = lean_ctor_get(x_17, 0);
lean_inc(x_34);
lean_dec(x_17);
x_35 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_13);
lean_inc(x_11);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_11);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Std_PersistentArray_push___rarg(x_34, x_36);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_33);
lean_ctor_set(x_16, 3, x_38);
x_39 = lean_st_ref_set(x_9, x_16, x_18);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_44 = lean_ctor_get(x_16, 0);
x_45 = lean_ctor_get(x_16, 1);
x_46 = lean_ctor_get(x_16, 2);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_16);
x_47 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
x_48 = lean_ctor_get(x_17, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_49 = x_17;
} else {
 lean_dec_ref(x_17);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_50, 0, x_1);
lean_ctor_set(x_50, 1, x_13);
lean_inc(x_11);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_11);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Std_PersistentArray_push___rarg(x_48, x_51);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(0, 1, 1);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_47);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_45);
lean_ctor_set(x_54, 2, x_46);
lean_ctor_set(x_54, 3, x_53);
x_55 = lean_st_ref_set(x_9, x_54, x_18);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_box(0);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_Lean_checkTraceOption(x_10, x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_899____closed__1;
x_2 = l_Lean_mkAppStx___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("propagateExpectedType");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1;
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("etaArgs.size: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", numRemainingArgs: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", fType: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_10, 5);
lean_inc(x_15);
x_16 = l_Array_isEmpty___rarg(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
uint8_t x_18; 
x_18 = lean_ctor_get_uint8(x_10, sizeof(void*)*9 + 2);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_10, 8);
lean_inc(x_19);
x_20 = l_Array_isEmpty___rarg(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_free_object(x_9);
x_21 = lean_st_ref_take(x_1, x_13);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = 1;
lean_ctor_set_uint8(x_22, sizeof(void*)*9 + 2, x_25);
x_26 = lean_st_ref_set(x_1, x_22, x_23);
x_27 = lean_ctor_get(x_10, 4);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_166; lean_object* x_167; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_35 = x_26;
} else {
 lean_dec_ref(x_26);
 x_35 = lean_box(0);
}
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_ctor_get(x_10, 2);
lean_inc(x_37);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_List_lengthAux___main___rarg(x_37, x_38);
lean_dec(x_37);
x_189 = lean_st_ref_get(x_7, x_34);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_190, 3);
lean_inc(x_191);
lean_dec(x_190);
x_192 = lean_ctor_get_uint8(x_191, sizeof(void*)*1);
lean_dec(x_191);
if (x_192 == 0)
{
lean_object* x_193; uint8_t x_194; 
x_193 = lean_ctor_get(x_189, 1);
lean_inc(x_193);
lean_dec(x_189);
x_194 = 0;
x_166 = x_194;
x_167 = x_193;
goto block_188;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_195 = lean_ctor_get(x_189, 1);
lean_inc(x_195);
lean_dec(x_189);
x_196 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_197 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_196, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_195);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = lean_unbox(x_198);
lean_dec(x_198);
x_166 = x_200;
x_167 = x_199;
goto block_188;
}
block_165:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_dec(x_10);
x_43 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody(x_39, x_41, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_36);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_35;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l_Lean_Expr_hasLooseBVars(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(0);
lean_inc(x_46);
lean_inc(x_19);
x_49 = l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_19, x_46, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_46);
lean_dec(x_36);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_35;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_40);
return x_51;
}
else
{
lean_object* x_52; 
lean_dec(x_49);
lean_inc(x_46);
x_52 = l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_19, x_46, x_48);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_35);
x_53 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_46);
x_54 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(x_46, x_53, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_40);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; uint8_t x_94; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
x_94 = lean_unbox(x_56);
lean_dec(x_56);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
lean_free_object(x_54);
x_95 = lean_st_ref_get(x_7, x_57);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_96, 3);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_ctor_get_uint8(x_97, sizeof(void*)*1);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
lean_dec(x_95);
x_100 = 0;
x_58 = x_100;
x_59 = x_99;
goto block_93;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
lean_dec(x_95);
x_102 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_103 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_102, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_101);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_unbox(x_104);
lean_dec(x_104);
x_58 = x_106;
x_59 = x_105;
goto block_93;
}
}
else
{
lean_object* x_107; 
lean_dec(x_46);
lean_dec(x_36);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = lean_box(0);
lean_ctor_set(x_54, 0, x_107);
return x_54;
}
block_93:
{
if (x_58 == 0)
{
lean_object* x_60; 
x_60 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_36, x_46, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_59);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
x_63 = lean_box(0);
lean_ctor_set(x_60, 0, x_63);
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec(x_60);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_60);
if (x_67 == 0)
{
return x_60;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_60, 0);
x_69 = lean_ctor_get(x_60, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_60);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_inc(x_36);
x_71 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_71, 0, x_36);
x_72 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_46);
x_76 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_76, 0, x_46);
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_72);
x_79 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_80 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_79, x_78, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_59);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_36, x_46, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_81);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 0);
lean_dec(x_84);
x_85 = lean_box(0);
lean_ctor_set(x_82, 0, x_85);
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_82);
if (x_89 == 0)
{
return x_82;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_82, 0);
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_82);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; uint8_t x_142; 
x_108 = lean_ctor_get(x_54, 0);
x_109 = lean_ctor_get(x_54, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_54);
x_142 = lean_unbox(x_108);
lean_dec(x_108);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_143 = lean_st_ref_get(x_7, x_109);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_144, 3);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_ctor_get_uint8(x_145, sizeof(void*)*1);
lean_dec(x_145);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
lean_dec(x_143);
x_148 = 0;
x_110 = x_148;
x_111 = x_147;
goto block_141;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_149 = lean_ctor_get(x_143, 1);
lean_inc(x_149);
lean_dec(x_143);
x_150 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_151 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_150, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_149);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_unbox(x_152);
lean_dec(x_152);
x_110 = x_154;
x_111 = x_153;
goto block_141;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_46);
lean_dec(x_36);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_155 = lean_box(0);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_109);
return x_156;
}
block_141:
{
if (x_110 == 0)
{
lean_object* x_112; 
x_112 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_36, x_46, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_111);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
x_115 = lean_box(0);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_112, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_119 = x_112;
} else {
 lean_dec_ref(x_112);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_inc(x_36);
x_121 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_121, 0, x_36);
x_122 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_123 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_125 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
lean_inc(x_46);
x_126 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_126, 0, x_46);
x_127 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_122);
x_129 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_130 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_129, x_128, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_111);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_36, x_46, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_131);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
x_135 = lean_box(0);
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_133);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_132, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_132, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_139 = x_132;
} else {
 lean_dec_ref(x_132);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_46);
lean_dec(x_36);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_54);
if (x_157 == 0)
{
return x_54;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_54, 0);
x_159 = lean_ctor_get(x_54, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_54);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_52);
lean_dec(x_46);
lean_dec(x_36);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_35;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_40);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_46);
lean_dec(x_36);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_163 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_35;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_40);
return x_164;
}
}
}
block_188:
{
if (x_166 == 0)
{
lean_dec(x_15);
x_40 = x_167;
goto block_165;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_168 = lean_array_get_size(x_15);
lean_dec(x_15);
x_169 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_168);
x_170 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_170, 0, x_169);
x_171 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5;
x_172 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
x_173 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7;
x_174 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
lean_inc(x_39);
x_175 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_39);
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_175);
x_177 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_176);
x_178 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9;
x_179 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_ctor_get(x_10, 1);
lean_inc(x_180);
x_181 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_182 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_181);
x_183 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_184 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
x_185 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_186 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_185, x_184, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_167);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
x_40 = x_187;
goto block_165;
}
}
}
}
else
{
uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_201 = lean_ctor_get_uint8(x_22, sizeof(void*)*9);
x_202 = lean_ctor_get(x_22, 0);
x_203 = lean_ctor_get(x_22, 1);
x_204 = lean_ctor_get(x_22, 2);
x_205 = lean_ctor_get(x_22, 3);
x_206 = lean_ctor_get_uint8(x_22, sizeof(void*)*9 + 1);
x_207 = lean_ctor_get(x_22, 4);
x_208 = lean_ctor_get(x_22, 5);
x_209 = lean_ctor_get(x_22, 6);
x_210 = lean_ctor_get(x_22, 7);
x_211 = lean_ctor_get(x_22, 8);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_22);
x_212 = 1;
x_213 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_213, 0, x_202);
lean_ctor_set(x_213, 1, x_203);
lean_ctor_set(x_213, 2, x_204);
lean_ctor_set(x_213, 3, x_205);
lean_ctor_set(x_213, 4, x_207);
lean_ctor_set(x_213, 5, x_208);
lean_ctor_set(x_213, 6, x_209);
lean_ctor_set(x_213, 7, x_210);
lean_ctor_set(x_213, 8, x_211);
lean_ctor_set_uint8(x_213, sizeof(void*)*9, x_201);
lean_ctor_set_uint8(x_213, sizeof(void*)*9 + 1, x_206);
lean_ctor_set_uint8(x_213, sizeof(void*)*9 + 2, x_212);
x_214 = lean_st_ref_set(x_1, x_213, x_23);
x_215 = lean_ctor_get(x_10, 4);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_217 = x_214;
} else {
 lean_dec_ref(x_214);
 x_217 = lean_box(0);
}
x_218 = lean_box(0);
if (lean_is_scalar(x_217)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_217;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_216);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_300; lean_object* x_301; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_220 = lean_ctor_get(x_214, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_221 = x_214;
} else {
 lean_dec_ref(x_214);
 x_221 = lean_box(0);
}
x_222 = lean_ctor_get(x_215, 0);
lean_inc(x_222);
lean_dec(x_215);
x_223 = lean_ctor_get(x_10, 2);
lean_inc(x_223);
x_224 = lean_unsigned_to_nat(0u);
x_225 = l_List_lengthAux___main___rarg(x_223, x_224);
lean_dec(x_223);
x_323 = lean_st_ref_get(x_7, x_220);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_324, 3);
lean_inc(x_325);
lean_dec(x_324);
x_326 = lean_ctor_get_uint8(x_325, sizeof(void*)*1);
lean_dec(x_325);
if (x_326 == 0)
{
lean_object* x_327; uint8_t x_328; 
x_327 = lean_ctor_get(x_323, 1);
lean_inc(x_327);
lean_dec(x_323);
x_328 = 0;
x_300 = x_328;
x_301 = x_327;
goto block_322;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_329 = lean_ctor_get(x_323, 1);
lean_inc(x_329);
lean_dec(x_323);
x_330 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_331 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_330, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_329);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = lean_unbox(x_332);
lean_dec(x_332);
x_300 = x_334;
x_301 = x_333;
goto block_322;
}
block_299:
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_10, 3);
lean_inc(x_227);
x_228 = lean_ctor_get(x_10, 1);
lean_inc(x_228);
lean_dec(x_10);
x_229 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody(x_225, x_227, x_228);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; 
lean_dec(x_222);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_230 = lean_box(0);
if (lean_is_scalar(x_221)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_221;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_226);
return x_231;
}
else
{
lean_object* x_232; uint8_t x_233; 
x_232 = lean_ctor_get(x_229, 0);
lean_inc(x_232);
lean_dec(x_229);
x_233 = l_Lean_Expr_hasLooseBVars(x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_box(0);
lean_inc(x_232);
lean_inc(x_19);
x_235 = l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_19, x_232, x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_232);
lean_dec(x_222);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_236 = lean_box(0);
if (lean_is_scalar(x_221)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_221;
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_226);
return x_237;
}
else
{
lean_object* x_238; 
lean_dec(x_235);
lean_inc(x_232);
x_238 = l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_19, x_232, x_234);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; 
lean_dec(x_221);
x_239 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_232);
x_240 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(x_232, x_239, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_226);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; uint8_t x_276; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_243 = x_240;
} else {
 lean_dec_ref(x_240);
 x_243 = lean_box(0);
}
x_276 = lean_unbox(x_241);
lean_dec(x_241);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
lean_dec(x_243);
x_277 = lean_st_ref_get(x_7, x_242);
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_278, 3);
lean_inc(x_279);
lean_dec(x_278);
x_280 = lean_ctor_get_uint8(x_279, sizeof(void*)*1);
lean_dec(x_279);
if (x_280 == 0)
{
lean_object* x_281; uint8_t x_282; 
x_281 = lean_ctor_get(x_277, 1);
lean_inc(x_281);
lean_dec(x_277);
x_282 = 0;
x_244 = x_282;
x_245 = x_281;
goto block_275;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_283 = lean_ctor_get(x_277, 1);
lean_inc(x_283);
lean_dec(x_277);
x_284 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_285 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_284, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_283);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_unbox(x_286);
lean_dec(x_286);
x_244 = x_288;
x_245 = x_287;
goto block_275;
}
}
else
{
lean_object* x_289; lean_object* x_290; 
lean_dec(x_232);
lean_dec(x_222);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_289 = lean_box(0);
if (lean_is_scalar(x_243)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_243;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_242);
return x_290;
}
block_275:
{
if (x_244 == 0)
{
lean_object* x_246; 
x_246 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_222, x_232, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_245);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_248 = x_246;
} else {
 lean_dec_ref(x_246);
 x_248 = lean_box(0);
}
x_249 = lean_box(0);
if (lean_is_scalar(x_248)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_248;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_247);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_251 = lean_ctor_get(x_246, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_246, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_253 = x_246;
} else {
 lean_dec_ref(x_246);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
return x_254;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_inc(x_222);
x_255 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_255, 0, x_222);
x_256 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_257 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_255);
x_258 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_259 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
lean_inc(x_232);
x_260 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_260, 0, x_232);
x_261 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
x_262 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_256);
x_263 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_264 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_263, x_262, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_245);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec(x_264);
x_266 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_222, x_232, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_265);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_268 = x_266;
} else {
 lean_dec_ref(x_266);
 x_268 = lean_box(0);
}
x_269 = lean_box(0);
if (lean_is_scalar(x_268)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_268;
}
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_267);
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_266, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_266, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_273 = x_266;
} else {
 lean_dec_ref(x_266);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_232);
lean_dec(x_222);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_291 = lean_ctor_get(x_240, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_240, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_293 = x_240;
} else {
 lean_dec_ref(x_240);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_238);
lean_dec(x_232);
lean_dec(x_222);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_295 = lean_box(0);
if (lean_is_scalar(x_221)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_221;
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_226);
return x_296;
}
}
}
else
{
lean_object* x_297; lean_object* x_298; 
lean_dec(x_232);
lean_dec(x_222);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_297 = lean_box(0);
if (lean_is_scalar(x_221)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_221;
}
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_226);
return x_298;
}
}
}
block_322:
{
if (x_300 == 0)
{
lean_dec(x_15);
x_226 = x_301;
goto block_299;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_302 = lean_array_get_size(x_15);
lean_dec(x_15);
x_303 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_302);
x_304 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_304, 0, x_303);
x_305 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5;
x_306 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_304);
x_307 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7;
x_308 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
lean_inc(x_225);
x_309 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_225);
x_310 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_310, 0, x_309);
x_311 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_310);
x_312 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9;
x_313 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
x_314 = lean_ctor_get(x_10, 1);
lean_inc(x_314);
x_315 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_315, 0, x_314);
x_316 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_316, 0, x_313);
lean_ctor_set(x_316, 1, x_315);
x_317 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_318 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
x_319 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_320 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_319, x_318, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_301);
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
lean_dec(x_320);
x_226 = x_321;
goto block_299;
}
}
}
}
}
else
{
lean_object* x_335; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_335 = lean_box(0);
lean_ctor_set(x_9, 0, x_335);
return x_9;
}
}
else
{
lean_object* x_336; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_336 = lean_box(0);
lean_ctor_set(x_9, 0, x_336);
return x_9;
}
}
}
else
{
lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_337 = lean_ctor_get(x_9, 1);
lean_inc(x_337);
lean_dec(x_9);
x_338 = lean_ctor_get(x_10, 5);
lean_inc(x_338);
x_339 = l_Array_isEmpty___rarg(x_338);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; 
lean_dec(x_338);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_340 = lean_box(0);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_337);
return x_341;
}
else
{
uint8_t x_342; 
x_342 = lean_ctor_get_uint8(x_10, sizeof(void*)*9 + 2);
if (x_342 == 0)
{
lean_object* x_343; uint8_t x_344; 
x_343 = lean_ctor_get(x_10, 8);
lean_inc(x_343);
x_344 = l_Array_isEmpty___rarg(x_343);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_345 = lean_st_ref_take(x_1, x_337);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_348 = lean_ctor_get_uint8(x_346, sizeof(void*)*9);
x_349 = lean_ctor_get(x_346, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_346, 1);
lean_inc(x_350);
x_351 = lean_ctor_get(x_346, 2);
lean_inc(x_351);
x_352 = lean_ctor_get(x_346, 3);
lean_inc(x_352);
x_353 = lean_ctor_get_uint8(x_346, sizeof(void*)*9 + 1);
x_354 = lean_ctor_get(x_346, 4);
lean_inc(x_354);
x_355 = lean_ctor_get(x_346, 5);
lean_inc(x_355);
x_356 = lean_ctor_get(x_346, 6);
lean_inc(x_356);
x_357 = lean_ctor_get(x_346, 7);
lean_inc(x_357);
x_358 = lean_ctor_get(x_346, 8);
lean_inc(x_358);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 lean_ctor_release(x_346, 2);
 lean_ctor_release(x_346, 3);
 lean_ctor_release(x_346, 4);
 lean_ctor_release(x_346, 5);
 lean_ctor_release(x_346, 6);
 lean_ctor_release(x_346, 7);
 lean_ctor_release(x_346, 8);
 x_359 = x_346;
} else {
 lean_dec_ref(x_346);
 x_359 = lean_box(0);
}
x_360 = 1;
if (lean_is_scalar(x_359)) {
 x_361 = lean_alloc_ctor(0, 9, 3);
} else {
 x_361 = x_359;
}
lean_ctor_set(x_361, 0, x_349);
lean_ctor_set(x_361, 1, x_350);
lean_ctor_set(x_361, 2, x_351);
lean_ctor_set(x_361, 3, x_352);
lean_ctor_set(x_361, 4, x_354);
lean_ctor_set(x_361, 5, x_355);
lean_ctor_set(x_361, 6, x_356);
lean_ctor_set(x_361, 7, x_357);
lean_ctor_set(x_361, 8, x_358);
lean_ctor_set_uint8(x_361, sizeof(void*)*9, x_348);
lean_ctor_set_uint8(x_361, sizeof(void*)*9 + 1, x_353);
lean_ctor_set_uint8(x_361, sizeof(void*)*9 + 2, x_360);
x_362 = lean_st_ref_set(x_1, x_361, x_347);
x_363 = lean_ctor_get(x_10, 4);
lean_inc(x_363);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_343);
lean_dec(x_338);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_365 = x_362;
} else {
 lean_dec_ref(x_362);
 x_365 = lean_box(0);
}
x_366 = lean_box(0);
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_364);
return x_367;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_448; lean_object* x_449; lean_object* x_471; lean_object* x_472; lean_object* x_473; uint8_t x_474; 
x_368 = lean_ctor_get(x_362, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_369 = x_362;
} else {
 lean_dec_ref(x_362);
 x_369 = lean_box(0);
}
x_370 = lean_ctor_get(x_363, 0);
lean_inc(x_370);
lean_dec(x_363);
x_371 = lean_ctor_get(x_10, 2);
lean_inc(x_371);
x_372 = lean_unsigned_to_nat(0u);
x_373 = l_List_lengthAux___main___rarg(x_371, x_372);
lean_dec(x_371);
x_471 = lean_st_ref_get(x_7, x_368);
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_472, 3);
lean_inc(x_473);
lean_dec(x_472);
x_474 = lean_ctor_get_uint8(x_473, sizeof(void*)*1);
lean_dec(x_473);
if (x_474 == 0)
{
lean_object* x_475; uint8_t x_476; 
x_475 = lean_ctor_get(x_471, 1);
lean_inc(x_475);
lean_dec(x_471);
x_476 = 0;
x_448 = x_476;
x_449 = x_475;
goto block_470;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; 
x_477 = lean_ctor_get(x_471, 1);
lean_inc(x_477);
lean_dec(x_471);
x_478 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_479 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_478, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_477);
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_479, 1);
lean_inc(x_481);
lean_dec(x_479);
x_482 = lean_unbox(x_480);
lean_dec(x_480);
x_448 = x_482;
x_449 = x_481;
goto block_470;
}
block_447:
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_10, 3);
lean_inc(x_375);
x_376 = lean_ctor_get(x_10, 1);
lean_inc(x_376);
lean_dec(x_10);
x_377 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody(x_373, x_375, x_376);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; 
lean_dec(x_370);
lean_dec(x_343);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_378 = lean_box(0);
if (lean_is_scalar(x_369)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_369;
}
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_374);
return x_379;
}
else
{
lean_object* x_380; uint8_t x_381; 
x_380 = lean_ctor_get(x_377, 0);
lean_inc(x_380);
lean_dec(x_377);
x_381 = l_Lean_Expr_hasLooseBVars(x_380);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_box(0);
lean_inc(x_380);
lean_inc(x_343);
x_383 = l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_343, x_380, x_382);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; 
lean_dec(x_380);
lean_dec(x_370);
lean_dec(x_343);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_384 = lean_box(0);
if (lean_is_scalar(x_369)) {
 x_385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_385 = x_369;
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_374);
return x_385;
}
else
{
lean_object* x_386; 
lean_dec(x_383);
lean_inc(x_380);
x_386 = l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_343, x_380, x_382);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_369);
x_387 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_380);
x_388 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(x_380, x_387, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_374);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; uint8_t x_424; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_391 = x_388;
} else {
 lean_dec_ref(x_388);
 x_391 = lean_box(0);
}
x_424 = lean_unbox(x_389);
lean_dec(x_389);
if (x_424 == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; 
lean_dec(x_391);
x_425 = lean_st_ref_get(x_7, x_390);
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_426, 3);
lean_inc(x_427);
lean_dec(x_426);
x_428 = lean_ctor_get_uint8(x_427, sizeof(void*)*1);
lean_dec(x_427);
if (x_428 == 0)
{
lean_object* x_429; uint8_t x_430; 
x_429 = lean_ctor_get(x_425, 1);
lean_inc(x_429);
lean_dec(x_425);
x_430 = 0;
x_392 = x_430;
x_393 = x_429;
goto block_423;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; 
x_431 = lean_ctor_get(x_425, 1);
lean_inc(x_431);
lean_dec(x_425);
x_432 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_433 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_432, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_431);
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
lean_dec(x_433);
x_436 = lean_unbox(x_434);
lean_dec(x_434);
x_392 = x_436;
x_393 = x_435;
goto block_423;
}
}
else
{
lean_object* x_437; lean_object* x_438; 
lean_dec(x_380);
lean_dec(x_370);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_437 = lean_box(0);
if (lean_is_scalar(x_391)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_391;
}
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_390);
return x_438;
}
block_423:
{
if (x_392 == 0)
{
lean_object* x_394; 
x_394 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_370, x_380, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_393);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_395 = lean_ctor_get(x_394, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_396 = x_394;
} else {
 lean_dec_ref(x_394);
 x_396 = lean_box(0);
}
x_397 = lean_box(0);
if (lean_is_scalar(x_396)) {
 x_398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_398 = x_396;
}
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_395);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_399 = lean_ctor_get(x_394, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_394, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_401 = x_394;
} else {
 lean_dec_ref(x_394);
 x_401 = lean_box(0);
}
if (lean_is_scalar(x_401)) {
 x_402 = lean_alloc_ctor(1, 2, 0);
} else {
 x_402 = x_401;
}
lean_ctor_set(x_402, 0, x_399);
lean_ctor_set(x_402, 1, x_400);
return x_402;
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_inc(x_370);
x_403 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_403, 0, x_370);
x_404 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_405 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_403);
x_406 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_407 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_406);
lean_inc(x_380);
x_408 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_408, 0, x_380);
x_409 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
x_410 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_404);
x_411 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_412 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_411, x_410, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_393);
x_413 = lean_ctor_get(x_412, 1);
lean_inc(x_413);
lean_dec(x_412);
x_414 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_370, x_380, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_413);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_415 = lean_ctor_get(x_414, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_416 = x_414;
} else {
 lean_dec_ref(x_414);
 x_416 = lean_box(0);
}
x_417 = lean_box(0);
if (lean_is_scalar(x_416)) {
 x_418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_418 = x_416;
}
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_415);
return x_418;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_419 = lean_ctor_get(x_414, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_414, 1);
lean_inc(x_420);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_421 = x_414;
} else {
 lean_dec_ref(x_414);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(1, 2, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_420);
return x_422;
}
}
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_380);
lean_dec(x_370);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_439 = lean_ctor_get(x_388, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_388, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_441 = x_388;
} else {
 lean_dec_ref(x_388);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_442 = lean_alloc_ctor(1, 2, 0);
} else {
 x_442 = x_441;
}
lean_ctor_set(x_442, 0, x_439);
lean_ctor_set(x_442, 1, x_440);
return x_442;
}
}
else
{
lean_object* x_443; lean_object* x_444; 
lean_dec(x_386);
lean_dec(x_380);
lean_dec(x_370);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_443 = lean_box(0);
if (lean_is_scalar(x_369)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_369;
}
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_374);
return x_444;
}
}
}
else
{
lean_object* x_445; lean_object* x_446; 
lean_dec(x_380);
lean_dec(x_370);
lean_dec(x_343);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_445 = lean_box(0);
if (lean_is_scalar(x_369)) {
 x_446 = lean_alloc_ctor(0, 2, 0);
} else {
 x_446 = x_369;
}
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_374);
return x_446;
}
}
}
block_470:
{
if (x_448 == 0)
{
lean_dec(x_338);
x_374 = x_449;
goto block_447;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_450 = lean_array_get_size(x_338);
lean_dec(x_338);
x_451 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_450);
x_452 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_452, 0, x_451);
x_453 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5;
x_454 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_452);
x_455 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7;
x_456 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
lean_inc(x_373);
x_457 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_373);
x_458 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_458, 0, x_457);
x_459 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_459, 0, x_456);
lean_ctor_set(x_459, 1, x_458);
x_460 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9;
x_461 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
x_462 = lean_ctor_get(x_10, 1);
lean_inc(x_462);
x_463 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_463, 0, x_462);
x_464 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_464, 0, x_461);
lean_ctor_set(x_464, 1, x_463);
x_465 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_466 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
x_467 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_468 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_467, x_466, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_449);
x_469 = lean_ctor_get(x_468, 1);
lean_inc(x_469);
lean_dec(x_468);
x_374 = x_469;
goto block_447;
}
}
}
}
else
{
lean_object* x_483; lean_object* x_484; 
lean_dec(x_343);
lean_dec(x_338);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_483 = lean_box(0);
x_484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_337);
return x_484;
}
}
else
{
lean_object* x_485; lean_object* x_486; 
lean_dec(x_338);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_485 = lean_box(0);
x_486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_337);
return x_486;
}
}
}
}
else
{
uint8_t x_487; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_487 = !lean_is_exclusive(x_9);
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; 
x_488 = lean_ctor_get(x_9, 0);
lean_dec(x_488);
x_489 = lean_box(0);
lean_ctor_set(x_9, 0, x_489);
return x_9;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_490 = lean_ctor_get(x_9, 1);
lean_inc(x_490);
lean_dec(x_9);
x_491 = lean_box(0);
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_491);
lean_ctor_set(x_492, 1, x_490);
return x_492;
}
}
}
}
lean_object* l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_5, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg___lambda__1), 10, 4);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_6);
lean_closure_set(x_13, 3, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
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
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg___boxed), 12, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_st_ref_take(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_12, 5);
lean_inc(x_2);
x_16 = lean_array_push(x_15, x_2);
lean_ctor_set(x_12, 5, x_16);
x_17 = lean_st_ref_set(x_3, x_12, x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_apply_8(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get_uint8(x_12, sizeof(void*)*9);
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_ctor_get(x_12, 2);
x_26 = lean_ctor_get(x_12, 3);
x_27 = lean_ctor_get_uint8(x_12, sizeof(void*)*9 + 1);
x_28 = lean_ctor_get(x_12, 4);
x_29 = lean_ctor_get(x_12, 5);
x_30 = lean_ctor_get(x_12, 6);
x_31 = lean_ctor_get(x_12, 7);
x_32 = lean_ctor_get(x_12, 8);
x_33 = lean_ctor_get_uint8(x_12, sizeof(void*)*9 + 2);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
lean_inc(x_2);
x_34 = lean_array_push(x_29, x_2);
x_35 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_24);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_35, 3, x_26);
lean_ctor_set(x_35, 4, x_28);
lean_ctor_set(x_35, 5, x_34);
lean_ctor_set(x_35, 6, x_30);
lean_ctor_set(x_35, 7, x_31);
lean_ctor_set(x_35, 8, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*9, x_22);
lean_ctor_set_uint8(x_35, sizeof(void*)*9 + 1, x_27);
lean_ctor_set_uint8(x_35, sizeof(void*)*9 + 2, x_33);
x_36 = lean_st_ref_set(x_3, x_35, x_13);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_apply_8(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_39);
return x_40;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getBindingName(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___lambda__1), 10, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = 0;
x_18 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg(x_11, x_17, x_14, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_18;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = x_5 < x_4;
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
lean_dec(x_6);
x_17 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorImplicitArgInfo(x_17, x_2, x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 1;
x_21 = x_5 + x_20;
x_22 = lean_box(0);
x_5 = x_21;
x_6 = x_22;
x_14 = x_19;
goto _start;
}
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___rarg(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
x_13 = lean_st_ref_get(x_7, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_9, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Std_HashMap_inhabited___closed__1;
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = 1;
x_24 = 0;
x_25 = l_Lean_MetavarContext_MkBinding_mkBinding(x_23, x_12, x_1, x_2, x_24, x_24, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
x_30 = lean_st_ref_take(x_9, x_19);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_31, 2);
lean_dec(x_34);
lean_ctor_set(x_31, 2, x_29);
x_35 = lean_st_ref_set(x_9, x_31, x_32);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
lean_dec(x_27);
x_38 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_37, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_6);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_28);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_43 = lean_ctor_get(x_31, 0);
x_44 = lean_ctor_get(x_31, 1);
x_45 = lean_ctor_get(x_31, 3);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_31);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_29);
lean_ctor_set(x_46, 3, x_45);
x_47 = lean_st_ref_set(x_9, x_46, x_32);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_27, 0);
lean_inc(x_49);
lean_dec(x_27);
x_50 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_49, x_6, x_7, x_8, x_9, x_48);
lean_dec(x_6);
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
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_28);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_54 = lean_ctor_get(x_25, 1);
lean_inc(x_54);
lean_dec(x_25);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___spec__1(x_55, x_6, x_7, x_8, x_9, x_19);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_st_ref_take(x_9, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_60, 2);
lean_dec(x_63);
lean_ctor_set(x_60, 2, x_58);
x_64 = lean_st_ref_set(x_9, x_60, x_61);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = l___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___rarg___closed__3;
x_67 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_66, x_6, x_7, x_8, x_9, x_65);
lean_dec(x_6);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_60, 0);
x_69 = lean_ctor_get(x_60, 1);
x_70 = lean_ctor_get(x_60, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_60);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_58);
lean_ctor_set(x_71, 3, x_70);
x_72 = lean_st_ref_set(x_9, x_71, x_61);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___rarg___closed__3;
x_75 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_74, x_6, x_7, x_8, x_9, x_73);
lean_dec(x_6);
return x_75;
}
}
}
else
{
lean_object* x_76; 
lean_dec(x_6);
lean_dec(x_1);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_2);
lean_ctor_set(x_76, 1, x_10);
return x_76;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after etaArgs, ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_57; lean_object* x_58; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_st_ref_get(x_12, x_13);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 3);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_ctor_get_uint8(x_73, sizeof(void*)*1);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = 0;
x_57 = x_76;
x_58 = x_75;
goto block_70;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
lean_dec(x_71);
lean_inc(x_2);
x_78 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_unbox(x_79);
lean_dec(x_79);
x_57 = x_81;
x_58 = x_80;
goto block_70;
}
block_56:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
lean_dec(x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_14);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_45 = lean_st_ref_get(x_12, x_14);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 3);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = 0;
x_19 = x_50;
x_20 = x_49;
goto block_44;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_dec(x_45);
lean_inc(x_2);
x_52 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_unbox(x_53);
lean_dec(x_53);
x_19 = x_55;
x_20 = x_54;
goto block_44;
}
block_44:
{
if (x_19 == 0)
{
lean_object* x_21; 
lean_dec(x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_21 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_18, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(x_4, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc(x_18);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_18);
x_30 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___lambda__4___closed__4;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_2, x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_36 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_18, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_box(0);
x_39 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(x_4, x_38, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
}
block_70:
{
if (x_57 == 0)
{
x_14 = x_58;
goto block_56;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_inc(x_4);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_4);
x_60 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__2;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_inc(x_3);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_3);
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_inc(x_2);
x_68 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_2, x_67, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_58);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_14 = x_69;
goto block_56;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("finalize");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1;
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_45 = lean_st_ref_get(x_7, x_11);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 3);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_14 = x_49;
goto block_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2;
x_52 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_51, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_14 = x_55;
goto block_44;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
lean_inc(x_12);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_12);
x_58 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_51, x_57, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_56);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_14 = x_59;
goto block_44;
}
}
block_44:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_15 = lean_ctor_get(x_6, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 6);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = lean_box(0);
lean_inc(x_12);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__1(x_12, x_15, x_16, x_18, x_19, x_20, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_16);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_10, 5);
lean_inc(x_24);
x_25 = l_Array_isEmpty___rarg(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_13);
lean_inc(x_4);
x_26 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__2(x_24, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_27);
x_29 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3(x_27, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2;
x_33 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2(x_10, x_32, x_30, x_27, x_22, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_22);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_27);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
return x_26;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_26);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_24);
x_42 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2;
x_43 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2(x_10, x_42, x_13, x_12, x_22, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
lean_dec(x_22);
return x_43;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__1(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_17;
}
}
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeFormerTypeImp(x_11, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_8(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
return x_14;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = 0;
x_15 = lean_box(0);
lean_inc(x_5);
x_16 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_13, x_14, x_15, x_5, x_6, x_7, x_8, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
x_19 = l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___spec__2(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___lambda__1(x_17, x_1, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_st_ref_take(x_2, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_27, 6);
x_31 = lean_ctor_get(x_27, 8);
x_32 = l_Lean_Expr_mvarId_x21(x_17);
lean_inc(x_32);
x_33 = lean_array_push(x_30, x_32);
x_34 = lean_array_push(x_31, x_32);
lean_ctor_set(x_27, 8, x_34);
lean_ctor_set(x_27, 6, x_33);
x_35 = lean_st_ref_set(x_2, x_27, x_28);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_box(0);
x_38 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___lambda__1(x_17, x_1, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
return x_38;
}
else
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_39 = lean_ctor_get_uint8(x_27, sizeof(void*)*9);
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
x_42 = lean_ctor_get(x_27, 2);
x_43 = lean_ctor_get(x_27, 3);
x_44 = lean_ctor_get_uint8(x_27, sizeof(void*)*9 + 1);
x_45 = lean_ctor_get(x_27, 4);
x_46 = lean_ctor_get(x_27, 5);
x_47 = lean_ctor_get(x_27, 6);
x_48 = lean_ctor_get(x_27, 7);
x_49 = lean_ctor_get(x_27, 8);
x_50 = lean_ctor_get_uint8(x_27, sizeof(void*)*9 + 2);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_27);
x_51 = l_Lean_Expr_mvarId_x21(x_17);
lean_inc(x_51);
x_52 = lean_array_push(x_47, x_51);
x_53 = lean_array_push(x_49, x_51);
x_54 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_54, 0, x_40);
lean_ctor_set(x_54, 1, x_41);
lean_ctor_set(x_54, 2, x_42);
lean_ctor_set(x_54, 3, x_43);
lean_ctor_set(x_54, 4, x_45);
lean_ctor_set(x_54, 5, x_46);
lean_ctor_set(x_54, 6, x_52);
lean_ctor_set(x_54, 7, x_48);
lean_ctor_set(x_54, 8, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*9, x_39);
lean_ctor_set_uint8(x_54, sizeof(void*)*9 + 1, x_44);
lean_ctor_set_uint8(x_54, sizeof(void*)*9 + 2, x_50);
x_55 = lean_st_ref_set(x_2, x_54, x_28);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___lambda__1(x_17, x_1, x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_56);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_19);
if (x_59 == 0)
{
return x_19;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_19, 0);
x_61 = lean_ctor_get(x_19, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_19);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
lean_object* l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___spec__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_box(x_1);
x_9 = lean_apply_3(x_7, x_8, x_3, x_3);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
if (lean_obj_tag(x_10) == 4)
{
lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_10, sizeof(void*)*2);
lean_dec(x_10);
x_14 = lean_box_uint64(x_13);
x_15 = lean_apply_4(x_5, x_2, x_11, x_12, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_5);
x_16 = lean_apply_2(x_6, x_2, x_10);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_apply_2(x_4, x_17, x_3);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_box(x_1);
x_20 = lean_apply_3(x_7, x_19, x_2, x_3);
return x_20;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2___rarg(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_Meta_Basic___instance__10___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid autoParam, argument must be a constant");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("by");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__4;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
x_15 = lean_ctor_get_uint8(x_11, sizeof(void*)*9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Expr_getOptParamDefault_x3f(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Expr_getAutoParamTactic_x3f(x_16);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_11, 3);
lean_inc(x_20);
lean_dec(x_11);
x_21 = l_List_isEmpty___rarg(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_22;
}
else
{
lean_object* x_23; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_fTypeHasOptAutoParams(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_st_ref_get(x_2, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_28, sizeof(void*)*9 + 1);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_2);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_dec(x_23);
x_35 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
else
{
lean_object* x_40; 
lean_dec(x_11);
x_40 = lean_ctor_get(x_19, 0);
lean_inc(x_40);
lean_dec(x_19);
if (lean_obj_tag(x_40) == 4)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_st_ref_get(x_8, x_17);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_7, 0);
lean_inc(x_46);
x_47 = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(x_45, x_46, x_41);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1___rarg(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_44);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
lean_dec(x_47);
x_53 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_44);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_54);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_Syntax_getArgs(x_52);
lean_dec(x_52);
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_Array_empty___closed__1;
x_60 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_57, x_57, x_58, x_59);
lean_dec(x_57);
x_61 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
x_62 = lean_array_push(x_60, x_61);
x_63 = l_Lean_nullKind___closed__2;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_array_push(x_59, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__4;
x_68 = lean_array_push(x_67, x_66);
x_69 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__29;
x_70 = lean_array_push(x_68, x_69);
x_71 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_array_push(x_59, x_72);
x_74 = l___regBuiltin_Lean_Elab_Tactic_evalTacticSeq___closed__2;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__6;
x_77 = lean_array_push(x_76, x_75);
x_78 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_ctor_get(x_7, 3);
lean_inc(x_80);
x_81 = l_Lean_Syntax_copyInfo(x_79, x_80);
lean_dec(x_80);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_82 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_81);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_85 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_86);
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
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_85);
if (x_88 == 0)
{
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_85, 0);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_85);
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
lean_dec(x_81);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_82);
if (x_92 == 0)
{
return x_82;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_82, 0);
x_94 = lean_ctor_get(x_82, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_82);
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
lean_dec(x_40);
lean_dec(x_1);
x_96 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__3;
x_97 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1___rarg(x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_16);
lean_dec(x_11);
x_98 = lean_ctor_get(x_18, 0);
lean_inc(x_98);
lean_dec(x_18);
x_99 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_100);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_14, 1);
lean_inc(x_102);
lean_dec(x_14);
x_103 = lean_ctor_get(x_11, 3);
lean_inc(x_103);
lean_dec(x_11);
x_104 = l_List_isEmpty___rarg(x_103);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_102);
return x_105;
}
else
{
lean_object* x_106; 
lean_dec(x_1);
x_106 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_102);
lean_dec(x_2);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_11);
x_107 = lean_ctor_get(x_10, 1);
lean_inc(x_107);
lean_dec(x_10);
x_108 = lean_ctor_get(x_12, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_12, 1);
lean_inc(x_109);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_110 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_107);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_st_ref_take(x_2, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = !lean_is_exclusive(x_113);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_113, 2);
lean_dec(x_116);
lean_ctor_set(x_113, 2, x_109);
x_117 = lean_st_ref_set(x_2, x_113, x_114);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_119 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_120);
return x_121;
}
else
{
uint8_t x_122; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_119);
if (x_122 == 0)
{
return x_119;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_119, 0);
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_119);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_126 = lean_ctor_get_uint8(x_113, sizeof(void*)*9);
x_127 = lean_ctor_get(x_113, 0);
x_128 = lean_ctor_get(x_113, 1);
x_129 = lean_ctor_get(x_113, 3);
x_130 = lean_ctor_get_uint8(x_113, sizeof(void*)*9 + 1);
x_131 = lean_ctor_get(x_113, 4);
x_132 = lean_ctor_get(x_113, 5);
x_133 = lean_ctor_get(x_113, 6);
x_134 = lean_ctor_get(x_113, 7);
x_135 = lean_ctor_get(x_113, 8);
x_136 = lean_ctor_get_uint8(x_113, sizeof(void*)*9 + 2);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_113);
x_137 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_137, 0, x_127);
lean_ctor_set(x_137, 1, x_128);
lean_ctor_set(x_137, 2, x_109);
lean_ctor_set(x_137, 3, x_129);
lean_ctor_set(x_137, 4, x_131);
lean_ctor_set(x_137, 5, x_132);
lean_ctor_set(x_137, 6, x_133);
lean_ctor_set(x_137, 7, x_134);
lean_ctor_set(x_137, 8, x_135);
lean_ctor_set_uint8(x_137, sizeof(void*)*9, x_126);
lean_ctor_set_uint8(x_137, sizeof(void*)*9 + 1, x_130);
lean_ctor_set_uint8(x_137, sizeof(void*)*9 + 2, x_136);
x_138 = lean_st_ref_set(x_2, x_137, x_114);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_140 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_141);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_143 = lean_ctor_get(x_140, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_140, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_145 = x_140;
} else {
 lean_dec_ref(x_140);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_110);
if (x_147 == 0)
{
return x_110;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_110, 0);
x_149 = lean_ctor_get(x_110, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_110);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*9);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_16;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processInstImplicitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*9);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_15);
x_18 = 1;
x_19 = lean_box(0);
lean_inc(x_5);
x_20 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_mvarId_x21(x_21);
x_24 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_dec(x_10);
x_30 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = 1;
x_41 = lean_box(0);
lean_inc(x_5);
x_42 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_39, x_40, x_41, x_5, x_6, x_7, x_8, x_38);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_st_ref_take(x_2, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_46, 2);
x_50 = l_List_tail_x21___rarg(x_49);
lean_dec(x_49);
lean_ctor_set(x_46, 2, x_50);
x_51 = lean_st_ref_set(x_2, x_46, x_47);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_Expr_mvarId_x21(x_43);
x_54 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar(x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_52);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_55);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_57);
return x_58;
}
else
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_59 = lean_ctor_get_uint8(x_46, sizeof(void*)*9);
x_60 = lean_ctor_get(x_46, 0);
x_61 = lean_ctor_get(x_46, 1);
x_62 = lean_ctor_get(x_46, 2);
x_63 = lean_ctor_get(x_46, 3);
x_64 = lean_ctor_get_uint8(x_46, sizeof(void*)*9 + 1);
x_65 = lean_ctor_get(x_46, 4);
x_66 = lean_ctor_get(x_46, 5);
x_67 = lean_ctor_get(x_46, 6);
x_68 = lean_ctor_get(x_46, 7);
x_69 = lean_ctor_get(x_46, 8);
x_70 = lean_ctor_get_uint8(x_46, sizeof(void*)*9 + 2);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_46);
x_71 = l_List_tail_x21___rarg(x_62);
lean_dec(x_62);
x_72 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_72, 0, x_60);
lean_ctor_set(x_72, 1, x_61);
lean_ctor_set(x_72, 2, x_71);
lean_ctor_set(x_72, 3, x_63);
lean_ctor_set(x_72, 4, x_65);
lean_ctor_set(x_72, 5, x_66);
lean_ctor_set(x_72, 6, x_67);
lean_ctor_set(x_72, 7, x_68);
lean_ctor_set(x_72, 8, x_69);
lean_ctor_set_uint8(x_72, sizeof(void*)*9, x_59);
lean_ctor_set_uint8(x_72, sizeof(void*)*9 + 1, x_64);
lean_ctor_set_uint8(x_72, sizeof(void*)*9 + 2, x_70);
x_73 = lean_st_ref_set(x_2, x_72, x_47);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = l_Lean_Expr_mvarId_x21(x_43);
x_76 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar(x_75, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_74);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_77);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_79);
return x_80;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasArgsToProcess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
x_13 = l_List_isEmpty___rarg(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; 
lean_dec(x_11);
x_14 = 1;
x_15 = lean_box(x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_11, 3);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l_List_isEmpty___rarg(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; 
x_18 = 1;
x_19 = lean_box(x_18);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
uint8_t x_20; lean_object* x_21; 
x_20 = 0;
x_21 = lean_box(x_20);
lean_ctor_set(x_9, 0, x_21);
return x_9;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_ctor_get(x_22, 2);
lean_inc(x_24);
x_25 = l_List_isEmpty___rarg(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_22, 3);
lean_inc(x_29);
lean_dec(x_22);
x_30 = l_List_isEmpty___rarg(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_31 = 1;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_23);
return x_33;
}
else
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_23);
return x_36;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasArgsToProcess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasArgsToProcess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_box(x_1);
switch (lean_obj_tag(x_5)) {
case 1:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 3:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(x_1);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
}
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ElabAppArgs_main_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Elab_Term_ElabAppArgs_main_match__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ElabAppArgs_main_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ElabAppArgs_main_match__3___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_ElabAppArgs_main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ElabAppArgs_main), 8, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 7)
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_12, sizeof(void*)*3);
lean_dec(x_12);
x_16 = lean_st_ref_get(x_1, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_14);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1___boxed), 2, 1);
lean_closure_set(x_19, 0, x_14);
x_20 = lean_ctor_get(x_17, 3);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_List_find_x3f___main___rarg(x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; lean_object* x_23; 
lean_dec(x_14);
x_22 = (uint8_t)((x_15 << 24) >> 61);
x_23 = lean_box(x_22);
switch (lean_obj_tag(x_23)) {
case 1:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Elab_Term_ElabAppArgs_main___closed__1;
x_25 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg(x_24, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
return x_25;
}
case 3:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_Elab_Term_ElabAppArgs_main___closed__1;
x_27 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processInstImplicitArg(x_26, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
return x_27;
}
default: 
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_23);
x_28 = l_Lean_Elab_Term_ElabAppArgs_main___closed__1;
x_29 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg(x_28, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg(x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_32);
lean_dec(x_14);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_36 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(x_35, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_8 = x_37;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
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
lean_dec(x_30);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_31);
if (x_43 == 0)
{
return x_31;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_31, 0);
x_45 = lean_ctor_get(x_31, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_31);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_12);
x_47 = lean_ctor_get(x_11, 1);
lean_inc(x_47);
lean_dec(x_11);
x_48 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasArgsToProcess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_51);
lean_dec(x_1);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_dec(x_48);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_54 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_8 = x_55;
goto _start;
}
else
{
uint8_t x_57; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_54);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_11);
if (x_61 == 0)
{
return x_11;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_11, 0);
x_63 = lean_ctor_get(x_11, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_11);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = l_Array_toList___rarg(x_1);
x_17 = l_Array_toList___rarg(x_2);
x_18 = l_Array_empty___closed__1;
x_19 = 0;
x_20 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_5);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_17);
lean_ctor_set(x_20, 4, x_7);
lean_ctor_set(x_20, 5, x_18);
lean_ctor_set(x_20, 6, x_18);
lean_ctor_set(x_20, 7, x_18);
lean_ctor_set(x_20, 8, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*9, x_3);
lean_ctor_set_uint8(x_20, sizeof(void*)*9 + 1, x_6);
lean_ctor_set_uint8(x_20, sizeof(void*)*9 + 2, x_19);
x_21 = lean_st_mk_ref(x_20, x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_22);
x_24 = l_Lean_Elab_Term_ElabAppArgs_main(x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_get(x_22, x_26);
lean_dec(x_22);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_22);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("args");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1;
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_14 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_42; lean_object* x_43; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_62 = lean_st_ref_get(x_12, x_19);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 3);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_ctor_get_uint8(x_64, sizeof(void*)*1);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec(x_62);
x_67 = 0;
x_42 = x_67;
x_43 = x_66;
goto block_61;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_dec(x_62);
x_69 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__2;
x_70 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_69, x_7, x_8, x_9, x_10, x_11, x_12, x_68);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_unbox(x_71);
lean_dec(x_71);
x_42 = x_73;
x_43 = x_72;
goto block_61;
}
block_41:
{
uint8_t x_21; 
x_21 = l_Array_isEmpty___rarg(x_2);
if (x_21 == 0)
{
lean_object* x_22; 
lean_inc(x_18);
x_22 = l_Lean_Elab_Term_tryPostponeIfMVar(x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1(x_3, x_2, x_5, x_1, x_18, x_6, x_4, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
lean_dec(x_23);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
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
x_30 = l_Array_isEmpty___rarg(x_3);
if (x_30 == 0)
{
lean_object* x_31; 
lean_inc(x_18);
x_31 = l_Lean_Elab_Term_tryPostponeIfMVar(x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1(x_3, x_2, x_5, x_1, x_18, x_6, x_4, x_32, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
lean_dec(x_32);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(0);
x_40 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1(x_3, x_2, x_5, x_1, x_18, x_6, x_4, x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
return x_40;
}
}
}
block_61:
{
if (x_42 == 0)
{
x_20 = x_43;
goto block_41;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_44 = l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__3(x_5);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__4;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__8;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_1);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_1);
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_inc(x_18);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_18);
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__2;
x_59 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_58, x_57, x_7, x_8, x_9, x_10, x_11, x_12, x_43);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_20 = x_60;
goto block_41;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_14);
if (x_74 == 0)
{
return x_14;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_14, 0);
x_76 = lean_ctor_get(x_14, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_14);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1(x_1, x_2, x_16, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_indentExpr(x_1);
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_indentExpr(x_2);
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_11);
x_21 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_1, x_8, x_2);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_3);
x_4 = l_Lean_Name_append(x_2, x_3);
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
x_12 = l_Array_findSomeMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1(x_1, x_3, x_10, x_11);
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
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_dec(x_7);
lean_dec(x_6);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box_uint64(x_10);
x_13 = lean_apply_4(x_3, x_8, x_9, x_12, x_11);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_box_uint64(x_16);
x_19 = lean_apply_4(x_4, x_14, x_15, x_18, x_17);
return x_19;
}
default: 
{
lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_box_uint64(x_22);
x_25 = lean_apply_4(x_5, x_20, x_21, x_24, x_23);
return x_25;
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_apply_2(x_6, x_1, x_26);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_6);
x_28 = lean_apply_2(x_7, x_1, x_2);
return x_28;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__5___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure has only ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" field(s)");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_getStructureFields(x_1, x_2);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_3, x_15);
x_17 = lean_array_get_size(x_14);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_17);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_4, x_5, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_2);
x_26 = l_Lean_isStructure(x_1, x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_13);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_array_fget(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
lean_inc(x_2);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_13);
return x_31;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_st_ref_get(x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
lean_inc(x_16);
x_17 = l_Lean_isStructureLike(x_16, x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_16);
lean_dec(x_1);
x_18 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__3;
x_19 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_3, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1(x_16, x_1, x_2, x_3, x_4, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_25;
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, type is not of the form (C ...) where C is a constant");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [..] notation, type is not of the form (C ...) where C is a constant");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, index must be greater than 0");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a valid \"field\" because environment does not contain '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("getOp");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [..] notation because environment does not contain '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_11) == 4)
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2(x_12, x_13, x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__9;
x_19 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
lean_dec(x_3);
x_26 = lean_st_ref_get(x_9, x_10);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_24);
lean_inc(x_30);
x_31 = l_Lean_isStructure(x_30, x_24);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc(x_25);
lean_inc(x_24);
x_32 = lean_name_mk_string(x_24, x_25);
x_33 = lean_ctor_get(x_4, 2);
lean_inc(x_33);
x_34 = lean_box(0);
lean_inc(x_32);
x_35 = l_Lean_Name_replacePrefix(x_32, x_33, x_34);
lean_dec(x_33);
x_36 = lean_ctor_get(x_6, 1);
lean_inc(x_36);
x_37 = lean_local_ctx_find_from_user_name(x_36, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_inc(x_25);
x_38 = lean_name_mk_string(x_34, x_25);
lean_inc(x_24);
x_39 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_30, x_24, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_free_object(x_26);
lean_dec(x_24);
x_40 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_41 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_32);
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_48, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_6);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_ctor_get(x_39, 0);
lean_inc(x_50);
lean_dec(x_39);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_24);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set(x_26, 0, x_53);
return x_26;
}
}
else
{
lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_37, 0);
lean_inc(x_54);
lean_dec(x_37);
x_55 = l_Lean_LocalDecl_binderInfo(x_54);
x_56 = 4;
x_57 = l_Lean_BinderInfo_beq(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_54);
lean_inc(x_25);
x_58 = lean_name_mk_string(x_34, x_25);
lean_inc(x_24);
x_59 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_30, x_24, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_26);
lean_dec(x_24);
x_60 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_61 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_65, 0, x_32);
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_68, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_6);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_ctor_get(x_59, 0);
lean_inc(x_70);
lean_dec(x_59);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_24);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_26, 0, x_73);
return x_26;
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_74 = l_Lean_LocalDecl_toExpr(x_54);
lean_dec(x_54);
x_75 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_75, 0, x_24);
lean_ctor_set(x_75, 1, x_32);
lean_ctor_set(x_75, 2, x_74);
lean_ctor_set(x_26, 0, x_75);
return x_26;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_box(0);
lean_inc(x_25);
x_77 = lean_name_mk_string(x_76, x_25);
lean_inc(x_24);
lean_inc(x_30);
x_78 = l_Lean_findField_x3f(x_30, x_24, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_inc(x_25);
lean_inc(x_24);
x_79 = lean_name_mk_string(x_24, x_25);
x_80 = lean_ctor_get(x_4, 2);
lean_inc(x_80);
lean_inc(x_79);
x_81 = l_Lean_Name_replacePrefix(x_79, x_80, x_76);
lean_dec(x_80);
x_82 = lean_ctor_get(x_6, 1);
lean_inc(x_82);
x_83 = lean_local_ctx_find_from_user_name(x_82, x_81);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
lean_inc(x_24);
x_84 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_30, x_24, x_77);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_free_object(x_26);
lean_dec(x_24);
x_85 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_86 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11;
x_87 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13;
x_89 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_90, 0, x_79);
x_91 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_93 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_93, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_6);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_79);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_ctor_get(x_84, 0);
lean_inc(x_95);
lean_dec(x_84);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_24);
lean_ctor_set(x_98, 2, x_97);
lean_ctor_set(x_26, 0, x_98);
return x_26;
}
}
else
{
lean_object* x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; 
x_99 = lean_ctor_get(x_83, 0);
lean_inc(x_99);
lean_dec(x_83);
x_100 = l_Lean_LocalDecl_binderInfo(x_99);
x_101 = 4;
x_102 = l_Lean_BinderInfo_beq(x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_99);
lean_inc(x_24);
x_103 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_30, x_24, x_77);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_free_object(x_26);
lean_dec(x_24);
x_104 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_105 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11;
x_106 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13;
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_109, 0, x_79);
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_112, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_6);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_79);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_114 = lean_ctor_get(x_103, 0);
lean_inc(x_114);
lean_dec(x_103);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_24);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set(x_26, 0, x_117);
return x_26;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_77);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_118 = l_Lean_LocalDecl_toExpr(x_99);
lean_dec(x_99);
x_119 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_119, 0, x_24);
lean_ctor_set(x_119, 1, x_79);
lean_ctor_set(x_119, 2, x_118);
lean_ctor_set(x_26, 0, x_119);
return x_26;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_ctor_get(x_78, 0);
lean_inc(x_120);
lean_dec(x_78);
x_121 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_24);
lean_ctor_set(x_121, 2, x_77);
lean_ctor_set(x_26, 0, x_121);
return x_26;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_122 = lean_ctor_get(x_26, 0);
x_123 = lean_ctor_get(x_26, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_26);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
lean_dec(x_122);
lean_inc(x_24);
lean_inc(x_124);
x_125 = l_Lean_isStructure(x_124, x_24);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_inc(x_25);
lean_inc(x_24);
x_126 = lean_name_mk_string(x_24, x_25);
x_127 = lean_ctor_get(x_4, 2);
lean_inc(x_127);
x_128 = lean_box(0);
lean_inc(x_126);
x_129 = l_Lean_Name_replacePrefix(x_126, x_127, x_128);
lean_dec(x_127);
x_130 = lean_ctor_get(x_6, 1);
lean_inc(x_130);
x_131 = lean_local_ctx_find_from_user_name(x_130, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_inc(x_25);
x_132 = lean_name_mk_string(x_128, x_25);
lean_inc(x_24);
x_133 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_124, x_24, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_24);
x_134 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_135 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11;
x_136 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
x_137 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13;
x_138 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_139, 0, x_126);
x_140 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_142 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_142, x_4, x_5, x_6, x_7, x_8, x_9, x_123);
lean_dec(x_6);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_126);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_144 = lean_ctor_get(x_133, 0);
lean_inc(x_144);
lean_dec(x_133);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_24);
lean_ctor_set(x_147, 2, x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_123);
return x_148;
}
}
else
{
lean_object* x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; 
x_149 = lean_ctor_get(x_131, 0);
lean_inc(x_149);
lean_dec(x_131);
x_150 = l_Lean_LocalDecl_binderInfo(x_149);
x_151 = 4;
x_152 = l_Lean_BinderInfo_beq(x_150, x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_149);
lean_inc(x_25);
x_153 = lean_name_mk_string(x_128, x_25);
lean_inc(x_24);
x_154 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_124, x_24, x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_24);
x_155 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_156 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11;
x_157 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13;
x_159 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_160, 0, x_126);
x_161 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_163 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_163, x_4, x_5, x_6, x_7, x_8, x_9, x_123);
lean_dec(x_6);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_126);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_165 = lean_ctor_get(x_154, 0);
lean_inc(x_165);
lean_dec(x_154);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_24);
lean_ctor_set(x_168, 2, x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_123);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_124);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_170 = l_Lean_LocalDecl_toExpr(x_149);
lean_dec(x_149);
x_171 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_171, 0, x_24);
lean_ctor_set(x_171, 1, x_126);
lean_ctor_set(x_171, 2, x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_123);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_box(0);
lean_inc(x_25);
x_174 = lean_name_mk_string(x_173, x_25);
lean_inc(x_24);
lean_inc(x_124);
x_175 = l_Lean_findField_x3f(x_124, x_24, x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_inc(x_25);
lean_inc(x_24);
x_176 = lean_name_mk_string(x_24, x_25);
x_177 = lean_ctor_get(x_4, 2);
lean_inc(x_177);
lean_inc(x_176);
x_178 = l_Lean_Name_replacePrefix(x_176, x_177, x_173);
lean_dec(x_177);
x_179 = lean_ctor_get(x_6, 1);
lean_inc(x_179);
x_180 = lean_local_ctx_find_from_user_name(x_179, x_178);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
lean_inc(x_24);
x_181 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_124, x_24, x_174);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_24);
x_182 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_183 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11;
x_184 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
x_185 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13;
x_186 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_187, 0, x_176);
x_188 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_189 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_190 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_190, x_4, x_5, x_6, x_7, x_8, x_9, x_123);
lean_dec(x_6);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_176);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_192 = lean_ctor_get(x_181, 0);
lean_inc(x_192);
lean_dec(x_181);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_24);
lean_ctor_set(x_195, 2, x_194);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_123);
return x_196;
}
}
else
{
lean_object* x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; 
x_197 = lean_ctor_get(x_180, 0);
lean_inc(x_197);
lean_dec(x_180);
x_198 = l_Lean_LocalDecl_binderInfo(x_197);
x_199 = 4;
x_200 = l_Lean_BinderInfo_beq(x_198, x_199);
if (x_200 == 0)
{
lean_object* x_201; 
lean_dec(x_197);
lean_inc(x_24);
x_201 = l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(x_124, x_24, x_174);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_24);
x_202 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_203 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11;
x_204 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
x_205 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13;
x_206 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_207, 0, x_176);
x_208 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_210 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_210, x_4, x_5, x_6, x_7, x_8, x_9, x_123);
lean_dec(x_6);
return x_211;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_176);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_212 = lean_ctor_get(x_201, 0);
lean_inc(x_212);
lean_dec(x_201);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_24);
lean_ctor_set(x_215, 2, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_123);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_174);
lean_dec(x_124);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_217 = l_Lean_LocalDecl_toExpr(x_197);
lean_dec(x_197);
x_218 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_218, 0, x_24);
lean_ctor_set(x_218, 1, x_176);
lean_ctor_set(x_218, 2, x_217);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_123);
return x_219;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_124);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_220 = lean_ctor_get(x_175, 0);
lean_inc(x_220);
lean_dec(x_175);
x_221 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_24);
lean_ctor_set(x_221, 2, x_174);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_123);
return x_222;
}
}
}
}
default: 
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_223 = lean_ctor_get(x_11, 0);
lean_inc(x_223);
lean_dec(x_11);
x_224 = lean_ctor_get(x_3, 0);
lean_inc(x_224);
lean_dec(x_3);
x_225 = lean_st_ref_get(x_9, x_10);
x_226 = !lean_is_exclusive(x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_227 = lean_ctor_get(x_225, 0);
x_228 = lean_ctor_get(x_225, 1);
x_229 = lean_ctor_get(x_227, 0);
lean_inc(x_229);
lean_dec(x_227);
x_230 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__14;
x_231 = lean_name_mk_string(x_223, x_230);
lean_inc(x_231);
x_232 = lean_environment_find(x_229, x_231);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_free_object(x_225);
lean_dec(x_224);
x_233 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_233, 0, x_231);
x_234 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__16;
x_235 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_233);
x_236 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_237 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
x_238 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_237, x_4, x_5, x_6, x_7, x_8, x_9, x_228);
lean_dec(x_6);
return x_238;
}
else
{
lean_object* x_239; 
lean_dec(x_232);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_239 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_239, 0, x_231);
lean_ctor_set(x_239, 1, x_224);
lean_ctor_set(x_225, 0, x_239);
return x_225;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_240 = lean_ctor_get(x_225, 0);
x_241 = lean_ctor_get(x_225, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_225);
x_242 = lean_ctor_get(x_240, 0);
lean_inc(x_242);
lean_dec(x_240);
x_243 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__14;
x_244 = lean_name_mk_string(x_223, x_243);
lean_inc(x_244);
x_245 = lean_environment_find(x_242, x_244);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_224);
x_246 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_246, 0, x_244);
x_247 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__16;
x_248 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_246);
x_249 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_250 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
x_251 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_250, x_4, x_5, x_6, x_7, x_8, x_9, x_241);
lean_dec(x_6);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_245);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_252 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_252, 0, x_244);
lean_ctor_set(x_252, 1, x_224);
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_241);
return x_253;
}
}
}
}
}
else
{
lean_dec(x_11);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_3);
x_254 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__6;
x_255 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_254, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_3);
x_256 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__3;
x_257 = l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(x_1, x_2, x_256, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_257;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
return x_14;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_13;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___at___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCoreImp___spec__2(x_2, x_5, x_6, x_7, x_8, x_9);
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
x_23 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_20, x_21, x_22, x_5, x_6, x_7, x_8, x_13);
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
x_44 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_41, x_42, x_43, x_5, x_6, x_7, x_8, x_35);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_apply_3(x_2, x_1, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_apply_2(x_3, x_1, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_15 = l_Lean_Elab_logException___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_20 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux(x_16, x_17, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
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
x_28 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_17, x_7, x_8, x_9, x_10, x_27);
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
x_32 = l_Array_forMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1(x_4, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
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
x_57 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux(x_53, x_54, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_56);
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
x_65 = l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(x_54, x_7, x_8, x_9, x_10, x_64);
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
x_69 = l_Array_forMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1(x_4, x_68, x_5, x_6, x_7, x_8, x_9, x_10, x_67);
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
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Array_empty___closed__1;
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop(x_2, x_1, x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLVal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLVal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("self");
return x_1;
}
}
static lean_object* _init_l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
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
lean_ctor_set(x_17, 0, x_2);
x_18 = l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
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
x_25 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_15, x_21, x_23, x_22, x_24, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
lean_dec(x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_1 = x_12;
x_2 = x_26;
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
lean_dec(x_2);
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
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to access field in parent structure");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__3;
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
x_19 = l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_1);
x_10 = lean_local_ctx_find(x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Meta_throwUnknownFVar___rarg(x_1, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_LocalDecl_userName(x_1);
x_10 = lean_name_eq(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_3);
return x_14;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, function '");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not have explicit argument with type (");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ...)");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_1);
x_16 = lean_nat_dec_lt(x_6, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_2);
x_18 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_22, 0, x_3);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__6;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_25, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_6, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_14);
return x_36;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 2);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = 2;
lean_ctor_set_uint8(x_17, 5, x_21);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_23 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isTypeApp_x3f___spec__1(x_1, x_10, x_11, x_22, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = l_Lean_Expr_consumeMData(x_25);
lean_dec(x_25);
x_28 = l_Lean_Expr_isAppOf(x_27, x_4);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_23);
lean_dec(x_7);
x_29 = lean_box(0);
x_30 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1(x_2, x_3, x_4, x_5, x_6, x_8, x_29, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_2);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_7);
x_32 = l_Array_insertAt___rarg(x_2, x_8, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_23, 0, x_36);
return x_23;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = l_Lean_Expr_consumeMData(x_37);
lean_dec(x_37);
x_40 = l_Lean_Expr_isAppOf(x_39, x_4);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_7);
x_41 = lean_box(0);
x_42 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1(x_2, x_3, x_4, x_5, x_6, x_8, x_41, x_10, x_11, x_12, x_13, x_14, x_15, x_38);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_2);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_7);
x_44 = l_Array_insertAt___rarg(x_2, x_8, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_5);
lean_ctor_set(x_46, 1, x_8);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_38);
return x_49;
}
}
}
else
{
uint8_t x_50; 
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
x_50 = !lean_is_exclusive(x_23);
if (x_50 == 0)
{
return x_23;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_23, 0);
x_52 = lean_ctor_get(x_23, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_23);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get_uint8(x_17, 0);
x_55 = lean_ctor_get_uint8(x_17, 1);
x_56 = lean_ctor_get_uint8(x_17, 2);
x_57 = lean_ctor_get_uint8(x_17, 3);
x_58 = lean_ctor_get_uint8(x_17, 4);
x_59 = lean_ctor_get_uint8(x_17, 6);
x_60 = lean_ctor_get_uint8(x_17, 7);
lean_dec(x_17);
x_61 = 2;
x_62 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_62, 0, x_54);
lean_ctor_set_uint8(x_62, 1, x_55);
lean_ctor_set_uint8(x_62, 2, x_56);
lean_ctor_set_uint8(x_62, 3, x_57);
lean_ctor_set_uint8(x_62, 4, x_58);
lean_ctor_set_uint8(x_62, 5, x_61);
lean_ctor_set_uint8(x_62, 6, x_59);
lean_ctor_set_uint8(x_62, 7, x_60);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_18);
lean_ctor_set(x_63, 2, x_19);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_64 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isTypeApp_x3f___spec__1(x_1, x_10, x_11, x_63, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = l_Lean_Expr_consumeMData(x_65);
lean_dec(x_65);
x_69 = l_Lean_Expr_isAppOf(x_68, x_4);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_67);
lean_dec(x_7);
x_70 = lean_box(0);
x_71 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1(x_2, x_3, x_4, x_5, x_6, x_8, x_70, x_10, x_11, x_12, x_13, x_14, x_15, x_66);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_2);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_7);
x_73 = l_Array_insertAt___rarg(x_2, x_8, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_5);
lean_ctor_set(x_75, 1, x_8);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
if (lean_is_scalar(x_67)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_67;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_66);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
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
x_79 = lean_ctor_get(x_64, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_64, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_81 = x_64;
} else {
 lean_dec_ref(x_64);
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
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, size_t x_10, size_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
uint8_t x_20; 
x_20 = x_11 < x_10;
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_array_uget(x_9, x_11);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_ctor_get(x_12, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 1);
x_29 = l_Lean_Expr_fvarId_x21(x_22);
lean_dec(x_22);
lean_inc(x_15);
x_30 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(x_29, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = l_Lean_LocalDecl_binderInfo(x_32);
x_35 = l_Lean_BinderInfo_isExplicit(x_34);
if (x_35 == 0)
{
size_t x_36; size_t x_37; 
lean_free_object(x_30);
lean_dec(x_32);
lean_inc(x_8);
lean_ctor_set(x_12, 0, x_8);
x_36 = 1;
x_37 = x_11 + x_36;
x_11 = x_37;
x_19 = x_33;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(x_32, x_27, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l_Lean_LocalDecl_type(x_32);
lean_dec(x_32);
x_42 = l_Lean_Expr_consumeMData(x_41);
x_43 = l_Lean_Expr_isAppOf(x_42, x_1);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_free_object(x_30);
lean_free_object(x_24);
lean_free_object(x_12);
x_44 = lean_box(0);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_4);
x_45 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__2(x_41, x_4, x_2, x_1, x_27, x_8, x_3, x_28, x_44, x_13, x_14, x_15, x_16, x_17, x_18, x_33);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
lean_dec(x_46);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; 
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_dec(x_45);
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
lean_dec(x_46);
x_55 = 1;
x_56 = x_11 + x_55;
x_11 = x_56;
x_12 = x_54;
x_19 = x_53;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
return x_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_41);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_3);
x_63 = l_Array_insertAt___rarg(x_4, x_28, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_12, 0, x_64);
lean_ctor_set(x_30, 0, x_12);
return x_30;
}
}
else
{
lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; 
lean_free_object(x_30);
lean_dec(x_32);
x_65 = lean_ctor_get(x_40, 0);
lean_inc(x_65);
lean_dec(x_40);
x_66 = l_Array_eraseIdx___rarg(x_27, x_65);
lean_dec(x_65);
lean_ctor_set(x_24, 0, x_66);
lean_inc(x_8);
lean_ctor_set(x_12, 0, x_8);
x_67 = 1;
x_68 = x_11 + x_67;
x_11 = x_68;
x_19 = x_33;
goto _start;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_30, 0);
x_71 = lean_ctor_get(x_30, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_30);
x_72 = l_Lean_LocalDecl_binderInfo(x_70);
x_73 = l_Lean_BinderInfo_isExplicit(x_72);
if (x_73 == 0)
{
size_t x_74; size_t x_75; 
lean_dec(x_70);
lean_inc(x_8);
lean_ctor_set(x_12, 0, x_8);
x_74 = 1;
x_75 = x_11 + x_74;
x_11 = x_75;
x_19 = x_71;
goto _start;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_unsigned_to_nat(0u);
x_78 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(x_70, x_27, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = l_Lean_LocalDecl_type(x_70);
lean_dec(x_70);
x_80 = l_Lean_Expr_consumeMData(x_79);
x_81 = l_Lean_Expr_isAppOf(x_80, x_1);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_free_object(x_24);
lean_free_object(x_12);
x_82 = lean_box(0);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_4);
x_83 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__2(x_79, x_4, x_2, x_1, x_27, x_8, x_3, x_28, x_82, x_13, x_14, x_15, x_16, x_17, x_18, x_71);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
lean_dec(x_84);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; size_t x_91; size_t x_92; 
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_dec(x_83);
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
lean_dec(x_84);
x_91 = 1;
x_92 = x_11 + x_91;
x_11 = x_92;
x_12 = x_90;
x_19 = x_89;
goto _start;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_ctor_get(x_83, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_83, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_96 = x_83;
} else {
 lean_dec_ref(x_83);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_79);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_3);
x_99 = l_Array_insertAt___rarg(x_4, x_28, x_98);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_12, 0, x_100);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_12);
lean_ctor_set(x_101, 1, x_71);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; size_t x_104; size_t x_105; 
lean_dec(x_70);
x_102 = lean_ctor_get(x_78, 0);
lean_inc(x_102);
lean_dec(x_78);
x_103 = l_Array_eraseIdx___rarg(x_27, x_102);
lean_dec(x_102);
lean_ctor_set(x_24, 0, x_103);
lean_inc(x_8);
lean_ctor_set(x_12, 0, x_8);
x_104 = 1;
x_105 = x_11 + x_104;
x_11 = x_105;
x_19 = x_71;
goto _start;
}
}
}
}
else
{
uint8_t x_107; 
lean_free_object(x_24);
lean_dec(x_28);
lean_dec(x_27);
lean_free_object(x_12);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_30);
if (x_107 == 0)
{
return x_30;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_30, 0);
x_109 = lean_ctor_get(x_30, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_30);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_24, 0);
x_112 = lean_ctor_get(x_24, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_24);
x_113 = l_Lean_Expr_fvarId_x21(x_22);
lean_dec(x_22);
lean_inc(x_15);
x_114 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(x_113, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
x_118 = l_Lean_LocalDecl_binderInfo(x_115);
x_119 = l_Lean_BinderInfo_isExplicit(x_118);
if (x_119 == 0)
{
lean_object* x_120; size_t x_121; size_t x_122; 
lean_dec(x_117);
lean_dec(x_115);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_111);
lean_ctor_set(x_120, 1, x_112);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_120);
lean_ctor_set(x_12, 0, x_8);
x_121 = 1;
x_122 = x_11 + x_121;
x_11 = x_122;
x_19 = x_116;
goto _start;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_unsigned_to_nat(0u);
x_125 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(x_115, x_111, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = l_Lean_LocalDecl_type(x_115);
lean_dec(x_115);
x_127 = l_Lean_Expr_consumeMData(x_126);
x_128 = l_Lean_Expr_isAppOf(x_127, x_1);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_117);
lean_free_object(x_12);
x_129 = lean_box(0);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_4);
x_130 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__2(x_126, x_4, x_2, x_1, x_111, x_8, x_3, x_112, x_129, x_13, x_14, x_15, x_16, x_17, x_18, x_116);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
lean_dec(x_131);
if (lean_is_scalar(x_133)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_133;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_132);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; size_t x_138; size_t x_139; 
x_136 = lean_ctor_get(x_130, 1);
lean_inc(x_136);
lean_dec(x_130);
x_137 = lean_ctor_get(x_131, 0);
lean_inc(x_137);
lean_dec(x_131);
x_138 = 1;
x_139 = x_11 + x_138;
x_11 = x_139;
x_12 = x_137;
x_19 = x_136;
goto _start;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = lean_ctor_get(x_130, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_130, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_143 = x_130;
} else {
 lean_dec_ref(x_130);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_126);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_3);
x_146 = l_Array_insertAt___rarg(x_4, x_112, x_145);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_111);
lean_ctor_set(x_148, 1, x_112);
lean_ctor_set(x_12, 1, x_148);
lean_ctor_set(x_12, 0, x_147);
if (lean_is_scalar(x_117)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_117;
}
lean_ctor_set(x_149, 0, x_12);
lean_ctor_set(x_149, 1, x_116);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; size_t x_153; size_t x_154; 
lean_dec(x_117);
lean_dec(x_115);
x_150 = lean_ctor_get(x_125, 0);
lean_inc(x_150);
lean_dec(x_125);
x_151 = l_Array_eraseIdx___rarg(x_111, x_150);
lean_dec(x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_112);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_152);
lean_ctor_set(x_12, 0, x_8);
x_153 = 1;
x_154 = x_11 + x_153;
x_11 = x_154;
x_19 = x_116;
goto _start;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_112);
lean_dec(x_111);
lean_free_object(x_12);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = lean_ctor_get(x_114, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_114, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_158 = x_114;
} else {
 lean_dec_ref(x_114);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_160 = lean_ctor_get(x_12, 1);
lean_inc(x_160);
lean_dec(x_12);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
x_164 = l_Lean_Expr_fvarId_x21(x_22);
lean_dec(x_22);
lean_inc(x_15);
x_165 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(x_164, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_170; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_168 = x_165;
} else {
 lean_dec_ref(x_165);
 x_168 = lean_box(0);
}
x_169 = l_Lean_LocalDecl_binderInfo(x_166);
x_170 = l_Lean_BinderInfo_isExplicit(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; size_t x_173; size_t x_174; 
lean_dec(x_168);
lean_dec(x_166);
if (lean_is_scalar(x_163)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_163;
}
lean_ctor_set(x_171, 0, x_161);
lean_ctor_set(x_171, 1, x_162);
lean_inc(x_8);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_8);
lean_ctor_set(x_172, 1, x_171);
x_173 = 1;
x_174 = x_11 + x_173;
x_11 = x_174;
x_12 = x_172;
x_19 = x_167;
goto _start;
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_unsigned_to_nat(0u);
x_177 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(x_166, x_161, x_176);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_178 = l_Lean_LocalDecl_type(x_166);
lean_dec(x_166);
x_179 = l_Lean_Expr_consumeMData(x_178);
x_180 = l_Lean_Expr_isAppOf(x_179, x_1);
lean_dec(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_168);
lean_dec(x_163);
x_181 = lean_box(0);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_4);
x_182 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__2(x_178, x_4, x_2, x_1, x_161, x_8, x_3, x_162, x_181, x_13, x_14, x_15, x_16, x_17, x_18, x_167);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
lean_dec(x_183);
if (lean_is_scalar(x_185)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_185;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_184);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; size_t x_190; size_t x_191; 
x_188 = lean_ctor_get(x_182, 1);
lean_inc(x_188);
lean_dec(x_182);
x_189 = lean_ctor_get(x_183, 0);
lean_inc(x_189);
lean_dec(x_183);
x_190 = 1;
x_191 = x_11 + x_190;
x_11 = x_191;
x_12 = x_189;
x_19 = x_188;
goto _start;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_193 = lean_ctor_get(x_182, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_182, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_195 = x_182;
} else {
 lean_dec_ref(x_182);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_178);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_3);
x_198 = l_Array_insertAt___rarg(x_4, x_162, x_197);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
if (lean_is_scalar(x_163)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_163;
}
lean_ctor_set(x_200, 0, x_161);
lean_ctor_set(x_200, 1, x_162);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
if (lean_is_scalar(x_168)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_168;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_167);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; size_t x_207; size_t x_208; 
lean_dec(x_168);
lean_dec(x_166);
x_203 = lean_ctor_get(x_177, 0);
lean_inc(x_203);
lean_dec(x_177);
x_204 = l_Array_eraseIdx___rarg(x_161, x_203);
lean_dec(x_203);
if (lean_is_scalar(x_163)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_163;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_162);
lean_inc(x_8);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_8);
lean_ctor_set(x_206, 1, x_205);
x_207 = 1;
x_208 = x_11 + x_207;
x_11 = x_208;
x_12 = x_206;
x_19 = x_167;
goto _start;
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_210 = lean_ctor_get(x_165, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_165, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_212 = x_165;
} else {
 lean_dec_ref(x_165);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
}
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___rarg), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_18 = lean_box(0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_get_size(x_9);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = 0;
lean_inc(x_5);
x_25 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_9, x_23, x_24, x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
lean_ctor_set(x_25, 0, x_5);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_25, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_34);
return x_25;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_25, 0);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_25);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__5;
x_2 = l_ReaderT_monadControl___closed__2;
x_3 = l_monadControlTrans___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__5;
x_15 = l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___closed__1;
x_16 = l_ReaderT_monadControl___closed__2;
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___boxed), 17, 8);
lean_closure_set(x_17, 0, x_5);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_3);
lean_closure_set(x_17, 4, x_4);
lean_closure_set(x_17, 5, x_14);
lean_closure_set(x_17, 6, x_15);
lean_closure_set(x_17, 7, x_16);
x_18 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___rarg(x_6, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
}
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_9);
return x_17;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___boxed(lean_object** _args) {
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
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_21 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_22 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_22;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___boxed(lean_object** _args) {
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
x_18 = l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_18;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_3(x_3, x_7, x_8, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_2(x_2, x_11, x_12);
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_3(x_4, x_14, x_15, x_16);
return x_17;
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_apply_3(x_5, x_18, x_19, x_20);
return x_21;
}
default: 
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_apply_2(x_6, x_22, x_23);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__1___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_apply_3(x_4, x_1, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__3___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
lean_inc(x_10);
lean_inc(x_1);
x_18 = l_Lean_Elab_Term_mkConst(x_1, x_17, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_List_isEmpty___rarg(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_dec(x_8);
lean_dec(x_1);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_9);
x_23 = l_Lean_mkOptionalNode___closed__2;
x_24 = lean_array_push(x_23, x_22);
x_25 = lean_box(0);
x_26 = l_Array_empty___closed__1;
x_27 = 0;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_28 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_19, x_26, x_24, x_25, x_27, x_27, x_10, x_11, x_12, x_13, x_14, x_15, x_20);
lean_dec(x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(x_3, x_4, x_5, x_6, x_7, x_29, x_2, x_10, x_11, x_12, x_13, x_14, x_15, x_30);
return x_31;
}
else
{
uint8_t x_32; 
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
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_19);
x_36 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_20);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
x_39 = l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg(x_8, x_1, x_9, x_4, x_3, x_37, x_10, x_11, x_12, x_13, x_14, x_15, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_19, x_3, x_40, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_41);
lean_dec(x_40);
lean_dec(x_3);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
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
else
{
uint8_t x_47; 
lean_dec(x_19);
lean_dec(x_15);
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
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_36);
if (x_47 == 0)
{
return x_36;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_36, 0);
x_49 = lean_ctor_get(x_36, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_36);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_15);
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
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_18);
if (x_51 == 0)
{
return x_18;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_18, 0);
x_53 = lean_ctor_get(x_18, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_18);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("idx");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_6, x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
x_18 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLVal(x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_20, 2);
lean_inc(x_25);
lean_dec(x_20);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_26 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections(x_23, x_24, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Name_append(x_23, x_25);
lean_dec(x_23);
x_30 = lean_box(0);
lean_inc(x_8);
x_31 = l_Lean_Elab_Term_mkConst(x_29, x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_List_isEmpty___rarg(x_17);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_27);
x_36 = l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_mkOptionalNode___closed__2;
x_39 = lean_array_push(x_38, x_37);
x_40 = lean_box(0);
x_41 = l_Array_empty___closed__1;
x_42 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_43 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_32, x_39, x_41, x_40, x_42, x_42, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
lean_dec(x_39);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_6 = x_44;
x_7 = x_17;
x_14 = x_45;
goto _start;
}
else
{
uint8_t x_47; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_17);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_27);
x_52 = l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
lean_inc(x_8);
x_54 = l_Lean_Elab_Term_addNamedArg(x_1, x_53, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_32, x_55, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_56);
lean_dec(x_2);
lean_dec(x_55);
return x_57;
}
else
{
uint8_t x_58; 
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_54, 0);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_54);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_31);
if (x_62 == 0)
{
return x_31;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_31, 0);
x_64 = lean_ctor_get(x_31, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_31);
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
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_26);
if (x_66 == 0)
{
return x_26;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_26, 0);
x_68 = lean_ctor_get(x_26, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_26);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
case 1:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_18, 1);
lean_inc(x_70);
lean_dec(x_18);
x_71 = lean_ctor_get(x_19, 0);
lean_inc(x_71);
lean_dec(x_19);
x_72 = lean_ctor_get(x_20, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_20, 1);
lean_inc(x_73);
lean_dec(x_20);
x_74 = l_Lean_mkProj(x_72, x_73, x_71);
x_6 = x_74;
x_7 = x_17;
x_14 = x_70;
goto _start;
}
case 2:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_76 = lean_ctor_get(x_18, 1);
lean_inc(x_76);
lean_dec(x_18);
x_77 = lean_ctor_get(x_19, 0);
lean_inc(x_77);
lean_dec(x_19);
x_78 = lean_ctor_get(x_20, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_20, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_20, 2);
lean_inc(x_80);
lean_dec(x_20);
x_81 = lean_name_eq(x_78, x_79);
if (x_81 == 0)
{
lean_object* x_82; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_82 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections(x_78, x_79, x_77, x_8, x_9, x_10, x_11, x_12, x_13, x_76);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(x_80, x_17, x_1, x_2, x_3, x_4, x_5, x_78, x_83, x_8, x_9, x_10, x_11, x_12, x_13, x_84);
return x_85;
}
else
{
uint8_t x_86; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_82);
if (x_86 == 0)
{
return x_82;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_82, 0);
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_82);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; 
lean_dec(x_79);
x_90 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(x_80, x_17, x_1, x_2, x_3, x_4, x_5, x_78, x_77, x_8, x_9, x_10, x_11, x_12, x_13, x_76);
return x_90;
}
}
case 3:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_91 = lean_ctor_get(x_18, 1);
lean_inc(x_91);
lean_dec(x_18);
x_92 = lean_ctor_get(x_19, 0);
lean_inc(x_92);
lean_dec(x_19);
x_93 = lean_ctor_get(x_20, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_20, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_20, 2);
lean_inc(x_95);
lean_dec(x_20);
x_96 = l_List_isEmpty___rarg(x_17);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; 
lean_dec(x_94);
lean_dec(x_93);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_92);
x_98 = l_Lean_mkOptionalNode___closed__2;
x_99 = lean_array_push(x_98, x_97);
x_100 = lean_box(0);
x_101 = l_Array_empty___closed__1;
x_102 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_103 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_95, x_101, x_99, x_100, x_102, x_102, x_8, x_9, x_10, x_11, x_12, x_13, x_91);
lean_dec(x_99);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_6 = x_104;
x_7 = x_17;
x_14 = x_105;
goto _start;
}
else
{
uint8_t x_107; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_103);
if (x_107 == 0)
{
return x_103;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_103, 0);
x_109 = lean_ctor_get(x_103, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_103);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; 
lean_dec(x_17);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_95);
x_111 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_95, x_8, x_9, x_10, x_11, x_12, x_13, x_91);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_114 = l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg(x_93, x_94, x_92, x_2, x_1, x_112, x_8, x_9, x_10, x_11, x_12, x_13, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_95, x_1, x_115, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_116);
lean_dec(x_115);
lean_dec(x_1);
return x_117;
}
else
{
uint8_t x_118; 
lean_dec(x_95);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_114);
if (x_118 == 0)
{
return x_114;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_114, 0);
x_120 = lean_ctor_get(x_114, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_114);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_111);
if (x_122 == 0)
{
return x_111;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_111, 0);
x_124 = lean_ctor_get(x_111, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_111);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
default: 
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = lean_ctor_get(x_18, 1);
lean_inc(x_126);
lean_dec(x_18);
x_127 = lean_ctor_get(x_19, 0);
lean_inc(x_127);
lean_dec(x_19);
x_128 = lean_ctor_get(x_20, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_20, 1);
lean_inc(x_129);
lean_dec(x_20);
x_130 = lean_box(0);
lean_inc(x_8);
x_131 = l_Lean_Elab_Term_mkConst(x_128, x_130, x_8, x_9, x_10, x_11, x_12, x_13, x_126);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_List_isEmpty___rarg(x_17);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; 
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_127);
x_136 = l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_129);
x_139 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2;
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_141 = l_Lean_mkAppStx___closed__9;
x_142 = lean_array_push(x_141, x_137);
x_143 = lean_array_push(x_142, x_140);
x_144 = lean_box(0);
x_145 = l_Array_empty___closed__1;
x_146 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_147 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_132, x_143, x_145, x_144, x_146, x_146, x_8, x_9, x_10, x_11, x_12, x_13, x_133);
lean_dec(x_143);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_6 = x_148;
x_7 = x_17;
x_14 = x_149;
goto _start;
}
else
{
uint8_t x_151; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_147);
if (x_151 == 0)
{
return x_147;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_147, 0);
x_153 = lean_ctor_get(x_147, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_147);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_17);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_127);
x_156 = l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
lean_inc(x_8);
x_158 = l_Lean_Elab_Term_addNamedArg(x_1, x_157, x_8, x_9, x_10, x_11, x_12, x_13, x_133);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_129);
x_162 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2;
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
lean_inc(x_8);
x_164 = l_Lean_Elab_Term_addNamedArg(x_159, x_163, x_8, x_9, x_10, x_11, x_12, x_13, x_160);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_132, x_165, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_166);
lean_dec(x_2);
lean_dec(x_165);
return x_167;
}
else
{
uint8_t x_168; 
lean_dec(x_132);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_168 = !lean_is_exclusive(x_164);
if (x_168 == 0)
{
return x_164;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_164, 0);
x_170 = lean_ctor_get(x_164, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_164);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_132);
lean_dec(x_129);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_172 = !lean_is_exclusive(x_158);
if (x_172 == 0)
{
return x_158;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_158, 0);
x_174 = lean_ctor_get(x_158, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_158);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_176 = !lean_is_exclusive(x_131);
if (x_176 == 0)
{
return x_131;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_131, 0);
x_178 = lean_ctor_get(x_131, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_131);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_180 = !lean_is_exclusive(x_18);
if (x_180 == 0)
{
return x_18;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_18, 0);
x_182 = lean_ctor_get(x_18, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_18);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of field notation with `@` modifier");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = l_List_isEmpty___rarg(x_2);
if (x_15 == 0)
{
if (x_6 == 0)
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(x_3, x_4, x_5, x_6, x_7, x_1, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__3;
x_18 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
x_23 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(x_3, x_4, x_5, x_6, x_7, x_1, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_23;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___lambda__1(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
return x_18;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_1, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_2, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1___rarg), 1, 0);
return x_7;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(lean_object* x_1) {
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
x_7 = l_List_map___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(x_5);
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
x_11 = l_List_map___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_53; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_List_map___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(x_21);
lean_inc(x_1);
x_23 = l_List_append___rarg(x_22, x_1);
x_24 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_53 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_20, x_23, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
if (lean_obj_tag(x_53) == 0)
{
if (x_7 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_27);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Elab_Term_SavedState_restore(x_25, x_10, x_11, x_12, x_13, x_14, x_15, x_58);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 1);
x_62 = lean_ctor_get(x_59, 0);
lean_dec(x_62);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 0, x_54);
x_63 = lean_array_push(x_8, x_59);
x_8 = x_63;
x_9 = x_19;
x_16 = x_61;
goto _start;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_dec(x_59);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_57);
x_67 = lean_array_push(x_8, x_66);
x_8 = x_67;
x_9 = x_19;
x_16 = x_65;
goto _start;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_53, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_53, 1);
lean_inc(x_70);
lean_dec(x_53);
x_71 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
x_72 = l_Lean_Elab_Term_ensureHasType(x_4, x_69, x_71, x_10, x_11, x_12, x_13, x_14, x_15, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_27);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Elab_Term_SavedState_restore(x_25, x_10, x_11, x_12, x_13, x_14, x_15, x_77);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_78, 1);
x_81 = lean_ctor_get(x_78, 0);
lean_dec(x_81);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set(x_78, 0, x_73);
x_82 = lean_array_push(x_8, x_78);
x_8 = x_82;
x_9 = x_19;
x_16 = x_80;
goto _start;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_78, 1);
lean_inc(x_84);
lean_dec(x_78);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_73);
lean_ctor_set(x_85, 1, x_76);
x_86 = lean_array_push(x_8, x_85);
x_8 = x_86;
x_9 = x_19;
x_16 = x_84;
goto _start;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_72, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_72, 1);
lean_inc(x_89);
lean_dec(x_72);
x_28 = x_88;
x_29 = x_89;
goto block_52;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_53, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_53, 1);
lean_inc(x_91);
lean_dec(x_53);
x_28 = x_90;
x_29 = x_91;
goto block_52;
}
block_52:
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_27);
x_30 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Term_SavedState_restore(x_25, x_10, x_11, x_12, x_13, x_14, x_15, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 1);
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 0, x_28);
x_37 = lean_array_push(x_8, x_33);
x_8 = x_37;
x_9 = x_19;
x_16 = x_35;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_31);
x_41 = lean_array_push(x_8, x_40);
x_8 = x_41;
x_9 = x_19;
x_16 = x_39;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_ctor_get(x_28, 0);
lean_inc(x_43);
x_44 = l_Lean_Elab_postponeExceptionId;
x_45 = lean_nat_dec_eq(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_27)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_27;
 lean_ctor_set_tag(x_46, 1);
}
lean_ctor_set(x_46, 0, x_28);
lean_ctor_set(x_46, 1, x_29);
return x_46;
}
else
{
lean_object* x_47; uint8_t x_48; 
lean_dec(x_27);
x_47 = l_Lean_Elab_Term_SavedState_restore(x_25, x_10, x_11, x_12, x_13, x_14, x_15, x_29);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 0, x_28);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_28);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_53; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_List_map___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(x_21);
lean_inc(x_1);
x_23 = l_List_append___rarg(x_22, x_1);
x_24 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_53 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_20, x_23, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
if (lean_obj_tag(x_53) == 0)
{
if (x_7 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_27);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Elab_Term_SavedState_restore(x_25, x_10, x_11, x_12, x_13, x_14, x_15, x_58);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 1);
x_62 = lean_ctor_get(x_59, 0);
lean_dec(x_62);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 0, x_54);
x_63 = lean_array_push(x_8, x_59);
x_8 = x_63;
x_9 = x_19;
x_16 = x_61;
goto _start;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_dec(x_59);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_57);
x_67 = lean_array_push(x_8, x_66);
x_8 = x_67;
x_9 = x_19;
x_16 = x_65;
goto _start;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_53, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_53, 1);
lean_inc(x_70);
lean_dec(x_53);
x_71 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
x_72 = l_Lean_Elab_Term_ensureHasType(x_4, x_69, x_71, x_10, x_11, x_12, x_13, x_14, x_15, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_27);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Elab_Term_SavedState_restore(x_25, x_10, x_11, x_12, x_13, x_14, x_15, x_77);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_78, 1);
x_81 = lean_ctor_get(x_78, 0);
lean_dec(x_81);
lean_ctor_set(x_78, 1, x_76);
lean_ctor_set(x_78, 0, x_73);
x_82 = lean_array_push(x_8, x_78);
x_8 = x_82;
x_9 = x_19;
x_16 = x_80;
goto _start;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_78, 1);
lean_inc(x_84);
lean_dec(x_78);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_73);
lean_ctor_set(x_85, 1, x_76);
x_86 = lean_array_push(x_8, x_85);
x_8 = x_86;
x_9 = x_19;
x_16 = x_84;
goto _start;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_72, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_72, 1);
lean_inc(x_89);
lean_dec(x_72);
x_28 = x_88;
x_29 = x_89;
goto block_52;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_53, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_53, 1);
lean_inc(x_91);
lean_dec(x_53);
x_28 = x_90;
x_29 = x_91;
goto block_52;
}
block_52:
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_27);
x_30 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Term_SavedState_restore(x_25, x_10, x_11, x_12, x_13, x_14, x_15, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 1);
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 0, x_28);
x_37 = lean_array_push(x_8, x_33);
x_8 = x_37;
x_9 = x_19;
x_16 = x_35;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_31);
x_41 = lean_array_push(x_8, x_40);
x_8 = x_41;
x_9 = x_19;
x_16 = x_39;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_19);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_ctor_get(x_28, 0);
lean_inc(x_43);
x_44 = l_Lean_Elab_postponeExceptionId;
x_45 = lean_nat_dec_eq(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_25);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_27)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_27;
 lean_ctor_set_tag(x_46, 1);
}
lean_ctor_set(x_46, 0, x_28);
lean_ctor_set(x_46, 1, x_29);
return x_46;
}
else
{
lean_object* x_47; uint8_t x_48; 
lean_dec(x_27);
x_47 = l_Lean_Elab_Term_SavedState_restore(x_25, x_10, x_11, x_12, x_13, x_14, x_15, x_29);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 0, x_28);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_28);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_15, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_15, 3);
lean_inc(x_23);
x_24 = l_Lean_replaceRef(x_1, x_23);
lean_dec(x_23);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_24);
lean_inc(x_13);
lean_inc(x_11);
x_26 = l_Lean_Elab_Term_resolveName(x_18, x_19, x_2, x_11, x_12, x_13, x_14, x_25, x_16, x_17);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_11, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_11, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_11, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_11, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_11, 5);
lean_inc(x_34);
x_35 = lean_ctor_get(x_11, 6);
lean_inc(x_35);
x_36 = lean_ctor_get(x_11, 7);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_11, sizeof(void*)*8);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_List_lengthAux___main___rarg(x_27, x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_dec_eq(x_39, x_40);
if (x_9 == 0)
{
uint8_t x_71; 
x_71 = lean_nat_dec_lt(x_40, x_39);
lean_dec(x_39);
x_42 = x_71;
goto block_70;
}
else
{
uint8_t x_72; 
lean_dec(x_39);
x_72 = 1;
x_42 = x_72;
goto block_70;
}
block_70:
{
if (x_41 == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_11);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_11, 7);
lean_dec(x_44);
x_45 = lean_ctor_get(x_11, 6);
lean_dec(x_45);
x_46 = lean_ctor_get(x_11, 5);
lean_dec(x_46);
x_47 = lean_ctor_get(x_11, 4);
lean_dec(x_47);
x_48 = lean_ctor_get(x_11, 3);
lean_dec(x_48);
x_49 = lean_ctor_get(x_11, 2);
lean_dec(x_49);
x_50 = lean_ctor_get(x_11, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_11, 0);
lean_dec(x_51);
x_52 = 0;
lean_ctor_set_uint8(x_11, sizeof(void*)*8 + 1, x_52);
x_53 = l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_8, x_42, x_10, x_27, x_11, x_12, x_13, x_14, x_15, x_16, x_28);
return x_53;
}
else
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_11);
x_54 = 0;
x_55 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_55, 0, x_29);
lean_ctor_set(x_55, 1, x_30);
lean_ctor_set(x_55, 2, x_31);
lean_ctor_set(x_55, 3, x_32);
lean_ctor_set(x_55, 4, x_33);
lean_ctor_set(x_55, 5, x_34);
lean_ctor_set(x_55, 6, x_35);
lean_ctor_set(x_55, 7, x_36);
lean_ctor_set_uint8(x_55, sizeof(void*)*8, x_37);
lean_ctor_set_uint8(x_55, sizeof(void*)*8 + 1, x_54);
x_56 = l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_8, x_42, x_10, x_27, x_55, x_12, x_13, x_14, x_15, x_16, x_28);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_11);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_11, 7);
lean_dec(x_58);
x_59 = lean_ctor_get(x_11, 6);
lean_dec(x_59);
x_60 = lean_ctor_get(x_11, 5);
lean_dec(x_60);
x_61 = lean_ctor_get(x_11, 4);
lean_dec(x_61);
x_62 = lean_ctor_get(x_11, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_11, 2);
lean_dec(x_63);
x_64 = lean_ctor_get(x_11, 1);
lean_dec(x_64);
x_65 = lean_ctor_get(x_11, 0);
lean_dec(x_65);
x_66 = l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4(x_3, x_4, x_5, x_6, x_7, x_8, x_42, x_10, x_27, x_11, x_12, x_13, x_14, x_15, x_16, x_28);
return x_66;
}
else
{
uint8_t x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get_uint8(x_11, sizeof(void*)*8 + 1);
lean_dec(x_11);
x_68 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_68, 0, x_29);
lean_ctor_set(x_68, 1, x_30);
lean_ctor_set(x_68, 2, x_31);
lean_ctor_set(x_68, 3, x_32);
lean_ctor_set(x_68, 4, x_33);
lean_ctor_set(x_68, 5, x_34);
lean_ctor_set(x_68, 6, x_35);
lean_ctor_set(x_68, 7, x_36);
lean_ctor_set_uint8(x_68, sizeof(void*)*8, x_37);
lean_ctor_set_uint8(x_68, sizeof(void*)*8 + 1, x_67);
x_69 = l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4(x_3, x_4, x_5, x_6, x_7, x_8, x_42, x_10, x_27, x_68, x_12, x_13, x_14, x_15, x_16, x_28);
return x_69;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_26);
if (x_73 == 0)
{
return x_26;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_26, 0);
x_75 = lean_ctor_get(x_26, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_26);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1___rarg(x_17);
return x_77;
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = lean_unbox(x_7);
lean_dec(x_7);
x_20 = l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3(x_1, x_2, x_3, x_4, x_17, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = lean_unbox(x_7);
lean_dec(x_7);
x_20 = l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4(x_1, x_2, x_3, x_4, x_17, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___boxed(lean_object** _args) {
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
uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = lean_unbox(x_8);
lean_dec(x_8);
x_20 = lean_unbox(x_9);
lean_dec(x_9);
x_21 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(x_1, x_2, x_3, x_4, x_5, x_6, x_18, x_19, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_21;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___rarg), 1, 0);
return x_7;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2(lean_object* x_1) {
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
x_7 = l_Lean_Name_toStringWithSep(x_6, x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_List_map___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2(x_5);
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
x_13 = l_Lean_Name_toStringWithSep(x_12, x_10);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_List_map___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_get_size(x_8);
x_19 = lean_nat_dec_lt(x_9, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_array_fget(x_8, x_9);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_9, x_22);
lean_dec(x_9);
x_24 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_25 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_24, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_9 = x_23;
x_10 = x_26;
x_17 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_push(x_1, x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("placeholders '_' cannot be used where a function is expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected occurrence of named pattern");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicitUniv");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("arrayRef");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namedPattern");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Expr_ctorName___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("dollarProj");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Init_LeanInit___instance__8___closed__1;
x_2 = l_System_FilePath_dirName___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
lean_inc(x_1);
x_345 = l_Lean_Syntax_getKind(x_1);
x_346 = l_Lean_choiceKind;
x_347 = lean_name_eq(x_345, x_346);
lean_dec(x_345);
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_750; lean_object* x_793; lean_object* x_819; uint8_t x_820; 
x_819 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__13;
lean_inc(x_1);
x_820 = l_Lean_Syntax_isOfKind(x_1, x_819);
if (x_820 == 0)
{
lean_object* x_821; 
x_821 = lean_box(0);
x_793 = x_821;
goto block_818;
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; uint8_t x_825; 
x_822 = l_Lean_Syntax_getArgs(x_1);
x_823 = lean_array_get_size(x_822);
lean_dec(x_822);
x_824 = lean_unsigned_to_nat(3u);
x_825 = lean_nat_dec_eq(x_823, x_824);
lean_dec(x_823);
if (x_825 == 0)
{
lean_object* x_826; 
x_826 = lean_box(0);
x_793 = x_826;
goto block_818;
}
else
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; uint8_t x_832; 
x_827 = lean_unsigned_to_nat(0u);
x_828 = l_Lean_Syntax_getArg(x_1, x_827);
x_829 = lean_unsigned_to_nat(2u);
x_830 = l_Lean_Syntax_getArg(x_1, x_829);
x_831 = l_Lean_fieldIdxKind___closed__2;
lean_inc(x_830);
x_832 = l_Lean_Syntax_isOfKind(x_830, x_831);
if (x_832 == 0)
{
lean_object* x_833; uint8_t x_834; 
x_833 = l_Lean_identKind___closed__2;
lean_inc(x_830);
x_834 = l_Lean_Syntax_isOfKind(x_830, x_833);
if (x_834 == 0)
{
uint8_t x_835; uint8_t x_836; 
lean_dec(x_830);
lean_dec(x_828);
x_835 = l_List_isEmpty___rarg(x_2);
if (x_8 == 0)
{
uint8_t x_1159; 
x_1159 = 1;
x_836 = x_1159;
goto block_1158;
}
else
{
uint8_t x_1160; 
x_1160 = 0;
x_836 = x_1160;
goto block_1158;
}
block_1158:
{
if (x_835 == 0)
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_874; lean_object* x_875; lean_object* x_897; 
x_837 = lean_box(0);
x_838 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_839 = lean_ctor_get(x_838, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_838, 1);
lean_inc(x_840);
if (lean_is_exclusive(x_838)) {
 lean_ctor_release(x_838, 0);
 lean_ctor_release(x_838, 1);
 x_841 = x_838;
} else {
 lean_dec_ref(x_838);
 x_841 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_897 = l_Lean_Elab_Term_elabTerm(x_1, x_837, x_836, x_10, x_11, x_12, x_13, x_14, x_15, x_840);
if (lean_obj_tag(x_897) == 0)
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; 
x_898 = lean_ctor_get(x_897, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_897, 1);
lean_inc(x_899);
lean_dec(x_897);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_900 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_898, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_899);
if (lean_obj_tag(x_900) == 0)
{
if (x_8 == 0)
{
lean_object* x_901; lean_object* x_902; 
lean_dec(x_841);
lean_dec(x_5);
x_901 = lean_ctor_get(x_900, 0);
lean_inc(x_901);
x_902 = lean_ctor_get(x_900, 1);
lean_inc(x_902);
lean_dec(x_900);
x_874 = x_901;
x_875 = x_902;
goto block_896;
}
else
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; 
x_903 = lean_ctor_get(x_900, 0);
lean_inc(x_903);
x_904 = lean_ctor_get(x_900, 1);
lean_inc(x_904);
lean_dec(x_900);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_905 = l_Lean_Elab_Term_ensureHasType(x_5, x_903, x_837, x_10, x_11, x_12, x_13, x_14, x_15, x_904);
if (lean_obj_tag(x_905) == 0)
{
lean_object* x_906; lean_object* x_907; 
lean_dec(x_841);
x_906 = lean_ctor_get(x_905, 0);
lean_inc(x_906);
x_907 = lean_ctor_get(x_905, 1);
lean_inc(x_907);
lean_dec(x_905);
x_874 = x_906;
x_875 = x_907;
goto block_896;
}
else
{
lean_object* x_908; lean_object* x_909; 
x_908 = lean_ctor_get(x_905, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_905, 1);
lean_inc(x_909);
lean_dec(x_905);
x_842 = x_908;
x_843 = x_909;
goto block_873;
}
}
}
else
{
lean_object* x_910; lean_object* x_911; 
lean_dec(x_5);
x_910 = lean_ctor_get(x_900, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_900, 1);
lean_inc(x_911);
lean_dec(x_900);
x_842 = x_910;
x_843 = x_911;
goto block_873;
}
}
else
{
lean_object* x_912; lean_object* x_913; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_912 = lean_ctor_get(x_897, 0);
lean_inc(x_912);
x_913 = lean_ctor_get(x_897, 1);
lean_inc(x_913);
lean_dec(x_897);
x_842 = x_912;
x_843 = x_913;
goto block_873;
}
block_873:
{
if (lean_obj_tag(x_842) == 0)
{
lean_object* x_844; uint8_t x_845; 
lean_dec(x_841);
x_844 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_843);
x_845 = !lean_is_exclusive(x_844);
if (x_845 == 0)
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; uint8_t x_849; 
x_846 = lean_ctor_get(x_844, 0);
x_847 = lean_ctor_get(x_844, 1);
x_848 = l_Lean_Elab_Term_SavedState_restore(x_839, x_10, x_11, x_12, x_13, x_14, x_15, x_847);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_849 = !lean_is_exclusive(x_848);
if (x_849 == 0)
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; 
x_850 = lean_ctor_get(x_848, 1);
x_851 = lean_ctor_get(x_848, 0);
lean_dec(x_851);
lean_ctor_set_tag(x_848, 1);
lean_ctor_set(x_848, 1, x_846);
lean_ctor_set(x_848, 0, x_842);
x_852 = lean_array_push(x_9, x_848);
lean_ctor_set(x_844, 1, x_850);
lean_ctor_set(x_844, 0, x_852);
return x_844;
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; 
x_853 = lean_ctor_get(x_848, 1);
lean_inc(x_853);
lean_dec(x_848);
x_854 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_854, 0, x_842);
lean_ctor_set(x_854, 1, x_846);
x_855 = lean_array_push(x_9, x_854);
lean_ctor_set(x_844, 1, x_853);
lean_ctor_set(x_844, 0, x_855);
return x_844;
}
}
else
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
x_856 = lean_ctor_get(x_844, 0);
x_857 = lean_ctor_get(x_844, 1);
lean_inc(x_857);
lean_inc(x_856);
lean_dec(x_844);
x_858 = l_Lean_Elab_Term_SavedState_restore(x_839, x_10, x_11, x_12, x_13, x_14, x_15, x_857);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_859 = lean_ctor_get(x_858, 1);
lean_inc(x_859);
if (lean_is_exclusive(x_858)) {
 lean_ctor_release(x_858, 0);
 lean_ctor_release(x_858, 1);
 x_860 = x_858;
} else {
 lean_dec_ref(x_858);
 x_860 = lean_box(0);
}
if (lean_is_scalar(x_860)) {
 x_861 = lean_alloc_ctor(1, 2, 0);
} else {
 x_861 = x_860;
 lean_ctor_set_tag(x_861, 1);
}
lean_ctor_set(x_861, 0, x_842);
lean_ctor_set(x_861, 1, x_856);
x_862 = lean_array_push(x_9, x_861);
x_863 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_863, 0, x_862);
lean_ctor_set(x_863, 1, x_859);
return x_863;
}
}
else
{
lean_object* x_864; lean_object* x_865; uint8_t x_866; 
lean_dec(x_9);
x_864 = lean_ctor_get(x_842, 0);
lean_inc(x_864);
x_865 = l_Lean_Elab_postponeExceptionId;
x_866 = lean_nat_dec_eq(x_864, x_865);
lean_dec(x_864);
if (x_866 == 0)
{
lean_object* x_867; 
lean_dec(x_839);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_841)) {
 x_867 = lean_alloc_ctor(1, 2, 0);
} else {
 x_867 = x_841;
 lean_ctor_set_tag(x_867, 1);
}
lean_ctor_set(x_867, 0, x_842);
lean_ctor_set(x_867, 1, x_843);
return x_867;
}
else
{
lean_object* x_868; uint8_t x_869; 
lean_dec(x_841);
x_868 = l_Lean_Elab_Term_SavedState_restore(x_839, x_10, x_11, x_12, x_13, x_14, x_15, x_843);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_869 = !lean_is_exclusive(x_868);
if (x_869 == 0)
{
lean_object* x_870; 
x_870 = lean_ctor_get(x_868, 0);
lean_dec(x_870);
lean_ctor_set_tag(x_868, 1);
lean_ctor_set(x_868, 0, x_842);
return x_868;
}
else
{
lean_object* x_871; lean_object* x_872; 
x_871 = lean_ctor_get(x_868, 1);
lean_inc(x_871);
lean_dec(x_868);
x_872 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_872, 0, x_842);
lean_ctor_set(x_872, 1, x_871);
return x_872;
}
}
}
}
block_896:
{
lean_object* x_876; uint8_t x_877; 
x_876 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_875);
x_877 = !lean_is_exclusive(x_876);
if (x_877 == 0)
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; uint8_t x_881; 
x_878 = lean_ctor_get(x_876, 0);
x_879 = lean_ctor_get(x_876, 1);
x_880 = l_Lean_Elab_Term_SavedState_restore(x_839, x_10, x_11, x_12, x_13, x_14, x_15, x_879);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_881 = !lean_is_exclusive(x_880);
if (x_881 == 0)
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; 
x_882 = lean_ctor_get(x_880, 1);
x_883 = lean_ctor_get(x_880, 0);
lean_dec(x_883);
lean_ctor_set(x_880, 1, x_878);
lean_ctor_set(x_880, 0, x_874);
x_884 = lean_array_push(x_9, x_880);
lean_ctor_set(x_876, 1, x_882);
lean_ctor_set(x_876, 0, x_884);
return x_876;
}
else
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; 
x_885 = lean_ctor_get(x_880, 1);
lean_inc(x_885);
lean_dec(x_880);
x_886 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_886, 0, x_874);
lean_ctor_set(x_886, 1, x_878);
x_887 = lean_array_push(x_9, x_886);
lean_ctor_set(x_876, 1, x_885);
lean_ctor_set(x_876, 0, x_887);
return x_876;
}
}
else
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; 
x_888 = lean_ctor_get(x_876, 0);
x_889 = lean_ctor_get(x_876, 1);
lean_inc(x_889);
lean_inc(x_888);
lean_dec(x_876);
x_890 = l_Lean_Elab_Term_SavedState_restore(x_839, x_10, x_11, x_12, x_13, x_14, x_15, x_889);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_891 = lean_ctor_get(x_890, 1);
lean_inc(x_891);
if (lean_is_exclusive(x_890)) {
 lean_ctor_release(x_890, 0);
 lean_ctor_release(x_890, 1);
 x_892 = x_890;
} else {
 lean_dec_ref(x_890);
 x_892 = lean_box(0);
}
if (lean_is_scalar(x_892)) {
 x_893 = lean_alloc_ctor(0, 2, 0);
} else {
 x_893 = x_892;
}
lean_ctor_set(x_893, 0, x_874);
lean_ctor_set(x_893, 1, x_888);
x_894 = lean_array_push(x_9, x_893);
x_895 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_895, 0, x_894);
lean_ctor_set(x_895, 1, x_891);
return x_895;
}
}
}
else
{
uint8_t x_914; 
x_914 = l_Array_isEmpty___rarg(x_3);
if (x_914 == 0)
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_952; lean_object* x_953; lean_object* x_975; 
x_915 = lean_box(0);
x_916 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_917 = lean_ctor_get(x_916, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_916, 1);
lean_inc(x_918);
if (lean_is_exclusive(x_916)) {
 lean_ctor_release(x_916, 0);
 lean_ctor_release(x_916, 1);
 x_919 = x_916;
} else {
 lean_dec_ref(x_916);
 x_919 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_975 = l_Lean_Elab_Term_elabTerm(x_1, x_915, x_836, x_10, x_11, x_12, x_13, x_14, x_15, x_918);
if (lean_obj_tag(x_975) == 0)
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; 
x_976 = lean_ctor_get(x_975, 0);
lean_inc(x_976);
x_977 = lean_ctor_get(x_975, 1);
lean_inc(x_977);
lean_dec(x_975);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_978 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_976, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_977);
if (lean_obj_tag(x_978) == 0)
{
if (x_8 == 0)
{
lean_object* x_979; lean_object* x_980; 
lean_dec(x_919);
lean_dec(x_5);
x_979 = lean_ctor_get(x_978, 0);
lean_inc(x_979);
x_980 = lean_ctor_get(x_978, 1);
lean_inc(x_980);
lean_dec(x_978);
x_952 = x_979;
x_953 = x_980;
goto block_974;
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; 
x_981 = lean_ctor_get(x_978, 0);
lean_inc(x_981);
x_982 = lean_ctor_get(x_978, 1);
lean_inc(x_982);
lean_dec(x_978);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_983 = l_Lean_Elab_Term_ensureHasType(x_5, x_981, x_915, x_10, x_11, x_12, x_13, x_14, x_15, x_982);
if (lean_obj_tag(x_983) == 0)
{
lean_object* x_984; lean_object* x_985; 
lean_dec(x_919);
x_984 = lean_ctor_get(x_983, 0);
lean_inc(x_984);
x_985 = lean_ctor_get(x_983, 1);
lean_inc(x_985);
lean_dec(x_983);
x_952 = x_984;
x_953 = x_985;
goto block_974;
}
else
{
lean_object* x_986; lean_object* x_987; 
x_986 = lean_ctor_get(x_983, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_983, 1);
lean_inc(x_987);
lean_dec(x_983);
x_920 = x_986;
x_921 = x_987;
goto block_951;
}
}
}
else
{
lean_object* x_988; lean_object* x_989; 
lean_dec(x_5);
x_988 = lean_ctor_get(x_978, 0);
lean_inc(x_988);
x_989 = lean_ctor_get(x_978, 1);
lean_inc(x_989);
lean_dec(x_978);
x_920 = x_988;
x_921 = x_989;
goto block_951;
}
}
else
{
lean_object* x_990; lean_object* x_991; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_990 = lean_ctor_get(x_975, 0);
lean_inc(x_990);
x_991 = lean_ctor_get(x_975, 1);
lean_inc(x_991);
lean_dec(x_975);
x_920 = x_990;
x_921 = x_991;
goto block_951;
}
block_951:
{
if (lean_obj_tag(x_920) == 0)
{
lean_object* x_922; uint8_t x_923; 
lean_dec(x_919);
x_922 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_921);
x_923 = !lean_is_exclusive(x_922);
if (x_923 == 0)
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; uint8_t x_927; 
x_924 = lean_ctor_get(x_922, 0);
x_925 = lean_ctor_get(x_922, 1);
x_926 = l_Lean_Elab_Term_SavedState_restore(x_917, x_10, x_11, x_12, x_13, x_14, x_15, x_925);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_927 = !lean_is_exclusive(x_926);
if (x_927 == 0)
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; 
x_928 = lean_ctor_get(x_926, 1);
x_929 = lean_ctor_get(x_926, 0);
lean_dec(x_929);
lean_ctor_set_tag(x_926, 1);
lean_ctor_set(x_926, 1, x_924);
lean_ctor_set(x_926, 0, x_920);
x_930 = lean_array_push(x_9, x_926);
lean_ctor_set(x_922, 1, x_928);
lean_ctor_set(x_922, 0, x_930);
return x_922;
}
else
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; 
x_931 = lean_ctor_get(x_926, 1);
lean_inc(x_931);
lean_dec(x_926);
x_932 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_932, 0, x_920);
lean_ctor_set(x_932, 1, x_924);
x_933 = lean_array_push(x_9, x_932);
lean_ctor_set(x_922, 1, x_931);
lean_ctor_set(x_922, 0, x_933);
return x_922;
}
}
else
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; 
x_934 = lean_ctor_get(x_922, 0);
x_935 = lean_ctor_get(x_922, 1);
lean_inc(x_935);
lean_inc(x_934);
lean_dec(x_922);
x_936 = l_Lean_Elab_Term_SavedState_restore(x_917, x_10, x_11, x_12, x_13, x_14, x_15, x_935);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_937 = lean_ctor_get(x_936, 1);
lean_inc(x_937);
if (lean_is_exclusive(x_936)) {
 lean_ctor_release(x_936, 0);
 lean_ctor_release(x_936, 1);
 x_938 = x_936;
} else {
 lean_dec_ref(x_936);
 x_938 = lean_box(0);
}
if (lean_is_scalar(x_938)) {
 x_939 = lean_alloc_ctor(1, 2, 0);
} else {
 x_939 = x_938;
 lean_ctor_set_tag(x_939, 1);
}
lean_ctor_set(x_939, 0, x_920);
lean_ctor_set(x_939, 1, x_934);
x_940 = lean_array_push(x_9, x_939);
x_941 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_941, 0, x_940);
lean_ctor_set(x_941, 1, x_937);
return x_941;
}
}
else
{
lean_object* x_942; lean_object* x_943; uint8_t x_944; 
lean_dec(x_9);
x_942 = lean_ctor_get(x_920, 0);
lean_inc(x_942);
x_943 = l_Lean_Elab_postponeExceptionId;
x_944 = lean_nat_dec_eq(x_942, x_943);
lean_dec(x_942);
if (x_944 == 0)
{
lean_object* x_945; 
lean_dec(x_917);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_919)) {
 x_945 = lean_alloc_ctor(1, 2, 0);
} else {
 x_945 = x_919;
 lean_ctor_set_tag(x_945, 1);
}
lean_ctor_set(x_945, 0, x_920);
lean_ctor_set(x_945, 1, x_921);
return x_945;
}
else
{
lean_object* x_946; uint8_t x_947; 
lean_dec(x_919);
x_946 = l_Lean_Elab_Term_SavedState_restore(x_917, x_10, x_11, x_12, x_13, x_14, x_15, x_921);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_947 = !lean_is_exclusive(x_946);
if (x_947 == 0)
{
lean_object* x_948; 
x_948 = lean_ctor_get(x_946, 0);
lean_dec(x_948);
lean_ctor_set_tag(x_946, 1);
lean_ctor_set(x_946, 0, x_920);
return x_946;
}
else
{
lean_object* x_949; lean_object* x_950; 
x_949 = lean_ctor_get(x_946, 1);
lean_inc(x_949);
lean_dec(x_946);
x_950 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_950, 0, x_920);
lean_ctor_set(x_950, 1, x_949);
return x_950;
}
}
}
}
block_974:
{
lean_object* x_954; uint8_t x_955; 
x_954 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_953);
x_955 = !lean_is_exclusive(x_954);
if (x_955 == 0)
{
lean_object* x_956; lean_object* x_957; lean_object* x_958; uint8_t x_959; 
x_956 = lean_ctor_get(x_954, 0);
x_957 = lean_ctor_get(x_954, 1);
x_958 = l_Lean_Elab_Term_SavedState_restore(x_917, x_10, x_11, x_12, x_13, x_14, x_15, x_957);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_959 = !lean_is_exclusive(x_958);
if (x_959 == 0)
{
lean_object* x_960; lean_object* x_961; lean_object* x_962; 
x_960 = lean_ctor_get(x_958, 1);
x_961 = lean_ctor_get(x_958, 0);
lean_dec(x_961);
lean_ctor_set(x_958, 1, x_956);
lean_ctor_set(x_958, 0, x_952);
x_962 = lean_array_push(x_9, x_958);
lean_ctor_set(x_954, 1, x_960);
lean_ctor_set(x_954, 0, x_962);
return x_954;
}
else
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; 
x_963 = lean_ctor_get(x_958, 1);
lean_inc(x_963);
lean_dec(x_958);
x_964 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_964, 0, x_952);
lean_ctor_set(x_964, 1, x_956);
x_965 = lean_array_push(x_9, x_964);
lean_ctor_set(x_954, 1, x_963);
lean_ctor_set(x_954, 0, x_965);
return x_954;
}
}
else
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; 
x_966 = lean_ctor_get(x_954, 0);
x_967 = lean_ctor_get(x_954, 1);
lean_inc(x_967);
lean_inc(x_966);
lean_dec(x_954);
x_968 = l_Lean_Elab_Term_SavedState_restore(x_917, x_10, x_11, x_12, x_13, x_14, x_15, x_967);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_969 = lean_ctor_get(x_968, 1);
lean_inc(x_969);
if (lean_is_exclusive(x_968)) {
 lean_ctor_release(x_968, 0);
 lean_ctor_release(x_968, 1);
 x_970 = x_968;
} else {
 lean_dec_ref(x_968);
 x_970 = lean_box(0);
}
if (lean_is_scalar(x_970)) {
 x_971 = lean_alloc_ctor(0, 2, 0);
} else {
 x_971 = x_970;
}
lean_ctor_set(x_971, 0, x_952);
lean_ctor_set(x_971, 1, x_966);
x_972 = lean_array_push(x_9, x_971);
x_973 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_973, 0, x_972);
lean_ctor_set(x_973, 1, x_969);
return x_973;
}
}
}
else
{
uint8_t x_992; 
x_992 = l_Array_isEmpty___rarg(x_4);
if (x_992 == 0)
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1030; lean_object* x_1031; lean_object* x_1053; 
x_993 = lean_box(0);
x_994 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_995 = lean_ctor_get(x_994, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_994, 1);
lean_inc(x_996);
if (lean_is_exclusive(x_994)) {
 lean_ctor_release(x_994, 0);
 lean_ctor_release(x_994, 1);
 x_997 = x_994;
} else {
 lean_dec_ref(x_994);
 x_997 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1053 = l_Lean_Elab_Term_elabTerm(x_1, x_993, x_836, x_10, x_11, x_12, x_13, x_14, x_15, x_996);
if (lean_obj_tag(x_1053) == 0)
{
lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
x_1054 = lean_ctor_get(x_1053, 0);
lean_inc(x_1054);
x_1055 = lean_ctor_get(x_1053, 1);
lean_inc(x_1055);
lean_dec(x_1053);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_1056 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_1054, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_1055);
if (lean_obj_tag(x_1056) == 0)
{
if (x_8 == 0)
{
lean_object* x_1057; lean_object* x_1058; 
lean_dec(x_997);
lean_dec(x_5);
x_1057 = lean_ctor_get(x_1056, 0);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1056, 1);
lean_inc(x_1058);
lean_dec(x_1056);
x_1030 = x_1057;
x_1031 = x_1058;
goto block_1052;
}
else
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; 
x_1059 = lean_ctor_get(x_1056, 0);
lean_inc(x_1059);
x_1060 = lean_ctor_get(x_1056, 1);
lean_inc(x_1060);
lean_dec(x_1056);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1061 = l_Lean_Elab_Term_ensureHasType(x_5, x_1059, x_993, x_10, x_11, x_12, x_13, x_14, x_15, x_1060);
if (lean_obj_tag(x_1061) == 0)
{
lean_object* x_1062; lean_object* x_1063; 
lean_dec(x_997);
x_1062 = lean_ctor_get(x_1061, 0);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_1061, 1);
lean_inc(x_1063);
lean_dec(x_1061);
x_1030 = x_1062;
x_1031 = x_1063;
goto block_1052;
}
else
{
lean_object* x_1064; lean_object* x_1065; 
x_1064 = lean_ctor_get(x_1061, 0);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_1061, 1);
lean_inc(x_1065);
lean_dec(x_1061);
x_998 = x_1064;
x_999 = x_1065;
goto block_1029;
}
}
}
else
{
lean_object* x_1066; lean_object* x_1067; 
lean_dec(x_5);
x_1066 = lean_ctor_get(x_1056, 0);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_1056, 1);
lean_inc(x_1067);
lean_dec(x_1056);
x_998 = x_1066;
x_999 = x_1067;
goto block_1029;
}
}
else
{
lean_object* x_1068; lean_object* x_1069; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1068 = lean_ctor_get(x_1053, 0);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_1053, 1);
lean_inc(x_1069);
lean_dec(x_1053);
x_998 = x_1068;
x_999 = x_1069;
goto block_1029;
}
block_1029:
{
if (lean_obj_tag(x_998) == 0)
{
lean_object* x_1000; uint8_t x_1001; 
lean_dec(x_997);
x_1000 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_999);
x_1001 = !lean_is_exclusive(x_1000);
if (x_1001 == 0)
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; uint8_t x_1005; 
x_1002 = lean_ctor_get(x_1000, 0);
x_1003 = lean_ctor_get(x_1000, 1);
x_1004 = l_Lean_Elab_Term_SavedState_restore(x_995, x_10, x_11, x_12, x_13, x_14, x_15, x_1003);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1005 = !lean_is_exclusive(x_1004);
if (x_1005 == 0)
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
x_1006 = lean_ctor_get(x_1004, 1);
x_1007 = lean_ctor_get(x_1004, 0);
lean_dec(x_1007);
lean_ctor_set_tag(x_1004, 1);
lean_ctor_set(x_1004, 1, x_1002);
lean_ctor_set(x_1004, 0, x_998);
x_1008 = lean_array_push(x_9, x_1004);
lean_ctor_set(x_1000, 1, x_1006);
lean_ctor_set(x_1000, 0, x_1008);
return x_1000;
}
else
{
lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
x_1009 = lean_ctor_get(x_1004, 1);
lean_inc(x_1009);
lean_dec(x_1004);
x_1010 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1010, 0, x_998);
lean_ctor_set(x_1010, 1, x_1002);
x_1011 = lean_array_push(x_9, x_1010);
lean_ctor_set(x_1000, 1, x_1009);
lean_ctor_set(x_1000, 0, x_1011);
return x_1000;
}
}
else
{
lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1012 = lean_ctor_get(x_1000, 0);
x_1013 = lean_ctor_get(x_1000, 1);
lean_inc(x_1013);
lean_inc(x_1012);
lean_dec(x_1000);
x_1014 = l_Lean_Elab_Term_SavedState_restore(x_995, x_10, x_11, x_12, x_13, x_14, x_15, x_1013);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1015 = lean_ctor_get(x_1014, 1);
lean_inc(x_1015);
if (lean_is_exclusive(x_1014)) {
 lean_ctor_release(x_1014, 0);
 lean_ctor_release(x_1014, 1);
 x_1016 = x_1014;
} else {
 lean_dec_ref(x_1014);
 x_1016 = lean_box(0);
}
if (lean_is_scalar(x_1016)) {
 x_1017 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1017 = x_1016;
 lean_ctor_set_tag(x_1017, 1);
}
lean_ctor_set(x_1017, 0, x_998);
lean_ctor_set(x_1017, 1, x_1012);
x_1018 = lean_array_push(x_9, x_1017);
x_1019 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1019, 0, x_1018);
lean_ctor_set(x_1019, 1, x_1015);
return x_1019;
}
}
else
{
lean_object* x_1020; lean_object* x_1021; uint8_t x_1022; 
lean_dec(x_9);
x_1020 = lean_ctor_get(x_998, 0);
lean_inc(x_1020);
x_1021 = l_Lean_Elab_postponeExceptionId;
x_1022 = lean_nat_dec_eq(x_1020, x_1021);
lean_dec(x_1020);
if (x_1022 == 0)
{
lean_object* x_1023; 
lean_dec(x_995);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_997)) {
 x_1023 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1023 = x_997;
 lean_ctor_set_tag(x_1023, 1);
}
lean_ctor_set(x_1023, 0, x_998);
lean_ctor_set(x_1023, 1, x_999);
return x_1023;
}
else
{
lean_object* x_1024; uint8_t x_1025; 
lean_dec(x_997);
x_1024 = l_Lean_Elab_Term_SavedState_restore(x_995, x_10, x_11, x_12, x_13, x_14, x_15, x_999);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1025 = !lean_is_exclusive(x_1024);
if (x_1025 == 0)
{
lean_object* x_1026; 
x_1026 = lean_ctor_get(x_1024, 0);
lean_dec(x_1026);
lean_ctor_set_tag(x_1024, 1);
lean_ctor_set(x_1024, 0, x_998);
return x_1024;
}
else
{
lean_object* x_1027; lean_object* x_1028; 
x_1027 = lean_ctor_get(x_1024, 1);
lean_inc(x_1027);
lean_dec(x_1024);
x_1028 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1028, 0, x_998);
lean_ctor_set(x_1028, 1, x_1027);
return x_1028;
}
}
}
}
block_1052:
{
lean_object* x_1032; uint8_t x_1033; 
x_1032 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1031);
x_1033 = !lean_is_exclusive(x_1032);
if (x_1033 == 0)
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; uint8_t x_1037; 
x_1034 = lean_ctor_get(x_1032, 0);
x_1035 = lean_ctor_get(x_1032, 1);
x_1036 = l_Lean_Elab_Term_SavedState_restore(x_995, x_10, x_11, x_12, x_13, x_14, x_15, x_1035);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1037 = !lean_is_exclusive(x_1036);
if (x_1037 == 0)
{
lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
x_1038 = lean_ctor_get(x_1036, 1);
x_1039 = lean_ctor_get(x_1036, 0);
lean_dec(x_1039);
lean_ctor_set(x_1036, 1, x_1034);
lean_ctor_set(x_1036, 0, x_1030);
x_1040 = lean_array_push(x_9, x_1036);
lean_ctor_set(x_1032, 1, x_1038);
lean_ctor_set(x_1032, 0, x_1040);
return x_1032;
}
else
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
x_1041 = lean_ctor_get(x_1036, 1);
lean_inc(x_1041);
lean_dec(x_1036);
x_1042 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1042, 0, x_1030);
lean_ctor_set(x_1042, 1, x_1034);
x_1043 = lean_array_push(x_9, x_1042);
lean_ctor_set(x_1032, 1, x_1041);
lean_ctor_set(x_1032, 0, x_1043);
return x_1032;
}
}
else
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
x_1044 = lean_ctor_get(x_1032, 0);
x_1045 = lean_ctor_get(x_1032, 1);
lean_inc(x_1045);
lean_inc(x_1044);
lean_dec(x_1032);
x_1046 = l_Lean_Elab_Term_SavedState_restore(x_995, x_10, x_11, x_12, x_13, x_14, x_15, x_1045);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1047 = lean_ctor_get(x_1046, 1);
lean_inc(x_1047);
if (lean_is_exclusive(x_1046)) {
 lean_ctor_release(x_1046, 0);
 lean_ctor_release(x_1046, 1);
 x_1048 = x_1046;
} else {
 lean_dec_ref(x_1046);
 x_1048 = lean_box(0);
}
if (lean_is_scalar(x_1048)) {
 x_1049 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1049 = x_1048;
}
lean_ctor_set(x_1049, 0, x_1030);
lean_ctor_set(x_1049, 1, x_1044);
x_1050 = lean_array_push(x_9, x_1049);
x_1051 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1051, 0, x_1050);
lean_ctor_set(x_1051, 1, x_1047);
return x_1051;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_8 == 0)
{
lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; uint8_t x_1097; lean_object* x_1098; 
x_1070 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_1071 = lean_ctor_get(x_1070, 0);
lean_inc(x_1071);
x_1072 = lean_ctor_get(x_1070, 1);
lean_inc(x_1072);
if (lean_is_exclusive(x_1070)) {
 lean_ctor_release(x_1070, 0);
 lean_ctor_release(x_1070, 1);
 x_1073 = x_1070;
} else {
 lean_dec_ref(x_1070);
 x_1073 = lean_box(0);
}
x_1097 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1098 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_1097, x_10, x_11, x_12, x_13, x_14, x_15, x_1072);
if (lean_obj_tag(x_1098) == 0)
{
lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; uint8_t x_1105; 
lean_dec(x_1073);
x_1099 = lean_ctor_get(x_1098, 0);
lean_inc(x_1099);
x_1100 = lean_ctor_get(x_1098, 1);
lean_inc(x_1100);
lean_dec(x_1098);
x_1101 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1100);
x_1102 = lean_ctor_get(x_1101, 0);
lean_inc(x_1102);
x_1103 = lean_ctor_get(x_1101, 1);
lean_inc(x_1103);
lean_dec(x_1101);
x_1104 = l_Lean_Elab_Term_SavedState_restore(x_1071, x_10, x_11, x_12, x_13, x_14, x_15, x_1103);
x_1105 = !lean_is_exclusive(x_1104);
if (x_1105 == 0)
{
lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; 
x_1106 = lean_ctor_get(x_1104, 1);
x_1107 = lean_ctor_get(x_1104, 0);
lean_dec(x_1107);
lean_ctor_set(x_1104, 1, x_1102);
lean_ctor_set(x_1104, 0, x_1099);
x_1108 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1104, x_10, x_11, x_12, x_13, x_14, x_15, x_1106);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1108;
}
else
{
lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; 
x_1109 = lean_ctor_get(x_1104, 1);
lean_inc(x_1109);
lean_dec(x_1104);
x_1110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1110, 0, x_1099);
lean_ctor_set(x_1110, 1, x_1102);
x_1111 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1110, x_10, x_11, x_12, x_13, x_14, x_15, x_1109);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1111;
}
}
else
{
lean_object* x_1112; lean_object* x_1113; 
x_1112 = lean_ctor_get(x_1098, 0);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_1098, 1);
lean_inc(x_1113);
lean_dec(x_1098);
x_1074 = x_1112;
x_1075 = x_1113;
goto block_1096;
}
block_1096:
{
if (lean_obj_tag(x_1074) == 0)
{
lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; uint8_t x_1080; 
lean_dec(x_1073);
x_1076 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1075);
x_1077 = lean_ctor_get(x_1076, 0);
lean_inc(x_1077);
x_1078 = lean_ctor_get(x_1076, 1);
lean_inc(x_1078);
lean_dec(x_1076);
x_1079 = l_Lean_Elab_Term_SavedState_restore(x_1071, x_10, x_11, x_12, x_13, x_14, x_15, x_1078);
x_1080 = !lean_is_exclusive(x_1079);
if (x_1080 == 0)
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
x_1081 = lean_ctor_get(x_1079, 1);
x_1082 = lean_ctor_get(x_1079, 0);
lean_dec(x_1082);
lean_ctor_set_tag(x_1079, 1);
lean_ctor_set(x_1079, 1, x_1077);
lean_ctor_set(x_1079, 0, x_1074);
x_1083 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1079, x_10, x_11, x_12, x_13, x_14, x_15, x_1081);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1083;
}
else
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; 
x_1084 = lean_ctor_get(x_1079, 1);
lean_inc(x_1084);
lean_dec(x_1079);
x_1085 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1085, 0, x_1074);
lean_ctor_set(x_1085, 1, x_1077);
x_1086 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1085, x_10, x_11, x_12, x_13, x_14, x_15, x_1084);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1086;
}
}
else
{
lean_object* x_1087; lean_object* x_1088; uint8_t x_1089; 
lean_dec(x_9);
x_1087 = lean_ctor_get(x_1074, 0);
lean_inc(x_1087);
x_1088 = l_Lean_Elab_postponeExceptionId;
x_1089 = lean_nat_dec_eq(x_1087, x_1088);
lean_dec(x_1087);
if (x_1089 == 0)
{
lean_object* x_1090; 
lean_dec(x_1071);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_1073)) {
 x_1090 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1090 = x_1073;
 lean_ctor_set_tag(x_1090, 1);
}
lean_ctor_set(x_1090, 0, x_1074);
lean_ctor_set(x_1090, 1, x_1075);
return x_1090;
}
else
{
lean_object* x_1091; uint8_t x_1092; 
lean_dec(x_1073);
x_1091 = l_Lean_Elab_Term_SavedState_restore(x_1071, x_10, x_11, x_12, x_13, x_14, x_15, x_1075);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1092 = !lean_is_exclusive(x_1091);
if (x_1092 == 0)
{
lean_object* x_1093; 
x_1093 = lean_ctor_get(x_1091, 0);
lean_dec(x_1093);
lean_ctor_set_tag(x_1091, 1);
lean_ctor_set(x_1091, 0, x_1074);
return x_1091;
}
else
{
lean_object* x_1094; lean_object* x_1095; 
x_1094 = lean_ctor_get(x_1091, 1);
lean_inc(x_1094);
lean_dec(x_1091);
x_1095 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1095, 0, x_1074);
lean_ctor_set(x_1095, 1, x_1094);
return x_1095;
}
}
}
}
}
else
{
lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1142; 
x_1114 = lean_box(0);
x_1115 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_1116 = lean_ctor_get(x_1115, 0);
lean_inc(x_1116);
x_1117 = lean_ctor_get(x_1115, 1);
lean_inc(x_1117);
if (lean_is_exclusive(x_1115)) {
 lean_ctor_release(x_1115, 0);
 lean_ctor_release(x_1115, 1);
 x_1118 = x_1115;
} else {
 lean_dec_ref(x_1115);
 x_1118 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_1142 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_836, x_1114, x_10, x_11, x_12, x_13, x_14, x_15, x_1117);
if (lean_obj_tag(x_1142) == 0)
{
lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; uint8_t x_1149; 
lean_dec(x_1118);
x_1143 = lean_ctor_get(x_1142, 0);
lean_inc(x_1143);
x_1144 = lean_ctor_get(x_1142, 1);
lean_inc(x_1144);
lean_dec(x_1142);
x_1145 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1144);
x_1146 = lean_ctor_get(x_1145, 0);
lean_inc(x_1146);
x_1147 = lean_ctor_get(x_1145, 1);
lean_inc(x_1147);
lean_dec(x_1145);
x_1148 = l_Lean_Elab_Term_SavedState_restore(x_1116, x_10, x_11, x_12, x_13, x_14, x_15, x_1147);
x_1149 = !lean_is_exclusive(x_1148);
if (x_1149 == 0)
{
lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; 
x_1150 = lean_ctor_get(x_1148, 1);
x_1151 = lean_ctor_get(x_1148, 0);
lean_dec(x_1151);
lean_ctor_set(x_1148, 1, x_1146);
lean_ctor_set(x_1148, 0, x_1143);
x_1152 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1148, x_10, x_11, x_12, x_13, x_14, x_15, x_1150);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1152;
}
else
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
x_1153 = lean_ctor_get(x_1148, 1);
lean_inc(x_1153);
lean_dec(x_1148);
x_1154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1154, 0, x_1143);
lean_ctor_set(x_1154, 1, x_1146);
x_1155 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1154, x_10, x_11, x_12, x_13, x_14, x_15, x_1153);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1155;
}
}
else
{
lean_object* x_1156; lean_object* x_1157; 
x_1156 = lean_ctor_get(x_1142, 0);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1142, 1);
lean_inc(x_1157);
lean_dec(x_1142);
x_1119 = x_1156;
x_1120 = x_1157;
goto block_1141;
}
block_1141:
{
if (lean_obj_tag(x_1119) == 0)
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; uint8_t x_1125; 
lean_dec(x_1118);
x_1121 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_1120);
x_1122 = lean_ctor_get(x_1121, 0);
lean_inc(x_1122);
x_1123 = lean_ctor_get(x_1121, 1);
lean_inc(x_1123);
lean_dec(x_1121);
x_1124 = l_Lean_Elab_Term_SavedState_restore(x_1116, x_10, x_11, x_12, x_13, x_14, x_15, x_1123);
x_1125 = !lean_is_exclusive(x_1124);
if (x_1125 == 0)
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; 
x_1126 = lean_ctor_get(x_1124, 1);
x_1127 = lean_ctor_get(x_1124, 0);
lean_dec(x_1127);
lean_ctor_set_tag(x_1124, 1);
lean_ctor_set(x_1124, 1, x_1122);
lean_ctor_set(x_1124, 0, x_1119);
x_1128 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1124, x_10, x_11, x_12, x_13, x_14, x_15, x_1126);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1128;
}
else
{
lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
x_1129 = lean_ctor_get(x_1124, 1);
lean_inc(x_1129);
lean_dec(x_1124);
x_1130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1130, 0, x_1119);
lean_ctor_set(x_1130, 1, x_1122);
x_1131 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_1130, x_10, x_11, x_12, x_13, x_14, x_15, x_1129);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1131;
}
}
else
{
lean_object* x_1132; lean_object* x_1133; uint8_t x_1134; 
lean_dec(x_9);
x_1132 = lean_ctor_get(x_1119, 0);
lean_inc(x_1132);
x_1133 = l_Lean_Elab_postponeExceptionId;
x_1134 = lean_nat_dec_eq(x_1132, x_1133);
lean_dec(x_1132);
if (x_1134 == 0)
{
lean_object* x_1135; 
lean_dec(x_1116);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_1118)) {
 x_1135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1135 = x_1118;
 lean_ctor_set_tag(x_1135, 1);
}
lean_ctor_set(x_1135, 0, x_1119);
lean_ctor_set(x_1135, 1, x_1120);
return x_1135;
}
else
{
lean_object* x_1136; uint8_t x_1137; 
lean_dec(x_1118);
x_1136 = l_Lean_Elab_Term_SavedState_restore(x_1116, x_10, x_11, x_12, x_13, x_14, x_15, x_1120);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_1137 = !lean_is_exclusive(x_1136);
if (x_1137 == 0)
{
lean_object* x_1138; 
x_1138 = lean_ctor_get(x_1136, 0);
lean_dec(x_1138);
lean_ctor_set_tag(x_1136, 1);
lean_ctor_set(x_1136, 0, x_1119);
return x_1136;
}
else
{
lean_object* x_1139; lean_object* x_1140; 
x_1139 = lean_ctor_get(x_1136, 1);
lean_inc(x_1139);
lean_dec(x_1136);
x_1140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1140, 0, x_1119);
lean_ctor_set(x_1140, 1, x_1139);
return x_1140;
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
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; 
lean_dec(x_1);
x_1161 = l_Lean_Syntax_getId(x_830);
lean_dec(x_830);
x_1162 = lean_erase_macro_scopes(x_1161);
x_1163 = l_Lean_Name_components(x_1162);
x_1164 = l_List_map___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2(x_1163);
x_1165 = l_List_append___rarg(x_1164, x_2);
x_1 = x_828;
x_2 = x_1165;
goto _start;
}
}
else
{
lean_object* x_1167; lean_object* x_1168; 
lean_dec(x_1);
x_1167 = l_Lean_fieldIdxKind;
x_1168 = l_Lean_Syntax_isNatLitAux(x_1167, x_830);
lean_dec(x_830);
if (lean_obj_tag(x_1168) == 0)
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; 
x_1169 = l_Nat_Inhabited;
x_1170 = l_Option_get_x21___rarg___closed__3;
x_1171 = lean_panic_fn(x_1169, x_1170);
x_1172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1172, 0, x_1171);
x_1173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1173, 0, x_1172);
lean_ctor_set(x_1173, 1, x_2);
x_1 = x_828;
x_2 = x_1173;
goto _start;
}
else
{
lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; 
x_1175 = lean_ctor_get(x_1168, 0);
lean_inc(x_1175);
lean_dec(x_1168);
x_1176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1176, 0, x_1175);
x_1177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1177, 0, x_1176);
lean_ctor_set(x_1177, 1, x_2);
x_1 = x_828;
x_2 = x_1177;
goto _start;
}
}
}
}
block_749:
{
lean_object* x_349; uint8_t x_350; 
lean_dec(x_348);
x_349 = l_Lean_identKind___closed__2;
lean_inc(x_1);
x_350 = l_Lean_Syntax_isOfKind(x_1, x_349);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_397; uint8_t x_398; 
x_397 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8;
lean_inc(x_1);
x_398 = l_Lean_Syntax_isOfKind(x_1, x_397);
if (x_398 == 0)
{
lean_object* x_399; 
x_399 = lean_box(0);
x_351 = x_399;
goto block_396;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; 
x_400 = l_Lean_Syntax_getArgs(x_1);
x_401 = lean_array_get_size(x_400);
lean_dec(x_400);
x_402 = lean_unsigned_to_nat(4u);
x_403 = lean_nat_dec_eq(x_401, x_402);
lean_dec(x_401);
if (x_403 == 0)
{
lean_object* x_404; 
x_404 = lean_box(0);
x_351 = x_404;
goto block_396;
}
else
{
lean_object* x_405; lean_object* x_406; uint8_t x_407; 
x_405 = lean_unsigned_to_nat(0u);
x_406 = l_Lean_Syntax_getArg(x_1, x_405);
lean_inc(x_406);
x_407 = l_Lean_Syntax_isOfKind(x_406, x_349);
if (x_407 == 0)
{
uint8_t x_408; uint8_t x_409; 
lean_dec(x_406);
x_408 = l_List_isEmpty___rarg(x_2);
if (x_8 == 0)
{
uint8_t x_732; 
x_732 = 1;
x_409 = x_732;
goto block_731;
}
else
{
uint8_t x_733; 
x_733 = 0;
x_409 = x_733;
goto block_731;
}
block_731:
{
if (x_408 == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_447; lean_object* x_448; lean_object* x_470; 
x_410 = lean_box(0);
x_411 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_414 = x_411;
} else {
 lean_dec_ref(x_411);
 x_414 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_470 = l_Lean_Elab_Term_elabTerm(x_1, x_410, x_409, x_10, x_11, x_12, x_13, x_14, x_15, x_413);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
lean_dec(x_470);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_473 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_471, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_472);
if (lean_obj_tag(x_473) == 0)
{
if (x_8 == 0)
{
lean_object* x_474; lean_object* x_475; 
lean_dec(x_414);
lean_dec(x_5);
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
lean_dec(x_473);
x_447 = x_474;
x_448 = x_475;
goto block_469;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_473, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_473, 1);
lean_inc(x_477);
lean_dec(x_473);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_478 = l_Lean_Elab_Term_ensureHasType(x_5, x_476, x_410, x_10, x_11, x_12, x_13, x_14, x_15, x_477);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; 
lean_dec(x_414);
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
lean_dec(x_478);
x_447 = x_479;
x_448 = x_480;
goto block_469;
}
else
{
lean_object* x_481; lean_object* x_482; 
x_481 = lean_ctor_get(x_478, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_478, 1);
lean_inc(x_482);
lean_dec(x_478);
x_415 = x_481;
x_416 = x_482;
goto block_446;
}
}
}
else
{
lean_object* x_483; lean_object* x_484; 
lean_dec(x_5);
x_483 = lean_ctor_get(x_473, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_473, 1);
lean_inc(x_484);
lean_dec(x_473);
x_415 = x_483;
x_416 = x_484;
goto block_446;
}
}
else
{
lean_object* x_485; lean_object* x_486; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_485 = lean_ctor_get(x_470, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_470, 1);
lean_inc(x_486);
lean_dec(x_470);
x_415 = x_485;
x_416 = x_486;
goto block_446;
}
block_446:
{
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_417; uint8_t x_418; 
lean_dec(x_414);
x_417 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_416);
x_418 = !lean_is_exclusive(x_417);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; 
x_419 = lean_ctor_get(x_417, 0);
x_420 = lean_ctor_get(x_417, 1);
x_421 = l_Lean_Elab_Term_SavedState_restore(x_412, x_10, x_11, x_12, x_13, x_14, x_15, x_420);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_422 = !lean_is_exclusive(x_421);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_421, 1);
x_424 = lean_ctor_get(x_421, 0);
lean_dec(x_424);
lean_ctor_set_tag(x_421, 1);
lean_ctor_set(x_421, 1, x_419);
lean_ctor_set(x_421, 0, x_415);
x_425 = lean_array_push(x_9, x_421);
lean_ctor_set(x_417, 1, x_423);
lean_ctor_set(x_417, 0, x_425);
return x_417;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_426 = lean_ctor_get(x_421, 1);
lean_inc(x_426);
lean_dec(x_421);
x_427 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_427, 0, x_415);
lean_ctor_set(x_427, 1, x_419);
x_428 = lean_array_push(x_9, x_427);
lean_ctor_set(x_417, 1, x_426);
lean_ctor_set(x_417, 0, x_428);
return x_417;
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_429 = lean_ctor_get(x_417, 0);
x_430 = lean_ctor_get(x_417, 1);
lean_inc(x_430);
lean_inc(x_429);
lean_dec(x_417);
x_431 = l_Lean_Elab_Term_SavedState_restore(x_412, x_10, x_11, x_12, x_13, x_14, x_15, x_430);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_432 = lean_ctor_get(x_431, 1);
lean_inc(x_432);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_433 = x_431;
} else {
 lean_dec_ref(x_431);
 x_433 = lean_box(0);
}
if (lean_is_scalar(x_433)) {
 x_434 = lean_alloc_ctor(1, 2, 0);
} else {
 x_434 = x_433;
 lean_ctor_set_tag(x_434, 1);
}
lean_ctor_set(x_434, 0, x_415);
lean_ctor_set(x_434, 1, x_429);
x_435 = lean_array_push(x_9, x_434);
x_436 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_432);
return x_436;
}
}
else
{
lean_object* x_437; lean_object* x_438; uint8_t x_439; 
lean_dec(x_9);
x_437 = lean_ctor_get(x_415, 0);
lean_inc(x_437);
x_438 = l_Lean_Elab_postponeExceptionId;
x_439 = lean_nat_dec_eq(x_437, x_438);
lean_dec(x_437);
if (x_439 == 0)
{
lean_object* x_440; 
lean_dec(x_412);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_414)) {
 x_440 = lean_alloc_ctor(1, 2, 0);
} else {
 x_440 = x_414;
 lean_ctor_set_tag(x_440, 1);
}
lean_ctor_set(x_440, 0, x_415);
lean_ctor_set(x_440, 1, x_416);
return x_440;
}
else
{
lean_object* x_441; uint8_t x_442; 
lean_dec(x_414);
x_441 = l_Lean_Elab_Term_SavedState_restore(x_412, x_10, x_11, x_12, x_13, x_14, x_15, x_416);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_442 = !lean_is_exclusive(x_441);
if (x_442 == 0)
{
lean_object* x_443; 
x_443 = lean_ctor_get(x_441, 0);
lean_dec(x_443);
lean_ctor_set_tag(x_441, 1);
lean_ctor_set(x_441, 0, x_415);
return x_441;
}
else
{
lean_object* x_444; lean_object* x_445; 
x_444 = lean_ctor_get(x_441, 1);
lean_inc(x_444);
lean_dec(x_441);
x_445 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_445, 0, x_415);
lean_ctor_set(x_445, 1, x_444);
return x_445;
}
}
}
}
block_469:
{
lean_object* x_449; uint8_t x_450; 
x_449 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_448);
x_450 = !lean_is_exclusive(x_449);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; 
x_451 = lean_ctor_get(x_449, 0);
x_452 = lean_ctor_get(x_449, 1);
x_453 = l_Lean_Elab_Term_SavedState_restore(x_412, x_10, x_11, x_12, x_13, x_14, x_15, x_452);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_454 = !lean_is_exclusive(x_453);
if (x_454 == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = lean_ctor_get(x_453, 1);
x_456 = lean_ctor_get(x_453, 0);
lean_dec(x_456);
lean_ctor_set(x_453, 1, x_451);
lean_ctor_set(x_453, 0, x_447);
x_457 = lean_array_push(x_9, x_453);
lean_ctor_set(x_449, 1, x_455);
lean_ctor_set(x_449, 0, x_457);
return x_449;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_453, 1);
lean_inc(x_458);
lean_dec(x_453);
x_459 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_459, 0, x_447);
lean_ctor_set(x_459, 1, x_451);
x_460 = lean_array_push(x_9, x_459);
lean_ctor_set(x_449, 1, x_458);
lean_ctor_set(x_449, 0, x_460);
return x_449;
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_461 = lean_ctor_get(x_449, 0);
x_462 = lean_ctor_get(x_449, 1);
lean_inc(x_462);
lean_inc(x_461);
lean_dec(x_449);
x_463 = l_Lean_Elab_Term_SavedState_restore(x_412, x_10, x_11, x_12, x_13, x_14, x_15, x_462);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_464 = lean_ctor_get(x_463, 1);
lean_inc(x_464);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_465 = x_463;
} else {
 lean_dec_ref(x_463);
 x_465 = lean_box(0);
}
if (lean_is_scalar(x_465)) {
 x_466 = lean_alloc_ctor(0, 2, 0);
} else {
 x_466 = x_465;
}
lean_ctor_set(x_466, 0, x_447);
lean_ctor_set(x_466, 1, x_461);
x_467 = lean_array_push(x_9, x_466);
x_468 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_464);
return x_468;
}
}
}
else
{
uint8_t x_487; 
x_487 = l_Array_isEmpty___rarg(x_3);
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_525; lean_object* x_526; lean_object* x_548; 
x_488 = lean_box(0);
x_489 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_490 = lean_ctor_get(x_489, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_489, 1);
lean_inc(x_491);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 lean_ctor_release(x_489, 1);
 x_492 = x_489;
} else {
 lean_dec_ref(x_489);
 x_492 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_548 = l_Lean_Elab_Term_elabTerm(x_1, x_488, x_409, x_10, x_11, x_12, x_13, x_14, x_15, x_491);
if (lean_obj_tag(x_548) == 0)
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
lean_dec(x_548);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_551 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_549, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_550);
if (lean_obj_tag(x_551) == 0)
{
if (x_8 == 0)
{
lean_object* x_552; lean_object* x_553; 
lean_dec(x_492);
lean_dec(x_5);
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
lean_dec(x_551);
x_525 = x_552;
x_526 = x_553;
goto block_547;
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_554 = lean_ctor_get(x_551, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_551, 1);
lean_inc(x_555);
lean_dec(x_551);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_556 = l_Lean_Elab_Term_ensureHasType(x_5, x_554, x_488, x_10, x_11, x_12, x_13, x_14, x_15, x_555);
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_557; lean_object* x_558; 
lean_dec(x_492);
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
lean_dec(x_556);
x_525 = x_557;
x_526 = x_558;
goto block_547;
}
else
{
lean_object* x_559; lean_object* x_560; 
x_559 = lean_ctor_get(x_556, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_556, 1);
lean_inc(x_560);
lean_dec(x_556);
x_493 = x_559;
x_494 = x_560;
goto block_524;
}
}
}
else
{
lean_object* x_561; lean_object* x_562; 
lean_dec(x_5);
x_561 = lean_ctor_get(x_551, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_551, 1);
lean_inc(x_562);
lean_dec(x_551);
x_493 = x_561;
x_494 = x_562;
goto block_524;
}
}
else
{
lean_object* x_563; lean_object* x_564; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_563 = lean_ctor_get(x_548, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_548, 1);
lean_inc(x_564);
lean_dec(x_548);
x_493 = x_563;
x_494 = x_564;
goto block_524;
}
block_524:
{
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_495; uint8_t x_496; 
lean_dec(x_492);
x_495 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_494);
x_496 = !lean_is_exclusive(x_495);
if (x_496 == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; uint8_t x_500; 
x_497 = lean_ctor_get(x_495, 0);
x_498 = lean_ctor_get(x_495, 1);
x_499 = l_Lean_Elab_Term_SavedState_restore(x_490, x_10, x_11, x_12, x_13, x_14, x_15, x_498);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_500 = !lean_is_exclusive(x_499);
if (x_500 == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_501 = lean_ctor_get(x_499, 1);
x_502 = lean_ctor_get(x_499, 0);
lean_dec(x_502);
lean_ctor_set_tag(x_499, 1);
lean_ctor_set(x_499, 1, x_497);
lean_ctor_set(x_499, 0, x_493);
x_503 = lean_array_push(x_9, x_499);
lean_ctor_set(x_495, 1, x_501);
lean_ctor_set(x_495, 0, x_503);
return x_495;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_504 = lean_ctor_get(x_499, 1);
lean_inc(x_504);
lean_dec(x_499);
x_505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_505, 0, x_493);
lean_ctor_set(x_505, 1, x_497);
x_506 = lean_array_push(x_9, x_505);
lean_ctor_set(x_495, 1, x_504);
lean_ctor_set(x_495, 0, x_506);
return x_495;
}
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_507 = lean_ctor_get(x_495, 0);
x_508 = lean_ctor_get(x_495, 1);
lean_inc(x_508);
lean_inc(x_507);
lean_dec(x_495);
x_509 = l_Lean_Elab_Term_SavedState_restore(x_490, x_10, x_11, x_12, x_13, x_14, x_15, x_508);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_510 = lean_ctor_get(x_509, 1);
lean_inc(x_510);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_511 = x_509;
} else {
 lean_dec_ref(x_509);
 x_511 = lean_box(0);
}
if (lean_is_scalar(x_511)) {
 x_512 = lean_alloc_ctor(1, 2, 0);
} else {
 x_512 = x_511;
 lean_ctor_set_tag(x_512, 1);
}
lean_ctor_set(x_512, 0, x_493);
lean_ctor_set(x_512, 1, x_507);
x_513 = lean_array_push(x_9, x_512);
x_514 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_514, 0, x_513);
lean_ctor_set(x_514, 1, x_510);
return x_514;
}
}
else
{
lean_object* x_515; lean_object* x_516; uint8_t x_517; 
lean_dec(x_9);
x_515 = lean_ctor_get(x_493, 0);
lean_inc(x_515);
x_516 = l_Lean_Elab_postponeExceptionId;
x_517 = lean_nat_dec_eq(x_515, x_516);
lean_dec(x_515);
if (x_517 == 0)
{
lean_object* x_518; 
lean_dec(x_490);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_492)) {
 x_518 = lean_alloc_ctor(1, 2, 0);
} else {
 x_518 = x_492;
 lean_ctor_set_tag(x_518, 1);
}
lean_ctor_set(x_518, 0, x_493);
lean_ctor_set(x_518, 1, x_494);
return x_518;
}
else
{
lean_object* x_519; uint8_t x_520; 
lean_dec(x_492);
x_519 = l_Lean_Elab_Term_SavedState_restore(x_490, x_10, x_11, x_12, x_13, x_14, x_15, x_494);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_520 = !lean_is_exclusive(x_519);
if (x_520 == 0)
{
lean_object* x_521; 
x_521 = lean_ctor_get(x_519, 0);
lean_dec(x_521);
lean_ctor_set_tag(x_519, 1);
lean_ctor_set(x_519, 0, x_493);
return x_519;
}
else
{
lean_object* x_522; lean_object* x_523; 
x_522 = lean_ctor_get(x_519, 1);
lean_inc(x_522);
lean_dec(x_519);
x_523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_523, 0, x_493);
lean_ctor_set(x_523, 1, x_522);
return x_523;
}
}
}
}
block_547:
{
lean_object* x_527; uint8_t x_528; 
x_527 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_526);
x_528 = !lean_is_exclusive(x_527);
if (x_528 == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; uint8_t x_532; 
x_529 = lean_ctor_get(x_527, 0);
x_530 = lean_ctor_get(x_527, 1);
x_531 = l_Lean_Elab_Term_SavedState_restore(x_490, x_10, x_11, x_12, x_13, x_14, x_15, x_530);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_532 = !lean_is_exclusive(x_531);
if (x_532 == 0)
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_533 = lean_ctor_get(x_531, 1);
x_534 = lean_ctor_get(x_531, 0);
lean_dec(x_534);
lean_ctor_set(x_531, 1, x_529);
lean_ctor_set(x_531, 0, x_525);
x_535 = lean_array_push(x_9, x_531);
lean_ctor_set(x_527, 1, x_533);
lean_ctor_set(x_527, 0, x_535);
return x_527;
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_536 = lean_ctor_get(x_531, 1);
lean_inc(x_536);
lean_dec(x_531);
x_537 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_537, 0, x_525);
lean_ctor_set(x_537, 1, x_529);
x_538 = lean_array_push(x_9, x_537);
lean_ctor_set(x_527, 1, x_536);
lean_ctor_set(x_527, 0, x_538);
return x_527;
}
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_539 = lean_ctor_get(x_527, 0);
x_540 = lean_ctor_get(x_527, 1);
lean_inc(x_540);
lean_inc(x_539);
lean_dec(x_527);
x_541 = l_Lean_Elab_Term_SavedState_restore(x_490, x_10, x_11, x_12, x_13, x_14, x_15, x_540);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_542 = lean_ctor_get(x_541, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 x_543 = x_541;
} else {
 lean_dec_ref(x_541);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_525);
lean_ctor_set(x_544, 1, x_539);
x_545 = lean_array_push(x_9, x_544);
x_546 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_546, 1, x_542);
return x_546;
}
}
}
else
{
uint8_t x_565; 
x_565 = l_Array_isEmpty___rarg(x_4);
if (x_565 == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_603; lean_object* x_604; lean_object* x_626; 
x_566 = lean_box(0);
x_567 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_567, 1);
lean_inc(x_569);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 lean_ctor_release(x_567, 1);
 x_570 = x_567;
} else {
 lean_dec_ref(x_567);
 x_570 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_626 = l_Lean_Elab_Term_elabTerm(x_1, x_566, x_409, x_10, x_11, x_12, x_13, x_14, x_15, x_569);
if (lean_obj_tag(x_626) == 0)
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_627 = lean_ctor_get(x_626, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_626, 1);
lean_inc(x_628);
lean_dec(x_626);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_629 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_627, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_628);
if (lean_obj_tag(x_629) == 0)
{
if (x_8 == 0)
{
lean_object* x_630; lean_object* x_631; 
lean_dec(x_570);
lean_dec(x_5);
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_629, 1);
lean_inc(x_631);
lean_dec(x_629);
x_603 = x_630;
x_604 = x_631;
goto block_625;
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_632 = lean_ctor_get(x_629, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_629, 1);
lean_inc(x_633);
lean_dec(x_629);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_634 = l_Lean_Elab_Term_ensureHasType(x_5, x_632, x_566, x_10, x_11, x_12, x_13, x_14, x_15, x_633);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; lean_object* x_636; 
lean_dec(x_570);
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_634, 1);
lean_inc(x_636);
lean_dec(x_634);
x_603 = x_635;
x_604 = x_636;
goto block_625;
}
else
{
lean_object* x_637; lean_object* x_638; 
x_637 = lean_ctor_get(x_634, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_634, 1);
lean_inc(x_638);
lean_dec(x_634);
x_571 = x_637;
x_572 = x_638;
goto block_602;
}
}
}
else
{
lean_object* x_639; lean_object* x_640; 
lean_dec(x_5);
x_639 = lean_ctor_get(x_629, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_629, 1);
lean_inc(x_640);
lean_dec(x_629);
x_571 = x_639;
x_572 = x_640;
goto block_602;
}
}
else
{
lean_object* x_641; lean_object* x_642; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_641 = lean_ctor_get(x_626, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_626, 1);
lean_inc(x_642);
lean_dec(x_626);
x_571 = x_641;
x_572 = x_642;
goto block_602;
}
block_602:
{
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_573; uint8_t x_574; 
lean_dec(x_570);
x_573 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_572);
x_574 = !lean_is_exclusive(x_573);
if (x_574 == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; uint8_t x_578; 
x_575 = lean_ctor_get(x_573, 0);
x_576 = lean_ctor_get(x_573, 1);
x_577 = l_Lean_Elab_Term_SavedState_restore(x_568, x_10, x_11, x_12, x_13, x_14, x_15, x_576);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_578 = !lean_is_exclusive(x_577);
if (x_578 == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_579 = lean_ctor_get(x_577, 1);
x_580 = lean_ctor_get(x_577, 0);
lean_dec(x_580);
lean_ctor_set_tag(x_577, 1);
lean_ctor_set(x_577, 1, x_575);
lean_ctor_set(x_577, 0, x_571);
x_581 = lean_array_push(x_9, x_577);
lean_ctor_set(x_573, 1, x_579);
lean_ctor_set(x_573, 0, x_581);
return x_573;
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_582 = lean_ctor_get(x_577, 1);
lean_inc(x_582);
lean_dec(x_577);
x_583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_583, 0, x_571);
lean_ctor_set(x_583, 1, x_575);
x_584 = lean_array_push(x_9, x_583);
lean_ctor_set(x_573, 1, x_582);
lean_ctor_set(x_573, 0, x_584);
return x_573;
}
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_585 = lean_ctor_get(x_573, 0);
x_586 = lean_ctor_get(x_573, 1);
lean_inc(x_586);
lean_inc(x_585);
lean_dec(x_573);
x_587 = l_Lean_Elab_Term_SavedState_restore(x_568, x_10, x_11, x_12, x_13, x_14, x_15, x_586);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_588 = lean_ctor_get(x_587, 1);
lean_inc(x_588);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_589 = x_587;
} else {
 lean_dec_ref(x_587);
 x_589 = lean_box(0);
}
if (lean_is_scalar(x_589)) {
 x_590 = lean_alloc_ctor(1, 2, 0);
} else {
 x_590 = x_589;
 lean_ctor_set_tag(x_590, 1);
}
lean_ctor_set(x_590, 0, x_571);
lean_ctor_set(x_590, 1, x_585);
x_591 = lean_array_push(x_9, x_590);
x_592 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_592, 0, x_591);
lean_ctor_set(x_592, 1, x_588);
return x_592;
}
}
else
{
lean_object* x_593; lean_object* x_594; uint8_t x_595; 
lean_dec(x_9);
x_593 = lean_ctor_get(x_571, 0);
lean_inc(x_593);
x_594 = l_Lean_Elab_postponeExceptionId;
x_595 = lean_nat_dec_eq(x_593, x_594);
lean_dec(x_593);
if (x_595 == 0)
{
lean_object* x_596; 
lean_dec(x_568);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_570)) {
 x_596 = lean_alloc_ctor(1, 2, 0);
} else {
 x_596 = x_570;
 lean_ctor_set_tag(x_596, 1);
}
lean_ctor_set(x_596, 0, x_571);
lean_ctor_set(x_596, 1, x_572);
return x_596;
}
else
{
lean_object* x_597; uint8_t x_598; 
lean_dec(x_570);
x_597 = l_Lean_Elab_Term_SavedState_restore(x_568, x_10, x_11, x_12, x_13, x_14, x_15, x_572);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_598 = !lean_is_exclusive(x_597);
if (x_598 == 0)
{
lean_object* x_599; 
x_599 = lean_ctor_get(x_597, 0);
lean_dec(x_599);
lean_ctor_set_tag(x_597, 1);
lean_ctor_set(x_597, 0, x_571);
return x_597;
}
else
{
lean_object* x_600; lean_object* x_601; 
x_600 = lean_ctor_get(x_597, 1);
lean_inc(x_600);
lean_dec(x_597);
x_601 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_601, 0, x_571);
lean_ctor_set(x_601, 1, x_600);
return x_601;
}
}
}
}
block_625:
{
lean_object* x_605; uint8_t x_606; 
x_605 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_604);
x_606 = !lean_is_exclusive(x_605);
if (x_606 == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; 
x_607 = lean_ctor_get(x_605, 0);
x_608 = lean_ctor_get(x_605, 1);
x_609 = l_Lean_Elab_Term_SavedState_restore(x_568, x_10, x_11, x_12, x_13, x_14, x_15, x_608);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_610 = !lean_is_exclusive(x_609);
if (x_610 == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_611 = lean_ctor_get(x_609, 1);
x_612 = lean_ctor_get(x_609, 0);
lean_dec(x_612);
lean_ctor_set(x_609, 1, x_607);
lean_ctor_set(x_609, 0, x_603);
x_613 = lean_array_push(x_9, x_609);
lean_ctor_set(x_605, 1, x_611);
lean_ctor_set(x_605, 0, x_613);
return x_605;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = lean_ctor_get(x_609, 1);
lean_inc(x_614);
lean_dec(x_609);
x_615 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_615, 0, x_603);
lean_ctor_set(x_615, 1, x_607);
x_616 = lean_array_push(x_9, x_615);
lean_ctor_set(x_605, 1, x_614);
lean_ctor_set(x_605, 0, x_616);
return x_605;
}
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_617 = lean_ctor_get(x_605, 0);
x_618 = lean_ctor_get(x_605, 1);
lean_inc(x_618);
lean_inc(x_617);
lean_dec(x_605);
x_619 = l_Lean_Elab_Term_SavedState_restore(x_568, x_10, x_11, x_12, x_13, x_14, x_15, x_618);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_620 = lean_ctor_get(x_619, 1);
lean_inc(x_620);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_621 = x_619;
} else {
 lean_dec_ref(x_619);
 x_621 = lean_box(0);
}
if (lean_is_scalar(x_621)) {
 x_622 = lean_alloc_ctor(0, 2, 0);
} else {
 x_622 = x_621;
}
lean_ctor_set(x_622, 0, x_603);
lean_ctor_set(x_622, 1, x_617);
x_623 = lean_array_push(x_9, x_622);
x_624 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_624, 0, x_623);
lean_ctor_set(x_624, 1, x_620);
return x_624;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_8 == 0)
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_670; lean_object* x_671; 
x_643 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_643, 1);
lean_inc(x_645);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_646 = x_643;
} else {
 lean_dec_ref(x_643);
 x_646 = lean_box(0);
}
x_670 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_671 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_670, x_10, x_11, x_12, x_13, x_14, x_15, x_645);
if (lean_obj_tag(x_671) == 0)
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; uint8_t x_678; 
lean_dec(x_646);
x_672 = lean_ctor_get(x_671, 0);
lean_inc(x_672);
x_673 = lean_ctor_get(x_671, 1);
lean_inc(x_673);
lean_dec(x_671);
x_674 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_673);
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
lean_dec(x_674);
x_677 = l_Lean_Elab_Term_SavedState_restore(x_644, x_10, x_11, x_12, x_13, x_14, x_15, x_676);
x_678 = !lean_is_exclusive(x_677);
if (x_678 == 0)
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_679 = lean_ctor_get(x_677, 1);
x_680 = lean_ctor_get(x_677, 0);
lean_dec(x_680);
lean_ctor_set(x_677, 1, x_675);
lean_ctor_set(x_677, 0, x_672);
x_681 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_677, x_10, x_11, x_12, x_13, x_14, x_15, x_679);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_681;
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_682 = lean_ctor_get(x_677, 1);
lean_inc(x_682);
lean_dec(x_677);
x_683 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_683, 0, x_672);
lean_ctor_set(x_683, 1, x_675);
x_684 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_683, x_10, x_11, x_12, x_13, x_14, x_15, x_682);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_684;
}
}
else
{
lean_object* x_685; lean_object* x_686; 
x_685 = lean_ctor_get(x_671, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_671, 1);
lean_inc(x_686);
lean_dec(x_671);
x_647 = x_685;
x_648 = x_686;
goto block_669;
}
block_669:
{
if (lean_obj_tag(x_647) == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; uint8_t x_653; 
lean_dec(x_646);
x_649 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_648);
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_649, 1);
lean_inc(x_651);
lean_dec(x_649);
x_652 = l_Lean_Elab_Term_SavedState_restore(x_644, x_10, x_11, x_12, x_13, x_14, x_15, x_651);
x_653 = !lean_is_exclusive(x_652);
if (x_653 == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_654 = lean_ctor_get(x_652, 1);
x_655 = lean_ctor_get(x_652, 0);
lean_dec(x_655);
lean_ctor_set_tag(x_652, 1);
lean_ctor_set(x_652, 1, x_650);
lean_ctor_set(x_652, 0, x_647);
x_656 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_652, x_10, x_11, x_12, x_13, x_14, x_15, x_654);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_656;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_657 = lean_ctor_get(x_652, 1);
lean_inc(x_657);
lean_dec(x_652);
x_658 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_658, 0, x_647);
lean_ctor_set(x_658, 1, x_650);
x_659 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_658, x_10, x_11, x_12, x_13, x_14, x_15, x_657);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_659;
}
}
else
{
lean_object* x_660; lean_object* x_661; uint8_t x_662; 
lean_dec(x_9);
x_660 = lean_ctor_get(x_647, 0);
lean_inc(x_660);
x_661 = l_Lean_Elab_postponeExceptionId;
x_662 = lean_nat_dec_eq(x_660, x_661);
lean_dec(x_660);
if (x_662 == 0)
{
lean_object* x_663; 
lean_dec(x_644);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_646)) {
 x_663 = lean_alloc_ctor(1, 2, 0);
} else {
 x_663 = x_646;
 lean_ctor_set_tag(x_663, 1);
}
lean_ctor_set(x_663, 0, x_647);
lean_ctor_set(x_663, 1, x_648);
return x_663;
}
else
{
lean_object* x_664; uint8_t x_665; 
lean_dec(x_646);
x_664 = l_Lean_Elab_Term_SavedState_restore(x_644, x_10, x_11, x_12, x_13, x_14, x_15, x_648);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_665 = !lean_is_exclusive(x_664);
if (x_665 == 0)
{
lean_object* x_666; 
x_666 = lean_ctor_get(x_664, 0);
lean_dec(x_666);
lean_ctor_set_tag(x_664, 1);
lean_ctor_set(x_664, 0, x_647);
return x_664;
}
else
{
lean_object* x_667; lean_object* x_668; 
x_667 = lean_ctor_get(x_664, 1);
lean_inc(x_667);
lean_dec(x_664);
x_668 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_668, 0, x_647);
lean_ctor_set(x_668, 1, x_667);
return x_668;
}
}
}
}
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_715; 
x_687 = lean_box(0);
x_688 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
x_690 = lean_ctor_get(x_688, 1);
lean_inc(x_690);
if (lean_is_exclusive(x_688)) {
 lean_ctor_release(x_688, 0);
 lean_ctor_release(x_688, 1);
 x_691 = x_688;
} else {
 lean_dec_ref(x_688);
 x_691 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_715 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_409, x_687, x_10, x_11, x_12, x_13, x_14, x_15, x_690);
if (lean_obj_tag(x_715) == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; uint8_t x_722; 
lean_dec(x_691);
x_716 = lean_ctor_get(x_715, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_715, 1);
lean_inc(x_717);
lean_dec(x_715);
x_718 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_717);
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_718, 1);
lean_inc(x_720);
lean_dec(x_718);
x_721 = l_Lean_Elab_Term_SavedState_restore(x_689, x_10, x_11, x_12, x_13, x_14, x_15, x_720);
x_722 = !lean_is_exclusive(x_721);
if (x_722 == 0)
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_723 = lean_ctor_get(x_721, 1);
x_724 = lean_ctor_get(x_721, 0);
lean_dec(x_724);
lean_ctor_set(x_721, 1, x_719);
lean_ctor_set(x_721, 0, x_716);
x_725 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_721, x_10, x_11, x_12, x_13, x_14, x_15, x_723);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_725;
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_726 = lean_ctor_get(x_721, 1);
lean_inc(x_726);
lean_dec(x_721);
x_727 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_727, 0, x_716);
lean_ctor_set(x_727, 1, x_719);
x_728 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_727, x_10, x_11, x_12, x_13, x_14, x_15, x_726);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_728;
}
}
else
{
lean_object* x_729; lean_object* x_730; 
x_729 = lean_ctor_get(x_715, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_715, 1);
lean_inc(x_730);
lean_dec(x_715);
x_692 = x_729;
x_693 = x_730;
goto block_714;
}
block_714:
{
if (lean_obj_tag(x_692) == 0)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; uint8_t x_698; 
lean_dec(x_691);
x_694 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_693);
x_695 = lean_ctor_get(x_694, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_694, 1);
lean_inc(x_696);
lean_dec(x_694);
x_697 = l_Lean_Elab_Term_SavedState_restore(x_689, x_10, x_11, x_12, x_13, x_14, x_15, x_696);
x_698 = !lean_is_exclusive(x_697);
if (x_698 == 0)
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; 
x_699 = lean_ctor_get(x_697, 1);
x_700 = lean_ctor_get(x_697, 0);
lean_dec(x_700);
lean_ctor_set_tag(x_697, 1);
lean_ctor_set(x_697, 1, x_695);
lean_ctor_set(x_697, 0, x_692);
x_701 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_697, x_10, x_11, x_12, x_13, x_14, x_15, x_699);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_701;
}
else
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_702 = lean_ctor_get(x_697, 1);
lean_inc(x_702);
lean_dec(x_697);
x_703 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_703, 0, x_692);
lean_ctor_set(x_703, 1, x_695);
x_704 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_703, x_10, x_11, x_12, x_13, x_14, x_15, x_702);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_704;
}
}
else
{
lean_object* x_705; lean_object* x_706; uint8_t x_707; 
lean_dec(x_9);
x_705 = lean_ctor_get(x_692, 0);
lean_inc(x_705);
x_706 = l_Lean_Elab_postponeExceptionId;
x_707 = lean_nat_dec_eq(x_705, x_706);
lean_dec(x_705);
if (x_707 == 0)
{
lean_object* x_708; 
lean_dec(x_689);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_691)) {
 x_708 = lean_alloc_ctor(1, 2, 0);
} else {
 x_708 = x_691;
 lean_ctor_set_tag(x_708, 1);
}
lean_ctor_set(x_708, 0, x_692);
lean_ctor_set(x_708, 1, x_693);
return x_708;
}
else
{
lean_object* x_709; uint8_t x_710; 
lean_dec(x_691);
x_709 = l_Lean_Elab_Term_SavedState_restore(x_689, x_10, x_11, x_12, x_13, x_14, x_15, x_693);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_710 = !lean_is_exclusive(x_709);
if (x_710 == 0)
{
lean_object* x_711; 
x_711 = lean_ctor_get(x_709, 0);
lean_dec(x_711);
lean_ctor_set_tag(x_709, 1);
lean_ctor_set(x_709, 0, x_692);
return x_709;
}
else
{
lean_object* x_712; lean_object* x_713; 
x_712 = lean_ctor_get(x_709, 1);
lean_inc(x_712);
lean_dec(x_709);
x_713 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_713, 0, x_692);
lean_ctor_set(x_713, 1, x_712);
return x_713;
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
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_734 = lean_unsigned_to_nat(2u);
x_735 = l_Lean_Syntax_getArg(x_1, x_734);
lean_dec(x_1);
x_736 = l_Lean_Syntax_getArgs(x_735);
lean_dec(x_735);
x_737 = l_Array_empty___closed__1;
x_738 = l_Array_foldlStepMAux___main___at_Lean_Syntax_getSepArgs___spec__1(x_734, x_736, x_405, x_737);
lean_dec(x_736);
x_739 = l_Lean_Elab_Term_elabExplicitUnivs(x_738, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_738);
if (lean_obj_tag(x_739) == 0)
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_740 = lean_ctor_get(x_739, 0);
lean_inc(x_740);
x_741 = lean_ctor_get(x_739, 1);
lean_inc(x_741);
lean_dec(x_739);
x_742 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(x_406, x_740, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_741);
return x_742;
}
else
{
uint8_t x_743; 
lean_dec(x_406);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_743 = !lean_is_exclusive(x_739);
if (x_743 == 0)
{
return x_739;
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; 
x_744 = lean_ctor_get(x_739, 0);
x_745 = lean_ctor_get(x_739, 1);
lean_inc(x_745);
lean_inc(x_744);
lean_dec(x_739);
x_746 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_746, 0, x_744);
lean_ctor_set(x_746, 1, x_745);
return x_746;
}
}
}
}
}
block_396:
{
lean_object* x_352; uint8_t x_353; 
lean_dec(x_351);
x_352 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_isExplicit___closed__2;
lean_inc(x_1);
x_353 = l_Lean_Syntax_isOfKind(x_1, x_352);
if (x_353 == 0)
{
lean_object* x_354; uint8_t x_355; 
x_354 = l_Lean_mkHole___closed__2;
lean_inc(x_1);
x_355 = l_Lean_Syntax_isOfKind(x_1, x_354);
if (x_355 == 0)
{
lean_object* x_356; 
x_356 = lean_box(0);
x_17 = x_356;
goto block_344;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; 
x_357 = l_Lean_Syntax_getArgs(x_1);
x_358 = lean_array_get_size(x_357);
lean_dec(x_357);
x_359 = lean_unsigned_to_nat(1u);
x_360 = lean_nat_dec_eq(x_358, x_359);
lean_dec(x_358);
if (x_360 == 0)
{
lean_object* x_361; 
x_361 = lean_box(0);
x_17 = x_361;
goto block_344;
}
else
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_362 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3;
x_363 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_362, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_363;
}
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; 
x_364 = l_Lean_Syntax_getArgs(x_1);
x_365 = lean_array_get_size(x_364);
lean_dec(x_364);
x_366 = lean_unsigned_to_nat(2u);
x_367 = lean_nat_dec_eq(x_365, x_366);
if (x_367 == 0)
{
lean_object* x_368; uint8_t x_369; 
x_368 = l_Lean_mkHole___closed__2;
lean_inc(x_1);
x_369 = l_Lean_Syntax_isOfKind(x_1, x_368);
if (x_369 == 0)
{
lean_object* x_370; 
lean_dec(x_365);
x_370 = lean_box(0);
x_17 = x_370;
goto block_344;
}
else
{
lean_object* x_371; uint8_t x_372; 
x_371 = lean_unsigned_to_nat(1u);
x_372 = lean_nat_dec_eq(x_365, x_371);
lean_dec(x_365);
if (x_372 == 0)
{
lean_object* x_373; 
x_373 = lean_box(0);
x_17 = x_373;
goto block_344;
}
else
{
lean_object* x_374; lean_object* x_375; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_374 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3;
x_375 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_374, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_375;
}
}
}
else
{
lean_object* x_376; lean_object* x_377; uint8_t x_378; 
lean_dec(x_365);
x_376 = lean_unsigned_to_nat(1u);
x_377 = l_Lean_Syntax_getArg(x_1, x_376);
lean_inc(x_377);
x_378 = l_Lean_Syntax_isOfKind(x_377, x_349);
if (x_378 == 0)
{
lean_object* x_379; uint8_t x_380; 
x_379 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8;
lean_inc(x_377);
x_380 = l_Lean_Syntax_isOfKind(x_377, x_379);
if (x_380 == 0)
{
lean_object* x_381; 
lean_dec(x_377);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_381 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___rarg(x_16);
return x_381;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_382 = l_Lean_Syntax_getArgs(x_377);
x_383 = lean_array_get_size(x_382);
lean_dec(x_382);
x_384 = lean_unsigned_to_nat(4u);
x_385 = lean_nat_dec_eq(x_383, x_384);
lean_dec(x_383);
if (x_385 == 0)
{
lean_object* x_386; 
lean_dec(x_377);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_386 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___rarg(x_16);
return x_386;
}
else
{
lean_object* x_387; lean_object* x_388; uint8_t x_389; 
x_387 = lean_unsigned_to_nat(0u);
x_388 = l_Lean_Syntax_getArg(x_377, x_387);
lean_dec(x_377);
x_389 = l_Lean_Syntax_isOfKind(x_388, x_349);
if (x_389 == 0)
{
lean_object* x_390; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_390 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___rarg(x_16);
return x_390;
}
else
{
lean_object* x_391; uint8_t x_392; 
x_391 = l_Lean_Syntax_getArg(x_1, x_376);
lean_dec(x_1);
x_392 = 1;
x_1 = x_391;
x_6 = x_392;
goto _start;
}
}
}
}
else
{
uint8_t x_394; 
lean_dec(x_1);
x_394 = 1;
x_1 = x_377;
x_6 = x_394;
goto _start;
}
}
}
}
}
else
{
lean_object* x_747; lean_object* x_748; 
x_747 = lean_box(0);
x_748 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(x_1, x_747, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_748;
}
}
block_792:
{
lean_object* x_751; uint8_t x_752; 
lean_dec(x_750);
x_751 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__10;
lean_inc(x_1);
x_752 = l_Lean_Syntax_isOfKind(x_1, x_751);
if (x_752 == 0)
{
lean_object* x_753; uint8_t x_754; 
x_753 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12;
lean_inc(x_1);
x_754 = l_Lean_Syntax_isOfKind(x_1, x_753);
if (x_754 == 0)
{
lean_object* x_755; 
x_755 = lean_box(0);
x_348 = x_755;
goto block_749;
}
else
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; uint8_t x_759; 
x_756 = l_Lean_Syntax_getArgs(x_1);
x_757 = lean_array_get_size(x_756);
lean_dec(x_756);
x_758 = lean_unsigned_to_nat(3u);
x_759 = lean_nat_dec_eq(x_757, x_758);
lean_dec(x_757);
if (x_759 == 0)
{
lean_object* x_760; 
x_760 = lean_box(0);
x_348 = x_760;
goto block_749;
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; uint8_t x_764; 
x_761 = lean_unsigned_to_nat(0u);
x_762 = l_Lean_Syntax_getArg(x_1, x_761);
x_763 = l_Lean_identKind___closed__2;
x_764 = l_Lean_Syntax_isOfKind(x_762, x_763);
if (x_764 == 0)
{
lean_object* x_765; 
x_765 = lean_box(0);
x_17 = x_765;
goto block_344;
}
else
{
lean_object* x_766; lean_object* x_767; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_766 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__6;
x_767 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_766, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_767;
}
}
}
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; uint8_t x_771; 
x_768 = l_Lean_Syntax_getArgs(x_1);
x_769 = lean_array_get_size(x_768);
lean_dec(x_768);
x_770 = lean_unsigned_to_nat(4u);
x_771 = lean_nat_dec_eq(x_769, x_770);
if (x_771 == 0)
{
lean_object* x_772; uint8_t x_773; 
x_772 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12;
lean_inc(x_1);
x_773 = l_Lean_Syntax_isOfKind(x_1, x_772);
if (x_773 == 0)
{
lean_object* x_774; 
lean_dec(x_769);
x_774 = lean_box(0);
x_348 = x_774;
goto block_749;
}
else
{
lean_object* x_775; uint8_t x_776; 
x_775 = lean_unsigned_to_nat(3u);
x_776 = lean_nat_dec_eq(x_769, x_775);
lean_dec(x_769);
if (x_776 == 0)
{
lean_object* x_777; 
x_777 = lean_box(0);
x_348 = x_777;
goto block_749;
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; uint8_t x_781; 
x_778 = lean_unsigned_to_nat(0u);
x_779 = l_Lean_Syntax_getArg(x_1, x_778);
x_780 = l_Lean_identKind___closed__2;
x_781 = l_Lean_Syntax_isOfKind(x_779, x_780);
if (x_781 == 0)
{
lean_object* x_782; 
x_782 = lean_box(0);
x_17 = x_782;
goto block_344;
}
else
{
lean_object* x_783; lean_object* x_784; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_783 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__6;
x_784 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_783, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_784;
}
}
}
}
else
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
lean_dec(x_769);
x_785 = lean_unsigned_to_nat(0u);
x_786 = l_Lean_Syntax_getArg(x_1, x_785);
x_787 = lean_unsigned_to_nat(2u);
x_788 = l_Lean_Syntax_getArg(x_1, x_787);
lean_dec(x_1);
x_789 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_789, 0, x_788);
x_790 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_790, 0, x_789);
lean_ctor_set(x_790, 1, x_2);
x_1 = x_786;
x_2 = x_790;
goto _start;
}
}
}
block_818:
{
lean_object* x_794; uint8_t x_795; 
lean_dec(x_793);
x_794 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__15;
lean_inc(x_1);
x_795 = l_Lean_Syntax_isOfKind(x_1, x_794);
if (x_795 == 0)
{
lean_object* x_796; 
x_796 = lean_box(0);
x_750 = x_796;
goto block_792;
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; uint8_t x_800; 
x_797 = l_Lean_Syntax_getArgs(x_1);
x_798 = lean_array_get_size(x_797);
lean_dec(x_797);
x_799 = lean_unsigned_to_nat(3u);
x_800 = lean_nat_dec_eq(x_798, x_799);
lean_dec(x_798);
if (x_800 == 0)
{
lean_object* x_801; 
x_801 = lean_box(0);
x_750 = x_801;
goto block_792;
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_802 = lean_unsigned_to_nat(0u);
x_803 = l_Lean_Syntax_getArg(x_1, x_802);
x_804 = lean_unsigned_to_nat(2u);
x_805 = l_Lean_Syntax_getArg(x_1, x_804);
lean_dec(x_1);
x_806 = l_Lean_Elab_Term_getCurrMacroScope(x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_807 = lean_ctor_get(x_806, 1);
lean_inc(x_807);
lean_dec(x_806);
x_808 = l_Lean_Elab_Term_getMainModule___rarg(x_15, x_807);
x_809 = lean_ctor_get(x_808, 1);
lean_inc(x_809);
lean_dec(x_808);
x_810 = l_Array_empty___closed__1;
x_811 = lean_array_push(x_810, x_803);
x_812 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__16;
x_813 = lean_array_push(x_811, x_812);
x_814 = lean_array_push(x_813, x_805);
x_815 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__13;
x_816 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_816, 0, x_815);
lean_ctor_set(x_816, 1, x_814);
x_1 = x_816;
x_16 = x_809;
goto _start;
}
}
}
}
else
{
lean_object* x_1179; uint8_t x_1180; 
x_1179 = l_Lean_Syntax_getArgs(x_1);
x_1180 = !lean_is_exclusive(x_10);
if (x_1180 == 0)
{
uint8_t x_1181; lean_object* x_1182; lean_object* x_1183; 
x_1181 = 0;
lean_ctor_set_uint8(x_10, sizeof(void*)*8 + 1, x_1181);
x_1182 = lean_unsigned_to_nat(0u);
x_1183 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_1179, x_1182, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1179);
lean_dec(x_1);
return x_1183;
}
else
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; uint8_t x_1192; uint8_t x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; 
x_1184 = lean_ctor_get(x_10, 0);
x_1185 = lean_ctor_get(x_10, 1);
x_1186 = lean_ctor_get(x_10, 2);
x_1187 = lean_ctor_get(x_10, 3);
x_1188 = lean_ctor_get(x_10, 4);
x_1189 = lean_ctor_get(x_10, 5);
x_1190 = lean_ctor_get(x_10, 6);
x_1191 = lean_ctor_get(x_10, 7);
x_1192 = lean_ctor_get_uint8(x_10, sizeof(void*)*8);
lean_inc(x_1191);
lean_inc(x_1190);
lean_inc(x_1189);
lean_inc(x_1188);
lean_inc(x_1187);
lean_inc(x_1186);
lean_inc(x_1185);
lean_inc(x_1184);
lean_dec(x_10);
x_1193 = 0;
x_1194 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1194, 0, x_1184);
lean_ctor_set(x_1194, 1, x_1185);
lean_ctor_set(x_1194, 2, x_1186);
lean_ctor_set(x_1194, 3, x_1187);
lean_ctor_set(x_1194, 4, x_1188);
lean_ctor_set(x_1194, 5, x_1189);
lean_ctor_set(x_1194, 6, x_1190);
lean_ctor_set(x_1194, 7, x_1191);
lean_ctor_set_uint8(x_1194, sizeof(void*)*8, x_1192);
lean_ctor_set_uint8(x_1194, sizeof(void*)*8 + 1, x_1193);
x_1195 = lean_unsigned_to_nat(0u);
x_1196 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_1179, x_1195, x_9, x_1194, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_1179);
lean_dec(x_1);
return x_1196;
}
}
block_344:
{
uint8_t x_18; uint8_t x_19; 
lean_dec(x_17);
x_18 = l_List_isEmpty___rarg(x_2);
if (x_8 == 0)
{
uint8_t x_342; 
x_342 = 1;
x_19 = x_342;
goto block_341;
}
else
{
uint8_t x_343; 
x_343 = 0;
x_19 = x_343;
goto block_341;
}
block_341:
{
if (x_18 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_57; lean_object* x_58; lean_object* x_80; 
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_80 = l_Lean_Elab_Term_elabTerm(x_1, x_20, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_23);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_83 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_81, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_82);
if (lean_obj_tag(x_83) == 0)
{
if (x_8 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_24);
lean_dec(x_5);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_57 = x_84;
x_58 = x_85;
goto block_79;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
lean_dec(x_83);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_88 = l_Lean_Elab_Term_ensureHasType(x_5, x_86, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_24);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_57 = x_89;
x_58 = x_90;
goto block_79;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_88, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_25 = x_91;
x_26 = x_92;
goto block_56;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_5);
x_93 = lean_ctor_get(x_83, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_83, 1);
lean_inc(x_94);
lean_dec(x_83);
x_25 = x_93;
x_26 = x_94;
goto block_56;
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = lean_ctor_get(x_80, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_80, 1);
lean_inc(x_96);
lean_dec(x_80);
x_25 = x_95;
x_26 = x_96;
goto block_56;
}
block_56:
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = l_Lean_Elab_Term_SavedState_restore(x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 1);
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 0, x_25);
x_35 = lean_array_push(x_9, x_31);
lean_ctor_set(x_27, 1, x_33);
lean_ctor_set(x_27, 0, x_35);
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_29);
x_38 = lean_array_push(x_9, x_37);
lean_ctor_set(x_27, 1, x_36);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_27, 0);
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_27);
x_41 = l_Lean_Elab_Term_SavedState_restore(x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_40);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
 lean_ctor_set_tag(x_44, 1);
}
lean_ctor_set(x_44, 0, x_25);
lean_ctor_set(x_44, 1, x_39);
x_45 = lean_array_push(x_9, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_9);
x_47 = lean_ctor_get(x_25, 0);
lean_inc(x_47);
x_48 = l_Lean_Elab_postponeExceptionId;
x_49 = lean_nat_dec_eq(x_47, x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_24)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_24;
 lean_ctor_set_tag(x_50, 1);
}
lean_ctor_set(x_50, 0, x_25);
lean_ctor_set(x_50, 1, x_26);
return x_50;
}
else
{
lean_object* x_51; uint8_t x_52; 
lean_dec(x_24);
x_51 = l_Lean_Elab_Term_SavedState_restore(x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_25);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_25);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
block_79:
{
lean_object* x_59; uint8_t x_60; 
x_59 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_58);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
x_63 = l_Lean_Elab_Term_SavedState_restore(x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_62);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 1);
x_66 = lean_ctor_get(x_63, 0);
lean_dec(x_66);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 0, x_57);
x_67 = lean_array_push(x_9, x_63);
lean_ctor_set(x_59, 1, x_65);
lean_ctor_set(x_59, 0, x_67);
return x_59;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_57);
lean_ctor_set(x_69, 1, x_61);
x_70 = lean_array_push(x_9, x_69);
lean_ctor_set(x_59, 1, x_68);
lean_ctor_set(x_59, 0, x_70);
return x_59;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_59, 0);
x_72 = lean_ctor_get(x_59, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_59);
x_73 = l_Lean_Elab_Term_SavedState_restore(x_22, x_10, x_11, x_12, x_13, x_14, x_15, x_72);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_57);
lean_ctor_set(x_76, 1, x_71);
x_77 = lean_array_push(x_9, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_74);
return x_78;
}
}
}
else
{
uint8_t x_97; 
x_97 = l_Array_isEmpty___rarg(x_3);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_135; lean_object* x_136; lean_object* x_158; 
x_98 = lean_box(0);
x_99 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_158 = l_Lean_Elab_Term_elabTerm(x_1, x_98, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_101);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_161 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_159, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_160);
if (lean_obj_tag(x_161) == 0)
{
if (x_8 == 0)
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_102);
lean_dec(x_5);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_135 = x_162;
x_136 = x_163;
goto block_157;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_161, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_161, 1);
lean_inc(x_165);
lean_dec(x_161);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_166 = l_Lean_Elab_Term_ensureHasType(x_5, x_164, x_98, x_10, x_11, x_12, x_13, x_14, x_15, x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_102);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_135 = x_167;
x_136 = x_168;
goto block_157;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_166, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_166, 1);
lean_inc(x_170);
lean_dec(x_166);
x_103 = x_169;
x_104 = x_170;
goto block_134;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_5);
x_171 = lean_ctor_get(x_161, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_161, 1);
lean_inc(x_172);
lean_dec(x_161);
x_103 = x_171;
x_104 = x_172;
goto block_134;
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_173 = lean_ctor_get(x_158, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_158, 1);
lean_inc(x_174);
lean_dec(x_158);
x_103 = x_173;
x_104 = x_174;
goto block_134;
}
block_134:
{
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_105; uint8_t x_106; 
lean_dec(x_102);
x_105 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_104);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_ctor_get(x_105, 1);
x_109 = l_Lean_Elab_Term_SavedState_restore(x_100, x_10, x_11, x_12, x_13, x_14, x_15, x_108);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_109, 1);
x_112 = lean_ctor_get(x_109, 0);
lean_dec(x_112);
lean_ctor_set_tag(x_109, 1);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set(x_109, 0, x_103);
x_113 = lean_array_push(x_9, x_109);
lean_ctor_set(x_105, 1, x_111);
lean_ctor_set(x_105, 0, x_113);
return x_105;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_dec(x_109);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_103);
lean_ctor_set(x_115, 1, x_107);
x_116 = lean_array_push(x_9, x_115);
lean_ctor_set(x_105, 1, x_114);
lean_ctor_set(x_105, 0, x_116);
return x_105;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_117 = lean_ctor_get(x_105, 0);
x_118 = lean_ctor_get(x_105, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_105);
x_119 = l_Lean_Elab_Term_SavedState_restore(x_100, x_10, x_11, x_12, x_13, x_14, x_15, x_118);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
 lean_ctor_set_tag(x_122, 1);
}
lean_ctor_set(x_122, 0, x_103);
lean_ctor_set(x_122, 1, x_117);
x_123 = lean_array_push(x_9, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_120);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_dec(x_9);
x_125 = lean_ctor_get(x_103, 0);
lean_inc(x_125);
x_126 = l_Lean_Elab_postponeExceptionId;
x_127 = lean_nat_dec_eq(x_125, x_126);
lean_dec(x_125);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_100);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_102)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_102;
 lean_ctor_set_tag(x_128, 1);
}
lean_ctor_set(x_128, 0, x_103);
lean_ctor_set(x_128, 1, x_104);
return x_128;
}
else
{
lean_object* x_129; uint8_t x_130; 
lean_dec(x_102);
x_129 = l_Lean_Elab_Term_SavedState_restore(x_100, x_10, x_11, x_12, x_13, x_14, x_15, x_104);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_129, 0);
lean_dec(x_131);
lean_ctor_set_tag(x_129, 1);
lean_ctor_set(x_129, 0, x_103);
return x_129;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_103);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
block_157:
{
lean_object* x_137; uint8_t x_138; 
x_137 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_136);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ctor_get(x_137, 1);
x_141 = l_Lean_Elab_Term_SavedState_restore(x_100, x_10, x_11, x_12, x_13, x_14, x_15, x_140);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_141, 1);
x_144 = lean_ctor_get(x_141, 0);
lean_dec(x_144);
lean_ctor_set(x_141, 1, x_139);
lean_ctor_set(x_141, 0, x_135);
x_145 = lean_array_push(x_9, x_141);
lean_ctor_set(x_137, 1, x_143);
lean_ctor_set(x_137, 0, x_145);
return x_137;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
lean_dec(x_141);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_135);
lean_ctor_set(x_147, 1, x_139);
x_148 = lean_array_push(x_9, x_147);
lean_ctor_set(x_137, 1, x_146);
lean_ctor_set(x_137, 0, x_148);
return x_137;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_149 = lean_ctor_get(x_137, 0);
x_150 = lean_ctor_get(x_137, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_137);
x_151 = l_Lean_Elab_Term_SavedState_restore(x_100, x_10, x_11, x_12, x_13, x_14, x_15, x_150);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_135);
lean_ctor_set(x_154, 1, x_149);
x_155 = lean_array_push(x_9, x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_152);
return x_156;
}
}
}
else
{
uint8_t x_175; 
x_175 = l_Array_isEmpty___rarg(x_4);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_213; lean_object* x_214; lean_object* x_236; 
x_176 = lean_box(0);
x_177 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_180 = x_177;
} else {
 lean_dec_ref(x_177);
 x_180 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_236 = l_Lean_Elab_Term_elabTerm(x_1, x_176, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_179);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_239 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_237, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_238);
if (lean_obj_tag(x_239) == 0)
{
if (x_8 == 0)
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_180);
lean_dec(x_5);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_213 = x_240;
x_214 = x_241;
goto block_235;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_239, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_239, 1);
lean_inc(x_243);
lean_dec(x_239);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_244 = l_Lean_Elab_Term_ensureHasType(x_5, x_242, x_176, x_10, x_11, x_12, x_13, x_14, x_15, x_243);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; 
lean_dec(x_180);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_213 = x_245;
x_214 = x_246;
goto block_235;
}
else
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_244, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_244, 1);
lean_inc(x_248);
lean_dec(x_244);
x_181 = x_247;
x_182 = x_248;
goto block_212;
}
}
}
else
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_5);
x_249 = lean_ctor_get(x_239, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_239, 1);
lean_inc(x_250);
lean_dec(x_239);
x_181 = x_249;
x_182 = x_250;
goto block_212;
}
}
else
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_251 = lean_ctor_get(x_236, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_236, 1);
lean_inc(x_252);
lean_dec(x_236);
x_181 = x_251;
x_182 = x_252;
goto block_212;
}
block_212:
{
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_183; uint8_t x_184; 
lean_dec(x_180);
x_183 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_182);
x_184 = !lean_is_exclusive(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_185 = lean_ctor_get(x_183, 0);
x_186 = lean_ctor_get(x_183, 1);
x_187 = l_Lean_Elab_Term_SavedState_restore(x_178, x_10, x_11, x_12, x_13, x_14, x_15, x_186);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_187, 1);
x_190 = lean_ctor_get(x_187, 0);
lean_dec(x_190);
lean_ctor_set_tag(x_187, 1);
lean_ctor_set(x_187, 1, x_185);
lean_ctor_set(x_187, 0, x_181);
x_191 = lean_array_push(x_9, x_187);
lean_ctor_set(x_183, 1, x_189);
lean_ctor_set(x_183, 0, x_191);
return x_183;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
lean_dec(x_187);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_181);
lean_ctor_set(x_193, 1, x_185);
x_194 = lean_array_push(x_9, x_193);
lean_ctor_set(x_183, 1, x_192);
lean_ctor_set(x_183, 0, x_194);
return x_183;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_195 = lean_ctor_get(x_183, 0);
x_196 = lean_ctor_get(x_183, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_183);
x_197 = l_Lean_Elab_Term_SavedState_restore(x_178, x_10, x_11, x_12, x_13, x_14, x_15, x_196);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
 lean_ctor_set_tag(x_200, 1);
}
lean_ctor_set(x_200, 0, x_181);
lean_ctor_set(x_200, 1, x_195);
x_201 = lean_array_push(x_9, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_198);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; 
lean_dec(x_9);
x_203 = lean_ctor_get(x_181, 0);
lean_inc(x_203);
x_204 = l_Lean_Elab_postponeExceptionId;
x_205 = lean_nat_dec_eq(x_203, x_204);
lean_dec(x_203);
if (x_205 == 0)
{
lean_object* x_206; 
lean_dec(x_178);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_180)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_180;
 lean_ctor_set_tag(x_206, 1);
}
lean_ctor_set(x_206, 0, x_181);
lean_ctor_set(x_206, 1, x_182);
return x_206;
}
else
{
lean_object* x_207; uint8_t x_208; 
lean_dec(x_180);
x_207 = l_Lean_Elab_Term_SavedState_restore(x_178, x_10, x_11, x_12, x_13, x_14, x_15, x_182);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_207, 0);
lean_dec(x_209);
lean_ctor_set_tag(x_207, 1);
lean_ctor_set(x_207, 0, x_181);
return x_207;
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
lean_dec(x_207);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_181);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
}
block_235:
{
lean_object* x_215; uint8_t x_216; 
x_215 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_214);
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_217 = lean_ctor_get(x_215, 0);
x_218 = lean_ctor_get(x_215, 1);
x_219 = l_Lean_Elab_Term_SavedState_restore(x_178, x_10, x_11, x_12, x_13, x_14, x_15, x_218);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_220 = !lean_is_exclusive(x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_219, 1);
x_222 = lean_ctor_get(x_219, 0);
lean_dec(x_222);
lean_ctor_set(x_219, 1, x_217);
lean_ctor_set(x_219, 0, x_213);
x_223 = lean_array_push(x_9, x_219);
lean_ctor_set(x_215, 1, x_221);
lean_ctor_set(x_215, 0, x_223);
return x_215;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_219, 1);
lean_inc(x_224);
lean_dec(x_219);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_213);
lean_ctor_set(x_225, 1, x_217);
x_226 = lean_array_push(x_9, x_225);
lean_ctor_set(x_215, 1, x_224);
lean_ctor_set(x_215, 0, x_226);
return x_215;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_227 = lean_ctor_get(x_215, 0);
x_228 = lean_ctor_get(x_215, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_215);
x_229 = l_Lean_Elab_Term_SavedState_restore(x_178, x_10, x_11, x_12, x_13, x_14, x_15, x_228);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_231 = x_229;
} else {
 lean_dec_ref(x_229);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_213);
lean_ctor_set(x_232, 1, x_227);
x_233 = lean_array_push(x_9, x_232);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_230);
return x_234;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_8 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_280; lean_object* x_281; 
x_253 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_256 = x_253;
} else {
 lean_dec_ref(x_253);
 x_256 = lean_box(0);
}
x_280 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_281 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_280, x_10, x_11, x_12, x_13, x_14, x_15, x_255);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
lean_dec(x_256);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_283);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
x_287 = l_Lean_Elab_Term_SavedState_restore(x_254, x_10, x_11, x_12, x_13, x_14, x_15, x_286);
x_288 = !lean_is_exclusive(x_287);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_287, 1);
x_290 = lean_ctor_get(x_287, 0);
lean_dec(x_290);
lean_ctor_set(x_287, 1, x_285);
lean_ctor_set(x_287, 0, x_282);
x_291 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_287, x_10, x_11, x_12, x_13, x_14, x_15, x_289);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_287, 1);
lean_inc(x_292);
lean_dec(x_287);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_282);
lean_ctor_set(x_293, 1, x_285);
x_294 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_293, x_10, x_11, x_12, x_13, x_14, x_15, x_292);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_281, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_281, 1);
lean_inc(x_296);
lean_dec(x_281);
x_257 = x_295;
x_258 = x_296;
goto block_279;
}
block_279:
{
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
lean_dec(x_256);
x_259 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_258);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = l_Lean_Elab_Term_SavedState_restore(x_254, x_10, x_11, x_12, x_13, x_14, x_15, x_261);
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_262, 1);
x_265 = lean_ctor_get(x_262, 0);
lean_dec(x_265);
lean_ctor_set_tag(x_262, 1);
lean_ctor_set(x_262, 1, x_260);
lean_ctor_set(x_262, 0, x_257);
x_266 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_262, x_10, x_11, x_12, x_13, x_14, x_15, x_264);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_266;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_262, 1);
lean_inc(x_267);
lean_dec(x_262);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_257);
lean_ctor_set(x_268, 1, x_260);
x_269 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_268, x_10, x_11, x_12, x_13, x_14, x_15, x_267);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; uint8_t x_272; 
lean_dec(x_9);
x_270 = lean_ctor_get(x_257, 0);
lean_inc(x_270);
x_271 = l_Lean_Elab_postponeExceptionId;
x_272 = lean_nat_dec_eq(x_270, x_271);
lean_dec(x_270);
if (x_272 == 0)
{
lean_object* x_273; 
lean_dec(x_254);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_256)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_256;
 lean_ctor_set_tag(x_273, 1);
}
lean_ctor_set(x_273, 0, x_257);
lean_ctor_set(x_273, 1, x_258);
return x_273;
}
else
{
lean_object* x_274; uint8_t x_275; 
lean_dec(x_256);
x_274 = l_Lean_Elab_Term_SavedState_restore(x_254, x_10, x_11, x_12, x_13, x_14, x_15, x_258);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_275 = !lean_is_exclusive(x_274);
if (x_275 == 0)
{
lean_object* x_276; 
x_276 = lean_ctor_get(x_274, 0);
lean_dec(x_276);
lean_ctor_set_tag(x_274, 1);
lean_ctor_set(x_274, 0, x_257);
return x_274;
}
else
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_274, 1);
lean_inc(x_277);
lean_dec(x_274);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_257);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_325; 
x_297 = lean_box(0);
x_298 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_301 = x_298;
} else {
 lean_dec_ref(x_298);
 x_301 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_325 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_19, x_297, x_10, x_11, x_12, x_13, x_14, x_15, x_300);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; 
lean_dec(x_301);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
lean_dec(x_325);
x_328 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_327);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
x_331 = l_Lean_Elab_Term_SavedState_restore(x_299, x_10, x_11, x_12, x_13, x_14, x_15, x_330);
x_332 = !lean_is_exclusive(x_331);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_331, 1);
x_334 = lean_ctor_get(x_331, 0);
lean_dec(x_334);
lean_ctor_set(x_331, 1, x_329);
lean_ctor_set(x_331, 0, x_326);
x_335 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_331, x_10, x_11, x_12, x_13, x_14, x_15, x_333);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_335;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_331, 1);
lean_inc(x_336);
lean_dec(x_331);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_326);
lean_ctor_set(x_337, 1, x_329);
x_338 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_337, x_10, x_11, x_12, x_13, x_14, x_15, x_336);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_338;
}
}
else
{
lean_object* x_339; lean_object* x_340; 
x_339 = lean_ctor_get(x_325, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_325, 1);
lean_inc(x_340);
lean_dec(x_325);
x_302 = x_339;
x_303 = x_340;
goto block_324;
}
block_324:
{
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
lean_dec(x_301);
x_304 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_303);
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = l_Lean_Elab_Term_SavedState_restore(x_299, x_10, x_11, x_12, x_13, x_14, x_15, x_306);
x_308 = !lean_is_exclusive(x_307);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_307, 1);
x_310 = lean_ctor_get(x_307, 0);
lean_dec(x_310);
lean_ctor_set_tag(x_307, 1);
lean_ctor_set(x_307, 1, x_305);
lean_ctor_set(x_307, 0, x_302);
x_311 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_307, x_10, x_11, x_12, x_13, x_14, x_15, x_309);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_311;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_307, 1);
lean_inc(x_312);
lean_dec(x_307);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_302);
lean_ctor_set(x_313, 1, x_305);
x_314 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_313, x_10, x_11, x_12, x_13, x_14, x_15, x_312);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_314;
}
}
else
{
lean_object* x_315; lean_object* x_316; uint8_t x_317; 
lean_dec(x_9);
x_315 = lean_ctor_get(x_302, 0);
lean_inc(x_315);
x_316 = l_Lean_Elab_postponeExceptionId;
x_317 = lean_nat_dec_eq(x_315, x_316);
lean_dec(x_315);
if (x_317 == 0)
{
lean_object* x_318; 
lean_dec(x_299);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_301)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_301;
 lean_ctor_set_tag(x_318, 1);
}
lean_ctor_set(x_318, 0, x_302);
lean_ctor_set(x_318, 1, x_303);
return x_318;
}
else
{
lean_object* x_319; uint8_t x_320; 
lean_dec(x_301);
x_319 = l_Lean_Elab_Term_SavedState_restore(x_299, x_10, x_11, x_12, x_13, x_14, x_15, x_303);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_320 = !lean_is_exclusive(x_319);
if (x_320 == 0)
{
lean_object* x_321; 
x_321 = lean_ctor_get(x_319, 0);
lean_dec(x_321);
lean_ctor_set_tag(x_319, 1);
lean_ctor_set(x_319, 0, x_302);
return x_319;
}
else
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_319, 1);
lean_inc(x_322);
lean_dec(x_319);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_302);
lean_ctor_set(x_323, 1, x_322);
return x_323;
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
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3___boxed(lean_object** _args) {
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
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = lean_unbox(x_7);
lean_dec(x_7);
x_20 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(x_1, x_2, x_3, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_8);
lean_dec(x_1);
return x_20;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = lean_unbox(x_8);
lean_dec(x_8);
x_20 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn(x_1, x_2, x_3, x_4, x_5, x_17, x_18, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess(lean_object* x_1) {
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess(x_7);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_filterAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___spec__1(x_1, x_2, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___rarg___boxed), 3, 0);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___rarg(x_6, x_7, x_8);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_17 = lean_ctor_get(x_2, 1);
x_18 = l_Lean_FileMap_toPosition(x_17, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__1;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_processAssignmentFOApprox_loop___closed__3;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Exception_toMessageData(x_1);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_22);
lean_ctor_set(x_9, 0, x_34);
return x_9;
}
else
{
lean_object* x_35; 
lean_dec(x_15);
x_35 = l_Lean_Exception_toMessageData(x_1);
lean_ctor_set(x_9, 0, x_35);
return x_9;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_9, 0);
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_9);
x_38 = l_Lean_Exception_getRef(x_1);
x_39 = l_Lean_Syntax_getPos(x_38);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_36);
x_40 = l_Lean_Exception_toMessageData(x_1);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_nat_dec_eq(x_36, x_42);
lean_dec(x_36);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_44 = lean_ctor_get(x_2, 1);
x_45 = l_Lean_FileMap_toPosition(x_44, x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__1;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_dec(x_45);
x_54 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
x_57 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_processAssignmentFOApprox_loop___closed__3;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Exception_toMessageData(x_1);
x_60 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_49);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_37);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_42);
x_63 = l_Lean_Exception_toMessageData(x_1);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_37);
return x_64;
}
}
}
}
}
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Array_toList___rarg(x_1);
x_3 = l_Lean_Elab_goalsToMessageData___closed__1;
x_4 = l_Lean_MessageData_joinSep(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_indentD(x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageList(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.App");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.App.0.Lean.Elab.Term.mergeFailures");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1;
x_2 = l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(772u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
x_6 = l___private_Init_Util_2__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
x_18 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_19 = l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3;
x_20 = lean_panic_fn(x_18, x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_21 = lean_apply_7(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_1, x_24);
x_26 = x_22;
x_27 = lean_array_fset(x_16, x_1, x_26);
lean_dec(x_1);
x_1 = x_25;
x_2 = x_27;
x_9 = x_23;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
x_34 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData(x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_1, x_37);
x_39 = x_35;
x_40 = lean_array_fset(x_16, x_1, x_39);
lean_dec(x_1);
x_1 = x_38;
x_2 = x_40;
x_9 = x_36;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("overloaded, errors ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = x_1;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1), 9, 2);
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageList(x_14);
lean_dec(x_14);
x_17 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.App.0.Lean.Elab.Term.elabAppAux");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1;
x_2 = l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(790u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
x_6 = l___private_Init_Util_2__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_11);
x_26 = l_Lean_MessageData_Lean_Message___instance__1;
x_27 = l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2;
x_28 = lean_panic_fn(x_26, x_27);
x_29 = x_28;
x_30 = lean_array_fset(x_10, x_3, x_29);
lean_dec(x_3);
x_3 = x_13;
x_4 = x_30;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous, possible interpretations ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_box(0);
x_14 = 0;
x_15 = l_Array_empty___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn(x_1, x_13, x_2, x_3, x_5, x_14, x_4, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_get_size(x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_unsigned_to_nat(0u);
lean_inc(x_17);
x_23 = l_Array_filterAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___spec__1(x_17, x_22, x_22);
x_24 = lean_array_get_size(x_23);
x_25 = lean_nat_dec_eq(x_24, x_20);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = lean_nat_dec_lt(x_20, x_24);
lean_dec(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_23);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_10, 3);
x_29 = l_Lean_replaceRef(x_1, x_28);
lean_dec(x_28);
lean_dec(x_1);
lean_ctor_set(x_10, 3, x_29);
x_30 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
x_33 = lean_ctor_get(x_10, 2);
x_34 = lean_ctor_get(x_10, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
x_35 = l_Lean_replaceRef(x_1, x_34);
lean_dec(x_34);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_35);
x_37 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg(x_17, x_6, x_7, x_8, x_9, x_36, x_11, x_18);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_17);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_10, 0);
lean_inc(x_39);
x_40 = x_23;
x_41 = l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1(x_38, x_39, x_22, x_40);
x_42 = x_41;
x_43 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageList(x_42);
lean_dec(x_42);
x_44 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__5___closed__1;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_1, x_47, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_1);
x_49 = l_Lean_Elab_Term_Lean_Elab_Term___instance__4;
x_50 = lean_array_get(x_49, x_23, x_22);
lean_dec(x_23);
x_51 = l_Lean_Elab_Term_applyResult(x_50, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
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
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
uint8_t x_56; 
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
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_1);
x_60 = l_Lean_Elab_Term_Lean_Elab_Term___instance__4;
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_array_get(x_60, x_17, x_61);
lean_dec(x_17);
x_63 = l_Lean_Elab_Term_applyResult(x_62, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_16);
if (x_64 == 0)
{
return x_16;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_16, 0);
x_66 = lean_ctor_get(x_16, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_16);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l_Lean_Elab_Term_expandApp_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandApp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandApp_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandApp_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandApp_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandApp_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandApp_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandApp_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_expandApp_match__3___rarg), 2, 0);
return x_2;
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
lean_object* x_1; 
x_1 = lean_mk_string("unexpected '..'");
return x_1;
}
}
static lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_4);
x_15 = lean_nat_dec_lt(x_5, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_array_fget(x_4, x_5);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
x_23 = l_Lean_Syntax_getKind(x_17);
x_24 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1;
lean_inc(x_1);
x_25 = lean_name_mk_string(x_1, x_24);
x_26 = lean_name_eq(x_23, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = lean_name_eq(x_23, x_2);
lean_dec(x_23);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_17);
x_29 = lean_array_push(x_22, x_28);
lean_ctor_set(x_6, 1, x_29);
x_5 = x_19;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_free_object(x_6);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_1);
x_31 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
x_32 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_17, x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_17);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_23);
x_37 = l_Lean_Syntax_getArg(x_17, x_18);
x_38 = l_Lean_Syntax_getId(x_37);
lean_dec(x_37);
x_39 = lean_erase_macro_scopes(x_38);
x_40 = lean_unsigned_to_nat(3u);
x_41 = l_Lean_Syntax_getArg(x_17, x_40);
lean_dec(x_17);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_7);
x_44 = l_Lean_Elab_Term_addNamedArg(x_21, x_43, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_ctor_set(x_6, 0, x_45);
x_5 = x_19;
x_13 = x_46;
goto _start;
}
else
{
uint8_t x_48; 
lean_free_object(x_6);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_ctor_get(x_6, 0);
x_53 = lean_ctor_get(x_6, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_6);
lean_inc(x_17);
x_54 = l_Lean_Syntax_getKind(x_17);
x_55 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1;
lean_inc(x_1);
x_56 = lean_name_mk_string(x_1, x_55);
x_57 = lean_name_eq(x_54, x_56);
lean_dec(x_56);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = lean_name_eq(x_54, x_2);
lean_dec(x_54);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_17);
x_60 = lean_array_push(x_53, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_60);
x_5 = x_19;
x_6 = x_61;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_19);
lean_dec(x_1);
x_63 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
x_64 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_17, x_63, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_17);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_54);
x_69 = l_Lean_Syntax_getArg(x_17, x_18);
x_70 = l_Lean_Syntax_getId(x_69);
lean_dec(x_69);
x_71 = lean_erase_macro_scopes(x_70);
x_72 = lean_unsigned_to_nat(3u);
x_73 = l_Lean_Syntax_getArg(x_17, x_72);
lean_dec(x_17);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_71);
lean_ctor_set(x_75, 1, x_74);
lean_inc(x_7);
x_76 = l_Lean_Elab_Term_addNamedArg(x_52, x_75, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_53);
x_5 = x_19;
x_6 = x_79;
x_13 = x_78;
goto _start;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_53);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_83 = x_76;
} else {
 lean_dec_ref(x_76);
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
}
}
}
static lean_object* _init_l_Lean_Elab_Term_expandApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ellipsis");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Elab_Term_expandApp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_expandApp(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_67; uint8_t x_68; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_14);
x_67 = l_Lean_Elab_Term_expandApp___closed__2;
x_68 = l_Lean_Syntax_isOfKind(x_15, x_67);
if (x_68 == 0)
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_69 = 0;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_14);
lean_ctor_set(x_71, 1, x_70);
x_16 = x_71;
goto block_66;
}
else
{
lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_array_pop(x_14);
x_73 = 1;
x_74 = lean_box(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
x_16 = x_75;
goto block_66;
}
block_66:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l_Lean_mkAppStx___closed__6;
x_21 = l_Lean_Elab_Term_expandApp___closed__2;
x_22 = l_Lean_importModules___closed__1;
x_23 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1(x_20, x_21, x_18, x_18, x_10, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_18);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 0, x_28);
lean_ctor_set(x_16, 1, x_25);
lean_ctor_set(x_16, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_11);
lean_ctor_set(x_29, 1, x_16);
lean_ctor_set(x_23, 0, x_29);
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_19);
lean_ctor_set(x_16, 1, x_32);
lean_ctor_set(x_16, 0, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_16);
lean_ctor_set(x_23, 0, x_33);
return x_23;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_38 = x_34;
} else {
 lean_dec_ref(x_34);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_19);
lean_ctor_set(x_16, 1, x_39);
lean_ctor_set(x_16, 0, x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_11);
lean_ctor_set(x_40, 1, x_16);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_35);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_free_object(x_16);
lean_dec(x_19);
lean_dec(x_11);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_16, 0);
x_47 = lean_ctor_get(x_16, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_16);
x_48 = l_Lean_mkAppStx___closed__6;
x_49 = l_Lean_Elab_Term_expandApp___closed__2;
x_50 = l_Lean_importModules___closed__1;
x_51 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1(x_48, x_49, x_46, x_46, x_10, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_46);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
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
x_55 = lean_ctor_get(x_52, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_57 = x_52;
} else {
 lean_dec_ref(x_52);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_47);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_11);
lean_ctor_set(x_60, 1, x_59);
if (lean_is_scalar(x_54)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_54;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_53);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_47);
lean_dec(x_11);
x_62 = lean_ctor_get(x_51, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_64 = x_51;
} else {
 lean_dec_ref(x_51);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
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
lean_object* l_Lean_Elab_Term_elabApp_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_apply_4(x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_elabApp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabApp_match__1___rarg), 2, 0);
return x_2;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
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
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
x_21 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux(x_16, x_17, x_18, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = l_Array_empty___closed__1;
x_11 = 0;
x_12 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux(x_1, x_10, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_elabIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_3 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_3 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8;
x_4 = l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_expandDollarProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_3 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__15;
x_4 = l___regBuiltin_Lean_Elab_Term_expandDollarProj___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_isExplicit___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l_Lean_Syntax_getArgs(x_1);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_62; uint8_t x_63; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
x_62 = l_Lean_identKind___closed__2;
lean_inc(x_19);
x_63 = l_Lean_Syntax_isOfKind(x_19, x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8;
lean_inc(x_19);
x_65 = l_Lean_Syntax_isOfKind(x_19, x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_1);
x_66 = lean_box(0);
x_20 = x_66;
goto block_61;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = l_Lean_Syntax_getArgs(x_19);
x_68 = lean_array_get_size(x_67);
lean_dec(x_67);
x_69 = lean_unsigned_to_nat(4u);
x_70 = lean_nat_dec_eq(x_68, x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_1);
x_71 = lean_box(0);
x_20 = x_71;
goto block_61;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_unsigned_to_nat(0u);
x_73 = l_Lean_Syntax_getArg(x_19, x_72);
x_74 = l_Lean_Syntax_isOfKind(x_73, x_62);
if (x_74 == 0)
{
uint8_t x_75; uint8_t x_76; lean_object* x_77; 
lean_dec(x_1);
x_75 = 1;
x_76 = 0;
x_77 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux(x_2, x_75, x_76, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_77;
}
else
{
lean_object* x_78; 
lean_dec(x_19);
x_78 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_78;
}
}
}
}
else
{
lean_object* x_79; 
lean_dec(x_19);
x_79 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_79;
}
block_61:
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_20);
x_21 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
lean_inc(x_19);
x_22 = l_Lean_Syntax_isOfKind(x_19, x_21);
if (x_22 == 0)
{
uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_23 = 1;
x_24 = 0;
x_25 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux(x_2, x_23, x_24, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = l_Lean_Syntax_getArgs(x_19);
x_27 = lean_array_get_size(x_26);
lean_dec(x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_dec_eq(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
uint8_t x_30; uint8_t x_31; lean_object* x_32; 
x_30 = 1;
x_31 = 0;
x_32 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux(x_2, x_30, x_31, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Lean_Syntax_getArg(x_19, x_18);
x_34 = l_Lean_nullKind___closed__2;
lean_inc(x_33);
x_35 = l_Lean_Syntax_isOfKind(x_33, x_34);
if (x_35 == 0)
{
uint8_t x_36; uint8_t x_37; lean_object* x_38; 
lean_dec(x_33);
x_36 = 1;
x_37 = 0;
x_38 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux(x_2, x_36, x_37, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = l_Lean_Syntax_getArgs(x_33);
x_40 = lean_array_get_size(x_39);
lean_dec(x_39);
x_41 = lean_nat_dec_eq(x_40, x_15);
lean_dec(x_40);
if (x_41 == 0)
{
uint8_t x_42; uint8_t x_43; lean_object* x_44; 
lean_dec(x_33);
x_42 = 1;
x_43 = 0;
x_44 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux(x_2, x_42, x_43, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Lean_Syntax_getArg(x_33, x_45);
x_47 = l_Lean_Syntax_getArg(x_33, x_18);
lean_dec(x_33);
lean_inc(x_47);
x_48 = l_Lean_Syntax_isOfKind(x_47, x_34);
if (x_48 == 0)
{
uint8_t x_49; uint8_t x_50; lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_46);
x_49 = 1;
x_50 = 0;
x_51 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux(x_2, x_49, x_50, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = l_Lean_Syntax_getArgs(x_47);
lean_dec(x_47);
x_53 = lean_array_get_size(x_52);
lean_dec(x_52);
x_54 = lean_nat_dec_eq(x_53, x_45);
lean_dec(x_53);
if (x_54 == 0)
{
uint8_t x_55; uint8_t x_56; lean_object* x_57; 
lean_dec(x_46);
x_55 = 1;
x_56 = 0;
x_57 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux(x_2, x_55, x_56, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_57;
}
else
{
uint8_t x_58; uint8_t x_59; lean_object* x_60; 
lean_dec(x_19);
x_58 = 1;
x_59 = 0;
x_60 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux(x_2, x_58, x_59, x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_3 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_isExplicit___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_3 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__13;
x_4 = l___regBuiltin_Lean_Elab_Term_elabProj___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_3 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__10;
x_4 = l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_7244_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
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
l_Lean_Elab_Term_Lean_Elab_App___instance__1___closed__1 = _init_l_Lean_Elab_Term_Lean_Elab_App___instance__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_App___instance__1___closed__1);
l_Lean_Elab_Term_Lean_Elab_App___instance__1 = _init_l_Lean_Elab_Term_Lean_Elab_App___instance__1();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_App___instance__1);
l_Lean_Elab_Term_Lean_Elab_App___instance__4___closed__1 = _init_l_Lean_Elab_Term_Lean_Elab_App___instance__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_App___instance__4___closed__1);
l_Lean_Elab_Term_Lean_Elab_App___instance__4 = _init_l_Lean_Elab_Term_Lean_Elab_App___instance__4();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_App___instance__4);
l_Lean_Elab_Term_addNamedArg___closed__1 = _init_l_Lean_Elab_Term_addNamedArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__1);
l_Lean_Elab_Term_addNamedArg___closed__2 = _init_l_Lean_Elab_Term_addNamedArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__2);
l_Lean_Elab_Term_addNamedArg___closed__3 = _init_l_Lean_Elab_Term_addNamedArg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__3);
l_Lean_Elab_Term_addNamedArg___closed__4 = _init_l_Lean_Elab_Term_addNamedArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__4);
l_Lean_Elab_Term_ElabAppArgs_State_ellipsis___default = _init_l_Lean_Elab_Term_ElabAppArgs_State_ellipsis___default();
l_Lean_Elab_Term_ElabAppArgs_State_etaArgs___default = _init_l_Lean_Elab_Term_ElabAppArgs_State_etaArgs___default();
lean_mark_persistent(l_Lean_Elab_Term_ElabAppArgs_State_etaArgs___default);
l_Lean_Elab_Term_ElabAppArgs_State_toSetErrorCtx___default = _init_l_Lean_Elab_Term_ElabAppArgs_State_toSetErrorCtx___default();
lean_mark_persistent(l_Lean_Elab_Term_ElabAppArgs_State_toSetErrorCtx___default);
l_Lean_Elab_Term_ElabAppArgs_State_instMVars___default = _init_l_Lean_Elab_Term_ElabAppArgs_State_instMVars___default();
lean_mark_persistent(l_Lean_Elab_Term_ElabAppArgs_State_instMVars___default);
l_Lean_Elab_Term_ElabAppArgs_State_typeMVars___default = _init_l_Lean_Elab_Term_ElabAppArgs_State_typeMVars___default();
lean_mark_persistent(l_Lean_Elab_Term_ElabAppArgs_State_typeMVars___default);
l_Lean_Elab_Term_ElabAppArgs_State_alreadyPropagated___default = _init_l_Lean_Elab_Term_ElabAppArgs_State_alreadyPropagated___default();
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__6 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__6);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__8 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__8);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__5 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__5);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__6 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__6);
l_Lean_Elab_Term_ElabAppArgs_main___closed__1 = _init_l_Lean_Elab_Term_ElabAppArgs_main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_ElabAppArgs_main___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__5 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__5);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__6 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__6);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__7 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__7);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__8 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__8);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__9 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__9);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__14 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__14();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__14);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__15 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__15();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__15);
l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__16 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__16();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__16);
l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1 = _init_l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1();
lean_mark_persistent(l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1);
l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2 = _init_l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2();
lean_mark_persistent(l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__4 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__4);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__5 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__5);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__6 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__6);
l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__5 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__5);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__6 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__6);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__7 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__7);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__9 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__9);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__10 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__10);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__11 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__11);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__13 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__13();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__13);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__14 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__14();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__14);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__15 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__15();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__15);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__16 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__16();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__16);
l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2);
l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__2);
l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2);
l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1);
l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2);
l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__3 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__3();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__3);
l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4 = _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4);
l_Lean_Elab_Term_expandApp___closed__1 = _init_l_Lean_Elab_Term_expandApp___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_expandApp___closed__1);
l_Lean_Elab_Term_expandApp___closed__2 = _init_l_Lean_Elab_Term_expandApp___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_expandApp___closed__2);
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
res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_7244_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
