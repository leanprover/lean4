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
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__1;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_List_tail_x21___rarg(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__4;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__6;
uint8_t l_Array_anyRangeMAux___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__3;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isTypeApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Init_Core___instance__33;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_fieldIdxKind___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_Meta_withoutPostponingUniverseConstraintsImp___rarg___closed__12;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__3(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__15;
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___lambda__3___closed__2;
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___closed__1;
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__11;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_inhabited___closed__1;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_0__Lean_Meta_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l_Lean_Elab_Term_NamedArg_ref___default;
lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
lean_object* l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__2(uint8_t);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__2(lean_object*);
lean_object* l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_expandDollarProj(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_State_typeMVars___default;
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12;
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__4;
lean_object* l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3;
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasArgsToProcess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp_match__2(lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__3(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2(lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_goalsToMessageData___closed__1;
extern lean_object* l_Lean_MessageData_nil;
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
lean_object* l_Array_findSomeMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess___boxed(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_CheckAssignment_addAssignmentInfo___rarg___closed__3;
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_995____spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__4___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__2(lean_object*);
lean_object* l_Array_iterateMAux___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Init_Data_Repr___instance__11___rarg___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__2;
lean_object* l_Array_anyRangeMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__10;
lean_object* l_Array_filterAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l_Lean_Meta_setPostponed___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getResetPostponed___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp_match__1(lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandDollarProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__2(lean_object*);
extern lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834____closed__1;
lean_object* l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__1;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__1;
uint8_t l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withoutPostponingUniverseConstraintsImp___at_Lean_Elab_Term_elabApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_fTypeHasOptAutoParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__7;
lean_object* l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__3;
lean_object* l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__4;
lean_object* l_Lean_Elab_Term_addNamedArg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_299____closed__5;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isExprDefEq___rarg___closed__2;
uint8_t l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__1;
extern lean_object* l_Init_Data_Repr___instance__7___rarg___closed__2;
extern lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getBindingName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__2_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__1(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3;
lean_object* l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind___closed__2;
uint8_t l_Lean_Elab_Term_ElabAppArgs_State_ellipsis___default;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__2;
lean_object* l_List_filterAux___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__1___closed__1;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_visit(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg_match__1(lean_object*);
lean_object* l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__1(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___boxed(lean_object**);
lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__2_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_expandApp_match__3___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__4;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getResetPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__2;
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3___boxed(lean_object**);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11;
extern lean_object* l___private_Init_Util_0__mkPanicMessage___closed__2;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___boxed(lean_object**);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__3___rarg(lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___boxed(lean_object**);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__4___closed__1;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhen___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_State_instMVars___default;
lean_object* l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData_match__1(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern(lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1;
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_Elab_Term_elabExplicitUnivs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasArgsToProcess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_State_toSetErrorCtx___default;
lean_object* l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__1;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__1(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__5;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_elabChoice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_liftMkBindingM___rarg___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__2(lean_object*);
extern lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__8;
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__15;
lean_object* l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__1;
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandDollarProj___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__16;
extern lean_object* l_Lean_importModules___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__1(lean_object*);
lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponedToMessageData___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
extern lean_object* l_Lean_formatEntry___closed__1;
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__3;
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
lean_object* l_Lean_Meta_withoutPostponingUniverseConstraintsImp___at_Lean_Elab_Term_elabApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections_match__1(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj___closed__1;
uint8_t l_Lean_Expr_isAutoParam(lean_object*);
lean_object* l_Lean_Elab_Term_elabNamedPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEqAux___closed__7;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageList(lean_object*);
lean_object* l_Array_foldlStepMAux___at_Lean_Syntax_getSepArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__3(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__14;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabBinders___rarg___closed__1;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Term_elabProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_Lean_Meta_Basic___instance__10___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__5(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__4;
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__4(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__1;
extern lean_object* l_Option_get_x21___rarg___closed__4;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__1;
extern lean_object* l_Lean_mkAppStx___closed__5;
extern lean_object* l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
lean_object* l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1;
lean_object* l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Elab_Term_expandApp_match__3(lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__2(lean_object*);
lean_object* l_List_find_x3f___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__2;
lean_object* l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2;
lean_object* l_Lean_getParentStructures(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess_match__1(lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_postponeExceptionId;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__3(lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_saveAllState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__2;
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_299____closed__29;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__3;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__1(lean_object*);
lean_object* l_Lean_Meta_throwUnknownFVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12;
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj(lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__5;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__6;
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__5;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1;
extern lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
extern lean_object* l_Lean_Init_LeanInit___instance__8___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__1___closed__6;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_State_etaArgs___default;
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_isExplicit___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__5(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__1(lean_object*);
lean_object* l_Lean_Exception_getRef(lean_object*);
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__6;
lean_object* l_Lean_Meta_commitWhen___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__6;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_7432_(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__2(lean_object*);
extern lean_object* l_Lean_Meta_throwLetTypeMismatchMessage___rarg___closed__7;
lean_object* l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__2;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___rarg(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__6;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__1___closed__2;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Array_findIdxAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__9;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__1;
extern lean_object* l_Lean_Elab_Term_Lean_Elab_Term___instance__4;
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__3;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1;
lean_object* l_Lean_Elab_Term_registerSyntheticMVarWithCurrRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPostponed___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__3(lean_object*);
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabApp_match__1(lean_object*);
lean_object* l_Array_forMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__3;
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
lean_object* l_Lean_Elab_Term_registerMVarErrorImplicitArgInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__8;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__1;
lean_object* l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole_match__1(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
extern lean_object* l_Init_Control_Reader___instance__10___closed__2;
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addImplicitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__11;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__3;
lean_object* l_Array_iterateMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__2___boxed(lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_applyResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__9;
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ensureArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__3___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_299____closed__4;
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__4;
lean_object* l_Lean_Elab_Term_expandApp___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__2;
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__6;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__14;
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1;
lean_object* l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__1;
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__2;
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__1___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__5;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withoutPostponingUniverseConstraintsImp___at_Lean_Elab_Term_elabBinders___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2;
lean_object* l_Lean_Meta_commitWhen___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasTypeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError(lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhen___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_ElabAppArgs_State_alreadyPropagated___default;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__4;
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__5;
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__5;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__1;
lean_object* l_Lean_Elab_Term_elabExplicitUnivs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__8;
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1;
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_Lean_Message___instance__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2;
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__3(lean_object*);
extern lean_object* l_Lean_Meta_mkArrow___rarg___closed__2;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_Elab_Term_NamedArg_ref___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_Lean_Elab_App___instance__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_System_FilePath_dirName___closed__1;
x_4 = l_Lean_Name_toStringWithSep(x_3, x_2);
x_5 = l_Init_Data_Repr___instance__11___rarg___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lean_formatEntry___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_ctor_get(x_1, 2);
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
x_18 = l_Init_Data_Repr___instance__7___rarg___closed__2;
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
x_23 = l_Init_Data_Repr___instance__7___rarg___closed__2;
x_24 = lean_string_append(x_22, x_23);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_Lean_Elab_App___instance__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Elab_Term_Lean_Elab_App___instance__1___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
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
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwInvalidNamedArg_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid argument name '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' for function");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' for function '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_7, 3);
x_13 = l_Lean_replaceRef(x_11, x_12);
lean_dec(x_12);
lean_ctor_set(x_7, 3, x_13);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__6;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_21);
x_28 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_28, 0, x_21);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_ctor_get(x_7, 1);
x_36 = lean_ctor_get(x_7, 2);
x_37 = lean_ctor_get(x_7, 3);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_7);
x_38 = l_Lean_replaceRef(x_33, x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 3, x_38);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__4;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_45, x_3, x_4, x_5, x_6, x_39, x_8, x_9);
lean_dec(x_39);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_47 = lean_ctor_get(x_2, 0);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
x_49 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__6;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_inc(x_47);
x_54 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_54, 0, x_47);
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_57, x_3, x_4, x_5, x_6, x_39, x_8, x_9);
lean_dec(x_39);
return x_58;
}
}
}
}
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwInvalidNamedArg___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_throwInvalidNamedArg___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
uint8_t l_Array_anyRangeMAux___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_8, 1);
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
uint8_t x_15; 
lean_dec(x_5);
x_15 = 1;
return x_15;
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
x_12 = l_Array_anyRangeMAux___at_Lean_Elab_Term_addNamedArg___spec__1(x_1, x_2, x_1, x_10, x_11);
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
x_15 = lean_ctor_get(x_2, 1);
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
lean_object* l_Array_anyRangeMAux___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___at_Lean_Elab_Term_addNamedArg___spec__1(x_1, x_2, x_3, x_4, x_5);
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
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CoeFun");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeFun");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_14 = l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
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
x_29 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__2;
lean_inc(x_28);
x_30 = l_Lean_mkConst(x_29, x_28);
x_31 = l_Lean_mkAppStx___closed__9;
lean_inc(x_1);
x_32 = lean_array_push(x_31, x_1);
lean_inc(x_21);
x_33 = lean_array_push(x_32, x_21);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Array_iterateMAux___at_Lean_mkAppN___spec__1(x_33, x_33, x_34, x_30);
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
x_42 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_39);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_42, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_42, 0, x_47);
return x_42;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec(x_42);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_42);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_42, 0);
lean_dec(x_52);
x_53 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__4;
x_54 = l_Lean_mkConst(x_53, x_28);
x_55 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_56 = lean_array_push(x_55, x_1);
x_57 = lean_array_push(x_56, x_21);
x_58 = lean_array_push(x_57, x_2);
x_59 = lean_array_push(x_58, x_39);
x_60 = l_Array_iterateMAux___at_Lean_mkAppN___spec__1(x_59, x_59, x_34, x_54);
lean_dec(x_59);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_42, 0, x_61);
return x_42;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_62 = lean_ctor_get(x_42, 1);
lean_inc(x_62);
lean_dec(x_42);
x_63 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__4;
x_64 = l_Lean_mkConst(x_63, x_28);
x_65 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_66 = lean_array_push(x_65, x_1);
x_67 = lean_array_push(x_66, x_21);
x_68 = lean_array_push(x_67, x_2);
x_69 = lean_array_push(x_68, x_39);
x_70 = l_Array_iterateMAux___at_Lean_mkAppN___spec__1(x_69, x_69, x_34, x_64);
lean_dec(x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_62);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_39);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_42);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_42, 0);
lean_dec(x_74);
x_75 = lean_box(0);
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 0, x_75);
return x_42;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_42, 1);
lean_inc(x_76);
lean_dec(x_42);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8_t x_79; 
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
x_79 = !lean_is_exclusive(x_23);
if (x_79 == 0)
{
return x_23;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_23, 0);
x_81 = lean_ctor_get(x_23, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_23);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
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
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__3___rarg), 3, 0);
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
x_14 = l_Lean_Meta_whnf___rarg___lambda__1(x_10, x_1, x_13, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_1);
x_15 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_16 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_995____spec__1___rarg(x_15, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
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
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_16 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_995____spec__1___rarg(x_15, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
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
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
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
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
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
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
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
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
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
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
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
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
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
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
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
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
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
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
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
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
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
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_13, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("function expected at");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nterm has type");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
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
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_22);
lean_inc(x_20);
x_23 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(x_20, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_16, 3);
lean_inc(x_26);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_2);
x_27 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3(x_22, x_26, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_indentExpr(x_22);
x_30 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_indentExpr(x_20);
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg(x_37, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_27);
if (x_39 == 0)
{
return x_27;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_27, 0);
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_27);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_16);
x_43 = lean_ctor_get(x_23, 1);
lean_inc(x_43);
lean_dec(x_23);
x_44 = lean_ctor_get(x_24, 0);
lean_inc(x_44);
lean_dec(x_24);
lean_inc(x_44);
x_45 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5(x_44, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_43);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_st_ref_take(x_1, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_49, 1);
lean_dec(x_52);
x_53 = lean_ctor_get(x_49, 0);
lean_dec(x_53);
lean_ctor_set(x_49, 1, x_46);
lean_ctor_set(x_49, 0, x_44);
x_54 = lean_st_ref_set(x_1, x_49, x_50);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_12);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_12);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_59 = lean_ctor_get_uint8(x_49, sizeof(void*)*9);
x_60 = lean_ctor_get(x_49, 2);
x_61 = lean_ctor_get(x_49, 3);
x_62 = lean_ctor_get_uint8(x_49, sizeof(void*)*9 + 1);
x_63 = lean_ctor_get(x_49, 4);
x_64 = lean_ctor_get(x_49, 5);
x_65 = lean_ctor_get(x_49, 6);
x_66 = lean_ctor_get(x_49, 7);
x_67 = lean_ctor_get(x_49, 8);
x_68 = lean_ctor_get_uint8(x_49, sizeof(void*)*9 + 2);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_49);
x_69 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_69, 0, x_44);
lean_ctor_set(x_69, 1, x_46);
lean_ctor_set(x_69, 2, x_60);
lean_ctor_set(x_69, 3, x_61);
lean_ctor_set(x_69, 4, x_63);
lean_ctor_set(x_69, 5, x_64);
lean_ctor_set(x_69, 6, x_65);
lean_ctor_set(x_69, 7, x_66);
lean_ctor_set(x_69, 8, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*9, x_59);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 1, x_62);
lean_ctor_set_uint8(x_69, sizeof(void*)*9 + 2, x_68);
x_70 = lean_st_ref_set(x_1, x_69, x_50);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_12);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_44);
x_74 = !lean_is_exclusive(x_45);
if (x_74 == 0)
{
return x_45;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_45, 0);
x_76 = lean_ctor_get(x_45, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_45);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_23);
if (x_78 == 0)
{
return x_23;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_23, 0);
x_80 = lean_ctor_get(x_23, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_23);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
case 1:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_19, 1);
lean_inc(x_82);
lean_dec(x_19);
x_83 = lean_ctor_get(x_16, 0);
lean_inc(x_83);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_83);
lean_inc(x_20);
x_84 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(x_20, x_83, x_2, x_3, x_4, x_5, x_6, x_7, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_16, 3);
lean_inc(x_87);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_2);
x_88 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__6(x_83, x_87, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_86);
lean_dec(x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_90 = l_Lean_indentExpr(x_83);
x_91 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2;
x_92 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4;
x_94 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_indentExpr(x_20);
x_96 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_98 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg(x_98, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_89);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_99;
}
else
{
uint8_t x_100; 
lean_dec(x_83);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_88);
if (x_100 == 0)
{
return x_88;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_88, 0);
x_102 = lean_ctor_get(x_88, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_88);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_83);
lean_dec(x_20);
lean_dec(x_16);
x_104 = lean_ctor_get(x_84, 1);
lean_inc(x_104);
lean_dec(x_84);
x_105 = lean_ctor_get(x_85, 0);
lean_inc(x_105);
lean_dec(x_85);
lean_inc(x_105);
x_106 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5(x_105, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_104);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_st_ref_take(x_1, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = !lean_is_exclusive(x_110);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_110, 1);
lean_dec(x_113);
x_114 = lean_ctor_get(x_110, 0);
lean_dec(x_114);
lean_ctor_set(x_110, 1, x_107);
lean_ctor_set(x_110, 0, x_105);
x_115 = lean_st_ref_set(x_1, x_110, x_111);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_115, 0);
lean_dec(x_117);
lean_ctor_set(x_115, 0, x_12);
return x_115;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_12);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
else
{
uint8_t x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_120 = lean_ctor_get_uint8(x_110, sizeof(void*)*9);
x_121 = lean_ctor_get(x_110, 2);
x_122 = lean_ctor_get(x_110, 3);
x_123 = lean_ctor_get_uint8(x_110, sizeof(void*)*9 + 1);
x_124 = lean_ctor_get(x_110, 4);
x_125 = lean_ctor_get(x_110, 5);
x_126 = lean_ctor_get(x_110, 6);
x_127 = lean_ctor_get(x_110, 7);
x_128 = lean_ctor_get(x_110, 8);
x_129 = lean_ctor_get_uint8(x_110, sizeof(void*)*9 + 2);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_110);
x_130 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_130, 0, x_105);
lean_ctor_set(x_130, 1, x_107);
lean_ctor_set(x_130, 2, x_121);
lean_ctor_set(x_130, 3, x_122);
lean_ctor_set(x_130, 4, x_124);
lean_ctor_set(x_130, 5, x_125);
lean_ctor_set(x_130, 6, x_126);
lean_ctor_set(x_130, 7, x_127);
lean_ctor_set(x_130, 8, x_128);
lean_ctor_set_uint8(x_130, sizeof(void*)*9, x_120);
lean_ctor_set_uint8(x_130, sizeof(void*)*9 + 1, x_123);
lean_ctor_set_uint8(x_130, sizeof(void*)*9 + 2, x_129);
x_131 = lean_st_ref_set(x_1, x_130, x_111);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_133 = x_131;
} else {
 lean_dec_ref(x_131);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_12);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
uint8_t x_135; 
lean_dec(x_105);
x_135 = !lean_is_exclusive(x_106);
if (x_135 == 0)
{
return x_106;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_106, 0);
x_137 = lean_ctor_get(x_106, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_106);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_83);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_139 = !lean_is_exclusive(x_84);
if (x_139 == 0)
{
return x_84;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_84, 0);
x_141 = lean_ctor_get(x_84, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_84);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
case 2:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_19, 1);
lean_inc(x_143);
lean_dec(x_19);
x_144 = lean_ctor_get(x_16, 0);
lean_inc(x_144);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_144);
lean_inc(x_20);
x_145 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(x_20, x_144, x_2, x_3, x_4, x_5, x_6, x_7, x_143);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_16, 3);
lean_inc(x_148);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_2);
x_149 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__7(x_144, x_148, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_147);
lean_dec(x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_151 = l_Lean_indentExpr(x_144);
x_152 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2;
x_153 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4;
x_155 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_indentExpr(x_20);
x_157 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_159 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg(x_159, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_150);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_160;
}
else
{
uint8_t x_161; 
lean_dec(x_144);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_161 = !lean_is_exclusive(x_149);
if (x_161 == 0)
{
return x_149;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_149, 0);
x_163 = lean_ctor_get(x_149, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_149);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_144);
lean_dec(x_20);
lean_dec(x_16);
x_165 = lean_ctor_get(x_145, 1);
lean_inc(x_165);
lean_dec(x_145);
x_166 = lean_ctor_get(x_146, 0);
lean_inc(x_166);
lean_dec(x_146);
lean_inc(x_166);
x_167 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5(x_166, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_165);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_st_ref_take(x_1, x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = !lean_is_exclusive(x_171);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_174 = lean_ctor_get(x_171, 1);
lean_dec(x_174);
x_175 = lean_ctor_get(x_171, 0);
lean_dec(x_175);
lean_ctor_set(x_171, 1, x_168);
lean_ctor_set(x_171, 0, x_166);
x_176 = lean_st_ref_set(x_1, x_171, x_172);
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_176, 0);
lean_dec(x_178);
lean_ctor_set(x_176, 0, x_12);
return x_176;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_12);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
else
{
uint8_t x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_181 = lean_ctor_get_uint8(x_171, sizeof(void*)*9);
x_182 = lean_ctor_get(x_171, 2);
x_183 = lean_ctor_get(x_171, 3);
x_184 = lean_ctor_get_uint8(x_171, sizeof(void*)*9 + 1);
x_185 = lean_ctor_get(x_171, 4);
x_186 = lean_ctor_get(x_171, 5);
x_187 = lean_ctor_get(x_171, 6);
x_188 = lean_ctor_get(x_171, 7);
x_189 = lean_ctor_get(x_171, 8);
x_190 = lean_ctor_get_uint8(x_171, sizeof(void*)*9 + 2);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_171);
x_191 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_191, 0, x_166);
lean_ctor_set(x_191, 1, x_168);
lean_ctor_set(x_191, 2, x_182);
lean_ctor_set(x_191, 3, x_183);
lean_ctor_set(x_191, 4, x_185);
lean_ctor_set(x_191, 5, x_186);
lean_ctor_set(x_191, 6, x_187);
lean_ctor_set(x_191, 7, x_188);
lean_ctor_set(x_191, 8, x_189);
lean_ctor_set_uint8(x_191, sizeof(void*)*9, x_181);
lean_ctor_set_uint8(x_191, sizeof(void*)*9 + 1, x_184);
lean_ctor_set_uint8(x_191, sizeof(void*)*9 + 2, x_190);
x_192 = lean_st_ref_set(x_1, x_191, x_172);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_194 = x_192;
} else {
 lean_dec_ref(x_192);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_12);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
else
{
uint8_t x_196; 
lean_dec(x_166);
x_196 = !lean_is_exclusive(x_167);
if (x_196 == 0)
{
return x_167;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_167, 0);
x_198 = lean_ctor_get(x_167, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_167);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
}
else
{
uint8_t x_200; 
lean_dec(x_144);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_200 = !lean_is_exclusive(x_145);
if (x_200 == 0)
{
return x_145;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_145, 0);
x_202 = lean_ctor_get(x_145, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_145);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
case 3:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_19, 1);
lean_inc(x_204);
lean_dec(x_19);
x_205 = lean_ctor_get(x_16, 0);
lean_inc(x_205);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_205);
lean_inc(x_20);
x_206 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(x_20, x_205, x_2, x_3, x_4, x_5, x_6, x_7, x_204);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = lean_ctor_get(x_16, 3);
lean_inc(x_209);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_2);
x_210 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__8(x_205, x_209, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_208);
lean_dec(x_209);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = l_Lean_indentExpr(x_205);
x_213 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2;
x_214 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_212);
x_215 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4;
x_216 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
x_217 = l_Lean_indentExpr(x_20);
x_218 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_220 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg(x_220, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_211);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_221;
}
else
{
uint8_t x_222; 
lean_dec(x_205);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_222 = !lean_is_exclusive(x_210);
if (x_222 == 0)
{
return x_210;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_210, 0);
x_224 = lean_ctor_get(x_210, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_210);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_205);
lean_dec(x_20);
lean_dec(x_16);
x_226 = lean_ctor_get(x_206, 1);
lean_inc(x_226);
lean_dec(x_206);
x_227 = lean_ctor_get(x_207, 0);
lean_inc(x_227);
lean_dec(x_207);
lean_inc(x_227);
x_228 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5(x_227, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_226);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_st_ref_take(x_1, x_230);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = !lean_is_exclusive(x_232);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_235 = lean_ctor_get(x_232, 1);
lean_dec(x_235);
x_236 = lean_ctor_get(x_232, 0);
lean_dec(x_236);
lean_ctor_set(x_232, 1, x_229);
lean_ctor_set(x_232, 0, x_227);
x_237 = lean_st_ref_set(x_1, x_232, x_233);
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_237, 0);
lean_dec(x_239);
lean_ctor_set(x_237, 0, x_12);
return x_237;
}
else
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_dec(x_237);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_12);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
else
{
uint8_t x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_242 = lean_ctor_get_uint8(x_232, sizeof(void*)*9);
x_243 = lean_ctor_get(x_232, 2);
x_244 = lean_ctor_get(x_232, 3);
x_245 = lean_ctor_get_uint8(x_232, sizeof(void*)*9 + 1);
x_246 = lean_ctor_get(x_232, 4);
x_247 = lean_ctor_get(x_232, 5);
x_248 = lean_ctor_get(x_232, 6);
x_249 = lean_ctor_get(x_232, 7);
x_250 = lean_ctor_get(x_232, 8);
x_251 = lean_ctor_get_uint8(x_232, sizeof(void*)*9 + 2);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_232);
x_252 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_252, 0, x_227);
lean_ctor_set(x_252, 1, x_229);
lean_ctor_set(x_252, 2, x_243);
lean_ctor_set(x_252, 3, x_244);
lean_ctor_set(x_252, 4, x_246);
lean_ctor_set(x_252, 5, x_247);
lean_ctor_set(x_252, 6, x_248);
lean_ctor_set(x_252, 7, x_249);
lean_ctor_set(x_252, 8, x_250);
lean_ctor_set_uint8(x_252, sizeof(void*)*9, x_242);
lean_ctor_set_uint8(x_252, sizeof(void*)*9 + 1, x_245);
lean_ctor_set_uint8(x_252, sizeof(void*)*9 + 2, x_251);
x_253 = lean_st_ref_set(x_1, x_252, x_233);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_255 = x_253;
} else {
 lean_dec_ref(x_253);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_12);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
else
{
uint8_t x_257; 
lean_dec(x_227);
x_257 = !lean_is_exclusive(x_228);
if (x_257 == 0)
{
return x_228;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_228, 0);
x_259 = lean_ctor_get(x_228, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_228);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
}
else
{
uint8_t x_261; 
lean_dec(x_205);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_261 = !lean_is_exclusive(x_206);
if (x_261 == 0)
{
return x_206;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_206, 0);
x_263 = lean_ctor_get(x_206, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_206);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
case 4:
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_19, 1);
lean_inc(x_265);
lean_dec(x_19);
x_266 = lean_ctor_get(x_16, 0);
lean_inc(x_266);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_266);
lean_inc(x_20);
x_267 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(x_20, x_266, x_2, x_3, x_4, x_5, x_6, x_7, x_265);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_270 = lean_ctor_get(x_16, 3);
lean_inc(x_270);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_2);
x_271 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__9(x_266, x_270, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_269);
lean_dec(x_270);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
lean_dec(x_271);
x_273 = l_Lean_indentExpr(x_266);
x_274 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2;
x_275 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_273);
x_276 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4;
x_277 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
x_278 = l_Lean_indentExpr(x_20);
x_279 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
x_280 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_281 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
x_282 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg(x_281, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_272);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_282;
}
else
{
uint8_t x_283; 
lean_dec(x_266);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_283 = !lean_is_exclusive(x_271);
if (x_283 == 0)
{
return x_271;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_271, 0);
x_285 = lean_ctor_get(x_271, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_271);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_266);
lean_dec(x_20);
lean_dec(x_16);
x_287 = lean_ctor_get(x_267, 1);
lean_inc(x_287);
lean_dec(x_267);
x_288 = lean_ctor_get(x_268, 0);
lean_inc(x_288);
lean_dec(x_268);
lean_inc(x_288);
x_289 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5(x_288, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_287);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec(x_289);
x_292 = lean_st_ref_take(x_1, x_291);
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_295 = !lean_is_exclusive(x_293);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_296 = lean_ctor_get(x_293, 1);
lean_dec(x_296);
x_297 = lean_ctor_get(x_293, 0);
lean_dec(x_297);
lean_ctor_set(x_293, 1, x_290);
lean_ctor_set(x_293, 0, x_288);
x_298 = lean_st_ref_set(x_1, x_293, x_294);
x_299 = !lean_is_exclusive(x_298);
if (x_299 == 0)
{
lean_object* x_300; 
x_300 = lean_ctor_get(x_298, 0);
lean_dec(x_300);
lean_ctor_set(x_298, 0, x_12);
return x_298;
}
else
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_12);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
}
else
{
uint8_t x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_303 = lean_ctor_get_uint8(x_293, sizeof(void*)*9);
x_304 = lean_ctor_get(x_293, 2);
x_305 = lean_ctor_get(x_293, 3);
x_306 = lean_ctor_get_uint8(x_293, sizeof(void*)*9 + 1);
x_307 = lean_ctor_get(x_293, 4);
x_308 = lean_ctor_get(x_293, 5);
x_309 = lean_ctor_get(x_293, 6);
x_310 = lean_ctor_get(x_293, 7);
x_311 = lean_ctor_get(x_293, 8);
x_312 = lean_ctor_get_uint8(x_293, sizeof(void*)*9 + 2);
lean_inc(x_311);
lean_inc(x_310);
lean_inc(x_309);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_293);
x_313 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_313, 0, x_288);
lean_ctor_set(x_313, 1, x_290);
lean_ctor_set(x_313, 2, x_304);
lean_ctor_set(x_313, 3, x_305);
lean_ctor_set(x_313, 4, x_307);
lean_ctor_set(x_313, 5, x_308);
lean_ctor_set(x_313, 6, x_309);
lean_ctor_set(x_313, 7, x_310);
lean_ctor_set(x_313, 8, x_311);
lean_ctor_set_uint8(x_313, sizeof(void*)*9, x_303);
lean_ctor_set_uint8(x_313, sizeof(void*)*9 + 1, x_306);
lean_ctor_set_uint8(x_313, sizeof(void*)*9 + 2, x_312);
x_314 = lean_st_ref_set(x_1, x_313, x_294);
x_315 = lean_ctor_get(x_314, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_316 = x_314;
} else {
 lean_dec_ref(x_314);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_12);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
else
{
uint8_t x_318; 
lean_dec(x_288);
x_318 = !lean_is_exclusive(x_289);
if (x_318 == 0)
{
return x_289;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_289, 0);
x_320 = lean_ctor_get(x_289, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_289);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
return x_321;
}
}
}
}
else
{
uint8_t x_322; 
lean_dec(x_266);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_322 = !lean_is_exclusive(x_267);
if (x_322 == 0)
{
return x_267;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_267, 0);
x_324 = lean_ctor_get(x_267, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_267);
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
return x_325;
}
}
}
case 5:
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_19, 1);
lean_inc(x_326);
lean_dec(x_19);
x_327 = lean_ctor_get(x_16, 0);
lean_inc(x_327);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_327);
lean_inc(x_20);
x_328 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(x_20, x_327, x_2, x_3, x_4, x_5, x_6, x_7, x_326);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
x_331 = lean_ctor_get(x_16, 3);
lean_inc(x_331);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_2);
x_332 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__10(x_327, x_331, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_330);
lean_dec(x_331);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_333 = lean_ctor_get(x_332, 1);
lean_inc(x_333);
lean_dec(x_332);
x_334 = l_Lean_indentExpr(x_327);
x_335 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2;
x_336 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_334);
x_337 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4;
x_338 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
x_339 = l_Lean_indentExpr(x_20);
x_340 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
x_341 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_342 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
x_343 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg(x_342, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_333);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_343;
}
else
{
uint8_t x_344; 
lean_dec(x_327);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_344 = !lean_is_exclusive(x_332);
if (x_344 == 0)
{
return x_332;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_332, 0);
x_346 = lean_ctor_get(x_332, 1);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_332);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
return x_347;
}
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_327);
lean_dec(x_20);
lean_dec(x_16);
x_348 = lean_ctor_get(x_328, 1);
lean_inc(x_348);
lean_dec(x_328);
x_349 = lean_ctor_get(x_329, 0);
lean_inc(x_349);
lean_dec(x_329);
lean_inc(x_349);
x_350 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5(x_349, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_348);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_353 = lean_st_ref_take(x_1, x_352);
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = !lean_is_exclusive(x_354);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; 
x_357 = lean_ctor_get(x_354, 1);
lean_dec(x_357);
x_358 = lean_ctor_get(x_354, 0);
lean_dec(x_358);
lean_ctor_set(x_354, 1, x_351);
lean_ctor_set(x_354, 0, x_349);
x_359 = lean_st_ref_set(x_1, x_354, x_355);
x_360 = !lean_is_exclusive(x_359);
if (x_360 == 0)
{
lean_object* x_361; 
x_361 = lean_ctor_get(x_359, 0);
lean_dec(x_361);
lean_ctor_set(x_359, 0, x_12);
return x_359;
}
else
{
lean_object* x_362; lean_object* x_363; 
x_362 = lean_ctor_get(x_359, 1);
lean_inc(x_362);
lean_dec(x_359);
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_12);
lean_ctor_set(x_363, 1, x_362);
return x_363;
}
}
else
{
uint8_t x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_364 = lean_ctor_get_uint8(x_354, sizeof(void*)*9);
x_365 = lean_ctor_get(x_354, 2);
x_366 = lean_ctor_get(x_354, 3);
x_367 = lean_ctor_get_uint8(x_354, sizeof(void*)*9 + 1);
x_368 = lean_ctor_get(x_354, 4);
x_369 = lean_ctor_get(x_354, 5);
x_370 = lean_ctor_get(x_354, 6);
x_371 = lean_ctor_get(x_354, 7);
x_372 = lean_ctor_get(x_354, 8);
x_373 = lean_ctor_get_uint8(x_354, sizeof(void*)*9 + 2);
lean_inc(x_372);
lean_inc(x_371);
lean_inc(x_370);
lean_inc(x_369);
lean_inc(x_368);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_354);
x_374 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_374, 0, x_349);
lean_ctor_set(x_374, 1, x_351);
lean_ctor_set(x_374, 2, x_365);
lean_ctor_set(x_374, 3, x_366);
lean_ctor_set(x_374, 4, x_368);
lean_ctor_set(x_374, 5, x_369);
lean_ctor_set(x_374, 6, x_370);
lean_ctor_set(x_374, 7, x_371);
lean_ctor_set(x_374, 8, x_372);
lean_ctor_set_uint8(x_374, sizeof(void*)*9, x_364);
lean_ctor_set_uint8(x_374, sizeof(void*)*9 + 1, x_367);
lean_ctor_set_uint8(x_374, sizeof(void*)*9 + 2, x_373);
x_375 = lean_st_ref_set(x_1, x_374, x_355);
x_376 = lean_ctor_get(x_375, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_377 = x_375;
} else {
 lean_dec_ref(x_375);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_12);
lean_ctor_set(x_378, 1, x_376);
return x_378;
}
}
else
{
uint8_t x_379; 
lean_dec(x_349);
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
}
else
{
uint8_t x_383; 
lean_dec(x_327);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_383 = !lean_is_exclusive(x_328);
if (x_383 == 0)
{
return x_328;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_384 = lean_ctor_get(x_328, 0);
x_385 = lean_ctor_get(x_328, 1);
lean_inc(x_385);
lean_inc(x_384);
lean_dec(x_328);
x_386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set(x_386, 1, x_385);
return x_386;
}
}
}
case 6:
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_19, 1);
lean_inc(x_387);
lean_dec(x_19);
x_388 = lean_ctor_get(x_16, 0);
lean_inc(x_388);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_388);
lean_inc(x_20);
x_389 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(x_20, x_388, x_2, x_3, x_4, x_5, x_6, x_7, x_387);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
lean_dec(x_389);
x_392 = lean_ctor_get(x_16, 3);
lean_inc(x_392);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_2);
x_393 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__11(x_388, x_392, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_391);
lean_dec(x_392);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
lean_dec(x_393);
x_395 = l_Lean_indentExpr(x_388);
x_396 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2;
x_397 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_395);
x_398 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4;
x_399 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_399, 1, x_398);
x_400 = l_Lean_indentExpr(x_20);
x_401 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_400);
x_402 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_403 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
x_404 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg(x_403, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_394);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_404;
}
else
{
uint8_t x_405; 
lean_dec(x_388);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_405 = !lean_is_exclusive(x_393);
if (x_405 == 0)
{
return x_393;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_393, 0);
x_407 = lean_ctor_get(x_393, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_393);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
return x_408;
}
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_388);
lean_dec(x_20);
lean_dec(x_16);
x_409 = lean_ctor_get(x_389, 1);
lean_inc(x_409);
lean_dec(x_389);
x_410 = lean_ctor_get(x_390, 0);
lean_inc(x_410);
lean_dec(x_390);
lean_inc(x_410);
x_411 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5(x_410, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_409);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = lean_st_ref_take(x_1, x_413);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_417 = !lean_is_exclusive(x_415);
if (x_417 == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; 
x_418 = lean_ctor_get(x_415, 1);
lean_dec(x_418);
x_419 = lean_ctor_get(x_415, 0);
lean_dec(x_419);
lean_ctor_set(x_415, 1, x_412);
lean_ctor_set(x_415, 0, x_410);
x_420 = lean_st_ref_set(x_1, x_415, x_416);
x_421 = !lean_is_exclusive(x_420);
if (x_421 == 0)
{
lean_object* x_422; 
x_422 = lean_ctor_get(x_420, 0);
lean_dec(x_422);
lean_ctor_set(x_420, 0, x_12);
return x_420;
}
else
{
lean_object* x_423; lean_object* x_424; 
x_423 = lean_ctor_get(x_420, 1);
lean_inc(x_423);
lean_dec(x_420);
x_424 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_424, 0, x_12);
lean_ctor_set(x_424, 1, x_423);
return x_424;
}
}
else
{
uint8_t x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_425 = lean_ctor_get_uint8(x_415, sizeof(void*)*9);
x_426 = lean_ctor_get(x_415, 2);
x_427 = lean_ctor_get(x_415, 3);
x_428 = lean_ctor_get_uint8(x_415, sizeof(void*)*9 + 1);
x_429 = lean_ctor_get(x_415, 4);
x_430 = lean_ctor_get(x_415, 5);
x_431 = lean_ctor_get(x_415, 6);
x_432 = lean_ctor_get(x_415, 7);
x_433 = lean_ctor_get(x_415, 8);
x_434 = lean_ctor_get_uint8(x_415, sizeof(void*)*9 + 2);
lean_inc(x_433);
lean_inc(x_432);
lean_inc(x_431);
lean_inc(x_430);
lean_inc(x_429);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_415);
x_435 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_435, 0, x_410);
lean_ctor_set(x_435, 1, x_412);
lean_ctor_set(x_435, 2, x_426);
lean_ctor_set(x_435, 3, x_427);
lean_ctor_set(x_435, 4, x_429);
lean_ctor_set(x_435, 5, x_430);
lean_ctor_set(x_435, 6, x_431);
lean_ctor_set(x_435, 7, x_432);
lean_ctor_set(x_435, 8, x_433);
lean_ctor_set_uint8(x_435, sizeof(void*)*9, x_425);
lean_ctor_set_uint8(x_435, sizeof(void*)*9 + 1, x_428);
lean_ctor_set_uint8(x_435, sizeof(void*)*9 + 2, x_434);
x_436 = lean_st_ref_set(x_1, x_435, x_416);
x_437 = lean_ctor_get(x_436, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 x_438 = x_436;
} else {
 lean_dec_ref(x_436);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(0, 2, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_12);
lean_ctor_set(x_439, 1, x_437);
return x_439;
}
}
else
{
uint8_t x_440; 
lean_dec(x_410);
x_440 = !lean_is_exclusive(x_411);
if (x_440 == 0)
{
return x_411;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_411, 0);
x_442 = lean_ctor_get(x_411, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_411);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
return x_443;
}
}
}
}
else
{
uint8_t x_444; 
lean_dec(x_388);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_444 = !lean_is_exclusive(x_389);
if (x_444 == 0)
{
return x_389;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_389, 0);
x_446 = lean_ctor_get(x_389, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_389);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
}
case 7:
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; uint8_t x_452; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_448 = lean_ctor_get(x_19, 1);
lean_inc(x_448);
lean_dec(x_19);
x_449 = lean_st_ref_take(x_1, x_448);
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_449, 1);
lean_inc(x_451);
lean_dec(x_449);
x_452 = !lean_is_exclusive(x_450);
if (x_452 == 0)
{
lean_object* x_453; lean_object* x_454; uint8_t x_455; 
x_453 = lean_ctor_get(x_450, 1);
lean_dec(x_453);
lean_ctor_set(x_450, 1, x_20);
x_454 = lean_st_ref_set(x_1, x_450, x_451);
x_455 = !lean_is_exclusive(x_454);
if (x_455 == 0)
{
lean_object* x_456; 
x_456 = lean_ctor_get(x_454, 0);
lean_dec(x_456);
lean_ctor_set(x_454, 0, x_12);
return x_454;
}
else
{
lean_object* x_457; lean_object* x_458; 
x_457 = lean_ctor_get(x_454, 1);
lean_inc(x_457);
lean_dec(x_454);
x_458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_458, 0, x_12);
lean_ctor_set(x_458, 1, x_457);
return x_458;
}
}
else
{
uint8_t x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_459 = lean_ctor_get_uint8(x_450, sizeof(void*)*9);
x_460 = lean_ctor_get(x_450, 0);
x_461 = lean_ctor_get(x_450, 2);
x_462 = lean_ctor_get(x_450, 3);
x_463 = lean_ctor_get_uint8(x_450, sizeof(void*)*9 + 1);
x_464 = lean_ctor_get(x_450, 4);
x_465 = lean_ctor_get(x_450, 5);
x_466 = lean_ctor_get(x_450, 6);
x_467 = lean_ctor_get(x_450, 7);
x_468 = lean_ctor_get(x_450, 8);
x_469 = lean_ctor_get_uint8(x_450, sizeof(void*)*9 + 2);
lean_inc(x_468);
lean_inc(x_467);
lean_inc(x_466);
lean_inc(x_465);
lean_inc(x_464);
lean_inc(x_462);
lean_inc(x_461);
lean_inc(x_460);
lean_dec(x_450);
x_470 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_470, 0, x_460);
lean_ctor_set(x_470, 1, x_20);
lean_ctor_set(x_470, 2, x_461);
lean_ctor_set(x_470, 3, x_462);
lean_ctor_set(x_470, 4, x_464);
lean_ctor_set(x_470, 5, x_465);
lean_ctor_set(x_470, 6, x_466);
lean_ctor_set(x_470, 7, x_467);
lean_ctor_set(x_470, 8, x_468);
lean_ctor_set_uint8(x_470, sizeof(void*)*9, x_459);
lean_ctor_set_uint8(x_470, sizeof(void*)*9 + 1, x_463);
lean_ctor_set_uint8(x_470, sizeof(void*)*9 + 2, x_469);
x_471 = lean_st_ref_set(x_1, x_470, x_451);
x_472 = lean_ctor_get(x_471, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 lean_ctor_release(x_471, 1);
 x_473 = x_471;
} else {
 lean_dec_ref(x_471);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(0, 2, 0);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_12);
lean_ctor_set(x_474, 1, x_472);
return x_474;
}
}
case 8:
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_19, 1);
lean_inc(x_475);
lean_dec(x_19);
x_476 = lean_ctor_get(x_16, 0);
lean_inc(x_476);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_476);
lean_inc(x_20);
x_477 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(x_20, x_476, x_2, x_3, x_4, x_5, x_6, x_7, x_475);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; 
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_477, 1);
lean_inc(x_479);
lean_dec(x_477);
x_480 = lean_ctor_get(x_16, 3);
lean_inc(x_480);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_2);
x_481 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__12(x_476, x_480, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_479);
lean_dec(x_480);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
lean_dec(x_481);
x_483 = l_Lean_indentExpr(x_476);
x_484 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2;
x_485 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_483);
x_486 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4;
x_487 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_487, 0, x_485);
lean_ctor_set(x_487, 1, x_486);
x_488 = l_Lean_indentExpr(x_20);
x_489 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_489, 0, x_487);
lean_ctor_set(x_489, 1, x_488);
x_490 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_491 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_491, 0, x_489);
lean_ctor_set(x_491, 1, x_490);
x_492 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg(x_491, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_482);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_492;
}
else
{
uint8_t x_493; 
lean_dec(x_476);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_493 = !lean_is_exclusive(x_481);
if (x_493 == 0)
{
return x_481;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_494 = lean_ctor_get(x_481, 0);
x_495 = lean_ctor_get(x_481, 1);
lean_inc(x_495);
lean_inc(x_494);
lean_dec(x_481);
x_496 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set(x_496, 1, x_495);
return x_496;
}
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; 
lean_dec(x_476);
lean_dec(x_20);
lean_dec(x_16);
x_497 = lean_ctor_get(x_477, 1);
lean_inc(x_497);
lean_dec(x_477);
x_498 = lean_ctor_get(x_478, 0);
lean_inc(x_498);
lean_dec(x_478);
lean_inc(x_498);
x_499 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5(x_498, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_497);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; 
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_499, 1);
lean_inc(x_501);
lean_dec(x_499);
x_502 = lean_st_ref_take(x_1, x_501);
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 1);
lean_inc(x_504);
lean_dec(x_502);
x_505 = !lean_is_exclusive(x_503);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; 
x_506 = lean_ctor_get(x_503, 1);
lean_dec(x_506);
x_507 = lean_ctor_get(x_503, 0);
lean_dec(x_507);
lean_ctor_set(x_503, 1, x_500);
lean_ctor_set(x_503, 0, x_498);
x_508 = lean_st_ref_set(x_1, x_503, x_504);
x_509 = !lean_is_exclusive(x_508);
if (x_509 == 0)
{
lean_object* x_510; 
x_510 = lean_ctor_get(x_508, 0);
lean_dec(x_510);
lean_ctor_set(x_508, 0, x_12);
return x_508;
}
else
{
lean_object* x_511; lean_object* x_512; 
x_511 = lean_ctor_get(x_508, 1);
lean_inc(x_511);
lean_dec(x_508);
x_512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_512, 0, x_12);
lean_ctor_set(x_512, 1, x_511);
return x_512;
}
}
else
{
uint8_t x_513; lean_object* x_514; lean_object* x_515; uint8_t x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_513 = lean_ctor_get_uint8(x_503, sizeof(void*)*9);
x_514 = lean_ctor_get(x_503, 2);
x_515 = lean_ctor_get(x_503, 3);
x_516 = lean_ctor_get_uint8(x_503, sizeof(void*)*9 + 1);
x_517 = lean_ctor_get(x_503, 4);
x_518 = lean_ctor_get(x_503, 5);
x_519 = lean_ctor_get(x_503, 6);
x_520 = lean_ctor_get(x_503, 7);
x_521 = lean_ctor_get(x_503, 8);
x_522 = lean_ctor_get_uint8(x_503, sizeof(void*)*9 + 2);
lean_inc(x_521);
lean_inc(x_520);
lean_inc(x_519);
lean_inc(x_518);
lean_inc(x_517);
lean_inc(x_515);
lean_inc(x_514);
lean_dec(x_503);
x_523 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_523, 0, x_498);
lean_ctor_set(x_523, 1, x_500);
lean_ctor_set(x_523, 2, x_514);
lean_ctor_set(x_523, 3, x_515);
lean_ctor_set(x_523, 4, x_517);
lean_ctor_set(x_523, 5, x_518);
lean_ctor_set(x_523, 6, x_519);
lean_ctor_set(x_523, 7, x_520);
lean_ctor_set(x_523, 8, x_521);
lean_ctor_set_uint8(x_523, sizeof(void*)*9, x_513);
lean_ctor_set_uint8(x_523, sizeof(void*)*9 + 1, x_516);
lean_ctor_set_uint8(x_523, sizeof(void*)*9 + 2, x_522);
x_524 = lean_st_ref_set(x_1, x_523, x_504);
x_525 = lean_ctor_get(x_524, 1);
lean_inc(x_525);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 x_526 = x_524;
} else {
 lean_dec_ref(x_524);
 x_526 = lean_box(0);
}
if (lean_is_scalar(x_526)) {
 x_527 = lean_alloc_ctor(0, 2, 0);
} else {
 x_527 = x_526;
}
lean_ctor_set(x_527, 0, x_12);
lean_ctor_set(x_527, 1, x_525);
return x_527;
}
}
else
{
uint8_t x_528; 
lean_dec(x_498);
x_528 = !lean_is_exclusive(x_499);
if (x_528 == 0)
{
return x_499;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_499, 0);
x_530 = lean_ctor_get(x_499, 1);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_499);
x_531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_531, 0, x_529);
lean_ctor_set(x_531, 1, x_530);
return x_531;
}
}
}
}
else
{
uint8_t x_532; 
lean_dec(x_476);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_532 = !lean_is_exclusive(x_477);
if (x_532 == 0)
{
return x_477;
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_533 = lean_ctor_get(x_477, 0);
x_534 = lean_ctor_get(x_477, 1);
lean_inc(x_534);
lean_inc(x_533);
lean_dec(x_477);
x_535 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_535, 0, x_533);
lean_ctor_set(x_535, 1, x_534);
return x_535;
}
}
}
case 9:
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_536 = lean_ctor_get(x_19, 1);
lean_inc(x_536);
lean_dec(x_19);
x_537 = lean_ctor_get(x_16, 0);
lean_inc(x_537);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_537);
lean_inc(x_20);
x_538 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(x_20, x_537, x_2, x_3, x_4, x_5, x_6, x_7, x_536);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; 
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_540 = lean_ctor_get(x_538, 1);
lean_inc(x_540);
lean_dec(x_538);
x_541 = lean_ctor_get(x_16, 3);
lean_inc(x_541);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_2);
x_542 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__13(x_537, x_541, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_540);
lean_dec(x_541);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_543 = lean_ctor_get(x_542, 1);
lean_inc(x_543);
lean_dec(x_542);
x_544 = l_Lean_indentExpr(x_537);
x_545 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2;
x_546 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_546, 1, x_544);
x_547 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4;
x_548 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_548, 0, x_546);
lean_ctor_set(x_548, 1, x_547);
x_549 = l_Lean_indentExpr(x_20);
x_550 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_550, 0, x_548);
lean_ctor_set(x_550, 1, x_549);
x_551 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_552 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
x_553 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg(x_552, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_543);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_553;
}
else
{
uint8_t x_554; 
lean_dec(x_537);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_554 = !lean_is_exclusive(x_542);
if (x_554 == 0)
{
return x_542;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_542, 0);
x_556 = lean_ctor_get(x_542, 1);
lean_inc(x_556);
lean_inc(x_555);
lean_dec(x_542);
x_557 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_556);
return x_557;
}
}
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; 
lean_dec(x_537);
lean_dec(x_20);
lean_dec(x_16);
x_558 = lean_ctor_get(x_538, 1);
lean_inc(x_558);
lean_dec(x_538);
x_559 = lean_ctor_get(x_539, 0);
lean_inc(x_559);
lean_dec(x_539);
lean_inc(x_559);
x_560 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5(x_559, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_558);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; uint8_t x_566; 
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_560, 1);
lean_inc(x_562);
lean_dec(x_560);
x_563 = lean_st_ref_take(x_1, x_562);
x_564 = lean_ctor_get(x_563, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_563, 1);
lean_inc(x_565);
lean_dec(x_563);
x_566 = !lean_is_exclusive(x_564);
if (x_566 == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; uint8_t x_570; 
x_567 = lean_ctor_get(x_564, 1);
lean_dec(x_567);
x_568 = lean_ctor_get(x_564, 0);
lean_dec(x_568);
lean_ctor_set(x_564, 1, x_561);
lean_ctor_set(x_564, 0, x_559);
x_569 = lean_st_ref_set(x_1, x_564, x_565);
x_570 = !lean_is_exclusive(x_569);
if (x_570 == 0)
{
lean_object* x_571; 
x_571 = lean_ctor_get(x_569, 0);
lean_dec(x_571);
lean_ctor_set(x_569, 0, x_12);
return x_569;
}
else
{
lean_object* x_572; lean_object* x_573; 
x_572 = lean_ctor_get(x_569, 1);
lean_inc(x_572);
lean_dec(x_569);
x_573 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_573, 0, x_12);
lean_ctor_set(x_573, 1, x_572);
return x_573;
}
}
else
{
uint8_t x_574; lean_object* x_575; lean_object* x_576; uint8_t x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; uint8_t x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_574 = lean_ctor_get_uint8(x_564, sizeof(void*)*9);
x_575 = lean_ctor_get(x_564, 2);
x_576 = lean_ctor_get(x_564, 3);
x_577 = lean_ctor_get_uint8(x_564, sizeof(void*)*9 + 1);
x_578 = lean_ctor_get(x_564, 4);
x_579 = lean_ctor_get(x_564, 5);
x_580 = lean_ctor_get(x_564, 6);
x_581 = lean_ctor_get(x_564, 7);
x_582 = lean_ctor_get(x_564, 8);
x_583 = lean_ctor_get_uint8(x_564, sizeof(void*)*9 + 2);
lean_inc(x_582);
lean_inc(x_581);
lean_inc(x_580);
lean_inc(x_579);
lean_inc(x_578);
lean_inc(x_576);
lean_inc(x_575);
lean_dec(x_564);
x_584 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_584, 0, x_559);
lean_ctor_set(x_584, 1, x_561);
lean_ctor_set(x_584, 2, x_575);
lean_ctor_set(x_584, 3, x_576);
lean_ctor_set(x_584, 4, x_578);
lean_ctor_set(x_584, 5, x_579);
lean_ctor_set(x_584, 6, x_580);
lean_ctor_set(x_584, 7, x_581);
lean_ctor_set(x_584, 8, x_582);
lean_ctor_set_uint8(x_584, sizeof(void*)*9, x_574);
lean_ctor_set_uint8(x_584, sizeof(void*)*9 + 1, x_577);
lean_ctor_set_uint8(x_584, sizeof(void*)*9 + 2, x_583);
x_585 = lean_st_ref_set(x_1, x_584, x_565);
x_586 = lean_ctor_get(x_585, 1);
lean_inc(x_586);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 lean_ctor_release(x_585, 1);
 x_587 = x_585;
} else {
 lean_dec_ref(x_585);
 x_587 = lean_box(0);
}
if (lean_is_scalar(x_587)) {
 x_588 = lean_alloc_ctor(0, 2, 0);
} else {
 x_588 = x_587;
}
lean_ctor_set(x_588, 0, x_12);
lean_ctor_set(x_588, 1, x_586);
return x_588;
}
}
else
{
uint8_t x_589; 
lean_dec(x_559);
x_589 = !lean_is_exclusive(x_560);
if (x_589 == 0)
{
return x_560;
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_560, 0);
x_591 = lean_ctor_get(x_560, 1);
lean_inc(x_591);
lean_inc(x_590);
lean_dec(x_560);
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_591);
return x_592;
}
}
}
}
else
{
uint8_t x_593; 
lean_dec(x_537);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_593 = !lean_is_exclusive(x_538);
if (x_593 == 0)
{
return x_538;
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_594 = lean_ctor_get(x_538, 0);
x_595 = lean_ctor_get(x_538, 1);
lean_inc(x_595);
lean_inc(x_594);
lean_dec(x_538);
x_596 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_596, 0, x_594);
lean_ctor_set(x_596, 1, x_595);
return x_596;
}
}
}
case 10:
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_19, 1);
lean_inc(x_597);
lean_dec(x_19);
x_598 = lean_ctor_get(x_16, 0);
lean_inc(x_598);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_598);
lean_inc(x_20);
x_599 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(x_20, x_598, x_2, x_3, x_4, x_5, x_6, x_7, x_597);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; 
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
x_602 = lean_ctor_get(x_16, 3);
lean_inc(x_602);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_2);
x_603 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__14(x_598, x_602, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_601);
lean_dec(x_602);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_604 = lean_ctor_get(x_603, 1);
lean_inc(x_604);
lean_dec(x_603);
x_605 = l_Lean_indentExpr(x_598);
x_606 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2;
x_607 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_607, 0, x_606);
lean_ctor_set(x_607, 1, x_605);
x_608 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4;
x_609 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_609, 0, x_607);
lean_ctor_set(x_609, 1, x_608);
x_610 = l_Lean_indentExpr(x_20);
x_611 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_611, 0, x_609);
lean_ctor_set(x_611, 1, x_610);
x_612 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_613 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_613, 0, x_611);
lean_ctor_set(x_613, 1, x_612);
x_614 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg(x_613, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_604);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_614;
}
else
{
uint8_t x_615; 
lean_dec(x_598);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_615 = !lean_is_exclusive(x_603);
if (x_615 == 0)
{
return x_603;
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_616 = lean_ctor_get(x_603, 0);
x_617 = lean_ctor_get(x_603, 1);
lean_inc(x_617);
lean_inc(x_616);
lean_dec(x_603);
x_618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_618, 0, x_616);
lean_ctor_set(x_618, 1, x_617);
return x_618;
}
}
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_598);
lean_dec(x_20);
lean_dec(x_16);
x_619 = lean_ctor_get(x_599, 1);
lean_inc(x_619);
lean_dec(x_599);
x_620 = lean_ctor_get(x_600, 0);
lean_inc(x_620);
lean_dec(x_600);
lean_inc(x_620);
x_621 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5(x_620, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_619);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; 
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec(x_621);
x_624 = lean_st_ref_take(x_1, x_623);
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_624, 1);
lean_inc(x_626);
lean_dec(x_624);
x_627 = !lean_is_exclusive(x_625);
if (x_627 == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; 
x_628 = lean_ctor_get(x_625, 1);
lean_dec(x_628);
x_629 = lean_ctor_get(x_625, 0);
lean_dec(x_629);
lean_ctor_set(x_625, 1, x_622);
lean_ctor_set(x_625, 0, x_620);
x_630 = lean_st_ref_set(x_1, x_625, x_626);
x_631 = !lean_is_exclusive(x_630);
if (x_631 == 0)
{
lean_object* x_632; 
x_632 = lean_ctor_get(x_630, 0);
lean_dec(x_632);
lean_ctor_set(x_630, 0, x_12);
return x_630;
}
else
{
lean_object* x_633; lean_object* x_634; 
x_633 = lean_ctor_get(x_630, 1);
lean_inc(x_633);
lean_dec(x_630);
x_634 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_634, 0, x_12);
lean_ctor_set(x_634, 1, x_633);
return x_634;
}
}
else
{
uint8_t x_635; lean_object* x_636; lean_object* x_637; uint8_t x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; uint8_t x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_635 = lean_ctor_get_uint8(x_625, sizeof(void*)*9);
x_636 = lean_ctor_get(x_625, 2);
x_637 = lean_ctor_get(x_625, 3);
x_638 = lean_ctor_get_uint8(x_625, sizeof(void*)*9 + 1);
x_639 = lean_ctor_get(x_625, 4);
x_640 = lean_ctor_get(x_625, 5);
x_641 = lean_ctor_get(x_625, 6);
x_642 = lean_ctor_get(x_625, 7);
x_643 = lean_ctor_get(x_625, 8);
x_644 = lean_ctor_get_uint8(x_625, sizeof(void*)*9 + 2);
lean_inc(x_643);
lean_inc(x_642);
lean_inc(x_641);
lean_inc(x_640);
lean_inc(x_639);
lean_inc(x_637);
lean_inc(x_636);
lean_dec(x_625);
x_645 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_645, 0, x_620);
lean_ctor_set(x_645, 1, x_622);
lean_ctor_set(x_645, 2, x_636);
lean_ctor_set(x_645, 3, x_637);
lean_ctor_set(x_645, 4, x_639);
lean_ctor_set(x_645, 5, x_640);
lean_ctor_set(x_645, 6, x_641);
lean_ctor_set(x_645, 7, x_642);
lean_ctor_set(x_645, 8, x_643);
lean_ctor_set_uint8(x_645, sizeof(void*)*9, x_635);
lean_ctor_set_uint8(x_645, sizeof(void*)*9 + 1, x_638);
lean_ctor_set_uint8(x_645, sizeof(void*)*9 + 2, x_644);
x_646 = lean_st_ref_set(x_1, x_645, x_626);
x_647 = lean_ctor_get(x_646, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 lean_ctor_release(x_646, 1);
 x_648 = x_646;
} else {
 lean_dec_ref(x_646);
 x_648 = lean_box(0);
}
if (lean_is_scalar(x_648)) {
 x_649 = lean_alloc_ctor(0, 2, 0);
} else {
 x_649 = x_648;
}
lean_ctor_set(x_649, 0, x_12);
lean_ctor_set(x_649, 1, x_647);
return x_649;
}
}
else
{
uint8_t x_650; 
lean_dec(x_620);
x_650 = !lean_is_exclusive(x_621);
if (x_650 == 0)
{
return x_621;
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_651 = lean_ctor_get(x_621, 0);
x_652 = lean_ctor_get(x_621, 1);
lean_inc(x_652);
lean_inc(x_651);
lean_dec(x_621);
x_653 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_653, 0, x_651);
lean_ctor_set(x_653, 1, x_652);
return x_653;
}
}
}
}
else
{
uint8_t x_654; 
lean_dec(x_598);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_654 = !lean_is_exclusive(x_599);
if (x_654 == 0)
{
return x_599;
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_655 = lean_ctor_get(x_599, 0);
x_656 = lean_ctor_get(x_599, 1);
lean_inc(x_656);
lean_inc(x_655);
lean_dec(x_599);
x_657 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_657, 0, x_655);
lean_ctor_set(x_657, 1, x_656);
return x_657;
}
}
}
case 11:
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_658 = lean_ctor_get(x_19, 1);
lean_inc(x_658);
lean_dec(x_19);
x_659 = lean_ctor_get(x_16, 0);
lean_inc(x_659);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_659);
lean_inc(x_20);
x_660 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(x_20, x_659, x_2, x_3, x_4, x_5, x_6, x_7, x_658);
if (lean_obj_tag(x_660) == 0)
{
lean_object* x_661; 
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_662 = lean_ctor_get(x_660, 1);
lean_inc(x_662);
lean_dec(x_660);
x_663 = lean_ctor_get(x_16, 3);
lean_inc(x_663);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_2);
x_664 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__15(x_659, x_663, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_662);
lean_dec(x_663);
if (lean_obj_tag(x_664) == 0)
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_665 = lean_ctor_get(x_664, 1);
lean_inc(x_665);
lean_dec(x_664);
x_666 = l_Lean_indentExpr(x_659);
x_667 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2;
x_668 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_668, 0, x_667);
lean_ctor_set(x_668, 1, x_666);
x_669 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4;
x_670 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_670, 0, x_668);
lean_ctor_set(x_670, 1, x_669);
x_671 = l_Lean_indentExpr(x_20);
x_672 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_672, 0, x_670);
lean_ctor_set(x_672, 1, x_671);
x_673 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_674 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_674, 0, x_672);
lean_ctor_set(x_674, 1, x_673);
x_675 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg(x_674, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_665);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_675;
}
else
{
uint8_t x_676; 
lean_dec(x_659);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_676 = !lean_is_exclusive(x_664);
if (x_676 == 0)
{
return x_664;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_677 = lean_ctor_get(x_664, 0);
x_678 = lean_ctor_get(x_664, 1);
lean_inc(x_678);
lean_inc(x_677);
lean_dec(x_664);
x_679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_679, 0, x_677);
lean_ctor_set(x_679, 1, x_678);
return x_679;
}
}
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; 
lean_dec(x_659);
lean_dec(x_20);
lean_dec(x_16);
x_680 = lean_ctor_get(x_660, 1);
lean_inc(x_680);
lean_dec(x_660);
x_681 = lean_ctor_get(x_661, 0);
lean_inc(x_681);
lean_dec(x_661);
lean_inc(x_681);
x_682 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5(x_681, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_680);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; uint8_t x_688; 
x_683 = lean_ctor_get(x_682, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_682, 1);
lean_inc(x_684);
lean_dec(x_682);
x_685 = lean_st_ref_take(x_1, x_684);
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_685, 1);
lean_inc(x_687);
lean_dec(x_685);
x_688 = !lean_is_exclusive(x_686);
if (x_688 == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; uint8_t x_692; 
x_689 = lean_ctor_get(x_686, 1);
lean_dec(x_689);
x_690 = lean_ctor_get(x_686, 0);
lean_dec(x_690);
lean_ctor_set(x_686, 1, x_683);
lean_ctor_set(x_686, 0, x_681);
x_691 = lean_st_ref_set(x_1, x_686, x_687);
x_692 = !lean_is_exclusive(x_691);
if (x_692 == 0)
{
lean_object* x_693; 
x_693 = lean_ctor_get(x_691, 0);
lean_dec(x_693);
lean_ctor_set(x_691, 0, x_12);
return x_691;
}
else
{
lean_object* x_694; lean_object* x_695; 
x_694 = lean_ctor_get(x_691, 1);
lean_inc(x_694);
lean_dec(x_691);
x_695 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_695, 0, x_12);
lean_ctor_set(x_695, 1, x_694);
return x_695;
}
}
else
{
uint8_t x_696; lean_object* x_697; lean_object* x_698; uint8_t x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; uint8_t x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; 
x_696 = lean_ctor_get_uint8(x_686, sizeof(void*)*9);
x_697 = lean_ctor_get(x_686, 2);
x_698 = lean_ctor_get(x_686, 3);
x_699 = lean_ctor_get_uint8(x_686, sizeof(void*)*9 + 1);
x_700 = lean_ctor_get(x_686, 4);
x_701 = lean_ctor_get(x_686, 5);
x_702 = lean_ctor_get(x_686, 6);
x_703 = lean_ctor_get(x_686, 7);
x_704 = lean_ctor_get(x_686, 8);
x_705 = lean_ctor_get_uint8(x_686, sizeof(void*)*9 + 2);
lean_inc(x_704);
lean_inc(x_703);
lean_inc(x_702);
lean_inc(x_701);
lean_inc(x_700);
lean_inc(x_698);
lean_inc(x_697);
lean_dec(x_686);
x_706 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_706, 0, x_681);
lean_ctor_set(x_706, 1, x_683);
lean_ctor_set(x_706, 2, x_697);
lean_ctor_set(x_706, 3, x_698);
lean_ctor_set(x_706, 4, x_700);
lean_ctor_set(x_706, 5, x_701);
lean_ctor_set(x_706, 6, x_702);
lean_ctor_set(x_706, 7, x_703);
lean_ctor_set(x_706, 8, x_704);
lean_ctor_set_uint8(x_706, sizeof(void*)*9, x_696);
lean_ctor_set_uint8(x_706, sizeof(void*)*9 + 1, x_699);
lean_ctor_set_uint8(x_706, sizeof(void*)*9 + 2, x_705);
x_707 = lean_st_ref_set(x_1, x_706, x_687);
x_708 = lean_ctor_get(x_707, 1);
lean_inc(x_708);
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 lean_ctor_release(x_707, 1);
 x_709 = x_707;
} else {
 lean_dec_ref(x_707);
 x_709 = lean_box(0);
}
if (lean_is_scalar(x_709)) {
 x_710 = lean_alloc_ctor(0, 2, 0);
} else {
 x_710 = x_709;
}
lean_ctor_set(x_710, 0, x_12);
lean_ctor_set(x_710, 1, x_708);
return x_710;
}
}
else
{
uint8_t x_711; 
lean_dec(x_681);
x_711 = !lean_is_exclusive(x_682);
if (x_711 == 0)
{
return x_682;
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; 
x_712 = lean_ctor_get(x_682, 0);
x_713 = lean_ctor_get(x_682, 1);
lean_inc(x_713);
lean_inc(x_712);
lean_dec(x_682);
x_714 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_714, 0, x_712);
lean_ctor_set(x_714, 1, x_713);
return x_714;
}
}
}
}
else
{
uint8_t x_715; 
lean_dec(x_659);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_715 = !lean_is_exclusive(x_660);
if (x_715 == 0)
{
return x_660;
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_716 = lean_ctor_get(x_660, 0);
x_717 = lean_ctor_get(x_660, 1);
lean_inc(x_717);
lean_inc(x_716);
lean_dec(x_660);
x_718 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_718, 0, x_716);
lean_ctor_set(x_718, 1, x_717);
return x_718;
}
}
}
default: 
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_719 = lean_ctor_get(x_19, 1);
lean_inc(x_719);
lean_dec(x_19);
x_720 = lean_ctor_get(x_16, 0);
lean_inc(x_720);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_720);
lean_inc(x_20);
x_721 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f(x_20, x_720, x_2, x_3, x_4, x_5, x_6, x_7, x_719);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; 
x_722 = lean_ctor_get(x_721, 0);
lean_inc(x_722);
if (lean_obj_tag(x_722) == 0)
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_723 = lean_ctor_get(x_721, 1);
lean_inc(x_723);
lean_dec(x_721);
x_724 = lean_ctor_get(x_16, 3);
lean_inc(x_724);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_2);
x_725 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__16(x_720, x_724, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_723);
lean_dec(x_724);
if (lean_obj_tag(x_725) == 0)
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_726 = lean_ctor_get(x_725, 1);
lean_inc(x_726);
lean_dec(x_725);
x_727 = l_Lean_indentExpr(x_720);
x_728 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2;
x_729 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_729, 0, x_728);
lean_ctor_set(x_729, 1, x_727);
x_730 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4;
x_731 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_731, 0, x_729);
lean_ctor_set(x_731, 1, x_730);
x_732 = l_Lean_indentExpr(x_20);
x_733 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_733, 0, x_731);
lean_ctor_set(x_733, 1, x_732);
x_734 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_735 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_735, 0, x_733);
lean_ctor_set(x_735, 1, x_734);
x_736 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg(x_735, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_726);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_736;
}
else
{
uint8_t x_737; 
lean_dec(x_720);
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_737 = !lean_is_exclusive(x_725);
if (x_737 == 0)
{
return x_725;
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_738 = lean_ctor_get(x_725, 0);
x_739 = lean_ctor_get(x_725, 1);
lean_inc(x_739);
lean_inc(x_738);
lean_dec(x_725);
x_740 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_740, 0, x_738);
lean_ctor_set(x_740, 1, x_739);
return x_740;
}
}
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; 
lean_dec(x_720);
lean_dec(x_20);
lean_dec(x_16);
x_741 = lean_ctor_get(x_721, 1);
lean_inc(x_741);
lean_dec(x_721);
x_742 = lean_ctor_get(x_722, 0);
lean_inc(x_742);
lean_dec(x_722);
lean_inc(x_742);
x_743 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5(x_742, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_741);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_743) == 0)
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; uint8_t x_749; 
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_743, 1);
lean_inc(x_745);
lean_dec(x_743);
x_746 = lean_st_ref_take(x_1, x_745);
x_747 = lean_ctor_get(x_746, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_746, 1);
lean_inc(x_748);
lean_dec(x_746);
x_749 = !lean_is_exclusive(x_747);
if (x_749 == 0)
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; uint8_t x_753; 
x_750 = lean_ctor_get(x_747, 1);
lean_dec(x_750);
x_751 = lean_ctor_get(x_747, 0);
lean_dec(x_751);
lean_ctor_set(x_747, 1, x_744);
lean_ctor_set(x_747, 0, x_742);
x_752 = lean_st_ref_set(x_1, x_747, x_748);
x_753 = !lean_is_exclusive(x_752);
if (x_753 == 0)
{
lean_object* x_754; 
x_754 = lean_ctor_get(x_752, 0);
lean_dec(x_754);
lean_ctor_set(x_752, 0, x_12);
return x_752;
}
else
{
lean_object* x_755; lean_object* x_756; 
x_755 = lean_ctor_get(x_752, 1);
lean_inc(x_755);
lean_dec(x_752);
x_756 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_756, 0, x_12);
lean_ctor_set(x_756, 1, x_755);
return x_756;
}
}
else
{
uint8_t x_757; lean_object* x_758; lean_object* x_759; uint8_t x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; uint8_t x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; 
x_757 = lean_ctor_get_uint8(x_747, sizeof(void*)*9);
x_758 = lean_ctor_get(x_747, 2);
x_759 = lean_ctor_get(x_747, 3);
x_760 = lean_ctor_get_uint8(x_747, sizeof(void*)*9 + 1);
x_761 = lean_ctor_get(x_747, 4);
x_762 = lean_ctor_get(x_747, 5);
x_763 = lean_ctor_get(x_747, 6);
x_764 = lean_ctor_get(x_747, 7);
x_765 = lean_ctor_get(x_747, 8);
x_766 = lean_ctor_get_uint8(x_747, sizeof(void*)*9 + 2);
lean_inc(x_765);
lean_inc(x_764);
lean_inc(x_763);
lean_inc(x_762);
lean_inc(x_761);
lean_inc(x_759);
lean_inc(x_758);
lean_dec(x_747);
x_767 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_767, 0, x_742);
lean_ctor_set(x_767, 1, x_744);
lean_ctor_set(x_767, 2, x_758);
lean_ctor_set(x_767, 3, x_759);
lean_ctor_set(x_767, 4, x_761);
lean_ctor_set(x_767, 5, x_762);
lean_ctor_set(x_767, 6, x_763);
lean_ctor_set(x_767, 7, x_764);
lean_ctor_set(x_767, 8, x_765);
lean_ctor_set_uint8(x_767, sizeof(void*)*9, x_757);
lean_ctor_set_uint8(x_767, sizeof(void*)*9 + 1, x_760);
lean_ctor_set_uint8(x_767, sizeof(void*)*9 + 2, x_766);
x_768 = lean_st_ref_set(x_1, x_767, x_748);
x_769 = lean_ctor_get(x_768, 1);
lean_inc(x_769);
if (lean_is_exclusive(x_768)) {
 lean_ctor_release(x_768, 0);
 lean_ctor_release(x_768, 1);
 x_770 = x_768;
} else {
 lean_dec_ref(x_768);
 x_770 = lean_box(0);
}
if (lean_is_scalar(x_770)) {
 x_771 = lean_alloc_ctor(0, 2, 0);
} else {
 x_771 = x_770;
}
lean_ctor_set(x_771, 0, x_12);
lean_ctor_set(x_771, 1, x_769);
return x_771;
}
}
else
{
uint8_t x_772; 
lean_dec(x_742);
x_772 = !lean_is_exclusive(x_743);
if (x_772 == 0)
{
return x_743;
}
else
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_773 = lean_ctor_get(x_743, 0);
x_774 = lean_ctor_get(x_743, 1);
lean_inc(x_774);
lean_inc(x_773);
lean_dec(x_743);
x_775 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_775, 0, x_773);
lean_ctor_set(x_775, 1, x_774);
return x_775;
}
}
}
}
else
{
uint8_t x_776; 
lean_dec(x_720);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_776 = !lean_is_exclusive(x_721);
if (x_776 == 0)
{
return x_721;
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; 
x_777 = lean_ctor_get(x_721, 0);
x_778 = lean_ctor_get(x_721, 1);
lean_inc(x_778);
lean_inc(x_777);
lean_dec(x_721);
x_779 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_779, 0, x_777);
lean_ctor_set(x_779, 1, x_778);
return x_779;
}
}
}
}
}
else
{
uint8_t x_780; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_780 = !lean_is_exclusive(x_19);
if (x_780 == 0)
{
return x_19;
}
else
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; 
x_781 = lean_ctor_get(x_19, 0);
x_782 = lean_ctor_get(x_19, 1);
lean_inc(x_782);
lean_inc(x_781);
lean_dec(x_19);
x_783 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_783, 0, x_781);
lean_ctor_set(x_783, 1, x_782);
return x_783;
}
}
}
else
{
uint8_t x_784; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_784 = !lean_is_exclusive(x_13);
if (x_784 == 0)
{
return x_13;
}
else
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; 
x_785 = lean_ctor_get(x_13, 0);
x_786 = lean_ctor_get(x_13, 1);
lean_inc(x_786);
lean_inc(x_785);
lean_dec(x_13);
x_787 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_787, 0, x_785);
lean_ctor_set(x_787, 1, x_786);
return x_787;
}
}
}
else
{
uint8_t x_788; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_788 = !lean_is_exclusive(x_9);
if (x_788 == 0)
{
return x_9;
}
else
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; 
x_789 = lean_ctor_get(x_9, 0);
x_790 = lean_ctor_get(x_9, 1);
lean_inc(x_790);
lean_inc(x_789);
lean_dec(x_9);
x_791 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_791, 0, x_789);
lean_ctor_set(x_791, 1, x_790);
return x_791;
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
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
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
lean_object* l_List_filterAux___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_6, 1);
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
x_14 = lean_ctor_get(x_12, 1);
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
x_4 = l_List_filterAux___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_List_filterAux___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterAux___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1(x_1, x_2, x_3);
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
lean_object* l_Array_anyRangeMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_18 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
x_13 = l_Array_anyRangeMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1(x_1, x_1, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Array_anyRangeMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_anyRangeMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
x_3 = lean_ctor_get(x_2, 1);
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
x_11 = l_List_find_x3f___rarg(x_10, x_2);
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
x_32 = l_List_find_x3f___rarg(x_31, x_2);
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
x_49 = l_List_find_x3f___rarg(x_48, x_2);
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
lean_object* l_Lean_Meta_commitWhen___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_28; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_5, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Meta_isExprDefEqAux(x_1, x_2, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = 0;
x_36 = lean_box(x_35);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_dec(x_28);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_42 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed(x_3, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_45);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = 0;
x_50 = lean_box(x_49);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = 0;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_42, 0);
lean_dec(x_56);
x_57 = 1;
x_58 = lean_box(x_57);
lean_ctor_set(x_42, 0, x_58);
return x_42;
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_42, 1);
lean_inc(x_59);
lean_dec(x_42);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
lean_dec(x_42);
x_20 = x_63;
x_21 = x_64;
goto block_27;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_28, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_28, 1);
lean_inc(x_66);
lean_dec(x_28);
x_20 = x_65;
x_21 = x_66;
goto block_27;
}
block_27:
{
lean_object* x_22; uint8_t x_23; 
x_22 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Meta_commitWhen___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_28; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_5, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Meta_isExprDefEqAux(x_1, x_2, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = 0;
x_36 = lean_box(x_35);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_dec(x_28);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_42 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed(x_3, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_45);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = 0;
x_50 = lean_box(x_49);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = 0;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_42, 0);
lean_dec(x_56);
x_57 = 1;
x_58 = lean_box(x_57);
lean_ctor_set(x_42, 0, x_58);
return x_42;
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_42, 1);
lean_inc(x_59);
lean_dec(x_42);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
lean_dec(x_42);
x_20 = x_63;
x_21 = x_64;
goto block_27;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_28, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_28, 1);
lean_inc(x_66);
lean_dec(x_28);
x_20 = x_65;
x_21 = x_66;
goto block_27;
}
block_27:
{
lean_object* x_22; uint8_t x_23; 
x_22 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_20; lean_object* x_21; lean_object* x_425; lean_object* x_426; lean_object* x_427; uint8_t x_428; 
x_425 = lean_st_ref_get(x_9, x_10);
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
x_20 = x_430;
x_21 = x_429;
goto block_424;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; 
x_431 = lean_ctor_get(x_425, 1);
lean_inc(x_431);
lean_dec(x_425);
x_432 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_433 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_432, x_6, x_7, x_8, x_9, x_431);
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
lean_dec(x_433);
x_436 = lean_unbox(x_434);
lean_dec(x_434);
x_20 = x_436;
x_21 = x_435;
goto block_424;
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
block_424:
{
if (x_20 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_st_ref_get(x_9, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 3);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_ctor_get_uint8(x_24, sizeof(void*)*1);
lean_dec(x_24);
x_27 = lean_st_ref_take(x_9, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_28, 3);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; uint8_t x_86; lean_object* x_87; 
x_34 = 0;
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_34);
x_35 = lean_st_ref_set(x_9, x_28, x_30);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_86 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_87 = l_Lean_Meta_commitWhen___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_1, x_2, x_86, x_6, x_7, x_8, x_9, x_36);
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
x_90 = x_34;
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
x_125 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_124, x_6, x_7, x_8, x_9, x_123);
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
x_37 = x_92;
x_38 = x_91;
goto block_85;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_93 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_93, 0, x_1);
x_94 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_95 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Meta_isLevelDefEqAux___closed__7;
x_97 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_98, 0, x_2);
x_99 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_Meta_isLevelDefEq___rarg___lambda__1___closed__2;
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_unbox(x_88);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_103 = l_Lean_Meta_isLevelDefEq___rarg___lambda__1___closed__4;
x_104 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_94);
x_106 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_107 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_106, x_105, x_6, x_7, x_8, x_9, x_91);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_unbox(x_88);
lean_dec(x_88);
x_37 = x_109;
x_38 = x_108;
goto block_85;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_110 = l_Lean_Meta_isLevelDefEq___rarg___lambda__1___closed__6;
x_111 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_111, 0, x_101);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_94);
x_113 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_114 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_113, x_112, x_6, x_7, x_8, x_9, x_91);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = lean_unbox(x_88);
lean_dec(x_88);
x_37 = x_116;
x_38 = x_115;
goto block_85;
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
lean_ctor_set_uint8(x_135, sizeof(void*)*1, x_26);
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
lean_ctor_set_uint8(x_146, sizeof(void*)*1, x_26);
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
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_26);
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
block_85:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_39 = lean_st_ref_get(x_9, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 3);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*1);
lean_dec(x_42);
x_44 = lean_st_ref_take(x_9, x_41);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_45, 3);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_26);
x_51 = lean_st_ref_set(x_9, x_45, x_47);
lean_dec(x_9);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
x_54 = lean_box(x_37);
x_55 = lean_box(x_43);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_51, 0, x_56);
x_11 = x_51;
goto block_19;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_dec(x_51);
x_58 = lean_box(x_37);
x_59 = lean_box(x_43);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
x_11 = x_61;
goto block_19;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_46, 0);
lean_inc(x_62);
lean_dec(x_46);
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_26);
lean_ctor_set(x_45, 3, x_63);
x_64 = lean_st_ref_set(x_9, x_45, x_47);
lean_dec(x_9);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(x_37);
x_68 = lean_box(x_43);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
if (lean_is_scalar(x_66)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_66;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
x_11 = x_70;
goto block_19;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_71 = lean_ctor_get(x_45, 0);
x_72 = lean_ctor_get(x_45, 1);
x_73 = lean_ctor_get(x_45, 2);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_45);
x_74 = lean_ctor_get(x_46, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_75 = x_46;
} else {
 lean_dec_ref(x_46);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 1, 1);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_26);
x_77 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_72);
lean_ctor_set(x_77, 2, x_73);
lean_ctor_set(x_77, 3, x_76);
x_78 = lean_st_ref_set(x_9, x_77, x_47);
lean_dec(x_9);
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
x_81 = lean_box(x_37);
x_82 = lean_box(x_43);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
if (lean_is_scalar(x_80)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_80;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_79);
x_11 = x_84;
goto block_19;
}
}
}
else
{
lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; uint8_t x_194; lean_object* x_195; 
x_162 = lean_ctor_get(x_29, 0);
lean_inc(x_162);
lean_dec(x_29);
x_163 = 0;
x_164 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*1, x_163);
lean_ctor_set(x_28, 3, x_164);
x_165 = lean_st_ref_set(x_9, x_28, x_30);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
x_194 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_195 = l_Lean_Meta_commitWhen___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_1, x_2, x_194, x_6, x_7, x_8, x_9, x_166);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_226 = lean_st_ref_get(x_9, x_197);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_227, 3);
lean_inc(x_228);
lean_dec(x_227);
x_229 = lean_ctor_get_uint8(x_228, sizeof(void*)*1);
lean_dec(x_228);
if (x_229 == 0)
{
lean_object* x_230; 
x_230 = lean_ctor_get(x_226, 1);
lean_inc(x_230);
lean_dec(x_226);
x_198 = x_163;
x_199 = x_230;
goto block_225;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_231 = lean_ctor_get(x_226, 1);
lean_inc(x_231);
lean_dec(x_226);
x_232 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_233 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_232, x_6, x_7, x_8, x_9, x_231);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_unbox(x_234);
lean_dec(x_234);
x_198 = x_236;
x_199 = x_235;
goto block_225;
}
block_225:
{
if (x_198 == 0)
{
uint8_t x_200; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_200 = lean_unbox(x_196);
lean_dec(x_196);
x_167 = x_200;
x_168 = x_199;
goto block_193;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_201 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_201, 0, x_1);
x_202 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_203 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
x_204 = l_Lean_Meta_isLevelDefEqAux___closed__7;
x_205 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_206, 0, x_2);
x_207 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = l_Lean_Meta_isLevelDefEq___rarg___lambda__1___closed__2;
x_209 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_unbox(x_196);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_211 = l_Lean_Meta_isLevelDefEq___rarg___lambda__1___closed__4;
x_212 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_202);
x_214 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_215 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_214, x_213, x_6, x_7, x_8, x_9, x_199);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_unbox(x_196);
lean_dec(x_196);
x_167 = x_217;
x_168 = x_216;
goto block_193;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_218 = l_Lean_Meta_isLevelDefEq___rarg___lambda__1___closed__6;
x_219 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_219, 0, x_209);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_202);
x_221 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_222 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_221, x_220, x_6, x_7, x_8, x_9, x_199);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_unbox(x_196);
lean_dec(x_196);
x_167 = x_224;
x_168 = x_223;
goto block_193;
}
}
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_237 = lean_ctor_get(x_195, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_195, 1);
lean_inc(x_238);
lean_dec(x_195);
x_239 = lean_st_ref_get(x_9, x_238);
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
x_241 = lean_st_ref_take(x_9, x_240);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_242, 3);
lean_inc(x_243);
x_244 = lean_ctor_get(x_241, 1);
lean_inc(x_244);
lean_dec(x_241);
x_245 = lean_ctor_get(x_242, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_242, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_242, 2);
lean_inc(x_247);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 lean_ctor_release(x_242, 2);
 lean_ctor_release(x_242, 3);
 x_248 = x_242;
} else {
 lean_dec_ref(x_242);
 x_248 = lean_box(0);
}
x_249 = lean_ctor_get(x_243, 0);
lean_inc(x_249);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 x_250 = x_243;
} else {
 lean_dec_ref(x_243);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(0, 1, 1);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set_uint8(x_251, sizeof(void*)*1, x_26);
if (lean_is_scalar(x_248)) {
 x_252 = lean_alloc_ctor(0, 4, 0);
} else {
 x_252 = x_248;
}
lean_ctor_set(x_252, 0, x_245);
lean_ctor_set(x_252, 1, x_246);
lean_ctor_set(x_252, 2, x_247);
lean_ctor_set(x_252, 3, x_251);
x_253 = lean_st_ref_set(x_9, x_252, x_244);
lean_dec(x_9);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_255 = x_253;
} else {
 lean_dec_ref(x_253);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
 lean_ctor_set_tag(x_256, 1);
}
lean_ctor_set(x_256, 0, x_237);
lean_ctor_set(x_256, 1, x_254);
return x_256;
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
lean_ctor_set_uint8(x_184, sizeof(void*)*1, x_26);
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
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; uint8_t x_294; lean_object* x_295; 
x_257 = lean_ctor_get(x_28, 0);
x_258 = lean_ctor_get(x_28, 1);
x_259 = lean_ctor_get(x_28, 2);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_28);
x_260 = lean_ctor_get(x_29, 0);
lean_inc(x_260);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_261 = x_29;
} else {
 lean_dec_ref(x_29);
 x_261 = lean_box(0);
}
x_262 = 0;
if (lean_is_scalar(x_261)) {
 x_263 = lean_alloc_ctor(0, 1, 1);
} else {
 x_263 = x_261;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set_uint8(x_263, sizeof(void*)*1, x_262);
x_264 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_264, 0, x_257);
lean_ctor_set(x_264, 1, x_258);
lean_ctor_set(x_264, 2, x_259);
lean_ctor_set(x_264, 3, x_263);
x_265 = lean_st_ref_set(x_9, x_264, x_30);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
lean_dec(x_265);
x_294 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_295 = l_Lean_Meta_commitWhen___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_1, x_2, x_294, x_6, x_7, x_8, x_9, x_266);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; uint8_t x_298; lean_object* x_299; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_326 = lean_st_ref_get(x_9, x_297);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_327, 3);
lean_inc(x_328);
lean_dec(x_327);
x_329 = lean_ctor_get_uint8(x_328, sizeof(void*)*1);
lean_dec(x_328);
if (x_329 == 0)
{
lean_object* x_330; 
x_330 = lean_ctor_get(x_326, 1);
lean_inc(x_330);
lean_dec(x_326);
x_298 = x_262;
x_299 = x_330;
goto block_325;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; 
x_331 = lean_ctor_get(x_326, 1);
lean_inc(x_331);
lean_dec(x_326);
x_332 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_333 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_332, x_6, x_7, x_8, x_9, x_331);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
lean_dec(x_333);
x_336 = lean_unbox(x_334);
lean_dec(x_334);
x_298 = x_336;
x_299 = x_335;
goto block_325;
}
block_325:
{
if (x_298 == 0)
{
uint8_t x_300; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_300 = lean_unbox(x_296);
lean_dec(x_296);
x_267 = x_300;
x_268 = x_299;
goto block_293;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; 
x_301 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_301, 0, x_1);
x_302 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_303 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_301);
x_304 = l_Lean_Meta_isLevelDefEqAux___closed__7;
x_305 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
x_306 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_306, 0, x_2);
x_307 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
x_308 = l_Lean_Meta_isLevelDefEq___rarg___lambda__1___closed__2;
x_309 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_unbox(x_296);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_311 = l_Lean_Meta_isLevelDefEq___rarg___lambda__1___closed__4;
x_312 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_302);
x_314 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_315 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_314, x_313, x_6, x_7, x_8, x_9, x_299);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
lean_dec(x_315);
x_317 = lean_unbox(x_296);
lean_dec(x_296);
x_267 = x_317;
x_268 = x_316;
goto block_293;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_318 = l_Lean_Meta_isLevelDefEq___rarg___lambda__1___closed__6;
x_319 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_319, 0, x_309);
lean_ctor_set(x_319, 1, x_318);
x_320 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_302);
x_321 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_322 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_321, x_320, x_6, x_7, x_8, x_9, x_299);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_323 = lean_ctor_get(x_322, 1);
lean_inc(x_323);
lean_dec(x_322);
x_324 = lean_unbox(x_296);
lean_dec(x_296);
x_267 = x_324;
x_268 = x_323;
goto block_293;
}
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_337 = lean_ctor_get(x_295, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_295, 1);
lean_inc(x_338);
lean_dec(x_295);
x_339 = lean_st_ref_get(x_9, x_338);
x_340 = lean_ctor_get(x_339, 1);
lean_inc(x_340);
lean_dec(x_339);
x_341 = lean_st_ref_take(x_9, x_340);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_342, 3);
lean_inc(x_343);
x_344 = lean_ctor_get(x_341, 1);
lean_inc(x_344);
lean_dec(x_341);
x_345 = lean_ctor_get(x_342, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_342, 1);
lean_inc(x_346);
x_347 = lean_ctor_get(x_342, 2);
lean_inc(x_347);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 lean_ctor_release(x_342, 2);
 lean_ctor_release(x_342, 3);
 x_348 = x_342;
} else {
 lean_dec_ref(x_342);
 x_348 = lean_box(0);
}
x_349 = lean_ctor_get(x_343, 0);
lean_inc(x_349);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 x_350 = x_343;
} else {
 lean_dec_ref(x_343);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(0, 1, 1);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set_uint8(x_351, sizeof(void*)*1, x_26);
if (lean_is_scalar(x_348)) {
 x_352 = lean_alloc_ctor(0, 4, 0);
} else {
 x_352 = x_348;
}
lean_ctor_set(x_352, 0, x_345);
lean_ctor_set(x_352, 1, x_346);
lean_ctor_set(x_352, 2, x_347);
lean_ctor_set(x_352, 3, x_351);
x_353 = lean_st_ref_set(x_9, x_352, x_344);
lean_dec(x_9);
x_354 = lean_ctor_get(x_353, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_355 = x_353;
} else {
 lean_dec_ref(x_353);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_356 = x_355;
 lean_ctor_set_tag(x_356, 1);
}
lean_ctor_set(x_356, 0, x_337);
lean_ctor_set(x_356, 1, x_354);
return x_356;
}
block_293:
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_269 = lean_st_ref_get(x_9, x_268);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = lean_ctor_get(x_270, 3);
lean_inc(x_272);
lean_dec(x_270);
x_273 = lean_ctor_get_uint8(x_272, sizeof(void*)*1);
lean_dec(x_272);
x_274 = lean_st_ref_take(x_9, x_271);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_275, 3);
lean_inc(x_276);
x_277 = lean_ctor_get(x_274, 1);
lean_inc(x_277);
lean_dec(x_274);
x_278 = lean_ctor_get(x_275, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_275, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_275, 2);
lean_inc(x_280);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 lean_ctor_release(x_275, 2);
 lean_ctor_release(x_275, 3);
 x_281 = x_275;
} else {
 lean_dec_ref(x_275);
 x_281 = lean_box(0);
}
x_282 = lean_ctor_get(x_276, 0);
lean_inc(x_282);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 x_283 = x_276;
} else {
 lean_dec_ref(x_276);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(0, 1, 1);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set_uint8(x_284, sizeof(void*)*1, x_26);
if (lean_is_scalar(x_281)) {
 x_285 = lean_alloc_ctor(0, 4, 0);
} else {
 x_285 = x_281;
}
lean_ctor_set(x_285, 0, x_278);
lean_ctor_set(x_285, 1, x_279);
lean_ctor_set(x_285, 2, x_280);
lean_ctor_set(x_285, 3, x_284);
x_286 = lean_st_ref_set(x_9, x_285, x_277);
lean_dec(x_9);
x_287 = lean_ctor_get(x_286, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_288 = x_286;
} else {
 lean_dec_ref(x_286);
 x_288 = lean_box(0);
}
x_289 = lean_box(x_267);
x_290 = lean_box(x_273);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
if (lean_is_scalar(x_288)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_288;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_287);
x_11 = x_292;
goto block_19;
}
}
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; lean_object* x_362; uint8_t x_372; lean_object* x_373; 
x_357 = lean_ctor_get(x_8, 3);
lean_inc(x_357);
x_358 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed___spec__1___rarg(x_9, x_21);
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
x_372 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_373 = l_Lean_Meta_commitWhen___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_1, x_2, x_372, x_6, x_7, x_8, x_9, x_360);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; uint8_t x_376; lean_object* x_377; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_404 = lean_st_ref_get(x_9, x_375);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_405, 3);
lean_inc(x_406);
lean_dec(x_405);
x_407 = lean_ctor_get_uint8(x_406, sizeof(void*)*1);
lean_dec(x_406);
if (x_407 == 0)
{
lean_object* x_408; uint8_t x_409; 
x_408 = lean_ctor_get(x_404, 1);
lean_inc(x_408);
lean_dec(x_404);
x_409 = 0;
x_376 = x_409;
x_377 = x_408;
goto block_403;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_410 = lean_ctor_get(x_404, 1);
lean_inc(x_410);
lean_dec(x_404);
x_411 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_412 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_411, x_6, x_7, x_8, x_9, x_410);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec(x_412);
x_415 = lean_unbox(x_413);
lean_dec(x_413);
x_376 = x_415;
x_377 = x_414;
goto block_403;
}
block_403:
{
if (x_376 == 0)
{
uint8_t x_378; 
lean_dec(x_2);
lean_dec(x_1);
x_378 = lean_unbox(x_374);
lean_dec(x_374);
x_361 = x_378;
x_362 = x_377;
goto block_371;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; 
x_379 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_379, 0, x_1);
x_380 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_381 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_379);
x_382 = l_Lean_Meta_isLevelDefEqAux___closed__7;
x_383 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
x_384 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_384, 0, x_2);
x_385 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
x_386 = l_Lean_Meta_isLevelDefEq___rarg___lambda__1___closed__2;
x_387 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
x_388 = lean_unbox(x_374);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; 
x_389 = l_Lean_Meta_isLevelDefEq___rarg___lambda__1___closed__4;
x_390 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_390, 0, x_387);
lean_ctor_set(x_390, 1, x_389);
x_391 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_380);
x_392 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_393 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_392, x_391, x_6, x_7, x_8, x_9, x_377);
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
lean_dec(x_393);
x_395 = lean_unbox(x_374);
lean_dec(x_374);
x_361 = x_395;
x_362 = x_394;
goto block_371;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; 
x_396 = l_Lean_Meta_isLevelDefEq___rarg___lambda__1___closed__6;
x_397 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_397, 0, x_387);
lean_ctor_set(x_397, 1, x_396);
x_398 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_380);
x_399 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_400 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_399, x_398, x_6, x_7, x_8, x_9, x_377);
x_401 = lean_ctor_get(x_400, 1);
lean_inc(x_401);
lean_dec(x_400);
x_402 = lean_unbox(x_374);
lean_dec(x_374);
x_361 = x_402;
x_362 = x_401;
goto block_371;
}
}
}
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; 
lean_dec(x_2);
lean_dec(x_1);
x_416 = lean_ctor_get(x_373, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_373, 1);
lean_inc(x_417);
lean_dec(x_373);
x_418 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_419 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed___spec__2(x_359, x_418, x_357, x_6, x_7, x_8, x_9, x_417);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_420 = !lean_is_exclusive(x_419);
if (x_420 == 0)
{
lean_object* x_421; 
x_421 = lean_ctor_get(x_419, 0);
lean_dec(x_421);
lean_ctor_set_tag(x_419, 1);
lean_ctor_set(x_419, 0, x_416);
return x_419;
}
else
{
lean_object* x_422; lean_object* x_423; 
x_422 = lean_ctor_get(x_419, 1);
lean_inc(x_422);
lean_dec(x_419);
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_416);
lean_ctor_set(x_423, 1, x_422);
return x_423;
}
}
block_371:
{
lean_object* x_363; lean_object* x_364; uint8_t x_365; 
x_363 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_364 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed___spec__2(x_359, x_363, x_357, x_6, x_7, x_8, x_9, x_362);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_365 = !lean_is_exclusive(x_364);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; 
x_366 = lean_ctor_get(x_364, 0);
lean_dec(x_366);
x_367 = lean_box(x_361);
lean_ctor_set(x_364, 0, x_367);
return x_364;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_364, 1);
lean_inc(x_368);
lean_dec(x_364);
x_369 = lean_box(x_361);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_368);
return x_370;
}
}
}
}
}
}
lean_object* l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834____closed__1;
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
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_1, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get_uint8(x_11, sizeof(void*)*9);
x_14 = lean_ctor_get(x_11, 5);
lean_inc(x_14);
x_15 = l_Array_isEmpty___rarg(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
if (x_13 == 0)
{
uint8_t x_17; 
x_17 = lean_ctor_get_uint8(x_11, sizeof(void*)*9 + 2);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_11, 8);
lean_inc(x_18);
x_19 = l_Array_isEmpty___rarg(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_free_object(x_9);
x_20 = lean_st_ref_take(x_1, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_24 = 1;
lean_ctor_set_uint8(x_21, sizeof(void*)*9 + 2, x_24);
x_25 = lean_st_ref_set(x_1, x_21, x_22);
x_26 = lean_ctor_get(x_11, 4);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_120; lean_object* x_121; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_34 = x_25;
} else {
 lean_dec_ref(x_25);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_ctor_get(x_11, 2);
lean_inc(x_36);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_List_lengthAux___rarg(x_36, x_37);
lean_dec(x_36);
x_143 = lean_st_ref_get(x_7, x_33);
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
x_120 = x_148;
x_121 = x_147;
goto block_142;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_149 = lean_ctor_get(x_143, 1);
lean_inc(x_149);
lean_dec(x_143);
x_150 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_151 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__7(x_150, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_149);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_unbox(x_152);
lean_dec(x_152);
x_120 = x_154;
x_121 = x_153;
goto block_142;
}
block_119:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_11, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_dec(x_11);
x_42 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody(x_38, x_40, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_35);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_34;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l_Lean_Expr_hasLooseBVars(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_box(0);
lean_inc(x_45);
lean_inc(x_18);
x_48 = l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_18, x_45, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_45);
lean_dec(x_35);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_34;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_39);
return x_50;
}
else
{
lean_object* x_51; 
lean_dec(x_48);
lean_inc(x_45);
x_51 = l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_18, x_45, x_47);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_34);
x_52 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_45);
x_53 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(x_45, x_52, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_39);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_93 = lean_st_ref_get(x_7, x_56);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 3);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_ctor_get_uint8(x_95, sizeof(void*)*1);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
x_98 = 0;
x_57 = x_98;
x_58 = x_97;
goto block_92;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
lean_dec(x_93);
x_100 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_101 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__7(x_100, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_99);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_unbox(x_102);
lean_dec(x_102);
x_57 = x_104;
x_58 = x_103;
goto block_92;
}
block_92:
{
if (x_57 == 0)
{
lean_object* x_59; 
x_59 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_35, x_45, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_58);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
x_62 = lean_box(0);
lean_ctor_set(x_59, 0, x_62);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_59);
if (x_66 == 0)
{
return x_59;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_59, 0);
x_68 = lean_ctor_get(x_59, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_59);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_inc(x_35);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_35);
x_71 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Meta_isLevelDefEqAux___closed__7;
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_inc(x_45);
x_75 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_75, 0, x_45);
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_71);
x_78 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_79 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__6(x_78, x_77, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_58);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_35, x_45, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_80);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
x_84 = lean_box(0);
lean_ctor_set(x_81, 0, x_84);
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_81);
if (x_88 == 0)
{
return x_81;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_81, 0);
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_81);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_45);
lean_dec(x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_53);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_53, 0);
lean_dec(x_106);
x_107 = lean_box(0);
lean_ctor_set(x_53, 0, x_107);
return x_53;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_53, 1);
lean_inc(x_108);
lean_dec(x_53);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_45);
lean_dec(x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_53);
if (x_111 == 0)
{
return x_53;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_53, 0);
x_113 = lean_ctor_get(x_53, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_53);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_51);
lean_dec(x_45);
lean_dec(x_35);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_34;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_39);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_45);
lean_dec(x_35);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_34;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_39);
return x_118;
}
}
}
block_142:
{
if (x_120 == 0)
{
lean_dec(x_14);
x_39 = x_121;
goto block_119;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_122 = lean_array_get_size(x_14);
lean_dec(x_14);
x_123 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_122);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5;
x_126 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7;
x_128 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
lean_inc(x_38);
x_129 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_38);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_130);
x_132 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9;
x_133 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_ctor_get(x_11, 1);
lean_inc(x_134);
x_135 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_138 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_140 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__6(x_139, x_138, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_121);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_39 = x_141;
goto block_119;
}
}
}
}
else
{
uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_155 = lean_ctor_get_uint8(x_21, sizeof(void*)*9);
x_156 = lean_ctor_get(x_21, 0);
x_157 = lean_ctor_get(x_21, 1);
x_158 = lean_ctor_get(x_21, 2);
x_159 = lean_ctor_get(x_21, 3);
x_160 = lean_ctor_get_uint8(x_21, sizeof(void*)*9 + 1);
x_161 = lean_ctor_get(x_21, 4);
x_162 = lean_ctor_get(x_21, 5);
x_163 = lean_ctor_get(x_21, 6);
x_164 = lean_ctor_get(x_21, 7);
x_165 = lean_ctor_get(x_21, 8);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_21);
x_166 = 1;
x_167 = lean_alloc_ctor(0, 9, 3);
lean_ctor_set(x_167, 0, x_156);
lean_ctor_set(x_167, 1, x_157);
lean_ctor_set(x_167, 2, x_158);
lean_ctor_set(x_167, 3, x_159);
lean_ctor_set(x_167, 4, x_161);
lean_ctor_set(x_167, 5, x_162);
lean_ctor_set(x_167, 6, x_163);
lean_ctor_set(x_167, 7, x_164);
lean_ctor_set(x_167, 8, x_165);
lean_ctor_set_uint8(x_167, sizeof(void*)*9, x_155);
lean_ctor_set_uint8(x_167, sizeof(void*)*9 + 1, x_160);
lean_ctor_set_uint8(x_167, sizeof(void*)*9 + 2, x_166);
x_168 = lean_st_ref_set(x_1, x_167, x_22);
x_169 = lean_ctor_get(x_11, 4);
lean_inc(x_169);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
x_172 = lean_box(0);
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_170);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_255; lean_object* x_256; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_174 = lean_ctor_get(x_168, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_175 = x_168;
} else {
 lean_dec_ref(x_168);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_169, 0);
lean_inc(x_176);
lean_dec(x_169);
x_177 = lean_ctor_get(x_11, 2);
lean_inc(x_177);
x_178 = lean_unsigned_to_nat(0u);
x_179 = l_List_lengthAux___rarg(x_177, x_178);
lean_dec(x_177);
x_278 = lean_st_ref_get(x_7, x_174);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_279, 3);
lean_inc(x_280);
lean_dec(x_279);
x_281 = lean_ctor_get_uint8(x_280, sizeof(void*)*1);
lean_dec(x_280);
if (x_281 == 0)
{
lean_object* x_282; uint8_t x_283; 
x_282 = lean_ctor_get(x_278, 1);
lean_inc(x_282);
lean_dec(x_278);
x_283 = 0;
x_255 = x_283;
x_256 = x_282;
goto block_277;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_284 = lean_ctor_get(x_278, 1);
lean_inc(x_284);
lean_dec(x_278);
x_285 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_286 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__7(x_285, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_284);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_unbox(x_287);
lean_dec(x_287);
x_255 = x_289;
x_256 = x_288;
goto block_277;
}
block_254:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_11, 3);
lean_inc(x_181);
x_182 = lean_ctor_get(x_11, 1);
lean_inc(x_182);
lean_dec(x_11);
x_183 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody(x_179, x_181, x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_176);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_184 = lean_box(0);
if (lean_is_scalar(x_175)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_175;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_180);
return x_185;
}
else
{
lean_object* x_186; uint8_t x_187; 
x_186 = lean_ctor_get(x_183, 0);
lean_inc(x_186);
lean_dec(x_183);
x_187 = l_Lean_Expr_hasLooseBVars(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_box(0);
lean_inc(x_186);
lean_inc(x_18);
x_189 = l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_18, x_186, x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_186);
lean_dec(x_176);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_190 = lean_box(0);
if (lean_is_scalar(x_175)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_175;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_180);
return x_191;
}
else
{
lean_object* x_192; 
lean_dec(x_189);
lean_inc(x_186);
x_192 = l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_18, x_186, x_188);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_175);
x_193 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_186);
x_194 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(x_186, x_193, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_180);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; uint8_t x_196; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_unbox(x_195);
lean_dec(x_195);
if (x_196 == 0)
{
lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
lean_dec(x_194);
x_230 = lean_st_ref_get(x_7, x_197);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_231, 3);
lean_inc(x_232);
lean_dec(x_231);
x_233 = lean_ctor_get_uint8(x_232, sizeof(void*)*1);
lean_dec(x_232);
if (x_233 == 0)
{
lean_object* x_234; uint8_t x_235; 
x_234 = lean_ctor_get(x_230, 1);
lean_inc(x_234);
lean_dec(x_230);
x_235 = 0;
x_198 = x_235;
x_199 = x_234;
goto block_229;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_236 = lean_ctor_get(x_230, 1);
lean_inc(x_236);
lean_dec(x_230);
x_237 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_238 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__7(x_237, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_236);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_unbox(x_239);
lean_dec(x_239);
x_198 = x_241;
x_199 = x_240;
goto block_229;
}
block_229:
{
if (x_198 == 0)
{
lean_object* x_200; 
x_200 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_176, x_186, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_199);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_202 = x_200;
} else {
 lean_dec_ref(x_200);
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
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_200, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_200, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_207 = x_200;
} else {
 lean_dec_ref(x_200);
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
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_inc(x_176);
x_209 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_209, 0, x_176);
x_210 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_211 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
x_212 = l_Lean_Meta_isLevelDefEqAux___closed__7;
x_213 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
lean_inc(x_186);
x_214 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_214, 0, x_186);
x_215 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_210);
x_217 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_218 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__6(x_217, x_216, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_199);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_220 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_176, x_186, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_219);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_222 = x_220;
} else {
 lean_dec_ref(x_220);
 x_222 = lean_box(0);
}
x_223 = lean_box(0);
if (lean_is_scalar(x_222)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_222;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_221);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_220, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_220, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_227 = x_220;
} else {
 lean_dec_ref(x_220);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_186);
lean_dec(x_176);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_242 = lean_ctor_get(x_194, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_243 = x_194;
} else {
 lean_dec_ref(x_194);
 x_243 = lean_box(0);
}
x_244 = lean_box(0);
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_242);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_186);
lean_dec(x_176);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_246 = lean_ctor_get(x_194, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_194, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_248 = x_194;
} else {
 lean_dec_ref(x_194);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_192);
lean_dec(x_186);
lean_dec(x_176);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_250 = lean_box(0);
if (lean_is_scalar(x_175)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_175;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_180);
return x_251;
}
}
}
else
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_186);
lean_dec(x_176);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_252 = lean_box(0);
if (lean_is_scalar(x_175)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_175;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_180);
return x_253;
}
}
}
block_277:
{
if (x_255 == 0)
{
lean_dec(x_14);
x_180 = x_256;
goto block_254;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_257 = lean_array_get_size(x_14);
lean_dec(x_14);
x_258 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_257);
x_259 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_259, 0, x_258);
x_260 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5;
x_261 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_259);
x_262 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7;
x_263 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
lean_inc(x_179);
x_264 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_179);
x_265 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_265, 0, x_264);
x_266 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_265);
x_267 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9;
x_268 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_ctor_get(x_11, 1);
lean_inc(x_269);
x_270 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_270, 0, x_269);
x_271 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_270);
x_272 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_273 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
x_274 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_275 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__6(x_274, x_273, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_256);
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
lean_dec(x_275);
x_180 = x_276;
goto block_254;
}
}
}
}
}
else
{
lean_object* x_290; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_290 = lean_box(0);
lean_ctor_set(x_9, 0, x_290);
return x_9;
}
}
else
{
lean_object* x_291; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_291 = lean_box(0);
lean_ctor_set(x_9, 0, x_291);
return x_9;
}
}
else
{
lean_object* x_292; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_292 = lean_box(0);
lean_ctor_set(x_9, 0, x_292);
return x_9;
}
}
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; uint8_t x_297; 
x_293 = lean_ctor_get(x_9, 0);
x_294 = lean_ctor_get(x_9, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_9);
x_295 = lean_ctor_get_uint8(x_293, sizeof(void*)*9);
x_296 = lean_ctor_get(x_293, 5);
lean_inc(x_296);
x_297 = l_Array_isEmpty___rarg(x_296);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_296);
lean_dec(x_293);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_298 = lean_box(0);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_294);
return x_299;
}
else
{
if (x_295 == 0)
{
uint8_t x_300; 
x_300 = lean_ctor_get_uint8(x_293, sizeof(void*)*9 + 2);
if (x_300 == 0)
{
lean_object* x_301; uint8_t x_302; 
x_301 = lean_ctor_get(x_293, 8);
lean_inc(x_301);
x_302 = l_Array_isEmpty___rarg(x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_303 = lean_st_ref_take(x_1, x_294);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = lean_ctor_get_uint8(x_304, sizeof(void*)*9);
x_307 = lean_ctor_get(x_304, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_304, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_304, 2);
lean_inc(x_309);
x_310 = lean_ctor_get(x_304, 3);
lean_inc(x_310);
x_311 = lean_ctor_get_uint8(x_304, sizeof(void*)*9 + 1);
x_312 = lean_ctor_get(x_304, 4);
lean_inc(x_312);
x_313 = lean_ctor_get(x_304, 5);
lean_inc(x_313);
x_314 = lean_ctor_get(x_304, 6);
lean_inc(x_314);
x_315 = lean_ctor_get(x_304, 7);
lean_inc(x_315);
x_316 = lean_ctor_get(x_304, 8);
lean_inc(x_316);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 lean_ctor_release(x_304, 2);
 lean_ctor_release(x_304, 3);
 lean_ctor_release(x_304, 4);
 lean_ctor_release(x_304, 5);
 lean_ctor_release(x_304, 6);
 lean_ctor_release(x_304, 7);
 lean_ctor_release(x_304, 8);
 x_317 = x_304;
} else {
 lean_dec_ref(x_304);
 x_317 = lean_box(0);
}
x_318 = 1;
if (lean_is_scalar(x_317)) {
 x_319 = lean_alloc_ctor(0, 9, 3);
} else {
 x_319 = x_317;
}
lean_ctor_set(x_319, 0, x_307);
lean_ctor_set(x_319, 1, x_308);
lean_ctor_set(x_319, 2, x_309);
lean_ctor_set(x_319, 3, x_310);
lean_ctor_set(x_319, 4, x_312);
lean_ctor_set(x_319, 5, x_313);
lean_ctor_set(x_319, 6, x_314);
lean_ctor_set(x_319, 7, x_315);
lean_ctor_set(x_319, 8, x_316);
lean_ctor_set_uint8(x_319, sizeof(void*)*9, x_306);
lean_ctor_set_uint8(x_319, sizeof(void*)*9 + 1, x_311);
lean_ctor_set_uint8(x_319, sizeof(void*)*9 + 2, x_318);
x_320 = lean_st_ref_set(x_1, x_319, x_305);
x_321 = lean_ctor_get(x_293, 4);
lean_inc(x_321);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_301);
lean_dec(x_296);
lean_dec(x_293);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_324 = lean_box(0);
if (lean_is_scalar(x_323)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_323;
}
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_322);
return x_325;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_407; lean_object* x_408; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; 
x_326 = lean_ctor_get(x_320, 1);
lean_inc(x_326);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_327 = x_320;
} else {
 lean_dec_ref(x_320);
 x_327 = lean_box(0);
}
x_328 = lean_ctor_get(x_321, 0);
lean_inc(x_328);
lean_dec(x_321);
x_329 = lean_ctor_get(x_293, 2);
lean_inc(x_329);
x_330 = lean_unsigned_to_nat(0u);
x_331 = l_List_lengthAux___rarg(x_329, x_330);
lean_dec(x_329);
x_430 = lean_st_ref_get(x_7, x_326);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_431, 3);
lean_inc(x_432);
lean_dec(x_431);
x_433 = lean_ctor_get_uint8(x_432, sizeof(void*)*1);
lean_dec(x_432);
if (x_433 == 0)
{
lean_object* x_434; uint8_t x_435; 
x_434 = lean_ctor_get(x_430, 1);
lean_inc(x_434);
lean_dec(x_430);
x_435 = 0;
x_407 = x_435;
x_408 = x_434;
goto block_429;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; 
x_436 = lean_ctor_get(x_430, 1);
lean_inc(x_436);
lean_dec(x_430);
x_437 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_438 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__7(x_437, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_436);
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
lean_dec(x_438);
x_441 = lean_unbox(x_439);
lean_dec(x_439);
x_407 = x_441;
x_408 = x_440;
goto block_429;
}
block_406:
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_293, 3);
lean_inc(x_333);
x_334 = lean_ctor_get(x_293, 1);
lean_inc(x_334);
lean_dec(x_293);
x_335 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody(x_331, x_333, x_334);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_328);
lean_dec(x_301);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_336 = lean_box(0);
if (lean_is_scalar(x_327)) {
 x_337 = lean_alloc_ctor(0, 2, 0);
} else {
 x_337 = x_327;
}
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_332);
return x_337;
}
else
{
lean_object* x_338; uint8_t x_339; 
x_338 = lean_ctor_get(x_335, 0);
lean_inc(x_338);
lean_dec(x_335);
x_339 = l_Lean_Expr_hasLooseBVars(x_338);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; 
x_340 = lean_box(0);
lean_inc(x_338);
lean_inc(x_301);
x_341 = l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_301, x_338, x_340);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; 
lean_dec(x_338);
lean_dec(x_328);
lean_dec(x_301);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_342 = lean_box(0);
if (lean_is_scalar(x_327)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_327;
}
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_332);
return x_343;
}
else
{
lean_object* x_344; 
lean_dec(x_341);
lean_inc(x_338);
x_344 = l_Lean_FindMVar_main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_301, x_338, x_340);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; 
lean_dec(x_327);
x_345 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_338);
x_346 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(x_338, x_345, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_332);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; uint8_t x_348; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_unbox(x_347);
lean_dec(x_347);
if (x_348 == 0)
{
lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_349 = lean_ctor_get(x_346, 1);
lean_inc(x_349);
lean_dec(x_346);
x_382 = lean_st_ref_get(x_7, x_349);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_383, 3);
lean_inc(x_384);
lean_dec(x_383);
x_385 = lean_ctor_get_uint8(x_384, sizeof(void*)*1);
lean_dec(x_384);
if (x_385 == 0)
{
lean_object* x_386; uint8_t x_387; 
x_386 = lean_ctor_get(x_382, 1);
lean_inc(x_386);
lean_dec(x_382);
x_387 = 0;
x_350 = x_387;
x_351 = x_386;
goto block_381;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_393; 
x_388 = lean_ctor_get(x_382, 1);
lean_inc(x_388);
lean_dec(x_382);
x_389 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_390 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__7(x_389, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_388);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_393 = lean_unbox(x_391);
lean_dec(x_391);
x_350 = x_393;
x_351 = x_392;
goto block_381;
}
block_381:
{
if (x_350 == 0)
{
lean_object* x_352; 
x_352 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_328, x_338, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_351);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_354 = x_352;
} else {
 lean_dec_ref(x_352);
 x_354 = lean_box(0);
}
x_355 = lean_box(0);
if (lean_is_scalar(x_354)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_354;
}
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_353);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_357 = lean_ctor_get(x_352, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_352, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_359 = x_352;
} else {
 lean_dec_ref(x_352);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(1, 2, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_358);
return x_360;
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_inc(x_328);
x_361 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_361, 0, x_328);
x_362 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_363 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_361);
x_364 = l_Lean_Meta_isLevelDefEqAux___closed__7;
x_365 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
lean_inc(x_338);
x_366 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_366, 0, x_338);
x_367 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
x_368 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_362);
x_369 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_370 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__6(x_369, x_368, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_351);
x_371 = lean_ctor_get(x_370, 1);
lean_inc(x_371);
lean_dec(x_370);
x_372 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_328, x_338, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_371);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_374 = x_372;
} else {
 lean_dec_ref(x_372);
 x_374 = lean_box(0);
}
x_375 = lean_box(0);
if (lean_is_scalar(x_374)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_374;
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_373);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_377 = lean_ctor_get(x_372, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_372, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_379 = x_372;
} else {
 lean_dec_ref(x_372);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(1, 2, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_377);
lean_ctor_set(x_380, 1, x_378);
return x_380;
}
}
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_338);
lean_dec(x_328);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_394 = lean_ctor_get(x_346, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_395 = x_346;
} else {
 lean_dec_ref(x_346);
 x_395 = lean_box(0);
}
x_396 = lean_box(0);
if (lean_is_scalar(x_395)) {
 x_397 = lean_alloc_ctor(0, 2, 0);
} else {
 x_397 = x_395;
}
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_394);
return x_397;
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_338);
lean_dec(x_328);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_398 = lean_ctor_get(x_346, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_346, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_400 = x_346;
} else {
 lean_dec_ref(x_346);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_398);
lean_ctor_set(x_401, 1, x_399);
return x_401;
}
}
else
{
lean_object* x_402; lean_object* x_403; 
lean_dec(x_344);
lean_dec(x_338);
lean_dec(x_328);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_402 = lean_box(0);
if (lean_is_scalar(x_327)) {
 x_403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_403 = x_327;
}
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_332);
return x_403;
}
}
}
else
{
lean_object* x_404; lean_object* x_405; 
lean_dec(x_338);
lean_dec(x_328);
lean_dec(x_301);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_404 = lean_box(0);
if (lean_is_scalar(x_327)) {
 x_405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_405 = x_327;
}
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_332);
return x_405;
}
}
}
block_429:
{
if (x_407 == 0)
{
lean_dec(x_296);
x_332 = x_408;
goto block_406;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_409 = lean_array_get_size(x_296);
lean_dec(x_296);
x_410 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_409);
x_411 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_411, 0, x_410);
x_412 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5;
x_413 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_411);
x_414 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7;
x_415 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
lean_inc(x_331);
x_416 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_331);
x_417 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_417, 0, x_416);
x_418 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_418, 0, x_415);
lean_ctor_set(x_418, 1, x_417);
x_419 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9;
x_420 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
x_421 = lean_ctor_get(x_293, 1);
lean_inc(x_421);
x_422 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_422, 0, x_421);
x_423 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_423, 0, x_420);
lean_ctor_set(x_423, 1, x_422);
x_424 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_425 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
x_426 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_427 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__6(x_426, x_425, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_408);
x_428 = lean_ctor_get(x_427, 1);
lean_inc(x_428);
lean_dec(x_427);
x_332 = x_428;
goto block_406;
}
}
}
}
else
{
lean_object* x_442; lean_object* x_443; 
lean_dec(x_301);
lean_dec(x_296);
lean_dec(x_293);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_442 = lean_box(0);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_294);
return x_443;
}
}
else
{
lean_object* x_444; lean_object* x_445; 
lean_dec(x_296);
lean_dec(x_293);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_444 = lean_box(0);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_294);
return x_445;
}
}
else
{
lean_object* x_446; lean_object* x_447; 
lean_dec(x_296);
lean_dec(x_293);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_446 = lean_box(0);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_294);
return x_447;
}
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
lean_object* l_Lean_Meta_commitWhen___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_commitWhen___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_commitWhen___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_commitWhen___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
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
lean_object* l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* x_14; uint8_t x_62; lean_object* x_63; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_st_ref_get(x_12, x_13);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 3);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_ctor_get_uint8(x_78, sizeof(void*)*1);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
x_81 = 0;
x_62 = x_81;
x_63 = x_80;
goto block_75;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
lean_dec(x_76);
lean_inc(x_2);
x_83 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__7(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_unbox(x_84);
lean_dec(x_84);
x_62 = x_86;
x_63 = x_85;
goto block_75;
}
block_61:
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_st_ref_get(x_12, x_14);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_24 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_18, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(x_4, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
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
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_dec(x_19);
lean_inc(x_2);
x_33 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__7(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_2);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_37 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_18, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_box(0);
x_40 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(x_4, x_39, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_38);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_37);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_dec(x_33);
lean_inc(x_18);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_18);
x_47 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___lambda__3___closed__2;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__6(x_2, x_50, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_45);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_53 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_18, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(x_4, x_55, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_54);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
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
}
}
block_75:
{
if (x_62 == 0)
{
x_14 = x_63;
goto block_61;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_inc(x_4);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_4);
x_65 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__2;
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_checkTypesAndAssign___closed__7;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_3);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_3);
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
lean_inc(x_2);
x_73 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__6(x_2, x_72, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_63);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_14 = x_74;
goto block_61;
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
x_52 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__7(x_51, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_50);
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
x_58 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__6(x_51, x_57, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_56);
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
x_29 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__5(x_27, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_28);
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
x_51 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_44);
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
x_60 = l_Array_iterateMAux___at_Array_append___spec__1___rarg(x_57, x_57, x_58, x_59);
lean_dec(x_57);
x_61 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_299____closed__5;
x_62 = lean_array_push(x_60, x_61);
x_63 = l_Lean_nullKind___closed__2;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_array_push(x_59, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_299____closed__4;
x_68 = lean_array_push(x_67, x_66);
x_69 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_299____closed__29;
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
x_97 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__4___rarg(x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
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
x_21 = l_List_find_x3f___rarg(x_19, x_20);
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
x_35 = lean_ctor_get(x_30, 2);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_17 = l_Lean_Meta_instantiateMVarsImp(x_15, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_42; lean_object* x_43; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
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
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
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
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
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
x_44 = l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__2(x_5);
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
x_56 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
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
x_74 = !lean_is_exclusive(x_17);
if (x_74 == 0)
{
return x_17;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_17, 0);
x_76 = lean_ctor_get(x_17, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_17);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_14);
if (x_78 == 0)
{
return x_14;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_14, 0);
x_80 = lean_ctor_get(x_14, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_14);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
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
x_11 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
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
lean_object* l_Array_findSomeMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_12 = l_Array_findSomeMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1(x_1, x_3, x_10, x_11);
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
lean_object* l_Array_findSomeMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1(x_1, x_2, x_3, x_4);
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
lean_object* l_Array_forMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
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
x_32 = l_Array_forMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1(x_4, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
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
x_69 = l_Array_forMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1(x_4, x_68, x_5, x_6, x_7, x_8, x_9, x_10, x_67);
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
lean_object* l_Array_forMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("self");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_2);
x_18 = lean_box(0);
x_19 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
x_21 = l_Lean_mkOptionalNode___closed__2;
x_22 = lean_array_push(x_21, x_20);
x_23 = lean_box(0);
x_24 = l_Array_empty___closed__1;
x_25 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_15, x_22, x_24, x_23, x_25, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
lean_dec(x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_1 = x_12;
x_2 = x_27;
x_9 = x_28;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
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
x_19 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
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
lean_object* l_Array_findIdxAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_7, 1);
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
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_4 < x_3;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_1);
x_17 = l_Lean_Elab_Term_throwInvalidNamedArg___rarg(x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_16);
lean_dec(x_15);
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
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, function '");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not have explicit argument with type (");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ...)");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_1);
x_16 = lean_nat_dec_lt(x_6, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
x_17 = lean_array_get_size(x_2);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = lean_box(0);
lean_inc(x_12);
lean_inc(x_8);
lean_inc(x_3);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3(x_3, x_2, x_18, x_19, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_3);
x_24 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__2;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__4;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_28, 0, x_4);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__6;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_31, x_8, x_9, x_10, x_11, x_12, x_13, x_22);
lean_dec(x_12);
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
else
{
uint8_t x_37; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_21);
if (x_37 == 0)
{
return x_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_21, 0);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_21);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_6, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_14);
return x_46;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
x_28 = l_Lean_Expr_isAppOf(x_27, x_5);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_23);
lean_dec(x_7);
x_29 = lean_box(0);
x_30 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1(x_2, x_3, x_4, x_5, x_6, x_8, x_29, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
lean_dec(x_15);
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
lean_dec(x_5);
lean_dec(x_4);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_7);
x_32 = l_Array_insertAt___rarg(x_2, x_8, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_3);
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
x_40 = l_Lean_Expr_isAppOf(x_39, x_5);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_7);
x_41 = lean_box(0);
x_42 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1(x_2, x_3, x_4, x_5, x_6, x_8, x_41, x_10, x_11, x_12, x_13, x_14, x_15, x_38);
lean_dec(x_15);
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
lean_dec(x_5);
lean_dec(x_4);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_7);
x_44 = l_Array_insertAt___rarg(x_2, x_8, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_3);
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
x_69 = l_Lean_Expr_isAppOf(x_68, x_5);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_67);
lean_dec(x_7);
x_70 = lean_box(0);
x_71 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1(x_2, x_3, x_4, x_5, x_6, x_8, x_70, x_10, x_11, x_12, x_13, x_14, x_15, x_66);
lean_dec(x_15);
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
lean_dec(x_5);
lean_dec(x_4);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_7);
x_73 = l_Array_insertAt___rarg(x_2, x_8, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_3);
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
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, size_t x_10, size_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
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
x_40 = l_Array_findIdxAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(x_32, x_27, x_39);
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
x_45 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__2(x_41, x_4, x_27, x_2, x_1, x_8, x_3, x_28, x_44, x_13, x_14, x_15, x_16, x_17, x_18, x_33);
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
x_78 = l_Array_findIdxAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(x_70, x_27, x_77);
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
x_83 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__2(x_79, x_4, x_27, x_2, x_1, x_8, x_3, x_28, x_82, x_13, x_14, x_15, x_16, x_17, x_18, x_71);
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
x_125 = l_Array_findIdxAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(x_115, x_111, x_124);
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
x_130 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__2(x_126, x_4, x_111, x_2, x_1, x_8, x_3, x_112, x_129, x_13, x_14, x_15, x_16, x_17, x_18, x_116);
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
x_177 = l_Array_findIdxAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(x_166, x_161, x_176);
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
x_182 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__2(x_178, x_4, x_161, x_2, x_1, x_8, x_3, x_162, x_181, x_13, x_14, x_15, x_16, x_17, x_18, x_167);
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
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__5___rarg), 9, 0);
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
x_25 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_9, x_23, x_24, x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__5;
x_15 = l_Lean_Elab_Term_elabBinders___rarg___closed__1;
x_16 = l_Init_Control_Reader___instance__10___closed__2;
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___boxed), 17, 8);
lean_closure_set(x_17, 0, x_5);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_3);
lean_closure_set(x_17, 4, x_4);
lean_closure_set(x_17, 5, x_14);
lean_closure_set(x_17, 6, x_15);
lean_closure_set(x_17, 7, x_16);
x_18 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__5___rarg(x_6, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_object* l_Array_findIdxAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_15;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
lean_dec(x_9);
return x_17;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___boxed(lean_object** _args) {
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
x_22 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_27);
x_36 = lean_box(0);
x_37 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_35);
x_39 = l_Lean_mkOptionalNode___closed__2;
x_40 = lean_array_push(x_39, x_38);
x_41 = lean_box(0);
x_42 = l_Array_empty___closed__1;
x_43 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_44 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_32, x_40, x_42, x_41, x_43, x_43, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
lean_dec(x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_6 = x_45;
x_7 = x_17;
x_14 = x_46;
goto _start;
}
else
{
uint8_t x_48; 
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
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_17);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_27);
x_53 = lean_box(0);
x_54 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_52);
lean_inc(x_8);
x_56 = l_Lean_Elab_Term_addNamedArg(x_1, x_55, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_32, x_57, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_58);
lean_dec(x_2);
lean_dec(x_57);
return x_59;
}
else
{
uint8_t x_60; 
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_56);
if (x_60 == 0)
{
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_56, 0);
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_56);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
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
x_64 = !lean_is_exclusive(x_31);
if (x_64 == 0)
{
return x_31;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_31, 0);
x_66 = lean_ctor_get(x_31, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_31);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
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
x_68 = !lean_is_exclusive(x_26);
if (x_68 == 0)
{
return x_26;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_26, 0);
x_70 = lean_ctor_get(x_26, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_26);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
case 1:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_18, 1);
lean_inc(x_72);
lean_dec(x_18);
x_73 = lean_ctor_get(x_19, 0);
lean_inc(x_73);
lean_dec(x_19);
x_74 = lean_ctor_get(x_20, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_20, 1);
lean_inc(x_75);
lean_dec(x_20);
x_76 = l_Lean_mkProj(x_74, x_75, x_73);
x_6 = x_76;
x_7 = x_17;
x_14 = x_72;
goto _start;
}
case 2:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_78 = lean_ctor_get(x_18, 1);
lean_inc(x_78);
lean_dec(x_18);
x_79 = lean_ctor_get(x_19, 0);
lean_inc(x_79);
lean_dec(x_19);
x_80 = lean_ctor_get(x_20, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_20, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_20, 2);
lean_inc(x_82);
lean_dec(x_20);
x_83 = lean_name_eq(x_80, x_81);
if (x_83 == 0)
{
lean_object* x_84; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_84 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections(x_80, x_81, x_79, x_8, x_9, x_10, x_11, x_12, x_13, x_78);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(x_82, x_17, x_1, x_2, x_3, x_4, x_5, x_80, x_85, x_8, x_9, x_10, x_11, x_12, x_13, x_86);
return x_87;
}
else
{
uint8_t x_88; 
lean_dec(x_82);
lean_dec(x_80);
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
x_88 = !lean_is_exclusive(x_84);
if (x_88 == 0)
{
return x_84;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_84, 0);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_84);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; 
lean_dec(x_81);
x_92 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(x_82, x_17, x_1, x_2, x_3, x_4, x_5, x_80, x_79, x_8, x_9, x_10, x_11, x_12, x_13, x_78);
return x_92;
}
}
case 3:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_93 = lean_ctor_get(x_18, 1);
lean_inc(x_93);
lean_dec(x_18);
x_94 = lean_ctor_get(x_19, 0);
lean_inc(x_94);
lean_dec(x_19);
x_95 = lean_ctor_get(x_20, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_20, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_20, 2);
lean_inc(x_97);
lean_dec(x_20);
x_98 = l_List_isEmpty___rarg(x_17);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; 
lean_dec(x_96);
lean_dec(x_95);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_94);
x_100 = l_Lean_mkOptionalNode___closed__2;
x_101 = lean_array_push(x_100, x_99);
x_102 = lean_box(0);
x_103 = l_Array_empty___closed__1;
x_104 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_105 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_97, x_103, x_101, x_102, x_104, x_104, x_8, x_9, x_10, x_11, x_12, x_13, x_93);
lean_dec(x_101);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_6 = x_106;
x_7 = x_17;
x_14 = x_107;
goto _start;
}
else
{
uint8_t x_109; 
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
x_109 = !lean_is_exclusive(x_105);
if (x_109 == 0)
{
return x_105;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_105, 0);
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_105);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_17);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_97);
x_113 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_97, x_8, x_9, x_10, x_11, x_12, x_13, x_93);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_116 = l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg(x_95, x_96, x_94, x_2, x_1, x_114, x_8, x_9, x_10, x_11, x_12, x_13, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_97, x_1, x_117, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_118);
lean_dec(x_117);
lean_dec(x_1);
return x_119;
}
else
{
uint8_t x_120; 
lean_dec(x_97);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_116);
if (x_120 == 0)
{
return x_116;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_116, 0);
x_122 = lean_ctor_get(x_116, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_116);
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
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_113);
if (x_124 == 0)
{
return x_113;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_113, 0);
x_126 = lean_ctor_get(x_113, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_113);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
default: 
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_128 = lean_ctor_get(x_18, 1);
lean_inc(x_128);
lean_dec(x_18);
x_129 = lean_ctor_get(x_19, 0);
lean_inc(x_129);
lean_dec(x_19);
x_130 = lean_ctor_get(x_20, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_20, 1);
lean_inc(x_131);
lean_dec(x_20);
x_132 = lean_box(0);
lean_inc(x_8);
x_133 = l_Lean_Elab_Term_mkConst(x_130, x_132, x_8, x_9, x_10, x_11, x_12, x_13, x_128);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_List_isEmpty___rarg(x_17);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; 
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_129);
x_138 = lean_box(0);
x_139 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
x_140 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_140, 2, x_137);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_131);
x_142 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2;
x_143 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_143, 0, x_138);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_143, 2, x_141);
x_144 = l_Lean_mkAppStx___closed__9;
x_145 = lean_array_push(x_144, x_140);
x_146 = lean_array_push(x_145, x_143);
x_147 = lean_box(0);
x_148 = l_Array_empty___closed__1;
x_149 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_150 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_134, x_146, x_148, x_147, x_149, x_149, x_8, x_9, x_10, x_11, x_12, x_13, x_135);
lean_dec(x_146);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_6 = x_151;
x_7 = x_17;
x_14 = x_152;
goto _start;
}
else
{
uint8_t x_154; 
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
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_17);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_129);
x_159 = lean_box(0);
x_160 = l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
x_161 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
lean_ctor_set(x_161, 2, x_158);
lean_inc(x_8);
x_162 = l_Lean_Elab_Term_addNamedArg(x_1, x_161, x_8, x_9, x_10, x_11, x_12, x_13, x_135);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_131);
x_166 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2;
x_167 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_167, 0, x_159);
lean_ctor_set(x_167, 1, x_166);
lean_ctor_set(x_167, 2, x_165);
lean_inc(x_8);
x_168 = l_Lean_Elab_Term_addNamedArg(x_163, x_167, x_8, x_9, x_10, x_11, x_12, x_13, x_164);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_134, x_169, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_170);
lean_dec(x_2);
lean_dec(x_169);
return x_171;
}
else
{
uint8_t x_172; 
lean_dec(x_134);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_172 = !lean_is_exclusive(x_168);
if (x_172 == 0)
{
return x_168;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_168, 0);
x_174 = lean_ctor_get(x_168, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_168);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_134);
lean_dec(x_131);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_176 = !lean_is_exclusive(x_162);
if (x_176 == 0)
{
return x_162;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_162, 0);
x_178 = lean_ctor_get(x_162, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_162);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_131);
lean_dec(x_129);
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
x_180 = !lean_is_exclusive(x_133);
if (x_180 == 0)
{
return x_133;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_133, 0);
x_182 = lean_ctor_get(x_133, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_133);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
}
}
else
{
uint8_t x_184; 
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
x_184 = !lean_is_exclusive(x_18);
if (x_184 == 0)
{
return x_18;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_18, 0);
x_186 = lean_ctor_get(x_18, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_18);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_11 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(x_1, x_1, x_10, lean_box(0), x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_Elab_Term_elabExplicitUnivs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_Basic_0__Array_iterateRevMAux___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_object* l_List_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(lean_object* x_1) {
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
x_7 = l_List_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(x_5);
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
x_11 = l_List_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
x_22 = l_List_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(x_21);
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
lean_object* l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
x_22 = l_List_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(x_21);
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_List_lengthAux___rarg(x_27, x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_dec_lt(x_31, x_30);
x_33 = lean_ctor_get(x_11, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_11, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_11, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_11, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_11, 5);
lean_inc(x_38);
x_39 = lean_ctor_get(x_11, 6);
lean_inc(x_39);
x_40 = lean_ctor_get(x_11, 7);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_11, sizeof(void*)*8);
x_42 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_9 == 0)
{
x_43 = x_32;
goto block_71;
}
else
{
uint8_t x_72; 
x_72 = 1;
x_43 = x_72;
goto block_71;
}
block_71:
{
if (x_42 == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_11, 7);
lean_dec(x_45);
x_46 = lean_ctor_get(x_11, 6);
lean_dec(x_46);
x_47 = lean_ctor_get(x_11, 5);
lean_dec(x_47);
x_48 = lean_ctor_get(x_11, 4);
lean_dec(x_48);
x_49 = lean_ctor_get(x_11, 3);
lean_dec(x_49);
x_50 = lean_ctor_get(x_11, 2);
lean_dec(x_50);
x_51 = lean_ctor_get(x_11, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_11, 0);
lean_dec(x_52);
x_53 = 0;
lean_ctor_set_uint8(x_11, sizeof(void*)*8 + 1, x_53);
x_54 = l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_8, x_43, x_10, x_27, x_11, x_12, x_13, x_14, x_15, x_16, x_28);
return x_54;
}
else
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_11);
x_55 = 0;
x_56 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_56, 0, x_33);
lean_ctor_set(x_56, 1, x_34);
lean_ctor_set(x_56, 2, x_35);
lean_ctor_set(x_56, 3, x_36);
lean_ctor_set(x_56, 4, x_37);
lean_ctor_set(x_56, 5, x_38);
lean_ctor_set(x_56, 6, x_39);
lean_ctor_set(x_56, 7, x_40);
lean_ctor_set_uint8(x_56, sizeof(void*)*8, x_41);
lean_ctor_set_uint8(x_56, sizeof(void*)*8 + 1, x_55);
x_57 = l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_8, x_43, x_10, x_27, x_56, x_12, x_13, x_14, x_15, x_16, x_28);
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_11);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_11, 7);
lean_dec(x_59);
x_60 = lean_ctor_get(x_11, 6);
lean_dec(x_60);
x_61 = lean_ctor_get(x_11, 5);
lean_dec(x_61);
x_62 = lean_ctor_get(x_11, 4);
lean_dec(x_62);
x_63 = lean_ctor_get(x_11, 3);
lean_dec(x_63);
x_64 = lean_ctor_get(x_11, 2);
lean_dec(x_64);
x_65 = lean_ctor_get(x_11, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_11, 0);
lean_dec(x_66);
x_67 = l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4(x_3, x_4, x_5, x_6, x_7, x_8, x_43, x_10, x_27, x_11, x_12, x_13, x_14, x_15, x_16, x_28);
return x_67;
}
else
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get_uint8(x_11, sizeof(void*)*8 + 1);
lean_dec(x_11);
x_69 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_69, 0, x_33);
lean_ctor_set(x_69, 1, x_34);
lean_ctor_set(x_69, 2, x_35);
lean_ctor_set(x_69, 3, x_36);
lean_ctor_set(x_69, 4, x_37);
lean_ctor_set(x_69, 5, x_38);
lean_ctor_set(x_69, 6, x_39);
lean_ctor_set(x_69, 7, x_40);
lean_ctor_set_uint8(x_69, sizeof(void*)*8, x_41);
lean_ctor_set_uint8(x_69, sizeof(void*)*8 + 1, x_68);
x_70 = l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4(x_3, x_4, x_5, x_6, x_7, x_8, x_43, x_10, x_27, x_69, x_12, x_13, x_14, x_15, x_16, x_28);
return x_70;
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
lean_object* l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = lean_unbox(x_7);
lean_dec(x_7);
x_20 = l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3(x_1, x_2, x_3, x_4, x_17, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
}
lean_object* l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = lean_unbox(x_7);
lean_dec(x_7);
x_20 = l_List_foldlM___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4(x_1, x_2, x_3, x_4, x_17, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
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
lean_object* l_List_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2(lean_object* x_1) {
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
x_9 = l_List_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2(x_5);
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
x_15 = l_List_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Array_iterateMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
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
lean_object* x_17; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
lean_inc(x_1);
x_196 = l_Lean_Syntax_getKind(x_1);
x_197 = l_Lean_choiceKind;
x_198 = lean_name_eq(x_196, x_197);
lean_dec(x_196);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_452; lean_object* x_495; lean_object* x_521; uint8_t x_522; 
x_521 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__13;
lean_inc(x_1);
x_522 = l_Lean_Syntax_isOfKind(x_1, x_521);
if (x_522 == 0)
{
lean_object* x_523; 
x_523 = lean_box(0);
x_495 = x_523;
goto block_520;
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; uint8_t x_527; 
x_524 = l_Lean_Syntax_getArgs(x_1);
x_525 = lean_array_get_size(x_524);
lean_dec(x_524);
x_526 = lean_unsigned_to_nat(3u);
x_527 = lean_nat_dec_eq(x_525, x_526);
lean_dec(x_525);
if (x_527 == 0)
{
lean_object* x_528; 
x_528 = lean_box(0);
x_495 = x_528;
goto block_520;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; uint8_t x_534; 
x_529 = lean_unsigned_to_nat(0u);
x_530 = l_Lean_Syntax_getArg(x_1, x_529);
x_531 = lean_unsigned_to_nat(2u);
x_532 = l_Lean_Syntax_getArg(x_1, x_531);
x_533 = l_Lean_fieldIdxKind___closed__2;
lean_inc(x_532);
x_534 = l_Lean_Syntax_isOfKind(x_532, x_533);
if (x_534 == 0)
{
lean_object* x_535; uint8_t x_536; 
x_535 = l_Lean_identKind___closed__2;
lean_inc(x_532);
x_536 = l_Lean_Syntax_isOfKind(x_532, x_535);
if (x_536 == 0)
{
uint8_t x_537; uint8_t x_538; 
lean_dec(x_532);
lean_dec(x_530);
x_537 = l_List_isEmpty___rarg(x_2);
if (x_8 == 0)
{
uint8_t x_712; 
x_712 = 1;
x_538 = x_712;
goto block_711;
}
else
{
uint8_t x_713; 
x_713 = 0;
x_538 = x_713;
goto block_711;
}
block_711:
{
lean_object* x_539; 
if (x_537 == 0)
{
lean_object* x_618; 
x_618 = lean_box(0);
x_539 = x_618;
goto block_617;
}
else
{
uint8_t x_619; 
x_619 = l_Array_isEmpty___rarg(x_3);
if (x_619 == 0)
{
lean_object* x_620; 
x_620 = lean_box(0);
x_539 = x_620;
goto block_617;
}
else
{
uint8_t x_621; 
x_621 = l_Array_isEmpty___rarg(x_4);
if (x_621 == 0)
{
lean_object* x_622; 
x_622 = lean_box(0);
x_539 = x_622;
goto block_617;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_8 == 0)
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; uint8_t x_650; lean_object* x_651; 
x_623 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_623, 1);
lean_inc(x_625);
if (lean_is_exclusive(x_623)) {
 lean_ctor_release(x_623, 0);
 lean_ctor_release(x_623, 1);
 x_626 = x_623;
} else {
 lean_dec_ref(x_623);
 x_626 = lean_box(0);
}
x_650 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_651 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_650, x_10, x_11, x_12, x_13, x_14, x_15, x_625);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; uint8_t x_658; 
lean_dec(x_626);
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_651, 1);
lean_inc(x_653);
lean_dec(x_651);
x_654 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_653);
x_655 = lean_ctor_get(x_654, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_654, 1);
lean_inc(x_656);
lean_dec(x_654);
x_657 = l_Lean_Elab_Term_SavedState_restore(x_624, x_10, x_11, x_12, x_13, x_14, x_15, x_656);
x_658 = !lean_is_exclusive(x_657);
if (x_658 == 0)
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = lean_ctor_get(x_657, 1);
x_660 = lean_ctor_get(x_657, 0);
lean_dec(x_660);
lean_ctor_set(x_657, 1, x_655);
lean_ctor_set(x_657, 0, x_652);
x_661 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_657, x_10, x_11, x_12, x_13, x_14, x_15, x_659);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_661;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_662 = lean_ctor_get(x_657, 1);
lean_inc(x_662);
lean_dec(x_657);
x_663 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_663, 0, x_652);
lean_ctor_set(x_663, 1, x_655);
x_664 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_663, x_10, x_11, x_12, x_13, x_14, x_15, x_662);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_664;
}
}
else
{
lean_object* x_665; lean_object* x_666; 
x_665 = lean_ctor_get(x_651, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_651, 1);
lean_inc(x_666);
lean_dec(x_651);
x_627 = x_665;
x_628 = x_666;
goto block_649;
}
block_649:
{
if (lean_obj_tag(x_627) == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; uint8_t x_633; 
lean_dec(x_626);
x_629 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_628);
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_629, 1);
lean_inc(x_631);
lean_dec(x_629);
x_632 = l_Lean_Elab_Term_SavedState_restore(x_624, x_10, x_11, x_12, x_13, x_14, x_15, x_631);
x_633 = !lean_is_exclusive(x_632);
if (x_633 == 0)
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_634 = lean_ctor_get(x_632, 1);
x_635 = lean_ctor_get(x_632, 0);
lean_dec(x_635);
lean_ctor_set_tag(x_632, 1);
lean_ctor_set(x_632, 1, x_630);
lean_ctor_set(x_632, 0, x_627);
x_636 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_632, x_10, x_11, x_12, x_13, x_14, x_15, x_634);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_636;
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_637 = lean_ctor_get(x_632, 1);
lean_inc(x_637);
lean_dec(x_632);
x_638 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_638, 0, x_627);
lean_ctor_set(x_638, 1, x_630);
x_639 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_638, x_10, x_11, x_12, x_13, x_14, x_15, x_637);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_639;
}
}
else
{
lean_object* x_640; lean_object* x_641; uint8_t x_642; 
lean_dec(x_9);
x_640 = lean_ctor_get(x_627, 0);
lean_inc(x_640);
x_641 = l_Lean_Elab_postponeExceptionId;
x_642 = lean_nat_dec_eq(x_640, x_641);
lean_dec(x_640);
if (x_642 == 0)
{
lean_object* x_643; 
lean_dec(x_624);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_626)) {
 x_643 = lean_alloc_ctor(1, 2, 0);
} else {
 x_643 = x_626;
 lean_ctor_set_tag(x_643, 1);
}
lean_ctor_set(x_643, 0, x_627);
lean_ctor_set(x_643, 1, x_628);
return x_643;
}
else
{
lean_object* x_644; uint8_t x_645; 
lean_dec(x_626);
x_644 = l_Lean_Elab_Term_SavedState_restore(x_624, x_10, x_11, x_12, x_13, x_14, x_15, x_628);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_645 = !lean_is_exclusive(x_644);
if (x_645 == 0)
{
lean_object* x_646; 
x_646 = lean_ctor_get(x_644, 0);
lean_dec(x_646);
lean_ctor_set_tag(x_644, 1);
lean_ctor_set(x_644, 0, x_627);
return x_644;
}
else
{
lean_object* x_647; lean_object* x_648; 
x_647 = lean_ctor_get(x_644, 1);
lean_inc(x_647);
lean_dec(x_644);
x_648 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_648, 0, x_627);
lean_ctor_set(x_648, 1, x_647);
return x_648;
}
}
}
}
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_695; 
x_667 = lean_box(0);
x_668 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_669 = lean_ctor_get(x_668, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_668, 1);
lean_inc(x_670);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 x_671 = x_668;
} else {
 lean_dec_ref(x_668);
 x_671 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_695 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_538, x_667, x_10, x_11, x_12, x_13, x_14, x_15, x_670);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; 
lean_dec(x_671);
x_696 = lean_ctor_get(x_695, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_695, 1);
lean_inc(x_697);
lean_dec(x_695);
x_698 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_697);
x_699 = lean_ctor_get(x_698, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_698, 1);
lean_inc(x_700);
lean_dec(x_698);
x_701 = l_Lean_Elab_Term_SavedState_restore(x_669, x_10, x_11, x_12, x_13, x_14, x_15, x_700);
x_702 = !lean_is_exclusive(x_701);
if (x_702 == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; 
x_703 = lean_ctor_get(x_701, 1);
x_704 = lean_ctor_get(x_701, 0);
lean_dec(x_704);
lean_ctor_set(x_701, 1, x_699);
lean_ctor_set(x_701, 0, x_696);
x_705 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_701, x_10, x_11, x_12, x_13, x_14, x_15, x_703);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_705;
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_706 = lean_ctor_get(x_701, 1);
lean_inc(x_706);
lean_dec(x_701);
x_707 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_707, 0, x_696);
lean_ctor_set(x_707, 1, x_699);
x_708 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_707, x_10, x_11, x_12, x_13, x_14, x_15, x_706);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_708;
}
}
else
{
lean_object* x_709; lean_object* x_710; 
x_709 = lean_ctor_get(x_695, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_695, 1);
lean_inc(x_710);
lean_dec(x_695);
x_672 = x_709;
x_673 = x_710;
goto block_694;
}
block_694:
{
if (lean_obj_tag(x_672) == 0)
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; uint8_t x_678; 
lean_dec(x_671);
x_674 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_673);
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
lean_dec(x_674);
x_677 = l_Lean_Elab_Term_SavedState_restore(x_669, x_10, x_11, x_12, x_13, x_14, x_15, x_676);
x_678 = !lean_is_exclusive(x_677);
if (x_678 == 0)
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_679 = lean_ctor_get(x_677, 1);
x_680 = lean_ctor_get(x_677, 0);
lean_dec(x_680);
lean_ctor_set_tag(x_677, 1);
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
x_683 = lean_alloc_ctor(1, 2, 0);
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
lean_object* x_685; lean_object* x_686; uint8_t x_687; 
lean_dec(x_9);
x_685 = lean_ctor_get(x_672, 0);
lean_inc(x_685);
x_686 = l_Lean_Elab_postponeExceptionId;
x_687 = lean_nat_dec_eq(x_685, x_686);
lean_dec(x_685);
if (x_687 == 0)
{
lean_object* x_688; 
lean_dec(x_669);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_671)) {
 x_688 = lean_alloc_ctor(1, 2, 0);
} else {
 x_688 = x_671;
 lean_ctor_set_tag(x_688, 1);
}
lean_ctor_set(x_688, 0, x_672);
lean_ctor_set(x_688, 1, x_673);
return x_688;
}
else
{
lean_object* x_689; uint8_t x_690; 
lean_dec(x_671);
x_689 = l_Lean_Elab_Term_SavedState_restore(x_669, x_10, x_11, x_12, x_13, x_14, x_15, x_673);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_690 = !lean_is_exclusive(x_689);
if (x_690 == 0)
{
lean_object* x_691; 
x_691 = lean_ctor_get(x_689, 0);
lean_dec(x_691);
lean_ctor_set_tag(x_689, 1);
lean_ctor_set(x_689, 0, x_672);
return x_689;
}
else
{
lean_object* x_692; lean_object* x_693; 
x_692 = lean_ctor_get(x_689, 1);
lean_inc(x_692);
lean_dec(x_689);
x_693 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_693, 0, x_672);
lean_ctor_set(x_693, 1, x_692);
return x_693;
}
}
}
}
}
}
}
}
block_617:
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_577; lean_object* x_578; lean_object* x_600; 
lean_dec(x_539);
x_540 = lean_box(0);
x_541 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_541, 1);
lean_inc(x_543);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 x_544 = x_541;
} else {
 lean_dec_ref(x_541);
 x_544 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_600 = l_Lean_Elab_Term_elabTerm(x_1, x_540, x_538, x_10, x_11, x_12, x_13, x_14, x_15, x_543);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_600, 1);
lean_inc(x_602);
lean_dec(x_600);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_603 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_601, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_602);
if (lean_obj_tag(x_603) == 0)
{
if (x_8 == 0)
{
lean_object* x_604; lean_object* x_605; 
lean_dec(x_544);
lean_dec(x_5);
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_603, 1);
lean_inc(x_605);
lean_dec(x_603);
x_577 = x_604;
x_578 = x_605;
goto block_599;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_606 = lean_ctor_get(x_603, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_603, 1);
lean_inc(x_607);
lean_dec(x_603);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_608 = l_Lean_Elab_Term_ensureHasType(x_5, x_606, x_540, x_10, x_11, x_12, x_13, x_14, x_15, x_607);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_609; lean_object* x_610; 
lean_dec(x_544);
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_608, 1);
lean_inc(x_610);
lean_dec(x_608);
x_577 = x_609;
x_578 = x_610;
goto block_599;
}
else
{
lean_object* x_611; lean_object* x_612; 
x_611 = lean_ctor_get(x_608, 0);
lean_inc(x_611);
x_612 = lean_ctor_get(x_608, 1);
lean_inc(x_612);
lean_dec(x_608);
x_545 = x_611;
x_546 = x_612;
goto block_576;
}
}
}
else
{
lean_object* x_613; lean_object* x_614; 
lean_dec(x_5);
x_613 = lean_ctor_get(x_603, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_603, 1);
lean_inc(x_614);
lean_dec(x_603);
x_545 = x_613;
x_546 = x_614;
goto block_576;
}
}
else
{
lean_object* x_615; lean_object* x_616; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_615 = lean_ctor_get(x_600, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_600, 1);
lean_inc(x_616);
lean_dec(x_600);
x_545 = x_615;
x_546 = x_616;
goto block_576;
}
block_576:
{
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_547; uint8_t x_548; 
lean_dec(x_544);
x_547 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_546);
x_548 = !lean_is_exclusive(x_547);
if (x_548 == 0)
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; uint8_t x_552; 
x_549 = lean_ctor_get(x_547, 0);
x_550 = lean_ctor_get(x_547, 1);
x_551 = l_Lean_Elab_Term_SavedState_restore(x_542, x_10, x_11, x_12, x_13, x_14, x_15, x_550);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_552 = !lean_is_exclusive(x_551);
if (x_552 == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_551, 1);
x_554 = lean_ctor_get(x_551, 0);
lean_dec(x_554);
lean_ctor_set_tag(x_551, 1);
lean_ctor_set(x_551, 1, x_549);
lean_ctor_set(x_551, 0, x_545);
x_555 = lean_array_push(x_9, x_551);
lean_ctor_set(x_547, 1, x_553);
lean_ctor_set(x_547, 0, x_555);
return x_547;
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_556 = lean_ctor_get(x_551, 1);
lean_inc(x_556);
lean_dec(x_551);
x_557 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_557, 0, x_545);
lean_ctor_set(x_557, 1, x_549);
x_558 = lean_array_push(x_9, x_557);
lean_ctor_set(x_547, 1, x_556);
lean_ctor_set(x_547, 0, x_558);
return x_547;
}
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_559 = lean_ctor_get(x_547, 0);
x_560 = lean_ctor_get(x_547, 1);
lean_inc(x_560);
lean_inc(x_559);
lean_dec(x_547);
x_561 = l_Lean_Elab_Term_SavedState_restore(x_542, x_10, x_11, x_12, x_13, x_14, x_15, x_560);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_562 = lean_ctor_get(x_561, 1);
lean_inc(x_562);
if (lean_is_exclusive(x_561)) {
 lean_ctor_release(x_561, 0);
 lean_ctor_release(x_561, 1);
 x_563 = x_561;
} else {
 lean_dec_ref(x_561);
 x_563 = lean_box(0);
}
if (lean_is_scalar(x_563)) {
 x_564 = lean_alloc_ctor(1, 2, 0);
} else {
 x_564 = x_563;
 lean_ctor_set_tag(x_564, 1);
}
lean_ctor_set(x_564, 0, x_545);
lean_ctor_set(x_564, 1, x_559);
x_565 = lean_array_push(x_9, x_564);
x_566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_562);
return x_566;
}
}
else
{
lean_object* x_567; lean_object* x_568; uint8_t x_569; 
lean_dec(x_9);
x_567 = lean_ctor_get(x_545, 0);
lean_inc(x_567);
x_568 = l_Lean_Elab_postponeExceptionId;
x_569 = lean_nat_dec_eq(x_567, x_568);
lean_dec(x_567);
if (x_569 == 0)
{
lean_object* x_570; 
lean_dec(x_542);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_544)) {
 x_570 = lean_alloc_ctor(1, 2, 0);
} else {
 x_570 = x_544;
 lean_ctor_set_tag(x_570, 1);
}
lean_ctor_set(x_570, 0, x_545);
lean_ctor_set(x_570, 1, x_546);
return x_570;
}
else
{
lean_object* x_571; uint8_t x_572; 
lean_dec(x_544);
x_571 = l_Lean_Elab_Term_SavedState_restore(x_542, x_10, x_11, x_12, x_13, x_14, x_15, x_546);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_572 = !lean_is_exclusive(x_571);
if (x_572 == 0)
{
lean_object* x_573; 
x_573 = lean_ctor_get(x_571, 0);
lean_dec(x_573);
lean_ctor_set_tag(x_571, 1);
lean_ctor_set(x_571, 0, x_545);
return x_571;
}
else
{
lean_object* x_574; lean_object* x_575; 
x_574 = lean_ctor_get(x_571, 1);
lean_inc(x_574);
lean_dec(x_571);
x_575 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_575, 0, x_545);
lean_ctor_set(x_575, 1, x_574);
return x_575;
}
}
}
}
block_599:
{
lean_object* x_579; uint8_t x_580; 
x_579 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_578);
x_580 = !lean_is_exclusive(x_579);
if (x_580 == 0)
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; uint8_t x_584; 
x_581 = lean_ctor_get(x_579, 0);
x_582 = lean_ctor_get(x_579, 1);
x_583 = l_Lean_Elab_Term_SavedState_restore(x_542, x_10, x_11, x_12, x_13, x_14, x_15, x_582);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_584 = !lean_is_exclusive(x_583);
if (x_584 == 0)
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_585 = lean_ctor_get(x_583, 1);
x_586 = lean_ctor_get(x_583, 0);
lean_dec(x_586);
lean_ctor_set(x_583, 1, x_581);
lean_ctor_set(x_583, 0, x_577);
x_587 = lean_array_push(x_9, x_583);
lean_ctor_set(x_579, 1, x_585);
lean_ctor_set(x_579, 0, x_587);
return x_579;
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_588 = lean_ctor_get(x_583, 1);
lean_inc(x_588);
lean_dec(x_583);
x_589 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_589, 0, x_577);
lean_ctor_set(x_589, 1, x_581);
x_590 = lean_array_push(x_9, x_589);
lean_ctor_set(x_579, 1, x_588);
lean_ctor_set(x_579, 0, x_590);
return x_579;
}
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_591 = lean_ctor_get(x_579, 0);
x_592 = lean_ctor_get(x_579, 1);
lean_inc(x_592);
lean_inc(x_591);
lean_dec(x_579);
x_593 = l_Lean_Elab_Term_SavedState_restore(x_542, x_10, x_11, x_12, x_13, x_14, x_15, x_592);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_594 = lean_ctor_get(x_593, 1);
lean_inc(x_594);
if (lean_is_exclusive(x_593)) {
 lean_ctor_release(x_593, 0);
 lean_ctor_release(x_593, 1);
 x_595 = x_593;
} else {
 lean_dec_ref(x_593);
 x_595 = lean_box(0);
}
if (lean_is_scalar(x_595)) {
 x_596 = lean_alloc_ctor(0, 2, 0);
} else {
 x_596 = x_595;
}
lean_ctor_set(x_596, 0, x_577);
lean_ctor_set(x_596, 1, x_591);
x_597 = lean_array_push(x_9, x_596);
x_598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_598, 0, x_597);
lean_ctor_set(x_598, 1, x_594);
return x_598;
}
}
}
}
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
lean_dec(x_1);
x_714 = l_Lean_Syntax_getId(x_532);
lean_dec(x_532);
x_715 = lean_erase_macro_scopes(x_714);
x_716 = l_Lean_Name_components(x_715);
x_717 = l_List_map___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2(x_716);
x_718 = l_List_append___rarg(x_717, x_2);
x_1 = x_530;
x_2 = x_718;
goto _start;
}
}
else
{
lean_object* x_720; lean_object* x_721; 
lean_dec(x_1);
x_720 = l_Lean_fieldIdxKind;
x_721 = l_Lean_Syntax_isNatLitAux(x_720, x_532);
lean_dec(x_532);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_722 = l_Init_Core___instance__33;
x_723 = l_Option_get_x21___rarg___closed__4;
x_724 = lean_panic_fn(x_722, x_723);
x_725 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_725, 0, x_724);
x_726 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_726, 0, x_725);
lean_ctor_set(x_726, 1, x_2);
x_1 = x_530;
x_2 = x_726;
goto _start;
}
else
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_728 = lean_ctor_get(x_721, 0);
lean_inc(x_728);
lean_dec(x_721);
x_729 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_729, 0, x_728);
x_730 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_730, 0, x_729);
lean_ctor_set(x_730, 1, x_2);
x_1 = x_530;
x_2 = x_730;
goto _start;
}
}
}
}
block_451:
{
lean_object* x_200; uint8_t x_201; 
lean_dec(x_199);
x_200 = l_Lean_identKind___closed__2;
lean_inc(x_1);
x_201 = l_Lean_Syntax_isOfKind(x_1, x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_248; uint8_t x_249; 
x_248 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8;
lean_inc(x_1);
x_249 = l_Lean_Syntax_isOfKind(x_1, x_248);
if (x_249 == 0)
{
lean_object* x_250; 
x_250 = lean_box(0);
x_202 = x_250;
goto block_247;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_251 = l_Lean_Syntax_getArgs(x_1);
x_252 = lean_array_get_size(x_251);
lean_dec(x_251);
x_253 = lean_unsigned_to_nat(4u);
x_254 = lean_nat_dec_eq(x_252, x_253);
lean_dec(x_252);
if (x_254 == 0)
{
lean_object* x_255; 
x_255 = lean_box(0);
x_202 = x_255;
goto block_247;
}
else
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_256 = lean_unsigned_to_nat(0u);
x_257 = l_Lean_Syntax_getArg(x_1, x_256);
lean_inc(x_257);
x_258 = l_Lean_Syntax_isOfKind(x_257, x_200);
if (x_258 == 0)
{
uint8_t x_259; uint8_t x_260; 
lean_dec(x_257);
x_259 = l_List_isEmpty___rarg(x_2);
if (x_8 == 0)
{
uint8_t x_434; 
x_434 = 1;
x_260 = x_434;
goto block_433;
}
else
{
uint8_t x_435; 
x_435 = 0;
x_260 = x_435;
goto block_433;
}
block_433:
{
lean_object* x_261; 
if (x_259 == 0)
{
lean_object* x_340; 
x_340 = lean_box(0);
x_261 = x_340;
goto block_339;
}
else
{
uint8_t x_341; 
x_341 = l_Array_isEmpty___rarg(x_3);
if (x_341 == 0)
{
lean_object* x_342; 
x_342 = lean_box(0);
x_261 = x_342;
goto block_339;
}
else
{
uint8_t x_343; 
x_343 = l_Array_isEmpty___rarg(x_4);
if (x_343 == 0)
{
lean_object* x_344; 
x_344 = lean_box(0);
x_261 = x_344;
goto block_339;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_8 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_372; lean_object* x_373; 
x_345 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_348 = x_345;
} else {
 lean_dec_ref(x_345);
 x_348 = lean_box(0);
}
x_372 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_373 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_372, x_10, x_11, x_12, x_13, x_14, x_15, x_347);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; 
lean_dec(x_348);
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_376 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_375);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec(x_376);
x_379 = l_Lean_Elab_Term_SavedState_restore(x_346, x_10, x_11, x_12, x_13, x_14, x_15, x_378);
x_380 = !lean_is_exclusive(x_379);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_379, 1);
x_382 = lean_ctor_get(x_379, 0);
lean_dec(x_382);
lean_ctor_set(x_379, 1, x_377);
lean_ctor_set(x_379, 0, x_374);
x_383 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_379, x_10, x_11, x_12, x_13, x_14, x_15, x_381);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_383;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_384 = lean_ctor_get(x_379, 1);
lean_inc(x_384);
lean_dec(x_379);
x_385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_385, 0, x_374);
lean_ctor_set(x_385, 1, x_377);
x_386 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_385, x_10, x_11, x_12, x_13, x_14, x_15, x_384);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_386;
}
}
else
{
lean_object* x_387; lean_object* x_388; 
x_387 = lean_ctor_get(x_373, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_373, 1);
lean_inc(x_388);
lean_dec(x_373);
x_349 = x_387;
x_350 = x_388;
goto block_371;
}
block_371:
{
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; 
lean_dec(x_348);
x_351 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_350);
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = l_Lean_Elab_Term_SavedState_restore(x_346, x_10, x_11, x_12, x_13, x_14, x_15, x_353);
x_355 = !lean_is_exclusive(x_354);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_354, 1);
x_357 = lean_ctor_get(x_354, 0);
lean_dec(x_357);
lean_ctor_set_tag(x_354, 1);
lean_ctor_set(x_354, 1, x_352);
lean_ctor_set(x_354, 0, x_349);
x_358 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_354, x_10, x_11, x_12, x_13, x_14, x_15, x_356);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_358;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_354, 1);
lean_inc(x_359);
lean_dec(x_354);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_349);
lean_ctor_set(x_360, 1, x_352);
x_361 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_360, x_10, x_11, x_12, x_13, x_14, x_15, x_359);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_361;
}
}
else
{
lean_object* x_362; lean_object* x_363; uint8_t x_364; 
lean_dec(x_9);
x_362 = lean_ctor_get(x_349, 0);
lean_inc(x_362);
x_363 = l_Lean_Elab_postponeExceptionId;
x_364 = lean_nat_dec_eq(x_362, x_363);
lean_dec(x_362);
if (x_364 == 0)
{
lean_object* x_365; 
lean_dec(x_346);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_348)) {
 x_365 = lean_alloc_ctor(1, 2, 0);
} else {
 x_365 = x_348;
 lean_ctor_set_tag(x_365, 1);
}
lean_ctor_set(x_365, 0, x_349);
lean_ctor_set(x_365, 1, x_350);
return x_365;
}
else
{
lean_object* x_366; uint8_t x_367; 
lean_dec(x_348);
x_366 = l_Lean_Elab_Term_SavedState_restore(x_346, x_10, x_11, x_12, x_13, x_14, x_15, x_350);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_367 = !lean_is_exclusive(x_366);
if (x_367 == 0)
{
lean_object* x_368; 
x_368 = lean_ctor_get(x_366, 0);
lean_dec(x_368);
lean_ctor_set_tag(x_366, 1);
lean_ctor_set(x_366, 0, x_349);
return x_366;
}
else
{
lean_object* x_369; lean_object* x_370; 
x_369 = lean_ctor_get(x_366, 1);
lean_inc(x_369);
lean_dec(x_366);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_349);
lean_ctor_set(x_370, 1, x_369);
return x_370;
}
}
}
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_417; 
x_389 = lean_box(0);
x_390 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_393 = x_390;
} else {
 lean_dec_ref(x_390);
 x_393 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_417 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_260, x_389, x_10, x_11, x_12, x_13, x_14, x_15, x_392);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
lean_dec(x_393);
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
x_420 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_419);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = l_Lean_Elab_Term_SavedState_restore(x_391, x_10, x_11, x_12, x_13, x_14, x_15, x_422);
x_424 = !lean_is_exclusive(x_423);
if (x_424 == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_423, 1);
x_426 = lean_ctor_get(x_423, 0);
lean_dec(x_426);
lean_ctor_set(x_423, 1, x_421);
lean_ctor_set(x_423, 0, x_418);
x_427 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_423, x_10, x_11, x_12, x_13, x_14, x_15, x_425);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_427;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_423, 1);
lean_inc(x_428);
lean_dec(x_423);
x_429 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_429, 0, x_418);
lean_ctor_set(x_429, 1, x_421);
x_430 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_429, x_10, x_11, x_12, x_13, x_14, x_15, x_428);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_430;
}
}
else
{
lean_object* x_431; lean_object* x_432; 
x_431 = lean_ctor_get(x_417, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_417, 1);
lean_inc(x_432);
lean_dec(x_417);
x_394 = x_431;
x_395 = x_432;
goto block_416;
}
block_416:
{
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; 
lean_dec(x_393);
x_396 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_395);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_399 = l_Lean_Elab_Term_SavedState_restore(x_391, x_10, x_11, x_12, x_13, x_14, x_15, x_398);
x_400 = !lean_is_exclusive(x_399);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_399, 1);
x_402 = lean_ctor_get(x_399, 0);
lean_dec(x_402);
lean_ctor_set_tag(x_399, 1);
lean_ctor_set(x_399, 1, x_397);
lean_ctor_set(x_399, 0, x_394);
x_403 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_399, x_10, x_11, x_12, x_13, x_14, x_15, x_401);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_403;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_399, 1);
lean_inc(x_404);
lean_dec(x_399);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_394);
lean_ctor_set(x_405, 1, x_397);
x_406 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_405, x_10, x_11, x_12, x_13, x_14, x_15, x_404);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_406;
}
}
else
{
lean_object* x_407; lean_object* x_408; uint8_t x_409; 
lean_dec(x_9);
x_407 = lean_ctor_get(x_394, 0);
lean_inc(x_407);
x_408 = l_Lean_Elab_postponeExceptionId;
x_409 = lean_nat_dec_eq(x_407, x_408);
lean_dec(x_407);
if (x_409 == 0)
{
lean_object* x_410; 
lean_dec(x_391);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_393)) {
 x_410 = lean_alloc_ctor(1, 2, 0);
} else {
 x_410 = x_393;
 lean_ctor_set_tag(x_410, 1);
}
lean_ctor_set(x_410, 0, x_394);
lean_ctor_set(x_410, 1, x_395);
return x_410;
}
else
{
lean_object* x_411; uint8_t x_412; 
lean_dec(x_393);
x_411 = l_Lean_Elab_Term_SavedState_restore(x_391, x_10, x_11, x_12, x_13, x_14, x_15, x_395);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_412 = !lean_is_exclusive(x_411);
if (x_412 == 0)
{
lean_object* x_413; 
x_413 = lean_ctor_get(x_411, 0);
lean_dec(x_413);
lean_ctor_set_tag(x_411, 1);
lean_ctor_set(x_411, 0, x_394);
return x_411;
}
else
{
lean_object* x_414; lean_object* x_415; 
x_414 = lean_ctor_get(x_411, 1);
lean_inc(x_414);
lean_dec(x_411);
x_415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_415, 0, x_394);
lean_ctor_set(x_415, 1, x_414);
return x_415;
}
}
}
}
}
}
}
}
block_339:
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_299; lean_object* x_300; lean_object* x_322; 
lean_dec(x_261);
x_262 = lean_box(0);
x_263 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_266 = x_263;
} else {
 lean_dec_ref(x_263);
 x_266 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_322 = l_Lean_Elab_Term_elabTerm(x_1, x_262, x_260, x_10, x_11, x_12, x_13, x_14, x_15, x_265);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_325 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_323, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_324);
if (lean_obj_tag(x_325) == 0)
{
if (x_8 == 0)
{
lean_object* x_326; lean_object* x_327; 
lean_dec(x_266);
lean_dec(x_5);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
lean_dec(x_325);
x_299 = x_326;
x_300 = x_327;
goto block_321;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_325, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_325, 1);
lean_inc(x_329);
lean_dec(x_325);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_330 = l_Lean_Elab_Term_ensureHasType(x_5, x_328, x_262, x_10, x_11, x_12, x_13, x_14, x_15, x_329);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_266);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_299 = x_331;
x_300 = x_332;
goto block_321;
}
else
{
lean_object* x_333; lean_object* x_334; 
x_333 = lean_ctor_get(x_330, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_330, 1);
lean_inc(x_334);
lean_dec(x_330);
x_267 = x_333;
x_268 = x_334;
goto block_298;
}
}
}
else
{
lean_object* x_335; lean_object* x_336; 
lean_dec(x_5);
x_335 = lean_ctor_get(x_325, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_325, 1);
lean_inc(x_336);
lean_dec(x_325);
x_267 = x_335;
x_268 = x_336;
goto block_298;
}
}
else
{
lean_object* x_337; lean_object* x_338; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_337 = lean_ctor_get(x_322, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_322, 1);
lean_inc(x_338);
lean_dec(x_322);
x_267 = x_337;
x_268 = x_338;
goto block_298;
}
block_298:
{
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_269; uint8_t x_270; 
lean_dec(x_266);
x_269 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_268);
x_270 = !lean_is_exclusive(x_269);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
x_271 = lean_ctor_get(x_269, 0);
x_272 = lean_ctor_get(x_269, 1);
x_273 = l_Lean_Elab_Term_SavedState_restore(x_264, x_10, x_11, x_12, x_13, x_14, x_15, x_272);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_274 = !lean_is_exclusive(x_273);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_273, 1);
x_276 = lean_ctor_get(x_273, 0);
lean_dec(x_276);
lean_ctor_set_tag(x_273, 1);
lean_ctor_set(x_273, 1, x_271);
lean_ctor_set(x_273, 0, x_267);
x_277 = lean_array_push(x_9, x_273);
lean_ctor_set(x_269, 1, x_275);
lean_ctor_set(x_269, 0, x_277);
return x_269;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_273, 1);
lean_inc(x_278);
lean_dec(x_273);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_267);
lean_ctor_set(x_279, 1, x_271);
x_280 = lean_array_push(x_9, x_279);
lean_ctor_set(x_269, 1, x_278);
lean_ctor_set(x_269, 0, x_280);
return x_269;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_281 = lean_ctor_get(x_269, 0);
x_282 = lean_ctor_get(x_269, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_269);
x_283 = l_Lean_Elab_Term_SavedState_restore(x_264, x_10, x_11, x_12, x_13, x_14, x_15, x_282);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_285 = x_283;
} else {
 lean_dec_ref(x_283);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_285;
 lean_ctor_set_tag(x_286, 1);
}
lean_ctor_set(x_286, 0, x_267);
lean_ctor_set(x_286, 1, x_281);
x_287 = lean_array_push(x_9, x_286);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_284);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; uint8_t x_291; 
lean_dec(x_9);
x_289 = lean_ctor_get(x_267, 0);
lean_inc(x_289);
x_290 = l_Lean_Elab_postponeExceptionId;
x_291 = lean_nat_dec_eq(x_289, x_290);
lean_dec(x_289);
if (x_291 == 0)
{
lean_object* x_292; 
lean_dec(x_264);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_266)) {
 x_292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_292 = x_266;
 lean_ctor_set_tag(x_292, 1);
}
lean_ctor_set(x_292, 0, x_267);
lean_ctor_set(x_292, 1, x_268);
return x_292;
}
else
{
lean_object* x_293; uint8_t x_294; 
lean_dec(x_266);
x_293 = l_Lean_Elab_Term_SavedState_restore(x_264, x_10, x_11, x_12, x_13, x_14, x_15, x_268);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_294 = !lean_is_exclusive(x_293);
if (x_294 == 0)
{
lean_object* x_295; 
x_295 = lean_ctor_get(x_293, 0);
lean_dec(x_295);
lean_ctor_set_tag(x_293, 1);
lean_ctor_set(x_293, 0, x_267);
return x_293;
}
else
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_293, 1);
lean_inc(x_296);
lean_dec(x_293);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_267);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
}
}
}
block_321:
{
lean_object* x_301; uint8_t x_302; 
x_301 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_300);
x_302 = !lean_is_exclusive(x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_303 = lean_ctor_get(x_301, 0);
x_304 = lean_ctor_get(x_301, 1);
x_305 = l_Lean_Elab_Term_SavedState_restore(x_264, x_10, x_11, x_12, x_13, x_14, x_15, x_304);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_306 = !lean_is_exclusive(x_305);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_305, 1);
x_308 = lean_ctor_get(x_305, 0);
lean_dec(x_308);
lean_ctor_set(x_305, 1, x_303);
lean_ctor_set(x_305, 0, x_299);
x_309 = lean_array_push(x_9, x_305);
lean_ctor_set(x_301, 1, x_307);
lean_ctor_set(x_301, 0, x_309);
return x_301;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_305, 1);
lean_inc(x_310);
lean_dec(x_305);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_299);
lean_ctor_set(x_311, 1, x_303);
x_312 = lean_array_push(x_9, x_311);
lean_ctor_set(x_301, 1, x_310);
lean_ctor_set(x_301, 0, x_312);
return x_301;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_313 = lean_ctor_get(x_301, 0);
x_314 = lean_ctor_get(x_301, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_301);
x_315 = l_Lean_Elab_Term_SavedState_restore(x_264, x_10, x_11, x_12, x_13, x_14, x_15, x_314);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_317 = x_315;
} else {
 lean_dec_ref(x_315);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_299);
lean_ctor_set(x_318, 1, x_313);
x_319 = lean_array_push(x_9, x_318);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_316);
return x_320;
}
}
}
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_436 = lean_unsigned_to_nat(2u);
x_437 = l_Lean_Syntax_getArg(x_1, x_436);
lean_dec(x_1);
x_438 = l_Lean_Syntax_getArgs(x_437);
lean_dec(x_437);
x_439 = l_Array_empty___closed__1;
x_440 = l_Array_foldlStepMAux___at_Lean_Syntax_getSepArgs___spec__1(x_436, x_438, x_256, x_439);
lean_dec(x_438);
x_441 = l_Lean_Elab_Term_elabExplicitUnivs(x_440, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_440);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_441, 1);
lean_inc(x_443);
lean_dec(x_441);
x_444 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(x_257, x_442, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_443);
return x_444;
}
else
{
uint8_t x_445; 
lean_dec(x_257);
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
x_445 = !lean_is_exclusive(x_441);
if (x_445 == 0)
{
return x_441;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_446 = lean_ctor_get(x_441, 0);
x_447 = lean_ctor_get(x_441, 1);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_441);
x_448 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_448, 0, x_446);
lean_ctor_set(x_448, 1, x_447);
return x_448;
}
}
}
}
}
block_247:
{
lean_object* x_203; uint8_t x_204; 
lean_dec(x_202);
x_203 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_isExplicit___closed__2;
lean_inc(x_1);
x_204 = l_Lean_Syntax_isOfKind(x_1, x_203);
if (x_204 == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = l_Lean_mkHole___closed__2;
lean_inc(x_1);
x_206 = l_Lean_Syntax_isOfKind(x_1, x_205);
if (x_206 == 0)
{
lean_object* x_207; 
x_207 = lean_box(0);
x_17 = x_207;
goto block_195;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_208 = l_Lean_Syntax_getArgs(x_1);
x_209 = lean_array_get_size(x_208);
lean_dec(x_208);
x_210 = lean_unsigned_to_nat(1u);
x_211 = lean_nat_dec_eq(x_209, x_210);
lean_dec(x_209);
if (x_211 == 0)
{
lean_object* x_212; 
x_212 = lean_box(0);
x_17 = x_212;
goto block_195;
}
else
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_213 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3;
x_214 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_213, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_214;
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_215 = l_Lean_Syntax_getArgs(x_1);
x_216 = lean_array_get_size(x_215);
lean_dec(x_215);
x_217 = lean_unsigned_to_nat(2u);
x_218 = lean_nat_dec_eq(x_216, x_217);
if (x_218 == 0)
{
lean_object* x_219; uint8_t x_220; 
x_219 = l_Lean_mkHole___closed__2;
lean_inc(x_1);
x_220 = l_Lean_Syntax_isOfKind(x_1, x_219);
if (x_220 == 0)
{
lean_object* x_221; 
lean_dec(x_216);
x_221 = lean_box(0);
x_17 = x_221;
goto block_195;
}
else
{
lean_object* x_222; uint8_t x_223; 
x_222 = lean_unsigned_to_nat(1u);
x_223 = lean_nat_dec_eq(x_216, x_222);
lean_dec(x_216);
if (x_223 == 0)
{
lean_object* x_224; 
x_224 = lean_box(0);
x_17 = x_224;
goto block_195;
}
else
{
lean_object* x_225; lean_object* x_226; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_225 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3;
x_226 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_225, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_226;
}
}
}
else
{
lean_object* x_227; lean_object* x_228; uint8_t x_229; 
lean_dec(x_216);
x_227 = lean_unsigned_to_nat(1u);
x_228 = l_Lean_Syntax_getArg(x_1, x_227);
lean_inc(x_228);
x_229 = l_Lean_Syntax_isOfKind(x_228, x_200);
if (x_229 == 0)
{
lean_object* x_230; uint8_t x_231; 
x_230 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8;
lean_inc(x_228);
x_231 = l_Lean_Syntax_isOfKind(x_228, x_230);
if (x_231 == 0)
{
lean_object* x_232; 
lean_dec(x_228);
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
x_232 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___rarg(x_16);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_233 = l_Lean_Syntax_getArgs(x_228);
x_234 = lean_array_get_size(x_233);
lean_dec(x_233);
x_235 = lean_unsigned_to_nat(4u);
x_236 = lean_nat_dec_eq(x_234, x_235);
lean_dec(x_234);
if (x_236 == 0)
{
lean_object* x_237; 
lean_dec(x_228);
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
x_237 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___rarg(x_16);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_238 = lean_unsigned_to_nat(0u);
x_239 = l_Lean_Syntax_getArg(x_228, x_238);
lean_dec(x_228);
x_240 = l_Lean_Syntax_isOfKind(x_239, x_200);
if (x_240 == 0)
{
lean_object* x_241; 
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
x_241 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___rarg(x_16);
return x_241;
}
else
{
lean_object* x_242; uint8_t x_243; 
x_242 = l_Lean_Syntax_getArg(x_1, x_227);
lean_dec(x_1);
x_243 = 1;
x_1 = x_242;
x_6 = x_243;
goto _start;
}
}
}
}
else
{
uint8_t x_245; 
lean_dec(x_1);
x_245 = 1;
x_1 = x_228;
x_6 = x_245;
goto _start;
}
}
}
}
}
else
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_box(0);
x_450 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(x_1, x_449, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_450;
}
}
block_494:
{
lean_object* x_453; uint8_t x_454; 
lean_dec(x_452);
x_453 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__10;
lean_inc(x_1);
x_454 = l_Lean_Syntax_isOfKind(x_1, x_453);
if (x_454 == 0)
{
lean_object* x_455; uint8_t x_456; 
x_455 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12;
lean_inc(x_1);
x_456 = l_Lean_Syntax_isOfKind(x_1, x_455);
if (x_456 == 0)
{
lean_object* x_457; 
x_457 = lean_box(0);
x_199 = x_457;
goto block_451;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; 
x_458 = l_Lean_Syntax_getArgs(x_1);
x_459 = lean_array_get_size(x_458);
lean_dec(x_458);
x_460 = lean_unsigned_to_nat(3u);
x_461 = lean_nat_dec_eq(x_459, x_460);
lean_dec(x_459);
if (x_461 == 0)
{
lean_object* x_462; 
x_462 = lean_box(0);
x_199 = x_462;
goto block_451;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_463 = lean_unsigned_to_nat(0u);
x_464 = l_Lean_Syntax_getArg(x_1, x_463);
x_465 = l_Lean_identKind___closed__2;
x_466 = l_Lean_Syntax_isOfKind(x_464, x_465);
if (x_466 == 0)
{
lean_object* x_467; 
x_467 = lean_box(0);
x_17 = x_467;
goto block_195;
}
else
{
lean_object* x_468; lean_object* x_469; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_468 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__6;
x_469 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_468, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_469;
}
}
}
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; uint8_t x_473; 
x_470 = l_Lean_Syntax_getArgs(x_1);
x_471 = lean_array_get_size(x_470);
lean_dec(x_470);
x_472 = lean_unsigned_to_nat(4u);
x_473 = lean_nat_dec_eq(x_471, x_472);
if (x_473 == 0)
{
lean_object* x_474; uint8_t x_475; 
x_474 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12;
lean_inc(x_1);
x_475 = l_Lean_Syntax_isOfKind(x_1, x_474);
if (x_475 == 0)
{
lean_object* x_476; 
lean_dec(x_471);
x_476 = lean_box(0);
x_199 = x_476;
goto block_451;
}
else
{
lean_object* x_477; uint8_t x_478; 
x_477 = lean_unsigned_to_nat(3u);
x_478 = lean_nat_dec_eq(x_471, x_477);
lean_dec(x_471);
if (x_478 == 0)
{
lean_object* x_479; 
x_479 = lean_box(0);
x_199 = x_479;
goto block_451;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; 
x_480 = lean_unsigned_to_nat(0u);
x_481 = l_Lean_Syntax_getArg(x_1, x_480);
x_482 = l_Lean_identKind___closed__2;
x_483 = l_Lean_Syntax_isOfKind(x_481, x_482);
if (x_483 == 0)
{
lean_object* x_484; 
x_484 = lean_box(0);
x_17 = x_484;
goto block_195;
}
else
{
lean_object* x_485; lean_object* x_486; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_485 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__6;
x_486 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_485, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_486;
}
}
}
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_471);
x_487 = lean_unsigned_to_nat(0u);
x_488 = l_Lean_Syntax_getArg(x_1, x_487);
x_489 = lean_unsigned_to_nat(2u);
x_490 = l_Lean_Syntax_getArg(x_1, x_489);
lean_dec(x_1);
x_491 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_491, 0, x_490);
x_492 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_492, 0, x_491);
lean_ctor_set(x_492, 1, x_2);
x_1 = x_488;
x_2 = x_492;
goto _start;
}
}
}
block_520:
{
lean_object* x_496; uint8_t x_497; 
lean_dec(x_495);
x_496 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__15;
lean_inc(x_1);
x_497 = l_Lean_Syntax_isOfKind(x_1, x_496);
if (x_497 == 0)
{
lean_object* x_498; 
x_498 = lean_box(0);
x_452 = x_498;
goto block_494;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; 
x_499 = l_Lean_Syntax_getArgs(x_1);
x_500 = lean_array_get_size(x_499);
lean_dec(x_499);
x_501 = lean_unsigned_to_nat(3u);
x_502 = lean_nat_dec_eq(x_500, x_501);
lean_dec(x_500);
if (x_502 == 0)
{
lean_object* x_503; 
x_503 = lean_box(0);
x_452 = x_503;
goto block_494;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_504 = lean_unsigned_to_nat(0u);
x_505 = l_Lean_Syntax_getArg(x_1, x_504);
x_506 = lean_unsigned_to_nat(2u);
x_507 = l_Lean_Syntax_getArg(x_1, x_506);
lean_dec(x_1);
x_508 = l_Lean_Elab_Term_getCurrMacroScope(x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_509 = lean_ctor_get(x_508, 1);
lean_inc(x_509);
lean_dec(x_508);
x_510 = l_Lean_Elab_Term_getMainModule___rarg(x_15, x_509);
x_511 = lean_ctor_get(x_510, 1);
lean_inc(x_511);
lean_dec(x_510);
x_512 = l_Array_empty___closed__1;
x_513 = lean_array_push(x_512, x_505);
x_514 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__16;
x_515 = lean_array_push(x_513, x_514);
x_516 = lean_array_push(x_515, x_507);
x_517 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__13;
x_518 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_516);
x_1 = x_518;
x_16 = x_511;
goto _start;
}
}
}
}
else
{
lean_object* x_732; uint8_t x_733; 
x_732 = l_Lean_Syntax_getArgs(x_1);
x_733 = !lean_is_exclusive(x_10);
if (x_733 == 0)
{
uint8_t x_734; lean_object* x_735; lean_object* x_736; 
x_734 = 0;
lean_ctor_set_uint8(x_10, sizeof(void*)*8 + 1, x_734);
x_735 = lean_unsigned_to_nat(0u);
x_736 = l_Array_iterateMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_732, x_735, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_732);
lean_dec(x_1);
return x_736;
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; uint8_t x_745; uint8_t x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
x_737 = lean_ctor_get(x_10, 0);
x_738 = lean_ctor_get(x_10, 1);
x_739 = lean_ctor_get(x_10, 2);
x_740 = lean_ctor_get(x_10, 3);
x_741 = lean_ctor_get(x_10, 4);
x_742 = lean_ctor_get(x_10, 5);
x_743 = lean_ctor_get(x_10, 6);
x_744 = lean_ctor_get(x_10, 7);
x_745 = lean_ctor_get_uint8(x_10, sizeof(void*)*8);
lean_inc(x_744);
lean_inc(x_743);
lean_inc(x_742);
lean_inc(x_741);
lean_inc(x_740);
lean_inc(x_739);
lean_inc(x_738);
lean_inc(x_737);
lean_dec(x_10);
x_746 = 0;
x_747 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_747, 0, x_737);
lean_ctor_set(x_747, 1, x_738);
lean_ctor_set(x_747, 2, x_739);
lean_ctor_set(x_747, 3, x_740);
lean_ctor_set(x_747, 4, x_741);
lean_ctor_set(x_747, 5, x_742);
lean_ctor_set(x_747, 6, x_743);
lean_ctor_set(x_747, 7, x_744);
lean_ctor_set_uint8(x_747, sizeof(void*)*8, x_745);
lean_ctor_set_uint8(x_747, sizeof(void*)*8 + 1, x_746);
x_748 = lean_unsigned_to_nat(0u);
x_749 = l_Array_iterateMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_732, x_748, x_9, x_747, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_732);
lean_dec(x_1);
return x_749;
}
}
block_195:
{
uint8_t x_18; uint8_t x_19; 
lean_dec(x_17);
x_18 = l_List_isEmpty___rarg(x_2);
if (x_8 == 0)
{
uint8_t x_193; 
x_193 = 1;
x_19 = x_193;
goto block_192;
}
else
{
uint8_t x_194; 
x_194 = 0;
x_19 = x_194;
goto block_192;
}
block_192:
{
lean_object* x_20; 
if (x_18 == 0)
{
lean_object* x_99; 
x_99 = lean_box(0);
x_20 = x_99;
goto block_98;
}
else
{
uint8_t x_100; 
x_100 = l_Array_isEmpty___rarg(x_3);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_box(0);
x_20 = x_101;
goto block_98;
}
else
{
uint8_t x_102; 
x_102 = l_Array_isEmpty___rarg(x_4);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = lean_box(0);
x_20 = x_103;
goto block_98;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (x_8 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_131; lean_object* x_132; 
x_104 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_131 = 1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_132 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_131, x_10, x_11, x_12, x_13, x_14, x_15, x_106);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_dec(x_107);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Elab_Term_SavedState_restore(x_105, x_10, x_11, x_12, x_13, x_14, x_15, x_137);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_138, 1);
x_141 = lean_ctor_get(x_138, 0);
lean_dec(x_141);
lean_ctor_set(x_138, 1, x_136);
lean_ctor_set(x_138, 0, x_133);
x_142 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_138, x_10, x_11, x_12, x_13, x_14, x_15, x_140);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_138, 1);
lean_inc(x_143);
lean_dec(x_138);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_133);
lean_ctor_set(x_144, 1, x_136);
x_145 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_144, x_10, x_11, x_12, x_13, x_14, x_15, x_143);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_132, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_132, 1);
lean_inc(x_147);
lean_dec(x_132);
x_108 = x_146;
x_109 = x_147;
goto block_130;
}
block_130:
{
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
lean_dec(x_107);
x_110 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = l_Lean_Elab_Term_SavedState_restore(x_105, x_10, x_11, x_12, x_13, x_14, x_15, x_112);
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_113, 1);
x_116 = lean_ctor_get(x_113, 0);
lean_dec(x_116);
lean_ctor_set_tag(x_113, 1);
lean_ctor_set(x_113, 1, x_111);
lean_ctor_set(x_113, 0, x_108);
x_117 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_113, x_10, x_11, x_12, x_13, x_14, x_15, x_115);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_113, 1);
lean_inc(x_118);
lean_dec(x_113);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_108);
lean_ctor_set(x_119, 1, x_111);
x_120 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_119, x_10, x_11, x_12, x_13, x_14, x_15, x_118);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; 
lean_dec(x_9);
x_121 = lean_ctor_get(x_108, 0);
lean_inc(x_121);
x_122 = l_Lean_Elab_postponeExceptionId;
x_123 = lean_nat_dec_eq(x_121, x_122);
lean_dec(x_121);
if (x_123 == 0)
{
lean_object* x_124; 
lean_dec(x_105);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_107)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_107;
 lean_ctor_set_tag(x_124, 1);
}
lean_ctor_set(x_124, 0, x_108);
lean_ctor_set(x_124, 1, x_109);
return x_124;
}
else
{
lean_object* x_125; uint8_t x_126; 
lean_dec(x_107);
x_125 = l_Lean_Elab_Term_SavedState_restore(x_105, x_10, x_11, x_12, x_13, x_14, x_15, x_109);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_125, 0);
lean_dec(x_127);
lean_ctor_set_tag(x_125, 1);
lean_ctor_set(x_125, 0, x_108);
return x_125;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_108);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_176; 
x_148 = lean_box(0);
x_149 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
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
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_176 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_19, x_148, x_10, x_11, x_12, x_13, x_14, x_15, x_151);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
lean_dec(x_152);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = l_Lean_Elab_Term_SavedState_restore(x_150, x_10, x_11, x_12, x_13, x_14, x_15, x_181);
x_183 = !lean_is_exclusive(x_182);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_182, 1);
x_185 = lean_ctor_get(x_182, 0);
lean_dec(x_185);
lean_ctor_set(x_182, 1, x_180);
lean_ctor_set(x_182, 0, x_177);
x_186 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_182, x_10, x_11, x_12, x_13, x_14, x_15, x_184);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_182, 1);
lean_inc(x_187);
lean_dec(x_182);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_177);
lean_ctor_set(x_188, 1, x_180);
x_189 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_188, x_10, x_11, x_12, x_13, x_14, x_15, x_187);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_176, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_176, 1);
lean_inc(x_191);
lean_dec(x_176);
x_153 = x_190;
x_154 = x_191;
goto block_175;
}
block_175:
{
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
lean_dec(x_152);
x_155 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l_Lean_Elab_Term_SavedState_restore(x_150, x_10, x_11, x_12, x_13, x_14, x_15, x_157);
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_158, 1);
x_161 = lean_ctor_get(x_158, 0);
lean_dec(x_161);
lean_ctor_set_tag(x_158, 1);
lean_ctor_set(x_158, 1, x_156);
lean_ctor_set(x_158, 0, x_153);
x_162 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_158, x_10, x_11, x_12, x_13, x_14, x_15, x_160);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_158, 1);
lean_inc(x_163);
lean_dec(x_158);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_153);
lean_ctor_set(x_164, 1, x_156);
x_165 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_9, x_164, x_10, x_11, x_12, x_13, x_14, x_15, x_163);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
lean_dec(x_9);
x_166 = lean_ctor_get(x_153, 0);
lean_inc(x_166);
x_167 = l_Lean_Elab_postponeExceptionId;
x_168 = lean_nat_dec_eq(x_166, x_167);
lean_dec(x_166);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_150);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_152)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_152;
 lean_ctor_set_tag(x_169, 1);
}
lean_ctor_set(x_169, 0, x_153);
lean_ctor_set(x_169, 1, x_154);
return x_169;
}
else
{
lean_object* x_170; uint8_t x_171; 
lean_dec(x_152);
x_170 = l_Lean_Elab_Term_SavedState_restore(x_150, x_10, x_11, x_12, x_13, x_14, x_15, x_154);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_170, 0);
lean_dec(x_172);
lean_ctor_set_tag(x_170, 1);
lean_ctor_set(x_170, 0, x_153);
return x_170;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec(x_170);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_153);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
}
}
}
}
block_98:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_58; lean_object* x_59; lean_object* x_81; 
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_16);
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
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_81 = l_Lean_Elab_Term_elabTerm(x_1, x_21, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_24);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
x_84 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_83);
if (lean_obj_tag(x_84) == 0)
{
if (x_8 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_25);
lean_dec(x_5);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_58 = x_85;
x_59 = x_86;
goto block_80;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_89 = l_Lean_Elab_Term_ensureHasType(x_5, x_87, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_25);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_58 = x_90;
x_59 = x_91;
goto block_80;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
lean_dec(x_89);
x_26 = x_92;
x_27 = x_93;
goto block_57;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_5);
x_94 = lean_ctor_get(x_84, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_84, 1);
lean_inc(x_95);
lean_dec(x_84);
x_26 = x_94;
x_27 = x_95;
goto block_57;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = lean_ctor_get(x_81, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_81, 1);
lean_inc(x_97);
lean_dec(x_81);
x_26 = x_96;
x_27 = x_97;
goto block_57;
}
block_57:
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_28; uint8_t x_29; 
lean_dec(x_25);
x_28 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_27);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = l_Lean_Elab_Term_SavedState_restore(x_23, x_10, x_11, x_12, x_13, x_14, x_15, x_31);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 1);
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 0, x_26);
x_36 = lean_array_push(x_9, x_32);
lean_ctor_set(x_28, 1, x_34);
lean_ctor_set(x_28, 0, x_36);
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_30);
x_39 = lean_array_push(x_9, x_38);
lean_ctor_set(x_28, 1, x_37);
lean_ctor_set(x_28, 0, x_39);
return x_28;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_28, 0);
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_28);
x_42 = l_Lean_Elab_Term_SavedState_restore(x_23, x_10, x_11, x_12, x_13, x_14, x_15, x_41);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
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
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
 lean_ctor_set_tag(x_45, 1);
}
lean_ctor_set(x_45, 0, x_26);
lean_ctor_set(x_45, 1, x_40);
x_46 = lean_array_push(x_9, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_9);
x_48 = lean_ctor_get(x_26, 0);
lean_inc(x_48);
x_49 = l_Lean_Elab_postponeExceptionId;
x_50 = lean_nat_dec_eq(x_48, x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
if (lean_is_scalar(x_25)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_25;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_26);
lean_ctor_set(x_51, 1, x_27);
return x_51;
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_25);
x_52 = l_Lean_Elab_Term_SavedState_restore(x_23, x_10, x_11, x_12, x_13, x_14, x_15, x_27);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set_tag(x_52, 1);
lean_ctor_set(x_52, 0, x_26);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_26);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
block_80:
{
lean_object* x_60; uint8_t x_61; 
x_60 = l_Lean_Elab_Term_saveAllState___rarg(x_11, x_12, x_13, x_14, x_15, x_59);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
x_64 = l_Lean_Elab_Term_SavedState_restore(x_23, x_10, x_11, x_12, x_13, x_14, x_15, x_63);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 1);
x_67 = lean_ctor_get(x_64, 0);
lean_dec(x_67);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 0, x_58);
x_68 = lean_array_push(x_9, x_64);
lean_ctor_set(x_60, 1, x_66);
lean_ctor_set(x_60, 0, x_68);
return x_60;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_dec(x_64);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_58);
lean_ctor_set(x_70, 1, x_62);
x_71 = lean_array_push(x_9, x_70);
lean_ctor_set(x_60, 1, x_69);
lean_ctor_set(x_60, 0, x_71);
return x_60;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_72 = lean_ctor_get(x_60, 0);
x_73 = lean_ctor_get(x_60, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_60);
x_74 = l_Lean_Elab_Term_SavedState_restore(x_23, x_10, x_11, x_12, x_13, x_14, x_15, x_73);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_58);
lean_ctor_set(x_77, 1, x_72);
x_78 = lean_array_push(x_9, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_75);
return x_79;
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
lean_object* l_Array_iterateMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3___boxed(lean_object** _args) {
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
x_20 = l_Array_iterateMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(x_1, x_2, x_3, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
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
lean_object* l_Array_filterAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l_Array_shrink___rarg(x_1, x_3);
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
x_3 = l_Array_filterAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___spec__1(x_1, x_2, x_2);
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
x_1 = l___private_Init_Util_0__mkPanicMessage___closed__2;
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
x_22 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
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
x_30 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_CheckAssignment_addAssignmentInfo___rarg___closed__3;
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
x_49 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
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
x_57 = l___private_Lean_Meta_ExprDefEq_0__Lean_Meta_CheckAssignment_addAssignmentInfo___rarg___closed__3;
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
static lean_object* _init_l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.App");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.App.0.Lean.Elab.Term.mergeFailures");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1;
x_2 = l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2;
x_3 = lean_unsigned_to_nat(784u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_19 = l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3;
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
x_11 = lean_alloc_closure((void*)(l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1), 9, 2);
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
x_19 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
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
static lean_object* _init_l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.App.0.Lean.Elab.Term.elabAppAux");
return x_1;
}
}
static lean_object* _init_l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1;
x_2 = l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(802u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_27 = l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2;
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
x_23 = l_Array_filterAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___spec__1(x_17, x_22, x_22);
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
x_41 = l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1(x_38, x_39, x_22, x_40);
x_42 = x_41;
x_43 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageList(x_42);
lean_dec(x_42);
x_44 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
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
static lean_object* _init_l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namedArgument");
return x_1;
}
}
static lean_object* _init_l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected '..'");
return x_1;
}
}
static lean_object* _init_l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_24 = l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__1;
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
x_31 = l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
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
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_17);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_43, 2, x_42);
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
x_55 = l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__1;
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
x_63 = l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
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
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_17);
lean_ctor_set(x_75, 1, x_71);
lean_ctor_set(x_75, 2, x_74);
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
x_23 = l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1(x_20, x_21, x_18, x_18, x_10, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_51 = l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1(x_48, x_49, x_46, x_46, x_10, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_object* l_Lean_Meta_withoutPostponingUniverseConstraintsImp___at_Lean_Elab_Term_elabApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getResetPostponed(x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 0;
lean_inc(x_7);
lean_inc(x_3);
x_14 = l_Lean_Elab_Term_expandApp(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux(x_19, x_20, x_21, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed(x_13, x_5, x_6, x_7, x_8, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_25);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Lean_Meta_getPostponed___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getNumPostponed___spec__1___rarg(x_6, x_7, x_8, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_MessageData_nil;
x_35 = l_Std_PersistentArray_forIn___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponedToMessageData___spec__1(x_32, x_34);
lean_dec(x_32);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Meta_withoutPostponingUniverseConstraintsImp___rarg___closed__12;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at_Lean_Meta_getMVarDecl___spec__1___rarg(x_41, x_5, x_6, x_7, x_8, x_33);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_setPostponed___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getResetPostponed___spec__1(x_11, x_5, x_6, x_7, x_8, x_44);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_27, 1);
lean_inc(x_50);
lean_dec(x_27);
x_51 = lean_box(0);
x_52 = l_Lean_Meta_withoutPostponingUniverseConstraintsImp___at_Lean_Elab_Term_elabBinders___spec__2___rarg___lambda__1(x_11, x_25, x_51, x_5, x_6, x_7, x_8, x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_25);
x_53 = lean_ctor_get(x_27, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_27, 1);
lean_inc(x_54);
lean_dec(x_27);
x_55 = l_Lean_Meta_setPostponed___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getResetPostponed___spec__1(x_11, x_5, x_6, x_7, x_8, x_54);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set_tag(x_55, 1);
lean_ctor_set(x_55, 0, x_53);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_24, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_24, 1);
lean_inc(x_61);
lean_dec(x_24);
x_62 = l_Lean_Meta_setPostponed___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getResetPostponed___spec__1(x_11, x_5, x_6, x_7, x_8, x_61);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 0, x_60);
return x_62;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = lean_ctor_get(x_14, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_14, 1);
lean_inc(x_68);
lean_dec(x_14);
x_69 = l_Lean_Meta_setPostponed___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getResetPostponed___spec__1(x_11, x_5, x_6, x_7, x_8, x_68);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 0, x_67);
return x_69;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
lean_object* l_Lean_Elab_Term_elabApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withoutPostponingUniverseConstraintsImp___at_Lean_Elab_Term_elabApp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
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
lean_object* l_Lean_Meta_withoutPostponingUniverseConstraintsImp___at_Lean_Elab_Term_elabApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_withoutPostponingUniverseConstraintsImp___at_Lean_Elab_Term_elabApp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
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
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_7432_(lean_object* x_1) {
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
l_Lean_Elab_Term_NamedArg_ref___default = _init_l_Lean_Elab_Term_NamedArg_ref___default();
lean_mark_persistent(l_Lean_Elab_Term_NamedArg_ref___default);
l_Lean_Elab_Term_Lean_Elab_App___instance__4___closed__1 = _init_l_Lean_Elab_Term_Lean_Elab_App___instance__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_App___instance__4___closed__1);
l_Lean_Elab_Term_Lean_Elab_App___instance__4 = _init_l_Lean_Elab_Term_Lean_Elab_App___instance__4();
lean_mark_persistent(l_Lean_Elab_Term_Lean_Elab_App___instance__4);
l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__1 = _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__1);
l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2 = _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__2);
l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__3 = _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__3);
l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__4 = _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__4);
l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__5 = _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__5);
l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__6 = _init_l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_throwInvalidNamedArg___rarg___closed__6);
l_Lean_Elab_Term_addNamedArg___closed__1 = _init_l_Lean_Elab_Term_addNamedArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__1);
l_Lean_Elab_Term_addNamedArg___closed__2 = _init_l_Lean_Elab_Term_addNamedArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__2);
l_Lean_Elab_Term_addNamedArg___closed__3 = _init_l_Lean_Elab_Term_addNamedArg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__3);
l_Lean_Elab_Term_addNamedArg___closed__4 = _init_l_Lean_Elab_Term_addNamedArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_addNamedArg___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_x3f___closed__4);
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
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___closed__4);
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
l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1 = _init_l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1);
l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2 = _init_l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2();
lean_mark_persistent(l_List_forIn_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__4 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__4);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__5 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__5);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__6 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___lambda__1___closed__6);
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
l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1 = _init_l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1);
l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2 = _init_l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2);
l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3 = _init_l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3();
lean_mark_persistent(l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__2);
l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1 = _init_l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__1);
l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2 = _init_l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2);
l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__1 = _init_l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__1();
lean_mark_persistent(l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__1);
l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__2 = _init_l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__2();
lean_mark_persistent(l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__2);
l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__3 = _init_l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__3();
lean_mark_persistent(l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__3);
l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__4 = _init_l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__4();
lean_mark_persistent(l_Array_iterateMAux___at_Lean_Elab_Term_expandApp___spec__1___closed__4);
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
res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_7432_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
