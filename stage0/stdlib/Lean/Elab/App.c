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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__1;
lean_object* l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Basic_27__withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___rarg___closed__1;
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Syntax_getSepArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_Term_0__Lean_Elab_Term_isTypeApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2;
extern lean_object* l_Lean_fieldIdxKind___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__3(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__5;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__15;
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___boxed(lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__11;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__2___rarg(lean_object*, lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l_List_map___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(lean_object*);
extern lean_object* l_Std_HashMap_inhabited___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___closed__3;
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_InferType_22__isTypeFormerTypeImp___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
lean_object* l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__2(lean_object*);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__3;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__4(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_match__1(lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__10;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_goalsToMessageData___closed__1;
lean_object* l_Lean_Elab_Term_elabApp_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__3;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getBindingName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess___boxed(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_hasToString(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess(lean_object*);
lean_object* l_List_find_x3f___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__2(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__2;
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__3(lean_object*);
lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___closed__1;
uint8_t l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__1;
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_InferType_4__getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__4___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__2(lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__2;
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
lean_object* l_Lean_Meta_setMCtx___at___private_Lean_Meta_Basic_6__liftMkBindingM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures(lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_Arg_hasToString_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_inhabited;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__4;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp_match__1(lean_object*);
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandDollarProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__1;
uint8_t l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_6__liftMkBindingM___rarg___closed__3;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_fTypeHasOptAutoParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__7;
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object*, lean_object*);
extern lean_object* l_ULift_HasRepr___rarg___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2___closed__3;
lean_object* l_Lean_Elab_Term_addNamedArg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__3;
extern lean_object* l_Lean_Meta_isExprDefEq___rarg___closed__2;
uint8_t l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize_match__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getBindingName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__5;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__1(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3;
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind___closed__2;
extern lean_object* l_Lean_MessageData_Inhabited;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___at___private_Lean_Elab_Term_0__Lean_Elab_Term_exceptionToSorry___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__2;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processInstImplicitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__1(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__1;
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_mkTypeMismatchError___closed__6;
lean_object* l_Lean_Elab_Term_expandApp_match__3___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_hasToString(lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__11;
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___closed__4;
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__7;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit(lean_object*);
extern lean_object* l_Lean_Meta_inferTypeRef;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__16;
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__4(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__3___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1___boxed(lean_object**);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_State_instMVars___default;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData_match__1(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern(lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice(lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasArgsToProcess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_State_toSetErrorCtx___default;
lean_object* l___private_Lean_CoreM_1__mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_hasToString_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_Elab_Term_elabApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__13;
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__2___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__1;
lean_object* l_Lean_Elab_Term_expandApp___closed__4;
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
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__10;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_elabChoice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_Iterator_HasRepr___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__2(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1___closed__2;
lean_object* l___private_Lean_Meta_Basic_20__forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__15;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_expandDollarProj___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__16;
extern lean_object* l_Lean_importModules___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__1(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__6;
extern lean_object* l_Lean_formatEntry___closed__1;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_TermElabResult_inhabited;
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
lean_object* l_Lean_MessageData_joinSep___main(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageList(lean_object*);
lean_object* l_Lean_Name_replacePrefix___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__5;
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___boxed(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__14;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__3(uint8_t);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Term_elabProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Elab_Term_expandApp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__5(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_Lean_Elab_setMacroStackOption(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__4(lean_object*);
extern lean_object* l_ReaderT_monadControl___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__1;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__3(lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_15__runDefEqM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__2;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__5;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Elab_Term_expandApp_match__3(lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2(lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getParentStructures(lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__29;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_isSuccess_match__1(lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
extern lean_object* l_Lean_Elab_postponeExceptionId;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures_match__1(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___spec__1___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__3(lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_saveAllState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__1(lean_object*);
lean_object* l_Lean_Meta_throwUnknownFVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___closed__2;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__12;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__6;
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___boxed(lean_object**);
lean_object* l_Lean_Elab_Term_ElabAppArgs_State_etaArgs___default;
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_0__Lean_Elab_Term_isExplicit___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2(lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
extern lean_object* l_Lean_Meta_whnfRef;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId_match__1(lean_object*);
lean_object* l_Lean_Exception_getRef(lean_object*);
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__6;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicitUnivs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__4(lean_object*);
extern lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope___closed__3;
lean_object* l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__5;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_7346_(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__2(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___main___at_Lean_Elab_Term_ElabAppArgs_eraseNamedArgCore___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__2;
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___rarg(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData___main(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__9;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1;
lean_object* l_Lean_Elab_Term_registerSyntheticMVarWithCurrRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__3(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isDefEqBindingDomain___main___closed__2;
lean_object* l_Lean_Elab_Term_Arg_inhabited___closed__1;
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__3(lean_object*);
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__4___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__13;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabApp_match__1(lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__1;
lean_object* l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrow___at___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
lean_object* l_Lean_Elab_Term_registerMVarErrorImplicitArgInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__8;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__2;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__2;
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__1;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole_match__1(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__4;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__11;
extern lean_object* l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__5;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
lean_object* l_Lean_Elab_Term_expandApp___closed__5;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_applyResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__9;
lean_object* l_Lean_Meta_getLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody_match__2(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ensureArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
lean_object* l_Lean_Elab_Term_expandApp___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__2;
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_301____closed__4;
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__6;
lean_object* l_Lean_Elab_Term_expandApp___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__14;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_findField_x3f___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_ElabAppArgs_State_alreadyPropagated___default;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux___closed__4;
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Tactic_evalTacticSeqBracketed___closed__2;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_inhabited;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___closed__1;
extern lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_907____closed__1;
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop_match__3(lean_object*);
extern lean_object* l_Lean_Meta_mkArrow___rarg___closed__2;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg_match__3___rarg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Term_Arg_hasToString_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Term_Arg_hasToString_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Arg_hasToString_match__1___rarg), 3, 0);
return x_2;
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
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("function expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeFun");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__4;
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
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__3;
x_15 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_7);
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__5;
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
x_38 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_36, x_37, x_19, x_5, x_6, x_7, x_8, x_25);
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
x_59 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
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
x_67 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__3;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 7);
x_11 = l_Array_empty___closed__1;
lean_ctor_set(x_1, 7, x_11);
x_12 = l_Lean_Elab_Term_synthesizeAppInstMVars(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
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
lean_ctor_set(x_18, 1, x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*9);
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_1, 2);
x_28 = lean_ctor_get(x_1, 3);
x_29 = lean_ctor_get(x_1, 4);
x_30 = lean_ctor_get(x_1, 5);
x_31 = lean_ctor_get(x_1, 6);
x_32 = lean_ctor_get(x_1, 7);
x_33 = lean_ctor_get(x_1, 8);
x_34 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 1);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_35 = l_Array_empty___closed__1;
x_36 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_26);
lean_ctor_set(x_36, 2, x_27);
lean_ctor_set(x_36, 3, x_28);
lean_ctor_set(x_36, 4, x_29);
lean_ctor_set(x_36, 5, x_30);
lean_ctor_set(x_36, 6, x_31);
lean_ctor_set(x_36, 7, x_35);
lean_ctor_set(x_36, 8, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*9, x_24);
lean_ctor_set_uint8(x_36, sizeof(void*)*9 + 1, x_34);
x_37 = l_Lean_Elab_Term_synthesizeAppInstMVars(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_32);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_36);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_36);
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
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
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_15 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
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
x_18 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__1(x_17, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 7)
{
uint8_t x_21; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_18, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_22, 1);
lean_dec(x_27);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_19, 0, x_14);
return x_18;
}
else
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_28 = lean_ctor_get_uint8(x_22, sizeof(void*)*9);
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 2);
x_31 = lean_ctor_get(x_22, 3);
x_32 = lean_ctor_get(x_22, 4);
x_33 = lean_ctor_get(x_22, 5);
x_34 = lean_ctor_get(x_22, 6);
x_35 = lean_ctor_get(x_22, 7);
x_36 = lean_ctor_get(x_22, 8);
x_37 = lean_ctor_get_uint8(x_22, sizeof(void*)*9 + 1);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_38 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_20);
lean_ctor_set(x_38, 2, x_30);
lean_ctor_set(x_38, 3, x_31);
lean_ctor_set(x_38, 4, x_32);
lean_ctor_set(x_38, 5, x_33);
lean_ctor_set(x_38, 6, x_34);
lean_ctor_set(x_38, 7, x_35);
lean_ctor_set(x_38, 8, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*9, x_28);
lean_ctor_set_uint8(x_38, sizeof(void*)*9 + 1, x_37);
lean_ctor_set(x_19, 1, x_38);
lean_ctor_set(x_19, 0, x_14);
return x_18;
}
}
else
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_dec(x_18);
x_40 = lean_ctor_get_uint8(x_22, sizeof(void*)*9);
x_41 = lean_ctor_get(x_22, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_22, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_22, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_22, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_22, 5);
lean_inc(x_45);
x_46 = lean_ctor_get(x_22, 6);
lean_inc(x_46);
x_47 = lean_ctor_get(x_22, 7);
lean_inc(x_47);
x_48 = lean_ctor_get(x_22, 8);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_22, sizeof(void*)*9 + 1);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 lean_ctor_release(x_22, 4);
 lean_ctor_release(x_22, 5);
 lean_ctor_release(x_22, 6);
 lean_ctor_release(x_22, 7);
 lean_ctor_release(x_22, 8);
 x_50 = x_22;
} else {
 lean_dec_ref(x_22);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 9, 2);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set(x_51, 1, x_20);
lean_ctor_set(x_51, 2, x_42);
lean_ctor_set(x_51, 3, x_43);
lean_ctor_set(x_51, 4, x_44);
lean_ctor_set(x_51, 5, x_45);
lean_ctor_set(x_51, 6, x_46);
lean_ctor_set(x_51, 7, x_47);
lean_ctor_set(x_51, 8, x_48);
lean_ctor_set_uint8(x_51, sizeof(void*)*9, x_40);
lean_ctor_set_uint8(x_51, sizeof(void*)*9 + 1, x_49);
lean_ctor_set(x_19, 1, x_51);
lean_ctor_set(x_19, 0, x_14);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_19);
lean_ctor_set(x_52, 1, x_39);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_53 = lean_ctor_get(x_19, 1);
lean_inc(x_53);
lean_dec(x_19);
x_54 = lean_ctor_get(x_18, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_55 = x_18;
} else {
 lean_dec_ref(x_18);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get_uint8(x_53, sizeof(void*)*9);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_53, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 4);
lean_inc(x_60);
x_61 = lean_ctor_get(x_53, 5);
lean_inc(x_61);
x_62 = lean_ctor_get(x_53, 6);
lean_inc(x_62);
x_63 = lean_ctor_get(x_53, 7);
lean_inc(x_63);
x_64 = lean_ctor_get(x_53, 8);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_53, sizeof(void*)*9 + 1);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 lean_ctor_release(x_53, 3);
 lean_ctor_release(x_53, 4);
 lean_ctor_release(x_53, 5);
 lean_ctor_release(x_53, 6);
 lean_ctor_release(x_53, 7);
 lean_ctor_release(x_53, 8);
 x_66 = x_53;
} else {
 lean_dec_ref(x_53);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 9, 2);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_57);
lean_ctor_set(x_67, 1, x_20);
lean_ctor_set(x_67, 2, x_58);
lean_ctor_set(x_67, 3, x_59);
lean_ctor_set(x_67, 4, x_60);
lean_ctor_set(x_67, 5, x_61);
lean_ctor_set(x_67, 6, x_62);
lean_ctor_set(x_67, 7, x_63);
lean_ctor_set(x_67, 8, x_64);
lean_ctor_set_uint8(x_67, sizeof(void*)*9, x_56);
lean_ctor_set_uint8(x_67, sizeof(void*)*9 + 1, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_14);
lean_ctor_set(x_68, 1, x_67);
if (lean_is_scalar(x_55)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_55;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_54);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_18, 1);
lean_inc(x_70);
lean_dec(x_18);
x_71 = lean_ctor_get(x_19, 1);
lean_inc(x_71);
lean_dec(x_19);
x_72 = lean_ctor_get(x_12, 0);
lean_inc(x_72);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_73 = l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun(x_20, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_74);
x_76 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3(x_74, x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_75);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
x_79 = !lean_is_exclusive(x_76);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_76, 0);
lean_dec(x_80);
x_81 = !lean_is_exclusive(x_77);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_77, 0);
x_83 = lean_ctor_get(x_77, 1);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_78);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_78, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_78, 0);
lean_dec(x_86);
lean_ctor_set(x_78, 1, x_82);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_77, 0, x_14);
return x_76;
}
else
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_87 = lean_ctor_get_uint8(x_78, sizeof(void*)*9);
x_88 = lean_ctor_get(x_78, 2);
x_89 = lean_ctor_get(x_78, 3);
x_90 = lean_ctor_get(x_78, 4);
x_91 = lean_ctor_get(x_78, 5);
x_92 = lean_ctor_get(x_78, 6);
x_93 = lean_ctor_get(x_78, 7);
x_94 = lean_ctor_get(x_78, 8);
x_95 = lean_ctor_get_uint8(x_78, sizeof(void*)*9 + 1);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_78);
x_96 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_96, 0, x_74);
lean_ctor_set(x_96, 1, x_82);
lean_ctor_set(x_96, 2, x_88);
lean_ctor_set(x_96, 3, x_89);
lean_ctor_set(x_96, 4, x_90);
lean_ctor_set(x_96, 5, x_91);
lean_ctor_set(x_96, 6, x_92);
lean_ctor_set(x_96, 7, x_93);
lean_ctor_set(x_96, 8, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*9, x_87);
lean_ctor_set_uint8(x_96, sizeof(void*)*9 + 1, x_95);
lean_ctor_set(x_77, 1, x_96);
lean_ctor_set(x_77, 0, x_14);
return x_76;
}
}
else
{
lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_97 = lean_ctor_get(x_77, 0);
lean_inc(x_97);
lean_dec(x_77);
x_98 = lean_ctor_get_uint8(x_78, sizeof(void*)*9);
x_99 = lean_ctor_get(x_78, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_78, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_78, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_78, 5);
lean_inc(x_102);
x_103 = lean_ctor_get(x_78, 6);
lean_inc(x_103);
x_104 = lean_ctor_get(x_78, 7);
lean_inc(x_104);
x_105 = lean_ctor_get(x_78, 8);
lean_inc(x_105);
x_106 = lean_ctor_get_uint8(x_78, sizeof(void*)*9 + 1);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 lean_ctor_release(x_78, 4);
 lean_ctor_release(x_78, 5);
 lean_ctor_release(x_78, 6);
 lean_ctor_release(x_78, 7);
 lean_ctor_release(x_78, 8);
 x_107 = x_78;
} else {
 lean_dec_ref(x_78);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(0, 9, 2);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_74);
lean_ctor_set(x_108, 1, x_97);
lean_ctor_set(x_108, 2, x_99);
lean_ctor_set(x_108, 3, x_100);
lean_ctor_set(x_108, 4, x_101);
lean_ctor_set(x_108, 5, x_102);
lean_ctor_set(x_108, 6, x_103);
lean_ctor_set(x_108, 7, x_104);
lean_ctor_set(x_108, 8, x_105);
lean_ctor_set_uint8(x_108, sizeof(void*)*9, x_98);
lean_ctor_set_uint8(x_108, sizeof(void*)*9 + 1, x_106);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_14);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_76, 0, x_109);
return x_76;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_110 = lean_ctor_get(x_76, 1);
lean_inc(x_110);
lean_dec(x_76);
x_111 = lean_ctor_get(x_77, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_112 = x_77;
} else {
 lean_dec_ref(x_77);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get_uint8(x_78, sizeof(void*)*9);
x_114 = lean_ctor_get(x_78, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_78, 3);
lean_inc(x_115);
x_116 = lean_ctor_get(x_78, 4);
lean_inc(x_116);
x_117 = lean_ctor_get(x_78, 5);
lean_inc(x_117);
x_118 = lean_ctor_get(x_78, 6);
lean_inc(x_118);
x_119 = lean_ctor_get(x_78, 7);
lean_inc(x_119);
x_120 = lean_ctor_get(x_78, 8);
lean_inc(x_120);
x_121 = lean_ctor_get_uint8(x_78, sizeof(void*)*9 + 1);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 lean_ctor_release(x_78, 3);
 lean_ctor_release(x_78, 4);
 lean_ctor_release(x_78, 5);
 lean_ctor_release(x_78, 6);
 lean_ctor_release(x_78, 7);
 lean_ctor_release(x_78, 8);
 x_122 = x_78;
} else {
 lean_dec_ref(x_78);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 9, 2);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_74);
lean_ctor_set(x_123, 1, x_111);
lean_ctor_set(x_123, 2, x_114);
lean_ctor_set(x_123, 3, x_115);
lean_ctor_set(x_123, 4, x_116);
lean_ctor_set(x_123, 5, x_117);
lean_ctor_set(x_123, 6, x_118);
lean_ctor_set(x_123, 7, x_119);
lean_ctor_set(x_123, 8, x_120);
lean_ctor_set_uint8(x_123, sizeof(void*)*9, x_113);
lean_ctor_set_uint8(x_123, sizeof(void*)*9 + 1, x_121);
if (lean_is_scalar(x_112)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_112;
}
lean_ctor_set(x_124, 0, x_14);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_110);
return x_125;
}
}
else
{
uint8_t x_126; 
lean_dec(x_74);
x_126 = !lean_is_exclusive(x_76);
if (x_126 == 0)
{
return x_76;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_76, 0);
x_128 = lean_ctor_get(x_76, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_76);
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
lean_dec(x_71);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_130 = !lean_is_exclusive(x_73);
if (x_130 == 0)
{
return x_73;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_73, 0);
x_132 = lean_ctor_get(x_73, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_73);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_134 = !lean_is_exclusive(x_18);
if (x_134 == 0)
{
return x_18;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_18, 0);
x_136 = lean_ctor_get(x_18, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_18);
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
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_138 = !lean_is_exclusive(x_15);
if (x_138 == 0)
{
return x_15;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_15, 0);
x_140 = lean_ctor_get(x_15, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_15);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_142 = !lean_is_exclusive(x_9);
if (x_142 == 0)
{
return x_9;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_9, 0);
x_144 = lean_ctor_get(x_9, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_9);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
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
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__1(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getBindingName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_inc(x_4);
lean_inc(x_3);
x_22 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ensureArgType(x_21, x_19, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_23, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
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
lean_inc(x_4);
lean_inc(x_3);
x_39 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ensureArgType(x_38, x_37, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_40, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_19 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_fTypeHasOptAutoParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
x_11 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(x_9, x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
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
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_12 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_1, x_7, x_3);
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
x_20 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_1, x_15, x_3);
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
x_28 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_1, x_23, x_3);
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
x_43 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_1, x_31, x_3);
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
x_38 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_1, x_32, x_34);
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
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_12 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_1, x_7, x_3);
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
x_20 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_1, x_15, x_3);
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
x_28 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_1, x_23, x_3);
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
x_43 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_1, x_31, x_3);
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
x_38 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_1, x_32, x_34);
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
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_Lean_AddMessageContext___spec__1(x_2, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
x_36 = lean_ctor_get(x_17, 0);
lean_inc(x_36);
lean_dec(x_17);
x_37 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_13);
lean_inc(x_11);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_11);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Std_PersistentArray_push___rarg(x_36, x_38);
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_35);
lean_ctor_set(x_16, 3, x_40);
x_41 = lean_st_ref_set(x_9, x_16, x_18);
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
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_3);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_47 = lean_ctor_get(x_16, 0);
x_48 = lean_ctor_get(x_16, 1);
x_49 = lean_ctor_get(x_16, 2);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_16);
x_50 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
x_51 = lean_ctor_get(x_17, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_52 = x_17;
} else {
 lean_dec_ref(x_17);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_13);
lean_inc(x_11);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_11);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Std_PersistentArray_push___rarg(x_51, x_54);
if (lean_is_scalar(x_52)) {
 x_56 = lean_alloc_ctor(0, 1, 1);
} else {
 x_56 = x_52;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_50);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_47);
lean_ctor_set(x_57, 1, x_48);
lean_ctor_set(x_57, 2, x_49);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_st_ref_set(x_9, x_57, x_18);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_3);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_Lean_checkTraceOption(x_10, x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_907____closed__1;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_isLevelDefEqAux___main___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("etaArgs.size: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", numRemainingArgs: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", fType: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_486; 
x_486 = lean_ctor_get_uint8(x_1, sizeof(void*)*9);
if (x_486 == 0)
{
lean_object* x_487; lean_object* x_488; uint8_t x_489; uint8_t x_490; 
x_487 = lean_ctor_get(x_1, 5);
lean_inc(x_487);
x_488 = lean_ctor_get(x_1, 8);
lean_inc(x_488);
x_489 = lean_ctor_get_uint8(x_1, sizeof(void*)*9 + 1);
x_490 = l_Array_isEmpty___rarg(x_487);
lean_dec(x_487);
if (x_490 == 0)
{
uint8_t x_491; 
lean_dec(x_488);
x_491 = 1;
x_9 = x_491;
goto block_485;
}
else
{
if (x_489 == 0)
{
uint8_t x_492; 
x_492 = l_Array_isEmpty___rarg(x_488);
lean_dec(x_488);
x_9 = x_492;
goto block_485;
}
else
{
uint8_t x_493; 
lean_dec(x_488);
x_493 = 1;
x_9 = x_493;
goto block_485;
}
}
}
else
{
uint8_t x_494; 
x_494 = 1;
x_9 = x_494;
goto block_485;
}
block_485:
{
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_ctor_get(x_1, 5);
x_16 = lean_ctor_get(x_1, 8);
x_17 = 1;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_ctor_set_uint8(x_1, sizeof(void*)*9 + 1, x_17);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
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
x_18 = lean_box(0);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_272; lean_object* x_273; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_List_lengthAux___main___rarg(x_12, x_22);
lean_dec(x_12);
x_304 = lean_st_ref_get(x_7, x_8);
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_305, 3);
lean_inc(x_306);
lean_dec(x_305);
x_307 = lean_ctor_get_uint8(x_306, sizeof(void*)*1);
lean_dec(x_306);
if (x_307 == 0)
{
lean_object* x_308; uint8_t x_309; lean_object* x_310; lean_object* x_311; 
x_308 = lean_ctor_get(x_304, 1);
lean_inc(x_308);
lean_dec(x_304);
x_309 = 0;
x_310 = lean_box(x_309);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_1);
x_272 = x_311;
x_273 = x_308;
goto block_303;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_312 = lean_ctor_get(x_304, 1);
lean_inc(x_312);
lean_dec(x_304);
x_313 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_314 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_313, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_312);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_272 = x_315;
x_273 = x_316;
goto block_303;
}
block_271:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
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
x_28 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody(x_23, x_13, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_27;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
x_33 = l_Lean_Expr_hasLooseBVars(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_box(0);
x_35 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_16, x_32, x_34);
x_36 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_16, x_32, x_34);
lean_dec(x_16);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_267; 
x_267 = 0;
x_37 = x_267;
goto block_266;
}
else
{
lean_dec(x_35);
x_37 = x_17;
goto block_266;
}
block_266:
{
uint8_t x_38; 
if (lean_obj_tag(x_36) == 0)
{
x_38 = x_17;
goto block_264;
}
else
{
uint8_t x_265; 
lean_dec(x_36);
x_265 = 0;
x_38 = x_265;
goto block_264;
}
block_264:
{
uint8_t x_39; 
if (x_37 == 0)
{
uint8_t x_263; 
x_263 = 0;
x_39 = x_263;
goto block_262;
}
else
{
x_39 = x_38;
goto block_262;
}
block_262:
{
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_32);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_27;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_26);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_25);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_27);
x_43 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_32);
x_44 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(x_32, x_43, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_25);
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
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_111; 
x_48 = lean_ctor_get(x_44, 1);
x_49 = lean_ctor_get(x_46, 0);
x_50 = lean_ctor_get(x_46, 1);
x_111 = lean_unbox(x_49);
lean_dec(x_49);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_free_object(x_44);
x_112 = lean_st_ref_get(x_7, x_48);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_113, 3);
lean_inc(x_114);
lean_dec(x_113);
x_115 = lean_ctor_get_uint8(x_114, sizeof(void*)*1);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_dec(x_112);
x_117 = 0;
x_118 = lean_box(x_117);
lean_ctor_set(x_46, 0, x_118);
x_51 = x_46;
x_52 = x_116;
goto block_110;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_free_object(x_46);
x_119 = lean_ctor_get(x_112, 1);
lean_inc(x_119);
lean_dec(x_112);
x_120 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_121 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_120, x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_119);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_51 = x_122;
x_52 = x_123;
goto block_110;
}
}
else
{
lean_object* x_124; 
lean_dec(x_32);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_124 = lean_box(0);
lean_ctor_set(x_46, 0, x_124);
return x_44;
}
block_110:
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_21, x_32, x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_52);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
x_61 = lean_box(0);
lean_ctor_set(x_58, 0, x_61);
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_dec(x_58);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_56, 0, x_64);
return x_56;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_56, 0);
x_66 = lean_ctor_get(x_56, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_56);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_box(0);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_66);
return x_71;
}
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_56);
if (x_72 == 0)
{
return x_56;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_56, 0);
x_74 = lean_ctor_get(x_56, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_56);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_76 = lean_ctor_get(x_51, 1);
lean_inc(x_76);
lean_dec(x_51);
lean_inc(x_21);
x_77 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_77, 0, x_21);
x_78 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__4;
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_32);
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_32);
x_83 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_78);
x_85 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_86 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_85, x_84, x_76, x_2, x_3, x_4, x_5, x_6, x_7, x_52);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_21, x_32, x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_88);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_92, 0);
lean_dec(x_94);
x_95 = lean_box(0);
lean_ctor_set(x_92, 0, x_95);
return x_90;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
lean_ctor_set(x_90, 0, x_98);
return x_90;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_90, 0);
x_100 = lean_ctor_get(x_90, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_90);
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
x_103 = lean_box(0);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_100);
return x_105;
}
}
else
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_90);
if (x_106 == 0)
{
return x_90;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_90, 0);
x_108 = lean_ctor_get(x_90, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_90);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_174; 
x_125 = lean_ctor_get(x_44, 1);
x_126 = lean_ctor_get(x_46, 0);
x_127 = lean_ctor_get(x_46, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_46);
x_174 = lean_unbox(x_126);
lean_dec(x_126);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
lean_free_object(x_44);
x_175 = lean_st_ref_get(x_7, x_125);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_176, 3);
lean_inc(x_177);
lean_dec(x_176);
x_178 = lean_ctor_get_uint8(x_177, sizeof(void*)*1);
lean_dec(x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
lean_dec(x_175);
x_180 = 0;
x_181 = lean_box(x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_127);
x_128 = x_182;
x_129 = x_179;
goto block_173;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_183 = lean_ctor_get(x_175, 1);
lean_inc(x_183);
lean_dec(x_175);
x_184 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_185 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_184, x_127, x_2, x_3, x_4, x_5, x_6, x_7, x_183);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_128 = x_186;
x_129 = x_187;
goto block_173;
}
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_32);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_188 = lean_box(0);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_127);
lean_ctor_set(x_44, 0, x_189);
return x_44;
}
block_173:
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
x_131 = lean_unbox(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_dec(x_128);
x_133 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_21, x_32, x_132, x_2, x_3, x_4, x_5, x_6, x_7, x_129);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_138 = x_134;
} else {
 lean_dec_ref(x_134);
 x_138 = lean_box(0);
}
x_139 = lean_box(0);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
if (lean_is_scalar(x_136)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_136;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_135);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_133, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_133, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_144 = x_133;
} else {
 lean_dec_ref(x_133);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_146 = lean_ctor_get(x_128, 1);
lean_inc(x_146);
lean_dec(x_128);
lean_inc(x_21);
x_147 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_147, 0, x_21);
x_148 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_149 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
x_150 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__4;
x_151 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
lean_inc(x_32);
x_152 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_152, 0, x_32);
x_153 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_148);
x_155 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_156 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_155, x_154, x_146, x_2, x_3, x_4, x_5, x_6, x_7, x_129);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_21, x_32, x_159, x_2, x_3, x_4, x_5, x_6, x_7, x_158);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
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
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_165 = x_161;
} else {
 lean_dec_ref(x_161);
 x_165 = lean_box(0);
}
x_166 = lean_box(0);
if (lean_is_scalar(x_165)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_165;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_164);
if (lean_is_scalar(x_163)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_163;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_162);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_ctor_get(x_160, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_160, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_171 = x_160;
} else {
 lean_dec_ref(x_160);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_241; 
x_190 = lean_ctor_get(x_44, 0);
x_191 = lean_ctor_get(x_44, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_44);
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_194 = x_190;
} else {
 lean_dec_ref(x_190);
 x_194 = lean_box(0);
}
x_241 = lean_unbox(x_192);
lean_dec(x_192);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_242 = lean_st_ref_get(x_7, x_191);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_243, 3);
lean_inc(x_244);
lean_dec(x_243);
x_245 = lean_ctor_get_uint8(x_244, sizeof(void*)*1);
lean_dec(x_244);
if (x_245 == 0)
{
lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_ctor_get(x_242, 1);
lean_inc(x_246);
lean_dec(x_242);
x_247 = 0;
x_248 = lean_box(x_247);
if (lean_is_scalar(x_194)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_194;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_193);
x_195 = x_249;
x_196 = x_246;
goto block_240;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_194);
x_250 = lean_ctor_get(x_242, 1);
lean_inc(x_250);
lean_dec(x_242);
x_251 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_252 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_251, x_193, x_2, x_3, x_4, x_5, x_6, x_7, x_250);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_195 = x_253;
x_196 = x_254;
goto block_240;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_32);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_255 = lean_box(0);
if (lean_is_scalar(x_194)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_194;
}
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_193);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_191);
return x_257;
}
block_240:
{
lean_object* x_197; uint8_t x_198; 
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
x_198 = lean_unbox(x_197);
lean_dec(x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_195, 1);
lean_inc(x_199);
lean_dec(x_195);
x_200 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_21, x_32, x_199, x_2, x_3, x_4, x_5, x_6, x_7, x_196);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_203 = x_200;
} else {
 lean_dec_ref(x_200);
 x_203 = lean_box(0);
}
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_205 = x_201;
} else {
 lean_dec_ref(x_201);
 x_205 = lean_box(0);
}
x_206 = lean_box(0);
if (lean_is_scalar(x_205)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_205;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_204);
if (lean_is_scalar(x_203)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_203;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_202);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = lean_ctor_get(x_200, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_200, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_211 = x_200;
} else {
 lean_dec_ref(x_200);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_213 = lean_ctor_get(x_195, 1);
lean_inc(x_213);
lean_dec(x_195);
lean_inc(x_21);
x_214 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_214, 0, x_21);
x_215 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_216 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
x_217 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__4;
x_218 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
lean_inc(x_32);
x_219 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_219, 0, x_32);
x_220 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_215);
x_222 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_223 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_222, x_221, x_213, x_2, x_3, x_4, x_5, x_6, x_7, x_196);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_21, x_32, x_226, x_2, x_3, x_4, x_5, x_6, x_7, x_225);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
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
x_231 = lean_ctor_get(x_228, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_232 = x_228;
} else {
 lean_dec_ref(x_228);
 x_232 = lean_box(0);
}
x_233 = lean_box(0);
if (lean_is_scalar(x_232)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_232;
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_231);
if (lean_is_scalar(x_230)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_230;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_229);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_236 = lean_ctor_get(x_227, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_227, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_238 = x_227;
} else {
 lean_dec_ref(x_227);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
}
}
}
else
{
uint8_t x_258; 
lean_dec(x_32);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_258 = !lean_is_exclusive(x_44);
if (x_258 == 0)
{
return x_44;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_44, 0);
x_260 = lean_ctor_get(x_44, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_44);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
}
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_32);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_268 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_27;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_26);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_25);
return x_270;
}
}
}
block_303:
{
lean_object* x_274; uint8_t x_275; 
x_274 = lean_ctor_get(x_272, 0);
lean_inc(x_274);
x_275 = lean_unbox(x_274);
lean_dec(x_274);
if (x_275 == 0)
{
uint8_t x_276; 
lean_dec(x_15);
x_276 = !lean_is_exclusive(x_272);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_272, 0);
lean_dec(x_277);
x_278 = lean_box(0);
lean_ctor_set(x_272, 0, x_278);
x_24 = x_272;
x_25 = x_273;
goto block_271;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_272, 1);
lean_inc(x_279);
lean_dec(x_272);
x_280 = lean_box(0);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_279);
x_24 = x_281;
x_25 = x_273;
goto block_271;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_282 = lean_ctor_get(x_272, 1);
lean_inc(x_282);
lean_dec(x_272);
x_283 = lean_array_get_size(x_15);
lean_dec(x_15);
x_284 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_283);
x_285 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_285, 0, x_284);
x_286 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__6;
x_287 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_285);
x_288 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__8;
x_289 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
lean_inc(x_23);
x_290 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_23);
x_291 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_291, 0, x_290);
x_292 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_291);
x_293 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__10;
x_294 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
lean_inc(x_11);
x_295 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_295, 0, x_11);
x_296 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
x_297 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_298 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
x_299 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_300 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_299, x_298, x_282, x_2, x_3, x_4, x_5, x_6, x_7, x_273);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_24 = x_301;
x_25 = x_302;
goto block_271;
}
}
}
}
else
{
uint8_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; lean_object* x_328; 
x_317 = lean_ctor_get_uint8(x_1, sizeof(void*)*9);
x_318 = lean_ctor_get(x_1, 0);
x_319 = lean_ctor_get(x_1, 1);
x_320 = lean_ctor_get(x_1, 2);
x_321 = lean_ctor_get(x_1, 3);
x_322 = lean_ctor_get(x_1, 4);
x_323 = lean_ctor_get(x_1, 5);
x_324 = lean_ctor_get(x_1, 6);
x_325 = lean_ctor_get(x_1, 7);
x_326 = lean_ctor_get(x_1, 8);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_dec(x_1);
x_327 = 1;
lean_inc(x_326);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
x_328 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_328, 0, x_318);
lean_ctor_set(x_328, 1, x_319);
lean_ctor_set(x_328, 2, x_320);
lean_ctor_set(x_328, 3, x_321);
lean_ctor_set(x_328, 4, x_322);
lean_ctor_set(x_328, 5, x_323);
lean_ctor_set(x_328, 6, x_324);
lean_ctor_set(x_328, 7, x_325);
lean_ctor_set(x_328, 8, x_326);
lean_ctor_set_uint8(x_328, sizeof(void*)*9, x_317);
lean_ctor_set_uint8(x_328, sizeof(void*)*9 + 1, x_327);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_326);
lean_dec(x_323);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_329 = lean_box(0);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_328);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_8);
return x_331;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_439; lean_object* x_440; lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; 
x_332 = lean_ctor_get(x_322, 0);
lean_inc(x_332);
lean_dec(x_322);
x_333 = lean_unsigned_to_nat(0u);
x_334 = l_List_lengthAux___main___rarg(x_320, x_333);
lean_dec(x_320);
x_469 = lean_st_ref_get(x_7, x_8);
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_470, 3);
lean_inc(x_471);
lean_dec(x_470);
x_472 = lean_ctor_get_uint8(x_471, sizeof(void*)*1);
lean_dec(x_471);
if (x_472 == 0)
{
lean_object* x_473; uint8_t x_474; lean_object* x_475; lean_object* x_476; 
x_473 = lean_ctor_get(x_469, 1);
lean_inc(x_473);
lean_dec(x_469);
x_474 = 0;
x_475 = lean_box(x_474);
x_476 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_476, 0, x_475);
lean_ctor_set(x_476, 1, x_328);
x_439 = x_476;
x_440 = x_473;
goto block_468;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_477 = lean_ctor_get(x_469, 1);
lean_inc(x_477);
lean_dec(x_469);
x_478 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_479 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_478, x_328, x_2, x_3, x_4, x_5, x_6, x_7, x_477);
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_479, 1);
lean_inc(x_481);
lean_dec(x_479);
x_439 = x_480;
x_440 = x_481;
goto block_468;
}
block_438:
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_338 = x_335;
} else {
 lean_dec_ref(x_335);
 x_338 = lean_box(0);
}
x_339 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody(x_334, x_321, x_319);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_332);
lean_dec(x_326);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_340 = lean_box(0);
if (lean_is_scalar(x_338)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_338;
}
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_337);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_336);
return x_342;
}
else
{
lean_object* x_343; uint8_t x_344; 
x_343 = lean_ctor_get(x_339, 0);
lean_inc(x_343);
lean_dec(x_339);
x_344 = l_Lean_Expr_hasLooseBVars(x_343);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; 
x_345 = lean_box(0);
x_346 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_326, x_343, x_345);
x_347 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_326, x_343, x_345);
lean_dec(x_326);
if (lean_obj_tag(x_346) == 0)
{
uint8_t x_434; 
x_434 = 0;
x_348 = x_434;
goto block_433;
}
else
{
lean_dec(x_346);
x_348 = x_327;
goto block_433;
}
block_433:
{
uint8_t x_349; 
if (lean_obj_tag(x_347) == 0)
{
x_349 = x_327;
goto block_431;
}
else
{
uint8_t x_432; 
lean_dec(x_347);
x_432 = 0;
x_349 = x_432;
goto block_431;
}
block_431:
{
uint8_t x_350; 
if (x_348 == 0)
{
uint8_t x_430; 
x_430 = 0;
x_350 = x_430;
goto block_429;
}
else
{
x_350 = x_349;
goto block_429;
}
block_429:
{
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_343);
lean_dec(x_332);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_351 = lean_box(0);
if (lean_is_scalar(x_338)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_338;
}
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_337);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_336);
return x_353;
}
else
{
lean_object* x_354; lean_object* x_355; 
lean_dec(x_338);
x_354 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_343);
x_355 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasOptAutoParams___spec__2___rarg(x_343, x_354, x_337, x_2, x_3, x_4, x_5, x_6, x_7, x_336);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_408; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_358 = x_355;
} else {
 lean_dec_ref(x_355);
 x_358 = lean_box(0);
}
x_359 = lean_ctor_get(x_356, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_356, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_361 = x_356;
} else {
 lean_dec_ref(x_356);
 x_361 = lean_box(0);
}
x_408 = lean_unbox(x_359);
lean_dec(x_359);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; 
lean_dec(x_358);
x_409 = lean_st_ref_get(x_7, x_357);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_410, 3);
lean_inc(x_411);
lean_dec(x_410);
x_412 = lean_ctor_get_uint8(x_411, sizeof(void*)*1);
lean_dec(x_411);
if (x_412 == 0)
{
lean_object* x_413; uint8_t x_414; lean_object* x_415; lean_object* x_416; 
x_413 = lean_ctor_get(x_409, 1);
lean_inc(x_413);
lean_dec(x_409);
x_414 = 0;
x_415 = lean_box(x_414);
if (lean_is_scalar(x_361)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_361;
}
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_360);
x_362 = x_416;
x_363 = x_413;
goto block_407;
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_361);
x_417 = lean_ctor_get(x_409, 1);
lean_inc(x_417);
lean_dec(x_409);
x_418 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_419 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_418, x_360, x_2, x_3, x_4, x_5, x_6, x_7, x_417);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_419, 1);
lean_inc(x_421);
lean_dec(x_419);
x_362 = x_420;
x_363 = x_421;
goto block_407;
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_343);
lean_dec(x_332);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_422 = lean_box(0);
if (lean_is_scalar(x_361)) {
 x_423 = lean_alloc_ctor(0, 2, 0);
} else {
 x_423 = x_361;
}
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_360);
if (lean_is_scalar(x_358)) {
 x_424 = lean_alloc_ctor(0, 2, 0);
} else {
 x_424 = x_358;
}
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_357);
return x_424;
}
block_407:
{
lean_object* x_364; uint8_t x_365; 
x_364 = lean_ctor_get(x_362, 0);
lean_inc(x_364);
x_365 = lean_unbox(x_364);
lean_dec(x_364);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; 
x_366 = lean_ctor_get(x_362, 1);
lean_inc(x_366);
lean_dec(x_362);
x_367 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_332, x_343, x_366, x_2, x_3, x_4, x_5, x_6, x_7, x_363);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_370 = x_367;
} else {
 lean_dec_ref(x_367);
 x_370 = lean_box(0);
}
x_371 = lean_ctor_get(x_368, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_372 = x_368;
} else {
 lean_dec_ref(x_368);
 x_372 = lean_box(0);
}
x_373 = lean_box(0);
if (lean_is_scalar(x_372)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_372;
}
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_371);
if (lean_is_scalar(x_370)) {
 x_375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_375 = x_370;
}
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_369);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_376 = lean_ctor_get(x_367, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_367, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_378 = x_367;
} else {
 lean_dec_ref(x_367);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(1, 2, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_376);
lean_ctor_set(x_379, 1, x_377);
return x_379;
}
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_380 = lean_ctor_get(x_362, 1);
lean_inc(x_380);
lean_dec(x_362);
lean_inc(x_332);
x_381 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_381, 0, x_332);
x_382 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_383 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_381);
x_384 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__4;
x_385 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
lean_inc(x_343);
x_386 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_386, 0, x_343);
x_387 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
x_388 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_382);
x_389 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_390 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_389, x_388, x_380, x_2, x_3, x_4, x_5, x_6, x_7, x_363);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_394 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_332, x_343, x_393, x_2, x_3, x_4, x_5, x_6, x_7, x_392);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_397 = x_394;
} else {
 lean_dec_ref(x_394);
 x_397 = lean_box(0);
}
x_398 = lean_ctor_get(x_395, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_399 = x_395;
} else {
 lean_dec_ref(x_395);
 x_399 = lean_box(0);
}
x_400 = lean_box(0);
if (lean_is_scalar(x_399)) {
 x_401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_401 = x_399;
}
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_398);
if (lean_is_scalar(x_397)) {
 x_402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_402 = x_397;
}
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_396);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_403 = lean_ctor_get(x_394, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_394, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_405 = x_394;
} else {
 lean_dec_ref(x_394);
 x_405 = lean_box(0);
}
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(1, 2, 0);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_404);
return x_406;
}
}
}
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
lean_dec(x_343);
lean_dec(x_332);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_425 = lean_ctor_get(x_355, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_355, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_427 = x_355;
} else {
 lean_dec_ref(x_355);
 x_427 = lean_box(0);
}
if (lean_is_scalar(x_427)) {
 x_428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_428 = x_427;
}
lean_ctor_set(x_428, 0, x_425);
lean_ctor_set(x_428, 1, x_426);
return x_428;
}
}
}
}
}
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_343);
lean_dec(x_332);
lean_dec(x_326);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_435 = lean_box(0);
if (lean_is_scalar(x_338)) {
 x_436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_436 = x_338;
}
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_337);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_336);
return x_437;
}
}
}
block_468:
{
lean_object* x_441; uint8_t x_442; 
x_441 = lean_ctor_get(x_439, 0);
lean_inc(x_441);
x_442 = lean_unbox(x_441);
lean_dec(x_441);
if (x_442 == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_323);
x_443 = lean_ctor_get(x_439, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_444 = x_439;
} else {
 lean_dec_ref(x_439);
 x_444 = lean_box(0);
}
x_445 = lean_box(0);
if (lean_is_scalar(x_444)) {
 x_446 = lean_alloc_ctor(0, 2, 0);
} else {
 x_446 = x_444;
}
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_443);
x_335 = x_446;
x_336 = x_440;
goto block_438;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_447 = lean_ctor_get(x_439, 1);
lean_inc(x_447);
lean_dec(x_439);
x_448 = lean_array_get_size(x_323);
lean_dec(x_323);
x_449 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_448);
x_450 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_450, 0, x_449);
x_451 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__6;
x_452 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_450);
x_453 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__8;
x_454 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
lean_inc(x_334);
x_455 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_334);
x_456 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_456, 0, x_455);
x_457 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_457, 0, x_454);
lean_ctor_set(x_457, 1, x_456);
x_458 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__10;
x_459 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set(x_459, 1, x_458);
lean_inc(x_319);
x_460 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_460, 0, x_319);
x_461 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
x_462 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_463 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_463, 0, x_461);
lean_ctor_set(x_463, 1, x_462);
x_464 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__3;
x_465 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_464, x_463, x_447, x_2, x_3, x_4, x_5, x_6, x_7, x_440);
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
x_335 = x_466;
x_336 = x_467;
goto block_438;
}
}
}
}
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_482 = lean_box(0);
x_483 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_1);
x_484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_8);
return x_484;
}
}
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
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
return x_11;
}
}
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_3, 5);
lean_inc(x_2);
x_13 = lean_array_push(x_12, x_2);
lean_ctor_set(x_3, 5, x_13);
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_33 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_2, x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getBindingName(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_15 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
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
x_20 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___lambda__1), 10, 1);
lean_closure_set(x_20, 0, x_1);
x_21 = 0;
x_22 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg___spec__1___rarg(x_13, x_21, x_18, x_20, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_22;
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
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
lean_dec(x_6);
x_18 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_2);
x_19 = l_Lean_Elab_Term_registerMVarErrorImplicitArgInfo(x_18, x_2, x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = 1;
x_22 = x_5 + x_21;
x_23 = lean_box(0);
x_5 = x_22;
x_6 = x_23;
x_14 = x_20;
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
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_1);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
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
lean_object* x_14; lean_object* x_15; lean_object* x_122; lean_object* x_123; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_146 = lean_st_ref_get(x_12, x_13);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_147, 3);
lean_inc(x_148);
lean_dec(x_147);
x_149 = lean_ctor_get_uint8(x_148, sizeof(void*)*1);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_146, 1);
lean_inc(x_150);
lean_dec(x_146);
x_151 = 0;
x_152 = lean_box(x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_6);
x_122 = x_153;
x_123 = x_150;
goto block_145;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_146, 1);
lean_inc(x_154);
lean_dec(x_146);
lean_inc(x_2);
x_155 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_122 = x_156;
x_123 = x_157;
goto block_145;
}
block_121:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
lean_dec(x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(x_4, x_18, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_21 = lean_ctor_get(x_14, 1);
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_60 = lean_st_ref_get(x_12, x_15);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 3);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_ctor_get_uint8(x_62, sizeof(void*)*1);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec(x_60);
x_65 = 0;
x_66 = lean_box(x_65);
lean_ctor_set(x_14, 0, x_66);
x_24 = x_14;
x_25 = x_64;
goto block_59;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_free_object(x_14);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
lean_inc(x_2);
x_68 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_2, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_24 = x_69;
x_25 = x_70;
goto block_59;
}
block_59:
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_29 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_23, x_3, x_28, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(0);
x_34 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(x_4, x_33, x_32, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
return x_34;
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
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_dec(x_24);
lean_inc(x_23);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_23);
x_41 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___closed__4;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_2, x_44, x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_49 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_23, x_3, x_48, x_7, x_8, x_9, x_10, x_11, x_12, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_box(0);
x_54 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(x_4, x_53, x_52, x_7, x_8, x_9, x_10, x_11, x_12, x_51);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_49);
if (x_55 == 0)
{
return x_49;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_49, 0);
x_57 = lean_ctor_get(x_49, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_49);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_71 = lean_ctor_get(x_14, 1);
lean_inc(x_71);
lean_dec(x_14);
x_72 = lean_ctor_get(x_16, 0);
lean_inc(x_72);
lean_dec(x_16);
x_109 = lean_st_ref_get(x_12, x_15);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_110, 3);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_ctor_get_uint8(x_111, sizeof(void*)*1);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
lean_dec(x_109);
x_114 = 0;
x_115 = lean_box(x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_71);
x_73 = x_116;
x_74 = x_113;
goto block_108;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_109, 1);
lean_inc(x_117);
lean_dec(x_109);
lean_inc(x_2);
x_118 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_2, x_71, x_7, x_8, x_9, x_10, x_11, x_12, x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_73 = x_119;
x_74 = x_120;
goto block_108;
}
block_108:
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_2);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_78 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_72, x_3, x_77, x_7, x_8, x_9, x_10, x_11, x_12, x_74);
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
lean_dec(x_79);
x_82 = lean_box(0);
x_83 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(x_4, x_82, x_81, x_7, x_8, x_9, x_10, x_11, x_12, x_80);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_84 = lean_ctor_get(x_78, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_86 = x_78;
} else {
 lean_dec_ref(x_78);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_88 = lean_ctor_get(x_73, 1);
lean_inc(x_88);
lean_dec(x_73);
lean_inc(x_72);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_72);
x_90 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___closed__4;
x_91 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_93 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_2, x_93, x_88, x_7, x_8, x_9, x_10, x_11, x_12, x_74);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_98 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__3(x_72, x_3, x_97, x_7, x_8, x_9, x_10, x_11, x_12, x_96);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_box(0);
x_103 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(x_4, x_102, x_101, x_7, x_8, x_9, x_10, x_11, x_12, x_100);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_106 = x_98;
} else {
 lean_dec_ref(x_98);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
}
}
}
}
block_145:
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_122);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_122, 0);
lean_dec(x_127);
x_128 = lean_box(0);
lean_ctor_set(x_122, 0, x_128);
x_14 = x_122;
x_15 = x_123;
goto block_121;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_122, 1);
lean_inc(x_129);
lean_dec(x_122);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_14 = x_131;
x_15 = x_123;
goto block_121;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_132 = lean_ctor_get(x_122, 1);
lean_inc(x_132);
lean_dec(x_122);
lean_inc(x_4);
x_133 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_133, 0, x_4);
x_134 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___closed__2;
x_135 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___closed__2;
x_137 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
lean_inc(x_3);
x_138 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_138, 0, x_3);
x_139 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_141 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
lean_inc(x_2);
x_142 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_2, x_141, x_132, x_7, x_8, x_9, x_10, x_11, x_12, x_123);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_14 = x_143;
x_15 = x_144;
goto block_121;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_50 = lean_st_ref_get(x_7, x_8);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 3);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get_uint8(x_52, sizeof(void*)*1);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_box(0);
lean_inc(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_1);
x_11 = x_56;
x_12 = x_54;
goto block_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_dec(x_50);
x_58 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2;
lean_inc(x_1);
x_59 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__5(x_58, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_60, 0);
lean_dec(x_65);
x_66 = lean_box(0);
lean_ctor_set(x_60, 0, x_66);
x_11 = x_60;
x_12 = x_63;
goto block_49;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_11 = x_69;
x_12 = x_63;
goto block_49;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_59, 1);
lean_inc(x_70);
lean_dec(x_59);
x_71 = lean_ctor_get(x_60, 1);
lean_inc(x_71);
lean_dec(x_60);
lean_inc(x_9);
x_72 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_72, 0, x_9);
x_73 = l_Lean_addTrace___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___spec__4(x_58, x_72, x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_70);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_11 = x_74;
x_12 = x_75;
goto block_49;
}
}
block_49:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_6, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 6);
lean_inc(x_15);
x_16 = lean_array_get_size(x_15);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = lean_box(0);
lean_inc(x_9);
x_20 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__1(x_9, x_14, x_15, x_17, x_18, x_19, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_1, 5);
lean_inc(x_25);
x_26 = l_Array_isEmpty___rarg(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_10);
lean_inc(x_4);
x_27 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___spec__2(x_25, x_9, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_30);
x_32 = l_Lean_Meta_inferType___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType___spec__3(x_30, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2;
x_38 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2(x_1, x_37, x_35, x_30, x_23, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_34);
lean_dec(x_23);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_30);
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_32, 0);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_32);
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
lean_dec(x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_27);
if (x_43 == 0)
{
return x_27;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_27, 0);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_27);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_25);
x_47 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___closed__2;
x_48 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2(x_1, x_47, x_10, x_9, x_23, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
lean_dec(x_23);
return x_48;
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
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_14;
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
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
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
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_2);
x_11 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_21 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
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
x_22 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_fTypeHasOptAutoParams(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
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
x_28 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
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
x_31 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg(x_1, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
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
x_42 = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(x_41, x_37);
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
x_46 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1___rarg(x_45, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
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
x_71 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__6;
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
x_77 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_51);
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
x_82 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(x_81, x_80, x_3, x_4, x_5, x_6, x_7, x_8, x_79);
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
x_96 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___closed__3;
x_97 = l_Lean_throwError___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg___spec__1___rarg(x_96, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
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
x_99 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_98, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
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
x_109 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addEtaArg(x_1, x_106, x_3, x_4, x_5, x_6, x_7, x_8, x_105);
return x_109;
}
else
{
lean_object* x_110; 
lean_dec(x_1);
x_110 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize(x_106, x_3, x_4, x_5, x_6, x_7, x_8, x_105);
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
x_113 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_119 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(x_111, x_115, x_3, x_4, x_5, x_6, x_7, x_8, x_116);
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
x_140 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(x_111, x_139, x_3, x_4, x_5, x_6, x_7, x_8, x_116);
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
lean_object* l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_apply_9(x_2, x_16, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_17;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_19 = l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___spec__1(x_16, x_17, x_18, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
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
x_24 = l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___spec__2(x_22, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___lambda__1(x_22, x_1, x_30, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_32, 6);
x_36 = lean_ctor_get(x_32, 8);
x_37 = l_Lean_Expr_mvarId_x21(x_22);
lean_inc(x_37);
x_38 = lean_array_push(x_35, x_37);
x_39 = lean_array_push(x_36, x_37);
lean_ctor_set(x_32, 8, x_39);
lean_ctor_set(x_32, 6, x_38);
x_40 = lean_box(0);
x_41 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___lambda__1(x_22, x_1, x_40, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
return x_41;
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_42 = lean_ctor_get_uint8(x_32, sizeof(void*)*9);
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
x_45 = lean_ctor_get(x_32, 2);
x_46 = lean_ctor_get(x_32, 3);
x_47 = lean_ctor_get(x_32, 4);
x_48 = lean_ctor_get(x_32, 5);
x_49 = lean_ctor_get(x_32, 6);
x_50 = lean_ctor_get(x_32, 7);
x_51 = lean_ctor_get(x_32, 8);
x_52 = lean_ctor_get_uint8(x_32, sizeof(void*)*9 + 1);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
x_53 = l_Lean_Expr_mvarId_x21(x_22);
lean_inc(x_53);
x_54 = lean_array_push(x_49, x_53);
x_55 = lean_array_push(x_51, x_53);
x_56 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_56, 0, x_43);
lean_ctor_set(x_56, 1, x_44);
lean_ctor_set(x_56, 2, x_45);
lean_ctor_set(x_56, 3, x_46);
lean_ctor_set(x_56, 4, x_47);
lean_ctor_set(x_56, 5, x_48);
lean_ctor_set(x_56, 6, x_54);
lean_ctor_set(x_56, 7, x_50);
lean_ctor_set(x_56, 8, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*9, x_42);
lean_ctor_set_uint8(x_56, sizeof(void*)*9 + 1, x_52);
x_57 = lean_box(0);
x_58 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___lambda__1(x_22, x_1, x_57, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_24);
if (x_59 == 0)
{
return x_24;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_24, 0);
x_61 = lean_ctor_get(x_24, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_24);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; 
x_63 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_63;
}
}
}
lean_object* l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___spec__1(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processInstImplicitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_2);
x_10 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getArgExpectedType(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_19 = l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___spec__1(x_16, x_17, x_18, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
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
x_25 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar(x_24, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_22, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
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
x_38 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_isNextArgHole(x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
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
x_44 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg(x_1, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_42);
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
x_50 = l_Lean_Meta_mkFreshExprMVar___at___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg___spec__1(x_47, x_48, x_49, x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_45);
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
x_59 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar(x_58, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_53);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_54, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_61);
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
x_83 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addInstMVar(x_82, x_81, x_3, x_4, x_5, x_6, x_7, x_8, x_53);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_addNewArg(x_54, x_86, x_3, x_4, x_5, x_6, x_7, x_8, x_85);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasArgsToProcess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ElabAppArgs_main_match__4___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_ElabAppArgs_main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_ElabAppArgs_main___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_ElabAppArgs_main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_normalizeFunType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 7)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_11, sizeof(void*)*3);
lean_dec(x_11);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_getForallBody___lambda__1___boxed), 2, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = lean_ctor_get(x_13, 3);
lean_inc(x_17);
x_18 = l_List_find_x3f___main___rarg(x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; lean_object* x_20; 
lean_dec(x_14);
x_19 = (uint8_t)((x_15 << 24) >> 61);
x_20 = lean_box(x_19);
switch (lean_obj_tag(x_20)) {
case 1:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Elab_Term_ElabAppArgs_main___rarg___closed__1;
x_22 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processImplicitArg(x_21, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_22;
}
case 3:
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Elab_Term_ElabAppArgs_main___rarg___closed__1;
x_24 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processInstImplicitArg(x_23, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_24;
}
default: 
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_20);
x_25 = l_Lean_Elab_Term_ElabAppArgs_main___rarg___closed__1;
x_26 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_processExplictArg(x_25, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_28 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_Term_ElabAppArgs_eraseNamedArg(x_14, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
lean_dec(x_14);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_37 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_elabAndAddNewArg(x_36, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_1 = x_40;
x_8 = x_39;
goto _start;
}
else
{
uint8_t x_42; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
uint8_t x_46; 
lean_dec(x_27);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_28);
if (x_46 == 0)
{
return x_28;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_28, 0);
x_48 = lean_ctor_get(x_28, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_28);
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
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_11);
x_50 = lean_ctor_get(x_9, 1);
lean_inc(x_50);
lean_dec(x_9);
x_51 = lean_ctor_get(x_10, 1);
lean_inc(x_51);
lean_dec(x_10);
x_52 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_hasArgsToProcess(x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_finalize(x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
lean_dec(x_53);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_61 = l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_synthesizePendingAndNormalizeFunType(x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_1 = x_64;
x_8 = x_63;
goto _start;
}
else
{
uint8_t x_66; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_61);
if (x_66 == 0)
{
return x_61;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_61, 0);
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_61);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_9);
if (x_70 == 0)
{
return x_9;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_9, 0);
x_72 = lean_ctor_get(x_9, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_9);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = l_Array_toList___rarg(x_1);
x_16 = l_Array_toList___rarg(x_2);
x_17 = l_Array_empty___closed__1;
x_18 = 0;
x_19 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_5);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_6);
lean_ctor_set(x_19, 5, x_17);
lean_ctor_set(x_19, 6, x_17);
lean_ctor_set(x_19, 7, x_17);
lean_ctor_set(x_19, 8, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*9, x_3);
lean_ctor_set_uint8(x_19, sizeof(void*)*9 + 1, x_18);
x_20 = l_Lean_Elab_Term_ElabAppArgs_main___rarg(x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
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
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_reprAux___main___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_13 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_41; lean_object* x_42; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
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
x_61 = lean_st_ref_get(x_11, x_18);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_62, 3);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get_uint8(x_63, sizeof(void*)*1);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
x_66 = 0;
x_41 = x_66;
x_42 = x_65;
goto block_60;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_dec(x_61);
x_68 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__2;
x_69 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_68, x_6, x_7, x_8, x_9, x_10, x_11, x_67);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_unbox(x_70);
lean_dec(x_70);
x_41 = x_72;
x_42 = x_71;
goto block_60;
}
block_40:
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1(x_3, x_2, x_5, x_1, x_17, x_4, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
lean_dec(x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
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
uint8_t x_29; 
x_29 = l_Array_isEmpty___rarg(x_3);
if (x_29 == 0)
{
lean_object* x_30; 
lean_inc(x_17);
x_30 = l_Lean_Elab_Term_tryPostponeIfMVar(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1(x_3, x_2, x_5, x_1, x_17, x_4, x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
lean_dec(x_31);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
x_39 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1(x_3, x_2, x_5, x_1, x_17, x_4, x_38, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
return x_39;
}
}
}
block_60:
{
if (x_41 == 0)
{
x_19 = x_42;
goto block_40;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_43 = l_Lean_fmt___at___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_synthesizeSyntheticMVarsStep___spec__3(x_5);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__4;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__5;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_inc(x_1);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_1);
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___closed__2;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_17);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_17);
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__2;
x_58 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_57, x_56, x_6, x_7, x_8, x_9, x_10, x_11, x_42);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_19 = x_59;
goto block_40;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_13);
if (x_73 == 0)
{
return x_13;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_13, 0);
x_75 = lean_ctor_get(x_13, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_13);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___lambda__1(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_throwLValError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
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
x_16 = l_Lean_Elab_Term_mkTypeMismatchError___closed__6;
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_findMethod_x3f_match__3___rarg), 3, 0);
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
x_19 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_17);
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
x_11 = l_Lean_Expr_getAppFn___main(x_2);
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
x_35 = l_Lean_Name_replacePrefix___main(x_32, x_33, x_34);
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
x_47 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__5;
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
x_67 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__5;
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
x_78 = l_Lean_findField_x3f___main(x_30, x_24, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_inc(x_25);
lean_inc(x_24);
x_79 = lean_name_mk_string(x_24, x_25);
x_80 = lean_ctor_get(x_4, 2);
lean_inc(x_80);
lean_inc(x_79);
x_81 = l_Lean_Name_replacePrefix___main(x_79, x_80, x_76);
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
x_92 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__5;
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
x_111 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__5;
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
x_129 = l_Lean_Name_replacePrefix___main(x_126, x_127, x_128);
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
x_141 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__5;
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
x_162 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__5;
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
x_175 = l_Lean_findField_x3f___main(x_124, x_24, x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_inc(x_25);
lean_inc(x_24);
x_176 = lean_name_mk_string(x_24, x_25);
x_177 = lean_ctor_get(x_4, 2);
lean_inc(x_177);
lean_inc(x_176);
x_178 = l_Lean_Name_replacePrefix___main(x_176, x_177, x_173);
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
x_189 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__5;
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
x_209 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__5;
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
x_236 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__5;
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
x_249 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__5;
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_consumeImplicits_match__3___rarg), 3, 0);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLValLoop_match__4___rarg), 4, 0);
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
x_25 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_15, x_21, x_23, x_22, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
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
x_27 = l_Lean_Expr_consumeMData___main(x_25);
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
x_39 = l_Lean_Expr_consumeMData___main(x_37);
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
x_68 = l_Lean_Expr_consumeMData___main(x_65);
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
x_42 = l_Lean_Expr_consumeMData___main(x_41);
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
x_80 = l_Lean_Expr_consumeMData___main(x_79);
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
x_127 = l_Lean_Expr_consumeMData___main(x_126);
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
x_179 = l_Lean_Expr_consumeMData___main(x_178);
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
x_11 = l___private_Lean_Meta_Basic_20__forallTelescopeReducingImp___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__5;
x_15 = l_Lean_Meta_isDefEqBindingDomain___main___closed__2;
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
lean_inc(x_9);
lean_inc(x_1);
x_17 = l_Lean_Elab_Term_mkConst(x_1, x_16, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_List_isEmpty___rarg(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
lean_dec(x_7);
lean_dec(x_1);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_8);
x_22 = l_Lean_mkOptionalNode___closed__2;
x_23 = lean_array_push(x_22, x_21);
x_24 = lean_box(0);
x_25 = l_Array_empty___closed__1;
x_26 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_27 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_18, x_25, x_23, x_24, x_26, x_9, x_10, x_11, x_12, x_13, x_14, x_19);
lean_dec(x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(x_3, x_4, x_5, x_6, x_28, x_2, x_9, x_10, x_11, x_12, x_13, x_14, x_29);
return x_30;
}
else
{
uint8_t x_31; 
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
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; 
lean_dec(x_2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_18);
x_35 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_19);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
x_38 = l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg(x_7, x_1, x_8, x_4, x_3, x_36, x_9, x_10, x_11, x_12, x_13, x_14, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_18, x_3, x_39, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_40);
lean_dec(x_39);
lean_dec(x_3);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_35);
if (x_46 == 0)
{
return x_35;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_35, 0);
x_48 = lean_ctor_get(x_35, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_35);
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
uint8_t x_50; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_17);
if (x_50 == 0)
{
return x_17;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_17, 0);
x_52 = lean_ctor_get(x_17, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_17);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_5, x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_17 = l___private_Lean_Elab_App_0__Lean_Elab_Term_resolveLVal(x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_25 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections(x_22, x_23, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
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
x_35 = l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
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
x_42 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_31, x_38, x_40, x_39, x_41, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
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
x_51 = l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
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
x_56 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_31, x_54, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_55);
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
x_81 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections(x_77, x_78, x_76, x_7, x_8, x_9, x_10, x_11, x_12, x_75);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(x_79, x_16, x_1, x_2, x_3, x_4, x_77, x_82, x_7, x_8, x_9, x_10, x_11, x_12, x_83);
return x_84;
}
else
{
uint8_t x_85; 
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
x_85 = !lean_is_exclusive(x_81);
if (x_85 == 0)
{
return x_81;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_81, 0);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_81);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; 
lean_dec(x_78);
x_89 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(x_79, x_16, x_1, x_2, x_3, x_4, x_77, x_76, x_7, x_8, x_9, x_10, x_11, x_12, x_75);
return x_89;
}
}
case 3:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_90 = lean_ctor_get(x_17, 1);
lean_inc(x_90);
lean_dec(x_17);
x_91 = lean_ctor_get(x_18, 0);
lean_inc(x_91);
lean_dec(x_18);
x_92 = lean_ctor_get(x_19, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_19, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_19, 2);
lean_inc(x_94);
lean_dec(x_19);
x_95 = l_List_isEmpty___rarg(x_16);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; 
lean_dec(x_93);
lean_dec(x_92);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_91);
x_97 = l_Lean_mkOptionalNode___closed__2;
x_98 = lean_array_push(x_97, x_96);
x_99 = lean_box(0);
x_100 = l_Array_empty___closed__1;
x_101 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_102 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_94, x_100, x_98, x_99, x_101, x_7, x_8, x_9, x_10, x_11, x_12, x_90);
lean_dec(x_98);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_5 = x_103;
x_6 = x_16;
x_13 = x_104;
goto _start;
}
else
{
uint8_t x_106; 
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
x_106 = !lean_is_exclusive(x_102);
if (x_106 == 0)
{
return x_102;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_102, 0);
x_108 = lean_ctor_get(x_102, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_102);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; 
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_94);
x_110 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_94, x_7, x_8, x_9, x_10, x_11, x_12, x_90);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_113 = l___private_Lean_Elab_App_0__Lean_Elab_Term_addLValArg(x_92, x_93, x_91, x_2, x_1, x_111, x_7, x_8, x_9, x_10, x_11, x_12, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_94, x_1, x_114, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_115);
lean_dec(x_114);
lean_dec(x_1);
return x_116;
}
else
{
uint8_t x_117; 
lean_dec(x_94);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_113);
if (x_117 == 0)
{
return x_113;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_113, 0);
x_119 = lean_ctor_get(x_113, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_113);
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
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_110);
if (x_121 == 0)
{
return x_110;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_110, 0);
x_123 = lean_ctor_get(x_110, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_110);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
default: 
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_17, 1);
lean_inc(x_125);
lean_dec(x_17);
x_126 = lean_ctor_get(x_18, 0);
lean_inc(x_126);
lean_dec(x_18);
x_127 = lean_ctor_get(x_19, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_19, 1);
lean_inc(x_128);
lean_dec(x_19);
x_129 = lean_box(0);
lean_inc(x_7);
x_130 = l_Lean_Elab_Term_mkConst(x_127, x_129, x_7, x_8, x_9, x_10, x_11, x_12, x_125);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = l_List_isEmpty___rarg(x_16);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; 
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_126);
x_135 = l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_128);
x_138 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2;
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
x_140 = l_Lean_mkAppStx___closed__9;
x_141 = lean_array_push(x_140, x_136);
x_142 = lean_array_push(x_141, x_139);
x_143 = lean_box(0);
x_144 = l_Array_empty___closed__1;
x_145 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_146 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_131, x_142, x_144, x_143, x_145, x_7, x_8, x_9, x_10, x_11, x_12, x_132);
lean_dec(x_142);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_5 = x_147;
x_6 = x_16;
x_13 = x_148;
goto _start;
}
else
{
uint8_t x_150; 
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
x_150 = !lean_is_exclusive(x_146);
if (x_150 == 0)
{
return x_146;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_146, 0);
x_152 = lean_ctor_get(x_146, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_146);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_16);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_126);
x_155 = l_List_forInAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_mkBaseProjections___spec__1___closed__2;
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
lean_inc(x_7);
x_157 = l_Lean_Elab_Term_addNamedArg(x_1, x_156, x_7, x_8, x_9, x_10, x_11, x_12, x_132);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_160, 0, x_128);
x_161 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2;
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_160);
lean_inc(x_7);
x_163 = l_Lean_Elab_Term_addNamedArg(x_158, x_162, x_7, x_8, x_9, x_10, x_11, x_12, x_159);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs(x_131, x_164, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_165);
lean_dec(x_2);
lean_dec(x_164);
return x_166;
}
else
{
uint8_t x_167; 
lean_dec(x_131);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_167 = !lean_is_exclusive(x_163);
if (x_167 == 0)
{
return x_163;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_163, 0);
x_169 = lean_ctor_get(x_163, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_163);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_131);
lean_dec(x_128);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_171 = !lean_is_exclusive(x_157);
if (x_171 == 0)
{
return x_157;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_157, 0);
x_173 = lean_ctor_get(x_157, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_157);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_128);
lean_dec(x_126);
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
x_175 = !lean_is_exclusive(x_130);
if (x_175 == 0)
{
return x_130;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_130, 0);
x_177 = lean_ctor_get(x_130, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_130);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
}
}
else
{
uint8_t x_179; 
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
x_179 = !lean_is_exclusive(x_17);
if (x_179 == 0)
{
return x_17;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_17, 0);
x_181 = lean_ctor_get(x_17, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_17);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_23; 
x_23 = l_List_isEmpty___rarg(x_2);
if (x_23 == 0)
{
x_14 = x_6;
goto block_22;
}
else
{
uint8_t x_24; 
x_24 = 0;
x_14 = x_24;
goto block_22;
}
block_22:
{
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop(x_3, x_4, x_5, x_6, x_1, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___closed__3;
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
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___lambda__1(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_16;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
x_21 = l_List_map___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(x_20);
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
x_52 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_19, x_22, x_2, x_3, x_4, x_5, x_9, x_10, x_11, x_12, x_13, x_14, x_25);
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
lean_inc(x_10);
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
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
x_21 = l_List_map___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__2(x_20);
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
x_52 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_19, x_22, x_2, x_3, x_4, x_5, x_9, x_10, x_11, x_12, x_13, x_14, x_25);
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
lean_inc(x_10);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
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
lean_dec(x_22);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_24);
lean_inc(x_12);
lean_inc(x_10);
x_26 = l_Lean_Elab_Term_resolveName(x_17, x_18, x_2, x_10, x_11, x_12, x_13, x_25, x_15, x_16);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_10, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_10, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_10, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_10, 5);
lean_inc(x_34);
x_35 = lean_ctor_get(x_10, 6);
lean_inc(x_35);
x_36 = lean_ctor_get(x_10, 7);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_10, sizeof(void*)*8);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_List_lengthAux___main___rarg(x_27, x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_dec_eq(x_39, x_40);
if (x_8 == 0)
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
x_43 = !lean_is_exclusive(x_10);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_10, 7);
lean_dec(x_44);
x_45 = lean_ctor_get(x_10, 6);
lean_dec(x_45);
x_46 = lean_ctor_get(x_10, 5);
lean_dec(x_46);
x_47 = lean_ctor_get(x_10, 4);
lean_dec(x_47);
x_48 = lean_ctor_get(x_10, 3);
lean_dec(x_48);
x_49 = lean_ctor_get(x_10, 2);
lean_dec(x_49);
x_50 = lean_ctor_get(x_10, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_10, 0);
lean_dec(x_51);
x_52 = 0;
lean_ctor_set_uint8(x_10, sizeof(void*)*8 + 1, x_52);
x_53 = l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_42, x_9, x_27, x_10, x_11, x_12, x_13, x_14, x_15, x_28);
return x_53;
}
else
{
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_10);
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
x_56 = l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_42, x_9, x_27, x_55, x_11, x_12, x_13, x_14, x_15, x_28);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_10);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_10, 7);
lean_dec(x_58);
x_59 = lean_ctor_get(x_10, 6);
lean_dec(x_59);
x_60 = lean_ctor_get(x_10, 5);
lean_dec(x_60);
x_61 = lean_ctor_get(x_10, 4);
lean_dec(x_61);
x_62 = lean_ctor_get(x_10, 3);
lean_dec(x_62);
x_63 = lean_ctor_get(x_10, 2);
lean_dec(x_63);
x_64 = lean_ctor_get(x_10, 1);
lean_dec(x_64);
x_65 = lean_ctor_get(x_10, 0);
lean_dec(x_65);
x_66 = l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4(x_3, x_4, x_5, x_6, x_7, x_42, x_9, x_27, x_10, x_11, x_12, x_13, x_14, x_15, x_28);
return x_66;
}
else
{
uint8_t x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get_uint8(x_10, sizeof(void*)*8 + 1);
lean_dec(x_10);
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
x_69 = l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4(x_3, x_4, x_5, x_6, x_7, x_42, x_9, x_27, x_68, x_11, x_12, x_13, x_14, x_15, x_28);
return x_69;
}
}
}
}
else
{
uint8_t x_73; 
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
x_77 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__1___rarg(x_16);
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
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__3(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_List_foldlM___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___spec__4(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = lean_unbox(x_8);
lean_dec(x_8);
x_19 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(x_6);
x_11 = lean_box(x_7);
x_12 = lean_apply_8(x_9, x_1, x_2, x_3, x_4, x_5, x_10, x_11, x_8);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn_match__1___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = lean_unbox(x_7);
lean_dec(x_7);
x_12 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn_match__1___rarg(x_1, x_2, x_3, x_4, x_5, x_10, x_11, x_8, x_9);
return x_12;
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
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_4);
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
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_10);
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
x_24 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn(x_20, x_2, x_3, x_4, x_5, x_6, x_23, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
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
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_System_FilePath_dirName___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
lean_inc(x_1);
x_194 = l_Lean_Syntax_getKind(x_1);
x_195 = l_Lean_choiceKind;
x_196 = lean_name_eq(x_194, x_195);
lean_dec(x_194);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_449; lean_object* x_492; lean_object* x_518; uint8_t x_519; 
x_518 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__13;
lean_inc(x_1);
x_519 = l_Lean_Syntax_isOfKind(x_1, x_518);
if (x_519 == 0)
{
lean_object* x_520; 
x_520 = lean_box(0);
x_492 = x_520;
goto block_517;
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; uint8_t x_524; 
x_521 = l_Lean_Syntax_getArgs(x_1);
x_522 = lean_array_get_size(x_521);
lean_dec(x_521);
x_523 = lean_unsigned_to_nat(3u);
x_524 = lean_nat_dec_eq(x_522, x_523);
lean_dec(x_522);
if (x_524 == 0)
{
lean_object* x_525; 
x_525 = lean_box(0);
x_492 = x_525;
goto block_517;
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; uint8_t x_531; 
x_526 = lean_unsigned_to_nat(0u);
x_527 = l_Lean_Syntax_getArg(x_1, x_526);
x_528 = lean_unsigned_to_nat(2u);
x_529 = l_Lean_Syntax_getArg(x_1, x_528);
x_530 = l_Lean_fieldIdxKind___closed__2;
lean_inc(x_529);
x_531 = l_Lean_Syntax_isOfKind(x_529, x_530);
if (x_531 == 0)
{
lean_object* x_532; uint8_t x_533; 
x_532 = l_Lean_identKind___closed__2;
lean_inc(x_529);
x_533 = l_Lean_Syntax_isOfKind(x_529, x_532);
if (x_533 == 0)
{
uint8_t x_534; uint8_t x_535; 
lean_dec(x_529);
lean_dec(x_527);
x_534 = l_List_isEmpty___rarg(x_2);
if (x_7 == 0)
{
uint8_t x_708; 
x_708 = 1;
x_535 = x_708;
goto block_707;
}
else
{
uint8_t x_709; 
x_709 = 0;
x_535 = x_709;
goto block_707;
}
block_707:
{
uint8_t x_536; 
if (x_534 == 0)
{
uint8_t x_703; 
x_703 = 0;
x_536 = x_703;
goto block_702;
}
else
{
uint8_t x_704; 
x_704 = l_Array_isEmpty___rarg(x_3);
if (x_704 == 0)
{
uint8_t x_705; 
x_705 = 0;
x_536 = x_705;
goto block_702;
}
else
{
uint8_t x_706; 
x_706 = l_Array_isEmpty___rarg(x_4);
x_536 = x_706;
goto block_702;
}
}
block_702:
{
if (x_536 == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_574; lean_object* x_575; lean_object* x_597; 
x_537 = lean_box(0);
x_538 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_538, 1);
lean_inc(x_540);
if (lean_is_exclusive(x_538)) {
 lean_ctor_release(x_538, 0);
 lean_ctor_release(x_538, 1);
 x_541 = x_538;
} else {
 lean_dec_ref(x_538);
 x_541 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_597 = l_Lean_Elab_Term_elabTerm(x_1, x_537, x_535, x_9, x_10, x_11, x_12, x_13, x_14, x_540);
if (lean_obj_tag(x_597) == 0)
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_598 = lean_ctor_get(x_597, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_597, 1);
lean_inc(x_599);
lean_dec(x_597);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_600 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_598, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_599);
if (lean_obj_tag(x_600) == 0)
{
if (x_7 == 0)
{
lean_object* x_601; lean_object* x_602; 
lean_dec(x_541);
lean_dec(x_5);
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_600, 1);
lean_inc(x_602);
lean_dec(x_600);
x_574 = x_601;
x_575 = x_602;
goto block_596;
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_603 = lean_ctor_get(x_600, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_600, 1);
lean_inc(x_604);
lean_dec(x_600);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_605 = l_Lean_Elab_Term_ensureHasType(x_5, x_603, x_537, x_9, x_10, x_11, x_12, x_13, x_14, x_604);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; 
lean_dec(x_541);
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_605, 1);
lean_inc(x_607);
lean_dec(x_605);
x_574 = x_606;
x_575 = x_607;
goto block_596;
}
else
{
lean_object* x_608; lean_object* x_609; 
x_608 = lean_ctor_get(x_605, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_605, 1);
lean_inc(x_609);
lean_dec(x_605);
x_542 = x_608;
x_543 = x_609;
goto block_573;
}
}
}
else
{
lean_object* x_610; lean_object* x_611; 
lean_dec(x_5);
x_610 = lean_ctor_get(x_600, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_600, 1);
lean_inc(x_611);
lean_dec(x_600);
x_542 = x_610;
x_543 = x_611;
goto block_573;
}
}
else
{
lean_object* x_612; lean_object* x_613; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_612 = lean_ctor_get(x_597, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_597, 1);
lean_inc(x_613);
lean_dec(x_597);
x_542 = x_612;
x_543 = x_613;
goto block_573;
}
block_573:
{
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_544; uint8_t x_545; 
lean_dec(x_541);
x_544 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_543);
x_545 = !lean_is_exclusive(x_544);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; uint8_t x_549; 
x_546 = lean_ctor_get(x_544, 0);
x_547 = lean_ctor_get(x_544, 1);
x_548 = l_Lean_Elab_Term_SavedState_restore(x_539, x_9, x_10, x_11, x_12, x_13, x_14, x_547);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_549 = !lean_is_exclusive(x_548);
if (x_549 == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_548, 1);
x_551 = lean_ctor_get(x_548, 0);
lean_dec(x_551);
lean_ctor_set_tag(x_548, 1);
lean_ctor_set(x_548, 1, x_546);
lean_ctor_set(x_548, 0, x_542);
x_552 = lean_array_push(x_8, x_548);
lean_ctor_set(x_544, 1, x_550);
lean_ctor_set(x_544, 0, x_552);
return x_544;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_548, 1);
lean_inc(x_553);
lean_dec(x_548);
x_554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_554, 0, x_542);
lean_ctor_set(x_554, 1, x_546);
x_555 = lean_array_push(x_8, x_554);
lean_ctor_set(x_544, 1, x_553);
lean_ctor_set(x_544, 0, x_555);
return x_544;
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_556 = lean_ctor_get(x_544, 0);
x_557 = lean_ctor_get(x_544, 1);
lean_inc(x_557);
lean_inc(x_556);
lean_dec(x_544);
x_558 = l_Lean_Elab_Term_SavedState_restore(x_539, x_9, x_10, x_11, x_12, x_13, x_14, x_557);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_559 = lean_ctor_get(x_558, 1);
lean_inc(x_559);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 lean_ctor_release(x_558, 1);
 x_560 = x_558;
} else {
 lean_dec_ref(x_558);
 x_560 = lean_box(0);
}
if (lean_is_scalar(x_560)) {
 x_561 = lean_alloc_ctor(1, 2, 0);
} else {
 x_561 = x_560;
 lean_ctor_set_tag(x_561, 1);
}
lean_ctor_set(x_561, 0, x_542);
lean_ctor_set(x_561, 1, x_556);
x_562 = lean_array_push(x_8, x_561);
x_563 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_559);
return x_563;
}
}
else
{
lean_object* x_564; lean_object* x_565; uint8_t x_566; 
lean_dec(x_8);
x_564 = lean_ctor_get(x_542, 0);
lean_inc(x_564);
x_565 = l_Lean_Elab_postponeExceptionId;
x_566 = lean_nat_dec_eq(x_564, x_565);
lean_dec(x_564);
if (x_566 == 0)
{
lean_object* x_567; 
lean_dec(x_539);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_541)) {
 x_567 = lean_alloc_ctor(1, 2, 0);
} else {
 x_567 = x_541;
 lean_ctor_set_tag(x_567, 1);
}
lean_ctor_set(x_567, 0, x_542);
lean_ctor_set(x_567, 1, x_543);
return x_567;
}
else
{
lean_object* x_568; uint8_t x_569; 
lean_dec(x_541);
x_568 = l_Lean_Elab_Term_SavedState_restore(x_539, x_9, x_10, x_11, x_12, x_13, x_14, x_543);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_569 = !lean_is_exclusive(x_568);
if (x_569 == 0)
{
lean_object* x_570; 
x_570 = lean_ctor_get(x_568, 0);
lean_dec(x_570);
lean_ctor_set_tag(x_568, 1);
lean_ctor_set(x_568, 0, x_542);
return x_568;
}
else
{
lean_object* x_571; lean_object* x_572; 
x_571 = lean_ctor_get(x_568, 1);
lean_inc(x_571);
lean_dec(x_568);
x_572 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_572, 0, x_542);
lean_ctor_set(x_572, 1, x_571);
return x_572;
}
}
}
}
block_596:
{
lean_object* x_576; uint8_t x_577; 
x_576 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_575);
x_577 = !lean_is_exclusive(x_576);
if (x_577 == 0)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; uint8_t x_581; 
x_578 = lean_ctor_get(x_576, 0);
x_579 = lean_ctor_get(x_576, 1);
x_580 = l_Lean_Elab_Term_SavedState_restore(x_539, x_9, x_10, x_11, x_12, x_13, x_14, x_579);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_581 = !lean_is_exclusive(x_580);
if (x_581 == 0)
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_582 = lean_ctor_get(x_580, 1);
x_583 = lean_ctor_get(x_580, 0);
lean_dec(x_583);
lean_ctor_set(x_580, 1, x_578);
lean_ctor_set(x_580, 0, x_574);
x_584 = lean_array_push(x_8, x_580);
lean_ctor_set(x_576, 1, x_582);
lean_ctor_set(x_576, 0, x_584);
return x_576;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_585 = lean_ctor_get(x_580, 1);
lean_inc(x_585);
lean_dec(x_580);
x_586 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_586, 0, x_574);
lean_ctor_set(x_586, 1, x_578);
x_587 = lean_array_push(x_8, x_586);
lean_ctor_set(x_576, 1, x_585);
lean_ctor_set(x_576, 0, x_587);
return x_576;
}
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_588 = lean_ctor_get(x_576, 0);
x_589 = lean_ctor_get(x_576, 1);
lean_inc(x_589);
lean_inc(x_588);
lean_dec(x_576);
x_590 = l_Lean_Elab_Term_SavedState_restore(x_539, x_9, x_10, x_11, x_12, x_13, x_14, x_589);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_591 = lean_ctor_get(x_590, 1);
lean_inc(x_591);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 lean_ctor_release(x_590, 1);
 x_592 = x_590;
} else {
 lean_dec_ref(x_590);
 x_592 = lean_box(0);
}
if (lean_is_scalar(x_592)) {
 x_593 = lean_alloc_ctor(0, 2, 0);
} else {
 x_593 = x_592;
}
lean_ctor_set(x_593, 0, x_574);
lean_ctor_set(x_593, 1, x_588);
x_594 = lean_array_push(x_8, x_593);
x_595 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_595, 0, x_594);
lean_ctor_set(x_595, 1, x_591);
return x_595;
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
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; uint8_t x_641; lean_object* x_642; 
x_614 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_614, 1);
lean_inc(x_616);
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 lean_ctor_release(x_614, 1);
 x_617 = x_614;
} else {
 lean_dec_ref(x_614);
 x_617 = lean_box(0);
}
x_641 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_642 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_641, x_9, x_10, x_11, x_12, x_13, x_14, x_616);
if (lean_obj_tag(x_642) == 0)
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_649; 
lean_dec(x_617);
x_643 = lean_ctor_get(x_642, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_642, 1);
lean_inc(x_644);
lean_dec(x_642);
x_645 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_644);
x_646 = lean_ctor_get(x_645, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_645, 1);
lean_inc(x_647);
lean_dec(x_645);
x_648 = l_Lean_Elab_Term_SavedState_restore(x_615, x_9, x_10, x_11, x_12, x_13, x_14, x_647);
x_649 = !lean_is_exclusive(x_648);
if (x_649 == 0)
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_650 = lean_ctor_get(x_648, 1);
x_651 = lean_ctor_get(x_648, 0);
lean_dec(x_651);
lean_ctor_set(x_648, 1, x_646);
lean_ctor_set(x_648, 0, x_643);
x_652 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_648, x_9, x_10, x_11, x_12, x_13, x_14, x_650);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_652;
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_653 = lean_ctor_get(x_648, 1);
lean_inc(x_653);
lean_dec(x_648);
x_654 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_654, 0, x_643);
lean_ctor_set(x_654, 1, x_646);
x_655 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_654, x_9, x_10, x_11, x_12, x_13, x_14, x_653);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_655;
}
}
else
{
lean_object* x_656; lean_object* x_657; 
x_656 = lean_ctor_get(x_642, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_642, 1);
lean_inc(x_657);
lean_dec(x_642);
x_618 = x_656;
x_619 = x_657;
goto block_640;
}
block_640:
{
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; 
lean_dec(x_617);
x_620 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_619);
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 1);
lean_inc(x_622);
lean_dec(x_620);
x_623 = l_Lean_Elab_Term_SavedState_restore(x_615, x_9, x_10, x_11, x_12, x_13, x_14, x_622);
x_624 = !lean_is_exclusive(x_623);
if (x_624 == 0)
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_625 = lean_ctor_get(x_623, 1);
x_626 = lean_ctor_get(x_623, 0);
lean_dec(x_626);
lean_ctor_set_tag(x_623, 1);
lean_ctor_set(x_623, 1, x_621);
lean_ctor_set(x_623, 0, x_618);
x_627 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_623, x_9, x_10, x_11, x_12, x_13, x_14, x_625);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_627;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_623, 1);
lean_inc(x_628);
lean_dec(x_623);
x_629 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_629, 0, x_618);
lean_ctor_set(x_629, 1, x_621);
x_630 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_629, x_9, x_10, x_11, x_12, x_13, x_14, x_628);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_630;
}
}
else
{
lean_object* x_631; lean_object* x_632; uint8_t x_633; 
lean_dec(x_8);
x_631 = lean_ctor_get(x_618, 0);
lean_inc(x_631);
x_632 = l_Lean_Elab_postponeExceptionId;
x_633 = lean_nat_dec_eq(x_631, x_632);
lean_dec(x_631);
if (x_633 == 0)
{
lean_object* x_634; 
lean_dec(x_615);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_617)) {
 x_634 = lean_alloc_ctor(1, 2, 0);
} else {
 x_634 = x_617;
 lean_ctor_set_tag(x_634, 1);
}
lean_ctor_set(x_634, 0, x_618);
lean_ctor_set(x_634, 1, x_619);
return x_634;
}
else
{
lean_object* x_635; uint8_t x_636; 
lean_dec(x_617);
x_635 = l_Lean_Elab_Term_SavedState_restore(x_615, x_9, x_10, x_11, x_12, x_13, x_14, x_619);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_636 = !lean_is_exclusive(x_635);
if (x_636 == 0)
{
lean_object* x_637; 
x_637 = lean_ctor_get(x_635, 0);
lean_dec(x_637);
lean_ctor_set_tag(x_635, 1);
lean_ctor_set(x_635, 0, x_618);
return x_635;
}
else
{
lean_object* x_638; lean_object* x_639; 
x_638 = lean_ctor_get(x_635, 1);
lean_inc(x_638);
lean_dec(x_635);
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_618);
lean_ctor_set(x_639, 1, x_638);
return x_639;
}
}
}
}
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_686; 
x_658 = lean_box(0);
x_659 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_660 = lean_ctor_get(x_659, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_659, 1);
lean_inc(x_661);
if (lean_is_exclusive(x_659)) {
 lean_ctor_release(x_659, 0);
 lean_ctor_release(x_659, 1);
 x_662 = x_659;
} else {
 lean_dec_ref(x_659);
 x_662 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_686 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_535, x_658, x_9, x_10, x_11, x_12, x_13, x_14, x_661);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; uint8_t x_693; 
lean_dec(x_662);
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_686, 1);
lean_inc(x_688);
lean_dec(x_686);
x_689 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_688);
x_690 = lean_ctor_get(x_689, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_689, 1);
lean_inc(x_691);
lean_dec(x_689);
x_692 = l_Lean_Elab_Term_SavedState_restore(x_660, x_9, x_10, x_11, x_12, x_13, x_14, x_691);
x_693 = !lean_is_exclusive(x_692);
if (x_693 == 0)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_694 = lean_ctor_get(x_692, 1);
x_695 = lean_ctor_get(x_692, 0);
lean_dec(x_695);
lean_ctor_set(x_692, 1, x_690);
lean_ctor_set(x_692, 0, x_687);
x_696 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_692, x_9, x_10, x_11, x_12, x_13, x_14, x_694);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_696;
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_697 = lean_ctor_get(x_692, 1);
lean_inc(x_697);
lean_dec(x_692);
x_698 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_698, 0, x_687);
lean_ctor_set(x_698, 1, x_690);
x_699 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_698, x_9, x_10, x_11, x_12, x_13, x_14, x_697);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_699;
}
}
else
{
lean_object* x_700; lean_object* x_701; 
x_700 = lean_ctor_get(x_686, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_686, 1);
lean_inc(x_701);
lean_dec(x_686);
x_663 = x_700;
x_664 = x_701;
goto block_685;
}
block_685:
{
if (lean_obj_tag(x_663) == 0)
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; uint8_t x_669; 
lean_dec(x_662);
x_665 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_664);
x_666 = lean_ctor_get(x_665, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_665, 1);
lean_inc(x_667);
lean_dec(x_665);
x_668 = l_Lean_Elab_Term_SavedState_restore(x_660, x_9, x_10, x_11, x_12, x_13, x_14, x_667);
x_669 = !lean_is_exclusive(x_668);
if (x_669 == 0)
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_670 = lean_ctor_get(x_668, 1);
x_671 = lean_ctor_get(x_668, 0);
lean_dec(x_671);
lean_ctor_set_tag(x_668, 1);
lean_ctor_set(x_668, 1, x_666);
lean_ctor_set(x_668, 0, x_663);
x_672 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_668, x_9, x_10, x_11, x_12, x_13, x_14, x_670);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_672;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_673 = lean_ctor_get(x_668, 1);
lean_inc(x_673);
lean_dec(x_668);
x_674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_674, 0, x_663);
lean_ctor_set(x_674, 1, x_666);
x_675 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_674, x_9, x_10, x_11, x_12, x_13, x_14, x_673);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_675;
}
}
else
{
lean_object* x_676; lean_object* x_677; uint8_t x_678; 
lean_dec(x_8);
x_676 = lean_ctor_get(x_663, 0);
lean_inc(x_676);
x_677 = l_Lean_Elab_postponeExceptionId;
x_678 = lean_nat_dec_eq(x_676, x_677);
lean_dec(x_676);
if (x_678 == 0)
{
lean_object* x_679; 
lean_dec(x_660);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_662)) {
 x_679 = lean_alloc_ctor(1, 2, 0);
} else {
 x_679 = x_662;
 lean_ctor_set_tag(x_679, 1);
}
lean_ctor_set(x_679, 0, x_663);
lean_ctor_set(x_679, 1, x_664);
return x_679;
}
else
{
lean_object* x_680; uint8_t x_681; 
lean_dec(x_662);
x_680 = l_Lean_Elab_Term_SavedState_restore(x_660, x_9, x_10, x_11, x_12, x_13, x_14, x_664);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_681 = !lean_is_exclusive(x_680);
if (x_681 == 0)
{
lean_object* x_682; 
x_682 = lean_ctor_get(x_680, 0);
lean_dec(x_682);
lean_ctor_set_tag(x_680, 1);
lean_ctor_set(x_680, 0, x_663);
return x_680;
}
else
{
lean_object* x_683; lean_object* x_684; 
x_683 = lean_ctor_get(x_680, 1);
lean_inc(x_683);
lean_dec(x_680);
x_684 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_684, 0, x_663);
lean_ctor_set(x_684, 1, x_683);
return x_684;
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
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
lean_dec(x_1);
x_710 = l_Lean_Syntax_getId(x_529);
lean_dec(x_529);
x_711 = lean_erase_macro_scopes(x_710);
x_712 = l_Lean_Name_components(x_711);
x_713 = l_List_map___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__2(x_712);
x_714 = l_List_append___rarg(x_713, x_2);
x_1 = x_527;
x_2 = x_714;
goto _start;
}
}
else
{
lean_object* x_716; lean_object* x_717; 
lean_dec(x_1);
x_716 = l_Lean_fieldIdxKind;
x_717 = l_Lean_Syntax_isNatLitAux(x_716, x_529);
lean_dec(x_529);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; 
x_718 = l_Nat_Inhabited;
x_719 = l_Option_get_x21___rarg___closed__3;
x_720 = lean_panic_fn(x_718, x_719);
x_721 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_721, 0, x_720);
x_722 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_722, 0, x_721);
lean_ctor_set(x_722, 1, x_2);
x_1 = x_527;
x_2 = x_722;
goto _start;
}
else
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_724 = lean_ctor_get(x_717, 0);
lean_inc(x_724);
lean_dec(x_717);
x_725 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_725, 0, x_724);
x_726 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_726, 0, x_725);
lean_ctor_set(x_726, 1, x_2);
x_1 = x_527;
x_2 = x_726;
goto _start;
}
}
}
}
block_448:
{
lean_object* x_198; uint8_t x_199; 
lean_dec(x_197);
x_198 = l_Lean_identKind___closed__2;
lean_inc(x_1);
x_199 = l_Lean_Syntax_isOfKind(x_1, x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_246; uint8_t x_247; 
x_246 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8;
lean_inc(x_1);
x_247 = l_Lean_Syntax_isOfKind(x_1, x_246);
if (x_247 == 0)
{
lean_object* x_248; 
x_248 = lean_box(0);
x_200 = x_248;
goto block_245;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_249 = l_Lean_Syntax_getArgs(x_1);
x_250 = lean_array_get_size(x_249);
lean_dec(x_249);
x_251 = lean_unsigned_to_nat(4u);
x_252 = lean_nat_dec_eq(x_250, x_251);
lean_dec(x_250);
if (x_252 == 0)
{
lean_object* x_253; 
x_253 = lean_box(0);
x_200 = x_253;
goto block_245;
}
else
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_254 = lean_unsigned_to_nat(0u);
x_255 = l_Lean_Syntax_getArg(x_1, x_254);
lean_inc(x_255);
x_256 = l_Lean_Syntax_isOfKind(x_255, x_198);
if (x_256 == 0)
{
uint8_t x_257; uint8_t x_258; 
lean_dec(x_255);
x_257 = l_List_isEmpty___rarg(x_2);
if (x_7 == 0)
{
uint8_t x_431; 
x_431 = 1;
x_258 = x_431;
goto block_430;
}
else
{
uint8_t x_432; 
x_432 = 0;
x_258 = x_432;
goto block_430;
}
block_430:
{
uint8_t x_259; 
if (x_257 == 0)
{
uint8_t x_426; 
x_426 = 0;
x_259 = x_426;
goto block_425;
}
else
{
uint8_t x_427; 
x_427 = l_Array_isEmpty___rarg(x_3);
if (x_427 == 0)
{
uint8_t x_428; 
x_428 = 0;
x_259 = x_428;
goto block_425;
}
else
{
uint8_t x_429; 
x_429 = l_Array_isEmpty___rarg(x_4);
x_259 = x_429;
goto block_425;
}
}
block_425:
{
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_297; lean_object* x_298; lean_object* x_320; 
x_260 = lean_box(0);
x_261 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_264 = x_261;
} else {
 lean_dec_ref(x_261);
 x_264 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_320 = l_Lean_Elab_Term_elabTerm(x_1, x_260, x_258, x_9, x_10, x_11, x_12, x_13, x_14, x_263);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_323 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_321, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_322);
if (lean_obj_tag(x_323) == 0)
{
if (x_7 == 0)
{
lean_object* x_324; lean_object* x_325; 
lean_dec(x_264);
lean_dec(x_5);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_297 = x_324;
x_298 = x_325;
goto block_319;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_323, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_323, 1);
lean_inc(x_327);
lean_dec(x_323);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_328 = l_Lean_Elab_Term_ensureHasType(x_5, x_326, x_260, x_9, x_10, x_11, x_12, x_13, x_14, x_327);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; 
lean_dec(x_264);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
x_297 = x_329;
x_298 = x_330;
goto block_319;
}
else
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_ctor_get(x_328, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_328, 1);
lean_inc(x_332);
lean_dec(x_328);
x_265 = x_331;
x_266 = x_332;
goto block_296;
}
}
}
else
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_5);
x_333 = lean_ctor_get(x_323, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_323, 1);
lean_inc(x_334);
lean_dec(x_323);
x_265 = x_333;
x_266 = x_334;
goto block_296;
}
}
else
{
lean_object* x_335; lean_object* x_336; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_335 = lean_ctor_get(x_320, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_320, 1);
lean_inc(x_336);
lean_dec(x_320);
x_265 = x_335;
x_266 = x_336;
goto block_296;
}
block_296:
{
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_267; uint8_t x_268; 
lean_dec(x_264);
x_267 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_266);
x_268 = !lean_is_exclusive(x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_269 = lean_ctor_get(x_267, 0);
x_270 = lean_ctor_get(x_267, 1);
x_271 = l_Lean_Elab_Term_SavedState_restore(x_262, x_9, x_10, x_11, x_12, x_13, x_14, x_270);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_272 = !lean_is_exclusive(x_271);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_271, 1);
x_274 = lean_ctor_get(x_271, 0);
lean_dec(x_274);
lean_ctor_set_tag(x_271, 1);
lean_ctor_set(x_271, 1, x_269);
lean_ctor_set(x_271, 0, x_265);
x_275 = lean_array_push(x_8, x_271);
lean_ctor_set(x_267, 1, x_273);
lean_ctor_set(x_267, 0, x_275);
return x_267;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_271, 1);
lean_inc(x_276);
lean_dec(x_271);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_265);
lean_ctor_set(x_277, 1, x_269);
x_278 = lean_array_push(x_8, x_277);
lean_ctor_set(x_267, 1, x_276);
lean_ctor_set(x_267, 0, x_278);
return x_267;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_279 = lean_ctor_get(x_267, 0);
x_280 = lean_ctor_get(x_267, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_267);
x_281 = l_Lean_Elab_Term_SavedState_restore(x_262, x_9, x_10, x_11, x_12, x_13, x_14, x_280);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_283 = x_281;
} else {
 lean_dec_ref(x_281);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
 lean_ctor_set_tag(x_284, 1);
}
lean_ctor_set(x_284, 0, x_265);
lean_ctor_set(x_284, 1, x_279);
x_285 = lean_array_push(x_8, x_284);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_282);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; uint8_t x_289; 
lean_dec(x_8);
x_287 = lean_ctor_get(x_265, 0);
lean_inc(x_287);
x_288 = l_Lean_Elab_postponeExceptionId;
x_289 = lean_nat_dec_eq(x_287, x_288);
lean_dec(x_287);
if (x_289 == 0)
{
lean_object* x_290; 
lean_dec(x_262);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_264)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_264;
 lean_ctor_set_tag(x_290, 1);
}
lean_ctor_set(x_290, 0, x_265);
lean_ctor_set(x_290, 1, x_266);
return x_290;
}
else
{
lean_object* x_291; uint8_t x_292; 
lean_dec(x_264);
x_291 = l_Lean_Elab_Term_SavedState_restore(x_262, x_9, x_10, x_11, x_12, x_13, x_14, x_266);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_292 = !lean_is_exclusive(x_291);
if (x_292 == 0)
{
lean_object* x_293; 
x_293 = lean_ctor_get(x_291, 0);
lean_dec(x_293);
lean_ctor_set_tag(x_291, 1);
lean_ctor_set(x_291, 0, x_265);
return x_291;
}
else
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_294);
lean_dec(x_291);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_265);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
}
block_319:
{
lean_object* x_299; uint8_t x_300; 
x_299 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_298);
x_300 = !lean_is_exclusive(x_299);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_301 = lean_ctor_get(x_299, 0);
x_302 = lean_ctor_get(x_299, 1);
x_303 = l_Lean_Elab_Term_SavedState_restore(x_262, x_9, x_10, x_11, x_12, x_13, x_14, x_302);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_304 = !lean_is_exclusive(x_303);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_303, 1);
x_306 = lean_ctor_get(x_303, 0);
lean_dec(x_306);
lean_ctor_set(x_303, 1, x_301);
lean_ctor_set(x_303, 0, x_297);
x_307 = lean_array_push(x_8, x_303);
lean_ctor_set(x_299, 1, x_305);
lean_ctor_set(x_299, 0, x_307);
return x_299;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_303, 1);
lean_inc(x_308);
lean_dec(x_303);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_297);
lean_ctor_set(x_309, 1, x_301);
x_310 = lean_array_push(x_8, x_309);
lean_ctor_set(x_299, 1, x_308);
lean_ctor_set(x_299, 0, x_310);
return x_299;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_311 = lean_ctor_get(x_299, 0);
x_312 = lean_ctor_get(x_299, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_299);
x_313 = l_Lean_Elab_Term_SavedState_restore(x_262, x_9, x_10, x_11, x_12, x_13, x_14, x_312);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_315 = x_313;
} else {
 lean_dec_ref(x_313);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_297);
lean_ctor_set(x_316, 1, x_311);
x_317 = lean_array_push(x_8, x_316);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_314);
return x_318;
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
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_364; lean_object* x_365; 
x_337 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_340 = x_337;
} else {
 lean_dec_ref(x_337);
 x_340 = lean_box(0);
}
x_364 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_365 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_364, x_9, x_10, x_11, x_12, x_13, x_14, x_339);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; 
lean_dec(x_340);
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_367);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_368, 1);
lean_inc(x_370);
lean_dec(x_368);
x_371 = l_Lean_Elab_Term_SavedState_restore(x_338, x_9, x_10, x_11, x_12, x_13, x_14, x_370);
x_372 = !lean_is_exclusive(x_371);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_371, 1);
x_374 = lean_ctor_get(x_371, 0);
lean_dec(x_374);
lean_ctor_set(x_371, 1, x_369);
lean_ctor_set(x_371, 0, x_366);
x_375 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_371, x_9, x_10, x_11, x_12, x_13, x_14, x_373);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_371, 1);
lean_inc(x_376);
lean_dec(x_371);
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_366);
lean_ctor_set(x_377, 1, x_369);
x_378 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_377, x_9, x_10, x_11, x_12, x_13, x_14, x_376);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_378;
}
}
else
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_365, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_365, 1);
lean_inc(x_380);
lean_dec(x_365);
x_341 = x_379;
x_342 = x_380;
goto block_363;
}
block_363:
{
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
lean_dec(x_340);
x_343 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_342);
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
x_346 = l_Lean_Elab_Term_SavedState_restore(x_338, x_9, x_10, x_11, x_12, x_13, x_14, x_345);
x_347 = !lean_is_exclusive(x_346);
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_346, 1);
x_349 = lean_ctor_get(x_346, 0);
lean_dec(x_349);
lean_ctor_set_tag(x_346, 1);
lean_ctor_set(x_346, 1, x_344);
lean_ctor_set(x_346, 0, x_341);
x_350 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_346, x_9, x_10, x_11, x_12, x_13, x_14, x_348);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_350;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_346, 1);
lean_inc(x_351);
lean_dec(x_346);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_341);
lean_ctor_set(x_352, 1, x_344);
x_353 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_352, x_9, x_10, x_11, x_12, x_13, x_14, x_351);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; uint8_t x_356; 
lean_dec(x_8);
x_354 = lean_ctor_get(x_341, 0);
lean_inc(x_354);
x_355 = l_Lean_Elab_postponeExceptionId;
x_356 = lean_nat_dec_eq(x_354, x_355);
lean_dec(x_354);
if (x_356 == 0)
{
lean_object* x_357; 
lean_dec(x_338);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_340)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_340;
 lean_ctor_set_tag(x_357, 1);
}
lean_ctor_set(x_357, 0, x_341);
lean_ctor_set(x_357, 1, x_342);
return x_357;
}
else
{
lean_object* x_358; uint8_t x_359; 
lean_dec(x_340);
x_358 = l_Lean_Elab_Term_SavedState_restore(x_338, x_9, x_10, x_11, x_12, x_13, x_14, x_342);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_359 = !lean_is_exclusive(x_358);
if (x_359 == 0)
{
lean_object* x_360; 
x_360 = lean_ctor_get(x_358, 0);
lean_dec(x_360);
lean_ctor_set_tag(x_358, 1);
lean_ctor_set(x_358, 0, x_341);
return x_358;
}
else
{
lean_object* x_361; lean_object* x_362; 
x_361 = lean_ctor_get(x_358, 1);
lean_inc(x_361);
lean_dec(x_358);
x_362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_362, 0, x_341);
lean_ctor_set(x_362, 1, x_361);
return x_362;
}
}
}
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_409; 
x_381 = lean_box(0);
x_382 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_385 = x_382;
} else {
 lean_dec_ref(x_382);
 x_385 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_409 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_258, x_381, x_9, x_10, x_11, x_12, x_13, x_14, x_384);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; 
lean_dec(x_385);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
x_412 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_411);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec(x_412);
x_415 = l_Lean_Elab_Term_SavedState_restore(x_383, x_9, x_10, x_11, x_12, x_13, x_14, x_414);
x_416 = !lean_is_exclusive(x_415);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_417 = lean_ctor_get(x_415, 1);
x_418 = lean_ctor_get(x_415, 0);
lean_dec(x_418);
lean_ctor_set(x_415, 1, x_413);
lean_ctor_set(x_415, 0, x_410);
x_419 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_415, x_9, x_10, x_11, x_12, x_13, x_14, x_417);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_419;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_420 = lean_ctor_get(x_415, 1);
lean_inc(x_420);
lean_dec(x_415);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_410);
lean_ctor_set(x_421, 1, x_413);
x_422 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_421, x_9, x_10, x_11, x_12, x_13, x_14, x_420);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_422;
}
}
else
{
lean_object* x_423; lean_object* x_424; 
x_423 = lean_ctor_get(x_409, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_409, 1);
lean_inc(x_424);
lean_dec(x_409);
x_386 = x_423;
x_387 = x_424;
goto block_408;
}
block_408:
{
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; 
lean_dec(x_385);
x_388 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_387);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = l_Lean_Elab_Term_SavedState_restore(x_383, x_9, x_10, x_11, x_12, x_13, x_14, x_390);
x_392 = !lean_is_exclusive(x_391);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_391, 1);
x_394 = lean_ctor_get(x_391, 0);
lean_dec(x_394);
lean_ctor_set_tag(x_391, 1);
lean_ctor_set(x_391, 1, x_389);
lean_ctor_set(x_391, 0, x_386);
x_395 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_391, x_9, x_10, x_11, x_12, x_13, x_14, x_393);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_395;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_391, 1);
lean_inc(x_396);
lean_dec(x_391);
x_397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_397, 0, x_386);
lean_ctor_set(x_397, 1, x_389);
x_398 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_397, x_9, x_10, x_11, x_12, x_13, x_14, x_396);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_398;
}
}
else
{
lean_object* x_399; lean_object* x_400; uint8_t x_401; 
lean_dec(x_8);
x_399 = lean_ctor_get(x_386, 0);
lean_inc(x_399);
x_400 = l_Lean_Elab_postponeExceptionId;
x_401 = lean_nat_dec_eq(x_399, x_400);
lean_dec(x_399);
if (x_401 == 0)
{
lean_object* x_402; 
lean_dec(x_383);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_385)) {
 x_402 = lean_alloc_ctor(1, 2, 0);
} else {
 x_402 = x_385;
 lean_ctor_set_tag(x_402, 1);
}
lean_ctor_set(x_402, 0, x_386);
lean_ctor_set(x_402, 1, x_387);
return x_402;
}
else
{
lean_object* x_403; uint8_t x_404; 
lean_dec(x_385);
x_403 = l_Lean_Elab_Term_SavedState_restore(x_383, x_9, x_10, x_11, x_12, x_13, x_14, x_387);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_404 = !lean_is_exclusive(x_403);
if (x_404 == 0)
{
lean_object* x_405; 
x_405 = lean_ctor_get(x_403, 0);
lean_dec(x_405);
lean_ctor_set_tag(x_403, 1);
lean_ctor_set(x_403, 0, x_386);
return x_403;
}
else
{
lean_object* x_406; lean_object* x_407; 
x_406 = lean_ctor_get(x_403, 1);
lean_inc(x_406);
lean_dec(x_403);
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_386);
lean_ctor_set(x_407, 1, x_406);
return x_407;
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
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_433 = lean_unsigned_to_nat(2u);
x_434 = l_Lean_Syntax_getArg(x_1, x_433);
lean_dec(x_1);
x_435 = l_Lean_Syntax_getArgs(x_434);
lean_dec(x_434);
x_436 = l_Array_empty___closed__1;
x_437 = l_Array_foldlStepMAux___main___at_Lean_Syntax_getSepArgs___spec__1(x_433, x_435, x_254, x_436);
lean_dec(x_435);
x_438 = l_Lean_Elab_Term_elabExplicitUnivs(x_437, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_437);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
lean_dec(x_438);
x_441 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(x_255, x_439, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_440);
return x_441;
}
else
{
uint8_t x_442; 
lean_dec(x_255);
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
x_442 = !lean_is_exclusive(x_438);
if (x_442 == 0)
{
return x_438;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_438, 0);
x_444 = lean_ctor_get(x_438, 1);
lean_inc(x_444);
lean_inc(x_443);
lean_dec(x_438);
x_445 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
return x_445;
}
}
}
}
}
block_245:
{
lean_object* x_201; uint8_t x_202; 
lean_dec(x_200);
x_201 = l___private_Lean_Elab_Term_0__Lean_Elab_Term_isExplicit___closed__2;
lean_inc(x_1);
x_202 = l_Lean_Syntax_isOfKind(x_1, x_201);
if (x_202 == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = l_Lean_mkHole___closed__2;
lean_inc(x_1);
x_204 = l_Lean_Syntax_isOfKind(x_1, x_203);
if (x_204 == 0)
{
lean_object* x_205; 
x_205 = lean_box(0);
x_16 = x_205;
goto block_193;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_206 = l_Lean_Syntax_getArgs(x_1);
x_207 = lean_array_get_size(x_206);
lean_dec(x_206);
x_208 = lean_unsigned_to_nat(1u);
x_209 = lean_nat_dec_eq(x_207, x_208);
lean_dec(x_207);
if (x_209 == 0)
{
lean_object* x_210; 
x_210 = lean_box(0);
x_16 = x_210;
goto block_193;
}
else
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_211 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3;
x_212 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_211, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_212;
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_213 = l_Lean_Syntax_getArgs(x_1);
x_214 = lean_array_get_size(x_213);
lean_dec(x_213);
x_215 = lean_unsigned_to_nat(2u);
x_216 = lean_nat_dec_eq(x_214, x_215);
if (x_216 == 0)
{
lean_object* x_217; uint8_t x_218; 
x_217 = l_Lean_mkHole___closed__2;
lean_inc(x_1);
x_218 = l_Lean_Syntax_isOfKind(x_1, x_217);
if (x_218 == 0)
{
lean_object* x_219; 
lean_dec(x_214);
x_219 = lean_box(0);
x_16 = x_219;
goto block_193;
}
else
{
lean_object* x_220; uint8_t x_221; 
x_220 = lean_unsigned_to_nat(1u);
x_221 = lean_nat_dec_eq(x_214, x_220);
lean_dec(x_214);
if (x_221 == 0)
{
lean_object* x_222; 
x_222 = lean_box(0);
x_16 = x_222;
goto block_193;
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_223 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__3;
x_224 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_223, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_224;
}
}
}
else
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; 
lean_dec(x_214);
x_225 = lean_unsigned_to_nat(1u);
x_226 = l_Lean_Syntax_getArg(x_1, x_225);
lean_inc(x_226);
x_227 = l_Lean_Syntax_isOfKind(x_226, x_198);
if (x_227 == 0)
{
lean_object* x_228; uint8_t x_229; 
x_228 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__8;
lean_inc(x_226);
x_229 = l_Lean_Syntax_isOfKind(x_226, x_228);
if (x_229 == 0)
{
lean_object* x_230; 
lean_dec(x_226);
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
x_230 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___rarg(x_15);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_231 = l_Lean_Syntax_getArgs(x_226);
x_232 = lean_array_get_size(x_231);
lean_dec(x_231);
x_233 = lean_unsigned_to_nat(4u);
x_234 = lean_nat_dec_eq(x_232, x_233);
lean_dec(x_232);
if (x_234 == 0)
{
lean_object* x_235; 
lean_dec(x_226);
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
x_235 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___rarg(x_15);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_236 = lean_unsigned_to_nat(0u);
x_237 = l_Lean_Syntax_getArg(x_226, x_236);
lean_dec(x_226);
x_238 = l_Lean_Syntax_isOfKind(x_237, x_198);
if (x_238 == 0)
{
lean_object* x_239; 
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
x_239 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__1___rarg(x_15);
return x_239;
}
else
{
lean_object* x_240; uint8_t x_241; 
x_240 = l_Lean_Syntax_getArg(x_1, x_225);
lean_dec(x_1);
x_241 = 1;
x_1 = x_240;
x_6 = x_241;
goto _start;
}
}
}
}
else
{
uint8_t x_243; 
lean_dec(x_1);
x_243 = 1;
x_1 = x_226;
x_6 = x_243;
goto _start;
}
}
}
}
}
else
{
lean_object* x_446; lean_object* x_447; 
x_446 = lean_box(0);
x_447 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFnId(x_1, x_446, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_447;
}
}
block_491:
{
lean_object* x_450; uint8_t x_451; 
lean_dec(x_449);
x_450 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__10;
lean_inc(x_1);
x_451 = l_Lean_Syntax_isOfKind(x_1, x_450);
if (x_451 == 0)
{
lean_object* x_452; uint8_t x_453; 
x_452 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12;
lean_inc(x_1);
x_453 = l_Lean_Syntax_isOfKind(x_1, x_452);
if (x_453 == 0)
{
lean_object* x_454; 
x_454 = lean_box(0);
x_197 = x_454;
goto block_448;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; 
x_455 = l_Lean_Syntax_getArgs(x_1);
x_456 = lean_array_get_size(x_455);
lean_dec(x_455);
x_457 = lean_unsigned_to_nat(3u);
x_458 = lean_nat_dec_eq(x_456, x_457);
lean_dec(x_456);
if (x_458 == 0)
{
lean_object* x_459; 
x_459 = lean_box(0);
x_197 = x_459;
goto block_448;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; 
x_460 = lean_unsigned_to_nat(0u);
x_461 = l_Lean_Syntax_getArg(x_1, x_460);
x_462 = l_Lean_identKind___closed__2;
x_463 = l_Lean_Syntax_isOfKind(x_461, x_462);
if (x_463 == 0)
{
lean_object* x_464; 
x_464 = lean_box(0);
x_16 = x_464;
goto block_193;
}
else
{
lean_object* x_465; lean_object* x_466; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_465 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__6;
x_466 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_465, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_466;
}
}
}
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; 
x_467 = l_Lean_Syntax_getArgs(x_1);
x_468 = lean_array_get_size(x_467);
lean_dec(x_467);
x_469 = lean_unsigned_to_nat(4u);
x_470 = lean_nat_dec_eq(x_468, x_469);
if (x_470 == 0)
{
lean_object* x_471; uint8_t x_472; 
x_471 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__12;
lean_inc(x_1);
x_472 = l_Lean_Syntax_isOfKind(x_1, x_471);
if (x_472 == 0)
{
lean_object* x_473; 
lean_dec(x_468);
x_473 = lean_box(0);
x_197 = x_473;
goto block_448;
}
else
{
lean_object* x_474; uint8_t x_475; 
x_474 = lean_unsigned_to_nat(3u);
x_475 = lean_nat_dec_eq(x_468, x_474);
lean_dec(x_468);
if (x_475 == 0)
{
lean_object* x_476; 
x_476 = lean_box(0);
x_197 = x_476;
goto block_448;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; 
x_477 = lean_unsigned_to_nat(0u);
x_478 = l_Lean_Syntax_getArg(x_1, x_477);
x_479 = l_Lean_identKind___closed__2;
x_480 = l_Lean_Syntax_isOfKind(x_478, x_479);
if (x_480 == 0)
{
lean_object* x_481; 
x_481 = lean_box(0);
x_16 = x_481;
goto block_193;
}
else
{
lean_object* x_482; lean_object* x_483; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_482 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__6;
x_483 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_482, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_483;
}
}
}
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
lean_dec(x_468);
x_484 = lean_unsigned_to_nat(0u);
x_485 = l_Lean_Syntax_getArg(x_1, x_484);
x_486 = lean_unsigned_to_nat(2u);
x_487 = l_Lean_Syntax_getArg(x_1, x_486);
lean_dec(x_1);
x_488 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_488, 0, x_487);
x_489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_2);
x_1 = x_485;
x_2 = x_489;
goto _start;
}
}
}
block_517:
{
lean_object* x_493; uint8_t x_494; 
lean_dec(x_492);
x_493 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__15;
lean_inc(x_1);
x_494 = l_Lean_Syntax_isOfKind(x_1, x_493);
if (x_494 == 0)
{
lean_object* x_495; 
x_495 = lean_box(0);
x_449 = x_495;
goto block_491;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; uint8_t x_499; 
x_496 = l_Lean_Syntax_getArgs(x_1);
x_497 = lean_array_get_size(x_496);
lean_dec(x_496);
x_498 = lean_unsigned_to_nat(3u);
x_499 = lean_nat_dec_eq(x_497, x_498);
lean_dec(x_497);
if (x_499 == 0)
{
lean_object* x_500; 
x_500 = lean_box(0);
x_449 = x_500;
goto block_491;
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_501 = lean_unsigned_to_nat(0u);
x_502 = l_Lean_Syntax_getArg(x_1, x_501);
x_503 = lean_unsigned_to_nat(2u);
x_504 = l_Lean_Syntax_getArg(x_1, x_503);
lean_dec(x_1);
x_505 = l_Lean_Elab_Term_getCurrMacroScope(x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_506 = lean_ctor_get(x_505, 1);
lean_inc(x_506);
lean_dec(x_505);
x_507 = l_Lean_Elab_Term_getMainModule___rarg(x_14, x_506);
x_508 = lean_ctor_get(x_507, 1);
lean_inc(x_508);
lean_dec(x_507);
x_509 = l_Array_empty___closed__1;
x_510 = lean_array_push(x_509, x_502);
x_511 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__16;
x_512 = lean_array_push(x_510, x_511);
x_513 = lean_array_push(x_512, x_504);
x_514 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___closed__13;
x_515 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_513);
x_1 = x_515;
x_15 = x_508;
goto _start;
}
}
}
}
else
{
lean_object* x_728; uint8_t x_729; 
x_728 = l_Lean_Syntax_getArgs(x_1);
x_729 = !lean_is_exclusive(x_9);
if (x_729 == 0)
{
uint8_t x_730; lean_object* x_731; lean_object* x_732; 
x_730 = 0;
lean_ctor_set_uint8(x_9, sizeof(void*)*8 + 1, x_730);
x_731 = lean_unsigned_to_nat(0u);
x_732 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_728, x_731, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_728);
lean_dec(x_1);
return x_732;
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; uint8_t x_741; uint8_t x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_733 = lean_ctor_get(x_9, 0);
x_734 = lean_ctor_get(x_9, 1);
x_735 = lean_ctor_get(x_9, 2);
x_736 = lean_ctor_get(x_9, 3);
x_737 = lean_ctor_get(x_9, 4);
x_738 = lean_ctor_get(x_9, 5);
x_739 = lean_ctor_get(x_9, 6);
x_740 = lean_ctor_get(x_9, 7);
x_741 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
lean_inc(x_740);
lean_inc(x_739);
lean_inc(x_738);
lean_inc(x_737);
lean_inc(x_736);
lean_inc(x_735);
lean_inc(x_734);
lean_inc(x_733);
lean_dec(x_9);
x_742 = 0;
x_743 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_743, 0, x_733);
lean_ctor_set(x_743, 1, x_734);
lean_ctor_set(x_743, 2, x_735);
lean_ctor_set(x_743, 3, x_736);
lean_ctor_set(x_743, 4, x_737);
lean_ctor_set(x_743, 5, x_738);
lean_ctor_set(x_743, 6, x_739);
lean_ctor_set(x_743, 7, x_740);
lean_ctor_set_uint8(x_743, sizeof(void*)*8, x_741);
lean_ctor_set_uint8(x_743, sizeof(void*)*8 + 1, x_742);
x_744 = lean_unsigned_to_nat(0u);
x_745 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_728, x_744, x_8, x_743, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_728);
lean_dec(x_1);
return x_745;
}
}
block_193:
{
uint8_t x_17; uint8_t x_18; 
lean_dec(x_16);
x_17 = l_List_isEmpty___rarg(x_2);
if (x_7 == 0)
{
uint8_t x_191; 
x_191 = 1;
x_18 = x_191;
goto block_190;
}
else
{
uint8_t x_192; 
x_192 = 0;
x_18 = x_192;
goto block_190;
}
block_190:
{
uint8_t x_19; 
if (x_17 == 0)
{
uint8_t x_186; 
x_186 = 0;
x_19 = x_186;
goto block_185;
}
else
{
uint8_t x_187; 
x_187 = l_Array_isEmpty___rarg(x_3);
if (x_187 == 0)
{
uint8_t x_188; 
x_188 = 0;
x_19 = x_188;
goto block_185;
}
else
{
uint8_t x_189; 
x_189 = l_Array_isEmpty___rarg(x_4);
x_19 = x_189;
goto block_185;
}
}
block_185:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_57; lean_object* x_58; lean_object* x_80; 
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
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
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_80 = l_Lean_Elab_Term_elabTerm(x_1, x_20, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_23);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_83 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLVals(x_81, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_82);
if (lean_obj_tag(x_83) == 0)
{
if (x_7 == 0)
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
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_88 = l_Lean_Elab_Term_ensureHasType(x_5, x_86, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_87);
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
x_27 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = l_Lean_Elab_Term_SavedState_restore(x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_30);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
x_35 = lean_array_push(x_8, x_31);
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
x_38 = lean_array_push(x_8, x_37);
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
x_41 = l_Lean_Elab_Term_SavedState_restore(x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_40);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
x_45 = lean_array_push(x_8, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_8);
x_47 = lean_ctor_get(x_25, 0);
lean_inc(x_47);
x_48 = l_Lean_Elab_postponeExceptionId;
x_49 = lean_nat_dec_eq(x_47, x_48);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
x_51 = l_Lean_Elab_Term_SavedState_restore(x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_26);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
x_59 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_58);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
x_63 = l_Lean_Elab_Term_SavedState_restore(x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_62);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 1);
x_66 = lean_ctor_get(x_63, 0);
lean_dec(x_66);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 0, x_57);
x_67 = lean_array_push(x_8, x_63);
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
x_70 = lean_array_push(x_8, x_69);
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
x_73 = l_Lean_Elab_Term_SavedState_restore(x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_72);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
x_77 = lean_array_push(x_8, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_74);
return x_78;
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
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_124; lean_object* x_125; 
x_97 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
x_124 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_125 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_124, x_9, x_10, x_11, x_12, x_13, x_14, x_99);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_100);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_127);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_Lean_Elab_Term_SavedState_restore(x_98, x_9, x_10, x_11, x_12, x_13, x_14, x_130);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_131, 1);
x_134 = lean_ctor_get(x_131, 0);
lean_dec(x_134);
lean_ctor_set(x_131, 1, x_129);
lean_ctor_set(x_131, 0, x_126);
x_135 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_131, x_9, x_10, x_11, x_12, x_13, x_14, x_133);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_131, 1);
lean_inc(x_136);
lean_dec(x_131);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_126);
lean_ctor_set(x_137, 1, x_129);
x_138 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_137, x_9, x_10, x_11, x_12, x_13, x_14, x_136);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_125, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_125, 1);
lean_inc(x_140);
lean_dec(x_125);
x_101 = x_139;
x_102 = x_140;
goto block_123;
}
block_123:
{
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_100);
x_103 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_Elab_Term_SavedState_restore(x_98, x_9, x_10, x_11, x_12, x_13, x_14, x_105);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_106, 1);
x_109 = lean_ctor_get(x_106, 0);
lean_dec(x_109);
lean_ctor_set_tag(x_106, 1);
lean_ctor_set(x_106, 1, x_104);
lean_ctor_set(x_106, 0, x_101);
x_110 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_106, x_9, x_10, x_11, x_12, x_13, x_14, x_108);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_dec(x_106);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_101);
lean_ctor_set(x_112, 1, x_104);
x_113 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_112, x_9, x_10, x_11, x_12, x_13, x_14, x_111);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_8);
x_114 = lean_ctor_get(x_101, 0);
lean_inc(x_114);
x_115 = l_Lean_Elab_postponeExceptionId;
x_116 = lean_nat_dec_eq(x_114, x_115);
lean_dec(x_114);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_98);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_100)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_100;
 lean_ctor_set_tag(x_117, 1);
}
lean_ctor_set(x_117, 0, x_101);
lean_ctor_set(x_117, 1, x_102);
return x_117;
}
else
{
lean_object* x_118; uint8_t x_119; 
lean_dec(x_100);
x_118 = l_Lean_Elab_Term_SavedState_restore(x_98, x_9, x_10, x_11, x_12, x_13, x_14, x_102);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_118, 0);
lean_dec(x_120);
lean_ctor_set_tag(x_118, 1);
lean_ctor_set(x_118, 0, x_101);
return x_118;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_101);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_169; 
x_141 = lean_box(0);
x_142 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_145 = x_142;
} else {
 lean_dec_ref(x_142);
 x_145 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_169 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_18, x_141, x_9, x_10, x_11, x_12, x_13, x_14, x_144);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
lean_dec(x_145);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_171);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = l_Lean_Elab_Term_SavedState_restore(x_143, x_9, x_10, x_11, x_12, x_13, x_14, x_174);
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_175, 1);
x_178 = lean_ctor_get(x_175, 0);
lean_dec(x_178);
lean_ctor_set(x_175, 1, x_173);
lean_ctor_set(x_175, 0, x_170);
x_179 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_175, x_9, x_10, x_11, x_12, x_13, x_14, x_177);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_175, 1);
lean_inc(x_180);
lean_dec(x_175);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_170);
lean_ctor_set(x_181, 1, x_173);
x_182 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_181, x_9, x_10, x_11, x_12, x_13, x_14, x_180);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_169, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_169, 1);
lean_inc(x_184);
lean_dec(x_169);
x_146 = x_183;
x_147 = x_184;
goto block_168;
}
block_168:
{
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
lean_dec(x_145);
x_148 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_147);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l_Lean_Elab_Term_SavedState_restore(x_143, x_9, x_10, x_11, x_12, x_13, x_14, x_150);
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_151, 1);
x_154 = lean_ctor_get(x_151, 0);
lean_dec(x_154);
lean_ctor_set_tag(x_151, 1);
lean_ctor_set(x_151, 1, x_149);
lean_ctor_set(x_151, 0, x_146);
x_155 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_151, x_9, x_10, x_11, x_12, x_13, x_14, x_153);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_151, 1);
lean_inc(x_156);
lean_dec(x_151);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_146);
lean_ctor_set(x_157, 1, x_149);
x_158 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___lambda__1(x_8, x_157, x_9, x_10, x_11, x_12, x_13, x_14, x_156);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_dec(x_8);
x_159 = lean_ctor_get(x_146, 0);
lean_inc(x_159);
x_160 = l_Lean_Elab_postponeExceptionId;
x_161 = lean_nat_dec_eq(x_159, x_160);
lean_dec(x_159);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_143);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_145)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_145;
 lean_ctor_set_tag(x_162, 1);
}
lean_ctor_set(x_162, 0, x_146);
lean_ctor_set(x_162, 1, x_147);
return x_162;
}
else
{
lean_object* x_163; uint8_t x_164; 
lean_dec(x_145);
x_163 = l_Lean_Elab_Term_SavedState_restore(x_143, x_9, x_10, x_11, x_12, x_13, x_14, x_147);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_163, 0);
lean_dec(x_165);
lean_ctor_set_tag(x_163, 1);
lean_ctor_set(x_163, 0, x_146);
return x_163;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_146);
lean_ctor_set(x_167, 1, x_166);
return x_167;
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___spec__3(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_1);
return x_18;
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn(x_1, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
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
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_String_Iterator_HasRepr___closed__2;
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
x_20 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
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
x_27 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__2;
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
x_47 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
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
x_54 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
x_57 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__2;
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
x_4 = l_Lean_MessageData_joinSep___main(x_2, x_3);
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
x_3 = lean_unsigned_to_nat(767u);
x_4 = lean_unsigned_to_nat(33u);
x_5 = l_Lean_ResolveName_resolveNamespaceUsingScope___closed__3;
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
x_19 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
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
x_3 = lean_unsigned_to_nat(787u);
x_4 = lean_unsigned_to_nat(33u);
x_5 = l_Lean_ResolveName_resolveNamespaceUsingScope___closed__3;
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
x_26 = l_Lean_MessageData_Inhabited;
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
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_15 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppFn(x_1, x_12, x_2, x_3, x_4, x_13, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_22 = l_Array_filterAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_getSuccess___spec__1(x_16, x_21, x_21);
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_9, 3);
x_28 = l_Lean_replaceRef(x_1, x_27);
lean_dec(x_1);
x_29 = l_Lean_replaceRef(x_28, x_27);
lean_dec(x_27);
lean_dec(x_28);
lean_ctor_set(x_9, 3, x_29);
x_30 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_9, 0);
x_32 = lean_ctor_get(x_9, 1);
x_33 = lean_ctor_get(x_9, 2);
x_34 = lean_ctor_get(x_9, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_9);
x_35 = l_Lean_replaceRef(x_1, x_34);
lean_dec(x_1);
x_36 = l_Lean_replaceRef(x_35, x_34);
lean_dec(x_34);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_33);
lean_ctor_set(x_37, 3, x_36);
x_38 = l___private_Lean_Elab_App_0__Lean_Elab_Term_mergeFailures___rarg(x_16, x_5, x_6, x_7, x_8, x_37, x_10, x_17);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_16);
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_9, 0);
lean_inc(x_40);
x_41 = x_22;
x_42 = l_Array_umapMAux___main___at___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___spec__1(x_39, x_40, x_21, x_41);
x_43 = x_42;
x_44 = l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageList(x_43);
lean_dec(x_43);
x_45 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__3;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_1, x_46, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_1);
x_48 = l_Lean_Elab_Term_TermElabResult_inhabited;
x_49 = lean_array_get(x_48, x_22, x_21);
lean_dec(x_22);
x_50 = l_Lean_Elab_Term_applyResult(x_49, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
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
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_1);
x_59 = l_Lean_Elab_Term_TermElabResult_inhabited;
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_array_get(x_59, x_16, x_60);
lean_dec(x_16);
x_62 = l_Lean_Elab_Term_applyResult(x_61, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_15);
if (x_63 == 0)
{
return x_15;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_15, 0);
x_65 = lean_ctor_get(x_15, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_15);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
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
lean_object* l_Lean_Elab_Term_expandApp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_importModules___closed__1;
x_16 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1(x_1, x_2, x_3, x_3, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_box(x_4);
lean_ctor_set(x_18, 1, x_22);
lean_ctor_set(x_18, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_box(x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_35 = x_31;
} else {
 lean_dec_ref(x_31);
 x_35 = lean_box(0);
}
x_36 = lean_box(x_4);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_16);
if (x_41 == 0)
{
return x_16;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_16, 0);
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_16);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
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
static lean_object* _init_l_Lean_Elab_Term_expandApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'..' is only allowed in patterns");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandApp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandApp___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_expandApp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandApp___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_expandApp(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_37; uint8_t x_38; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_14);
x_37 = l_Lean_Elab_Term_expandApp___closed__2;
x_38 = l_Lean_Syntax_isOfKind(x_15, x_37);
if (x_38 == 0)
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_39 = 0;
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_14);
lean_ctor_set(x_41, 1, x_40);
x_16 = x_41;
goto block_36;
}
else
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_array_pop(x_14);
x_43 = 1;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_16 = x_45;
goto block_36;
}
block_36:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
if (x_2 == 0)
{
uint8_t x_33; 
x_33 = lean_unbox(x_18);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = 1;
x_19 = x_34;
goto block_32;
}
else
{
x_19 = x_2;
goto block_32;
}
}
else
{
uint8_t x_35; 
x_35 = 1;
x_19 = x_35;
goto block_32;
}
block_32:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_18);
lean_dec(x_11);
x_20 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_17);
lean_dec(x_17);
x_21 = l_Lean_Elab_Term_expandApp___closed__5;
x_22 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_20);
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
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_27 = l_Lean_mkAppStx___closed__6;
x_28 = l_Lean_Elab_Term_expandApp___closed__2;
x_29 = lean_box(0);
x_30 = lean_unbox(x_18);
lean_dec(x_18);
x_31 = l_Lean_Elab_Term_expandApp___lambda__1(x_27, x_28, x_17, x_30, x_11, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_17);
return x_31;
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
lean_object* l_Lean_Elab_Term_expandApp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_Elab_Term_expandApp___lambda__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
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
x_19 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux(x_16, x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
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
lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Array_empty___closed__1;
x_11 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux(x_1, x_10, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
lean_object* l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_7346_(lean_object* x_1) {
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
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__5 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___lambda__1___closed__5);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_tryCoeFun___closed__4);
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
l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__10 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_ElabAppArgs_propagateExpectedType___closed__10);
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
l_Lean_Elab_Term_ElabAppArgs_main___rarg___closed__1 = _init_l_Lean_Elab_Term_ElabAppArgs_main___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_ElabAppArgs_main___rarg___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__1 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__1);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__2);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__3);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__4 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__4);
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__5 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppArgs___closed__5);
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
l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__2 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_toMessageData___closed__2);
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
l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__3 = _init_l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppAux___closed__3);
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
l_Lean_Elab_Term_expandApp___closed__3 = _init_l_Lean_Elab_Term_expandApp___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_expandApp___closed__3);
l_Lean_Elab_Term_expandApp___closed__4 = _init_l_Lean_Elab_Term_expandApp___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_expandApp___closed__4);
l_Lean_Elab_Term_expandApp___closed__5 = _init_l_Lean_Elab_Term_expandApp___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_expandApp___closed__5);
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
res = l_Lean_Elab_Term_initFn____x40_Lean_Elab_App___hyg_7346_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
