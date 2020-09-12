// Lean compiler output
// Module: Lean.Elab.App
// Imports: Init Lean.Util.FindMVar Lean.Elab.Term Lean.Elab.Binders
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
lean_object* l___private_Lean_Elab_App_19__elabAppLValsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__5;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_7__hasOnlyTypeMVar___boxed(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__23;
lean_object* l___private_Lean_Elab_App_20__elabAppLVals___closed__3;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__12;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__13;
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__3;
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__11;
lean_object* l___private_Lean_Elab_App_9__nextArgIsHole___boxed(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__5;
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__7;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(lean_object*, lean_object*);
extern lean_object* l_Lean_fieldIdxKind___closed__2;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__21;
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__18;
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_15__resolveLValLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l___private_Lean_Elab_App_17__mkBaseProjections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_18__addLValArg___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__6;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___closed__3;
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__2;
lean_object* l___private_Lean_Meta_InferType_22__isTypeFormerTypeImp___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__5;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
lean_object* l___private_Lean_Elab_Term_4__liftMetaMFinalizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__7;
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_App_5__getForallBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__6;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__17;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_App_9__nextArgIsHole(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_12__throwLValError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__10;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__8;
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent(lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__20;
uint8_t l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorContext___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_18__addLValArg___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_hasToString(lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__27;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__11;
lean_object* l___private_Lean_Elab_App_13__findMethod_x3f___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__9;
lean_object* l___private_Lean_Elab_App_17__mkBaseProjections___closed__2;
lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___closed__1;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_3__mkArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_13__findMethod_x3f___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__2;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__6;
lean_object* l___private_Lean_Elab_App_17__mkBaseProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_inhabited;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__mkBaseProjections___closed__1;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__4;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__1;
extern lean_object* l_Lean_mkAppStx___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__5;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__9;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__3;
lean_object* l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__3;
lean_object* l___private_Lean_Elab_App_18__addLValArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppFnId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_repr___main___closed__13;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__2;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__14;
lean_object* l_Lean_Elab_Term_registerMVarErrorContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__28;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__3;
lean_object* l___private_Lean_Elab_App_22__elabAppFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__5;
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__6;
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_15__resolveLValLoop___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__18;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__15;
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshAnonymousName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1;
lean_object* l___private_Lean_Elab_App_6__hasTypeMVar___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__1;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__13;
uint8_t l___private_Lean_Elab_App_7__hasOnlyTypeMVar(lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_App_26__elabAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_15__resolveLValLoop___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrNamespace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__7;
extern lean_object* l_Lean_choiceKind___closed__2;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_Inhabited;
extern lean_object* l___private_Lean_Syntax_6__formatInfo___closed__1;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__6;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__7;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1___rarg(lean_object*);
lean_object* l___private_Lean_Elab_App_5__getForallBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__5;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyInfo(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__14;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__20;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__25;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__3;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__10;
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__7;
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__3;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l_Lean_Elab_Term_NamedArg_inhabited___closed__1;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_hasToString(lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__8;
extern lean_object* l_Std_PersistentArray_Stats_toString___closed__4;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_24__toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1;
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l___private_Lean_Elab_App_12__throwLValError(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit(lean_object*);
lean_object* l___private_Lean_Elab_App_19__elabAppLValsAux___main___closed__2;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__4;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__22;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__17;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Lean_Elab_App_19__elabAppLValsAux___main(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l___private_Lean_Elab_App_24__toMessageData___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_16__resolveLVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice(lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_App_6__hasTypeMVar(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__10;
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__8;
lean_object* l___private_Lean_Elab_App_19__elabAppLValsAux___main___closed__1;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__4;
lean_object* l_Lean_Elab_Term_elabIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_Elab_Term_elabApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_24__toMessageData___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__9;
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__3;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_18__useImplicitLambda_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_8__propagateExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_elabChoice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__6;
lean_object* l___private_Lean_Elab_App_15__resolveLValLoop___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_2__elabArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppFnId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__1;
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
extern lean_object* l_Lean_importModules___closed__1;
extern lean_object* l_Lean_formatEntry___closed__1;
lean_object* l___private_Lean_Elab_App_16__resolveLVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_TermElabResult_inhabited;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_25__mergeFailures___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj___closed__1;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAutoParam(lean_object*);
lean_object* l_Lean_Elab_Term_elabNamedPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_1__ensureArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
lean_object* l___private_Lean_Elab_App_19__elabAppLValsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__19;
lean_object* l_Lean_Elab_Term_mkConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_26__elabAppAux___closed__3;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l___private_Lean_Elab_App_28__regTraceClasses(lean_object*);
lean_object* l_Lean_Elab_Term_elabProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofArray(lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_24__toMessageData___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_17__mkBaseProjections___closed__3;
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_Lean_Meta_getLevel___at_Lean_Elab_Term_tryCoe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_15__resolveLValLoop___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__5;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_1__ensureArgType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__16;
extern lean_object* l_Lean_mkAppStx___closed__5;
lean_object* l_Lean_Elab_Term_elabApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1;
lean_object* l_Lean_getParentStructures(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__2;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__8;
extern lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
extern lean_object* l_Lean_Elab_postponeExceptionId;
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__13;
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
lean_object* l___private_Lean_Elab_App_26__elabAppAux___closed__2;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_saveAllState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeInstMVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__10;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__20;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_23__getSuccess(lean_object*);
lean_object* l_Lean_Exception_getRef(lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__2;
lean_object* l___private_Lean_Elab_App_12__throwLValError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l___private_Lean_Elab_App_15__resolveLValLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_27__elabAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicitUnivs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l___private_Lean_Elab_App_20__elabAppLVals___closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__12;
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__19;
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__11;
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__7;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_20__elabAppLVals___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1;
lean_object* l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData___main(lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__8;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_24__toMessageData___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__1;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__11;
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__1;
extern lean_object* l_Lean_KernelException_toMessageData___closed__12;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_3__mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1;
lean_object* l_Lean_Elab_Term_registerSyntheticMVarWithCurrRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__4;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__10;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_inhabited___closed__1;
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l_Lean_Elab_logException___at___private_Lean_Elab_Term_10__exceptionToSorry___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__1;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_25__mergeFailures___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__2(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__2;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Elab_App_8__propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_13__findMethod_x3f___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_26__elabAppAux___closed__1;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__11;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__1;
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__3;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__26;
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_24__toMessageData___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__11;
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__9;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Term_21__elabTermAux___main(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___closed__5;
lean_object* l_Lean_Elab_Term_applyResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
lean_object* l_List_map___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__8;
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_14__isExplicit___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
lean_object* l_Lean_Elab_Term_expandApp___closed__2;
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1;
lean_object* l___private_Lean_Elab_App_25__mergeFailures(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_repr___main___closed__16;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__2;
lean_object* l___private_Lean_Elab_App_13__findMethod_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_App_23__getSuccess___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_26__elabAppAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasTypeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__12;
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findField_x3f___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__1;
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__addLValArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l___private_Lean_Elab_App_20__elabAppLVals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__4;
lean_object* l___private_Lean_Elab_App_20__elabAppLVals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__4;
lean_object* l_Lean_Elab_Term_elabExplicitUnivs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___closed__2;
lean_object* l___private_Lean_Elab_App_19__elabAppLValsAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__2;
lean_object* l___private_Lean_Elab_App_11__elabAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__7;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_inhabited;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* _init_l_Lean_Elab_Term_Arg_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_Arg_inhabited() {
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
x_18 = l_Option_HasRepr___rarg___closed__3;
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
x_23 = l_Option_HasRepr___rarg___closed__3;
x_24 = lean_string_append(x_22, x_23);
return x_24;
}
}
}
lean_object* _init_l_Lean_Elab_Term_NamedArg_inhabited___closed__1() {
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
lean_object* _init_l_Lean_Elab_Term_NamedArg_inhabited() {
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
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("argument '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' was already set");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_addNamedArg___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_addNamedArg___closed__6() {
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
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Elab_Term_addNamedArg___closed__6;
x_23 = lean_alloc_ctor(9, 2, 0);
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
lean_object* l___private_Lean_Elab_App_1__ensureArgType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
x_11 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = l_Lean_Elab_Term_ensureHasTypeAux(x_14, x_12, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l___private_Lean_Elab_App_1__ensureArgType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_1__ensureArgType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
lean_object* l___private_Lean_Elab_App_2__elabArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
x_13 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Elab_Term_elabTerm(x_11, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Elab_App_1__ensureArgType(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_5);
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
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = l___private_Lean_Elab_App_1__ensureArgType(x_1, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_23;
}
}
}
lean_object* l___private_Lean_Elab_App_3__mkArrow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_mkFreshAnonymousName___rarg(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = 0;
x_14 = l_Lean_mkForall(x_12, x_13, x_1, x_2);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = 0;
x_18 = l_Lean_mkForall(x_15, x_17, x_1, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
lean_object* l___private_Lean_Elab_App_3__mkArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_3__mkArrow(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CoeFun");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_4__tryCoeFun___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("function expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_4__tryCoeFun___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_4__tryCoeFun___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeFun");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_4__tryCoeFun___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_4__tryCoeFun___closed__5;
x_2 = l_Lean_MessageData_ofList___closed__3;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_4__tryCoeFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_3);
x_10 = l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_mkSort(x_11);
lean_inc(x_1);
x_14 = l___private_Lean_Elab_App_3__mkArrow(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
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
lean_inc(x_3);
x_20 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_17, x_18, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_23 = l_Lean_Meta_getLevel___at_Lean_Elab_Term_tryCoe___spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
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
x_29 = l___private_Lean_Elab_App_4__tryCoeFun___closed__2;
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
lean_inc(x_3);
x_38 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_36, x_37, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
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
x_56 = l_Lean_Expr_mvarId_x21(x_39);
x_57 = lean_ctor_get(x_3, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_3, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_3, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_3, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_3, 5);
lean_inc(x_62);
x_63 = lean_ctor_get(x_3, 6);
lean_inc(x_63);
x_64 = lean_ctor_get(x_3, 7);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_66 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_67 = 0;
x_68 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_68, 0, x_57);
lean_ctor_set(x_68, 1, x_58);
lean_ctor_set(x_68, 2, x_59);
lean_ctor_set(x_68, 3, x_60);
lean_ctor_set(x_68, 4, x_61);
lean_ctor_set(x_68, 5, x_62);
lean_ctor_set(x_68, 6, x_63);
lean_ctor_set(x_68, 7, x_64);
lean_ctor_set_uint8(x_68, sizeof(void*)*8, x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*8 + 1, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*8 + 2, x_67);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_69 = l_Lean_Elab_Term_synthesizeInstMVarCore(x_56, x_68, x_4, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_unbox(x_70);
lean_dec(x_70);
x_42 = x_72;
x_43 = x_71;
goto block_55;
}
else
{
lean_object* x_73; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_2);
lean_dec(x_1);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_dec(x_69);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l___private_Lean_Elab_App_4__tryCoeFun___closed__8;
x_77 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_77, x_3, x_4, x_5, x_6, x_7, x_8, x_74);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
return x_78;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_78);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_73);
x_83 = lean_ctor_get(x_69, 1);
lean_inc(x_83);
lean_dec(x_69);
x_84 = l___private_Lean_Elab_App_4__tryCoeFun___closed__5;
x_85 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_84, x_3, x_4, x_5, x_6, x_7, x_8, x_83);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
block_55:
{
if (x_42 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_2);
lean_dec(x_1);
x_44 = l___private_Lean_Elab_App_4__tryCoeFun___closed__5;
x_45 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_46 = l___private_Lean_Elab_App_4__tryCoeFun___closed__7;
x_47 = l_Lean_mkConst(x_46, x_28);
x_48 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_49 = lean_array_push(x_48, x_1);
x_50 = lean_array_push(x_49, x_21);
x_51 = lean_array_push(x_50, x_2);
x_52 = lean_array_push(x_51, x_39);
x_53 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_52, x_52, x_34, x_47);
lean_dec(x_52);
if (lean_is_scalar(x_41)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_41;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_43);
return x_54;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_23);
if (x_90 == 0)
{
return x_23;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_23, 0);
x_92 = lean_ctor_get(x_23, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_23);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_4__tryCoeFun(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_App_5__getForallBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1(x_4, x_2, x_8);
lean_dec(x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; uint8_t x_11; 
x_10 = (uint8_t)((x_7 << 24) >> 61);
x_11 = l_Lean_BinderInfo_isExplicit(x_10);
if (x_11 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
x_3 = x_6;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_8, x_1);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isAutoParam(x_5);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Expr_isOptParam(x_5);
lean_dec(x_5);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_3);
return x_16;
}
else
{
lean_dec(x_3);
x_3 = x_6;
goto _start;
}
}
else
{
lean_dec(x_5);
lean_dec(x_3);
x_3 = x_6;
goto _start;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_1, x_19);
lean_dec(x_1);
x_1 = x_20;
x_3 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
lean_dec(x_3);
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
lean_dec(x_9);
x_23 = l_Array_eraseIdx___rarg(x_2, x_22);
lean_dec(x_22);
x_2 = x_23;
x_3 = x_6;
goto _start;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_1, x_25);
lean_dec(x_1);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(0);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = l_Array_isEmpty___rarg(x_2);
lean_dec(x_2);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_3);
x_29 = lean_box(0);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_3);
return x_30;
}
}
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_5__getForallBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_App_5__getForallBody___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_1, 6);
x_6 = l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorContext___spec__2(x_5, x_4);
if (x_6 == 0)
{
return x_3;
}
else
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_Expr_hasMVar(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasMVar(x_9);
if (x_11 == 0)
{
return x_3;
}
else
{
x_2 = x_9;
goto _start;
}
}
else
{
lean_object* x_13; 
x_13 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1(x_1, x_8, x_3);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_hasMVar(x_9);
if (x_14 == 0)
{
return x_13;
}
else
{
x_2 = x_9;
x_3 = x_13;
goto _start;
}
}
else
{
return x_13;
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
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
x_18 = l_Lean_Expr_hasMVar(x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_hasMVar(x_17);
if (x_19 == 0)
{
return x_3;
}
else
{
x_2 = x_17;
goto _start;
}
}
else
{
lean_object* x_21; 
x_21 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1(x_1, x_16, x_3);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_hasMVar(x_17);
if (x_22 == 0)
{
return x_21;
}
else
{
x_2 = x_17;
x_3 = x_21;
goto _start;
}
}
else
{
return x_21;
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
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = l_Lean_Expr_hasMVar(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_hasMVar(x_25);
if (x_27 == 0)
{
return x_3;
}
else
{
x_2 = x_25;
goto _start;
}
}
else
{
lean_object* x_29; 
x_29 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1(x_1, x_24, x_3);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Expr_hasMVar(x_25);
if (x_30 == 0)
{
return x_29;
}
else
{
x_2 = x_25;
x_3 = x_29;
goto _start;
}
}
else
{
return x_29;
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_2, 1);
x_33 = lean_ctor_get(x_2, 2);
x_34 = lean_ctor_get(x_2, 3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Expr_hasMVar(x_32);
if (x_43 == 0)
{
x_35 = x_3;
goto block_42;
}
else
{
lean_object* x_44; 
x_44 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1(x_1, x_32, x_3);
if (lean_obj_tag(x_44) == 0)
{
x_35 = x_44;
goto block_42;
}
else
{
return x_44;
}
}
}
else
{
return x_3;
}
block_42:
{
uint8_t x_36; 
x_36 = l_Lean_Expr_hasMVar(x_33);
if (x_36 == 0)
{
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Expr_hasMVar(x_34);
if (x_37 == 0)
{
return x_35;
}
else
{
x_2 = x_34;
x_3 = x_35;
goto _start;
}
}
else
{
return x_35;
}
}
else
{
lean_object* x_39; 
x_39 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1(x_1, x_33, x_35);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Expr_hasMVar(x_34);
if (x_40 == 0)
{
return x_39;
}
else
{
x_2 = x_34;
x_3 = x_39;
goto _start;
}
}
else
{
return x_39;
}
}
}
}
case 10:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_2, 1);
x_46 = l_Lean_Expr_hasMVar(x_45);
if (x_46 == 0)
{
return x_3;
}
else
{
x_2 = x_45;
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
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_2, 2);
x_49 = l_Lean_Expr_hasMVar(x_48);
if (x_49 == 0)
{
return x_3;
}
else
{
x_2 = x_48;
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
uint8_t l___private_Lean_Elab_App_6__hasTypeMVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
}
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_6__hasTypeMVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_App_6__hasTypeMVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_1, 6);
x_6 = l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorContext___spec__2(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_Expr_hasMVar(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasMVar(x_9);
if (x_11 == 0)
{
return x_3;
}
else
{
x_2 = x_9;
goto _start;
}
}
else
{
lean_object* x_13; 
x_13 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_8, x_3);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_hasMVar(x_9);
if (x_14 == 0)
{
return x_13;
}
else
{
x_2 = x_9;
x_3 = x_13;
goto _start;
}
}
else
{
return x_13;
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
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
x_18 = l_Lean_Expr_hasMVar(x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_hasMVar(x_17);
if (x_19 == 0)
{
return x_3;
}
else
{
x_2 = x_17;
goto _start;
}
}
else
{
lean_object* x_21; 
x_21 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_16, x_3);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_hasMVar(x_17);
if (x_22 == 0)
{
return x_21;
}
else
{
x_2 = x_17;
x_3 = x_21;
goto _start;
}
}
else
{
return x_21;
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
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = l_Lean_Expr_hasMVar(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_hasMVar(x_25);
if (x_27 == 0)
{
return x_3;
}
else
{
x_2 = x_25;
goto _start;
}
}
else
{
lean_object* x_29; 
x_29 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_24, x_3);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Expr_hasMVar(x_25);
if (x_30 == 0)
{
return x_29;
}
else
{
x_2 = x_25;
x_3 = x_29;
goto _start;
}
}
else
{
return x_29;
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_2, 1);
x_33 = lean_ctor_get(x_2, 2);
x_34 = lean_ctor_get(x_2, 3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Expr_hasMVar(x_32);
if (x_43 == 0)
{
x_35 = x_3;
goto block_42;
}
else
{
lean_object* x_44; 
x_44 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_32, x_3);
if (lean_obj_tag(x_44) == 0)
{
x_35 = x_44;
goto block_42;
}
else
{
return x_44;
}
}
}
else
{
return x_3;
}
block_42:
{
uint8_t x_36; 
x_36 = l_Lean_Expr_hasMVar(x_33);
if (x_36 == 0)
{
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Expr_hasMVar(x_34);
if (x_37 == 0)
{
return x_35;
}
else
{
x_2 = x_34;
x_3 = x_35;
goto _start;
}
}
else
{
return x_35;
}
}
else
{
lean_object* x_39; 
x_39 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_33, x_35);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Expr_hasMVar(x_34);
if (x_40 == 0)
{
return x_39;
}
else
{
x_2 = x_34;
x_3 = x_39;
goto _start;
}
}
else
{
return x_39;
}
}
}
}
case 10:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_2, 1);
x_46 = l_Lean_Expr_hasMVar(x_45);
if (x_46 == 0)
{
return x_3;
}
else
{
x_2 = x_45;
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
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_2, 2);
x_49 = l_Lean_Expr_hasMVar(x_48);
if (x_49 == 0)
{
return x_3;
}
else
{
x_2 = x_48;
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
uint8_t l___private_Lean_Elab_App_7__hasOnlyTypeMVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_7__hasOnlyTypeMVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_App_7__hasOnlyTypeMVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_8__propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*8 + 1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 6);
lean_inc(x_13);
x_14 = l_Array_isEmpty___rarg(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_7, 3);
x_21 = l_Lean_replaceRef(x_12, x_20);
lean_dec(x_12);
x_22 = l_Lean_replaceRef(x_21, x_20);
lean_dec(x_21);
x_23 = l_Lean_replaceRef(x_22, x_20);
lean_dec(x_20);
lean_dec(x_22);
lean_ctor_set(x_7, 3, x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_array_get_size(x_24);
lean_dec(x_24);
x_26 = lean_ctor_get(x_1, 3);
lean_inc(x_26);
x_27 = lean_nat_sub(x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
x_28 = lean_ctor_get(x_1, 4);
lean_inc(x_28);
x_29 = l___private_Lean_Elab_App_5__getForallBody___main(x_27, x_28, x_2);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_7);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_9);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l_Lean_Expr_hasLooseBVars(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l___private_Lean_Elab_App_6__hasTypeMVar(x_1, x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_9);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = l___private_Lean_Elab_App_7__hasOnlyTypeMVar(x_1, x_32);
lean_dec(x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_9);
return x_39;
}
else
{
lean_object* x_40; 
x_40 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_18, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
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
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_9);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_53 = lean_ctor_get(x_7, 0);
x_54 = lean_ctor_get(x_7, 1);
x_55 = lean_ctor_get(x_7, 2);
x_56 = lean_ctor_get(x_7, 3);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_7);
x_57 = l_Lean_replaceRef(x_12, x_56);
lean_dec(x_12);
x_58 = l_Lean_replaceRef(x_57, x_56);
lean_dec(x_57);
x_59 = l_Lean_replaceRef(x_58, x_56);
lean_dec(x_56);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_54);
lean_ctor_set(x_60, 2, x_55);
lean_ctor_set(x_60, 3, x_59);
x_61 = lean_ctor_get(x_1, 1);
lean_inc(x_61);
x_62 = lean_array_get_size(x_61);
lean_dec(x_61);
x_63 = lean_ctor_get(x_1, 3);
lean_inc(x_63);
x_64 = lean_nat_sub(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
x_65 = lean_ctor_get(x_1, 4);
lean_inc(x_65);
x_66 = l___private_Lean_Elab_App_5__getForallBody___main(x_64, x_65, x_2);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_60);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_9);
return x_68;
}
else
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l_Lean_Expr_hasLooseBVars(x_69);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = l___private_Lean_Elab_App_6__hasTypeMVar(x_1, x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_69);
lean_dec(x_60);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_9);
return x_73;
}
else
{
uint8_t x_74; 
x_74 = l___private_Lean_Elab_App_7__hasOnlyTypeMVar(x_1, x_69);
lean_dec(x_1);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_69);
lean_dec(x_60);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_9);
return x_76;
}
else
{
lean_object* x_77; 
x_77 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_18, x_69, x_3, x_4, x_5, x_6, x_60, x_8, x_9);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
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
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_84 = x_77;
} else {
 lean_dec_ref(x_77);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_69);
lean_dec(x_60);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_9);
return x_87;
}
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_9);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_9);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_9);
return x_93;
}
}
}
lean_object* l___private_Lean_Elab_App_8__propagateExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
uint8_t l___private_Lean_Elab_App_9__nextArgIsHole(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_array_fget(x_3, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
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
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = l_Lean_mkAppStx___closed__1;
x_19 = lean_string_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_20 = 0;
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_mkAppStx___closed__3;
x_22 = lean_string_dec_eq(x_16, x_21);
lean_dec(x_16);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_15);
lean_dec(x_14);
x_23 = 0;
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_mkAppStx___closed__5;
x_25 = lean_string_dec_eq(x_15, x_24);
lean_dec(x_15);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_14);
x_26 = 0;
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_mkHole___closed__1;
x_28 = lean_string_dec_eq(x_14, x_27);
lean_dec(x_14);
return x_28;
}
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_29 = 0;
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_30 = 0;
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_31 = 0;
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_9);
x_32 = 0;
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_9);
x_33 = 0;
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_8);
x_34 = 0;
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_7);
x_35 = 0;
return x_35;
}
}
}
}
lean_object* l___private_Lean_Elab_App_9__nextArgIsHole___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_App_9__nextArgIsHole(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_take(x_7, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
x_18 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_14, 2, x_18);
x_19 = lean_st_ref_set(x_7, x_14, x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l___private_Lean_Meta_InferType_22__isTypeFormerTypeImp___main(x_22, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec(x_24);
x_34 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_33);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_32);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_21, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_dec(x_21);
x_41 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_14, 0);
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_14);
x_48 = l_Lean_TraceState_Inhabited___closed__1;
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_48);
x_50 = lean_st_ref_set(x_7, x_49, x_15);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_52 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1, x_4, x_5, x_6, x_7, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_55 = l___private_Lean_Meta_InferType_22__isTypeFormerTypeImp___main(x_53, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_57);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_55, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
lean_dec(x_55);
x_64 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_63);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
 lean_ctor_set_tag(x_67, 1);
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_52, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
x_70 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_69);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
 lean_ctor_set_tag(x_73, 1);
}
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_registerMVarErrorContext(x_16, x_2, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_11 = x_19;
goto _start;
}
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l_Lean_mkAppStx___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("finalize");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1;
x_2 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit parameter '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is missing, unused named arguments ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid autoParam, argument must be a constant");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("by");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__13;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__14;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("seq");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("nestedTacticBlockCurly");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__18;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Std_PersistentArray_Stats_toString___closed__4;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 6);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 7);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*8 + 1);
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 3);
x_24 = l_Lean_replaceRef(x_11, x_23);
x_25 = l_Lean_replaceRef(x_24, x_23);
lean_dec(x_24);
x_26 = l_Lean_replaceRef(x_25, x_23);
lean_dec(x_23);
lean_dec(x_25);
lean_inc(x_22);
lean_ctor_set(x_8, 3, x_26);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_27 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_18__useImplicitLambda_x3f___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 7)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint64_t x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_28, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_28, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_28, 2);
lean_inc(x_114);
x_115 = lean_ctor_get_uint64(x_28, sizeof(void*)*3);
x_116 = lean_unsigned_to_nat(0u);
x_117 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__3(x_112, x_16, x_116);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = (uint8_t)((x_115 << 24) >> 61);
switch (x_118) {
case 0:
{
lean_object* x_119; uint8_t x_120; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_119 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_120 = !lean_is_exclusive(x_1);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_121 = lean_ctor_get(x_1, 7);
lean_dec(x_121);
x_122 = lean_ctor_get(x_1, 6);
lean_dec(x_122);
x_123 = lean_ctor_get(x_1, 5);
lean_dec(x_123);
x_124 = lean_ctor_get(x_1, 4);
lean_dec(x_124);
x_125 = lean_ctor_get(x_1, 3);
lean_dec(x_125);
x_126 = lean_ctor_get(x_1, 2);
lean_dec(x_126);
x_127 = lean_ctor_get(x_1, 1);
lean_dec(x_127);
x_128 = lean_ctor_get(x_1, 0);
lean_dec(x_128);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_129; uint8_t x_130; lean_object* x_131; uint8_t x_132; 
x_129 = lean_ctor_get(x_119, 1);
lean_inc(x_129);
lean_dec(x_119);
x_130 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_ctor_set_uint8(x_1, sizeof(void*)*8 + 1, x_130);
x_131 = lean_array_get_size(x_12);
x_132 = lean_nat_dec_lt(x_15, x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_133; 
x_133 = l_Lean_Expr_getOptParamDefault_x3f(x_113);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
x_134 = l_Lean_Expr_getAutoParamTactic_x3f(x_113);
if (lean_obj_tag(x_134) == 0)
{
uint8_t x_135; 
lean_dec(x_1);
lean_dec(x_114);
lean_dec(x_113);
x_135 = l_Array_isEmpty___rarg(x_16);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_136 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_136, 0, x_112);
x_137 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_138 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
x_139 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_140 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = x_16;
x_142 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_116, x_141);
x_143 = x_142;
x_144 = l_Array_toList___rarg(x_143);
lean_dec(x_143);
x_145 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_144);
x_146 = l_Array_HasRepr___rarg___closed__1;
x_147 = lean_string_append(x_146, x_145);
lean_dec(x_145);
x_148 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_149 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_150, 0, x_140);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_150, x_4, x_5, x_6, x_7, x_8, x_9, x_129);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_151;
}
else
{
lean_object* x_152; uint8_t x_153; 
lean_dec(x_112);
lean_dec(x_16);
x_152 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_153 = l_Lean_checkTraceOption(x_22, x_152);
lean_dec(x_22);
if (x_153 == 0)
{
lean_object* x_154; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_154 = x_129;
goto block_166;
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_13, 0);
lean_inc(x_167);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_168 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_167, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_129);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_154 = x_169;
goto block_166;
}
else
{
uint8_t x_170; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_170 = !lean_is_exclusive(x_168);
if (x_170 == 0)
{
return x_168;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_168, 0);
x_172 = lean_ctor_get(x_168, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_168);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
block_166:
{
lean_object* x_155; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_155 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_154);
lean_dec(x_17);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
lean_inc(x_2);
x_157 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__5(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_156);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_157, 0);
lean_dec(x_159);
lean_ctor_set(x_157, 0, x_2);
return x_157;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec(x_157);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_2);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
else
{
uint8_t x_162; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_162 = !lean_is_exclusive(x_155);
if (x_162 == 0)
{
return x_155;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_155, 0);
x_164 = lean_ctor_get(x_155, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_155);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_inc(x_2);
x_174 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_174, 0, x_2);
x_175 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_152, x_174, x_4, x_5, x_6, x_7, x_8, x_9, x_129);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_177 = x_176;
goto block_189;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_13, 0);
lean_inc(x_190);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_191 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_190, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_176);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_177 = x_192;
goto block_189;
}
else
{
uint8_t x_193; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_193 = !lean_is_exclusive(x_191);
if (x_193 == 0)
{
return x_191;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_191, 0);
x_195 = lean_ctor_get(x_191, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_191);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
block_189:
{
lean_object* x_178; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_178 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_177);
lean_dec(x_17);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
lean_inc(x_2);
x_180 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__6(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_179);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_180, 0);
lean_dec(x_182);
lean_ctor_set(x_180, 0, x_2);
return x_180;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_dec(x_180);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_2);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
else
{
uint8_t x_185; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
}
}
else
{
lean_object* x_197; 
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_197 = lean_ctor_get(x_134, 0);
lean_inc(x_197);
lean_dec(x_134);
if (lean_obj_tag(x_197) == 4)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
lean_dec(x_197);
x_199 = lean_st_ref_get(x_9, x_129);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = lean_ctor_get(x_200, 0);
lean_inc(x_202);
lean_dec(x_200);
x_203 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_202, x_198);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_1);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_11);
lean_dec(x_2);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec(x_203);
x_205 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_205, 0, x_204);
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_205);
x_207 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_206, x_4, x_5, x_6, x_7, x_8, x_9, x_201);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_208 = lean_ctor_get(x_203, 0);
lean_inc(x_208);
lean_dec(x_203);
x_209 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_201);
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
x_211 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_210);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = l_Lean_Syntax_getArgs(x_208);
lean_dec(x_208);
x_214 = l_Array_empty___closed__1;
x_215 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_213, x_213, x_116, x_214);
lean_dec(x_213);
x_216 = l_Lean_nullKind___closed__2;
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_215);
x_218 = lean_array_push(x_214, x_217);
x_219 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__17;
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_218);
x_221 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_222 = lean_array_push(x_221, x_220);
x_223 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__20;
x_224 = lean_array_push(x_222, x_223);
x_225 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__19;
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_224);
x_227 = lean_array_push(x_214, x_226);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_216);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_array_push(x_214, x_228);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_219);
lean_ctor_set(x_230, 1, x_229);
x_231 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_232 = lean_array_push(x_231, x_230);
x_233 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_232);
x_235 = l_Lean_Syntax_copyInfo(x_234, x_11);
lean_dec(x_11);
x_236 = l_Lean_Expr_getAppNumArgsAux___main(x_113, x_116);
x_237 = lean_nat_sub(x_236, x_116);
lean_dec(x_236);
x_238 = lean_unsigned_to_nat(1u);
x_239 = lean_nat_sub(x_237, x_238);
lean_dec(x_237);
x_240 = l_Lean_Expr_getRevArg_x21___main(x_113, x_239);
lean_dec(x_113);
x_241 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_241, 0, x_235);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_242 = l___private_Lean_Elab_App_2__elabArg(x_2, x_241, x_240, x_4, x_5, x_6, x_7, x_8, x_9, x_212);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
lean_inc(x_243);
x_245 = l_Lean_mkApp(x_2, x_243);
x_246 = lean_expr_instantiate1(x_114, x_243);
lean_dec(x_243);
lean_dec(x_114);
x_2 = x_245;
x_3 = x_246;
x_10 = x_244;
goto _start;
}
else
{
uint8_t x_248; 
lean_dec(x_1);
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_248 = !lean_is_exclusive(x_242);
if (x_248 == 0)
{
return x_242;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_242, 0);
x_250 = lean_ctor_get(x_242, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_242);
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
lean_object* x_252; lean_object* x_253; 
lean_dec(x_197);
lean_dec(x_1);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_11);
lean_dec(x_2);
x_252 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_253 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_252, x_4, x_5, x_6, x_7, x_8, x_9, x_129);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_253;
}
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_254 = lean_ctor_get(x_133, 0);
lean_inc(x_254);
lean_dec(x_133);
lean_inc(x_254);
x_255 = l_Lean_mkApp(x_2, x_254);
x_256 = lean_expr_instantiate1(x_114, x_254);
lean_dec(x_254);
lean_dec(x_114);
x_2 = x_255;
x_3 = x_256;
x_10 = x_129;
goto _start;
}
}
else
{
uint8_t x_258; 
lean_dec(x_1);
lean_dec(x_114);
lean_dec(x_113);
x_258 = l_Array_isEmpty___rarg(x_16);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_259 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_259, 0, x_112);
x_260 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_261 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_259);
x_262 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_263 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
x_264 = x_16;
x_265 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_116, x_264);
x_266 = x_265;
x_267 = l_Array_toList___rarg(x_266);
lean_dec(x_266);
x_268 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_267);
x_269 = l_Array_HasRepr___rarg___closed__1;
x_270 = lean_string_append(x_269, x_268);
lean_dec(x_268);
x_271 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_271, 0, x_270);
x_272 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_272, 0, x_271);
x_273 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_273, 0, x_263);
lean_ctor_set(x_273, 1, x_272);
x_274 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_273, x_4, x_5, x_6, x_7, x_8, x_9, x_129);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_274;
}
else
{
lean_object* x_275; uint8_t x_276; 
lean_dec(x_112);
lean_dec(x_16);
x_275 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_276 = l_Lean_checkTraceOption(x_22, x_275);
lean_dec(x_22);
if (x_276 == 0)
{
lean_object* x_277; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_277 = x_129;
goto block_289;
}
else
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_13, 0);
lean_inc(x_290);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_291 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_290, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_129);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; 
x_292 = lean_ctor_get(x_291, 1);
lean_inc(x_292);
lean_dec(x_291);
x_277 = x_292;
goto block_289;
}
else
{
uint8_t x_293; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_293 = !lean_is_exclusive(x_291);
if (x_293 == 0)
{
return x_291;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_291, 0);
x_295 = lean_ctor_get(x_291, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_291);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
block_289:
{
lean_object* x_278; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_278 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_277);
lean_dec(x_17);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec(x_278);
lean_inc(x_2);
x_280 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__7(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_279);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_281 = !lean_is_exclusive(x_280);
if (x_281 == 0)
{
lean_object* x_282; 
x_282 = lean_ctor_get(x_280, 0);
lean_dec(x_282);
lean_ctor_set(x_280, 0, x_2);
return x_280;
}
else
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
lean_dec(x_280);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_2);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
else
{
uint8_t x_285; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_285 = !lean_is_exclusive(x_278);
if (x_285 == 0)
{
return x_278;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_278, 0);
x_287 = lean_ctor_get(x_278, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_278);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_inc(x_2);
x_297 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_297, 0, x_2);
x_298 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_275, x_297, x_4, x_5, x_6, x_7, x_8, x_9, x_129);
x_299 = lean_ctor_get(x_298, 1);
lean_inc(x_299);
lean_dec(x_298);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_300 = x_299;
goto block_312;
}
else
{
lean_object* x_313; lean_object* x_314; 
x_313 = lean_ctor_get(x_13, 0);
lean_inc(x_313);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_314 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_313, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_299);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; 
x_315 = lean_ctor_get(x_314, 1);
lean_inc(x_315);
lean_dec(x_314);
x_300 = x_315;
goto block_312;
}
else
{
uint8_t x_316; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_316 = !lean_is_exclusive(x_314);
if (x_316 == 0)
{
return x_314;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_314, 0);
x_318 = lean_ctor_get(x_314, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_314);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
}
}
block_312:
{
lean_object* x_301; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_301 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_300);
lean_dec(x_17);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
lean_dec(x_301);
lean_inc(x_2);
x_303 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__8(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_302);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_304 = !lean_is_exclusive(x_303);
if (x_304 == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_303, 0);
lean_dec(x_305);
lean_ctor_set(x_303, 0, x_2);
return x_303;
}
else
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_ctor_get(x_303, 1);
lean_inc(x_306);
lean_dec(x_303);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_2);
lean_ctor_set(x_307, 1, x_306);
return x_307;
}
}
else
{
uint8_t x_308; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_308 = !lean_is_exclusive(x_301);
if (x_308 == 0)
{
return x_301;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_301, 0);
x_310 = lean_ctor_get(x_301, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_301);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
}
}
}
}
else
{
lean_object* x_320; lean_object* x_321; 
lean_dec(x_1);
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_3);
x_320 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_321 = l___private_Lean_Elab_App_2__elabArg(x_2, x_320, x_113, x_4, x_5, x_6, x_7, x_8, x_9, x_129);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
x_324 = lean_unsigned_to_nat(1u);
x_325 = lean_nat_add(x_15, x_324);
lean_dec(x_15);
x_326 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_326, 0, x_11);
lean_ctor_set(x_326, 1, x_12);
lean_ctor_set(x_326, 2, x_13);
lean_ctor_set(x_326, 3, x_325);
lean_ctor_set(x_326, 4, x_16);
lean_ctor_set(x_326, 5, x_17);
lean_ctor_set(x_326, 6, x_18);
lean_ctor_set(x_326, 7, x_19);
lean_ctor_set_uint8(x_326, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_326, sizeof(void*)*8 + 1, x_130);
lean_inc(x_322);
x_327 = l_Lean_mkApp(x_2, x_322);
x_328 = lean_expr_instantiate1(x_114, x_322);
lean_dec(x_322);
lean_dec(x_114);
x_1 = x_326;
x_2 = x_327;
x_3 = x_328;
x_10 = x_323;
goto _start;
}
else
{
uint8_t x_330; 
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_330 = !lean_is_exclusive(x_321);
if (x_330 == 0)
{
return x_321;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_321, 0);
x_332 = lean_ctor_get(x_321, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_321);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
return x_333;
}
}
}
}
else
{
uint8_t x_334; 
lean_free_object(x_1);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_8);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_334 = !lean_is_exclusive(x_119);
if (x_334 == 0)
{
return x_119;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_119, 0);
x_336 = lean_ctor_get(x_119, 1);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_119);
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
return x_337;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_338; uint8_t x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
x_338 = lean_ctor_get(x_119, 1);
lean_inc(x_338);
lean_dec(x_119);
x_339 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_340 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_340, 0, x_11);
lean_ctor_set(x_340, 1, x_12);
lean_ctor_set(x_340, 2, x_13);
lean_ctor_set(x_340, 3, x_15);
lean_ctor_set(x_340, 4, x_16);
lean_ctor_set(x_340, 5, x_17);
lean_ctor_set(x_340, 6, x_18);
lean_ctor_set(x_340, 7, x_19);
lean_ctor_set_uint8(x_340, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_340, sizeof(void*)*8 + 1, x_339);
x_341 = lean_array_get_size(x_12);
x_342 = lean_nat_dec_lt(x_15, x_341);
lean_dec(x_341);
if (x_342 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_343; 
x_343 = l_Lean_Expr_getOptParamDefault_x3f(x_113);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; 
x_344 = l_Lean_Expr_getAutoParamTactic_x3f(x_113);
if (lean_obj_tag(x_344) == 0)
{
uint8_t x_345; 
lean_dec(x_340);
lean_dec(x_114);
lean_dec(x_113);
x_345 = l_Array_isEmpty___rarg(x_16);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_346 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_346, 0, x_112);
x_347 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_348 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_346);
x_349 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_350 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
x_351 = x_16;
x_352 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_116, x_351);
x_353 = x_352;
x_354 = l_Array_toList___rarg(x_353);
lean_dec(x_353);
x_355 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_354);
x_356 = l_Array_HasRepr___rarg___closed__1;
x_357 = lean_string_append(x_356, x_355);
lean_dec(x_355);
x_358 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_358, 0, x_357);
x_359 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_359, 0, x_358);
x_360 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_360, 0, x_350);
lean_ctor_set(x_360, 1, x_359);
x_361 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_360, x_4, x_5, x_6, x_7, x_8, x_9, x_338);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_361;
}
else
{
lean_object* x_362; uint8_t x_363; 
lean_dec(x_112);
lean_dec(x_16);
x_362 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_363 = l_Lean_checkTraceOption(x_22, x_362);
lean_dec(x_22);
if (x_363 == 0)
{
lean_object* x_364; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_364 = x_338;
goto block_375;
}
else
{
lean_object* x_376; lean_object* x_377; 
x_376 = lean_ctor_get(x_13, 0);
lean_inc(x_376);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_377 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_376, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_338);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; 
x_378 = lean_ctor_get(x_377, 1);
lean_inc(x_378);
lean_dec(x_377);
x_364 = x_378;
goto block_375;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_379 = lean_ctor_get(x_377, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_377, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_381 = x_377;
} else {
 lean_dec_ref(x_377);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(1, 2, 0);
} else {
 x_382 = x_381;
}
lean_ctor_set(x_382, 0, x_379);
lean_ctor_set(x_382, 1, x_380);
return x_382;
}
}
block_375:
{
lean_object* x_365; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_365 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_364);
lean_dec(x_17);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
lean_dec(x_365);
lean_inc(x_2);
x_367 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__5(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_366);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_368 = lean_ctor_get(x_367, 1);
lean_inc(x_368);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_369 = x_367;
} else {
 lean_dec_ref(x_367);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(0, 2, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_2);
lean_ctor_set(x_370, 1, x_368);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_371 = lean_ctor_get(x_365, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_365, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_373 = x_365;
} else {
 lean_dec_ref(x_365);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(1, 2, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_372);
return x_374;
}
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_inc(x_2);
x_383 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_383, 0, x_2);
x_384 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_362, x_383, x_4, x_5, x_6, x_7, x_8, x_9, x_338);
x_385 = lean_ctor_get(x_384, 1);
lean_inc(x_385);
lean_dec(x_384);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_386 = x_385;
goto block_397;
}
else
{
lean_object* x_398; lean_object* x_399; 
x_398 = lean_ctor_get(x_13, 0);
lean_inc(x_398);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_399 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_398, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_385);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; 
x_400 = lean_ctor_get(x_399, 1);
lean_inc(x_400);
lean_dec(x_399);
x_386 = x_400;
goto block_397;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_401 = lean_ctor_get(x_399, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_399, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_403 = x_399;
} else {
 lean_dec_ref(x_399);
 x_403 = lean_box(0);
}
if (lean_is_scalar(x_403)) {
 x_404 = lean_alloc_ctor(1, 2, 0);
} else {
 x_404 = x_403;
}
lean_ctor_set(x_404, 0, x_401);
lean_ctor_set(x_404, 1, x_402);
return x_404;
}
}
block_397:
{
lean_object* x_387; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_387 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_386);
lean_dec(x_17);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
lean_dec(x_387);
lean_inc(x_2);
x_389 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__6(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_388);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_390 = lean_ctor_get(x_389, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_391 = x_389;
} else {
 lean_dec_ref(x_389);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_2);
lean_ctor_set(x_392, 1, x_390);
return x_392;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_393 = lean_ctor_get(x_387, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_387, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_395 = x_387;
} else {
 lean_dec_ref(x_387);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_393);
lean_ctor_set(x_396, 1, x_394);
return x_396;
}
}
}
}
}
else
{
lean_object* x_405; 
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_405 = lean_ctor_get(x_344, 0);
lean_inc(x_405);
lean_dec(x_344);
if (lean_obj_tag(x_405) == 4)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
lean_dec(x_405);
x_407 = lean_st_ref_get(x_9, x_338);
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_410 = lean_ctor_get(x_408, 0);
lean_inc(x_410);
lean_dec(x_408);
x_411 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_410, x_406);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
lean_dec(x_340);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_11);
lean_dec(x_2);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
lean_dec(x_411);
x_413 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_413, 0, x_412);
x_414 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_414, 0, x_413);
x_415 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_414, x_4, x_5, x_6, x_7, x_8, x_9, x_409);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_415;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_416 = lean_ctor_get(x_411, 0);
lean_inc(x_416);
lean_dec(x_411);
x_417 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_409);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
lean_dec(x_417);
x_419 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_418);
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
lean_dec(x_419);
x_421 = l_Lean_Syntax_getArgs(x_416);
lean_dec(x_416);
x_422 = l_Array_empty___closed__1;
x_423 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_421, x_421, x_116, x_422);
lean_dec(x_421);
x_424 = l_Lean_nullKind___closed__2;
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_423);
x_426 = lean_array_push(x_422, x_425);
x_427 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__17;
x_428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_426);
x_429 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_430 = lean_array_push(x_429, x_428);
x_431 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__20;
x_432 = lean_array_push(x_430, x_431);
x_433 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__19;
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_432);
x_435 = lean_array_push(x_422, x_434);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_424);
lean_ctor_set(x_436, 1, x_435);
x_437 = lean_array_push(x_422, x_436);
x_438 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_438, 0, x_427);
lean_ctor_set(x_438, 1, x_437);
x_439 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_440 = lean_array_push(x_439, x_438);
x_441 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_440);
x_443 = l_Lean_Syntax_copyInfo(x_442, x_11);
lean_dec(x_11);
x_444 = l_Lean_Expr_getAppNumArgsAux___main(x_113, x_116);
x_445 = lean_nat_sub(x_444, x_116);
lean_dec(x_444);
x_446 = lean_unsigned_to_nat(1u);
x_447 = lean_nat_sub(x_445, x_446);
lean_dec(x_445);
x_448 = l_Lean_Expr_getRevArg_x21___main(x_113, x_447);
lean_dec(x_113);
x_449 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_449, 0, x_443);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_450 = l___private_Lean_Elab_App_2__elabArg(x_2, x_449, x_448, x_4, x_5, x_6, x_7, x_8, x_9, x_420);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
lean_dec(x_450);
lean_inc(x_451);
x_453 = l_Lean_mkApp(x_2, x_451);
x_454 = lean_expr_instantiate1(x_114, x_451);
lean_dec(x_451);
lean_dec(x_114);
x_1 = x_340;
x_2 = x_453;
x_3 = x_454;
x_10 = x_452;
goto _start;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_340);
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_456 = lean_ctor_get(x_450, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_450, 1);
lean_inc(x_457);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_458 = x_450;
} else {
 lean_dec_ref(x_450);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(1, 2, 0);
} else {
 x_459 = x_458;
}
lean_ctor_set(x_459, 0, x_456);
lean_ctor_set(x_459, 1, x_457);
return x_459;
}
}
}
else
{
lean_object* x_460; lean_object* x_461; 
lean_dec(x_405);
lean_dec(x_340);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_11);
lean_dec(x_2);
x_460 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_461 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_460, x_4, x_5, x_6, x_7, x_8, x_9, x_338);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_461;
}
}
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_462 = lean_ctor_get(x_343, 0);
lean_inc(x_462);
lean_dec(x_343);
lean_inc(x_462);
x_463 = l_Lean_mkApp(x_2, x_462);
x_464 = lean_expr_instantiate1(x_114, x_462);
lean_dec(x_462);
lean_dec(x_114);
x_1 = x_340;
x_2 = x_463;
x_3 = x_464;
x_10 = x_338;
goto _start;
}
}
else
{
uint8_t x_466; 
lean_dec(x_340);
lean_dec(x_114);
lean_dec(x_113);
x_466 = l_Array_isEmpty___rarg(x_16);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_467 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_467, 0, x_112);
x_468 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_469 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_467);
x_470 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_471 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_471, 0, x_469);
lean_ctor_set(x_471, 1, x_470);
x_472 = x_16;
x_473 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_116, x_472);
x_474 = x_473;
x_475 = l_Array_toList___rarg(x_474);
lean_dec(x_474);
x_476 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_475);
x_477 = l_Array_HasRepr___rarg___closed__1;
x_478 = lean_string_append(x_477, x_476);
lean_dec(x_476);
x_479 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_479, 0, x_478);
x_480 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_480, 0, x_479);
x_481 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_481, 0, x_471);
lean_ctor_set(x_481, 1, x_480);
x_482 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_481, x_4, x_5, x_6, x_7, x_8, x_9, x_338);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_482;
}
else
{
lean_object* x_483; uint8_t x_484; 
lean_dec(x_112);
lean_dec(x_16);
x_483 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_484 = l_Lean_checkTraceOption(x_22, x_483);
lean_dec(x_22);
if (x_484 == 0)
{
lean_object* x_485; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_485 = x_338;
goto block_496;
}
else
{
lean_object* x_497; lean_object* x_498; 
x_497 = lean_ctor_get(x_13, 0);
lean_inc(x_497);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_498 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_497, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_338);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; 
x_499 = lean_ctor_get(x_498, 1);
lean_inc(x_499);
lean_dec(x_498);
x_485 = x_499;
goto block_496;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_500 = lean_ctor_get(x_498, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_498, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 x_502 = x_498;
} else {
 lean_dec_ref(x_498);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 2, 0);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_500);
lean_ctor_set(x_503, 1, x_501);
return x_503;
}
}
block_496:
{
lean_object* x_486; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_486 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_485);
lean_dec(x_17);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_487 = lean_ctor_get(x_486, 1);
lean_inc(x_487);
lean_dec(x_486);
lean_inc(x_2);
x_488 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__7(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_487);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_489 = lean_ctor_get(x_488, 1);
lean_inc(x_489);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 x_490 = x_488;
} else {
 lean_dec_ref(x_488);
 x_490 = lean_box(0);
}
if (lean_is_scalar(x_490)) {
 x_491 = lean_alloc_ctor(0, 2, 0);
} else {
 x_491 = x_490;
}
lean_ctor_set(x_491, 0, x_2);
lean_ctor_set(x_491, 1, x_489);
return x_491;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_492 = lean_ctor_get(x_486, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_486, 1);
lean_inc(x_493);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_494 = x_486;
} else {
 lean_dec_ref(x_486);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(1, 2, 0);
} else {
 x_495 = x_494;
}
lean_ctor_set(x_495, 0, x_492);
lean_ctor_set(x_495, 1, x_493);
return x_495;
}
}
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_inc(x_2);
x_504 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_504, 0, x_2);
x_505 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_483, x_504, x_4, x_5, x_6, x_7, x_8, x_9, x_338);
x_506 = lean_ctor_get(x_505, 1);
lean_inc(x_506);
lean_dec(x_505);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_507 = x_506;
goto block_518;
}
else
{
lean_object* x_519; lean_object* x_520; 
x_519 = lean_ctor_get(x_13, 0);
lean_inc(x_519);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_520 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_519, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_506);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; 
x_521 = lean_ctor_get(x_520, 1);
lean_inc(x_521);
lean_dec(x_520);
x_507 = x_521;
goto block_518;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_522 = lean_ctor_get(x_520, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_520, 1);
lean_inc(x_523);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 lean_ctor_release(x_520, 1);
 x_524 = x_520;
} else {
 lean_dec_ref(x_520);
 x_524 = lean_box(0);
}
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(1, 2, 0);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_522);
lean_ctor_set(x_525, 1, x_523);
return x_525;
}
}
block_518:
{
lean_object* x_508; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_508 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_507);
lean_dec(x_17);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_509 = lean_ctor_get(x_508, 1);
lean_inc(x_509);
lean_dec(x_508);
lean_inc(x_2);
x_510 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__8(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_509);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_511 = lean_ctor_get(x_510, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_510)) {
 lean_ctor_release(x_510, 0);
 lean_ctor_release(x_510, 1);
 x_512 = x_510;
} else {
 lean_dec_ref(x_510);
 x_512 = lean_box(0);
}
if (lean_is_scalar(x_512)) {
 x_513 = lean_alloc_ctor(0, 2, 0);
} else {
 x_513 = x_512;
}
lean_ctor_set(x_513, 0, x_2);
lean_ctor_set(x_513, 1, x_511);
return x_513;
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_514 = lean_ctor_get(x_508, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_508, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_516 = x_508;
} else {
 lean_dec_ref(x_508);
 x_516 = lean_box(0);
}
if (lean_is_scalar(x_516)) {
 x_517 = lean_alloc_ctor(1, 2, 0);
} else {
 x_517 = x_516;
}
lean_ctor_set(x_517, 0, x_514);
lean_ctor_set(x_517, 1, x_515);
return x_517;
}
}
}
}
}
}
else
{
lean_object* x_526; lean_object* x_527; 
lean_dec(x_340);
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_3);
x_526 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_527 = l___private_Lean_Elab_App_2__elabArg(x_2, x_526, x_113, x_4, x_5, x_6, x_7, x_8, x_9, x_338);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_527, 1);
lean_inc(x_529);
lean_dec(x_527);
x_530 = lean_unsigned_to_nat(1u);
x_531 = lean_nat_add(x_15, x_530);
lean_dec(x_15);
x_532 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_532, 0, x_11);
lean_ctor_set(x_532, 1, x_12);
lean_ctor_set(x_532, 2, x_13);
lean_ctor_set(x_532, 3, x_531);
lean_ctor_set(x_532, 4, x_16);
lean_ctor_set(x_532, 5, x_17);
lean_ctor_set(x_532, 6, x_18);
lean_ctor_set(x_532, 7, x_19);
lean_ctor_set_uint8(x_532, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_532, sizeof(void*)*8 + 1, x_339);
lean_inc(x_528);
x_533 = l_Lean_mkApp(x_2, x_528);
x_534 = lean_expr_instantiate1(x_114, x_528);
lean_dec(x_528);
lean_dec(x_114);
x_1 = x_532;
x_2 = x_533;
x_3 = x_534;
x_10 = x_529;
goto _start;
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_536 = lean_ctor_get(x_527, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_527, 1);
lean_inc(x_537);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 lean_ctor_release(x_527, 1);
 x_538 = x_527;
} else {
 lean_dec_ref(x_527);
 x_538 = lean_box(0);
}
if (lean_is_scalar(x_538)) {
 x_539 = lean_alloc_ctor(1, 2, 0);
} else {
 x_539 = x_538;
}
lean_ctor_set(x_539, 0, x_536);
lean_ctor_set(x_539, 1, x_537);
return x_539;
}
}
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_8);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_540 = lean_ctor_get(x_119, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_119, 1);
lean_inc(x_541);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_542 = x_119;
} else {
 lean_dec_ref(x_119);
 x_542 = lean_box(0);
}
if (lean_is_scalar(x_542)) {
 x_543 = lean_alloc_ctor(1, 2, 0);
} else {
 x_543 = x_542;
}
lean_ctor_set(x_543, 0, x_540);
lean_ctor_set(x_543, 1, x_541);
return x_543;
}
}
}
case 1:
{
if (x_14 == 0)
{
lean_object* x_544; lean_object* x_545; uint8_t x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_560; 
lean_dec(x_112);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_544 = x_1;
} else {
 lean_dec_ref(x_1);
 x_544 = lean_box(0);
}
x_545 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_545, 0, x_113);
x_546 = 0;
x_547 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_548 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_545, x_546, x_547, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
lean_dec(x_548);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_549);
x_560 = l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__9(x_549, x_4, x_5, x_6, x_7, x_8, x_9, x_550);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; uint8_t x_562; 
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
x_562 = lean_unbox(x_561);
lean_dec(x_561);
if (x_562 == 0)
{
lean_object* x_563; 
x_563 = lean_ctor_get(x_560, 1);
lean_inc(x_563);
lean_dec(x_560);
x_551 = x_18;
x_552 = x_563;
goto block_559;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_560, 1);
lean_inc(x_564);
lean_dec(x_560);
x_565 = l_Lean_Expr_mvarId_x21(x_549);
x_566 = lean_array_push(x_18, x_565);
x_551 = x_566;
x_552 = x_564;
goto block_559;
}
}
else
{
uint8_t x_567; 
lean_dec(x_549);
lean_dec(x_544);
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_567 = !lean_is_exclusive(x_560);
if (x_567 == 0)
{
return x_560;
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_568 = lean_ctor_get(x_560, 0);
x_569 = lean_ctor_get(x_560, 1);
lean_inc(x_569);
lean_inc(x_568);
lean_dec(x_560);
x_570 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_570, 0, x_568);
lean_ctor_set(x_570, 1, x_569);
return x_570;
}
}
block_559:
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_553 = l_Lean_Expr_mvarId_x21(x_549);
x_554 = lean_array_push(x_19, x_553);
if (lean_is_scalar(x_544)) {
 x_555 = lean_alloc_ctor(0, 8, 2);
} else {
 x_555 = x_544;
}
lean_ctor_set(x_555, 0, x_11);
lean_ctor_set(x_555, 1, x_12);
lean_ctor_set(x_555, 2, x_13);
lean_ctor_set(x_555, 3, x_15);
lean_ctor_set(x_555, 4, x_16);
lean_ctor_set(x_555, 5, x_17);
lean_ctor_set(x_555, 6, x_551);
lean_ctor_set(x_555, 7, x_554);
lean_ctor_set_uint8(x_555, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_555, sizeof(void*)*8 + 1, x_21);
lean_inc(x_549);
x_556 = l_Lean_mkApp(x_2, x_549);
x_557 = lean_expr_instantiate1(x_114, x_549);
lean_dec(x_549);
lean_dec(x_114);
x_1 = x_555;
x_2 = x_556;
x_3 = x_557;
x_10 = x_552;
goto _start;
}
}
else
{
lean_object* x_571; uint8_t x_572; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_571 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_572 = !lean_is_exclusive(x_1);
if (x_572 == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_573 = lean_ctor_get(x_1, 7);
lean_dec(x_573);
x_574 = lean_ctor_get(x_1, 6);
lean_dec(x_574);
x_575 = lean_ctor_get(x_1, 5);
lean_dec(x_575);
x_576 = lean_ctor_get(x_1, 4);
lean_dec(x_576);
x_577 = lean_ctor_get(x_1, 3);
lean_dec(x_577);
x_578 = lean_ctor_get(x_1, 2);
lean_dec(x_578);
x_579 = lean_ctor_get(x_1, 1);
lean_dec(x_579);
x_580 = lean_ctor_get(x_1, 0);
lean_dec(x_580);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_581; lean_object* x_582; uint8_t x_583; 
x_581 = lean_ctor_get(x_571, 1);
lean_inc(x_581);
lean_dec(x_571);
x_582 = lean_array_get_size(x_12);
x_583 = lean_nat_dec_lt(x_15, x_582);
lean_dec(x_582);
if (x_583 == 0)
{
uint8_t x_584; 
lean_free_object(x_1);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_584 = l_Array_isEmpty___rarg(x_16);
if (x_584 == 0)
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_585 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_585, 0, x_112);
x_586 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_587 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_587, 0, x_586);
lean_ctor_set(x_587, 1, x_585);
x_588 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_589 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_589, 0, x_587);
lean_ctor_set(x_589, 1, x_588);
x_590 = x_16;
x_591 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_116, x_590);
x_592 = x_591;
x_593 = l_Array_toList___rarg(x_592);
lean_dec(x_592);
x_594 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_593);
x_595 = l_Array_HasRepr___rarg___closed__1;
x_596 = lean_string_append(x_595, x_594);
lean_dec(x_594);
x_597 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_597, 0, x_596);
x_598 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_598, 0, x_597);
x_599 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_599, 0, x_589);
lean_ctor_set(x_599, 1, x_598);
x_600 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_599, x_4, x_5, x_6, x_7, x_8, x_9, x_581);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_600;
}
else
{
lean_object* x_601; uint8_t x_602; 
lean_dec(x_112);
lean_dec(x_16);
x_601 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_602 = l_Lean_checkTraceOption(x_22, x_601);
lean_dec(x_22);
if (x_602 == 0)
{
lean_object* x_603; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_603 = x_581;
goto block_615;
}
else
{
lean_object* x_616; lean_object* x_617; 
x_616 = lean_ctor_get(x_13, 0);
lean_inc(x_616);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_617 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_616, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_581);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; 
x_618 = lean_ctor_get(x_617, 1);
lean_inc(x_618);
lean_dec(x_617);
x_603 = x_618;
goto block_615;
}
else
{
uint8_t x_619; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_619 = !lean_is_exclusive(x_617);
if (x_619 == 0)
{
return x_617;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_620 = lean_ctor_get(x_617, 0);
x_621 = lean_ctor_get(x_617, 1);
lean_inc(x_621);
lean_inc(x_620);
lean_dec(x_617);
x_622 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_622, 0, x_620);
lean_ctor_set(x_622, 1, x_621);
return x_622;
}
}
}
block_615:
{
lean_object* x_604; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_604 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_603);
lean_dec(x_17);
if (lean_obj_tag(x_604) == 0)
{
lean_object* x_605; lean_object* x_606; uint8_t x_607; 
x_605 = lean_ctor_get(x_604, 1);
lean_inc(x_605);
lean_dec(x_604);
lean_inc(x_2);
x_606 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__10(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_605);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_607 = !lean_is_exclusive(x_606);
if (x_607 == 0)
{
lean_object* x_608; 
x_608 = lean_ctor_get(x_606, 0);
lean_dec(x_608);
lean_ctor_set(x_606, 0, x_2);
return x_606;
}
else
{
lean_object* x_609; lean_object* x_610; 
x_609 = lean_ctor_get(x_606, 1);
lean_inc(x_609);
lean_dec(x_606);
x_610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_610, 0, x_2);
lean_ctor_set(x_610, 1, x_609);
return x_610;
}
}
else
{
uint8_t x_611; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_611 = !lean_is_exclusive(x_604);
if (x_611 == 0)
{
return x_604;
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_612 = lean_ctor_get(x_604, 0);
x_613 = lean_ctor_get(x_604, 1);
lean_inc(x_613);
lean_inc(x_612);
lean_dec(x_604);
x_614 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_614, 0, x_612);
lean_ctor_set(x_614, 1, x_613);
return x_614;
}
}
}
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; 
lean_inc(x_2);
x_623 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_623, 0, x_2);
x_624 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_601, x_623, x_4, x_5, x_6, x_7, x_8, x_9, x_581);
x_625 = lean_ctor_get(x_624, 1);
lean_inc(x_625);
lean_dec(x_624);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_626 = x_625;
goto block_638;
}
else
{
lean_object* x_639; lean_object* x_640; 
x_639 = lean_ctor_get(x_13, 0);
lean_inc(x_639);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_640 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_639, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_625);
if (lean_obj_tag(x_640) == 0)
{
lean_object* x_641; 
x_641 = lean_ctor_get(x_640, 1);
lean_inc(x_641);
lean_dec(x_640);
x_626 = x_641;
goto block_638;
}
else
{
uint8_t x_642; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_642 = !lean_is_exclusive(x_640);
if (x_642 == 0)
{
return x_640;
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_643 = lean_ctor_get(x_640, 0);
x_644 = lean_ctor_get(x_640, 1);
lean_inc(x_644);
lean_inc(x_643);
lean_dec(x_640);
x_645 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_645, 0, x_643);
lean_ctor_set(x_645, 1, x_644);
return x_645;
}
}
}
block_638:
{
lean_object* x_627; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_627 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_626);
lean_dec(x_17);
if (lean_obj_tag(x_627) == 0)
{
lean_object* x_628; lean_object* x_629; uint8_t x_630; 
x_628 = lean_ctor_get(x_627, 1);
lean_inc(x_628);
lean_dec(x_627);
lean_inc(x_2);
x_629 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__11(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_628);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_630 = !lean_is_exclusive(x_629);
if (x_630 == 0)
{
lean_object* x_631; 
x_631 = lean_ctor_get(x_629, 0);
lean_dec(x_631);
lean_ctor_set(x_629, 0, x_2);
return x_629;
}
else
{
lean_object* x_632; lean_object* x_633; 
x_632 = lean_ctor_get(x_629, 1);
lean_inc(x_632);
lean_dec(x_629);
x_633 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_633, 0, x_2);
lean_ctor_set(x_633, 1, x_632);
return x_633;
}
}
else
{
uint8_t x_634; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_634 = !lean_is_exclusive(x_627);
if (x_634 == 0)
{
return x_627;
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_635 = lean_ctor_get(x_627, 0);
x_636 = lean_ctor_get(x_627, 1);
lean_inc(x_636);
lean_inc(x_635);
lean_dec(x_627);
x_637 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_637, 0, x_635);
lean_ctor_set(x_637, 1, x_636);
return x_637;
}
}
}
}
}
}
else
{
lean_object* x_646; lean_object* x_647; 
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_3);
x_646 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_647 = l___private_Lean_Elab_App_2__elabArg(x_2, x_646, x_113, x_4, x_5, x_6, x_7, x_8, x_9, x_581);
if (lean_obj_tag(x_647) == 0)
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; uint8_t x_652; lean_object* x_653; lean_object* x_654; 
x_648 = lean_ctor_get(x_647, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_647, 1);
lean_inc(x_649);
lean_dec(x_647);
x_650 = lean_unsigned_to_nat(1u);
x_651 = lean_nat_add(x_15, x_650);
lean_dec(x_15);
x_652 = 1;
lean_ctor_set(x_1, 3, x_651);
lean_ctor_set_uint8(x_1, sizeof(void*)*8 + 1, x_652);
lean_inc(x_648);
x_653 = l_Lean_mkApp(x_2, x_648);
x_654 = lean_expr_instantiate1(x_114, x_648);
lean_dec(x_648);
lean_dec(x_114);
x_2 = x_653;
x_3 = x_654;
x_10 = x_649;
goto _start;
}
else
{
uint8_t x_656; 
lean_free_object(x_1);
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_656 = !lean_is_exclusive(x_647);
if (x_656 == 0)
{
return x_647;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_657 = lean_ctor_get(x_647, 0);
x_658 = lean_ctor_get(x_647, 1);
lean_inc(x_658);
lean_inc(x_657);
lean_dec(x_647);
x_659 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_659, 0, x_657);
lean_ctor_set(x_659, 1, x_658);
return x_659;
}
}
}
}
else
{
uint8_t x_660; 
lean_free_object(x_1);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_8);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_660 = !lean_is_exclusive(x_571);
if (x_660 == 0)
{
return x_571;
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_661 = lean_ctor_get(x_571, 0);
x_662 = lean_ctor_get(x_571, 1);
lean_inc(x_662);
lean_inc(x_661);
lean_dec(x_571);
x_663 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_663, 0, x_661);
lean_ctor_set(x_663, 1, x_662);
return x_663;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_664; lean_object* x_665; uint8_t x_666; 
x_664 = lean_ctor_get(x_571, 1);
lean_inc(x_664);
lean_dec(x_571);
x_665 = lean_array_get_size(x_12);
x_666 = lean_nat_dec_lt(x_15, x_665);
lean_dec(x_665);
if (x_666 == 0)
{
uint8_t x_667; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_667 = l_Array_isEmpty___rarg(x_16);
if (x_667 == 0)
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_668 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_668, 0, x_112);
x_669 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_670 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_670, 0, x_669);
lean_ctor_set(x_670, 1, x_668);
x_671 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_672 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_672, 0, x_670);
lean_ctor_set(x_672, 1, x_671);
x_673 = x_16;
x_674 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_116, x_673);
x_675 = x_674;
x_676 = l_Array_toList___rarg(x_675);
lean_dec(x_675);
x_677 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_676);
x_678 = l_Array_HasRepr___rarg___closed__1;
x_679 = lean_string_append(x_678, x_677);
lean_dec(x_677);
x_680 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_680, 0, x_679);
x_681 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_681, 0, x_680);
x_682 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_682, 0, x_672);
lean_ctor_set(x_682, 1, x_681);
x_683 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_682, x_4, x_5, x_6, x_7, x_8, x_9, x_664);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_683;
}
else
{
lean_object* x_684; uint8_t x_685; 
lean_dec(x_112);
lean_dec(x_16);
x_684 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_685 = l_Lean_checkTraceOption(x_22, x_684);
lean_dec(x_22);
if (x_685 == 0)
{
lean_object* x_686; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_686 = x_664;
goto block_697;
}
else
{
lean_object* x_698; lean_object* x_699; 
x_698 = lean_ctor_get(x_13, 0);
lean_inc(x_698);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_699 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_698, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_664);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_700; 
x_700 = lean_ctor_get(x_699, 1);
lean_inc(x_700);
lean_dec(x_699);
x_686 = x_700;
goto block_697;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_701 = lean_ctor_get(x_699, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_699, 1);
lean_inc(x_702);
if (lean_is_exclusive(x_699)) {
 lean_ctor_release(x_699, 0);
 lean_ctor_release(x_699, 1);
 x_703 = x_699;
} else {
 lean_dec_ref(x_699);
 x_703 = lean_box(0);
}
if (lean_is_scalar(x_703)) {
 x_704 = lean_alloc_ctor(1, 2, 0);
} else {
 x_704 = x_703;
}
lean_ctor_set(x_704, 0, x_701);
lean_ctor_set(x_704, 1, x_702);
return x_704;
}
}
block_697:
{
lean_object* x_687; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_687 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_686);
lean_dec(x_17);
if (lean_obj_tag(x_687) == 0)
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_688 = lean_ctor_get(x_687, 1);
lean_inc(x_688);
lean_dec(x_687);
lean_inc(x_2);
x_689 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__10(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_688);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_690 = lean_ctor_get(x_689, 1);
lean_inc(x_690);
if (lean_is_exclusive(x_689)) {
 lean_ctor_release(x_689, 0);
 lean_ctor_release(x_689, 1);
 x_691 = x_689;
} else {
 lean_dec_ref(x_689);
 x_691 = lean_box(0);
}
if (lean_is_scalar(x_691)) {
 x_692 = lean_alloc_ctor(0, 2, 0);
} else {
 x_692 = x_691;
}
lean_ctor_set(x_692, 0, x_2);
lean_ctor_set(x_692, 1, x_690);
return x_692;
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_693 = lean_ctor_get(x_687, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_687, 1);
lean_inc(x_694);
if (lean_is_exclusive(x_687)) {
 lean_ctor_release(x_687, 0);
 lean_ctor_release(x_687, 1);
 x_695 = x_687;
} else {
 lean_dec_ref(x_687);
 x_695 = lean_box(0);
}
if (lean_is_scalar(x_695)) {
 x_696 = lean_alloc_ctor(1, 2, 0);
} else {
 x_696 = x_695;
}
lean_ctor_set(x_696, 0, x_693);
lean_ctor_set(x_696, 1, x_694);
return x_696;
}
}
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
lean_inc(x_2);
x_705 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_705, 0, x_2);
x_706 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_684, x_705, x_4, x_5, x_6, x_7, x_8, x_9, x_664);
x_707 = lean_ctor_get(x_706, 1);
lean_inc(x_707);
lean_dec(x_706);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_708 = x_707;
goto block_719;
}
else
{
lean_object* x_720; lean_object* x_721; 
x_720 = lean_ctor_get(x_13, 0);
lean_inc(x_720);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_721 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_720, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_707);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; 
x_722 = lean_ctor_get(x_721, 1);
lean_inc(x_722);
lean_dec(x_721);
x_708 = x_722;
goto block_719;
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_723 = lean_ctor_get(x_721, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_721, 1);
lean_inc(x_724);
if (lean_is_exclusive(x_721)) {
 lean_ctor_release(x_721, 0);
 lean_ctor_release(x_721, 1);
 x_725 = x_721;
} else {
 lean_dec_ref(x_721);
 x_725 = lean_box(0);
}
if (lean_is_scalar(x_725)) {
 x_726 = lean_alloc_ctor(1, 2, 0);
} else {
 x_726 = x_725;
}
lean_ctor_set(x_726, 0, x_723);
lean_ctor_set(x_726, 1, x_724);
return x_726;
}
}
block_719:
{
lean_object* x_709; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_709 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_708);
lean_dec(x_17);
if (lean_obj_tag(x_709) == 0)
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
x_710 = lean_ctor_get(x_709, 1);
lean_inc(x_710);
lean_dec(x_709);
lean_inc(x_2);
x_711 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__11(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_710);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_712 = lean_ctor_get(x_711, 1);
lean_inc(x_712);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 lean_ctor_release(x_711, 1);
 x_713 = x_711;
} else {
 lean_dec_ref(x_711);
 x_713 = lean_box(0);
}
if (lean_is_scalar(x_713)) {
 x_714 = lean_alloc_ctor(0, 2, 0);
} else {
 x_714 = x_713;
}
lean_ctor_set(x_714, 0, x_2);
lean_ctor_set(x_714, 1, x_712);
return x_714;
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_715 = lean_ctor_get(x_709, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_709, 1);
lean_inc(x_716);
if (lean_is_exclusive(x_709)) {
 lean_ctor_release(x_709, 0);
 lean_ctor_release(x_709, 1);
 x_717 = x_709;
} else {
 lean_dec_ref(x_709);
 x_717 = lean_box(0);
}
if (lean_is_scalar(x_717)) {
 x_718 = lean_alloc_ctor(1, 2, 0);
} else {
 x_718 = x_717;
}
lean_ctor_set(x_718, 0, x_715);
lean_ctor_set(x_718, 1, x_716);
return x_718;
}
}
}
}
}
else
{
lean_object* x_727; lean_object* x_728; 
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_3);
x_727 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_728 = l___private_Lean_Elab_App_2__elabArg(x_2, x_727, x_113, x_4, x_5, x_6, x_7, x_8, x_9, x_664);
if (lean_obj_tag(x_728) == 0)
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; uint8_t x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_729 = lean_ctor_get(x_728, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_728, 1);
lean_inc(x_730);
lean_dec(x_728);
x_731 = lean_unsigned_to_nat(1u);
x_732 = lean_nat_add(x_15, x_731);
lean_dec(x_15);
x_733 = 1;
x_734 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_734, 0, x_11);
lean_ctor_set(x_734, 1, x_12);
lean_ctor_set(x_734, 2, x_13);
lean_ctor_set(x_734, 3, x_732);
lean_ctor_set(x_734, 4, x_16);
lean_ctor_set(x_734, 5, x_17);
lean_ctor_set(x_734, 6, x_18);
lean_ctor_set(x_734, 7, x_19);
lean_ctor_set_uint8(x_734, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_734, sizeof(void*)*8 + 1, x_733);
lean_inc(x_729);
x_735 = l_Lean_mkApp(x_2, x_729);
x_736 = lean_expr_instantiate1(x_114, x_729);
lean_dec(x_729);
lean_dec(x_114);
x_1 = x_734;
x_2 = x_735;
x_3 = x_736;
x_10 = x_730;
goto _start;
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; 
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_738 = lean_ctor_get(x_728, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_728, 1);
lean_inc(x_739);
if (lean_is_exclusive(x_728)) {
 lean_ctor_release(x_728, 0);
 lean_ctor_release(x_728, 1);
 x_740 = x_728;
} else {
 lean_dec_ref(x_728);
 x_740 = lean_box(0);
}
if (lean_is_scalar(x_740)) {
 x_741 = lean_alloc_ctor(1, 2, 0);
} else {
 x_741 = x_740;
}
lean_ctor_set(x_741, 0, x_738);
lean_ctor_set(x_741, 1, x_739);
return x_741;
}
}
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_8);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_742 = lean_ctor_get(x_571, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_571, 1);
lean_inc(x_743);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 lean_ctor_release(x_571, 1);
 x_744 = x_571;
} else {
 lean_dec_ref(x_571);
 x_744 = lean_box(0);
}
if (lean_is_scalar(x_744)) {
 x_745 = lean_alloc_ctor(1, 2, 0);
} else {
 x_745 = x_744;
}
lean_ctor_set(x_745, 0, x_742);
lean_ctor_set(x_745, 1, x_743);
return x_745;
}
}
}
}
case 2:
{
lean_object* x_746; uint8_t x_747; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_746 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_747 = !lean_is_exclusive(x_1);
if (x_747 == 0)
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_748 = lean_ctor_get(x_1, 7);
lean_dec(x_748);
x_749 = lean_ctor_get(x_1, 6);
lean_dec(x_749);
x_750 = lean_ctor_get(x_1, 5);
lean_dec(x_750);
x_751 = lean_ctor_get(x_1, 4);
lean_dec(x_751);
x_752 = lean_ctor_get(x_1, 3);
lean_dec(x_752);
x_753 = lean_ctor_get(x_1, 2);
lean_dec(x_753);
x_754 = lean_ctor_get(x_1, 1);
lean_dec(x_754);
x_755 = lean_ctor_get(x_1, 0);
lean_dec(x_755);
if (lean_obj_tag(x_746) == 0)
{
lean_object* x_756; uint8_t x_757; lean_object* x_758; uint8_t x_759; 
x_756 = lean_ctor_get(x_746, 1);
lean_inc(x_756);
lean_dec(x_746);
x_757 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_ctor_set_uint8(x_1, sizeof(void*)*8 + 1, x_757);
x_758 = lean_array_get_size(x_12);
x_759 = lean_nat_dec_lt(x_15, x_758);
lean_dec(x_758);
if (x_759 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_760; 
x_760 = l_Lean_Expr_getOptParamDefault_x3f(x_113);
if (lean_obj_tag(x_760) == 0)
{
lean_object* x_761; 
x_761 = l_Lean_Expr_getAutoParamTactic_x3f(x_113);
if (lean_obj_tag(x_761) == 0)
{
uint8_t x_762; 
lean_dec(x_1);
lean_dec(x_114);
lean_dec(x_113);
x_762 = l_Array_isEmpty___rarg(x_16);
if (x_762 == 0)
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_763 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_763, 0, x_112);
x_764 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_765 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_765, 0, x_764);
lean_ctor_set(x_765, 1, x_763);
x_766 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_767 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_767, 0, x_765);
lean_ctor_set(x_767, 1, x_766);
x_768 = x_16;
x_769 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_116, x_768);
x_770 = x_769;
x_771 = l_Array_toList___rarg(x_770);
lean_dec(x_770);
x_772 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_771);
x_773 = l_Array_HasRepr___rarg___closed__1;
x_774 = lean_string_append(x_773, x_772);
lean_dec(x_772);
x_775 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_775, 0, x_774);
x_776 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_776, 0, x_775);
x_777 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_777, 0, x_767);
lean_ctor_set(x_777, 1, x_776);
x_778 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_777, x_4, x_5, x_6, x_7, x_8, x_9, x_756);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_778;
}
else
{
lean_object* x_779; uint8_t x_780; 
lean_dec(x_112);
lean_dec(x_16);
x_779 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_780 = l_Lean_checkTraceOption(x_22, x_779);
lean_dec(x_22);
if (x_780 == 0)
{
lean_object* x_781; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_781 = x_756;
goto block_793;
}
else
{
lean_object* x_794; lean_object* x_795; 
x_794 = lean_ctor_get(x_13, 0);
lean_inc(x_794);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_795 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_794, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_756);
if (lean_obj_tag(x_795) == 0)
{
lean_object* x_796; 
x_796 = lean_ctor_get(x_795, 1);
lean_inc(x_796);
lean_dec(x_795);
x_781 = x_796;
goto block_793;
}
else
{
uint8_t x_797; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_797 = !lean_is_exclusive(x_795);
if (x_797 == 0)
{
return x_795;
}
else
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; 
x_798 = lean_ctor_get(x_795, 0);
x_799 = lean_ctor_get(x_795, 1);
lean_inc(x_799);
lean_inc(x_798);
lean_dec(x_795);
x_800 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_800, 0, x_798);
lean_ctor_set(x_800, 1, x_799);
return x_800;
}
}
}
block_793:
{
lean_object* x_782; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_782 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_781);
lean_dec(x_17);
if (lean_obj_tag(x_782) == 0)
{
lean_object* x_783; lean_object* x_784; uint8_t x_785; 
x_783 = lean_ctor_get(x_782, 1);
lean_inc(x_783);
lean_dec(x_782);
lean_inc(x_2);
x_784 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__12(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_783);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_785 = !lean_is_exclusive(x_784);
if (x_785 == 0)
{
lean_object* x_786; 
x_786 = lean_ctor_get(x_784, 0);
lean_dec(x_786);
lean_ctor_set(x_784, 0, x_2);
return x_784;
}
else
{
lean_object* x_787; lean_object* x_788; 
x_787 = lean_ctor_get(x_784, 1);
lean_inc(x_787);
lean_dec(x_784);
x_788 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_788, 0, x_2);
lean_ctor_set(x_788, 1, x_787);
return x_788;
}
}
else
{
uint8_t x_789; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_789 = !lean_is_exclusive(x_782);
if (x_789 == 0)
{
return x_782;
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_790 = lean_ctor_get(x_782, 0);
x_791 = lean_ctor_get(x_782, 1);
lean_inc(x_791);
lean_inc(x_790);
lean_dec(x_782);
x_792 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_792, 0, x_790);
lean_ctor_set(x_792, 1, x_791);
return x_792;
}
}
}
}
else
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; 
lean_inc(x_2);
x_801 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_801, 0, x_2);
x_802 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_779, x_801, x_4, x_5, x_6, x_7, x_8, x_9, x_756);
x_803 = lean_ctor_get(x_802, 1);
lean_inc(x_803);
lean_dec(x_802);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_804 = x_803;
goto block_816;
}
else
{
lean_object* x_817; lean_object* x_818; 
x_817 = lean_ctor_get(x_13, 0);
lean_inc(x_817);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_818 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_817, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_803);
if (lean_obj_tag(x_818) == 0)
{
lean_object* x_819; 
x_819 = lean_ctor_get(x_818, 1);
lean_inc(x_819);
lean_dec(x_818);
x_804 = x_819;
goto block_816;
}
else
{
uint8_t x_820; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_820 = !lean_is_exclusive(x_818);
if (x_820 == 0)
{
return x_818;
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_821 = lean_ctor_get(x_818, 0);
x_822 = lean_ctor_get(x_818, 1);
lean_inc(x_822);
lean_inc(x_821);
lean_dec(x_818);
x_823 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_823, 0, x_821);
lean_ctor_set(x_823, 1, x_822);
return x_823;
}
}
}
block_816:
{
lean_object* x_805; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_805 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_804);
lean_dec(x_17);
if (lean_obj_tag(x_805) == 0)
{
lean_object* x_806; lean_object* x_807; uint8_t x_808; 
x_806 = lean_ctor_get(x_805, 1);
lean_inc(x_806);
lean_dec(x_805);
lean_inc(x_2);
x_807 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__13(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_806);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_808 = !lean_is_exclusive(x_807);
if (x_808 == 0)
{
lean_object* x_809; 
x_809 = lean_ctor_get(x_807, 0);
lean_dec(x_809);
lean_ctor_set(x_807, 0, x_2);
return x_807;
}
else
{
lean_object* x_810; lean_object* x_811; 
x_810 = lean_ctor_get(x_807, 1);
lean_inc(x_810);
lean_dec(x_807);
x_811 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_811, 0, x_2);
lean_ctor_set(x_811, 1, x_810);
return x_811;
}
}
else
{
uint8_t x_812; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_812 = !lean_is_exclusive(x_805);
if (x_812 == 0)
{
return x_805;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_813 = lean_ctor_get(x_805, 0);
x_814 = lean_ctor_get(x_805, 1);
lean_inc(x_814);
lean_inc(x_813);
lean_dec(x_805);
x_815 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_815, 0, x_813);
lean_ctor_set(x_815, 1, x_814);
return x_815;
}
}
}
}
}
}
else
{
lean_object* x_824; 
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_824 = lean_ctor_get(x_761, 0);
lean_inc(x_824);
lean_dec(x_761);
if (lean_obj_tag(x_824) == 4)
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; 
x_825 = lean_ctor_get(x_824, 0);
lean_inc(x_825);
lean_dec(x_824);
x_826 = lean_st_ref_get(x_9, x_756);
x_827 = lean_ctor_get(x_826, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_826, 1);
lean_inc(x_828);
lean_dec(x_826);
x_829 = lean_ctor_get(x_827, 0);
lean_inc(x_829);
lean_dec(x_827);
x_830 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_829, x_825);
if (lean_obj_tag(x_830) == 0)
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; 
lean_dec(x_1);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_11);
lean_dec(x_2);
x_831 = lean_ctor_get(x_830, 0);
lean_inc(x_831);
lean_dec(x_830);
x_832 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_832, 0, x_831);
x_833 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_833, 0, x_832);
x_834 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_833, x_4, x_5, x_6, x_7, x_8, x_9, x_828);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_834;
}
else
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
x_835 = lean_ctor_get(x_830, 0);
lean_inc(x_835);
lean_dec(x_830);
x_836 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_828);
x_837 = lean_ctor_get(x_836, 1);
lean_inc(x_837);
lean_dec(x_836);
x_838 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_837);
x_839 = lean_ctor_get(x_838, 1);
lean_inc(x_839);
lean_dec(x_838);
x_840 = l_Lean_Syntax_getArgs(x_835);
lean_dec(x_835);
x_841 = l_Array_empty___closed__1;
x_842 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_840, x_840, x_116, x_841);
lean_dec(x_840);
x_843 = l_Lean_nullKind___closed__2;
x_844 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_844, 0, x_843);
lean_ctor_set(x_844, 1, x_842);
x_845 = lean_array_push(x_841, x_844);
x_846 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__17;
x_847 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_847, 0, x_846);
lean_ctor_set(x_847, 1, x_845);
x_848 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_849 = lean_array_push(x_848, x_847);
x_850 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__20;
x_851 = lean_array_push(x_849, x_850);
x_852 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__19;
x_853 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_853, 0, x_852);
lean_ctor_set(x_853, 1, x_851);
x_854 = lean_array_push(x_841, x_853);
x_855 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_855, 0, x_843);
lean_ctor_set(x_855, 1, x_854);
x_856 = lean_array_push(x_841, x_855);
x_857 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_857, 0, x_846);
lean_ctor_set(x_857, 1, x_856);
x_858 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_859 = lean_array_push(x_858, x_857);
x_860 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_861 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_861, 0, x_860);
lean_ctor_set(x_861, 1, x_859);
x_862 = l_Lean_Syntax_copyInfo(x_861, x_11);
lean_dec(x_11);
x_863 = l_Lean_Expr_getAppNumArgsAux___main(x_113, x_116);
x_864 = lean_nat_sub(x_863, x_116);
lean_dec(x_863);
x_865 = lean_unsigned_to_nat(1u);
x_866 = lean_nat_sub(x_864, x_865);
lean_dec(x_864);
x_867 = l_Lean_Expr_getRevArg_x21___main(x_113, x_866);
lean_dec(x_113);
x_868 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_868, 0, x_862);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_869 = l___private_Lean_Elab_App_2__elabArg(x_2, x_868, x_867, x_4, x_5, x_6, x_7, x_8, x_9, x_839);
if (lean_obj_tag(x_869) == 0)
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; 
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
lean_dec(x_869);
lean_inc(x_870);
x_872 = l_Lean_mkApp(x_2, x_870);
x_873 = lean_expr_instantiate1(x_114, x_870);
lean_dec(x_870);
lean_dec(x_114);
x_2 = x_872;
x_3 = x_873;
x_10 = x_871;
goto _start;
}
else
{
uint8_t x_875; 
lean_dec(x_1);
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_875 = !lean_is_exclusive(x_869);
if (x_875 == 0)
{
return x_869;
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; 
x_876 = lean_ctor_get(x_869, 0);
x_877 = lean_ctor_get(x_869, 1);
lean_inc(x_877);
lean_inc(x_876);
lean_dec(x_869);
x_878 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_878, 0, x_876);
lean_ctor_set(x_878, 1, x_877);
return x_878;
}
}
}
}
else
{
lean_object* x_879; lean_object* x_880; 
lean_dec(x_824);
lean_dec(x_1);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_11);
lean_dec(x_2);
x_879 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_880 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_879, x_4, x_5, x_6, x_7, x_8, x_9, x_756);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_880;
}
}
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_881 = lean_ctor_get(x_760, 0);
lean_inc(x_881);
lean_dec(x_760);
lean_inc(x_881);
x_882 = l_Lean_mkApp(x_2, x_881);
x_883 = lean_expr_instantiate1(x_114, x_881);
lean_dec(x_881);
lean_dec(x_114);
x_2 = x_882;
x_3 = x_883;
x_10 = x_756;
goto _start;
}
}
else
{
uint8_t x_885; 
lean_dec(x_1);
lean_dec(x_114);
lean_dec(x_113);
x_885 = l_Array_isEmpty___rarg(x_16);
if (x_885 == 0)
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_886 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_886, 0, x_112);
x_887 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_888 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_888, 0, x_887);
lean_ctor_set(x_888, 1, x_886);
x_889 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_890 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_890, 0, x_888);
lean_ctor_set(x_890, 1, x_889);
x_891 = x_16;
x_892 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_116, x_891);
x_893 = x_892;
x_894 = l_Array_toList___rarg(x_893);
lean_dec(x_893);
x_895 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_894);
x_896 = l_Array_HasRepr___rarg___closed__1;
x_897 = lean_string_append(x_896, x_895);
lean_dec(x_895);
x_898 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_898, 0, x_897);
x_899 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_899, 0, x_898);
x_900 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_900, 0, x_890);
lean_ctor_set(x_900, 1, x_899);
x_901 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_900, x_4, x_5, x_6, x_7, x_8, x_9, x_756);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_901;
}
else
{
lean_object* x_902; uint8_t x_903; 
lean_dec(x_112);
lean_dec(x_16);
x_902 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_903 = l_Lean_checkTraceOption(x_22, x_902);
lean_dec(x_22);
if (x_903 == 0)
{
lean_object* x_904; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_904 = x_756;
goto block_916;
}
else
{
lean_object* x_917; lean_object* x_918; 
x_917 = lean_ctor_get(x_13, 0);
lean_inc(x_917);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_918 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_917, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_756);
if (lean_obj_tag(x_918) == 0)
{
lean_object* x_919; 
x_919 = lean_ctor_get(x_918, 1);
lean_inc(x_919);
lean_dec(x_918);
x_904 = x_919;
goto block_916;
}
else
{
uint8_t x_920; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_920 = !lean_is_exclusive(x_918);
if (x_920 == 0)
{
return x_918;
}
else
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; 
x_921 = lean_ctor_get(x_918, 0);
x_922 = lean_ctor_get(x_918, 1);
lean_inc(x_922);
lean_inc(x_921);
lean_dec(x_918);
x_923 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_923, 0, x_921);
lean_ctor_set(x_923, 1, x_922);
return x_923;
}
}
}
block_916:
{
lean_object* x_905; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_905 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_904);
lean_dec(x_17);
if (lean_obj_tag(x_905) == 0)
{
lean_object* x_906; lean_object* x_907; uint8_t x_908; 
x_906 = lean_ctor_get(x_905, 1);
lean_inc(x_906);
lean_dec(x_905);
lean_inc(x_2);
x_907 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__14(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_906);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_908 = !lean_is_exclusive(x_907);
if (x_908 == 0)
{
lean_object* x_909; 
x_909 = lean_ctor_get(x_907, 0);
lean_dec(x_909);
lean_ctor_set(x_907, 0, x_2);
return x_907;
}
else
{
lean_object* x_910; lean_object* x_911; 
x_910 = lean_ctor_get(x_907, 1);
lean_inc(x_910);
lean_dec(x_907);
x_911 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_911, 0, x_2);
lean_ctor_set(x_911, 1, x_910);
return x_911;
}
}
else
{
uint8_t x_912; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_912 = !lean_is_exclusive(x_905);
if (x_912 == 0)
{
return x_905;
}
else
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; 
x_913 = lean_ctor_get(x_905, 0);
x_914 = lean_ctor_get(x_905, 1);
lean_inc(x_914);
lean_inc(x_913);
lean_dec(x_905);
x_915 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_915, 0, x_913);
lean_ctor_set(x_915, 1, x_914);
return x_915;
}
}
}
}
else
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; 
lean_inc(x_2);
x_924 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_924, 0, x_2);
x_925 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_902, x_924, x_4, x_5, x_6, x_7, x_8, x_9, x_756);
x_926 = lean_ctor_get(x_925, 1);
lean_inc(x_926);
lean_dec(x_925);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_927 = x_926;
goto block_939;
}
else
{
lean_object* x_940; lean_object* x_941; 
x_940 = lean_ctor_get(x_13, 0);
lean_inc(x_940);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_941 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_940, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_926);
if (lean_obj_tag(x_941) == 0)
{
lean_object* x_942; 
x_942 = lean_ctor_get(x_941, 1);
lean_inc(x_942);
lean_dec(x_941);
x_927 = x_942;
goto block_939;
}
else
{
uint8_t x_943; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_943 = !lean_is_exclusive(x_941);
if (x_943 == 0)
{
return x_941;
}
else
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; 
x_944 = lean_ctor_get(x_941, 0);
x_945 = lean_ctor_get(x_941, 1);
lean_inc(x_945);
lean_inc(x_944);
lean_dec(x_941);
x_946 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_946, 0, x_944);
lean_ctor_set(x_946, 1, x_945);
return x_946;
}
}
}
block_939:
{
lean_object* x_928; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_928 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_927);
lean_dec(x_17);
if (lean_obj_tag(x_928) == 0)
{
lean_object* x_929; lean_object* x_930; uint8_t x_931; 
x_929 = lean_ctor_get(x_928, 1);
lean_inc(x_929);
lean_dec(x_928);
lean_inc(x_2);
x_930 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__15(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_929);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_931 = !lean_is_exclusive(x_930);
if (x_931 == 0)
{
lean_object* x_932; 
x_932 = lean_ctor_get(x_930, 0);
lean_dec(x_932);
lean_ctor_set(x_930, 0, x_2);
return x_930;
}
else
{
lean_object* x_933; lean_object* x_934; 
x_933 = lean_ctor_get(x_930, 1);
lean_inc(x_933);
lean_dec(x_930);
x_934 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_934, 0, x_2);
lean_ctor_set(x_934, 1, x_933);
return x_934;
}
}
else
{
uint8_t x_935; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_935 = !lean_is_exclusive(x_928);
if (x_935 == 0)
{
return x_928;
}
else
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_936 = lean_ctor_get(x_928, 0);
x_937 = lean_ctor_get(x_928, 1);
lean_inc(x_937);
lean_inc(x_936);
lean_dec(x_928);
x_938 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_938, 0, x_936);
lean_ctor_set(x_938, 1, x_937);
return x_938;
}
}
}
}
}
}
}
else
{
lean_object* x_947; lean_object* x_948; 
lean_dec(x_1);
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_3);
x_947 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_948 = l___private_Lean_Elab_App_2__elabArg(x_2, x_947, x_113, x_4, x_5, x_6, x_7, x_8, x_9, x_756);
if (lean_obj_tag(x_948) == 0)
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; 
x_949 = lean_ctor_get(x_948, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_948, 1);
lean_inc(x_950);
lean_dec(x_948);
x_951 = lean_unsigned_to_nat(1u);
x_952 = lean_nat_add(x_15, x_951);
lean_dec(x_15);
x_953 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_953, 0, x_11);
lean_ctor_set(x_953, 1, x_12);
lean_ctor_set(x_953, 2, x_13);
lean_ctor_set(x_953, 3, x_952);
lean_ctor_set(x_953, 4, x_16);
lean_ctor_set(x_953, 5, x_17);
lean_ctor_set(x_953, 6, x_18);
lean_ctor_set(x_953, 7, x_19);
lean_ctor_set_uint8(x_953, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_953, sizeof(void*)*8 + 1, x_757);
lean_inc(x_949);
x_954 = l_Lean_mkApp(x_2, x_949);
x_955 = lean_expr_instantiate1(x_114, x_949);
lean_dec(x_949);
lean_dec(x_114);
x_1 = x_953;
x_2 = x_954;
x_3 = x_955;
x_10 = x_950;
goto _start;
}
else
{
uint8_t x_957; 
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_957 = !lean_is_exclusive(x_948);
if (x_957 == 0)
{
return x_948;
}
else
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; 
x_958 = lean_ctor_get(x_948, 0);
x_959 = lean_ctor_get(x_948, 1);
lean_inc(x_959);
lean_inc(x_958);
lean_dec(x_948);
x_960 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_960, 0, x_958);
lean_ctor_set(x_960, 1, x_959);
return x_960;
}
}
}
}
else
{
uint8_t x_961; 
lean_free_object(x_1);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_8);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_961 = !lean_is_exclusive(x_746);
if (x_961 == 0)
{
return x_746;
}
else
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; 
x_962 = lean_ctor_get(x_746, 0);
x_963 = lean_ctor_get(x_746, 1);
lean_inc(x_963);
lean_inc(x_962);
lean_dec(x_746);
x_964 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_964, 0, x_962);
lean_ctor_set(x_964, 1, x_963);
return x_964;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_746) == 0)
{
lean_object* x_965; uint8_t x_966; lean_object* x_967; lean_object* x_968; uint8_t x_969; 
x_965 = lean_ctor_get(x_746, 1);
lean_inc(x_965);
lean_dec(x_746);
x_966 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_967 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_967, 0, x_11);
lean_ctor_set(x_967, 1, x_12);
lean_ctor_set(x_967, 2, x_13);
lean_ctor_set(x_967, 3, x_15);
lean_ctor_set(x_967, 4, x_16);
lean_ctor_set(x_967, 5, x_17);
lean_ctor_set(x_967, 6, x_18);
lean_ctor_set(x_967, 7, x_19);
lean_ctor_set_uint8(x_967, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_967, sizeof(void*)*8 + 1, x_966);
x_968 = lean_array_get_size(x_12);
x_969 = lean_nat_dec_lt(x_15, x_968);
lean_dec(x_968);
if (x_969 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_970; 
x_970 = l_Lean_Expr_getOptParamDefault_x3f(x_113);
if (lean_obj_tag(x_970) == 0)
{
lean_object* x_971; 
x_971 = l_Lean_Expr_getAutoParamTactic_x3f(x_113);
if (lean_obj_tag(x_971) == 0)
{
uint8_t x_972; 
lean_dec(x_967);
lean_dec(x_114);
lean_dec(x_113);
x_972 = l_Array_isEmpty___rarg(x_16);
if (x_972 == 0)
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_973 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_973, 0, x_112);
x_974 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_975 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_975, 0, x_974);
lean_ctor_set(x_975, 1, x_973);
x_976 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_977 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_977, 0, x_975);
lean_ctor_set(x_977, 1, x_976);
x_978 = x_16;
x_979 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_116, x_978);
x_980 = x_979;
x_981 = l_Array_toList___rarg(x_980);
lean_dec(x_980);
x_982 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_981);
x_983 = l_Array_HasRepr___rarg___closed__1;
x_984 = lean_string_append(x_983, x_982);
lean_dec(x_982);
x_985 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_985, 0, x_984);
x_986 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_986, 0, x_985);
x_987 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_987, 0, x_977);
lean_ctor_set(x_987, 1, x_986);
x_988 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_987, x_4, x_5, x_6, x_7, x_8, x_9, x_965);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_988;
}
else
{
lean_object* x_989; uint8_t x_990; 
lean_dec(x_112);
lean_dec(x_16);
x_989 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_990 = l_Lean_checkTraceOption(x_22, x_989);
lean_dec(x_22);
if (x_990 == 0)
{
lean_object* x_991; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_991 = x_965;
goto block_1002;
}
else
{
lean_object* x_1003; lean_object* x_1004; 
x_1003 = lean_ctor_get(x_13, 0);
lean_inc(x_1003);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1004 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1003, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_965);
if (lean_obj_tag(x_1004) == 0)
{
lean_object* x_1005; 
x_1005 = lean_ctor_get(x_1004, 1);
lean_inc(x_1005);
lean_dec(x_1004);
x_991 = x_1005;
goto block_1002;
}
else
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1006 = lean_ctor_get(x_1004, 0);
lean_inc(x_1006);
x_1007 = lean_ctor_get(x_1004, 1);
lean_inc(x_1007);
if (lean_is_exclusive(x_1004)) {
 lean_ctor_release(x_1004, 0);
 lean_ctor_release(x_1004, 1);
 x_1008 = x_1004;
} else {
 lean_dec_ref(x_1004);
 x_1008 = lean_box(0);
}
if (lean_is_scalar(x_1008)) {
 x_1009 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1009 = x_1008;
}
lean_ctor_set(x_1009, 0, x_1006);
lean_ctor_set(x_1009, 1, x_1007);
return x_1009;
}
}
block_1002:
{
lean_object* x_992; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_992 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_991);
lean_dec(x_17);
if (lean_obj_tag(x_992) == 0)
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; 
x_993 = lean_ctor_get(x_992, 1);
lean_inc(x_993);
lean_dec(x_992);
lean_inc(x_2);
x_994 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__12(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_993);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_995 = lean_ctor_get(x_994, 1);
lean_inc(x_995);
if (lean_is_exclusive(x_994)) {
 lean_ctor_release(x_994, 0);
 lean_ctor_release(x_994, 1);
 x_996 = x_994;
} else {
 lean_dec_ref(x_994);
 x_996 = lean_box(0);
}
if (lean_is_scalar(x_996)) {
 x_997 = lean_alloc_ctor(0, 2, 0);
} else {
 x_997 = x_996;
}
lean_ctor_set(x_997, 0, x_2);
lean_ctor_set(x_997, 1, x_995);
return x_997;
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_998 = lean_ctor_get(x_992, 0);
lean_inc(x_998);
x_999 = lean_ctor_get(x_992, 1);
lean_inc(x_999);
if (lean_is_exclusive(x_992)) {
 lean_ctor_release(x_992, 0);
 lean_ctor_release(x_992, 1);
 x_1000 = x_992;
} else {
 lean_dec_ref(x_992);
 x_1000 = lean_box(0);
}
if (lean_is_scalar(x_1000)) {
 x_1001 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1001 = x_1000;
}
lean_ctor_set(x_1001, 0, x_998);
lean_ctor_set(x_1001, 1, x_999);
return x_1001;
}
}
}
else
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
lean_inc(x_2);
x_1010 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1010, 0, x_2);
x_1011 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_989, x_1010, x_4, x_5, x_6, x_7, x_8, x_9, x_965);
x_1012 = lean_ctor_get(x_1011, 1);
lean_inc(x_1012);
lean_dec(x_1011);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1013 = x_1012;
goto block_1024;
}
else
{
lean_object* x_1025; lean_object* x_1026; 
x_1025 = lean_ctor_get(x_13, 0);
lean_inc(x_1025);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1026 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1025, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1012);
if (lean_obj_tag(x_1026) == 0)
{
lean_object* x_1027; 
x_1027 = lean_ctor_get(x_1026, 1);
lean_inc(x_1027);
lean_dec(x_1026);
x_1013 = x_1027;
goto block_1024;
}
else
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1028 = lean_ctor_get(x_1026, 0);
lean_inc(x_1028);
x_1029 = lean_ctor_get(x_1026, 1);
lean_inc(x_1029);
if (lean_is_exclusive(x_1026)) {
 lean_ctor_release(x_1026, 0);
 lean_ctor_release(x_1026, 1);
 x_1030 = x_1026;
} else {
 lean_dec_ref(x_1026);
 x_1030 = lean_box(0);
}
if (lean_is_scalar(x_1030)) {
 x_1031 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1031 = x_1030;
}
lean_ctor_set(x_1031, 0, x_1028);
lean_ctor_set(x_1031, 1, x_1029);
return x_1031;
}
}
block_1024:
{
lean_object* x_1014; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1014 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1013);
lean_dec(x_17);
if (lean_obj_tag(x_1014) == 0)
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1015 = lean_ctor_get(x_1014, 1);
lean_inc(x_1015);
lean_dec(x_1014);
lean_inc(x_2);
x_1016 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__13(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1015);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1017 = lean_ctor_get(x_1016, 1);
lean_inc(x_1017);
if (lean_is_exclusive(x_1016)) {
 lean_ctor_release(x_1016, 0);
 lean_ctor_release(x_1016, 1);
 x_1018 = x_1016;
} else {
 lean_dec_ref(x_1016);
 x_1018 = lean_box(0);
}
if (lean_is_scalar(x_1018)) {
 x_1019 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1019 = x_1018;
}
lean_ctor_set(x_1019, 0, x_2);
lean_ctor_set(x_1019, 1, x_1017);
return x_1019;
}
else
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1020 = lean_ctor_get(x_1014, 0);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_1014, 1);
lean_inc(x_1021);
if (lean_is_exclusive(x_1014)) {
 lean_ctor_release(x_1014, 0);
 lean_ctor_release(x_1014, 1);
 x_1022 = x_1014;
} else {
 lean_dec_ref(x_1014);
 x_1022 = lean_box(0);
}
if (lean_is_scalar(x_1022)) {
 x_1023 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1023 = x_1022;
}
lean_ctor_set(x_1023, 0, x_1020);
lean_ctor_set(x_1023, 1, x_1021);
return x_1023;
}
}
}
}
}
else
{
lean_object* x_1032; 
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_1032 = lean_ctor_get(x_971, 0);
lean_inc(x_1032);
lean_dec(x_971);
if (lean_obj_tag(x_1032) == 4)
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1033 = lean_ctor_get(x_1032, 0);
lean_inc(x_1033);
lean_dec(x_1032);
x_1034 = lean_st_ref_get(x_9, x_965);
x_1035 = lean_ctor_get(x_1034, 0);
lean_inc(x_1035);
x_1036 = lean_ctor_get(x_1034, 1);
lean_inc(x_1036);
lean_dec(x_1034);
x_1037 = lean_ctor_get(x_1035, 0);
lean_inc(x_1037);
lean_dec(x_1035);
x_1038 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1037, x_1033);
if (lean_obj_tag(x_1038) == 0)
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
lean_dec(x_967);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_11);
lean_dec(x_2);
x_1039 = lean_ctor_get(x_1038, 0);
lean_inc(x_1039);
lean_dec(x_1038);
x_1040 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1040, 0, x_1039);
x_1041 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1041, 0, x_1040);
x_1042 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1041, x_4, x_5, x_6, x_7, x_8, x_9, x_1036);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1042;
}
else
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; 
x_1043 = lean_ctor_get(x_1038, 0);
lean_inc(x_1043);
lean_dec(x_1038);
x_1044 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_1036);
x_1045 = lean_ctor_get(x_1044, 1);
lean_inc(x_1045);
lean_dec(x_1044);
x_1046 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_1045);
x_1047 = lean_ctor_get(x_1046, 1);
lean_inc(x_1047);
lean_dec(x_1046);
x_1048 = l_Lean_Syntax_getArgs(x_1043);
lean_dec(x_1043);
x_1049 = l_Array_empty___closed__1;
x_1050 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1048, x_1048, x_116, x_1049);
lean_dec(x_1048);
x_1051 = l_Lean_nullKind___closed__2;
x_1052 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1052, 0, x_1051);
lean_ctor_set(x_1052, 1, x_1050);
x_1053 = lean_array_push(x_1049, x_1052);
x_1054 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__17;
x_1055 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1055, 0, x_1054);
lean_ctor_set(x_1055, 1, x_1053);
x_1056 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_1057 = lean_array_push(x_1056, x_1055);
x_1058 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__20;
x_1059 = lean_array_push(x_1057, x_1058);
x_1060 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__19;
x_1061 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1061, 0, x_1060);
lean_ctor_set(x_1061, 1, x_1059);
x_1062 = lean_array_push(x_1049, x_1061);
x_1063 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1063, 0, x_1051);
lean_ctor_set(x_1063, 1, x_1062);
x_1064 = lean_array_push(x_1049, x_1063);
x_1065 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1065, 0, x_1054);
lean_ctor_set(x_1065, 1, x_1064);
x_1066 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1067 = lean_array_push(x_1066, x_1065);
x_1068 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_1069 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1069, 0, x_1068);
lean_ctor_set(x_1069, 1, x_1067);
x_1070 = l_Lean_Syntax_copyInfo(x_1069, x_11);
lean_dec(x_11);
x_1071 = l_Lean_Expr_getAppNumArgsAux___main(x_113, x_116);
x_1072 = lean_nat_sub(x_1071, x_116);
lean_dec(x_1071);
x_1073 = lean_unsigned_to_nat(1u);
x_1074 = lean_nat_sub(x_1072, x_1073);
lean_dec(x_1072);
x_1075 = l_Lean_Expr_getRevArg_x21___main(x_113, x_1074);
lean_dec(x_113);
x_1076 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1076, 0, x_1070);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1077 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1076, x_1075, x_4, x_5, x_6, x_7, x_8, x_9, x_1047);
if (lean_obj_tag(x_1077) == 0)
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; 
x_1078 = lean_ctor_get(x_1077, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1077, 1);
lean_inc(x_1079);
lean_dec(x_1077);
lean_inc(x_1078);
x_1080 = l_Lean_mkApp(x_2, x_1078);
x_1081 = lean_expr_instantiate1(x_114, x_1078);
lean_dec(x_1078);
lean_dec(x_114);
x_1 = x_967;
x_2 = x_1080;
x_3 = x_1081;
x_10 = x_1079;
goto _start;
}
else
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; 
lean_dec(x_967);
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1083 = lean_ctor_get(x_1077, 0);
lean_inc(x_1083);
x_1084 = lean_ctor_get(x_1077, 1);
lean_inc(x_1084);
if (lean_is_exclusive(x_1077)) {
 lean_ctor_release(x_1077, 0);
 lean_ctor_release(x_1077, 1);
 x_1085 = x_1077;
} else {
 lean_dec_ref(x_1077);
 x_1085 = lean_box(0);
}
if (lean_is_scalar(x_1085)) {
 x_1086 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1086 = x_1085;
}
lean_ctor_set(x_1086, 0, x_1083);
lean_ctor_set(x_1086, 1, x_1084);
return x_1086;
}
}
}
else
{
lean_object* x_1087; lean_object* x_1088; 
lean_dec(x_1032);
lean_dec(x_967);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_11);
lean_dec(x_2);
x_1087 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1088 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1087, x_4, x_5, x_6, x_7, x_8, x_9, x_965);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1088;
}
}
}
else
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_1089 = lean_ctor_get(x_970, 0);
lean_inc(x_1089);
lean_dec(x_970);
lean_inc(x_1089);
x_1090 = l_Lean_mkApp(x_2, x_1089);
x_1091 = lean_expr_instantiate1(x_114, x_1089);
lean_dec(x_1089);
lean_dec(x_114);
x_1 = x_967;
x_2 = x_1090;
x_3 = x_1091;
x_10 = x_965;
goto _start;
}
}
else
{
uint8_t x_1093; 
lean_dec(x_967);
lean_dec(x_114);
lean_dec(x_113);
x_1093 = l_Array_isEmpty___rarg(x_16);
if (x_1093 == 0)
{
lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_1094 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1094, 0, x_112);
x_1095 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1096 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1096, 0, x_1095);
lean_ctor_set(x_1096, 1, x_1094);
x_1097 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1098 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1098, 0, x_1096);
lean_ctor_set(x_1098, 1, x_1097);
x_1099 = x_16;
x_1100 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_116, x_1099);
x_1101 = x_1100;
x_1102 = l_Array_toList___rarg(x_1101);
lean_dec(x_1101);
x_1103 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1102);
x_1104 = l_Array_HasRepr___rarg___closed__1;
x_1105 = lean_string_append(x_1104, x_1103);
lean_dec(x_1103);
x_1106 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1106, 0, x_1105);
x_1107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1107, 0, x_1106);
x_1108 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1108, 0, x_1098);
lean_ctor_set(x_1108, 1, x_1107);
x_1109 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1108, x_4, x_5, x_6, x_7, x_8, x_9, x_965);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1109;
}
else
{
lean_object* x_1110; uint8_t x_1111; 
lean_dec(x_112);
lean_dec(x_16);
x_1110 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1111 = l_Lean_checkTraceOption(x_22, x_1110);
lean_dec(x_22);
if (x_1111 == 0)
{
lean_object* x_1112; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1112 = x_965;
goto block_1123;
}
else
{
lean_object* x_1124; lean_object* x_1125; 
x_1124 = lean_ctor_get(x_13, 0);
lean_inc(x_1124);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1125 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1124, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_965);
if (lean_obj_tag(x_1125) == 0)
{
lean_object* x_1126; 
x_1126 = lean_ctor_get(x_1125, 1);
lean_inc(x_1126);
lean_dec(x_1125);
x_1112 = x_1126;
goto block_1123;
}
else
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1127 = lean_ctor_get(x_1125, 0);
lean_inc(x_1127);
x_1128 = lean_ctor_get(x_1125, 1);
lean_inc(x_1128);
if (lean_is_exclusive(x_1125)) {
 lean_ctor_release(x_1125, 0);
 lean_ctor_release(x_1125, 1);
 x_1129 = x_1125;
} else {
 lean_dec_ref(x_1125);
 x_1129 = lean_box(0);
}
if (lean_is_scalar(x_1129)) {
 x_1130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1130 = x_1129;
}
lean_ctor_set(x_1130, 0, x_1127);
lean_ctor_set(x_1130, 1, x_1128);
return x_1130;
}
}
block_1123:
{
lean_object* x_1113; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1113 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1112);
lean_dec(x_17);
if (lean_obj_tag(x_1113) == 0)
{
lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1114 = lean_ctor_get(x_1113, 1);
lean_inc(x_1114);
lean_dec(x_1113);
lean_inc(x_2);
x_1115 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__14(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1114);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1116 = lean_ctor_get(x_1115, 1);
lean_inc(x_1116);
if (lean_is_exclusive(x_1115)) {
 lean_ctor_release(x_1115, 0);
 lean_ctor_release(x_1115, 1);
 x_1117 = x_1115;
} else {
 lean_dec_ref(x_1115);
 x_1117 = lean_box(0);
}
if (lean_is_scalar(x_1117)) {
 x_1118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1118 = x_1117;
}
lean_ctor_set(x_1118, 0, x_2);
lean_ctor_set(x_1118, 1, x_1116);
return x_1118;
}
else
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1119 = lean_ctor_get(x_1113, 0);
lean_inc(x_1119);
x_1120 = lean_ctor_get(x_1113, 1);
lean_inc(x_1120);
if (lean_is_exclusive(x_1113)) {
 lean_ctor_release(x_1113, 0);
 lean_ctor_release(x_1113, 1);
 x_1121 = x_1113;
} else {
 lean_dec_ref(x_1113);
 x_1121 = lean_box(0);
}
if (lean_is_scalar(x_1121)) {
 x_1122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1122 = x_1121;
}
lean_ctor_set(x_1122, 0, x_1119);
lean_ctor_set(x_1122, 1, x_1120);
return x_1122;
}
}
}
else
{
lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; 
lean_inc(x_2);
x_1131 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1131, 0, x_2);
x_1132 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1110, x_1131, x_4, x_5, x_6, x_7, x_8, x_9, x_965);
x_1133 = lean_ctor_get(x_1132, 1);
lean_inc(x_1133);
lean_dec(x_1132);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1134 = x_1133;
goto block_1145;
}
else
{
lean_object* x_1146; lean_object* x_1147; 
x_1146 = lean_ctor_get(x_13, 0);
lean_inc(x_1146);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1147 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1146, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1133);
if (lean_obj_tag(x_1147) == 0)
{
lean_object* x_1148; 
x_1148 = lean_ctor_get(x_1147, 1);
lean_inc(x_1148);
lean_dec(x_1147);
x_1134 = x_1148;
goto block_1145;
}
else
{
lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1149 = lean_ctor_get(x_1147, 0);
lean_inc(x_1149);
x_1150 = lean_ctor_get(x_1147, 1);
lean_inc(x_1150);
if (lean_is_exclusive(x_1147)) {
 lean_ctor_release(x_1147, 0);
 lean_ctor_release(x_1147, 1);
 x_1151 = x_1147;
} else {
 lean_dec_ref(x_1147);
 x_1151 = lean_box(0);
}
if (lean_is_scalar(x_1151)) {
 x_1152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1152 = x_1151;
}
lean_ctor_set(x_1152, 0, x_1149);
lean_ctor_set(x_1152, 1, x_1150);
return x_1152;
}
}
block_1145:
{
lean_object* x_1135; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1135 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1134);
lean_dec(x_17);
if (lean_obj_tag(x_1135) == 0)
{
lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
x_1136 = lean_ctor_get(x_1135, 1);
lean_inc(x_1136);
lean_dec(x_1135);
lean_inc(x_2);
x_1137 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__15(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1136);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1138 = lean_ctor_get(x_1137, 1);
lean_inc(x_1138);
if (lean_is_exclusive(x_1137)) {
 lean_ctor_release(x_1137, 0);
 lean_ctor_release(x_1137, 1);
 x_1139 = x_1137;
} else {
 lean_dec_ref(x_1137);
 x_1139 = lean_box(0);
}
if (lean_is_scalar(x_1139)) {
 x_1140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1140 = x_1139;
}
lean_ctor_set(x_1140, 0, x_2);
lean_ctor_set(x_1140, 1, x_1138);
return x_1140;
}
else
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1141 = lean_ctor_get(x_1135, 0);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1135, 1);
lean_inc(x_1142);
if (lean_is_exclusive(x_1135)) {
 lean_ctor_release(x_1135, 0);
 lean_ctor_release(x_1135, 1);
 x_1143 = x_1135;
} else {
 lean_dec_ref(x_1135);
 x_1143 = lean_box(0);
}
if (lean_is_scalar(x_1143)) {
 x_1144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1144 = x_1143;
}
lean_ctor_set(x_1144, 0, x_1141);
lean_ctor_set(x_1144, 1, x_1142);
return x_1144;
}
}
}
}
}
}
else
{
lean_object* x_1153; lean_object* x_1154; 
lean_dec(x_967);
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_3);
x_1153 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1154 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1153, x_113, x_4, x_5, x_6, x_7, x_8, x_9, x_965);
if (lean_obj_tag(x_1154) == 0)
{
lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; 
x_1155 = lean_ctor_get(x_1154, 0);
lean_inc(x_1155);
x_1156 = lean_ctor_get(x_1154, 1);
lean_inc(x_1156);
lean_dec(x_1154);
x_1157 = lean_unsigned_to_nat(1u);
x_1158 = lean_nat_add(x_15, x_1157);
lean_dec(x_15);
x_1159 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1159, 0, x_11);
lean_ctor_set(x_1159, 1, x_12);
lean_ctor_set(x_1159, 2, x_13);
lean_ctor_set(x_1159, 3, x_1158);
lean_ctor_set(x_1159, 4, x_16);
lean_ctor_set(x_1159, 5, x_17);
lean_ctor_set(x_1159, 6, x_18);
lean_ctor_set(x_1159, 7, x_19);
lean_ctor_set_uint8(x_1159, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1159, sizeof(void*)*8 + 1, x_966);
lean_inc(x_1155);
x_1160 = l_Lean_mkApp(x_2, x_1155);
x_1161 = lean_expr_instantiate1(x_114, x_1155);
lean_dec(x_1155);
lean_dec(x_114);
x_1 = x_1159;
x_2 = x_1160;
x_3 = x_1161;
x_10 = x_1156;
goto _start;
}
else
{
lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; 
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1163 = lean_ctor_get(x_1154, 0);
lean_inc(x_1163);
x_1164 = lean_ctor_get(x_1154, 1);
lean_inc(x_1164);
if (lean_is_exclusive(x_1154)) {
 lean_ctor_release(x_1154, 0);
 lean_ctor_release(x_1154, 1);
 x_1165 = x_1154;
} else {
 lean_dec_ref(x_1154);
 x_1165 = lean_box(0);
}
if (lean_is_scalar(x_1165)) {
 x_1166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1166 = x_1165;
}
lean_ctor_set(x_1166, 0, x_1163);
lean_ctor_set(x_1166, 1, x_1164);
return x_1166;
}
}
}
else
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_8);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1167 = lean_ctor_get(x_746, 0);
lean_inc(x_1167);
x_1168 = lean_ctor_get(x_746, 1);
lean_inc(x_1168);
if (lean_is_exclusive(x_746)) {
 lean_ctor_release(x_746, 0);
 lean_ctor_release(x_746, 1);
 x_1169 = x_746;
} else {
 lean_dec_ref(x_746);
 x_1169 = lean_box(0);
}
if (lean_is_scalar(x_1169)) {
 x_1170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1170 = x_1169;
}
lean_ctor_set(x_1170, 0, x_1167);
lean_ctor_set(x_1170, 1, x_1168);
return x_1170;
}
}
}
case 3:
{
if (x_14 == 0)
{
uint8_t x_1171; 
lean_dec(x_112);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_3);
x_1171 = !lean_is_exclusive(x_1);
if (x_1171 == 0)
{
lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; uint8_t x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; 
x_1172 = lean_ctor_get(x_1, 7);
lean_dec(x_1172);
x_1173 = lean_ctor_get(x_1, 6);
lean_dec(x_1173);
x_1174 = lean_ctor_get(x_1, 5);
lean_dec(x_1174);
x_1175 = lean_ctor_get(x_1, 4);
lean_dec(x_1175);
x_1176 = lean_ctor_get(x_1, 3);
lean_dec(x_1176);
x_1177 = lean_ctor_get(x_1, 2);
lean_dec(x_1177);
x_1178 = lean_ctor_get(x_1, 1);
lean_dec(x_1178);
x_1179 = lean_ctor_get(x_1, 0);
lean_dec(x_1179);
x_1180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1180, 0, x_113);
x_1181 = 1;
x_1182 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_1183 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_1180, x_1181, x_1182, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_1184 = lean_ctor_get(x_1183, 0);
lean_inc(x_1184);
x_1185 = lean_ctor_get(x_1183, 1);
lean_inc(x_1185);
lean_dec(x_1183);
x_1186 = l_Lean_Expr_mvarId_x21(x_1184);
x_1187 = lean_array_push(x_17, x_1186);
lean_ctor_set(x_1, 5, x_1187);
lean_inc(x_1184);
x_1188 = l_Lean_mkApp(x_2, x_1184);
x_1189 = lean_expr_instantiate1(x_114, x_1184);
lean_dec(x_1184);
lean_dec(x_114);
x_2 = x_1188;
x_3 = x_1189;
x_10 = x_1185;
goto _start;
}
else
{
lean_object* x_1191; uint8_t x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; 
lean_dec(x_1);
x_1191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1191, 0, x_113);
x_1192 = 1;
x_1193 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_1194 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_1191, x_1192, x_1193, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_1195 = lean_ctor_get(x_1194, 0);
lean_inc(x_1195);
x_1196 = lean_ctor_get(x_1194, 1);
lean_inc(x_1196);
lean_dec(x_1194);
x_1197 = l_Lean_Expr_mvarId_x21(x_1195);
x_1198 = lean_array_push(x_17, x_1197);
x_1199 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1199, 0, x_11);
lean_ctor_set(x_1199, 1, x_12);
lean_ctor_set(x_1199, 2, x_13);
lean_ctor_set(x_1199, 3, x_15);
lean_ctor_set(x_1199, 4, x_16);
lean_ctor_set(x_1199, 5, x_1198);
lean_ctor_set(x_1199, 6, x_18);
lean_ctor_set(x_1199, 7, x_19);
lean_ctor_set_uint8(x_1199, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1199, sizeof(void*)*8 + 1, x_21);
lean_inc(x_1195);
x_1200 = l_Lean_mkApp(x_2, x_1195);
x_1201 = lean_expr_instantiate1(x_114, x_1195);
lean_dec(x_1195);
lean_dec(x_114);
x_1 = x_1199;
x_2 = x_1200;
x_3 = x_1201;
x_10 = x_1196;
goto _start;
}
}
else
{
uint8_t x_1203; 
x_1203 = l___private_Lean_Elab_App_9__nextArgIsHole(x_1);
if (x_1203 == 0)
{
lean_object* x_1204; uint8_t x_1205; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_1204 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_1205 = !lean_is_exclusive(x_1);
if (x_1205 == 0)
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; 
x_1206 = lean_ctor_get(x_1, 7);
lean_dec(x_1206);
x_1207 = lean_ctor_get(x_1, 6);
lean_dec(x_1207);
x_1208 = lean_ctor_get(x_1, 5);
lean_dec(x_1208);
x_1209 = lean_ctor_get(x_1, 4);
lean_dec(x_1209);
x_1210 = lean_ctor_get(x_1, 3);
lean_dec(x_1210);
x_1211 = lean_ctor_get(x_1, 2);
lean_dec(x_1211);
x_1212 = lean_ctor_get(x_1, 1);
lean_dec(x_1212);
x_1213 = lean_ctor_get(x_1, 0);
lean_dec(x_1213);
if (lean_obj_tag(x_1204) == 0)
{
lean_object* x_1214; lean_object* x_1215; uint8_t x_1216; 
x_1214 = lean_ctor_get(x_1204, 1);
lean_inc(x_1214);
lean_dec(x_1204);
x_1215 = lean_array_get_size(x_12);
x_1216 = lean_nat_dec_lt(x_15, x_1215);
lean_dec(x_1215);
if (x_1216 == 0)
{
uint8_t x_1217; 
lean_free_object(x_1);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_1217 = l_Array_isEmpty___rarg(x_16);
if (x_1217 == 0)
{
lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_1218 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1218, 0, x_112);
x_1219 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1220 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1220, 0, x_1219);
lean_ctor_set(x_1220, 1, x_1218);
x_1221 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1222 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1222, 0, x_1220);
lean_ctor_set(x_1222, 1, x_1221);
x_1223 = x_16;
x_1224 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_116, x_1223);
x_1225 = x_1224;
x_1226 = l_Array_toList___rarg(x_1225);
lean_dec(x_1225);
x_1227 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1226);
x_1228 = l_Array_HasRepr___rarg___closed__1;
x_1229 = lean_string_append(x_1228, x_1227);
lean_dec(x_1227);
x_1230 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1230, 0, x_1229);
x_1231 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1231, 0, x_1230);
x_1232 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1232, 0, x_1222);
lean_ctor_set(x_1232, 1, x_1231);
x_1233 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1232, x_4, x_5, x_6, x_7, x_8, x_9, x_1214);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1233;
}
else
{
lean_object* x_1234; uint8_t x_1235; 
lean_dec(x_112);
lean_dec(x_16);
x_1234 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1235 = l_Lean_checkTraceOption(x_22, x_1234);
lean_dec(x_22);
if (x_1235 == 0)
{
lean_object* x_1236; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1236 = x_1214;
goto block_1248;
}
else
{
lean_object* x_1249; lean_object* x_1250; 
x_1249 = lean_ctor_get(x_13, 0);
lean_inc(x_1249);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1250 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1249, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1214);
if (lean_obj_tag(x_1250) == 0)
{
lean_object* x_1251; 
x_1251 = lean_ctor_get(x_1250, 1);
lean_inc(x_1251);
lean_dec(x_1250);
x_1236 = x_1251;
goto block_1248;
}
else
{
uint8_t x_1252; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1252 = !lean_is_exclusive(x_1250);
if (x_1252 == 0)
{
return x_1250;
}
else
{
lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; 
x_1253 = lean_ctor_get(x_1250, 0);
x_1254 = lean_ctor_get(x_1250, 1);
lean_inc(x_1254);
lean_inc(x_1253);
lean_dec(x_1250);
x_1255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1255, 0, x_1253);
lean_ctor_set(x_1255, 1, x_1254);
return x_1255;
}
}
}
block_1248:
{
lean_object* x_1237; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1237 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1236);
lean_dec(x_17);
if (lean_obj_tag(x_1237) == 0)
{
lean_object* x_1238; lean_object* x_1239; uint8_t x_1240; 
x_1238 = lean_ctor_get(x_1237, 1);
lean_inc(x_1238);
lean_dec(x_1237);
lean_inc(x_2);
x_1239 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__16(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1238);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1240 = !lean_is_exclusive(x_1239);
if (x_1240 == 0)
{
lean_object* x_1241; 
x_1241 = lean_ctor_get(x_1239, 0);
lean_dec(x_1241);
lean_ctor_set(x_1239, 0, x_2);
return x_1239;
}
else
{
lean_object* x_1242; lean_object* x_1243; 
x_1242 = lean_ctor_get(x_1239, 1);
lean_inc(x_1242);
lean_dec(x_1239);
x_1243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1243, 0, x_2);
lean_ctor_set(x_1243, 1, x_1242);
return x_1243;
}
}
else
{
uint8_t x_1244; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1244 = !lean_is_exclusive(x_1237);
if (x_1244 == 0)
{
return x_1237;
}
else
{
lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; 
x_1245 = lean_ctor_get(x_1237, 0);
x_1246 = lean_ctor_get(x_1237, 1);
lean_inc(x_1246);
lean_inc(x_1245);
lean_dec(x_1237);
x_1247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1247, 0, x_1245);
lean_ctor_set(x_1247, 1, x_1246);
return x_1247;
}
}
}
}
else
{
lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; 
lean_inc(x_2);
x_1256 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1256, 0, x_2);
x_1257 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1234, x_1256, x_4, x_5, x_6, x_7, x_8, x_9, x_1214);
x_1258 = lean_ctor_get(x_1257, 1);
lean_inc(x_1258);
lean_dec(x_1257);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1259 = x_1258;
goto block_1271;
}
else
{
lean_object* x_1272; lean_object* x_1273; 
x_1272 = lean_ctor_get(x_13, 0);
lean_inc(x_1272);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1273 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1272, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1258);
if (lean_obj_tag(x_1273) == 0)
{
lean_object* x_1274; 
x_1274 = lean_ctor_get(x_1273, 1);
lean_inc(x_1274);
lean_dec(x_1273);
x_1259 = x_1274;
goto block_1271;
}
else
{
uint8_t x_1275; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1275 = !lean_is_exclusive(x_1273);
if (x_1275 == 0)
{
return x_1273;
}
else
{
lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; 
x_1276 = lean_ctor_get(x_1273, 0);
x_1277 = lean_ctor_get(x_1273, 1);
lean_inc(x_1277);
lean_inc(x_1276);
lean_dec(x_1273);
x_1278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1278, 0, x_1276);
lean_ctor_set(x_1278, 1, x_1277);
return x_1278;
}
}
}
block_1271:
{
lean_object* x_1260; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1260 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1259);
lean_dec(x_17);
if (lean_obj_tag(x_1260) == 0)
{
lean_object* x_1261; lean_object* x_1262; uint8_t x_1263; 
x_1261 = lean_ctor_get(x_1260, 1);
lean_inc(x_1261);
lean_dec(x_1260);
lean_inc(x_2);
x_1262 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__17(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1261);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1263 = !lean_is_exclusive(x_1262);
if (x_1263 == 0)
{
lean_object* x_1264; 
x_1264 = lean_ctor_get(x_1262, 0);
lean_dec(x_1264);
lean_ctor_set(x_1262, 0, x_2);
return x_1262;
}
else
{
lean_object* x_1265; lean_object* x_1266; 
x_1265 = lean_ctor_get(x_1262, 1);
lean_inc(x_1265);
lean_dec(x_1262);
x_1266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1266, 0, x_2);
lean_ctor_set(x_1266, 1, x_1265);
return x_1266;
}
}
else
{
uint8_t x_1267; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1267 = !lean_is_exclusive(x_1260);
if (x_1267 == 0)
{
return x_1260;
}
else
{
lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; 
x_1268 = lean_ctor_get(x_1260, 0);
x_1269 = lean_ctor_get(x_1260, 1);
lean_inc(x_1269);
lean_inc(x_1268);
lean_dec(x_1260);
x_1270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1270, 0, x_1268);
lean_ctor_set(x_1270, 1, x_1269);
return x_1270;
}
}
}
}
}
}
else
{
lean_object* x_1279; lean_object* x_1280; 
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_3);
x_1279 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1280 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1279, x_113, x_4, x_5, x_6, x_7, x_8, x_9, x_1214);
if (lean_obj_tag(x_1280) == 0)
{
lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; uint8_t x_1285; lean_object* x_1286; lean_object* x_1287; 
x_1281 = lean_ctor_get(x_1280, 0);
lean_inc(x_1281);
x_1282 = lean_ctor_get(x_1280, 1);
lean_inc(x_1282);
lean_dec(x_1280);
x_1283 = lean_unsigned_to_nat(1u);
x_1284 = lean_nat_add(x_15, x_1283);
lean_dec(x_15);
x_1285 = 1;
lean_ctor_set(x_1, 3, x_1284);
lean_ctor_set_uint8(x_1, sizeof(void*)*8 + 1, x_1285);
lean_inc(x_1281);
x_1286 = l_Lean_mkApp(x_2, x_1281);
x_1287 = lean_expr_instantiate1(x_114, x_1281);
lean_dec(x_1281);
lean_dec(x_114);
x_2 = x_1286;
x_3 = x_1287;
x_10 = x_1282;
goto _start;
}
else
{
uint8_t x_1289; 
lean_free_object(x_1);
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1289 = !lean_is_exclusive(x_1280);
if (x_1289 == 0)
{
return x_1280;
}
else
{
lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; 
x_1290 = lean_ctor_get(x_1280, 0);
x_1291 = lean_ctor_get(x_1280, 1);
lean_inc(x_1291);
lean_inc(x_1290);
lean_dec(x_1280);
x_1292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1292, 0, x_1290);
lean_ctor_set(x_1292, 1, x_1291);
return x_1292;
}
}
}
}
else
{
uint8_t x_1293; 
lean_free_object(x_1);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_8);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1293 = !lean_is_exclusive(x_1204);
if (x_1293 == 0)
{
return x_1204;
}
else
{
lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; 
x_1294 = lean_ctor_get(x_1204, 0);
x_1295 = lean_ctor_get(x_1204, 1);
lean_inc(x_1295);
lean_inc(x_1294);
lean_dec(x_1204);
x_1296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1296, 0, x_1294);
lean_ctor_set(x_1296, 1, x_1295);
return x_1296;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_1204) == 0)
{
lean_object* x_1297; lean_object* x_1298; uint8_t x_1299; 
x_1297 = lean_ctor_get(x_1204, 1);
lean_inc(x_1297);
lean_dec(x_1204);
x_1298 = lean_array_get_size(x_12);
x_1299 = lean_nat_dec_lt(x_15, x_1298);
lean_dec(x_1298);
if (x_1299 == 0)
{
uint8_t x_1300; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_1300 = l_Array_isEmpty___rarg(x_16);
if (x_1300 == 0)
{
lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_1301 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1301, 0, x_112);
x_1302 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1303 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1303, 0, x_1302);
lean_ctor_set(x_1303, 1, x_1301);
x_1304 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1305 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1305, 0, x_1303);
lean_ctor_set(x_1305, 1, x_1304);
x_1306 = x_16;
x_1307 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_116, x_1306);
x_1308 = x_1307;
x_1309 = l_Array_toList___rarg(x_1308);
lean_dec(x_1308);
x_1310 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1309);
x_1311 = l_Array_HasRepr___rarg___closed__1;
x_1312 = lean_string_append(x_1311, x_1310);
lean_dec(x_1310);
x_1313 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1313, 0, x_1312);
x_1314 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1314, 0, x_1313);
x_1315 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1315, 0, x_1305);
lean_ctor_set(x_1315, 1, x_1314);
x_1316 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1315, x_4, x_5, x_6, x_7, x_8, x_9, x_1297);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1316;
}
else
{
lean_object* x_1317; uint8_t x_1318; 
lean_dec(x_112);
lean_dec(x_16);
x_1317 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1318 = l_Lean_checkTraceOption(x_22, x_1317);
lean_dec(x_22);
if (x_1318 == 0)
{
lean_object* x_1319; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1319 = x_1297;
goto block_1330;
}
else
{
lean_object* x_1331; lean_object* x_1332; 
x_1331 = lean_ctor_get(x_13, 0);
lean_inc(x_1331);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1332 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1331, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1297);
if (lean_obj_tag(x_1332) == 0)
{
lean_object* x_1333; 
x_1333 = lean_ctor_get(x_1332, 1);
lean_inc(x_1333);
lean_dec(x_1332);
x_1319 = x_1333;
goto block_1330;
}
else
{
lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1334 = lean_ctor_get(x_1332, 0);
lean_inc(x_1334);
x_1335 = lean_ctor_get(x_1332, 1);
lean_inc(x_1335);
if (lean_is_exclusive(x_1332)) {
 lean_ctor_release(x_1332, 0);
 lean_ctor_release(x_1332, 1);
 x_1336 = x_1332;
} else {
 lean_dec_ref(x_1332);
 x_1336 = lean_box(0);
}
if (lean_is_scalar(x_1336)) {
 x_1337 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1337 = x_1336;
}
lean_ctor_set(x_1337, 0, x_1334);
lean_ctor_set(x_1337, 1, x_1335);
return x_1337;
}
}
block_1330:
{
lean_object* x_1320; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1320 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1319);
lean_dec(x_17);
if (lean_obj_tag(x_1320) == 0)
{
lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; 
x_1321 = lean_ctor_get(x_1320, 1);
lean_inc(x_1321);
lean_dec(x_1320);
lean_inc(x_2);
x_1322 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__16(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1321);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1323 = lean_ctor_get(x_1322, 1);
lean_inc(x_1323);
if (lean_is_exclusive(x_1322)) {
 lean_ctor_release(x_1322, 0);
 lean_ctor_release(x_1322, 1);
 x_1324 = x_1322;
} else {
 lean_dec_ref(x_1322);
 x_1324 = lean_box(0);
}
if (lean_is_scalar(x_1324)) {
 x_1325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1325 = x_1324;
}
lean_ctor_set(x_1325, 0, x_2);
lean_ctor_set(x_1325, 1, x_1323);
return x_1325;
}
else
{
lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1326 = lean_ctor_get(x_1320, 0);
lean_inc(x_1326);
x_1327 = lean_ctor_get(x_1320, 1);
lean_inc(x_1327);
if (lean_is_exclusive(x_1320)) {
 lean_ctor_release(x_1320, 0);
 lean_ctor_release(x_1320, 1);
 x_1328 = x_1320;
} else {
 lean_dec_ref(x_1320);
 x_1328 = lean_box(0);
}
if (lean_is_scalar(x_1328)) {
 x_1329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1329 = x_1328;
}
lean_ctor_set(x_1329, 0, x_1326);
lean_ctor_set(x_1329, 1, x_1327);
return x_1329;
}
}
}
else
{
lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; 
lean_inc(x_2);
x_1338 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1338, 0, x_2);
x_1339 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1317, x_1338, x_4, x_5, x_6, x_7, x_8, x_9, x_1297);
x_1340 = lean_ctor_get(x_1339, 1);
lean_inc(x_1340);
lean_dec(x_1339);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1341 = x_1340;
goto block_1352;
}
else
{
lean_object* x_1353; lean_object* x_1354; 
x_1353 = lean_ctor_get(x_13, 0);
lean_inc(x_1353);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1354 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1353, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1340);
if (lean_obj_tag(x_1354) == 0)
{
lean_object* x_1355; 
x_1355 = lean_ctor_get(x_1354, 1);
lean_inc(x_1355);
lean_dec(x_1354);
x_1341 = x_1355;
goto block_1352;
}
else
{
lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1356 = lean_ctor_get(x_1354, 0);
lean_inc(x_1356);
x_1357 = lean_ctor_get(x_1354, 1);
lean_inc(x_1357);
if (lean_is_exclusive(x_1354)) {
 lean_ctor_release(x_1354, 0);
 lean_ctor_release(x_1354, 1);
 x_1358 = x_1354;
} else {
 lean_dec_ref(x_1354);
 x_1358 = lean_box(0);
}
if (lean_is_scalar(x_1358)) {
 x_1359 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1359 = x_1358;
}
lean_ctor_set(x_1359, 0, x_1356);
lean_ctor_set(x_1359, 1, x_1357);
return x_1359;
}
}
block_1352:
{
lean_object* x_1342; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1342 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1341);
lean_dec(x_17);
if (lean_obj_tag(x_1342) == 0)
{
lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; 
x_1343 = lean_ctor_get(x_1342, 1);
lean_inc(x_1343);
lean_dec(x_1342);
lean_inc(x_2);
x_1344 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__17(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1343);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1345 = lean_ctor_get(x_1344, 1);
lean_inc(x_1345);
if (lean_is_exclusive(x_1344)) {
 lean_ctor_release(x_1344, 0);
 lean_ctor_release(x_1344, 1);
 x_1346 = x_1344;
} else {
 lean_dec_ref(x_1344);
 x_1346 = lean_box(0);
}
if (lean_is_scalar(x_1346)) {
 x_1347 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1347 = x_1346;
}
lean_ctor_set(x_1347, 0, x_2);
lean_ctor_set(x_1347, 1, x_1345);
return x_1347;
}
else
{
lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1348 = lean_ctor_get(x_1342, 0);
lean_inc(x_1348);
x_1349 = lean_ctor_get(x_1342, 1);
lean_inc(x_1349);
if (lean_is_exclusive(x_1342)) {
 lean_ctor_release(x_1342, 0);
 lean_ctor_release(x_1342, 1);
 x_1350 = x_1342;
} else {
 lean_dec_ref(x_1342);
 x_1350 = lean_box(0);
}
if (lean_is_scalar(x_1350)) {
 x_1351 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1351 = x_1350;
}
lean_ctor_set(x_1351, 0, x_1348);
lean_ctor_set(x_1351, 1, x_1349);
return x_1351;
}
}
}
}
}
else
{
lean_object* x_1360; lean_object* x_1361; 
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_3);
x_1360 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1361 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1360, x_113, x_4, x_5, x_6, x_7, x_8, x_9, x_1297);
if (lean_obj_tag(x_1361) == 0)
{
lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; uint8_t x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; 
x_1362 = lean_ctor_get(x_1361, 0);
lean_inc(x_1362);
x_1363 = lean_ctor_get(x_1361, 1);
lean_inc(x_1363);
lean_dec(x_1361);
x_1364 = lean_unsigned_to_nat(1u);
x_1365 = lean_nat_add(x_15, x_1364);
lean_dec(x_15);
x_1366 = 1;
x_1367 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1367, 0, x_11);
lean_ctor_set(x_1367, 1, x_12);
lean_ctor_set(x_1367, 2, x_13);
lean_ctor_set(x_1367, 3, x_1365);
lean_ctor_set(x_1367, 4, x_16);
lean_ctor_set(x_1367, 5, x_17);
lean_ctor_set(x_1367, 6, x_18);
lean_ctor_set(x_1367, 7, x_19);
lean_ctor_set_uint8(x_1367, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1367, sizeof(void*)*8 + 1, x_1366);
lean_inc(x_1362);
x_1368 = l_Lean_mkApp(x_2, x_1362);
x_1369 = lean_expr_instantiate1(x_114, x_1362);
lean_dec(x_1362);
lean_dec(x_114);
x_1 = x_1367;
x_2 = x_1368;
x_3 = x_1369;
x_10 = x_1363;
goto _start;
}
else
{
lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1371 = lean_ctor_get(x_1361, 0);
lean_inc(x_1371);
x_1372 = lean_ctor_get(x_1361, 1);
lean_inc(x_1372);
if (lean_is_exclusive(x_1361)) {
 lean_ctor_release(x_1361, 0);
 lean_ctor_release(x_1361, 1);
 x_1373 = x_1361;
} else {
 lean_dec_ref(x_1361);
 x_1373 = lean_box(0);
}
if (lean_is_scalar(x_1373)) {
 x_1374 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1374 = x_1373;
}
lean_ctor_set(x_1374, 0, x_1371);
lean_ctor_set(x_1374, 1, x_1372);
return x_1374;
}
}
}
else
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_8);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1375 = lean_ctor_get(x_1204, 0);
lean_inc(x_1375);
x_1376 = lean_ctor_get(x_1204, 1);
lean_inc(x_1376);
if (lean_is_exclusive(x_1204)) {
 lean_ctor_release(x_1204, 0);
 lean_ctor_release(x_1204, 1);
 x_1377 = x_1204;
} else {
 lean_dec_ref(x_1204);
 x_1377 = lean_box(0);
}
if (lean_is_scalar(x_1377)) {
 x_1378 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1378 = x_1377;
}
lean_ctor_set(x_1378, 0, x_1375);
lean_ctor_set(x_1378, 1, x_1376);
return x_1378;
}
}
}
else
{
uint8_t x_1379; 
lean_dec(x_112);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_3);
x_1379 = !lean_is_exclusive(x_1);
if (x_1379 == 0)
{
lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; uint8_t x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; 
x_1380 = lean_ctor_get(x_1, 7);
lean_dec(x_1380);
x_1381 = lean_ctor_get(x_1, 6);
lean_dec(x_1381);
x_1382 = lean_ctor_get(x_1, 5);
lean_dec(x_1382);
x_1383 = lean_ctor_get(x_1, 4);
lean_dec(x_1383);
x_1384 = lean_ctor_get(x_1, 3);
lean_dec(x_1384);
x_1385 = lean_ctor_get(x_1, 2);
lean_dec(x_1385);
x_1386 = lean_ctor_get(x_1, 1);
lean_dec(x_1386);
x_1387 = lean_ctor_get(x_1, 0);
lean_dec(x_1387);
x_1388 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1388, 0, x_113);
x_1389 = 1;
x_1390 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_1391 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_1388, x_1389, x_1390, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_1392 = lean_ctor_get(x_1391, 0);
lean_inc(x_1392);
x_1393 = lean_ctor_get(x_1391, 1);
lean_inc(x_1393);
lean_dec(x_1391);
x_1394 = lean_unsigned_to_nat(1u);
x_1395 = lean_nat_add(x_15, x_1394);
lean_dec(x_15);
x_1396 = l_Lean_Expr_mvarId_x21(x_1392);
x_1397 = lean_array_push(x_17, x_1396);
lean_ctor_set(x_1, 5, x_1397);
lean_ctor_set(x_1, 3, x_1395);
lean_inc(x_1392);
x_1398 = l_Lean_mkApp(x_2, x_1392);
x_1399 = lean_expr_instantiate1(x_114, x_1392);
lean_dec(x_1392);
lean_dec(x_114);
x_2 = x_1398;
x_3 = x_1399;
x_10 = x_1393;
goto _start;
}
else
{
lean_object* x_1401; uint8_t x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; 
lean_dec(x_1);
x_1401 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1401, 0, x_113);
x_1402 = 1;
x_1403 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_1404 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_1401, x_1402, x_1403, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_1405 = lean_ctor_get(x_1404, 0);
lean_inc(x_1405);
x_1406 = lean_ctor_get(x_1404, 1);
lean_inc(x_1406);
lean_dec(x_1404);
x_1407 = lean_unsigned_to_nat(1u);
x_1408 = lean_nat_add(x_15, x_1407);
lean_dec(x_15);
x_1409 = l_Lean_Expr_mvarId_x21(x_1405);
x_1410 = lean_array_push(x_17, x_1409);
x_1411 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1411, 0, x_11);
lean_ctor_set(x_1411, 1, x_12);
lean_ctor_set(x_1411, 2, x_13);
lean_ctor_set(x_1411, 3, x_1408);
lean_ctor_set(x_1411, 4, x_16);
lean_ctor_set(x_1411, 5, x_1410);
lean_ctor_set(x_1411, 6, x_18);
lean_ctor_set(x_1411, 7, x_19);
lean_ctor_set_uint8(x_1411, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1411, sizeof(void*)*8 + 1, x_21);
lean_inc(x_1405);
x_1412 = l_Lean_mkApp(x_2, x_1405);
x_1413 = lean_expr_instantiate1(x_114, x_1405);
lean_dec(x_1405);
lean_dec(x_114);
x_1 = x_1411;
x_2 = x_1412;
x_3 = x_1413;
x_10 = x_1406;
goto _start;
}
}
}
}
default: 
{
lean_object* x_1415; uint8_t x_1416; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_1415 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_1416 = !lean_is_exclusive(x_1);
if (x_1416 == 0)
{
lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; 
x_1417 = lean_ctor_get(x_1, 7);
lean_dec(x_1417);
x_1418 = lean_ctor_get(x_1, 6);
lean_dec(x_1418);
x_1419 = lean_ctor_get(x_1, 5);
lean_dec(x_1419);
x_1420 = lean_ctor_get(x_1, 4);
lean_dec(x_1420);
x_1421 = lean_ctor_get(x_1, 3);
lean_dec(x_1421);
x_1422 = lean_ctor_get(x_1, 2);
lean_dec(x_1422);
x_1423 = lean_ctor_get(x_1, 1);
lean_dec(x_1423);
x_1424 = lean_ctor_get(x_1, 0);
lean_dec(x_1424);
if (lean_obj_tag(x_1415) == 0)
{
lean_object* x_1425; uint8_t x_1426; lean_object* x_1427; uint8_t x_1428; 
x_1425 = lean_ctor_get(x_1415, 1);
lean_inc(x_1425);
lean_dec(x_1415);
x_1426 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_ctor_set_uint8(x_1, sizeof(void*)*8 + 1, x_1426);
x_1427 = lean_array_get_size(x_12);
x_1428 = lean_nat_dec_lt(x_15, x_1427);
lean_dec(x_1427);
if (x_1428 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_1429; 
x_1429 = l_Lean_Expr_getOptParamDefault_x3f(x_113);
if (lean_obj_tag(x_1429) == 0)
{
lean_object* x_1430; 
x_1430 = l_Lean_Expr_getAutoParamTactic_x3f(x_113);
if (lean_obj_tag(x_1430) == 0)
{
uint8_t x_1431; 
lean_dec(x_1);
lean_dec(x_114);
lean_dec(x_113);
x_1431 = l_Array_isEmpty___rarg(x_16);
if (x_1431 == 0)
{
lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_1432 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1432, 0, x_112);
x_1433 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1434 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1434, 0, x_1433);
lean_ctor_set(x_1434, 1, x_1432);
x_1435 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1436 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1436, 0, x_1434);
lean_ctor_set(x_1436, 1, x_1435);
x_1437 = x_16;
x_1438 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_116, x_1437);
x_1439 = x_1438;
x_1440 = l_Array_toList___rarg(x_1439);
lean_dec(x_1439);
x_1441 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1440);
x_1442 = l_Array_HasRepr___rarg___closed__1;
x_1443 = lean_string_append(x_1442, x_1441);
lean_dec(x_1441);
x_1444 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1444, 0, x_1443);
x_1445 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1445, 0, x_1444);
x_1446 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1446, 0, x_1436);
lean_ctor_set(x_1446, 1, x_1445);
x_1447 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1446, x_4, x_5, x_6, x_7, x_8, x_9, x_1425);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1447;
}
else
{
lean_object* x_1448; uint8_t x_1449; 
lean_dec(x_112);
lean_dec(x_16);
x_1448 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1449 = l_Lean_checkTraceOption(x_22, x_1448);
lean_dec(x_22);
if (x_1449 == 0)
{
lean_object* x_1450; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1450 = x_1425;
goto block_1462;
}
else
{
lean_object* x_1463; lean_object* x_1464; 
x_1463 = lean_ctor_get(x_13, 0);
lean_inc(x_1463);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1464 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1463, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1425);
if (lean_obj_tag(x_1464) == 0)
{
lean_object* x_1465; 
x_1465 = lean_ctor_get(x_1464, 1);
lean_inc(x_1465);
lean_dec(x_1464);
x_1450 = x_1465;
goto block_1462;
}
else
{
uint8_t x_1466; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1466 = !lean_is_exclusive(x_1464);
if (x_1466 == 0)
{
return x_1464;
}
else
{
lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; 
x_1467 = lean_ctor_get(x_1464, 0);
x_1468 = lean_ctor_get(x_1464, 1);
lean_inc(x_1468);
lean_inc(x_1467);
lean_dec(x_1464);
x_1469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1469, 0, x_1467);
lean_ctor_set(x_1469, 1, x_1468);
return x_1469;
}
}
}
block_1462:
{
lean_object* x_1451; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1451 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1450);
lean_dec(x_17);
if (lean_obj_tag(x_1451) == 0)
{
lean_object* x_1452; lean_object* x_1453; uint8_t x_1454; 
x_1452 = lean_ctor_get(x_1451, 1);
lean_inc(x_1452);
lean_dec(x_1451);
lean_inc(x_2);
x_1453 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__18(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1452);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1454 = !lean_is_exclusive(x_1453);
if (x_1454 == 0)
{
lean_object* x_1455; 
x_1455 = lean_ctor_get(x_1453, 0);
lean_dec(x_1455);
lean_ctor_set(x_1453, 0, x_2);
return x_1453;
}
else
{
lean_object* x_1456; lean_object* x_1457; 
x_1456 = lean_ctor_get(x_1453, 1);
lean_inc(x_1456);
lean_dec(x_1453);
x_1457 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1457, 0, x_2);
lean_ctor_set(x_1457, 1, x_1456);
return x_1457;
}
}
else
{
uint8_t x_1458; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1458 = !lean_is_exclusive(x_1451);
if (x_1458 == 0)
{
return x_1451;
}
else
{
lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; 
x_1459 = lean_ctor_get(x_1451, 0);
x_1460 = lean_ctor_get(x_1451, 1);
lean_inc(x_1460);
lean_inc(x_1459);
lean_dec(x_1451);
x_1461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1461, 0, x_1459);
lean_ctor_set(x_1461, 1, x_1460);
return x_1461;
}
}
}
}
else
{
lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; 
lean_inc(x_2);
x_1470 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1470, 0, x_2);
x_1471 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1448, x_1470, x_4, x_5, x_6, x_7, x_8, x_9, x_1425);
x_1472 = lean_ctor_get(x_1471, 1);
lean_inc(x_1472);
lean_dec(x_1471);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1473 = x_1472;
goto block_1485;
}
else
{
lean_object* x_1486; lean_object* x_1487; 
x_1486 = lean_ctor_get(x_13, 0);
lean_inc(x_1486);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1487 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1486, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1472);
if (lean_obj_tag(x_1487) == 0)
{
lean_object* x_1488; 
x_1488 = lean_ctor_get(x_1487, 1);
lean_inc(x_1488);
lean_dec(x_1487);
x_1473 = x_1488;
goto block_1485;
}
else
{
uint8_t x_1489; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1489 = !lean_is_exclusive(x_1487);
if (x_1489 == 0)
{
return x_1487;
}
else
{
lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; 
x_1490 = lean_ctor_get(x_1487, 0);
x_1491 = lean_ctor_get(x_1487, 1);
lean_inc(x_1491);
lean_inc(x_1490);
lean_dec(x_1487);
x_1492 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1492, 0, x_1490);
lean_ctor_set(x_1492, 1, x_1491);
return x_1492;
}
}
}
block_1485:
{
lean_object* x_1474; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1474 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1473);
lean_dec(x_17);
if (lean_obj_tag(x_1474) == 0)
{
lean_object* x_1475; lean_object* x_1476; uint8_t x_1477; 
x_1475 = lean_ctor_get(x_1474, 1);
lean_inc(x_1475);
lean_dec(x_1474);
lean_inc(x_2);
x_1476 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__19(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1475);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1477 = !lean_is_exclusive(x_1476);
if (x_1477 == 0)
{
lean_object* x_1478; 
x_1478 = lean_ctor_get(x_1476, 0);
lean_dec(x_1478);
lean_ctor_set(x_1476, 0, x_2);
return x_1476;
}
else
{
lean_object* x_1479; lean_object* x_1480; 
x_1479 = lean_ctor_get(x_1476, 1);
lean_inc(x_1479);
lean_dec(x_1476);
x_1480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1480, 0, x_2);
lean_ctor_set(x_1480, 1, x_1479);
return x_1480;
}
}
else
{
uint8_t x_1481; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1481 = !lean_is_exclusive(x_1474);
if (x_1481 == 0)
{
return x_1474;
}
else
{
lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; 
x_1482 = lean_ctor_get(x_1474, 0);
x_1483 = lean_ctor_get(x_1474, 1);
lean_inc(x_1483);
lean_inc(x_1482);
lean_dec(x_1474);
x_1484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1484, 0, x_1482);
lean_ctor_set(x_1484, 1, x_1483);
return x_1484;
}
}
}
}
}
}
else
{
lean_object* x_1493; 
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_1493 = lean_ctor_get(x_1430, 0);
lean_inc(x_1493);
lean_dec(x_1430);
if (lean_obj_tag(x_1493) == 4)
{
lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; 
x_1494 = lean_ctor_get(x_1493, 0);
lean_inc(x_1494);
lean_dec(x_1493);
x_1495 = lean_st_ref_get(x_9, x_1425);
x_1496 = lean_ctor_get(x_1495, 0);
lean_inc(x_1496);
x_1497 = lean_ctor_get(x_1495, 1);
lean_inc(x_1497);
lean_dec(x_1495);
x_1498 = lean_ctor_get(x_1496, 0);
lean_inc(x_1498);
lean_dec(x_1496);
x_1499 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1498, x_1494);
if (lean_obj_tag(x_1499) == 0)
{
lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; 
lean_dec(x_1);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_11);
lean_dec(x_2);
x_1500 = lean_ctor_get(x_1499, 0);
lean_inc(x_1500);
lean_dec(x_1499);
x_1501 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1501, 0, x_1500);
x_1502 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1502, 0, x_1501);
x_1503 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1502, x_4, x_5, x_6, x_7, x_8, x_9, x_1497);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1503;
}
else
{
lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; 
x_1504 = lean_ctor_get(x_1499, 0);
lean_inc(x_1504);
lean_dec(x_1499);
x_1505 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_1497);
x_1506 = lean_ctor_get(x_1505, 1);
lean_inc(x_1506);
lean_dec(x_1505);
x_1507 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_1506);
x_1508 = lean_ctor_get(x_1507, 1);
lean_inc(x_1508);
lean_dec(x_1507);
x_1509 = l_Lean_Syntax_getArgs(x_1504);
lean_dec(x_1504);
x_1510 = l_Array_empty___closed__1;
x_1511 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1509, x_1509, x_116, x_1510);
lean_dec(x_1509);
x_1512 = l_Lean_nullKind___closed__2;
x_1513 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1513, 0, x_1512);
lean_ctor_set(x_1513, 1, x_1511);
x_1514 = lean_array_push(x_1510, x_1513);
x_1515 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__17;
x_1516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1516, 0, x_1515);
lean_ctor_set(x_1516, 1, x_1514);
x_1517 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_1518 = lean_array_push(x_1517, x_1516);
x_1519 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__20;
x_1520 = lean_array_push(x_1518, x_1519);
x_1521 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__19;
x_1522 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1522, 0, x_1521);
lean_ctor_set(x_1522, 1, x_1520);
x_1523 = lean_array_push(x_1510, x_1522);
x_1524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1524, 0, x_1512);
lean_ctor_set(x_1524, 1, x_1523);
x_1525 = lean_array_push(x_1510, x_1524);
x_1526 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1526, 0, x_1515);
lean_ctor_set(x_1526, 1, x_1525);
x_1527 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1528 = lean_array_push(x_1527, x_1526);
x_1529 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_1530 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1530, 0, x_1529);
lean_ctor_set(x_1530, 1, x_1528);
x_1531 = l_Lean_Syntax_copyInfo(x_1530, x_11);
lean_dec(x_11);
x_1532 = l_Lean_Expr_getAppNumArgsAux___main(x_113, x_116);
x_1533 = lean_nat_sub(x_1532, x_116);
lean_dec(x_1532);
x_1534 = lean_unsigned_to_nat(1u);
x_1535 = lean_nat_sub(x_1533, x_1534);
lean_dec(x_1533);
x_1536 = l_Lean_Expr_getRevArg_x21___main(x_113, x_1535);
lean_dec(x_113);
x_1537 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1537, 0, x_1531);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1538 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1537, x_1536, x_4, x_5, x_6, x_7, x_8, x_9, x_1508);
if (lean_obj_tag(x_1538) == 0)
{
lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; 
x_1539 = lean_ctor_get(x_1538, 0);
lean_inc(x_1539);
x_1540 = lean_ctor_get(x_1538, 1);
lean_inc(x_1540);
lean_dec(x_1538);
lean_inc(x_1539);
x_1541 = l_Lean_mkApp(x_2, x_1539);
x_1542 = lean_expr_instantiate1(x_114, x_1539);
lean_dec(x_1539);
lean_dec(x_114);
x_2 = x_1541;
x_3 = x_1542;
x_10 = x_1540;
goto _start;
}
else
{
uint8_t x_1544; 
lean_dec(x_1);
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1544 = !lean_is_exclusive(x_1538);
if (x_1544 == 0)
{
return x_1538;
}
else
{
lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; 
x_1545 = lean_ctor_get(x_1538, 0);
x_1546 = lean_ctor_get(x_1538, 1);
lean_inc(x_1546);
lean_inc(x_1545);
lean_dec(x_1538);
x_1547 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1547, 0, x_1545);
lean_ctor_set(x_1547, 1, x_1546);
return x_1547;
}
}
}
}
else
{
lean_object* x_1548; lean_object* x_1549; 
lean_dec(x_1493);
lean_dec(x_1);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_11);
lean_dec(x_2);
x_1548 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1549 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1548, x_4, x_5, x_6, x_7, x_8, x_9, x_1425);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1549;
}
}
}
else
{
lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_1550 = lean_ctor_get(x_1429, 0);
lean_inc(x_1550);
lean_dec(x_1429);
lean_inc(x_1550);
x_1551 = l_Lean_mkApp(x_2, x_1550);
x_1552 = lean_expr_instantiate1(x_114, x_1550);
lean_dec(x_1550);
lean_dec(x_114);
x_2 = x_1551;
x_3 = x_1552;
x_10 = x_1425;
goto _start;
}
}
else
{
uint8_t x_1554; 
lean_dec(x_1);
lean_dec(x_114);
lean_dec(x_113);
x_1554 = l_Array_isEmpty___rarg(x_16);
if (x_1554 == 0)
{
lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_1555 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1555, 0, x_112);
x_1556 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1557 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1557, 0, x_1556);
lean_ctor_set(x_1557, 1, x_1555);
x_1558 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1559 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1559, 0, x_1557);
lean_ctor_set(x_1559, 1, x_1558);
x_1560 = x_16;
x_1561 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_116, x_1560);
x_1562 = x_1561;
x_1563 = l_Array_toList___rarg(x_1562);
lean_dec(x_1562);
x_1564 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1563);
x_1565 = l_Array_HasRepr___rarg___closed__1;
x_1566 = lean_string_append(x_1565, x_1564);
lean_dec(x_1564);
x_1567 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1567, 0, x_1566);
x_1568 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1568, 0, x_1567);
x_1569 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1569, 0, x_1559);
lean_ctor_set(x_1569, 1, x_1568);
x_1570 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1569, x_4, x_5, x_6, x_7, x_8, x_9, x_1425);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1570;
}
else
{
lean_object* x_1571; uint8_t x_1572; 
lean_dec(x_112);
lean_dec(x_16);
x_1571 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1572 = l_Lean_checkTraceOption(x_22, x_1571);
lean_dec(x_22);
if (x_1572 == 0)
{
lean_object* x_1573; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1573 = x_1425;
goto block_1585;
}
else
{
lean_object* x_1586; lean_object* x_1587; 
x_1586 = lean_ctor_get(x_13, 0);
lean_inc(x_1586);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1587 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1586, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1425);
if (lean_obj_tag(x_1587) == 0)
{
lean_object* x_1588; 
x_1588 = lean_ctor_get(x_1587, 1);
lean_inc(x_1588);
lean_dec(x_1587);
x_1573 = x_1588;
goto block_1585;
}
else
{
uint8_t x_1589; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1589 = !lean_is_exclusive(x_1587);
if (x_1589 == 0)
{
return x_1587;
}
else
{
lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; 
x_1590 = lean_ctor_get(x_1587, 0);
x_1591 = lean_ctor_get(x_1587, 1);
lean_inc(x_1591);
lean_inc(x_1590);
lean_dec(x_1587);
x_1592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1592, 0, x_1590);
lean_ctor_set(x_1592, 1, x_1591);
return x_1592;
}
}
}
block_1585:
{
lean_object* x_1574; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1574 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1573);
lean_dec(x_17);
if (lean_obj_tag(x_1574) == 0)
{
lean_object* x_1575; lean_object* x_1576; uint8_t x_1577; 
x_1575 = lean_ctor_get(x_1574, 1);
lean_inc(x_1575);
lean_dec(x_1574);
lean_inc(x_2);
x_1576 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__20(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1575);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1577 = !lean_is_exclusive(x_1576);
if (x_1577 == 0)
{
lean_object* x_1578; 
x_1578 = lean_ctor_get(x_1576, 0);
lean_dec(x_1578);
lean_ctor_set(x_1576, 0, x_2);
return x_1576;
}
else
{
lean_object* x_1579; lean_object* x_1580; 
x_1579 = lean_ctor_get(x_1576, 1);
lean_inc(x_1579);
lean_dec(x_1576);
x_1580 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1580, 0, x_2);
lean_ctor_set(x_1580, 1, x_1579);
return x_1580;
}
}
else
{
uint8_t x_1581; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1581 = !lean_is_exclusive(x_1574);
if (x_1581 == 0)
{
return x_1574;
}
else
{
lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; 
x_1582 = lean_ctor_get(x_1574, 0);
x_1583 = lean_ctor_get(x_1574, 1);
lean_inc(x_1583);
lean_inc(x_1582);
lean_dec(x_1574);
x_1584 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1584, 0, x_1582);
lean_ctor_set(x_1584, 1, x_1583);
return x_1584;
}
}
}
}
else
{
lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; 
lean_inc(x_2);
x_1593 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1593, 0, x_2);
x_1594 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1571, x_1593, x_4, x_5, x_6, x_7, x_8, x_9, x_1425);
x_1595 = lean_ctor_get(x_1594, 1);
lean_inc(x_1595);
lean_dec(x_1594);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1596 = x_1595;
goto block_1608;
}
else
{
lean_object* x_1609; lean_object* x_1610; 
x_1609 = lean_ctor_get(x_13, 0);
lean_inc(x_1609);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1610 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1609, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1595);
if (lean_obj_tag(x_1610) == 0)
{
lean_object* x_1611; 
x_1611 = lean_ctor_get(x_1610, 1);
lean_inc(x_1611);
lean_dec(x_1610);
x_1596 = x_1611;
goto block_1608;
}
else
{
uint8_t x_1612; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1612 = !lean_is_exclusive(x_1610);
if (x_1612 == 0)
{
return x_1610;
}
else
{
lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; 
x_1613 = lean_ctor_get(x_1610, 0);
x_1614 = lean_ctor_get(x_1610, 1);
lean_inc(x_1614);
lean_inc(x_1613);
lean_dec(x_1610);
x_1615 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1615, 0, x_1613);
lean_ctor_set(x_1615, 1, x_1614);
return x_1615;
}
}
}
block_1608:
{
lean_object* x_1597; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1597 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1596);
lean_dec(x_17);
if (lean_obj_tag(x_1597) == 0)
{
lean_object* x_1598; lean_object* x_1599; uint8_t x_1600; 
x_1598 = lean_ctor_get(x_1597, 1);
lean_inc(x_1598);
lean_dec(x_1597);
lean_inc(x_2);
x_1599 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__21(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1598);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1600 = !lean_is_exclusive(x_1599);
if (x_1600 == 0)
{
lean_object* x_1601; 
x_1601 = lean_ctor_get(x_1599, 0);
lean_dec(x_1601);
lean_ctor_set(x_1599, 0, x_2);
return x_1599;
}
else
{
lean_object* x_1602; lean_object* x_1603; 
x_1602 = lean_ctor_get(x_1599, 1);
lean_inc(x_1602);
lean_dec(x_1599);
x_1603 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1603, 0, x_2);
lean_ctor_set(x_1603, 1, x_1602);
return x_1603;
}
}
else
{
uint8_t x_1604; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1604 = !lean_is_exclusive(x_1597);
if (x_1604 == 0)
{
return x_1597;
}
else
{
lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; 
x_1605 = lean_ctor_get(x_1597, 0);
x_1606 = lean_ctor_get(x_1597, 1);
lean_inc(x_1606);
lean_inc(x_1605);
lean_dec(x_1597);
x_1607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1607, 0, x_1605);
lean_ctor_set(x_1607, 1, x_1606);
return x_1607;
}
}
}
}
}
}
}
else
{
lean_object* x_1616; lean_object* x_1617; 
lean_dec(x_1);
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_3);
x_1616 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1617 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1616, x_113, x_4, x_5, x_6, x_7, x_8, x_9, x_1425);
if (lean_obj_tag(x_1617) == 0)
{
lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; 
x_1618 = lean_ctor_get(x_1617, 0);
lean_inc(x_1618);
x_1619 = lean_ctor_get(x_1617, 1);
lean_inc(x_1619);
lean_dec(x_1617);
x_1620 = lean_unsigned_to_nat(1u);
x_1621 = lean_nat_add(x_15, x_1620);
lean_dec(x_15);
x_1622 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1622, 0, x_11);
lean_ctor_set(x_1622, 1, x_12);
lean_ctor_set(x_1622, 2, x_13);
lean_ctor_set(x_1622, 3, x_1621);
lean_ctor_set(x_1622, 4, x_16);
lean_ctor_set(x_1622, 5, x_17);
lean_ctor_set(x_1622, 6, x_18);
lean_ctor_set(x_1622, 7, x_19);
lean_ctor_set_uint8(x_1622, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1622, sizeof(void*)*8 + 1, x_1426);
lean_inc(x_1618);
x_1623 = l_Lean_mkApp(x_2, x_1618);
x_1624 = lean_expr_instantiate1(x_114, x_1618);
lean_dec(x_1618);
lean_dec(x_114);
x_1 = x_1622;
x_2 = x_1623;
x_3 = x_1624;
x_10 = x_1619;
goto _start;
}
else
{
uint8_t x_1626; 
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1626 = !lean_is_exclusive(x_1617);
if (x_1626 == 0)
{
return x_1617;
}
else
{
lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; 
x_1627 = lean_ctor_get(x_1617, 0);
x_1628 = lean_ctor_get(x_1617, 1);
lean_inc(x_1628);
lean_inc(x_1627);
lean_dec(x_1617);
x_1629 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1629, 0, x_1627);
lean_ctor_set(x_1629, 1, x_1628);
return x_1629;
}
}
}
}
else
{
uint8_t x_1630; 
lean_free_object(x_1);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_8);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1630 = !lean_is_exclusive(x_1415);
if (x_1630 == 0)
{
return x_1415;
}
else
{
lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; 
x_1631 = lean_ctor_get(x_1415, 0);
x_1632 = lean_ctor_get(x_1415, 1);
lean_inc(x_1632);
lean_inc(x_1631);
lean_dec(x_1415);
x_1633 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1633, 0, x_1631);
lean_ctor_set(x_1633, 1, x_1632);
return x_1633;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_1415) == 0)
{
lean_object* x_1634; uint8_t x_1635; lean_object* x_1636; lean_object* x_1637; uint8_t x_1638; 
x_1634 = lean_ctor_get(x_1415, 1);
lean_inc(x_1634);
lean_dec(x_1415);
x_1635 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_1636 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1636, 0, x_11);
lean_ctor_set(x_1636, 1, x_12);
lean_ctor_set(x_1636, 2, x_13);
lean_ctor_set(x_1636, 3, x_15);
lean_ctor_set(x_1636, 4, x_16);
lean_ctor_set(x_1636, 5, x_17);
lean_ctor_set(x_1636, 6, x_18);
lean_ctor_set(x_1636, 7, x_19);
lean_ctor_set_uint8(x_1636, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1636, sizeof(void*)*8 + 1, x_1635);
x_1637 = lean_array_get_size(x_12);
x_1638 = lean_nat_dec_lt(x_15, x_1637);
lean_dec(x_1637);
if (x_1638 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_1639; 
x_1639 = l_Lean_Expr_getOptParamDefault_x3f(x_113);
if (lean_obj_tag(x_1639) == 0)
{
lean_object* x_1640; 
x_1640 = l_Lean_Expr_getAutoParamTactic_x3f(x_113);
if (lean_obj_tag(x_1640) == 0)
{
uint8_t x_1641; 
lean_dec(x_1636);
lean_dec(x_114);
lean_dec(x_113);
x_1641 = l_Array_isEmpty___rarg(x_16);
if (x_1641 == 0)
{
lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_1642 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1642, 0, x_112);
x_1643 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1644 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1644, 0, x_1643);
lean_ctor_set(x_1644, 1, x_1642);
x_1645 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1646 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1646, 0, x_1644);
lean_ctor_set(x_1646, 1, x_1645);
x_1647 = x_16;
x_1648 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_116, x_1647);
x_1649 = x_1648;
x_1650 = l_Array_toList___rarg(x_1649);
lean_dec(x_1649);
x_1651 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1650);
x_1652 = l_Array_HasRepr___rarg___closed__1;
x_1653 = lean_string_append(x_1652, x_1651);
lean_dec(x_1651);
x_1654 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1654, 0, x_1653);
x_1655 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1655, 0, x_1654);
x_1656 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1656, 0, x_1646);
lean_ctor_set(x_1656, 1, x_1655);
x_1657 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1656, x_4, x_5, x_6, x_7, x_8, x_9, x_1634);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1657;
}
else
{
lean_object* x_1658; uint8_t x_1659; 
lean_dec(x_112);
lean_dec(x_16);
x_1658 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1659 = l_Lean_checkTraceOption(x_22, x_1658);
lean_dec(x_22);
if (x_1659 == 0)
{
lean_object* x_1660; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1660 = x_1634;
goto block_1671;
}
else
{
lean_object* x_1672; lean_object* x_1673; 
x_1672 = lean_ctor_get(x_13, 0);
lean_inc(x_1672);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1673 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1672, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1634);
if (lean_obj_tag(x_1673) == 0)
{
lean_object* x_1674; 
x_1674 = lean_ctor_get(x_1673, 1);
lean_inc(x_1674);
lean_dec(x_1673);
x_1660 = x_1674;
goto block_1671;
}
else
{
lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1675 = lean_ctor_get(x_1673, 0);
lean_inc(x_1675);
x_1676 = lean_ctor_get(x_1673, 1);
lean_inc(x_1676);
if (lean_is_exclusive(x_1673)) {
 lean_ctor_release(x_1673, 0);
 lean_ctor_release(x_1673, 1);
 x_1677 = x_1673;
} else {
 lean_dec_ref(x_1673);
 x_1677 = lean_box(0);
}
if (lean_is_scalar(x_1677)) {
 x_1678 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1678 = x_1677;
}
lean_ctor_set(x_1678, 0, x_1675);
lean_ctor_set(x_1678, 1, x_1676);
return x_1678;
}
}
block_1671:
{
lean_object* x_1661; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1661 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1660);
lean_dec(x_17);
if (lean_obj_tag(x_1661) == 0)
{
lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; 
x_1662 = lean_ctor_get(x_1661, 1);
lean_inc(x_1662);
lean_dec(x_1661);
lean_inc(x_2);
x_1663 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__18(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1662);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1664 = lean_ctor_get(x_1663, 1);
lean_inc(x_1664);
if (lean_is_exclusive(x_1663)) {
 lean_ctor_release(x_1663, 0);
 lean_ctor_release(x_1663, 1);
 x_1665 = x_1663;
} else {
 lean_dec_ref(x_1663);
 x_1665 = lean_box(0);
}
if (lean_is_scalar(x_1665)) {
 x_1666 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1666 = x_1665;
}
lean_ctor_set(x_1666, 0, x_2);
lean_ctor_set(x_1666, 1, x_1664);
return x_1666;
}
else
{
lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1667 = lean_ctor_get(x_1661, 0);
lean_inc(x_1667);
x_1668 = lean_ctor_get(x_1661, 1);
lean_inc(x_1668);
if (lean_is_exclusive(x_1661)) {
 lean_ctor_release(x_1661, 0);
 lean_ctor_release(x_1661, 1);
 x_1669 = x_1661;
} else {
 lean_dec_ref(x_1661);
 x_1669 = lean_box(0);
}
if (lean_is_scalar(x_1669)) {
 x_1670 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1670 = x_1669;
}
lean_ctor_set(x_1670, 0, x_1667);
lean_ctor_set(x_1670, 1, x_1668);
return x_1670;
}
}
}
else
{
lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; 
lean_inc(x_2);
x_1679 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1679, 0, x_2);
x_1680 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1658, x_1679, x_4, x_5, x_6, x_7, x_8, x_9, x_1634);
x_1681 = lean_ctor_get(x_1680, 1);
lean_inc(x_1681);
lean_dec(x_1680);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1682 = x_1681;
goto block_1693;
}
else
{
lean_object* x_1694; lean_object* x_1695; 
x_1694 = lean_ctor_get(x_13, 0);
lean_inc(x_1694);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1695 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1694, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1681);
if (lean_obj_tag(x_1695) == 0)
{
lean_object* x_1696; 
x_1696 = lean_ctor_get(x_1695, 1);
lean_inc(x_1696);
lean_dec(x_1695);
x_1682 = x_1696;
goto block_1693;
}
else
{
lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; lean_object* x_1700; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1697 = lean_ctor_get(x_1695, 0);
lean_inc(x_1697);
x_1698 = lean_ctor_get(x_1695, 1);
lean_inc(x_1698);
if (lean_is_exclusive(x_1695)) {
 lean_ctor_release(x_1695, 0);
 lean_ctor_release(x_1695, 1);
 x_1699 = x_1695;
} else {
 lean_dec_ref(x_1695);
 x_1699 = lean_box(0);
}
if (lean_is_scalar(x_1699)) {
 x_1700 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1700 = x_1699;
}
lean_ctor_set(x_1700, 0, x_1697);
lean_ctor_set(x_1700, 1, x_1698);
return x_1700;
}
}
block_1693:
{
lean_object* x_1683; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1683 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1682);
lean_dec(x_17);
if (lean_obj_tag(x_1683) == 0)
{
lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; 
x_1684 = lean_ctor_get(x_1683, 1);
lean_inc(x_1684);
lean_dec(x_1683);
lean_inc(x_2);
x_1685 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__19(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1684);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1686 = lean_ctor_get(x_1685, 1);
lean_inc(x_1686);
if (lean_is_exclusive(x_1685)) {
 lean_ctor_release(x_1685, 0);
 lean_ctor_release(x_1685, 1);
 x_1687 = x_1685;
} else {
 lean_dec_ref(x_1685);
 x_1687 = lean_box(0);
}
if (lean_is_scalar(x_1687)) {
 x_1688 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1688 = x_1687;
}
lean_ctor_set(x_1688, 0, x_2);
lean_ctor_set(x_1688, 1, x_1686);
return x_1688;
}
else
{
lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1689 = lean_ctor_get(x_1683, 0);
lean_inc(x_1689);
x_1690 = lean_ctor_get(x_1683, 1);
lean_inc(x_1690);
if (lean_is_exclusive(x_1683)) {
 lean_ctor_release(x_1683, 0);
 lean_ctor_release(x_1683, 1);
 x_1691 = x_1683;
} else {
 lean_dec_ref(x_1683);
 x_1691 = lean_box(0);
}
if (lean_is_scalar(x_1691)) {
 x_1692 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1692 = x_1691;
}
lean_ctor_set(x_1692, 0, x_1689);
lean_ctor_set(x_1692, 1, x_1690);
return x_1692;
}
}
}
}
}
else
{
lean_object* x_1701; 
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_1701 = lean_ctor_get(x_1640, 0);
lean_inc(x_1701);
lean_dec(x_1640);
if (lean_obj_tag(x_1701) == 4)
{
lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; 
x_1702 = lean_ctor_get(x_1701, 0);
lean_inc(x_1702);
lean_dec(x_1701);
x_1703 = lean_st_ref_get(x_9, x_1634);
x_1704 = lean_ctor_get(x_1703, 0);
lean_inc(x_1704);
x_1705 = lean_ctor_get(x_1703, 1);
lean_inc(x_1705);
lean_dec(x_1703);
x_1706 = lean_ctor_get(x_1704, 0);
lean_inc(x_1706);
lean_dec(x_1704);
x_1707 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1706, x_1702);
if (lean_obj_tag(x_1707) == 0)
{
lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; 
lean_dec(x_1636);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_11);
lean_dec(x_2);
x_1708 = lean_ctor_get(x_1707, 0);
lean_inc(x_1708);
lean_dec(x_1707);
x_1709 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1709, 0, x_1708);
x_1710 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1710, 0, x_1709);
x_1711 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1710, x_4, x_5, x_6, x_7, x_8, x_9, x_1705);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1711;
}
else
{
lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; 
x_1712 = lean_ctor_get(x_1707, 0);
lean_inc(x_1712);
lean_dec(x_1707);
x_1713 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_1705);
x_1714 = lean_ctor_get(x_1713, 1);
lean_inc(x_1714);
lean_dec(x_1713);
x_1715 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_1714);
x_1716 = lean_ctor_get(x_1715, 1);
lean_inc(x_1716);
lean_dec(x_1715);
x_1717 = l_Lean_Syntax_getArgs(x_1712);
lean_dec(x_1712);
x_1718 = l_Array_empty___closed__1;
x_1719 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1717, x_1717, x_116, x_1718);
lean_dec(x_1717);
x_1720 = l_Lean_nullKind___closed__2;
x_1721 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1721, 0, x_1720);
lean_ctor_set(x_1721, 1, x_1719);
x_1722 = lean_array_push(x_1718, x_1721);
x_1723 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__17;
x_1724 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1724, 0, x_1723);
lean_ctor_set(x_1724, 1, x_1722);
x_1725 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_1726 = lean_array_push(x_1725, x_1724);
x_1727 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__20;
x_1728 = lean_array_push(x_1726, x_1727);
x_1729 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__19;
x_1730 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1730, 0, x_1729);
lean_ctor_set(x_1730, 1, x_1728);
x_1731 = lean_array_push(x_1718, x_1730);
x_1732 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1732, 0, x_1720);
lean_ctor_set(x_1732, 1, x_1731);
x_1733 = lean_array_push(x_1718, x_1732);
x_1734 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1734, 0, x_1723);
lean_ctor_set(x_1734, 1, x_1733);
x_1735 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1736 = lean_array_push(x_1735, x_1734);
x_1737 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_1738 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1738, 0, x_1737);
lean_ctor_set(x_1738, 1, x_1736);
x_1739 = l_Lean_Syntax_copyInfo(x_1738, x_11);
lean_dec(x_11);
x_1740 = l_Lean_Expr_getAppNumArgsAux___main(x_113, x_116);
x_1741 = lean_nat_sub(x_1740, x_116);
lean_dec(x_1740);
x_1742 = lean_unsigned_to_nat(1u);
x_1743 = lean_nat_sub(x_1741, x_1742);
lean_dec(x_1741);
x_1744 = l_Lean_Expr_getRevArg_x21___main(x_113, x_1743);
lean_dec(x_113);
x_1745 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1745, 0, x_1739);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1746 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1745, x_1744, x_4, x_5, x_6, x_7, x_8, x_9, x_1716);
if (lean_obj_tag(x_1746) == 0)
{
lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; 
x_1747 = lean_ctor_get(x_1746, 0);
lean_inc(x_1747);
x_1748 = lean_ctor_get(x_1746, 1);
lean_inc(x_1748);
lean_dec(x_1746);
lean_inc(x_1747);
x_1749 = l_Lean_mkApp(x_2, x_1747);
x_1750 = lean_expr_instantiate1(x_114, x_1747);
lean_dec(x_1747);
lean_dec(x_114);
x_1 = x_1636;
x_2 = x_1749;
x_3 = x_1750;
x_10 = x_1748;
goto _start;
}
else
{
lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; 
lean_dec(x_1636);
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1752 = lean_ctor_get(x_1746, 0);
lean_inc(x_1752);
x_1753 = lean_ctor_get(x_1746, 1);
lean_inc(x_1753);
if (lean_is_exclusive(x_1746)) {
 lean_ctor_release(x_1746, 0);
 lean_ctor_release(x_1746, 1);
 x_1754 = x_1746;
} else {
 lean_dec_ref(x_1746);
 x_1754 = lean_box(0);
}
if (lean_is_scalar(x_1754)) {
 x_1755 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1755 = x_1754;
}
lean_ctor_set(x_1755, 0, x_1752);
lean_ctor_set(x_1755, 1, x_1753);
return x_1755;
}
}
}
else
{
lean_object* x_1756; lean_object* x_1757; 
lean_dec(x_1701);
lean_dec(x_1636);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_11);
lean_dec(x_2);
x_1756 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1757 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1756, x_4, x_5, x_6, x_7, x_8, x_9, x_1634);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1757;
}
}
}
else
{
lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_1758 = lean_ctor_get(x_1639, 0);
lean_inc(x_1758);
lean_dec(x_1639);
lean_inc(x_1758);
x_1759 = l_Lean_mkApp(x_2, x_1758);
x_1760 = lean_expr_instantiate1(x_114, x_1758);
lean_dec(x_1758);
lean_dec(x_114);
x_1 = x_1636;
x_2 = x_1759;
x_3 = x_1760;
x_10 = x_1634;
goto _start;
}
}
else
{
uint8_t x_1762; 
lean_dec(x_1636);
lean_dec(x_114);
lean_dec(x_113);
x_1762 = l_Array_isEmpty___rarg(x_16);
if (x_1762 == 0)
{
lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; lean_object* x_1778; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_1763 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1763, 0, x_112);
x_1764 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1765 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1765, 0, x_1764);
lean_ctor_set(x_1765, 1, x_1763);
x_1766 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1767 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1767, 0, x_1765);
lean_ctor_set(x_1767, 1, x_1766);
x_1768 = x_16;
x_1769 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_116, x_1768);
x_1770 = x_1769;
x_1771 = l_Array_toList___rarg(x_1770);
lean_dec(x_1770);
x_1772 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_1771);
x_1773 = l_Array_HasRepr___rarg___closed__1;
x_1774 = lean_string_append(x_1773, x_1772);
lean_dec(x_1772);
x_1775 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1775, 0, x_1774);
x_1776 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1776, 0, x_1775);
x_1777 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1777, 0, x_1767);
lean_ctor_set(x_1777, 1, x_1776);
x_1778 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1777, x_4, x_5, x_6, x_7, x_8, x_9, x_1634);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1778;
}
else
{
lean_object* x_1779; uint8_t x_1780; 
lean_dec(x_112);
lean_dec(x_16);
x_1779 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1780 = l_Lean_checkTraceOption(x_22, x_1779);
lean_dec(x_22);
if (x_1780 == 0)
{
lean_object* x_1781; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1781 = x_1634;
goto block_1792;
}
else
{
lean_object* x_1793; lean_object* x_1794; 
x_1793 = lean_ctor_get(x_13, 0);
lean_inc(x_1793);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1794 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1793, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1634);
if (lean_obj_tag(x_1794) == 0)
{
lean_object* x_1795; 
x_1795 = lean_ctor_get(x_1794, 1);
lean_inc(x_1795);
lean_dec(x_1794);
x_1781 = x_1795;
goto block_1792;
}
else
{
lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1796 = lean_ctor_get(x_1794, 0);
lean_inc(x_1796);
x_1797 = lean_ctor_get(x_1794, 1);
lean_inc(x_1797);
if (lean_is_exclusive(x_1794)) {
 lean_ctor_release(x_1794, 0);
 lean_ctor_release(x_1794, 1);
 x_1798 = x_1794;
} else {
 lean_dec_ref(x_1794);
 x_1798 = lean_box(0);
}
if (lean_is_scalar(x_1798)) {
 x_1799 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1799 = x_1798;
}
lean_ctor_set(x_1799, 0, x_1796);
lean_ctor_set(x_1799, 1, x_1797);
return x_1799;
}
}
block_1792:
{
lean_object* x_1782; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1782 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1781);
lean_dec(x_17);
if (lean_obj_tag(x_1782) == 0)
{
lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; 
x_1783 = lean_ctor_get(x_1782, 1);
lean_inc(x_1783);
lean_dec(x_1782);
lean_inc(x_2);
x_1784 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__20(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1783);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1785 = lean_ctor_get(x_1784, 1);
lean_inc(x_1785);
if (lean_is_exclusive(x_1784)) {
 lean_ctor_release(x_1784, 0);
 lean_ctor_release(x_1784, 1);
 x_1786 = x_1784;
} else {
 lean_dec_ref(x_1784);
 x_1786 = lean_box(0);
}
if (lean_is_scalar(x_1786)) {
 x_1787 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1787 = x_1786;
}
lean_ctor_set(x_1787, 0, x_2);
lean_ctor_set(x_1787, 1, x_1785);
return x_1787;
}
else
{
lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1788 = lean_ctor_get(x_1782, 0);
lean_inc(x_1788);
x_1789 = lean_ctor_get(x_1782, 1);
lean_inc(x_1789);
if (lean_is_exclusive(x_1782)) {
 lean_ctor_release(x_1782, 0);
 lean_ctor_release(x_1782, 1);
 x_1790 = x_1782;
} else {
 lean_dec_ref(x_1782);
 x_1790 = lean_box(0);
}
if (lean_is_scalar(x_1790)) {
 x_1791 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1791 = x_1790;
}
lean_ctor_set(x_1791, 0, x_1788);
lean_ctor_set(x_1791, 1, x_1789);
return x_1791;
}
}
}
else
{
lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; 
lean_inc(x_2);
x_1800 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1800, 0, x_2);
x_1801 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1779, x_1800, x_4, x_5, x_6, x_7, x_8, x_9, x_1634);
x_1802 = lean_ctor_get(x_1801, 1);
lean_inc(x_1802);
lean_dec(x_1801);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1803 = x_1802;
goto block_1814;
}
else
{
lean_object* x_1815; lean_object* x_1816; 
x_1815 = lean_ctor_get(x_13, 0);
lean_inc(x_1815);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1816 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1815, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1802);
if (lean_obj_tag(x_1816) == 0)
{
lean_object* x_1817; 
x_1817 = lean_ctor_get(x_1816, 1);
lean_inc(x_1817);
lean_dec(x_1816);
x_1803 = x_1817;
goto block_1814;
}
else
{
lean_object* x_1818; lean_object* x_1819; lean_object* x_1820; lean_object* x_1821; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1818 = lean_ctor_get(x_1816, 0);
lean_inc(x_1818);
x_1819 = lean_ctor_get(x_1816, 1);
lean_inc(x_1819);
if (lean_is_exclusive(x_1816)) {
 lean_ctor_release(x_1816, 0);
 lean_ctor_release(x_1816, 1);
 x_1820 = x_1816;
} else {
 lean_dec_ref(x_1816);
 x_1820 = lean_box(0);
}
if (lean_is_scalar(x_1820)) {
 x_1821 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1821 = x_1820;
}
lean_ctor_set(x_1821, 0, x_1818);
lean_ctor_set(x_1821, 1, x_1819);
return x_1821;
}
}
block_1814:
{
lean_object* x_1804; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1804 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1803);
lean_dec(x_17);
if (lean_obj_tag(x_1804) == 0)
{
lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; 
x_1805 = lean_ctor_get(x_1804, 1);
lean_inc(x_1805);
lean_dec(x_1804);
lean_inc(x_2);
x_1806 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__21(x_2, x_11, x_19, x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_1805);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1807 = lean_ctor_get(x_1806, 1);
lean_inc(x_1807);
if (lean_is_exclusive(x_1806)) {
 lean_ctor_release(x_1806, 0);
 lean_ctor_release(x_1806, 1);
 x_1808 = x_1806;
} else {
 lean_dec_ref(x_1806);
 x_1808 = lean_box(0);
}
if (lean_is_scalar(x_1808)) {
 x_1809 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1809 = x_1808;
}
lean_ctor_set(x_1809, 0, x_2);
lean_ctor_set(x_1809, 1, x_1807);
return x_1809;
}
else
{
lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1810 = lean_ctor_get(x_1804, 0);
lean_inc(x_1810);
x_1811 = lean_ctor_get(x_1804, 1);
lean_inc(x_1811);
if (lean_is_exclusive(x_1804)) {
 lean_ctor_release(x_1804, 0);
 lean_ctor_release(x_1804, 1);
 x_1812 = x_1804;
} else {
 lean_dec_ref(x_1804);
 x_1812 = lean_box(0);
}
if (lean_is_scalar(x_1812)) {
 x_1813 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1813 = x_1812;
}
lean_ctor_set(x_1813, 0, x_1810);
lean_ctor_set(x_1813, 1, x_1811);
return x_1813;
}
}
}
}
}
}
else
{
lean_object* x_1822; lean_object* x_1823; 
lean_dec(x_1636);
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_3);
x_1822 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1823 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1822, x_113, x_4, x_5, x_6, x_7, x_8, x_9, x_1634);
if (lean_obj_tag(x_1823) == 0)
{
lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; 
x_1824 = lean_ctor_get(x_1823, 0);
lean_inc(x_1824);
x_1825 = lean_ctor_get(x_1823, 1);
lean_inc(x_1825);
lean_dec(x_1823);
x_1826 = lean_unsigned_to_nat(1u);
x_1827 = lean_nat_add(x_15, x_1826);
lean_dec(x_15);
x_1828 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1828, 0, x_11);
lean_ctor_set(x_1828, 1, x_12);
lean_ctor_set(x_1828, 2, x_13);
lean_ctor_set(x_1828, 3, x_1827);
lean_ctor_set(x_1828, 4, x_16);
lean_ctor_set(x_1828, 5, x_17);
lean_ctor_set(x_1828, 6, x_18);
lean_ctor_set(x_1828, 7, x_19);
lean_ctor_set_uint8(x_1828, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1828, sizeof(void*)*8 + 1, x_1635);
lean_inc(x_1824);
x_1829 = l_Lean_mkApp(x_2, x_1824);
x_1830 = lean_expr_instantiate1(x_114, x_1824);
lean_dec(x_1824);
lean_dec(x_114);
x_1 = x_1828;
x_2 = x_1829;
x_3 = x_1830;
x_10 = x_1825;
goto _start;
}
else
{
lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; 
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1832 = lean_ctor_get(x_1823, 0);
lean_inc(x_1832);
x_1833 = lean_ctor_get(x_1823, 1);
lean_inc(x_1833);
if (lean_is_exclusive(x_1823)) {
 lean_ctor_release(x_1823, 0);
 lean_ctor_release(x_1823, 1);
 x_1834 = x_1823;
} else {
 lean_dec_ref(x_1823);
 x_1834 = lean_box(0);
}
if (lean_is_scalar(x_1834)) {
 x_1835 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1835 = x_1834;
}
lean_ctor_set(x_1835, 0, x_1832);
lean_ctor_set(x_1835, 1, x_1833);
return x_1835;
}
}
}
else
{
lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_8);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1836 = lean_ctor_get(x_1415, 0);
lean_inc(x_1836);
x_1837 = lean_ctor_get(x_1415, 1);
lean_inc(x_1837);
if (lean_is_exclusive(x_1415)) {
 lean_ctor_release(x_1415, 0);
 lean_ctor_release(x_1415, 1);
 x_1838 = x_1415;
} else {
 lean_dec_ref(x_1415);
 x_1838 = lean_box(0);
}
if (lean_is_scalar(x_1838)) {
 x_1839 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1839 = x_1838;
}
lean_ctor_set(x_1839, 0, x_1836);
lean_ctor_set(x_1839, 1, x_1837);
return x_1839;
}
}
}
}
}
else
{
lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; 
lean_dec(x_112);
lean_dec(x_22);
lean_dec(x_3);
x_1840 = lean_ctor_get(x_117, 0);
lean_inc(x_1840);
lean_dec(x_117);
x_1841 = l_Lean_Elab_Term_NamedArg_inhabited;
x_1842 = lean_array_get(x_1841, x_16, x_1840);
x_1843 = l_Array_eraseIdx___rarg(x_16, x_1840);
lean_dec(x_1840);
x_1844 = lean_ctor_get(x_1842, 1);
lean_inc(x_1844);
lean_dec(x_1842);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1845 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1844, x_113, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_1845) == 0)
{
lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; uint8_t x_1849; 
x_1846 = lean_ctor_get(x_1845, 0);
lean_inc(x_1846);
x_1847 = lean_ctor_get(x_1845, 1);
lean_inc(x_1847);
lean_dec(x_1845);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_1848 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_1847);
x_1849 = !lean_is_exclusive(x_1);
if (x_1849 == 0)
{
lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; 
x_1850 = lean_ctor_get(x_1, 7);
lean_dec(x_1850);
x_1851 = lean_ctor_get(x_1, 6);
lean_dec(x_1851);
x_1852 = lean_ctor_get(x_1, 5);
lean_dec(x_1852);
x_1853 = lean_ctor_get(x_1, 4);
lean_dec(x_1853);
x_1854 = lean_ctor_get(x_1, 3);
lean_dec(x_1854);
x_1855 = lean_ctor_get(x_1, 2);
lean_dec(x_1855);
x_1856 = lean_ctor_get(x_1, 1);
lean_dec(x_1856);
x_1857 = lean_ctor_get(x_1, 0);
lean_dec(x_1857);
if (lean_obj_tag(x_1848) == 0)
{
lean_object* x_1858; uint8_t x_1859; lean_object* x_1860; lean_object* x_1861; 
x_1858 = lean_ctor_get(x_1848, 1);
lean_inc(x_1858);
lean_dec(x_1848);
x_1859 = 1;
lean_ctor_set(x_1, 4, x_1843);
lean_ctor_set_uint8(x_1, sizeof(void*)*8 + 1, x_1859);
lean_inc(x_1846);
x_1860 = l_Lean_mkApp(x_2, x_1846);
x_1861 = lean_expr_instantiate1(x_114, x_1846);
lean_dec(x_1846);
lean_dec(x_114);
x_2 = x_1860;
x_3 = x_1861;
x_10 = x_1858;
goto _start;
}
else
{
uint8_t x_1863; 
lean_free_object(x_1);
lean_dec(x_1846);
lean_dec(x_1843);
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1863 = !lean_is_exclusive(x_1848);
if (x_1863 == 0)
{
return x_1848;
}
else
{
lean_object* x_1864; lean_object* x_1865; lean_object* x_1866; 
x_1864 = lean_ctor_get(x_1848, 0);
x_1865 = lean_ctor_get(x_1848, 1);
lean_inc(x_1865);
lean_inc(x_1864);
lean_dec(x_1848);
x_1866 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1866, 0, x_1864);
lean_ctor_set(x_1866, 1, x_1865);
return x_1866;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_1848) == 0)
{
lean_object* x_1867; uint8_t x_1868; lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; 
x_1867 = lean_ctor_get(x_1848, 1);
lean_inc(x_1867);
lean_dec(x_1848);
x_1868 = 1;
x_1869 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1869, 0, x_11);
lean_ctor_set(x_1869, 1, x_12);
lean_ctor_set(x_1869, 2, x_13);
lean_ctor_set(x_1869, 3, x_15);
lean_ctor_set(x_1869, 4, x_1843);
lean_ctor_set(x_1869, 5, x_17);
lean_ctor_set(x_1869, 6, x_18);
lean_ctor_set(x_1869, 7, x_19);
lean_ctor_set_uint8(x_1869, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1869, sizeof(void*)*8 + 1, x_1868);
lean_inc(x_1846);
x_1870 = l_Lean_mkApp(x_2, x_1846);
x_1871 = lean_expr_instantiate1(x_114, x_1846);
lean_dec(x_1846);
lean_dec(x_114);
x_1 = x_1869;
x_2 = x_1870;
x_3 = x_1871;
x_10 = x_1867;
goto _start;
}
else
{
lean_object* x_1873; lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; 
lean_dec(x_1846);
lean_dec(x_1843);
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1873 = lean_ctor_get(x_1848, 0);
lean_inc(x_1873);
x_1874 = lean_ctor_get(x_1848, 1);
lean_inc(x_1874);
if (lean_is_exclusive(x_1848)) {
 lean_ctor_release(x_1848, 0);
 lean_ctor_release(x_1848, 1);
 x_1875 = x_1848;
} else {
 lean_dec_ref(x_1848);
 x_1875 = lean_box(0);
}
if (lean_is_scalar(x_1875)) {
 x_1876 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1876 = x_1875;
}
lean_ctor_set(x_1876, 0, x_1873);
lean_ctor_set(x_1876, 1, x_1874);
return x_1876;
}
}
}
else
{
uint8_t x_1877; 
lean_dec(x_1843);
lean_dec(x_114);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_1877 = !lean_is_exclusive(x_1845);
if (x_1877 == 0)
{
return x_1845;
}
else
{
lean_object* x_1878; lean_object* x_1879; lean_object* x_1880; 
x_1878 = lean_ctor_get(x_1845, 0);
x_1879 = lean_ctor_get(x_1845, 1);
lean_inc(x_1879);
lean_inc(x_1878);
lean_dec(x_1845);
x_1880 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1880, 0, x_1878);
lean_ctor_set(x_1880, 1, x_1879);
return x_1880;
}
}
}
}
else
{
lean_object* x_1881; 
lean_dec(x_18);
x_1881 = lean_box(0);
x_30 = x_1881;
goto block_111;
}
block_111:
{
uint8_t x_31; 
lean_dec(x_30);
x_31 = l_Array_isEmpty___rarg(x_16);
lean_dec(x_16);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_32 = l___private_Lean_Elab_App_4__tryCoeFun(x_28, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_33);
x_35 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_2 = x_33;
x_3 = x_36;
x_10 = x_37;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_33);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
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
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_32);
if (x_43 == 0)
{
return x_32;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_32, 0);
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_32);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_array_get_size(x_12);
lean_dec(x_12);
x_48 = lean_nat_dec_eq(x_15, x_47);
lean_dec(x_47);
lean_dec(x_15);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_49 = l___private_Lean_Elab_App_4__tryCoeFun(x_28, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_50);
x_52 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_50, x_4, x_5, x_6, x_7, x_8, x_9, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_2 = x_50;
x_3 = x_53;
x_10 = x_54;
goto _start;
}
else
{
uint8_t x_56; 
lean_dec(x_50);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_52);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_49);
if (x_60 == 0)
{
return x_49;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_49, 0);
x_62 = lean_ctor_get(x_49, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_49);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_28);
lean_dec(x_1);
x_64 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_65 = l_Lean_checkTraceOption(x_22, x_64);
lean_dec(x_22);
if (x_65 == 0)
{
lean_object* x_66; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_66 = x_29;
goto block_79;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_13, 0);
lean_inc(x_80);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_81 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_80, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_66 = x_82;
goto block_79;
}
else
{
uint8_t x_83; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
return x_81;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_81, 0);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_81);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
block_79:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_68 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_67, x_4, x_5, x_6, x_7, x_8, x_9, x_66);
lean_dec(x_17);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
lean_inc(x_2);
x_70 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(x_2, x_11, x_19, x_67, x_4, x_5, x_6, x_7, x_8, x_9, x_69);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
lean_ctor_set(x_70, 0, x_2);
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_2);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_68);
if (x_75 == 0)
{
return x_68;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_68, 0);
x_77 = lean_ctor_get(x_68, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_68);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_inc(x_2);
x_87 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_87, 0, x_2);
x_88 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_64, x_87, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_90 = x_89;
goto block_103;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_13, 0);
lean_inc(x_104);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_105 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_104, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_89);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_90 = x_106;
goto block_103;
}
else
{
uint8_t x_107; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_107 = !lean_is_exclusive(x_105);
if (x_107 == 0)
{
return x_105;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_105, 0);
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_105);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
block_103:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_92 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_91, x_4, x_5, x_6, x_7, x_8, x_9, x_90);
lean_dec(x_17);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
lean_inc(x_2);
x_94 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_2, x_11, x_19, x_91, x_4, x_5, x_6, x_7, x_8, x_9, x_93);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
lean_ctor_set(x_94, 0, x_2);
return x_94;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_2);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_92);
if (x_99 == 0)
{
return x_92;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_92, 0);
x_101 = lean_ctor_get(x_92, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_92);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
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
uint8_t x_1882; 
lean_dec(x_8);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1882 = !lean_is_exclusive(x_27);
if (x_1882 == 0)
{
return x_27;
}
else
{
lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; 
x_1883 = lean_ctor_get(x_27, 0);
x_1884 = lean_ctor_get(x_27, 1);
lean_inc(x_1884);
lean_inc(x_1883);
lean_dec(x_27);
x_1885 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1885, 0, x_1883);
lean_ctor_set(x_1885, 1, x_1884);
return x_1885;
}
}
}
else
{
uint8_t x_1886; lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; 
x_1886 = lean_ctor_get_uint8(x_1, sizeof(void*)*8 + 1);
x_1887 = lean_ctor_get(x_8, 0);
x_1888 = lean_ctor_get(x_8, 1);
x_1889 = lean_ctor_get(x_8, 2);
x_1890 = lean_ctor_get(x_8, 3);
lean_inc(x_1890);
lean_inc(x_1889);
lean_inc(x_1888);
lean_inc(x_1887);
lean_dec(x_8);
x_1891 = l_Lean_replaceRef(x_11, x_1890);
x_1892 = l_Lean_replaceRef(x_1891, x_1890);
lean_dec(x_1891);
x_1893 = l_Lean_replaceRef(x_1892, x_1890);
lean_dec(x_1890);
lean_dec(x_1892);
lean_inc(x_1887);
x_1894 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1894, 0, x_1887);
lean_ctor_set(x_1894, 1, x_1888);
lean_ctor_set(x_1894, 2, x_1889);
lean_ctor_set(x_1894, 3, x_1893);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_1895 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_18__useImplicitLambda_x3f___spec__1(x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_10);
if (lean_obj_tag(x_1895) == 0)
{
lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; 
x_1896 = lean_ctor_get(x_1895, 0);
lean_inc(x_1896);
x_1897 = lean_ctor_get(x_1895, 1);
lean_inc(x_1897);
lean_dec(x_1895);
if (lean_obj_tag(x_1896) == 7)
{
lean_object* x_1978; lean_object* x_1979; lean_object* x_1980; uint64_t x_1981; lean_object* x_1982; lean_object* x_1983; 
x_1978 = lean_ctor_get(x_1896, 0);
lean_inc(x_1978);
x_1979 = lean_ctor_get(x_1896, 1);
lean_inc(x_1979);
x_1980 = lean_ctor_get(x_1896, 2);
lean_inc(x_1980);
x_1981 = lean_ctor_get_uint64(x_1896, sizeof(void*)*3);
x_1982 = lean_unsigned_to_nat(0u);
x_1983 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__3(x_1978, x_16, x_1982);
if (lean_obj_tag(x_1983) == 0)
{
uint8_t x_1984; 
x_1984 = (uint8_t)((x_1981 << 24) >> 61);
switch (x_1984) {
case 0:
{
lean_object* x_1985; lean_object* x_1986; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_1985 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1896, x_4, x_5, x_6, x_7, x_1894, x_9, x_1897);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_1986 = x_1;
} else {
 lean_dec_ref(x_1);
 x_1986 = lean_box(0);
}
if (lean_obj_tag(x_1985) == 0)
{
lean_object* x_1987; uint8_t x_1988; lean_object* x_1989; lean_object* x_1990; uint8_t x_1991; 
x_1987 = lean_ctor_get(x_1985, 1);
lean_inc(x_1987);
lean_dec(x_1985);
x_1988 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
if (lean_is_scalar(x_1986)) {
 x_1989 = lean_alloc_ctor(0, 8, 2);
} else {
 x_1989 = x_1986;
}
lean_ctor_set(x_1989, 0, x_11);
lean_ctor_set(x_1989, 1, x_12);
lean_ctor_set(x_1989, 2, x_13);
lean_ctor_set(x_1989, 3, x_15);
lean_ctor_set(x_1989, 4, x_16);
lean_ctor_set(x_1989, 5, x_17);
lean_ctor_set(x_1989, 6, x_18);
lean_ctor_set(x_1989, 7, x_19);
lean_ctor_set_uint8(x_1989, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1989, sizeof(void*)*8 + 1, x_1988);
x_1990 = lean_array_get_size(x_12);
x_1991 = lean_nat_dec_lt(x_15, x_1990);
lean_dec(x_1990);
if (x_1991 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_1992; 
x_1992 = l_Lean_Expr_getOptParamDefault_x3f(x_1979);
if (lean_obj_tag(x_1992) == 0)
{
lean_object* x_1993; 
x_1993 = l_Lean_Expr_getAutoParamTactic_x3f(x_1979);
if (lean_obj_tag(x_1993) == 0)
{
uint8_t x_1994; 
lean_dec(x_1989);
lean_dec(x_1980);
lean_dec(x_1979);
x_1994 = l_Array_isEmpty___rarg(x_16);
if (x_1994 == 0)
{
lean_object* x_1995; lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; lean_object* x_2004; lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; 
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_1995 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1995, 0, x_1978);
x_1996 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1997 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1997, 0, x_1996);
lean_ctor_set(x_1997, 1, x_1995);
x_1998 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1999 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1999, 0, x_1997);
lean_ctor_set(x_1999, 1, x_1998);
x_2000 = x_16;
x_2001 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_1982, x_2000);
x_2002 = x_2001;
x_2003 = l_Array_toList___rarg(x_2002);
lean_dec(x_2002);
x_2004 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_2003);
x_2005 = l_Array_HasRepr___rarg___closed__1;
x_2006 = lean_string_append(x_2005, x_2004);
lean_dec(x_2004);
x_2007 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2007, 0, x_2006);
x_2008 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2008, 0, x_2007);
x_2009 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2009, 0, x_1999);
lean_ctor_set(x_2009, 1, x_2008);
x_2010 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2009, x_4, x_5, x_6, x_7, x_1894, x_9, x_1987);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2010;
}
else
{
lean_object* x_2011; uint8_t x_2012; 
lean_dec(x_1978);
lean_dec(x_16);
x_2011 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2012 = l_Lean_checkTraceOption(x_1887, x_2011);
lean_dec(x_1887);
if (x_2012 == 0)
{
lean_object* x_2013; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2013 = x_1987;
goto block_2024;
}
else
{
lean_object* x_2025; lean_object* x_2026; 
x_2025 = lean_ctor_get(x_13, 0);
lean_inc(x_2025);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2026 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2025, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_1987);
if (lean_obj_tag(x_2026) == 0)
{
lean_object* x_2027; 
x_2027 = lean_ctor_get(x_2026, 1);
lean_inc(x_2027);
lean_dec(x_2026);
x_2013 = x_2027;
goto block_2024;
}
else
{
lean_object* x_2028; lean_object* x_2029; lean_object* x_2030; lean_object* x_2031; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2028 = lean_ctor_get(x_2026, 0);
lean_inc(x_2028);
x_2029 = lean_ctor_get(x_2026, 1);
lean_inc(x_2029);
if (lean_is_exclusive(x_2026)) {
 lean_ctor_release(x_2026, 0);
 lean_ctor_release(x_2026, 1);
 x_2030 = x_2026;
} else {
 lean_dec_ref(x_2026);
 x_2030 = lean_box(0);
}
if (lean_is_scalar(x_2030)) {
 x_2031 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2031 = x_2030;
}
lean_ctor_set(x_2031, 0, x_2028);
lean_ctor_set(x_2031, 1, x_2029);
return x_2031;
}
}
block_2024:
{
lean_object* x_2014; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2014 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2013);
lean_dec(x_17);
if (lean_obj_tag(x_2014) == 0)
{
lean_object* x_2015; lean_object* x_2016; lean_object* x_2017; lean_object* x_2018; lean_object* x_2019; 
x_2015 = lean_ctor_get(x_2014, 1);
lean_inc(x_2015);
lean_dec(x_2014);
lean_inc(x_2);
x_2016 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__5(x_2, x_11, x_19, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2015);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2017 = lean_ctor_get(x_2016, 1);
lean_inc(x_2017);
if (lean_is_exclusive(x_2016)) {
 lean_ctor_release(x_2016, 0);
 lean_ctor_release(x_2016, 1);
 x_2018 = x_2016;
} else {
 lean_dec_ref(x_2016);
 x_2018 = lean_box(0);
}
if (lean_is_scalar(x_2018)) {
 x_2019 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2019 = x_2018;
}
lean_ctor_set(x_2019, 0, x_2);
lean_ctor_set(x_2019, 1, x_2017);
return x_2019;
}
else
{
lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; lean_object* x_2023; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2020 = lean_ctor_get(x_2014, 0);
lean_inc(x_2020);
x_2021 = lean_ctor_get(x_2014, 1);
lean_inc(x_2021);
if (lean_is_exclusive(x_2014)) {
 lean_ctor_release(x_2014, 0);
 lean_ctor_release(x_2014, 1);
 x_2022 = x_2014;
} else {
 lean_dec_ref(x_2014);
 x_2022 = lean_box(0);
}
if (lean_is_scalar(x_2022)) {
 x_2023 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2023 = x_2022;
}
lean_ctor_set(x_2023, 0, x_2020);
lean_ctor_set(x_2023, 1, x_2021);
return x_2023;
}
}
}
else
{
lean_object* x_2032; lean_object* x_2033; lean_object* x_2034; lean_object* x_2035; 
lean_inc(x_2);
x_2032 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2032, 0, x_2);
x_2033 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2011, x_2032, x_4, x_5, x_6, x_7, x_1894, x_9, x_1987);
x_2034 = lean_ctor_get(x_2033, 1);
lean_inc(x_2034);
lean_dec(x_2033);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2035 = x_2034;
goto block_2046;
}
else
{
lean_object* x_2047; lean_object* x_2048; 
x_2047 = lean_ctor_get(x_13, 0);
lean_inc(x_2047);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2048 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2047, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_2034);
if (lean_obj_tag(x_2048) == 0)
{
lean_object* x_2049; 
x_2049 = lean_ctor_get(x_2048, 1);
lean_inc(x_2049);
lean_dec(x_2048);
x_2035 = x_2049;
goto block_2046;
}
else
{
lean_object* x_2050; lean_object* x_2051; lean_object* x_2052; lean_object* x_2053; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2050 = lean_ctor_get(x_2048, 0);
lean_inc(x_2050);
x_2051 = lean_ctor_get(x_2048, 1);
lean_inc(x_2051);
if (lean_is_exclusive(x_2048)) {
 lean_ctor_release(x_2048, 0);
 lean_ctor_release(x_2048, 1);
 x_2052 = x_2048;
} else {
 lean_dec_ref(x_2048);
 x_2052 = lean_box(0);
}
if (lean_is_scalar(x_2052)) {
 x_2053 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2053 = x_2052;
}
lean_ctor_set(x_2053, 0, x_2050);
lean_ctor_set(x_2053, 1, x_2051);
return x_2053;
}
}
block_2046:
{
lean_object* x_2036; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2036 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2035);
lean_dec(x_17);
if (lean_obj_tag(x_2036) == 0)
{
lean_object* x_2037; lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; lean_object* x_2041; 
x_2037 = lean_ctor_get(x_2036, 1);
lean_inc(x_2037);
lean_dec(x_2036);
lean_inc(x_2);
x_2038 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__6(x_2, x_11, x_19, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2037);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2039 = lean_ctor_get(x_2038, 1);
lean_inc(x_2039);
if (lean_is_exclusive(x_2038)) {
 lean_ctor_release(x_2038, 0);
 lean_ctor_release(x_2038, 1);
 x_2040 = x_2038;
} else {
 lean_dec_ref(x_2038);
 x_2040 = lean_box(0);
}
if (lean_is_scalar(x_2040)) {
 x_2041 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2041 = x_2040;
}
lean_ctor_set(x_2041, 0, x_2);
lean_ctor_set(x_2041, 1, x_2039);
return x_2041;
}
else
{
lean_object* x_2042; lean_object* x_2043; lean_object* x_2044; lean_object* x_2045; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2042 = lean_ctor_get(x_2036, 0);
lean_inc(x_2042);
x_2043 = lean_ctor_get(x_2036, 1);
lean_inc(x_2043);
if (lean_is_exclusive(x_2036)) {
 lean_ctor_release(x_2036, 0);
 lean_ctor_release(x_2036, 1);
 x_2044 = x_2036;
} else {
 lean_dec_ref(x_2036);
 x_2044 = lean_box(0);
}
if (lean_is_scalar(x_2044)) {
 x_2045 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2045 = x_2044;
}
lean_ctor_set(x_2045, 0, x_2042);
lean_ctor_set(x_2045, 1, x_2043);
return x_2045;
}
}
}
}
}
else
{
lean_object* x_2054; 
lean_dec(x_1978);
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_2054 = lean_ctor_get(x_1993, 0);
lean_inc(x_2054);
lean_dec(x_1993);
if (lean_obj_tag(x_2054) == 4)
{
lean_object* x_2055; lean_object* x_2056; lean_object* x_2057; lean_object* x_2058; lean_object* x_2059; lean_object* x_2060; 
x_2055 = lean_ctor_get(x_2054, 0);
lean_inc(x_2055);
lean_dec(x_2054);
x_2056 = lean_st_ref_get(x_9, x_1987);
x_2057 = lean_ctor_get(x_2056, 0);
lean_inc(x_2057);
x_2058 = lean_ctor_get(x_2056, 1);
lean_inc(x_2058);
lean_dec(x_2056);
x_2059 = lean_ctor_get(x_2057, 0);
lean_inc(x_2059);
lean_dec(x_2057);
x_2060 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_2059, x_2055);
if (lean_obj_tag(x_2060) == 0)
{
lean_object* x_2061; lean_object* x_2062; lean_object* x_2063; lean_object* x_2064; 
lean_dec(x_1989);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_11);
lean_dec(x_2);
x_2061 = lean_ctor_get(x_2060, 0);
lean_inc(x_2061);
lean_dec(x_2060);
x_2062 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2062, 0, x_2061);
x_2063 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2063, 0, x_2062);
x_2064 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2063, x_4, x_5, x_6, x_7, x_1894, x_9, x_2058);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2064;
}
else
{
lean_object* x_2065; lean_object* x_2066; lean_object* x_2067; lean_object* x_2068; lean_object* x_2069; lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; lean_object* x_2083; lean_object* x_2084; lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; 
x_2065 = lean_ctor_get(x_2060, 0);
lean_inc(x_2065);
lean_dec(x_2060);
x_2066 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_1894, x_9, x_2058);
x_2067 = lean_ctor_get(x_2066, 1);
lean_inc(x_2067);
lean_dec(x_2066);
x_2068 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_2067);
x_2069 = lean_ctor_get(x_2068, 1);
lean_inc(x_2069);
lean_dec(x_2068);
x_2070 = l_Lean_Syntax_getArgs(x_2065);
lean_dec(x_2065);
x_2071 = l_Array_empty___closed__1;
x_2072 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2070, x_2070, x_1982, x_2071);
lean_dec(x_2070);
x_2073 = l_Lean_nullKind___closed__2;
x_2074 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2074, 0, x_2073);
lean_ctor_set(x_2074, 1, x_2072);
x_2075 = lean_array_push(x_2071, x_2074);
x_2076 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__17;
x_2077 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2077, 0, x_2076);
lean_ctor_set(x_2077, 1, x_2075);
x_2078 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_2079 = lean_array_push(x_2078, x_2077);
x_2080 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__20;
x_2081 = lean_array_push(x_2079, x_2080);
x_2082 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__19;
x_2083 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2083, 0, x_2082);
lean_ctor_set(x_2083, 1, x_2081);
x_2084 = lean_array_push(x_2071, x_2083);
x_2085 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2085, 0, x_2073);
lean_ctor_set(x_2085, 1, x_2084);
x_2086 = lean_array_push(x_2071, x_2085);
x_2087 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2087, 0, x_2076);
lean_ctor_set(x_2087, 1, x_2086);
x_2088 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_2089 = lean_array_push(x_2088, x_2087);
x_2090 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_2091 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2091, 0, x_2090);
lean_ctor_set(x_2091, 1, x_2089);
x_2092 = l_Lean_Syntax_copyInfo(x_2091, x_11);
lean_dec(x_11);
x_2093 = l_Lean_Expr_getAppNumArgsAux___main(x_1979, x_1982);
x_2094 = lean_nat_sub(x_2093, x_1982);
lean_dec(x_2093);
x_2095 = lean_unsigned_to_nat(1u);
x_2096 = lean_nat_sub(x_2094, x_2095);
lean_dec(x_2094);
x_2097 = l_Lean_Expr_getRevArg_x21___main(x_1979, x_2096);
lean_dec(x_1979);
x_2098 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2098, 0, x_2092);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2099 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2098, x_2097, x_4, x_5, x_6, x_7, x_1894, x_9, x_2069);
if (lean_obj_tag(x_2099) == 0)
{
lean_object* x_2100; lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; 
x_2100 = lean_ctor_get(x_2099, 0);
lean_inc(x_2100);
x_2101 = lean_ctor_get(x_2099, 1);
lean_inc(x_2101);
lean_dec(x_2099);
lean_inc(x_2100);
x_2102 = l_Lean_mkApp(x_2, x_2100);
x_2103 = lean_expr_instantiate1(x_1980, x_2100);
lean_dec(x_2100);
lean_dec(x_1980);
x_1 = x_1989;
x_2 = x_2102;
x_3 = x_2103;
x_8 = x_1894;
x_10 = x_2101;
goto _start;
}
else
{
lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; 
lean_dec(x_1989);
lean_dec(x_1980);
lean_dec(x_1894);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2105 = lean_ctor_get(x_2099, 0);
lean_inc(x_2105);
x_2106 = lean_ctor_get(x_2099, 1);
lean_inc(x_2106);
if (lean_is_exclusive(x_2099)) {
 lean_ctor_release(x_2099, 0);
 lean_ctor_release(x_2099, 1);
 x_2107 = x_2099;
} else {
 lean_dec_ref(x_2099);
 x_2107 = lean_box(0);
}
if (lean_is_scalar(x_2107)) {
 x_2108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2108 = x_2107;
}
lean_ctor_set(x_2108, 0, x_2105);
lean_ctor_set(x_2108, 1, x_2106);
return x_2108;
}
}
}
else
{
lean_object* x_2109; lean_object* x_2110; 
lean_dec(x_2054);
lean_dec(x_1989);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_11);
lean_dec(x_2);
x_2109 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_2110 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2109, x_4, x_5, x_6, x_7, x_1894, x_9, x_1987);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2110;
}
}
}
else
{
lean_object* x_2111; lean_object* x_2112; lean_object* x_2113; 
lean_dec(x_1979);
lean_dec(x_1978);
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_2111 = lean_ctor_get(x_1992, 0);
lean_inc(x_2111);
lean_dec(x_1992);
lean_inc(x_2111);
x_2112 = l_Lean_mkApp(x_2, x_2111);
x_2113 = lean_expr_instantiate1(x_1980, x_2111);
lean_dec(x_2111);
lean_dec(x_1980);
x_1 = x_1989;
x_2 = x_2112;
x_3 = x_2113;
x_8 = x_1894;
x_10 = x_1987;
goto _start;
}
}
else
{
uint8_t x_2115; 
lean_dec(x_1989);
lean_dec(x_1980);
lean_dec(x_1979);
x_2115 = l_Array_isEmpty___rarg(x_16);
if (x_2115 == 0)
{
lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; lean_object* x_2130; lean_object* x_2131; 
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_2116 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2116, 0, x_1978);
x_2117 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_2118 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2118, 0, x_2117);
lean_ctor_set(x_2118, 1, x_2116);
x_2119 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_2120 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2120, 0, x_2118);
lean_ctor_set(x_2120, 1, x_2119);
x_2121 = x_16;
x_2122 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_1982, x_2121);
x_2123 = x_2122;
x_2124 = l_Array_toList___rarg(x_2123);
lean_dec(x_2123);
x_2125 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_2124);
x_2126 = l_Array_HasRepr___rarg___closed__1;
x_2127 = lean_string_append(x_2126, x_2125);
lean_dec(x_2125);
x_2128 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2128, 0, x_2127);
x_2129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2129, 0, x_2128);
x_2130 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2130, 0, x_2120);
lean_ctor_set(x_2130, 1, x_2129);
x_2131 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2130, x_4, x_5, x_6, x_7, x_1894, x_9, x_1987);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2131;
}
else
{
lean_object* x_2132; uint8_t x_2133; 
lean_dec(x_1978);
lean_dec(x_16);
x_2132 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2133 = l_Lean_checkTraceOption(x_1887, x_2132);
lean_dec(x_1887);
if (x_2133 == 0)
{
lean_object* x_2134; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2134 = x_1987;
goto block_2145;
}
else
{
lean_object* x_2146; lean_object* x_2147; 
x_2146 = lean_ctor_get(x_13, 0);
lean_inc(x_2146);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2147 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2146, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_1987);
if (lean_obj_tag(x_2147) == 0)
{
lean_object* x_2148; 
x_2148 = lean_ctor_get(x_2147, 1);
lean_inc(x_2148);
lean_dec(x_2147);
x_2134 = x_2148;
goto block_2145;
}
else
{
lean_object* x_2149; lean_object* x_2150; lean_object* x_2151; lean_object* x_2152; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2149 = lean_ctor_get(x_2147, 0);
lean_inc(x_2149);
x_2150 = lean_ctor_get(x_2147, 1);
lean_inc(x_2150);
if (lean_is_exclusive(x_2147)) {
 lean_ctor_release(x_2147, 0);
 lean_ctor_release(x_2147, 1);
 x_2151 = x_2147;
} else {
 lean_dec_ref(x_2147);
 x_2151 = lean_box(0);
}
if (lean_is_scalar(x_2151)) {
 x_2152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2152 = x_2151;
}
lean_ctor_set(x_2152, 0, x_2149);
lean_ctor_set(x_2152, 1, x_2150);
return x_2152;
}
}
block_2145:
{
lean_object* x_2135; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2135 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2134);
lean_dec(x_17);
if (lean_obj_tag(x_2135) == 0)
{
lean_object* x_2136; lean_object* x_2137; lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; 
x_2136 = lean_ctor_get(x_2135, 1);
lean_inc(x_2136);
lean_dec(x_2135);
lean_inc(x_2);
x_2137 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__7(x_2, x_11, x_19, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2136);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2138 = lean_ctor_get(x_2137, 1);
lean_inc(x_2138);
if (lean_is_exclusive(x_2137)) {
 lean_ctor_release(x_2137, 0);
 lean_ctor_release(x_2137, 1);
 x_2139 = x_2137;
} else {
 lean_dec_ref(x_2137);
 x_2139 = lean_box(0);
}
if (lean_is_scalar(x_2139)) {
 x_2140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2140 = x_2139;
}
lean_ctor_set(x_2140, 0, x_2);
lean_ctor_set(x_2140, 1, x_2138);
return x_2140;
}
else
{
lean_object* x_2141; lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2141 = lean_ctor_get(x_2135, 0);
lean_inc(x_2141);
x_2142 = lean_ctor_get(x_2135, 1);
lean_inc(x_2142);
if (lean_is_exclusive(x_2135)) {
 lean_ctor_release(x_2135, 0);
 lean_ctor_release(x_2135, 1);
 x_2143 = x_2135;
} else {
 lean_dec_ref(x_2135);
 x_2143 = lean_box(0);
}
if (lean_is_scalar(x_2143)) {
 x_2144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2144 = x_2143;
}
lean_ctor_set(x_2144, 0, x_2141);
lean_ctor_set(x_2144, 1, x_2142);
return x_2144;
}
}
}
else
{
lean_object* x_2153; lean_object* x_2154; lean_object* x_2155; lean_object* x_2156; 
lean_inc(x_2);
x_2153 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2153, 0, x_2);
x_2154 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2132, x_2153, x_4, x_5, x_6, x_7, x_1894, x_9, x_1987);
x_2155 = lean_ctor_get(x_2154, 1);
lean_inc(x_2155);
lean_dec(x_2154);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2156 = x_2155;
goto block_2167;
}
else
{
lean_object* x_2168; lean_object* x_2169; 
x_2168 = lean_ctor_get(x_13, 0);
lean_inc(x_2168);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2169 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2168, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_2155);
if (lean_obj_tag(x_2169) == 0)
{
lean_object* x_2170; 
x_2170 = lean_ctor_get(x_2169, 1);
lean_inc(x_2170);
lean_dec(x_2169);
x_2156 = x_2170;
goto block_2167;
}
else
{
lean_object* x_2171; lean_object* x_2172; lean_object* x_2173; lean_object* x_2174; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2171 = lean_ctor_get(x_2169, 0);
lean_inc(x_2171);
x_2172 = lean_ctor_get(x_2169, 1);
lean_inc(x_2172);
if (lean_is_exclusive(x_2169)) {
 lean_ctor_release(x_2169, 0);
 lean_ctor_release(x_2169, 1);
 x_2173 = x_2169;
} else {
 lean_dec_ref(x_2169);
 x_2173 = lean_box(0);
}
if (lean_is_scalar(x_2173)) {
 x_2174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2174 = x_2173;
}
lean_ctor_set(x_2174, 0, x_2171);
lean_ctor_set(x_2174, 1, x_2172);
return x_2174;
}
}
block_2167:
{
lean_object* x_2157; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2157 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2156);
lean_dec(x_17);
if (lean_obj_tag(x_2157) == 0)
{
lean_object* x_2158; lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; lean_object* x_2162; 
x_2158 = lean_ctor_get(x_2157, 1);
lean_inc(x_2158);
lean_dec(x_2157);
lean_inc(x_2);
x_2159 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__8(x_2, x_11, x_19, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2158);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2160 = lean_ctor_get(x_2159, 1);
lean_inc(x_2160);
if (lean_is_exclusive(x_2159)) {
 lean_ctor_release(x_2159, 0);
 lean_ctor_release(x_2159, 1);
 x_2161 = x_2159;
} else {
 lean_dec_ref(x_2159);
 x_2161 = lean_box(0);
}
if (lean_is_scalar(x_2161)) {
 x_2162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2162 = x_2161;
}
lean_ctor_set(x_2162, 0, x_2);
lean_ctor_set(x_2162, 1, x_2160);
return x_2162;
}
else
{
lean_object* x_2163; lean_object* x_2164; lean_object* x_2165; lean_object* x_2166; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2163 = lean_ctor_get(x_2157, 0);
lean_inc(x_2163);
x_2164 = lean_ctor_get(x_2157, 1);
lean_inc(x_2164);
if (lean_is_exclusive(x_2157)) {
 lean_ctor_release(x_2157, 0);
 lean_ctor_release(x_2157, 1);
 x_2165 = x_2157;
} else {
 lean_dec_ref(x_2157);
 x_2165 = lean_box(0);
}
if (lean_is_scalar(x_2165)) {
 x_2166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2166 = x_2165;
}
lean_ctor_set(x_2166, 0, x_2163);
lean_ctor_set(x_2166, 1, x_2164);
return x_2166;
}
}
}
}
}
}
else
{
lean_object* x_2175; lean_object* x_2176; 
lean_dec(x_1989);
lean_dec(x_1978);
lean_dec(x_1887);
lean_dec(x_3);
x_2175 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2176 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2175, x_1979, x_4, x_5, x_6, x_7, x_1894, x_9, x_1987);
if (lean_obj_tag(x_2176) == 0)
{
lean_object* x_2177; lean_object* x_2178; lean_object* x_2179; lean_object* x_2180; lean_object* x_2181; lean_object* x_2182; lean_object* x_2183; 
x_2177 = lean_ctor_get(x_2176, 0);
lean_inc(x_2177);
x_2178 = lean_ctor_get(x_2176, 1);
lean_inc(x_2178);
lean_dec(x_2176);
x_2179 = lean_unsigned_to_nat(1u);
x_2180 = lean_nat_add(x_15, x_2179);
lean_dec(x_15);
x_2181 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_2181, 0, x_11);
lean_ctor_set(x_2181, 1, x_12);
lean_ctor_set(x_2181, 2, x_13);
lean_ctor_set(x_2181, 3, x_2180);
lean_ctor_set(x_2181, 4, x_16);
lean_ctor_set(x_2181, 5, x_17);
lean_ctor_set(x_2181, 6, x_18);
lean_ctor_set(x_2181, 7, x_19);
lean_ctor_set_uint8(x_2181, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2181, sizeof(void*)*8 + 1, x_1988);
lean_inc(x_2177);
x_2182 = l_Lean_mkApp(x_2, x_2177);
x_2183 = lean_expr_instantiate1(x_1980, x_2177);
lean_dec(x_2177);
lean_dec(x_1980);
x_1 = x_2181;
x_2 = x_2182;
x_3 = x_2183;
x_8 = x_1894;
x_10 = x_2178;
goto _start;
}
else
{
lean_object* x_2185; lean_object* x_2186; lean_object* x_2187; lean_object* x_2188; 
lean_dec(x_1980);
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2185 = lean_ctor_get(x_2176, 0);
lean_inc(x_2185);
x_2186 = lean_ctor_get(x_2176, 1);
lean_inc(x_2186);
if (lean_is_exclusive(x_2176)) {
 lean_ctor_release(x_2176, 0);
 lean_ctor_release(x_2176, 1);
 x_2187 = x_2176;
} else {
 lean_dec_ref(x_2176);
 x_2187 = lean_box(0);
}
if (lean_is_scalar(x_2187)) {
 x_2188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2188 = x_2187;
}
lean_ctor_set(x_2188, 0, x_2185);
lean_ctor_set(x_2188, 1, x_2186);
return x_2188;
}
}
}
else
{
lean_object* x_2189; lean_object* x_2190; lean_object* x_2191; lean_object* x_2192; 
lean_dec(x_1986);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_1978);
lean_dec(x_1894);
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2189 = lean_ctor_get(x_1985, 0);
lean_inc(x_2189);
x_2190 = lean_ctor_get(x_1985, 1);
lean_inc(x_2190);
if (lean_is_exclusive(x_1985)) {
 lean_ctor_release(x_1985, 0);
 lean_ctor_release(x_1985, 1);
 x_2191 = x_1985;
} else {
 lean_dec_ref(x_1985);
 x_2191 = lean_box(0);
}
if (lean_is_scalar(x_2191)) {
 x_2192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2192 = x_2191;
}
lean_ctor_set(x_2192, 0, x_2189);
lean_ctor_set(x_2192, 1, x_2190);
return x_2192;
}
}
case 1:
{
if (x_14 == 0)
{
lean_object* x_2193; lean_object* x_2194; uint8_t x_2195; lean_object* x_2196; lean_object* x_2197; lean_object* x_2198; lean_object* x_2199; lean_object* x_2200; lean_object* x_2201; lean_object* x_2209; 
lean_dec(x_1978);
lean_dec(x_1896);
lean_dec(x_1887);
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_2193 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2193 = lean_box(0);
}
x_2194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2194, 0, x_1979);
x_2195 = 0;
x_2196 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_2197 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_2194, x_2195, x_2196, x_4, x_5, x_6, x_7, x_1894, x_9, x_1897);
x_2198 = lean_ctor_get(x_2197, 0);
lean_inc(x_2198);
x_2199 = lean_ctor_get(x_2197, 1);
lean_inc(x_2199);
lean_dec(x_2197);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2198);
x_2209 = l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__9(x_2198, x_4, x_5, x_6, x_7, x_1894, x_9, x_2199);
if (lean_obj_tag(x_2209) == 0)
{
lean_object* x_2210; uint8_t x_2211; 
x_2210 = lean_ctor_get(x_2209, 0);
lean_inc(x_2210);
x_2211 = lean_unbox(x_2210);
lean_dec(x_2210);
if (x_2211 == 0)
{
lean_object* x_2212; 
x_2212 = lean_ctor_get(x_2209, 1);
lean_inc(x_2212);
lean_dec(x_2209);
x_2200 = x_18;
x_2201 = x_2212;
goto block_2208;
}
else
{
lean_object* x_2213; lean_object* x_2214; lean_object* x_2215; 
x_2213 = lean_ctor_get(x_2209, 1);
lean_inc(x_2213);
lean_dec(x_2209);
x_2214 = l_Lean_Expr_mvarId_x21(x_2198);
x_2215 = lean_array_push(x_18, x_2214);
x_2200 = x_2215;
x_2201 = x_2213;
goto block_2208;
}
}
else
{
lean_object* x_2216; lean_object* x_2217; lean_object* x_2218; lean_object* x_2219; 
lean_dec(x_2198);
lean_dec(x_2193);
lean_dec(x_1980);
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2216 = lean_ctor_get(x_2209, 0);
lean_inc(x_2216);
x_2217 = lean_ctor_get(x_2209, 1);
lean_inc(x_2217);
if (lean_is_exclusive(x_2209)) {
 lean_ctor_release(x_2209, 0);
 lean_ctor_release(x_2209, 1);
 x_2218 = x_2209;
} else {
 lean_dec_ref(x_2209);
 x_2218 = lean_box(0);
}
if (lean_is_scalar(x_2218)) {
 x_2219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2219 = x_2218;
}
lean_ctor_set(x_2219, 0, x_2216);
lean_ctor_set(x_2219, 1, x_2217);
return x_2219;
}
block_2208:
{
lean_object* x_2202; lean_object* x_2203; lean_object* x_2204; lean_object* x_2205; lean_object* x_2206; 
x_2202 = l_Lean_Expr_mvarId_x21(x_2198);
x_2203 = lean_array_push(x_19, x_2202);
if (lean_is_scalar(x_2193)) {
 x_2204 = lean_alloc_ctor(0, 8, 2);
} else {
 x_2204 = x_2193;
}
lean_ctor_set(x_2204, 0, x_11);
lean_ctor_set(x_2204, 1, x_12);
lean_ctor_set(x_2204, 2, x_13);
lean_ctor_set(x_2204, 3, x_15);
lean_ctor_set(x_2204, 4, x_16);
lean_ctor_set(x_2204, 5, x_17);
lean_ctor_set(x_2204, 6, x_2200);
lean_ctor_set(x_2204, 7, x_2203);
lean_ctor_set_uint8(x_2204, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2204, sizeof(void*)*8 + 1, x_1886);
lean_inc(x_2198);
x_2205 = l_Lean_mkApp(x_2, x_2198);
x_2206 = lean_expr_instantiate1(x_1980, x_2198);
lean_dec(x_2198);
lean_dec(x_1980);
x_1 = x_2204;
x_2 = x_2205;
x_3 = x_2206;
x_8 = x_1894;
x_10 = x_2201;
goto _start;
}
}
else
{
lean_object* x_2220; lean_object* x_2221; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_2220 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1896, x_4, x_5, x_6, x_7, x_1894, x_9, x_1897);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_2221 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2221 = lean_box(0);
}
if (lean_obj_tag(x_2220) == 0)
{
lean_object* x_2222; lean_object* x_2223; uint8_t x_2224; 
x_2222 = lean_ctor_get(x_2220, 1);
lean_inc(x_2222);
lean_dec(x_2220);
x_2223 = lean_array_get_size(x_12);
x_2224 = lean_nat_dec_lt(x_15, x_2223);
lean_dec(x_2223);
if (x_2224 == 0)
{
uint8_t x_2225; 
lean_dec(x_2221);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_2225 = l_Array_isEmpty___rarg(x_16);
if (x_2225 == 0)
{
lean_object* x_2226; lean_object* x_2227; lean_object* x_2228; lean_object* x_2229; lean_object* x_2230; lean_object* x_2231; lean_object* x_2232; lean_object* x_2233; lean_object* x_2234; lean_object* x_2235; lean_object* x_2236; lean_object* x_2237; lean_object* x_2238; lean_object* x_2239; lean_object* x_2240; lean_object* x_2241; 
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_2226 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2226, 0, x_1978);
x_2227 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_2228 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2228, 0, x_2227);
lean_ctor_set(x_2228, 1, x_2226);
x_2229 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_2230 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2230, 0, x_2228);
lean_ctor_set(x_2230, 1, x_2229);
x_2231 = x_16;
x_2232 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_1982, x_2231);
x_2233 = x_2232;
x_2234 = l_Array_toList___rarg(x_2233);
lean_dec(x_2233);
x_2235 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_2234);
x_2236 = l_Array_HasRepr___rarg___closed__1;
x_2237 = lean_string_append(x_2236, x_2235);
lean_dec(x_2235);
x_2238 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2238, 0, x_2237);
x_2239 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2239, 0, x_2238);
x_2240 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2240, 0, x_2230);
lean_ctor_set(x_2240, 1, x_2239);
x_2241 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2240, x_4, x_5, x_6, x_7, x_1894, x_9, x_2222);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2241;
}
else
{
lean_object* x_2242; uint8_t x_2243; 
lean_dec(x_1978);
lean_dec(x_16);
x_2242 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2243 = l_Lean_checkTraceOption(x_1887, x_2242);
lean_dec(x_1887);
if (x_2243 == 0)
{
lean_object* x_2244; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2244 = x_2222;
goto block_2255;
}
else
{
lean_object* x_2256; lean_object* x_2257; 
x_2256 = lean_ctor_get(x_13, 0);
lean_inc(x_2256);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2257 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2256, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_2222);
if (lean_obj_tag(x_2257) == 0)
{
lean_object* x_2258; 
x_2258 = lean_ctor_get(x_2257, 1);
lean_inc(x_2258);
lean_dec(x_2257);
x_2244 = x_2258;
goto block_2255;
}
else
{
lean_object* x_2259; lean_object* x_2260; lean_object* x_2261; lean_object* x_2262; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2259 = lean_ctor_get(x_2257, 0);
lean_inc(x_2259);
x_2260 = lean_ctor_get(x_2257, 1);
lean_inc(x_2260);
if (lean_is_exclusive(x_2257)) {
 lean_ctor_release(x_2257, 0);
 lean_ctor_release(x_2257, 1);
 x_2261 = x_2257;
} else {
 lean_dec_ref(x_2257);
 x_2261 = lean_box(0);
}
if (lean_is_scalar(x_2261)) {
 x_2262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2262 = x_2261;
}
lean_ctor_set(x_2262, 0, x_2259);
lean_ctor_set(x_2262, 1, x_2260);
return x_2262;
}
}
block_2255:
{
lean_object* x_2245; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2245 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2244);
lean_dec(x_17);
if (lean_obj_tag(x_2245) == 0)
{
lean_object* x_2246; lean_object* x_2247; lean_object* x_2248; lean_object* x_2249; lean_object* x_2250; 
x_2246 = lean_ctor_get(x_2245, 1);
lean_inc(x_2246);
lean_dec(x_2245);
lean_inc(x_2);
x_2247 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__10(x_2, x_11, x_19, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2246);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2248 = lean_ctor_get(x_2247, 1);
lean_inc(x_2248);
if (lean_is_exclusive(x_2247)) {
 lean_ctor_release(x_2247, 0);
 lean_ctor_release(x_2247, 1);
 x_2249 = x_2247;
} else {
 lean_dec_ref(x_2247);
 x_2249 = lean_box(0);
}
if (lean_is_scalar(x_2249)) {
 x_2250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2250 = x_2249;
}
lean_ctor_set(x_2250, 0, x_2);
lean_ctor_set(x_2250, 1, x_2248);
return x_2250;
}
else
{
lean_object* x_2251; lean_object* x_2252; lean_object* x_2253; lean_object* x_2254; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2251 = lean_ctor_get(x_2245, 0);
lean_inc(x_2251);
x_2252 = lean_ctor_get(x_2245, 1);
lean_inc(x_2252);
if (lean_is_exclusive(x_2245)) {
 lean_ctor_release(x_2245, 0);
 lean_ctor_release(x_2245, 1);
 x_2253 = x_2245;
} else {
 lean_dec_ref(x_2245);
 x_2253 = lean_box(0);
}
if (lean_is_scalar(x_2253)) {
 x_2254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2254 = x_2253;
}
lean_ctor_set(x_2254, 0, x_2251);
lean_ctor_set(x_2254, 1, x_2252);
return x_2254;
}
}
}
else
{
lean_object* x_2263; lean_object* x_2264; lean_object* x_2265; lean_object* x_2266; 
lean_inc(x_2);
x_2263 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2263, 0, x_2);
x_2264 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2242, x_2263, x_4, x_5, x_6, x_7, x_1894, x_9, x_2222);
x_2265 = lean_ctor_get(x_2264, 1);
lean_inc(x_2265);
lean_dec(x_2264);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2266 = x_2265;
goto block_2277;
}
else
{
lean_object* x_2278; lean_object* x_2279; 
x_2278 = lean_ctor_get(x_13, 0);
lean_inc(x_2278);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2279 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2278, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_2265);
if (lean_obj_tag(x_2279) == 0)
{
lean_object* x_2280; 
x_2280 = lean_ctor_get(x_2279, 1);
lean_inc(x_2280);
lean_dec(x_2279);
x_2266 = x_2280;
goto block_2277;
}
else
{
lean_object* x_2281; lean_object* x_2282; lean_object* x_2283; lean_object* x_2284; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2281 = lean_ctor_get(x_2279, 0);
lean_inc(x_2281);
x_2282 = lean_ctor_get(x_2279, 1);
lean_inc(x_2282);
if (lean_is_exclusive(x_2279)) {
 lean_ctor_release(x_2279, 0);
 lean_ctor_release(x_2279, 1);
 x_2283 = x_2279;
} else {
 lean_dec_ref(x_2279);
 x_2283 = lean_box(0);
}
if (lean_is_scalar(x_2283)) {
 x_2284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2284 = x_2283;
}
lean_ctor_set(x_2284, 0, x_2281);
lean_ctor_set(x_2284, 1, x_2282);
return x_2284;
}
}
block_2277:
{
lean_object* x_2267; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2267 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2266);
lean_dec(x_17);
if (lean_obj_tag(x_2267) == 0)
{
lean_object* x_2268; lean_object* x_2269; lean_object* x_2270; lean_object* x_2271; lean_object* x_2272; 
x_2268 = lean_ctor_get(x_2267, 1);
lean_inc(x_2268);
lean_dec(x_2267);
lean_inc(x_2);
x_2269 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__11(x_2, x_11, x_19, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2268);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2270 = lean_ctor_get(x_2269, 1);
lean_inc(x_2270);
if (lean_is_exclusive(x_2269)) {
 lean_ctor_release(x_2269, 0);
 lean_ctor_release(x_2269, 1);
 x_2271 = x_2269;
} else {
 lean_dec_ref(x_2269);
 x_2271 = lean_box(0);
}
if (lean_is_scalar(x_2271)) {
 x_2272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2272 = x_2271;
}
lean_ctor_set(x_2272, 0, x_2);
lean_ctor_set(x_2272, 1, x_2270);
return x_2272;
}
else
{
lean_object* x_2273; lean_object* x_2274; lean_object* x_2275; lean_object* x_2276; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2273 = lean_ctor_get(x_2267, 0);
lean_inc(x_2273);
x_2274 = lean_ctor_get(x_2267, 1);
lean_inc(x_2274);
if (lean_is_exclusive(x_2267)) {
 lean_ctor_release(x_2267, 0);
 lean_ctor_release(x_2267, 1);
 x_2275 = x_2267;
} else {
 lean_dec_ref(x_2267);
 x_2275 = lean_box(0);
}
if (lean_is_scalar(x_2275)) {
 x_2276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2276 = x_2275;
}
lean_ctor_set(x_2276, 0, x_2273);
lean_ctor_set(x_2276, 1, x_2274);
return x_2276;
}
}
}
}
}
else
{
lean_object* x_2285; lean_object* x_2286; 
lean_dec(x_1978);
lean_dec(x_1887);
lean_dec(x_3);
x_2285 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2286 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2285, x_1979, x_4, x_5, x_6, x_7, x_1894, x_9, x_2222);
if (lean_obj_tag(x_2286) == 0)
{
lean_object* x_2287; lean_object* x_2288; lean_object* x_2289; lean_object* x_2290; uint8_t x_2291; lean_object* x_2292; lean_object* x_2293; lean_object* x_2294; 
x_2287 = lean_ctor_get(x_2286, 0);
lean_inc(x_2287);
x_2288 = lean_ctor_get(x_2286, 1);
lean_inc(x_2288);
lean_dec(x_2286);
x_2289 = lean_unsigned_to_nat(1u);
x_2290 = lean_nat_add(x_15, x_2289);
lean_dec(x_15);
x_2291 = 1;
if (lean_is_scalar(x_2221)) {
 x_2292 = lean_alloc_ctor(0, 8, 2);
} else {
 x_2292 = x_2221;
}
lean_ctor_set(x_2292, 0, x_11);
lean_ctor_set(x_2292, 1, x_12);
lean_ctor_set(x_2292, 2, x_13);
lean_ctor_set(x_2292, 3, x_2290);
lean_ctor_set(x_2292, 4, x_16);
lean_ctor_set(x_2292, 5, x_17);
lean_ctor_set(x_2292, 6, x_18);
lean_ctor_set(x_2292, 7, x_19);
lean_ctor_set_uint8(x_2292, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2292, sizeof(void*)*8 + 1, x_2291);
lean_inc(x_2287);
x_2293 = l_Lean_mkApp(x_2, x_2287);
x_2294 = lean_expr_instantiate1(x_1980, x_2287);
lean_dec(x_2287);
lean_dec(x_1980);
x_1 = x_2292;
x_2 = x_2293;
x_3 = x_2294;
x_8 = x_1894;
x_10 = x_2288;
goto _start;
}
else
{
lean_object* x_2296; lean_object* x_2297; lean_object* x_2298; lean_object* x_2299; 
lean_dec(x_2221);
lean_dec(x_1980);
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2296 = lean_ctor_get(x_2286, 0);
lean_inc(x_2296);
x_2297 = lean_ctor_get(x_2286, 1);
lean_inc(x_2297);
if (lean_is_exclusive(x_2286)) {
 lean_ctor_release(x_2286, 0);
 lean_ctor_release(x_2286, 1);
 x_2298 = x_2286;
} else {
 lean_dec_ref(x_2286);
 x_2298 = lean_box(0);
}
if (lean_is_scalar(x_2298)) {
 x_2299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2299 = x_2298;
}
lean_ctor_set(x_2299, 0, x_2296);
lean_ctor_set(x_2299, 1, x_2297);
return x_2299;
}
}
}
else
{
lean_object* x_2300; lean_object* x_2301; lean_object* x_2302; lean_object* x_2303; 
lean_dec(x_2221);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_1978);
lean_dec(x_1894);
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2300 = lean_ctor_get(x_2220, 0);
lean_inc(x_2300);
x_2301 = lean_ctor_get(x_2220, 1);
lean_inc(x_2301);
if (lean_is_exclusive(x_2220)) {
 lean_ctor_release(x_2220, 0);
 lean_ctor_release(x_2220, 1);
 x_2302 = x_2220;
} else {
 lean_dec_ref(x_2220);
 x_2302 = lean_box(0);
}
if (lean_is_scalar(x_2302)) {
 x_2303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2303 = x_2302;
}
lean_ctor_set(x_2303, 0, x_2300);
lean_ctor_set(x_2303, 1, x_2301);
return x_2303;
}
}
}
case 2:
{
lean_object* x_2304; lean_object* x_2305; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_2304 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1896, x_4, x_5, x_6, x_7, x_1894, x_9, x_1897);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_2305 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2305 = lean_box(0);
}
if (lean_obj_tag(x_2304) == 0)
{
lean_object* x_2306; uint8_t x_2307; lean_object* x_2308; lean_object* x_2309; uint8_t x_2310; 
x_2306 = lean_ctor_get(x_2304, 1);
lean_inc(x_2306);
lean_dec(x_2304);
x_2307 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
if (lean_is_scalar(x_2305)) {
 x_2308 = lean_alloc_ctor(0, 8, 2);
} else {
 x_2308 = x_2305;
}
lean_ctor_set(x_2308, 0, x_11);
lean_ctor_set(x_2308, 1, x_12);
lean_ctor_set(x_2308, 2, x_13);
lean_ctor_set(x_2308, 3, x_15);
lean_ctor_set(x_2308, 4, x_16);
lean_ctor_set(x_2308, 5, x_17);
lean_ctor_set(x_2308, 6, x_18);
lean_ctor_set(x_2308, 7, x_19);
lean_ctor_set_uint8(x_2308, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2308, sizeof(void*)*8 + 1, x_2307);
x_2309 = lean_array_get_size(x_12);
x_2310 = lean_nat_dec_lt(x_15, x_2309);
lean_dec(x_2309);
if (x_2310 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_2311; 
x_2311 = l_Lean_Expr_getOptParamDefault_x3f(x_1979);
if (lean_obj_tag(x_2311) == 0)
{
lean_object* x_2312; 
x_2312 = l_Lean_Expr_getAutoParamTactic_x3f(x_1979);
if (lean_obj_tag(x_2312) == 0)
{
uint8_t x_2313; 
lean_dec(x_2308);
lean_dec(x_1980);
lean_dec(x_1979);
x_2313 = l_Array_isEmpty___rarg(x_16);
if (x_2313 == 0)
{
lean_object* x_2314; lean_object* x_2315; lean_object* x_2316; lean_object* x_2317; lean_object* x_2318; lean_object* x_2319; lean_object* x_2320; lean_object* x_2321; lean_object* x_2322; lean_object* x_2323; lean_object* x_2324; lean_object* x_2325; lean_object* x_2326; lean_object* x_2327; lean_object* x_2328; lean_object* x_2329; 
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_2314 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2314, 0, x_1978);
x_2315 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_2316 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2316, 0, x_2315);
lean_ctor_set(x_2316, 1, x_2314);
x_2317 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_2318 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2318, 0, x_2316);
lean_ctor_set(x_2318, 1, x_2317);
x_2319 = x_16;
x_2320 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_1982, x_2319);
x_2321 = x_2320;
x_2322 = l_Array_toList___rarg(x_2321);
lean_dec(x_2321);
x_2323 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_2322);
x_2324 = l_Array_HasRepr___rarg___closed__1;
x_2325 = lean_string_append(x_2324, x_2323);
lean_dec(x_2323);
x_2326 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2326, 0, x_2325);
x_2327 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2327, 0, x_2326);
x_2328 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2328, 0, x_2318);
lean_ctor_set(x_2328, 1, x_2327);
x_2329 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2328, x_4, x_5, x_6, x_7, x_1894, x_9, x_2306);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2329;
}
else
{
lean_object* x_2330; uint8_t x_2331; 
lean_dec(x_1978);
lean_dec(x_16);
x_2330 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2331 = l_Lean_checkTraceOption(x_1887, x_2330);
lean_dec(x_1887);
if (x_2331 == 0)
{
lean_object* x_2332; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2332 = x_2306;
goto block_2343;
}
else
{
lean_object* x_2344; lean_object* x_2345; 
x_2344 = lean_ctor_get(x_13, 0);
lean_inc(x_2344);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2345 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2344, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_2306);
if (lean_obj_tag(x_2345) == 0)
{
lean_object* x_2346; 
x_2346 = lean_ctor_get(x_2345, 1);
lean_inc(x_2346);
lean_dec(x_2345);
x_2332 = x_2346;
goto block_2343;
}
else
{
lean_object* x_2347; lean_object* x_2348; lean_object* x_2349; lean_object* x_2350; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2347 = lean_ctor_get(x_2345, 0);
lean_inc(x_2347);
x_2348 = lean_ctor_get(x_2345, 1);
lean_inc(x_2348);
if (lean_is_exclusive(x_2345)) {
 lean_ctor_release(x_2345, 0);
 lean_ctor_release(x_2345, 1);
 x_2349 = x_2345;
} else {
 lean_dec_ref(x_2345);
 x_2349 = lean_box(0);
}
if (lean_is_scalar(x_2349)) {
 x_2350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2350 = x_2349;
}
lean_ctor_set(x_2350, 0, x_2347);
lean_ctor_set(x_2350, 1, x_2348);
return x_2350;
}
}
block_2343:
{
lean_object* x_2333; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2333 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2332);
lean_dec(x_17);
if (lean_obj_tag(x_2333) == 0)
{
lean_object* x_2334; lean_object* x_2335; lean_object* x_2336; lean_object* x_2337; lean_object* x_2338; 
x_2334 = lean_ctor_get(x_2333, 1);
lean_inc(x_2334);
lean_dec(x_2333);
lean_inc(x_2);
x_2335 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__12(x_2, x_11, x_19, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2334);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2336 = lean_ctor_get(x_2335, 1);
lean_inc(x_2336);
if (lean_is_exclusive(x_2335)) {
 lean_ctor_release(x_2335, 0);
 lean_ctor_release(x_2335, 1);
 x_2337 = x_2335;
} else {
 lean_dec_ref(x_2335);
 x_2337 = lean_box(0);
}
if (lean_is_scalar(x_2337)) {
 x_2338 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2338 = x_2337;
}
lean_ctor_set(x_2338, 0, x_2);
lean_ctor_set(x_2338, 1, x_2336);
return x_2338;
}
else
{
lean_object* x_2339; lean_object* x_2340; lean_object* x_2341; lean_object* x_2342; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2339 = lean_ctor_get(x_2333, 0);
lean_inc(x_2339);
x_2340 = lean_ctor_get(x_2333, 1);
lean_inc(x_2340);
if (lean_is_exclusive(x_2333)) {
 lean_ctor_release(x_2333, 0);
 lean_ctor_release(x_2333, 1);
 x_2341 = x_2333;
} else {
 lean_dec_ref(x_2333);
 x_2341 = lean_box(0);
}
if (lean_is_scalar(x_2341)) {
 x_2342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2342 = x_2341;
}
lean_ctor_set(x_2342, 0, x_2339);
lean_ctor_set(x_2342, 1, x_2340);
return x_2342;
}
}
}
else
{
lean_object* x_2351; lean_object* x_2352; lean_object* x_2353; lean_object* x_2354; 
lean_inc(x_2);
x_2351 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2351, 0, x_2);
x_2352 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2330, x_2351, x_4, x_5, x_6, x_7, x_1894, x_9, x_2306);
x_2353 = lean_ctor_get(x_2352, 1);
lean_inc(x_2353);
lean_dec(x_2352);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2354 = x_2353;
goto block_2365;
}
else
{
lean_object* x_2366; lean_object* x_2367; 
x_2366 = lean_ctor_get(x_13, 0);
lean_inc(x_2366);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2367 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2366, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_2353);
if (lean_obj_tag(x_2367) == 0)
{
lean_object* x_2368; 
x_2368 = lean_ctor_get(x_2367, 1);
lean_inc(x_2368);
lean_dec(x_2367);
x_2354 = x_2368;
goto block_2365;
}
else
{
lean_object* x_2369; lean_object* x_2370; lean_object* x_2371; lean_object* x_2372; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2369 = lean_ctor_get(x_2367, 0);
lean_inc(x_2369);
x_2370 = lean_ctor_get(x_2367, 1);
lean_inc(x_2370);
if (lean_is_exclusive(x_2367)) {
 lean_ctor_release(x_2367, 0);
 lean_ctor_release(x_2367, 1);
 x_2371 = x_2367;
} else {
 lean_dec_ref(x_2367);
 x_2371 = lean_box(0);
}
if (lean_is_scalar(x_2371)) {
 x_2372 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2372 = x_2371;
}
lean_ctor_set(x_2372, 0, x_2369);
lean_ctor_set(x_2372, 1, x_2370);
return x_2372;
}
}
block_2365:
{
lean_object* x_2355; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2355 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2354);
lean_dec(x_17);
if (lean_obj_tag(x_2355) == 0)
{
lean_object* x_2356; lean_object* x_2357; lean_object* x_2358; lean_object* x_2359; lean_object* x_2360; 
x_2356 = lean_ctor_get(x_2355, 1);
lean_inc(x_2356);
lean_dec(x_2355);
lean_inc(x_2);
x_2357 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__13(x_2, x_11, x_19, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2356);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2358 = lean_ctor_get(x_2357, 1);
lean_inc(x_2358);
if (lean_is_exclusive(x_2357)) {
 lean_ctor_release(x_2357, 0);
 lean_ctor_release(x_2357, 1);
 x_2359 = x_2357;
} else {
 lean_dec_ref(x_2357);
 x_2359 = lean_box(0);
}
if (lean_is_scalar(x_2359)) {
 x_2360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2360 = x_2359;
}
lean_ctor_set(x_2360, 0, x_2);
lean_ctor_set(x_2360, 1, x_2358);
return x_2360;
}
else
{
lean_object* x_2361; lean_object* x_2362; lean_object* x_2363; lean_object* x_2364; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2361 = lean_ctor_get(x_2355, 0);
lean_inc(x_2361);
x_2362 = lean_ctor_get(x_2355, 1);
lean_inc(x_2362);
if (lean_is_exclusive(x_2355)) {
 lean_ctor_release(x_2355, 0);
 lean_ctor_release(x_2355, 1);
 x_2363 = x_2355;
} else {
 lean_dec_ref(x_2355);
 x_2363 = lean_box(0);
}
if (lean_is_scalar(x_2363)) {
 x_2364 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2364 = x_2363;
}
lean_ctor_set(x_2364, 0, x_2361);
lean_ctor_set(x_2364, 1, x_2362);
return x_2364;
}
}
}
}
}
else
{
lean_object* x_2373; 
lean_dec(x_1978);
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_2373 = lean_ctor_get(x_2312, 0);
lean_inc(x_2373);
lean_dec(x_2312);
if (lean_obj_tag(x_2373) == 4)
{
lean_object* x_2374; lean_object* x_2375; lean_object* x_2376; lean_object* x_2377; lean_object* x_2378; lean_object* x_2379; 
x_2374 = lean_ctor_get(x_2373, 0);
lean_inc(x_2374);
lean_dec(x_2373);
x_2375 = lean_st_ref_get(x_9, x_2306);
x_2376 = lean_ctor_get(x_2375, 0);
lean_inc(x_2376);
x_2377 = lean_ctor_get(x_2375, 1);
lean_inc(x_2377);
lean_dec(x_2375);
x_2378 = lean_ctor_get(x_2376, 0);
lean_inc(x_2378);
lean_dec(x_2376);
x_2379 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_2378, x_2374);
if (lean_obj_tag(x_2379) == 0)
{
lean_object* x_2380; lean_object* x_2381; lean_object* x_2382; lean_object* x_2383; 
lean_dec(x_2308);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_11);
lean_dec(x_2);
x_2380 = lean_ctor_get(x_2379, 0);
lean_inc(x_2380);
lean_dec(x_2379);
x_2381 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2381, 0, x_2380);
x_2382 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2382, 0, x_2381);
x_2383 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2382, x_4, x_5, x_6, x_7, x_1894, x_9, x_2377);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2383;
}
else
{
lean_object* x_2384; lean_object* x_2385; lean_object* x_2386; lean_object* x_2387; lean_object* x_2388; lean_object* x_2389; lean_object* x_2390; lean_object* x_2391; lean_object* x_2392; lean_object* x_2393; lean_object* x_2394; lean_object* x_2395; lean_object* x_2396; lean_object* x_2397; lean_object* x_2398; lean_object* x_2399; lean_object* x_2400; lean_object* x_2401; lean_object* x_2402; lean_object* x_2403; lean_object* x_2404; lean_object* x_2405; lean_object* x_2406; lean_object* x_2407; lean_object* x_2408; lean_object* x_2409; lean_object* x_2410; lean_object* x_2411; lean_object* x_2412; lean_object* x_2413; lean_object* x_2414; lean_object* x_2415; lean_object* x_2416; lean_object* x_2417; lean_object* x_2418; 
x_2384 = lean_ctor_get(x_2379, 0);
lean_inc(x_2384);
lean_dec(x_2379);
x_2385 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_1894, x_9, x_2377);
x_2386 = lean_ctor_get(x_2385, 1);
lean_inc(x_2386);
lean_dec(x_2385);
x_2387 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_2386);
x_2388 = lean_ctor_get(x_2387, 1);
lean_inc(x_2388);
lean_dec(x_2387);
x_2389 = l_Lean_Syntax_getArgs(x_2384);
lean_dec(x_2384);
x_2390 = l_Array_empty___closed__1;
x_2391 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2389, x_2389, x_1982, x_2390);
lean_dec(x_2389);
x_2392 = l_Lean_nullKind___closed__2;
x_2393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2393, 0, x_2392);
lean_ctor_set(x_2393, 1, x_2391);
x_2394 = lean_array_push(x_2390, x_2393);
x_2395 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__17;
x_2396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2396, 0, x_2395);
lean_ctor_set(x_2396, 1, x_2394);
x_2397 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_2398 = lean_array_push(x_2397, x_2396);
x_2399 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__20;
x_2400 = lean_array_push(x_2398, x_2399);
x_2401 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__19;
x_2402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2402, 0, x_2401);
lean_ctor_set(x_2402, 1, x_2400);
x_2403 = lean_array_push(x_2390, x_2402);
x_2404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2404, 0, x_2392);
lean_ctor_set(x_2404, 1, x_2403);
x_2405 = lean_array_push(x_2390, x_2404);
x_2406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2406, 0, x_2395);
lean_ctor_set(x_2406, 1, x_2405);
x_2407 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_2408 = lean_array_push(x_2407, x_2406);
x_2409 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_2410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2410, 0, x_2409);
lean_ctor_set(x_2410, 1, x_2408);
x_2411 = l_Lean_Syntax_copyInfo(x_2410, x_11);
lean_dec(x_11);
x_2412 = l_Lean_Expr_getAppNumArgsAux___main(x_1979, x_1982);
x_2413 = lean_nat_sub(x_2412, x_1982);
lean_dec(x_2412);
x_2414 = lean_unsigned_to_nat(1u);
x_2415 = lean_nat_sub(x_2413, x_2414);
lean_dec(x_2413);
x_2416 = l_Lean_Expr_getRevArg_x21___main(x_1979, x_2415);
lean_dec(x_1979);
x_2417 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2417, 0, x_2411);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2418 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2417, x_2416, x_4, x_5, x_6, x_7, x_1894, x_9, x_2388);
if (lean_obj_tag(x_2418) == 0)
{
lean_object* x_2419; lean_object* x_2420; lean_object* x_2421; lean_object* x_2422; 
x_2419 = lean_ctor_get(x_2418, 0);
lean_inc(x_2419);
x_2420 = lean_ctor_get(x_2418, 1);
lean_inc(x_2420);
lean_dec(x_2418);
lean_inc(x_2419);
x_2421 = l_Lean_mkApp(x_2, x_2419);
x_2422 = lean_expr_instantiate1(x_1980, x_2419);
lean_dec(x_2419);
lean_dec(x_1980);
x_1 = x_2308;
x_2 = x_2421;
x_3 = x_2422;
x_8 = x_1894;
x_10 = x_2420;
goto _start;
}
else
{
lean_object* x_2424; lean_object* x_2425; lean_object* x_2426; lean_object* x_2427; 
lean_dec(x_2308);
lean_dec(x_1980);
lean_dec(x_1894);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2424 = lean_ctor_get(x_2418, 0);
lean_inc(x_2424);
x_2425 = lean_ctor_get(x_2418, 1);
lean_inc(x_2425);
if (lean_is_exclusive(x_2418)) {
 lean_ctor_release(x_2418, 0);
 lean_ctor_release(x_2418, 1);
 x_2426 = x_2418;
} else {
 lean_dec_ref(x_2418);
 x_2426 = lean_box(0);
}
if (lean_is_scalar(x_2426)) {
 x_2427 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2427 = x_2426;
}
lean_ctor_set(x_2427, 0, x_2424);
lean_ctor_set(x_2427, 1, x_2425);
return x_2427;
}
}
}
else
{
lean_object* x_2428; lean_object* x_2429; 
lean_dec(x_2373);
lean_dec(x_2308);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_11);
lean_dec(x_2);
x_2428 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_2429 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2428, x_4, x_5, x_6, x_7, x_1894, x_9, x_2306);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2429;
}
}
}
else
{
lean_object* x_2430; lean_object* x_2431; lean_object* x_2432; 
lean_dec(x_1979);
lean_dec(x_1978);
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_2430 = lean_ctor_get(x_2311, 0);
lean_inc(x_2430);
lean_dec(x_2311);
lean_inc(x_2430);
x_2431 = l_Lean_mkApp(x_2, x_2430);
x_2432 = lean_expr_instantiate1(x_1980, x_2430);
lean_dec(x_2430);
lean_dec(x_1980);
x_1 = x_2308;
x_2 = x_2431;
x_3 = x_2432;
x_8 = x_1894;
x_10 = x_2306;
goto _start;
}
}
else
{
uint8_t x_2434; 
lean_dec(x_2308);
lean_dec(x_1980);
lean_dec(x_1979);
x_2434 = l_Array_isEmpty___rarg(x_16);
if (x_2434 == 0)
{
lean_object* x_2435; lean_object* x_2436; lean_object* x_2437; lean_object* x_2438; lean_object* x_2439; lean_object* x_2440; lean_object* x_2441; lean_object* x_2442; lean_object* x_2443; lean_object* x_2444; lean_object* x_2445; lean_object* x_2446; lean_object* x_2447; lean_object* x_2448; lean_object* x_2449; lean_object* x_2450; 
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_2435 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2435, 0, x_1978);
x_2436 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_2437 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2437, 0, x_2436);
lean_ctor_set(x_2437, 1, x_2435);
x_2438 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_2439 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2439, 0, x_2437);
lean_ctor_set(x_2439, 1, x_2438);
x_2440 = x_16;
x_2441 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_1982, x_2440);
x_2442 = x_2441;
x_2443 = l_Array_toList___rarg(x_2442);
lean_dec(x_2442);
x_2444 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_2443);
x_2445 = l_Array_HasRepr___rarg___closed__1;
x_2446 = lean_string_append(x_2445, x_2444);
lean_dec(x_2444);
x_2447 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2447, 0, x_2446);
x_2448 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2448, 0, x_2447);
x_2449 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2449, 0, x_2439);
lean_ctor_set(x_2449, 1, x_2448);
x_2450 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2449, x_4, x_5, x_6, x_7, x_1894, x_9, x_2306);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2450;
}
else
{
lean_object* x_2451; uint8_t x_2452; 
lean_dec(x_1978);
lean_dec(x_16);
x_2451 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2452 = l_Lean_checkTraceOption(x_1887, x_2451);
lean_dec(x_1887);
if (x_2452 == 0)
{
lean_object* x_2453; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2453 = x_2306;
goto block_2464;
}
else
{
lean_object* x_2465; lean_object* x_2466; 
x_2465 = lean_ctor_get(x_13, 0);
lean_inc(x_2465);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2466 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2465, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_2306);
if (lean_obj_tag(x_2466) == 0)
{
lean_object* x_2467; 
x_2467 = lean_ctor_get(x_2466, 1);
lean_inc(x_2467);
lean_dec(x_2466);
x_2453 = x_2467;
goto block_2464;
}
else
{
lean_object* x_2468; lean_object* x_2469; lean_object* x_2470; lean_object* x_2471; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2468 = lean_ctor_get(x_2466, 0);
lean_inc(x_2468);
x_2469 = lean_ctor_get(x_2466, 1);
lean_inc(x_2469);
if (lean_is_exclusive(x_2466)) {
 lean_ctor_release(x_2466, 0);
 lean_ctor_release(x_2466, 1);
 x_2470 = x_2466;
} else {
 lean_dec_ref(x_2466);
 x_2470 = lean_box(0);
}
if (lean_is_scalar(x_2470)) {
 x_2471 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2471 = x_2470;
}
lean_ctor_set(x_2471, 0, x_2468);
lean_ctor_set(x_2471, 1, x_2469);
return x_2471;
}
}
block_2464:
{
lean_object* x_2454; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2454 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2453);
lean_dec(x_17);
if (lean_obj_tag(x_2454) == 0)
{
lean_object* x_2455; lean_object* x_2456; lean_object* x_2457; lean_object* x_2458; lean_object* x_2459; 
x_2455 = lean_ctor_get(x_2454, 1);
lean_inc(x_2455);
lean_dec(x_2454);
lean_inc(x_2);
x_2456 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__14(x_2, x_11, x_19, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2455);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2457 = lean_ctor_get(x_2456, 1);
lean_inc(x_2457);
if (lean_is_exclusive(x_2456)) {
 lean_ctor_release(x_2456, 0);
 lean_ctor_release(x_2456, 1);
 x_2458 = x_2456;
} else {
 lean_dec_ref(x_2456);
 x_2458 = lean_box(0);
}
if (lean_is_scalar(x_2458)) {
 x_2459 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2459 = x_2458;
}
lean_ctor_set(x_2459, 0, x_2);
lean_ctor_set(x_2459, 1, x_2457);
return x_2459;
}
else
{
lean_object* x_2460; lean_object* x_2461; lean_object* x_2462; lean_object* x_2463; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2460 = lean_ctor_get(x_2454, 0);
lean_inc(x_2460);
x_2461 = lean_ctor_get(x_2454, 1);
lean_inc(x_2461);
if (lean_is_exclusive(x_2454)) {
 lean_ctor_release(x_2454, 0);
 lean_ctor_release(x_2454, 1);
 x_2462 = x_2454;
} else {
 lean_dec_ref(x_2454);
 x_2462 = lean_box(0);
}
if (lean_is_scalar(x_2462)) {
 x_2463 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2463 = x_2462;
}
lean_ctor_set(x_2463, 0, x_2460);
lean_ctor_set(x_2463, 1, x_2461);
return x_2463;
}
}
}
else
{
lean_object* x_2472; lean_object* x_2473; lean_object* x_2474; lean_object* x_2475; 
lean_inc(x_2);
x_2472 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2472, 0, x_2);
x_2473 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2451, x_2472, x_4, x_5, x_6, x_7, x_1894, x_9, x_2306);
x_2474 = lean_ctor_get(x_2473, 1);
lean_inc(x_2474);
lean_dec(x_2473);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2475 = x_2474;
goto block_2486;
}
else
{
lean_object* x_2487; lean_object* x_2488; 
x_2487 = lean_ctor_get(x_13, 0);
lean_inc(x_2487);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2488 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2487, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_2474);
if (lean_obj_tag(x_2488) == 0)
{
lean_object* x_2489; 
x_2489 = lean_ctor_get(x_2488, 1);
lean_inc(x_2489);
lean_dec(x_2488);
x_2475 = x_2489;
goto block_2486;
}
else
{
lean_object* x_2490; lean_object* x_2491; lean_object* x_2492; lean_object* x_2493; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2490 = lean_ctor_get(x_2488, 0);
lean_inc(x_2490);
x_2491 = lean_ctor_get(x_2488, 1);
lean_inc(x_2491);
if (lean_is_exclusive(x_2488)) {
 lean_ctor_release(x_2488, 0);
 lean_ctor_release(x_2488, 1);
 x_2492 = x_2488;
} else {
 lean_dec_ref(x_2488);
 x_2492 = lean_box(0);
}
if (lean_is_scalar(x_2492)) {
 x_2493 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2493 = x_2492;
}
lean_ctor_set(x_2493, 0, x_2490);
lean_ctor_set(x_2493, 1, x_2491);
return x_2493;
}
}
block_2486:
{
lean_object* x_2476; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2476 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2475);
lean_dec(x_17);
if (lean_obj_tag(x_2476) == 0)
{
lean_object* x_2477; lean_object* x_2478; lean_object* x_2479; lean_object* x_2480; lean_object* x_2481; 
x_2477 = lean_ctor_get(x_2476, 1);
lean_inc(x_2477);
lean_dec(x_2476);
lean_inc(x_2);
x_2478 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__15(x_2, x_11, x_19, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2477);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2479 = lean_ctor_get(x_2478, 1);
lean_inc(x_2479);
if (lean_is_exclusive(x_2478)) {
 lean_ctor_release(x_2478, 0);
 lean_ctor_release(x_2478, 1);
 x_2480 = x_2478;
} else {
 lean_dec_ref(x_2478);
 x_2480 = lean_box(0);
}
if (lean_is_scalar(x_2480)) {
 x_2481 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2481 = x_2480;
}
lean_ctor_set(x_2481, 0, x_2);
lean_ctor_set(x_2481, 1, x_2479);
return x_2481;
}
else
{
lean_object* x_2482; lean_object* x_2483; lean_object* x_2484; lean_object* x_2485; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2482 = lean_ctor_get(x_2476, 0);
lean_inc(x_2482);
x_2483 = lean_ctor_get(x_2476, 1);
lean_inc(x_2483);
if (lean_is_exclusive(x_2476)) {
 lean_ctor_release(x_2476, 0);
 lean_ctor_release(x_2476, 1);
 x_2484 = x_2476;
} else {
 lean_dec_ref(x_2476);
 x_2484 = lean_box(0);
}
if (lean_is_scalar(x_2484)) {
 x_2485 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2485 = x_2484;
}
lean_ctor_set(x_2485, 0, x_2482);
lean_ctor_set(x_2485, 1, x_2483);
return x_2485;
}
}
}
}
}
}
else
{
lean_object* x_2494; lean_object* x_2495; 
lean_dec(x_2308);
lean_dec(x_1978);
lean_dec(x_1887);
lean_dec(x_3);
x_2494 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2495 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2494, x_1979, x_4, x_5, x_6, x_7, x_1894, x_9, x_2306);
if (lean_obj_tag(x_2495) == 0)
{
lean_object* x_2496; lean_object* x_2497; lean_object* x_2498; lean_object* x_2499; lean_object* x_2500; lean_object* x_2501; lean_object* x_2502; 
x_2496 = lean_ctor_get(x_2495, 0);
lean_inc(x_2496);
x_2497 = lean_ctor_get(x_2495, 1);
lean_inc(x_2497);
lean_dec(x_2495);
x_2498 = lean_unsigned_to_nat(1u);
x_2499 = lean_nat_add(x_15, x_2498);
lean_dec(x_15);
x_2500 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_2500, 0, x_11);
lean_ctor_set(x_2500, 1, x_12);
lean_ctor_set(x_2500, 2, x_13);
lean_ctor_set(x_2500, 3, x_2499);
lean_ctor_set(x_2500, 4, x_16);
lean_ctor_set(x_2500, 5, x_17);
lean_ctor_set(x_2500, 6, x_18);
lean_ctor_set(x_2500, 7, x_19);
lean_ctor_set_uint8(x_2500, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2500, sizeof(void*)*8 + 1, x_2307);
lean_inc(x_2496);
x_2501 = l_Lean_mkApp(x_2, x_2496);
x_2502 = lean_expr_instantiate1(x_1980, x_2496);
lean_dec(x_2496);
lean_dec(x_1980);
x_1 = x_2500;
x_2 = x_2501;
x_3 = x_2502;
x_8 = x_1894;
x_10 = x_2497;
goto _start;
}
else
{
lean_object* x_2504; lean_object* x_2505; lean_object* x_2506; lean_object* x_2507; 
lean_dec(x_1980);
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2504 = lean_ctor_get(x_2495, 0);
lean_inc(x_2504);
x_2505 = lean_ctor_get(x_2495, 1);
lean_inc(x_2505);
if (lean_is_exclusive(x_2495)) {
 lean_ctor_release(x_2495, 0);
 lean_ctor_release(x_2495, 1);
 x_2506 = x_2495;
} else {
 lean_dec_ref(x_2495);
 x_2506 = lean_box(0);
}
if (lean_is_scalar(x_2506)) {
 x_2507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2507 = x_2506;
}
lean_ctor_set(x_2507, 0, x_2504);
lean_ctor_set(x_2507, 1, x_2505);
return x_2507;
}
}
}
else
{
lean_object* x_2508; lean_object* x_2509; lean_object* x_2510; lean_object* x_2511; 
lean_dec(x_2305);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_1978);
lean_dec(x_1894);
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2508 = lean_ctor_get(x_2304, 0);
lean_inc(x_2508);
x_2509 = lean_ctor_get(x_2304, 1);
lean_inc(x_2509);
if (lean_is_exclusive(x_2304)) {
 lean_ctor_release(x_2304, 0);
 lean_ctor_release(x_2304, 1);
 x_2510 = x_2304;
} else {
 lean_dec_ref(x_2304);
 x_2510 = lean_box(0);
}
if (lean_is_scalar(x_2510)) {
 x_2511 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2511 = x_2510;
}
lean_ctor_set(x_2511, 0, x_2508);
lean_ctor_set(x_2511, 1, x_2509);
return x_2511;
}
}
case 3:
{
if (x_14 == 0)
{
lean_object* x_2512; lean_object* x_2513; uint8_t x_2514; lean_object* x_2515; lean_object* x_2516; lean_object* x_2517; lean_object* x_2518; lean_object* x_2519; lean_object* x_2520; lean_object* x_2521; lean_object* x_2522; lean_object* x_2523; 
lean_dec(x_1978);
lean_dec(x_1896);
lean_dec(x_1887);
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_2512 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2512 = lean_box(0);
}
x_2513 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2513, 0, x_1979);
x_2514 = 1;
x_2515 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_2516 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_2513, x_2514, x_2515, x_4, x_5, x_6, x_7, x_1894, x_9, x_1897);
x_2517 = lean_ctor_get(x_2516, 0);
lean_inc(x_2517);
x_2518 = lean_ctor_get(x_2516, 1);
lean_inc(x_2518);
lean_dec(x_2516);
x_2519 = l_Lean_Expr_mvarId_x21(x_2517);
x_2520 = lean_array_push(x_17, x_2519);
if (lean_is_scalar(x_2512)) {
 x_2521 = lean_alloc_ctor(0, 8, 2);
} else {
 x_2521 = x_2512;
}
lean_ctor_set(x_2521, 0, x_11);
lean_ctor_set(x_2521, 1, x_12);
lean_ctor_set(x_2521, 2, x_13);
lean_ctor_set(x_2521, 3, x_15);
lean_ctor_set(x_2521, 4, x_16);
lean_ctor_set(x_2521, 5, x_2520);
lean_ctor_set(x_2521, 6, x_18);
lean_ctor_set(x_2521, 7, x_19);
lean_ctor_set_uint8(x_2521, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2521, sizeof(void*)*8 + 1, x_1886);
lean_inc(x_2517);
x_2522 = l_Lean_mkApp(x_2, x_2517);
x_2523 = lean_expr_instantiate1(x_1980, x_2517);
lean_dec(x_2517);
lean_dec(x_1980);
x_1 = x_2521;
x_2 = x_2522;
x_3 = x_2523;
x_8 = x_1894;
x_10 = x_2518;
goto _start;
}
else
{
uint8_t x_2525; 
x_2525 = l___private_Lean_Elab_App_9__nextArgIsHole(x_1);
if (x_2525 == 0)
{
lean_object* x_2526; lean_object* x_2527; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_2526 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1896, x_4, x_5, x_6, x_7, x_1894, x_9, x_1897);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_2527 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2527 = lean_box(0);
}
if (lean_obj_tag(x_2526) == 0)
{
lean_object* x_2528; lean_object* x_2529; uint8_t x_2530; 
x_2528 = lean_ctor_get(x_2526, 1);
lean_inc(x_2528);
lean_dec(x_2526);
x_2529 = lean_array_get_size(x_12);
x_2530 = lean_nat_dec_lt(x_15, x_2529);
lean_dec(x_2529);
if (x_2530 == 0)
{
uint8_t x_2531; 
lean_dec(x_2527);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_2531 = l_Array_isEmpty___rarg(x_16);
if (x_2531 == 0)
{
lean_object* x_2532; lean_object* x_2533; lean_object* x_2534; lean_object* x_2535; lean_object* x_2536; lean_object* x_2537; lean_object* x_2538; lean_object* x_2539; lean_object* x_2540; lean_object* x_2541; lean_object* x_2542; lean_object* x_2543; lean_object* x_2544; lean_object* x_2545; lean_object* x_2546; lean_object* x_2547; 
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_2532 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2532, 0, x_1978);
x_2533 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_2534 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2534, 0, x_2533);
lean_ctor_set(x_2534, 1, x_2532);
x_2535 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_2536 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2536, 0, x_2534);
lean_ctor_set(x_2536, 1, x_2535);
x_2537 = x_16;
x_2538 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_1982, x_2537);
x_2539 = x_2538;
x_2540 = l_Array_toList___rarg(x_2539);
lean_dec(x_2539);
x_2541 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_2540);
x_2542 = l_Array_HasRepr___rarg___closed__1;
x_2543 = lean_string_append(x_2542, x_2541);
lean_dec(x_2541);
x_2544 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2544, 0, x_2543);
x_2545 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2545, 0, x_2544);
x_2546 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2546, 0, x_2536);
lean_ctor_set(x_2546, 1, x_2545);
x_2547 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2546, x_4, x_5, x_6, x_7, x_1894, x_9, x_2528);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2547;
}
else
{
lean_object* x_2548; uint8_t x_2549; 
lean_dec(x_1978);
lean_dec(x_16);
x_2548 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2549 = l_Lean_checkTraceOption(x_1887, x_2548);
lean_dec(x_1887);
if (x_2549 == 0)
{
lean_object* x_2550; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2550 = x_2528;
goto block_2561;
}
else
{
lean_object* x_2562; lean_object* x_2563; 
x_2562 = lean_ctor_get(x_13, 0);
lean_inc(x_2562);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2563 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2562, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_2528);
if (lean_obj_tag(x_2563) == 0)
{
lean_object* x_2564; 
x_2564 = lean_ctor_get(x_2563, 1);
lean_inc(x_2564);
lean_dec(x_2563);
x_2550 = x_2564;
goto block_2561;
}
else
{
lean_object* x_2565; lean_object* x_2566; lean_object* x_2567; lean_object* x_2568; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2565 = lean_ctor_get(x_2563, 0);
lean_inc(x_2565);
x_2566 = lean_ctor_get(x_2563, 1);
lean_inc(x_2566);
if (lean_is_exclusive(x_2563)) {
 lean_ctor_release(x_2563, 0);
 lean_ctor_release(x_2563, 1);
 x_2567 = x_2563;
} else {
 lean_dec_ref(x_2563);
 x_2567 = lean_box(0);
}
if (lean_is_scalar(x_2567)) {
 x_2568 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2568 = x_2567;
}
lean_ctor_set(x_2568, 0, x_2565);
lean_ctor_set(x_2568, 1, x_2566);
return x_2568;
}
}
block_2561:
{
lean_object* x_2551; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2551 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2550);
lean_dec(x_17);
if (lean_obj_tag(x_2551) == 0)
{
lean_object* x_2552; lean_object* x_2553; lean_object* x_2554; lean_object* x_2555; lean_object* x_2556; 
x_2552 = lean_ctor_get(x_2551, 1);
lean_inc(x_2552);
lean_dec(x_2551);
lean_inc(x_2);
x_2553 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__16(x_2, x_11, x_19, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2552);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2554 = lean_ctor_get(x_2553, 1);
lean_inc(x_2554);
if (lean_is_exclusive(x_2553)) {
 lean_ctor_release(x_2553, 0);
 lean_ctor_release(x_2553, 1);
 x_2555 = x_2553;
} else {
 lean_dec_ref(x_2553);
 x_2555 = lean_box(0);
}
if (lean_is_scalar(x_2555)) {
 x_2556 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2556 = x_2555;
}
lean_ctor_set(x_2556, 0, x_2);
lean_ctor_set(x_2556, 1, x_2554);
return x_2556;
}
else
{
lean_object* x_2557; lean_object* x_2558; lean_object* x_2559; lean_object* x_2560; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2557 = lean_ctor_get(x_2551, 0);
lean_inc(x_2557);
x_2558 = lean_ctor_get(x_2551, 1);
lean_inc(x_2558);
if (lean_is_exclusive(x_2551)) {
 lean_ctor_release(x_2551, 0);
 lean_ctor_release(x_2551, 1);
 x_2559 = x_2551;
} else {
 lean_dec_ref(x_2551);
 x_2559 = lean_box(0);
}
if (lean_is_scalar(x_2559)) {
 x_2560 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2560 = x_2559;
}
lean_ctor_set(x_2560, 0, x_2557);
lean_ctor_set(x_2560, 1, x_2558);
return x_2560;
}
}
}
else
{
lean_object* x_2569; lean_object* x_2570; lean_object* x_2571; lean_object* x_2572; 
lean_inc(x_2);
x_2569 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2569, 0, x_2);
x_2570 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2548, x_2569, x_4, x_5, x_6, x_7, x_1894, x_9, x_2528);
x_2571 = lean_ctor_get(x_2570, 1);
lean_inc(x_2571);
lean_dec(x_2570);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2572 = x_2571;
goto block_2583;
}
else
{
lean_object* x_2584; lean_object* x_2585; 
x_2584 = lean_ctor_get(x_13, 0);
lean_inc(x_2584);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2585 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2584, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_2571);
if (lean_obj_tag(x_2585) == 0)
{
lean_object* x_2586; 
x_2586 = lean_ctor_get(x_2585, 1);
lean_inc(x_2586);
lean_dec(x_2585);
x_2572 = x_2586;
goto block_2583;
}
else
{
lean_object* x_2587; lean_object* x_2588; lean_object* x_2589; lean_object* x_2590; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2587 = lean_ctor_get(x_2585, 0);
lean_inc(x_2587);
x_2588 = lean_ctor_get(x_2585, 1);
lean_inc(x_2588);
if (lean_is_exclusive(x_2585)) {
 lean_ctor_release(x_2585, 0);
 lean_ctor_release(x_2585, 1);
 x_2589 = x_2585;
} else {
 lean_dec_ref(x_2585);
 x_2589 = lean_box(0);
}
if (lean_is_scalar(x_2589)) {
 x_2590 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2590 = x_2589;
}
lean_ctor_set(x_2590, 0, x_2587);
lean_ctor_set(x_2590, 1, x_2588);
return x_2590;
}
}
block_2583:
{
lean_object* x_2573; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2573 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2572);
lean_dec(x_17);
if (lean_obj_tag(x_2573) == 0)
{
lean_object* x_2574; lean_object* x_2575; lean_object* x_2576; lean_object* x_2577; lean_object* x_2578; 
x_2574 = lean_ctor_get(x_2573, 1);
lean_inc(x_2574);
lean_dec(x_2573);
lean_inc(x_2);
x_2575 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__17(x_2, x_11, x_19, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2574);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2576 = lean_ctor_get(x_2575, 1);
lean_inc(x_2576);
if (lean_is_exclusive(x_2575)) {
 lean_ctor_release(x_2575, 0);
 lean_ctor_release(x_2575, 1);
 x_2577 = x_2575;
} else {
 lean_dec_ref(x_2575);
 x_2577 = lean_box(0);
}
if (lean_is_scalar(x_2577)) {
 x_2578 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2578 = x_2577;
}
lean_ctor_set(x_2578, 0, x_2);
lean_ctor_set(x_2578, 1, x_2576);
return x_2578;
}
else
{
lean_object* x_2579; lean_object* x_2580; lean_object* x_2581; lean_object* x_2582; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2579 = lean_ctor_get(x_2573, 0);
lean_inc(x_2579);
x_2580 = lean_ctor_get(x_2573, 1);
lean_inc(x_2580);
if (lean_is_exclusive(x_2573)) {
 lean_ctor_release(x_2573, 0);
 lean_ctor_release(x_2573, 1);
 x_2581 = x_2573;
} else {
 lean_dec_ref(x_2573);
 x_2581 = lean_box(0);
}
if (lean_is_scalar(x_2581)) {
 x_2582 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2582 = x_2581;
}
lean_ctor_set(x_2582, 0, x_2579);
lean_ctor_set(x_2582, 1, x_2580);
return x_2582;
}
}
}
}
}
else
{
lean_object* x_2591; lean_object* x_2592; 
lean_dec(x_1978);
lean_dec(x_1887);
lean_dec(x_3);
x_2591 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2592 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2591, x_1979, x_4, x_5, x_6, x_7, x_1894, x_9, x_2528);
if (lean_obj_tag(x_2592) == 0)
{
lean_object* x_2593; lean_object* x_2594; lean_object* x_2595; lean_object* x_2596; uint8_t x_2597; lean_object* x_2598; lean_object* x_2599; lean_object* x_2600; 
x_2593 = lean_ctor_get(x_2592, 0);
lean_inc(x_2593);
x_2594 = lean_ctor_get(x_2592, 1);
lean_inc(x_2594);
lean_dec(x_2592);
x_2595 = lean_unsigned_to_nat(1u);
x_2596 = lean_nat_add(x_15, x_2595);
lean_dec(x_15);
x_2597 = 1;
if (lean_is_scalar(x_2527)) {
 x_2598 = lean_alloc_ctor(0, 8, 2);
} else {
 x_2598 = x_2527;
}
lean_ctor_set(x_2598, 0, x_11);
lean_ctor_set(x_2598, 1, x_12);
lean_ctor_set(x_2598, 2, x_13);
lean_ctor_set(x_2598, 3, x_2596);
lean_ctor_set(x_2598, 4, x_16);
lean_ctor_set(x_2598, 5, x_17);
lean_ctor_set(x_2598, 6, x_18);
lean_ctor_set(x_2598, 7, x_19);
lean_ctor_set_uint8(x_2598, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2598, sizeof(void*)*8 + 1, x_2597);
lean_inc(x_2593);
x_2599 = l_Lean_mkApp(x_2, x_2593);
x_2600 = lean_expr_instantiate1(x_1980, x_2593);
lean_dec(x_2593);
lean_dec(x_1980);
x_1 = x_2598;
x_2 = x_2599;
x_3 = x_2600;
x_8 = x_1894;
x_10 = x_2594;
goto _start;
}
else
{
lean_object* x_2602; lean_object* x_2603; lean_object* x_2604; lean_object* x_2605; 
lean_dec(x_2527);
lean_dec(x_1980);
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2602 = lean_ctor_get(x_2592, 0);
lean_inc(x_2602);
x_2603 = lean_ctor_get(x_2592, 1);
lean_inc(x_2603);
if (lean_is_exclusive(x_2592)) {
 lean_ctor_release(x_2592, 0);
 lean_ctor_release(x_2592, 1);
 x_2604 = x_2592;
} else {
 lean_dec_ref(x_2592);
 x_2604 = lean_box(0);
}
if (lean_is_scalar(x_2604)) {
 x_2605 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2605 = x_2604;
}
lean_ctor_set(x_2605, 0, x_2602);
lean_ctor_set(x_2605, 1, x_2603);
return x_2605;
}
}
}
else
{
lean_object* x_2606; lean_object* x_2607; lean_object* x_2608; lean_object* x_2609; 
lean_dec(x_2527);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_1978);
lean_dec(x_1894);
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2606 = lean_ctor_get(x_2526, 0);
lean_inc(x_2606);
x_2607 = lean_ctor_get(x_2526, 1);
lean_inc(x_2607);
if (lean_is_exclusive(x_2526)) {
 lean_ctor_release(x_2526, 0);
 lean_ctor_release(x_2526, 1);
 x_2608 = x_2526;
} else {
 lean_dec_ref(x_2526);
 x_2608 = lean_box(0);
}
if (lean_is_scalar(x_2608)) {
 x_2609 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2609 = x_2608;
}
lean_ctor_set(x_2609, 0, x_2606);
lean_ctor_set(x_2609, 1, x_2607);
return x_2609;
}
}
else
{
lean_object* x_2610; lean_object* x_2611; uint8_t x_2612; lean_object* x_2613; lean_object* x_2614; lean_object* x_2615; lean_object* x_2616; lean_object* x_2617; lean_object* x_2618; lean_object* x_2619; lean_object* x_2620; lean_object* x_2621; lean_object* x_2622; lean_object* x_2623; 
lean_dec(x_1978);
lean_dec(x_1896);
lean_dec(x_1887);
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_2610 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2610 = lean_box(0);
}
x_2611 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2611, 0, x_1979);
x_2612 = 1;
x_2613 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_2614 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_2611, x_2612, x_2613, x_4, x_5, x_6, x_7, x_1894, x_9, x_1897);
x_2615 = lean_ctor_get(x_2614, 0);
lean_inc(x_2615);
x_2616 = lean_ctor_get(x_2614, 1);
lean_inc(x_2616);
lean_dec(x_2614);
x_2617 = lean_unsigned_to_nat(1u);
x_2618 = lean_nat_add(x_15, x_2617);
lean_dec(x_15);
x_2619 = l_Lean_Expr_mvarId_x21(x_2615);
x_2620 = lean_array_push(x_17, x_2619);
if (lean_is_scalar(x_2610)) {
 x_2621 = lean_alloc_ctor(0, 8, 2);
} else {
 x_2621 = x_2610;
}
lean_ctor_set(x_2621, 0, x_11);
lean_ctor_set(x_2621, 1, x_12);
lean_ctor_set(x_2621, 2, x_13);
lean_ctor_set(x_2621, 3, x_2618);
lean_ctor_set(x_2621, 4, x_16);
lean_ctor_set(x_2621, 5, x_2620);
lean_ctor_set(x_2621, 6, x_18);
lean_ctor_set(x_2621, 7, x_19);
lean_ctor_set_uint8(x_2621, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2621, sizeof(void*)*8 + 1, x_1886);
lean_inc(x_2615);
x_2622 = l_Lean_mkApp(x_2, x_2615);
x_2623 = lean_expr_instantiate1(x_1980, x_2615);
lean_dec(x_2615);
lean_dec(x_1980);
x_1 = x_2621;
x_2 = x_2622;
x_3 = x_2623;
x_8 = x_1894;
x_10 = x_2616;
goto _start;
}
}
}
default: 
{
lean_object* x_2625; lean_object* x_2626; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_2625 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1896, x_4, x_5, x_6, x_7, x_1894, x_9, x_1897);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_2626 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2626 = lean_box(0);
}
if (lean_obj_tag(x_2625) == 0)
{
lean_object* x_2627; uint8_t x_2628; lean_object* x_2629; lean_object* x_2630; uint8_t x_2631; 
x_2627 = lean_ctor_get(x_2625, 1);
lean_inc(x_2627);
lean_dec(x_2625);
x_2628 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
if (lean_is_scalar(x_2626)) {
 x_2629 = lean_alloc_ctor(0, 8, 2);
} else {
 x_2629 = x_2626;
}
lean_ctor_set(x_2629, 0, x_11);
lean_ctor_set(x_2629, 1, x_12);
lean_ctor_set(x_2629, 2, x_13);
lean_ctor_set(x_2629, 3, x_15);
lean_ctor_set(x_2629, 4, x_16);
lean_ctor_set(x_2629, 5, x_17);
lean_ctor_set(x_2629, 6, x_18);
lean_ctor_set(x_2629, 7, x_19);
lean_ctor_set_uint8(x_2629, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2629, sizeof(void*)*8 + 1, x_2628);
x_2630 = lean_array_get_size(x_12);
x_2631 = lean_nat_dec_lt(x_15, x_2630);
lean_dec(x_2630);
if (x_2631 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_2632; 
x_2632 = l_Lean_Expr_getOptParamDefault_x3f(x_1979);
if (lean_obj_tag(x_2632) == 0)
{
lean_object* x_2633; 
x_2633 = l_Lean_Expr_getAutoParamTactic_x3f(x_1979);
if (lean_obj_tag(x_2633) == 0)
{
uint8_t x_2634; 
lean_dec(x_2629);
lean_dec(x_1980);
lean_dec(x_1979);
x_2634 = l_Array_isEmpty___rarg(x_16);
if (x_2634 == 0)
{
lean_object* x_2635; lean_object* x_2636; lean_object* x_2637; lean_object* x_2638; lean_object* x_2639; lean_object* x_2640; lean_object* x_2641; lean_object* x_2642; lean_object* x_2643; lean_object* x_2644; lean_object* x_2645; lean_object* x_2646; lean_object* x_2647; lean_object* x_2648; lean_object* x_2649; lean_object* x_2650; 
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_2635 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2635, 0, x_1978);
x_2636 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_2637 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2637, 0, x_2636);
lean_ctor_set(x_2637, 1, x_2635);
x_2638 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_2639 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2639, 0, x_2637);
lean_ctor_set(x_2639, 1, x_2638);
x_2640 = x_16;
x_2641 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_1982, x_2640);
x_2642 = x_2641;
x_2643 = l_Array_toList___rarg(x_2642);
lean_dec(x_2642);
x_2644 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_2643);
x_2645 = l_Array_HasRepr___rarg___closed__1;
x_2646 = lean_string_append(x_2645, x_2644);
lean_dec(x_2644);
x_2647 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2647, 0, x_2646);
x_2648 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2648, 0, x_2647);
x_2649 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2649, 0, x_2639);
lean_ctor_set(x_2649, 1, x_2648);
x_2650 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2649, x_4, x_5, x_6, x_7, x_1894, x_9, x_2627);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2650;
}
else
{
lean_object* x_2651; uint8_t x_2652; 
lean_dec(x_1978);
lean_dec(x_16);
x_2651 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2652 = l_Lean_checkTraceOption(x_1887, x_2651);
lean_dec(x_1887);
if (x_2652 == 0)
{
lean_object* x_2653; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2653 = x_2627;
goto block_2664;
}
else
{
lean_object* x_2665; lean_object* x_2666; 
x_2665 = lean_ctor_get(x_13, 0);
lean_inc(x_2665);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2666 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2665, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_2627);
if (lean_obj_tag(x_2666) == 0)
{
lean_object* x_2667; 
x_2667 = lean_ctor_get(x_2666, 1);
lean_inc(x_2667);
lean_dec(x_2666);
x_2653 = x_2667;
goto block_2664;
}
else
{
lean_object* x_2668; lean_object* x_2669; lean_object* x_2670; lean_object* x_2671; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2668 = lean_ctor_get(x_2666, 0);
lean_inc(x_2668);
x_2669 = lean_ctor_get(x_2666, 1);
lean_inc(x_2669);
if (lean_is_exclusive(x_2666)) {
 lean_ctor_release(x_2666, 0);
 lean_ctor_release(x_2666, 1);
 x_2670 = x_2666;
} else {
 lean_dec_ref(x_2666);
 x_2670 = lean_box(0);
}
if (lean_is_scalar(x_2670)) {
 x_2671 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2671 = x_2670;
}
lean_ctor_set(x_2671, 0, x_2668);
lean_ctor_set(x_2671, 1, x_2669);
return x_2671;
}
}
block_2664:
{
lean_object* x_2654; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2654 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2653);
lean_dec(x_17);
if (lean_obj_tag(x_2654) == 0)
{
lean_object* x_2655; lean_object* x_2656; lean_object* x_2657; lean_object* x_2658; lean_object* x_2659; 
x_2655 = lean_ctor_get(x_2654, 1);
lean_inc(x_2655);
lean_dec(x_2654);
lean_inc(x_2);
x_2656 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__18(x_2, x_11, x_19, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2655);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2657 = lean_ctor_get(x_2656, 1);
lean_inc(x_2657);
if (lean_is_exclusive(x_2656)) {
 lean_ctor_release(x_2656, 0);
 lean_ctor_release(x_2656, 1);
 x_2658 = x_2656;
} else {
 lean_dec_ref(x_2656);
 x_2658 = lean_box(0);
}
if (lean_is_scalar(x_2658)) {
 x_2659 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2659 = x_2658;
}
lean_ctor_set(x_2659, 0, x_2);
lean_ctor_set(x_2659, 1, x_2657);
return x_2659;
}
else
{
lean_object* x_2660; lean_object* x_2661; lean_object* x_2662; lean_object* x_2663; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2660 = lean_ctor_get(x_2654, 0);
lean_inc(x_2660);
x_2661 = lean_ctor_get(x_2654, 1);
lean_inc(x_2661);
if (lean_is_exclusive(x_2654)) {
 lean_ctor_release(x_2654, 0);
 lean_ctor_release(x_2654, 1);
 x_2662 = x_2654;
} else {
 lean_dec_ref(x_2654);
 x_2662 = lean_box(0);
}
if (lean_is_scalar(x_2662)) {
 x_2663 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2663 = x_2662;
}
lean_ctor_set(x_2663, 0, x_2660);
lean_ctor_set(x_2663, 1, x_2661);
return x_2663;
}
}
}
else
{
lean_object* x_2672; lean_object* x_2673; lean_object* x_2674; lean_object* x_2675; 
lean_inc(x_2);
x_2672 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2672, 0, x_2);
x_2673 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2651, x_2672, x_4, x_5, x_6, x_7, x_1894, x_9, x_2627);
x_2674 = lean_ctor_get(x_2673, 1);
lean_inc(x_2674);
lean_dec(x_2673);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2675 = x_2674;
goto block_2686;
}
else
{
lean_object* x_2687; lean_object* x_2688; 
x_2687 = lean_ctor_get(x_13, 0);
lean_inc(x_2687);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2688 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2687, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_2674);
if (lean_obj_tag(x_2688) == 0)
{
lean_object* x_2689; 
x_2689 = lean_ctor_get(x_2688, 1);
lean_inc(x_2689);
lean_dec(x_2688);
x_2675 = x_2689;
goto block_2686;
}
else
{
lean_object* x_2690; lean_object* x_2691; lean_object* x_2692; lean_object* x_2693; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2690 = lean_ctor_get(x_2688, 0);
lean_inc(x_2690);
x_2691 = lean_ctor_get(x_2688, 1);
lean_inc(x_2691);
if (lean_is_exclusive(x_2688)) {
 lean_ctor_release(x_2688, 0);
 lean_ctor_release(x_2688, 1);
 x_2692 = x_2688;
} else {
 lean_dec_ref(x_2688);
 x_2692 = lean_box(0);
}
if (lean_is_scalar(x_2692)) {
 x_2693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2693 = x_2692;
}
lean_ctor_set(x_2693, 0, x_2690);
lean_ctor_set(x_2693, 1, x_2691);
return x_2693;
}
}
block_2686:
{
lean_object* x_2676; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2676 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2675);
lean_dec(x_17);
if (lean_obj_tag(x_2676) == 0)
{
lean_object* x_2677; lean_object* x_2678; lean_object* x_2679; lean_object* x_2680; lean_object* x_2681; 
x_2677 = lean_ctor_get(x_2676, 1);
lean_inc(x_2677);
lean_dec(x_2676);
lean_inc(x_2);
x_2678 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__19(x_2, x_11, x_19, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2677);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2679 = lean_ctor_get(x_2678, 1);
lean_inc(x_2679);
if (lean_is_exclusive(x_2678)) {
 lean_ctor_release(x_2678, 0);
 lean_ctor_release(x_2678, 1);
 x_2680 = x_2678;
} else {
 lean_dec_ref(x_2678);
 x_2680 = lean_box(0);
}
if (lean_is_scalar(x_2680)) {
 x_2681 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2681 = x_2680;
}
lean_ctor_set(x_2681, 0, x_2);
lean_ctor_set(x_2681, 1, x_2679);
return x_2681;
}
else
{
lean_object* x_2682; lean_object* x_2683; lean_object* x_2684; lean_object* x_2685; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2682 = lean_ctor_get(x_2676, 0);
lean_inc(x_2682);
x_2683 = lean_ctor_get(x_2676, 1);
lean_inc(x_2683);
if (lean_is_exclusive(x_2676)) {
 lean_ctor_release(x_2676, 0);
 lean_ctor_release(x_2676, 1);
 x_2684 = x_2676;
} else {
 lean_dec_ref(x_2676);
 x_2684 = lean_box(0);
}
if (lean_is_scalar(x_2684)) {
 x_2685 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2685 = x_2684;
}
lean_ctor_set(x_2685, 0, x_2682);
lean_ctor_set(x_2685, 1, x_2683);
return x_2685;
}
}
}
}
}
else
{
lean_object* x_2694; 
lean_dec(x_1978);
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_2694 = lean_ctor_get(x_2633, 0);
lean_inc(x_2694);
lean_dec(x_2633);
if (lean_obj_tag(x_2694) == 4)
{
lean_object* x_2695; lean_object* x_2696; lean_object* x_2697; lean_object* x_2698; lean_object* x_2699; lean_object* x_2700; 
x_2695 = lean_ctor_get(x_2694, 0);
lean_inc(x_2695);
lean_dec(x_2694);
x_2696 = lean_st_ref_get(x_9, x_2627);
x_2697 = lean_ctor_get(x_2696, 0);
lean_inc(x_2697);
x_2698 = lean_ctor_get(x_2696, 1);
lean_inc(x_2698);
lean_dec(x_2696);
x_2699 = lean_ctor_get(x_2697, 0);
lean_inc(x_2699);
lean_dec(x_2697);
x_2700 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_2699, x_2695);
if (lean_obj_tag(x_2700) == 0)
{
lean_object* x_2701; lean_object* x_2702; lean_object* x_2703; lean_object* x_2704; 
lean_dec(x_2629);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_11);
lean_dec(x_2);
x_2701 = lean_ctor_get(x_2700, 0);
lean_inc(x_2701);
lean_dec(x_2700);
x_2702 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2702, 0, x_2701);
x_2703 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2703, 0, x_2702);
x_2704 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2703, x_4, x_5, x_6, x_7, x_1894, x_9, x_2698);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2704;
}
else
{
lean_object* x_2705; lean_object* x_2706; lean_object* x_2707; lean_object* x_2708; lean_object* x_2709; lean_object* x_2710; lean_object* x_2711; lean_object* x_2712; lean_object* x_2713; lean_object* x_2714; lean_object* x_2715; lean_object* x_2716; lean_object* x_2717; lean_object* x_2718; lean_object* x_2719; lean_object* x_2720; lean_object* x_2721; lean_object* x_2722; lean_object* x_2723; lean_object* x_2724; lean_object* x_2725; lean_object* x_2726; lean_object* x_2727; lean_object* x_2728; lean_object* x_2729; lean_object* x_2730; lean_object* x_2731; lean_object* x_2732; lean_object* x_2733; lean_object* x_2734; lean_object* x_2735; lean_object* x_2736; lean_object* x_2737; lean_object* x_2738; lean_object* x_2739; 
x_2705 = lean_ctor_get(x_2700, 0);
lean_inc(x_2705);
lean_dec(x_2700);
x_2706 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_1894, x_9, x_2698);
x_2707 = lean_ctor_get(x_2706, 1);
lean_inc(x_2707);
lean_dec(x_2706);
x_2708 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_2707);
x_2709 = lean_ctor_get(x_2708, 1);
lean_inc(x_2709);
lean_dec(x_2708);
x_2710 = l_Lean_Syntax_getArgs(x_2705);
lean_dec(x_2705);
x_2711 = l_Array_empty___closed__1;
x_2712 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2710, x_2710, x_1982, x_2711);
lean_dec(x_2710);
x_2713 = l_Lean_nullKind___closed__2;
x_2714 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2714, 0, x_2713);
lean_ctor_set(x_2714, 1, x_2712);
x_2715 = lean_array_push(x_2711, x_2714);
x_2716 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__17;
x_2717 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2717, 0, x_2716);
lean_ctor_set(x_2717, 1, x_2715);
x_2718 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_2719 = lean_array_push(x_2718, x_2717);
x_2720 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__20;
x_2721 = lean_array_push(x_2719, x_2720);
x_2722 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__19;
x_2723 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2723, 0, x_2722);
lean_ctor_set(x_2723, 1, x_2721);
x_2724 = lean_array_push(x_2711, x_2723);
x_2725 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2725, 0, x_2713);
lean_ctor_set(x_2725, 1, x_2724);
x_2726 = lean_array_push(x_2711, x_2725);
x_2727 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2727, 0, x_2716);
lean_ctor_set(x_2727, 1, x_2726);
x_2728 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_2729 = lean_array_push(x_2728, x_2727);
x_2730 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_2731 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2731, 0, x_2730);
lean_ctor_set(x_2731, 1, x_2729);
x_2732 = l_Lean_Syntax_copyInfo(x_2731, x_11);
lean_dec(x_11);
x_2733 = l_Lean_Expr_getAppNumArgsAux___main(x_1979, x_1982);
x_2734 = lean_nat_sub(x_2733, x_1982);
lean_dec(x_2733);
x_2735 = lean_unsigned_to_nat(1u);
x_2736 = lean_nat_sub(x_2734, x_2735);
lean_dec(x_2734);
x_2737 = l_Lean_Expr_getRevArg_x21___main(x_1979, x_2736);
lean_dec(x_1979);
x_2738 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2738, 0, x_2732);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2739 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2738, x_2737, x_4, x_5, x_6, x_7, x_1894, x_9, x_2709);
if (lean_obj_tag(x_2739) == 0)
{
lean_object* x_2740; lean_object* x_2741; lean_object* x_2742; lean_object* x_2743; 
x_2740 = lean_ctor_get(x_2739, 0);
lean_inc(x_2740);
x_2741 = lean_ctor_get(x_2739, 1);
lean_inc(x_2741);
lean_dec(x_2739);
lean_inc(x_2740);
x_2742 = l_Lean_mkApp(x_2, x_2740);
x_2743 = lean_expr_instantiate1(x_1980, x_2740);
lean_dec(x_2740);
lean_dec(x_1980);
x_1 = x_2629;
x_2 = x_2742;
x_3 = x_2743;
x_8 = x_1894;
x_10 = x_2741;
goto _start;
}
else
{
lean_object* x_2745; lean_object* x_2746; lean_object* x_2747; lean_object* x_2748; 
lean_dec(x_2629);
lean_dec(x_1980);
lean_dec(x_1894);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2745 = lean_ctor_get(x_2739, 0);
lean_inc(x_2745);
x_2746 = lean_ctor_get(x_2739, 1);
lean_inc(x_2746);
if (lean_is_exclusive(x_2739)) {
 lean_ctor_release(x_2739, 0);
 lean_ctor_release(x_2739, 1);
 x_2747 = x_2739;
} else {
 lean_dec_ref(x_2739);
 x_2747 = lean_box(0);
}
if (lean_is_scalar(x_2747)) {
 x_2748 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2748 = x_2747;
}
lean_ctor_set(x_2748, 0, x_2745);
lean_ctor_set(x_2748, 1, x_2746);
return x_2748;
}
}
}
else
{
lean_object* x_2749; lean_object* x_2750; 
lean_dec(x_2694);
lean_dec(x_2629);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_11);
lean_dec(x_2);
x_2749 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_2750 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2749, x_4, x_5, x_6, x_7, x_1894, x_9, x_2627);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2750;
}
}
}
else
{
lean_object* x_2751; lean_object* x_2752; lean_object* x_2753; 
lean_dec(x_1979);
lean_dec(x_1978);
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_2751 = lean_ctor_get(x_2632, 0);
lean_inc(x_2751);
lean_dec(x_2632);
lean_inc(x_2751);
x_2752 = l_Lean_mkApp(x_2, x_2751);
x_2753 = lean_expr_instantiate1(x_1980, x_2751);
lean_dec(x_2751);
lean_dec(x_1980);
x_1 = x_2629;
x_2 = x_2752;
x_3 = x_2753;
x_8 = x_1894;
x_10 = x_2627;
goto _start;
}
}
else
{
uint8_t x_2755; 
lean_dec(x_2629);
lean_dec(x_1980);
lean_dec(x_1979);
x_2755 = l_Array_isEmpty___rarg(x_16);
if (x_2755 == 0)
{
lean_object* x_2756; lean_object* x_2757; lean_object* x_2758; lean_object* x_2759; lean_object* x_2760; lean_object* x_2761; lean_object* x_2762; lean_object* x_2763; lean_object* x_2764; lean_object* x_2765; lean_object* x_2766; lean_object* x_2767; lean_object* x_2768; lean_object* x_2769; lean_object* x_2770; lean_object* x_2771; 
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_2756 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2756, 0, x_1978);
x_2757 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_2758 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2758, 0, x_2757);
lean_ctor_set(x_2758, 1, x_2756);
x_2759 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_2760 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2760, 0, x_2758);
lean_ctor_set(x_2760, 1, x_2759);
x_2761 = x_16;
x_2762 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_1982, x_2761);
x_2763 = x_2762;
x_2764 = l_Array_toList___rarg(x_2763);
lean_dec(x_2763);
x_2765 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_2764);
x_2766 = l_Array_HasRepr___rarg___closed__1;
x_2767 = lean_string_append(x_2766, x_2765);
lean_dec(x_2765);
x_2768 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2768, 0, x_2767);
x_2769 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2769, 0, x_2768);
x_2770 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_2770, 0, x_2760);
lean_ctor_set(x_2770, 1, x_2769);
x_2771 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2770, x_4, x_5, x_6, x_7, x_1894, x_9, x_2627);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2771;
}
else
{
lean_object* x_2772; uint8_t x_2773; 
lean_dec(x_1978);
lean_dec(x_16);
x_2772 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2773 = l_Lean_checkTraceOption(x_1887, x_2772);
lean_dec(x_1887);
if (x_2773 == 0)
{
lean_object* x_2774; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2774 = x_2627;
goto block_2785;
}
else
{
lean_object* x_2786; lean_object* x_2787; 
x_2786 = lean_ctor_get(x_13, 0);
lean_inc(x_2786);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2787 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2786, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_2627);
if (lean_obj_tag(x_2787) == 0)
{
lean_object* x_2788; 
x_2788 = lean_ctor_get(x_2787, 1);
lean_inc(x_2788);
lean_dec(x_2787);
x_2774 = x_2788;
goto block_2785;
}
else
{
lean_object* x_2789; lean_object* x_2790; lean_object* x_2791; lean_object* x_2792; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2789 = lean_ctor_get(x_2787, 0);
lean_inc(x_2789);
x_2790 = lean_ctor_get(x_2787, 1);
lean_inc(x_2790);
if (lean_is_exclusive(x_2787)) {
 lean_ctor_release(x_2787, 0);
 lean_ctor_release(x_2787, 1);
 x_2791 = x_2787;
} else {
 lean_dec_ref(x_2787);
 x_2791 = lean_box(0);
}
if (lean_is_scalar(x_2791)) {
 x_2792 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2792 = x_2791;
}
lean_ctor_set(x_2792, 0, x_2789);
lean_ctor_set(x_2792, 1, x_2790);
return x_2792;
}
}
block_2785:
{
lean_object* x_2775; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2775 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2774);
lean_dec(x_17);
if (lean_obj_tag(x_2775) == 0)
{
lean_object* x_2776; lean_object* x_2777; lean_object* x_2778; lean_object* x_2779; lean_object* x_2780; 
x_2776 = lean_ctor_get(x_2775, 1);
lean_inc(x_2776);
lean_dec(x_2775);
lean_inc(x_2);
x_2777 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__20(x_2, x_11, x_19, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2776);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2778 = lean_ctor_get(x_2777, 1);
lean_inc(x_2778);
if (lean_is_exclusive(x_2777)) {
 lean_ctor_release(x_2777, 0);
 lean_ctor_release(x_2777, 1);
 x_2779 = x_2777;
} else {
 lean_dec_ref(x_2777);
 x_2779 = lean_box(0);
}
if (lean_is_scalar(x_2779)) {
 x_2780 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2780 = x_2779;
}
lean_ctor_set(x_2780, 0, x_2);
lean_ctor_set(x_2780, 1, x_2778);
return x_2780;
}
else
{
lean_object* x_2781; lean_object* x_2782; lean_object* x_2783; lean_object* x_2784; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2781 = lean_ctor_get(x_2775, 0);
lean_inc(x_2781);
x_2782 = lean_ctor_get(x_2775, 1);
lean_inc(x_2782);
if (lean_is_exclusive(x_2775)) {
 lean_ctor_release(x_2775, 0);
 lean_ctor_release(x_2775, 1);
 x_2783 = x_2775;
} else {
 lean_dec_ref(x_2775);
 x_2783 = lean_box(0);
}
if (lean_is_scalar(x_2783)) {
 x_2784 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2784 = x_2783;
}
lean_ctor_set(x_2784, 0, x_2781);
lean_ctor_set(x_2784, 1, x_2782);
return x_2784;
}
}
}
else
{
lean_object* x_2793; lean_object* x_2794; lean_object* x_2795; lean_object* x_2796; 
lean_inc(x_2);
x_2793 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2793, 0, x_2);
x_2794 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2772, x_2793, x_4, x_5, x_6, x_7, x_1894, x_9, x_2627);
x_2795 = lean_ctor_get(x_2794, 1);
lean_inc(x_2795);
lean_dec(x_2794);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2796 = x_2795;
goto block_2807;
}
else
{
lean_object* x_2808; lean_object* x_2809; 
x_2808 = lean_ctor_get(x_13, 0);
lean_inc(x_2808);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2809 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2808, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_2795);
if (lean_obj_tag(x_2809) == 0)
{
lean_object* x_2810; 
x_2810 = lean_ctor_get(x_2809, 1);
lean_inc(x_2810);
lean_dec(x_2809);
x_2796 = x_2810;
goto block_2807;
}
else
{
lean_object* x_2811; lean_object* x_2812; lean_object* x_2813; lean_object* x_2814; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2811 = lean_ctor_get(x_2809, 0);
lean_inc(x_2811);
x_2812 = lean_ctor_get(x_2809, 1);
lean_inc(x_2812);
if (lean_is_exclusive(x_2809)) {
 lean_ctor_release(x_2809, 0);
 lean_ctor_release(x_2809, 1);
 x_2813 = x_2809;
} else {
 lean_dec_ref(x_2809);
 x_2813 = lean_box(0);
}
if (lean_is_scalar(x_2813)) {
 x_2814 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2814 = x_2813;
}
lean_ctor_set(x_2814, 0, x_2811);
lean_ctor_set(x_2814, 1, x_2812);
return x_2814;
}
}
block_2807:
{
lean_object* x_2797; 
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2797 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2796);
lean_dec(x_17);
if (lean_obj_tag(x_2797) == 0)
{
lean_object* x_2798; lean_object* x_2799; lean_object* x_2800; lean_object* x_2801; lean_object* x_2802; 
x_2798 = lean_ctor_get(x_2797, 1);
lean_inc(x_2798);
lean_dec(x_2797);
lean_inc(x_2);
x_2799 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__21(x_2, x_11, x_19, x_1982, x_4, x_5, x_6, x_7, x_1894, x_9, x_2798);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2800 = lean_ctor_get(x_2799, 1);
lean_inc(x_2800);
if (lean_is_exclusive(x_2799)) {
 lean_ctor_release(x_2799, 0);
 lean_ctor_release(x_2799, 1);
 x_2801 = x_2799;
} else {
 lean_dec_ref(x_2799);
 x_2801 = lean_box(0);
}
if (lean_is_scalar(x_2801)) {
 x_2802 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2802 = x_2801;
}
lean_ctor_set(x_2802, 0, x_2);
lean_ctor_set(x_2802, 1, x_2800);
return x_2802;
}
else
{
lean_object* x_2803; lean_object* x_2804; lean_object* x_2805; lean_object* x_2806; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2803 = lean_ctor_get(x_2797, 0);
lean_inc(x_2803);
x_2804 = lean_ctor_get(x_2797, 1);
lean_inc(x_2804);
if (lean_is_exclusive(x_2797)) {
 lean_ctor_release(x_2797, 0);
 lean_ctor_release(x_2797, 1);
 x_2805 = x_2797;
} else {
 lean_dec_ref(x_2797);
 x_2805 = lean_box(0);
}
if (lean_is_scalar(x_2805)) {
 x_2806 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2806 = x_2805;
}
lean_ctor_set(x_2806, 0, x_2803);
lean_ctor_set(x_2806, 1, x_2804);
return x_2806;
}
}
}
}
}
}
else
{
lean_object* x_2815; lean_object* x_2816; 
lean_dec(x_2629);
lean_dec(x_1978);
lean_dec(x_1887);
lean_dec(x_3);
x_2815 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2816 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2815, x_1979, x_4, x_5, x_6, x_7, x_1894, x_9, x_2627);
if (lean_obj_tag(x_2816) == 0)
{
lean_object* x_2817; lean_object* x_2818; lean_object* x_2819; lean_object* x_2820; lean_object* x_2821; lean_object* x_2822; lean_object* x_2823; 
x_2817 = lean_ctor_get(x_2816, 0);
lean_inc(x_2817);
x_2818 = lean_ctor_get(x_2816, 1);
lean_inc(x_2818);
lean_dec(x_2816);
x_2819 = lean_unsigned_to_nat(1u);
x_2820 = lean_nat_add(x_15, x_2819);
lean_dec(x_15);
x_2821 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_2821, 0, x_11);
lean_ctor_set(x_2821, 1, x_12);
lean_ctor_set(x_2821, 2, x_13);
lean_ctor_set(x_2821, 3, x_2820);
lean_ctor_set(x_2821, 4, x_16);
lean_ctor_set(x_2821, 5, x_17);
lean_ctor_set(x_2821, 6, x_18);
lean_ctor_set(x_2821, 7, x_19);
lean_ctor_set_uint8(x_2821, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2821, sizeof(void*)*8 + 1, x_2628);
lean_inc(x_2817);
x_2822 = l_Lean_mkApp(x_2, x_2817);
x_2823 = lean_expr_instantiate1(x_1980, x_2817);
lean_dec(x_2817);
lean_dec(x_1980);
x_1 = x_2821;
x_2 = x_2822;
x_3 = x_2823;
x_8 = x_1894;
x_10 = x_2818;
goto _start;
}
else
{
lean_object* x_2825; lean_object* x_2826; lean_object* x_2827; lean_object* x_2828; 
lean_dec(x_1980);
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2825 = lean_ctor_get(x_2816, 0);
lean_inc(x_2825);
x_2826 = lean_ctor_get(x_2816, 1);
lean_inc(x_2826);
if (lean_is_exclusive(x_2816)) {
 lean_ctor_release(x_2816, 0);
 lean_ctor_release(x_2816, 1);
 x_2827 = x_2816;
} else {
 lean_dec_ref(x_2816);
 x_2827 = lean_box(0);
}
if (lean_is_scalar(x_2827)) {
 x_2828 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2828 = x_2827;
}
lean_ctor_set(x_2828, 0, x_2825);
lean_ctor_set(x_2828, 1, x_2826);
return x_2828;
}
}
}
else
{
lean_object* x_2829; lean_object* x_2830; lean_object* x_2831; lean_object* x_2832; 
lean_dec(x_2626);
lean_dec(x_1980);
lean_dec(x_1979);
lean_dec(x_1978);
lean_dec(x_1894);
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2829 = lean_ctor_get(x_2625, 0);
lean_inc(x_2829);
x_2830 = lean_ctor_get(x_2625, 1);
lean_inc(x_2830);
if (lean_is_exclusive(x_2625)) {
 lean_ctor_release(x_2625, 0);
 lean_ctor_release(x_2625, 1);
 x_2831 = x_2625;
} else {
 lean_dec_ref(x_2625);
 x_2831 = lean_box(0);
}
if (lean_is_scalar(x_2831)) {
 x_2832 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2832 = x_2831;
}
lean_ctor_set(x_2832, 0, x_2829);
lean_ctor_set(x_2832, 1, x_2830);
return x_2832;
}
}
}
}
else
{
lean_object* x_2833; lean_object* x_2834; lean_object* x_2835; lean_object* x_2836; lean_object* x_2837; lean_object* x_2838; 
lean_dec(x_1978);
lean_dec(x_1887);
lean_dec(x_3);
x_2833 = lean_ctor_get(x_1983, 0);
lean_inc(x_2833);
lean_dec(x_1983);
x_2834 = l_Lean_Elab_Term_NamedArg_inhabited;
x_2835 = lean_array_get(x_2834, x_16, x_2833);
x_2836 = l_Array_eraseIdx___rarg(x_16, x_2833);
lean_dec(x_2833);
x_2837 = lean_ctor_get(x_2835, 1);
lean_inc(x_2837);
lean_dec(x_2835);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2838 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2837, x_1979, x_4, x_5, x_6, x_7, x_1894, x_9, x_1897);
if (lean_obj_tag(x_2838) == 0)
{
lean_object* x_2839; lean_object* x_2840; lean_object* x_2841; lean_object* x_2842; 
x_2839 = lean_ctor_get(x_2838, 0);
lean_inc(x_2839);
x_2840 = lean_ctor_get(x_2838, 1);
lean_inc(x_2840);
lean_dec(x_2838);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_2841 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1896, x_4, x_5, x_6, x_7, x_1894, x_9, x_2840);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_2842 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2842 = lean_box(0);
}
if (lean_obj_tag(x_2841) == 0)
{
lean_object* x_2843; uint8_t x_2844; lean_object* x_2845; lean_object* x_2846; lean_object* x_2847; 
x_2843 = lean_ctor_get(x_2841, 1);
lean_inc(x_2843);
lean_dec(x_2841);
x_2844 = 1;
if (lean_is_scalar(x_2842)) {
 x_2845 = lean_alloc_ctor(0, 8, 2);
} else {
 x_2845 = x_2842;
}
lean_ctor_set(x_2845, 0, x_11);
lean_ctor_set(x_2845, 1, x_12);
lean_ctor_set(x_2845, 2, x_13);
lean_ctor_set(x_2845, 3, x_15);
lean_ctor_set(x_2845, 4, x_2836);
lean_ctor_set(x_2845, 5, x_17);
lean_ctor_set(x_2845, 6, x_18);
lean_ctor_set(x_2845, 7, x_19);
lean_ctor_set_uint8(x_2845, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2845, sizeof(void*)*8 + 1, x_2844);
lean_inc(x_2839);
x_2846 = l_Lean_mkApp(x_2, x_2839);
x_2847 = lean_expr_instantiate1(x_1980, x_2839);
lean_dec(x_2839);
lean_dec(x_1980);
x_1 = x_2845;
x_2 = x_2846;
x_3 = x_2847;
x_8 = x_1894;
x_10 = x_2843;
goto _start;
}
else
{
lean_object* x_2849; lean_object* x_2850; lean_object* x_2851; lean_object* x_2852; 
lean_dec(x_2842);
lean_dec(x_2839);
lean_dec(x_2836);
lean_dec(x_1980);
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2849 = lean_ctor_get(x_2841, 0);
lean_inc(x_2849);
x_2850 = lean_ctor_get(x_2841, 1);
lean_inc(x_2850);
if (lean_is_exclusive(x_2841)) {
 lean_ctor_release(x_2841, 0);
 lean_ctor_release(x_2841, 1);
 x_2851 = x_2841;
} else {
 lean_dec_ref(x_2841);
 x_2851 = lean_box(0);
}
if (lean_is_scalar(x_2851)) {
 x_2852 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2852 = x_2851;
}
lean_ctor_set(x_2852, 0, x_2849);
lean_ctor_set(x_2852, 1, x_2850);
return x_2852;
}
}
else
{
lean_object* x_2853; lean_object* x_2854; lean_object* x_2855; lean_object* x_2856; 
lean_dec(x_2836);
lean_dec(x_1980);
lean_dec(x_1896);
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_2853 = lean_ctor_get(x_2838, 0);
lean_inc(x_2853);
x_2854 = lean_ctor_get(x_2838, 1);
lean_inc(x_2854);
if (lean_is_exclusive(x_2838)) {
 lean_ctor_release(x_2838, 0);
 lean_ctor_release(x_2838, 1);
 x_2855 = x_2838;
} else {
 lean_dec_ref(x_2838);
 x_2855 = lean_box(0);
}
if (lean_is_scalar(x_2855)) {
 x_2856 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2856 = x_2855;
}
lean_ctor_set(x_2856, 0, x_2853);
lean_ctor_set(x_2856, 1, x_2854);
return x_2856;
}
}
}
else
{
lean_object* x_2857; 
lean_dec(x_18);
x_2857 = lean_box(0);
x_1898 = x_2857;
goto block_1977;
}
block_1977:
{
uint8_t x_1899; 
lean_dec(x_1898);
x_1899 = l_Array_isEmpty___rarg(x_16);
lean_dec(x_16);
if (x_1899 == 0)
{
lean_object* x_1900; 
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1900 = l___private_Lean_Elab_App_4__tryCoeFun(x_1896, x_2, x_4, x_5, x_6, x_7, x_1894, x_9, x_1897);
if (lean_obj_tag(x_1900) == 0)
{
lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; 
x_1901 = lean_ctor_get(x_1900, 0);
lean_inc(x_1901);
x_1902 = lean_ctor_get(x_1900, 1);
lean_inc(x_1902);
lean_dec(x_1900);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1901);
x_1903 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_1901, x_4, x_5, x_6, x_7, x_1894, x_9, x_1902);
if (lean_obj_tag(x_1903) == 0)
{
lean_object* x_1904; lean_object* x_1905; 
x_1904 = lean_ctor_get(x_1903, 0);
lean_inc(x_1904);
x_1905 = lean_ctor_get(x_1903, 1);
lean_inc(x_1905);
lean_dec(x_1903);
x_2 = x_1901;
x_3 = x_1904;
x_8 = x_1894;
x_10 = x_1905;
goto _start;
}
else
{
lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; 
lean_dec(x_1901);
lean_dec(x_1894);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1907 = lean_ctor_get(x_1903, 0);
lean_inc(x_1907);
x_1908 = lean_ctor_get(x_1903, 1);
lean_inc(x_1908);
if (lean_is_exclusive(x_1903)) {
 lean_ctor_release(x_1903, 0);
 lean_ctor_release(x_1903, 1);
 x_1909 = x_1903;
} else {
 lean_dec_ref(x_1903);
 x_1909 = lean_box(0);
}
if (lean_is_scalar(x_1909)) {
 x_1910 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1910 = x_1909;
}
lean_ctor_set(x_1910, 0, x_1907);
lean_ctor_set(x_1910, 1, x_1908);
return x_1910;
}
}
else
{
lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; 
lean_dec(x_1894);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1911 = lean_ctor_get(x_1900, 0);
lean_inc(x_1911);
x_1912 = lean_ctor_get(x_1900, 1);
lean_inc(x_1912);
if (lean_is_exclusive(x_1900)) {
 lean_ctor_release(x_1900, 0);
 lean_ctor_release(x_1900, 1);
 x_1913 = x_1900;
} else {
 lean_dec_ref(x_1900);
 x_1913 = lean_box(0);
}
if (lean_is_scalar(x_1913)) {
 x_1914 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1914 = x_1913;
}
lean_ctor_set(x_1914, 0, x_1911);
lean_ctor_set(x_1914, 1, x_1912);
return x_1914;
}
}
else
{
lean_object* x_1915; uint8_t x_1916; 
x_1915 = lean_array_get_size(x_12);
lean_dec(x_12);
x_1916 = lean_nat_dec_eq(x_15, x_1915);
lean_dec(x_1915);
lean_dec(x_15);
if (x_1916 == 0)
{
lean_object* x_1917; 
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1917 = l___private_Lean_Elab_App_4__tryCoeFun(x_1896, x_2, x_4, x_5, x_6, x_7, x_1894, x_9, x_1897);
if (lean_obj_tag(x_1917) == 0)
{
lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; 
x_1918 = lean_ctor_get(x_1917, 0);
lean_inc(x_1918);
x_1919 = lean_ctor_get(x_1917, 1);
lean_inc(x_1919);
lean_dec(x_1917);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1918);
x_1920 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_1918, x_4, x_5, x_6, x_7, x_1894, x_9, x_1919);
if (lean_obj_tag(x_1920) == 0)
{
lean_object* x_1921; lean_object* x_1922; 
x_1921 = lean_ctor_get(x_1920, 0);
lean_inc(x_1921);
x_1922 = lean_ctor_get(x_1920, 1);
lean_inc(x_1922);
lean_dec(x_1920);
x_2 = x_1918;
x_3 = x_1921;
x_8 = x_1894;
x_10 = x_1922;
goto _start;
}
else
{
lean_object* x_1924; lean_object* x_1925; lean_object* x_1926; lean_object* x_1927; 
lean_dec(x_1918);
lean_dec(x_1894);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1924 = lean_ctor_get(x_1920, 0);
lean_inc(x_1924);
x_1925 = lean_ctor_get(x_1920, 1);
lean_inc(x_1925);
if (lean_is_exclusive(x_1920)) {
 lean_ctor_release(x_1920, 0);
 lean_ctor_release(x_1920, 1);
 x_1926 = x_1920;
} else {
 lean_dec_ref(x_1920);
 x_1926 = lean_box(0);
}
if (lean_is_scalar(x_1926)) {
 x_1927 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1927 = x_1926;
}
lean_ctor_set(x_1927, 0, x_1924);
lean_ctor_set(x_1927, 1, x_1925);
return x_1927;
}
}
else
{
lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; 
lean_dec(x_1894);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_1928 = lean_ctor_get(x_1917, 0);
lean_inc(x_1928);
x_1929 = lean_ctor_get(x_1917, 1);
lean_inc(x_1929);
if (lean_is_exclusive(x_1917)) {
 lean_ctor_release(x_1917, 0);
 lean_ctor_release(x_1917, 1);
 x_1930 = x_1917;
} else {
 lean_dec_ref(x_1917);
 x_1930 = lean_box(0);
}
if (lean_is_scalar(x_1930)) {
 x_1931 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1931 = x_1930;
}
lean_ctor_set(x_1931, 0, x_1928);
lean_ctor_set(x_1931, 1, x_1929);
return x_1931;
}
}
else
{
lean_object* x_1932; uint8_t x_1933; 
lean_dec(x_1896);
lean_dec(x_1);
x_1932 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1933 = l_Lean_checkTraceOption(x_1887, x_1932);
lean_dec(x_1887);
if (x_1933 == 0)
{
lean_object* x_1934; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1934 = x_1897;
goto block_1946;
}
else
{
lean_object* x_1947; lean_object* x_1948; 
x_1947 = lean_ctor_get(x_13, 0);
lean_inc(x_1947);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1948 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1947, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_1897);
if (lean_obj_tag(x_1948) == 0)
{
lean_object* x_1949; 
x_1949 = lean_ctor_get(x_1948, 1);
lean_inc(x_1949);
lean_dec(x_1948);
x_1934 = x_1949;
goto block_1946;
}
else
{
lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1950 = lean_ctor_get(x_1948, 0);
lean_inc(x_1950);
x_1951 = lean_ctor_get(x_1948, 1);
lean_inc(x_1951);
if (lean_is_exclusive(x_1948)) {
 lean_ctor_release(x_1948, 0);
 lean_ctor_release(x_1948, 1);
 x_1952 = x_1948;
} else {
 lean_dec_ref(x_1948);
 x_1952 = lean_box(0);
}
if (lean_is_scalar(x_1952)) {
 x_1953 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1953 = x_1952;
}
lean_ctor_set(x_1953, 0, x_1950);
lean_ctor_set(x_1953, 1, x_1951);
return x_1953;
}
}
block_1946:
{
lean_object* x_1935; lean_object* x_1936; 
x_1935 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1936 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1935, x_4, x_5, x_6, x_7, x_1894, x_9, x_1934);
lean_dec(x_17);
if (lean_obj_tag(x_1936) == 0)
{
lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; 
x_1937 = lean_ctor_get(x_1936, 1);
lean_inc(x_1937);
lean_dec(x_1936);
lean_inc(x_2);
x_1938 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(x_2, x_11, x_19, x_1935, x_4, x_5, x_6, x_7, x_1894, x_9, x_1937);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1939 = lean_ctor_get(x_1938, 1);
lean_inc(x_1939);
if (lean_is_exclusive(x_1938)) {
 lean_ctor_release(x_1938, 0);
 lean_ctor_release(x_1938, 1);
 x_1940 = x_1938;
} else {
 lean_dec_ref(x_1938);
 x_1940 = lean_box(0);
}
if (lean_is_scalar(x_1940)) {
 x_1941 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1941 = x_1940;
}
lean_ctor_set(x_1941, 0, x_2);
lean_ctor_set(x_1941, 1, x_1939);
return x_1941;
}
else
{
lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1942 = lean_ctor_get(x_1936, 0);
lean_inc(x_1942);
x_1943 = lean_ctor_get(x_1936, 1);
lean_inc(x_1943);
if (lean_is_exclusive(x_1936)) {
 lean_ctor_release(x_1936, 0);
 lean_ctor_release(x_1936, 1);
 x_1944 = x_1936;
} else {
 lean_dec_ref(x_1936);
 x_1944 = lean_box(0);
}
if (lean_is_scalar(x_1944)) {
 x_1945 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1945 = x_1944;
}
lean_ctor_set(x_1945, 0, x_1942);
lean_ctor_set(x_1945, 1, x_1943);
return x_1945;
}
}
}
else
{
lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; 
lean_inc(x_2);
x_1954 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1954, 0, x_2);
x_1955 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1932, x_1954, x_4, x_5, x_6, x_7, x_1894, x_9, x_1897);
x_1956 = lean_ctor_get(x_1955, 1);
lean_inc(x_1956);
lean_dec(x_1955);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1957 = x_1956;
goto block_1969;
}
else
{
lean_object* x_1970; lean_object* x_1971; 
x_1970 = lean_ctor_get(x_13, 0);
lean_inc(x_1970);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1971 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1970, x_3, x_4, x_5, x_6, x_7, x_1894, x_9, x_1956);
if (lean_obj_tag(x_1971) == 0)
{
lean_object* x_1972; 
x_1972 = lean_ctor_get(x_1971, 1);
lean_inc(x_1972);
lean_dec(x_1971);
x_1957 = x_1972;
goto block_1969;
}
else
{
lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; lean_object* x_1976; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1973 = lean_ctor_get(x_1971, 0);
lean_inc(x_1973);
x_1974 = lean_ctor_get(x_1971, 1);
lean_inc(x_1974);
if (lean_is_exclusive(x_1971)) {
 lean_ctor_release(x_1971, 0);
 lean_ctor_release(x_1971, 1);
 x_1975 = x_1971;
} else {
 lean_dec_ref(x_1971);
 x_1975 = lean_box(0);
}
if (lean_is_scalar(x_1975)) {
 x_1976 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1976 = x_1975;
}
lean_ctor_set(x_1976, 0, x_1973);
lean_ctor_set(x_1976, 1, x_1974);
return x_1976;
}
}
block_1969:
{
lean_object* x_1958; lean_object* x_1959; 
x_1958 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_1894);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1959 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1958, x_4, x_5, x_6, x_7, x_1894, x_9, x_1957);
lean_dec(x_17);
if (lean_obj_tag(x_1959) == 0)
{
lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; lean_object* x_1964; 
x_1960 = lean_ctor_get(x_1959, 1);
lean_inc(x_1960);
lean_dec(x_1959);
lean_inc(x_2);
x_1961 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_2, x_11, x_19, x_1958, x_4, x_5, x_6, x_7, x_1894, x_9, x_1960);
lean_dec(x_9);
lean_dec(x_1894);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1962 = lean_ctor_get(x_1961, 1);
lean_inc(x_1962);
if (lean_is_exclusive(x_1961)) {
 lean_ctor_release(x_1961, 0);
 lean_ctor_release(x_1961, 1);
 x_1963 = x_1961;
} else {
 lean_dec_ref(x_1961);
 x_1963 = lean_box(0);
}
if (lean_is_scalar(x_1963)) {
 x_1964 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1964 = x_1963;
}
lean_ctor_set(x_1964, 0, x_2);
lean_ctor_set(x_1964, 1, x_1962);
return x_1964;
}
else
{
lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; lean_object* x_1968; 
lean_dec(x_1894);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1965 = lean_ctor_get(x_1959, 0);
lean_inc(x_1965);
x_1966 = lean_ctor_get(x_1959, 1);
lean_inc(x_1966);
if (lean_is_exclusive(x_1959)) {
 lean_ctor_release(x_1959, 0);
 lean_ctor_release(x_1959, 1);
 x_1967 = x_1959;
} else {
 lean_dec_ref(x_1959);
 x_1967 = lean_box(0);
}
if (lean_is_scalar(x_1967)) {
 x_1968 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1968 = x_1967;
}
lean_ctor_set(x_1968, 0, x_1965);
lean_ctor_set(x_1968, 1, x_1966);
return x_1968;
}
}
}
}
}
}
}
else
{
lean_object* x_2858; lean_object* x_2859; lean_object* x_2860; lean_object* x_2861; 
lean_dec(x_1894);
lean_dec(x_1887);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_2858 = lean_ctor_get(x_1895, 0);
lean_inc(x_2858);
x_2859 = lean_ctor_get(x_1895, 1);
lean_inc(x_2859);
if (lean_is_exclusive(x_1895)) {
 lean_ctor_release(x_1895, 0);
 lean_ctor_release(x_1895, 1);
 x_2860 = x_1895;
} else {
 lean_dec_ref(x_1895);
 x_2860 = lean_box(0);
}
if (lean_is_scalar(x_2860)) {
 x_2861 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2861 = x_2860;
}
lean_ctor_set(x_2861, 0, x_2858);
lean_ctor_set(x_2861, 1, x_2859);
return x_2861;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__15(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__20(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__21(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("args");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1;
x_2 = l___private_Lean_Elab_App_11__elabAppArgs___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit: ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_11__elabAppArgs___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_11__elabAppArgs___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_11__elabAppArgs___closed__5;
x_2 = l___private_Lean_Elab_App_11__elabAppArgs___closed__6;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_11__elabAppArgs___closed__7;
x_2 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_repr___main___closed__16;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_11__elabAppArgs___closed__5;
x_2 = l___private_Lean_Elab_App_11__elabAppArgs___closed__9;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_11__elabAppArgs___closed__10;
x_2 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_11__elabAppArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_6);
x_16 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_53 = lean_ctor_get(x_10, 0);
lean_inc(x_53);
x_54 = l___private_Lean_Elab_App_11__elabAppArgs___closed__2;
x_55 = l_Lean_checkTraceOption(x_53, x_54);
lean_dec(x_53);
if (x_55 == 0)
{
x_19 = x_18;
goto block_52;
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_inc(x_1);
x_56 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_56, 0, x_1);
lean_inc(x_17);
x_57 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_57, 0, x_17);
if (x_5 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = l___private_Lean_Elab_App_11__elabAppArgs___closed__8;
x_59 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
x_60 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_61 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
x_63 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_54, x_62, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_19 = x_64;
goto block_52;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = l___private_Lean_Elab_App_11__elabAppArgs___closed__11;
x_66 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_56);
x_67 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_68 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_57);
x_70 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_54, x_69, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_19 = x_71;
goto block_52;
}
}
block_52:
{
uint8_t x_20; 
x_20 = l_Array_isEmpty___rarg(x_2);
if (x_20 == 0)
{
lean_object* x_21; 
lean_inc(x_6);
lean_inc(x_17);
x_21 = l_Lean_Elab_Term_tryPostponeIfMVar(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_10, 3);
lean_inc(x_23);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_empty___closed__1;
x_26 = 0;
x_27 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set(x_27, 2, x_4);
lean_ctor_set(x_27, 3, x_24);
lean_ctor_set(x_27, 4, x_2);
lean_ctor_set(x_27, 5, x_25);
lean_ctor_set(x_27, 6, x_25);
lean_ctor_set(x_27, 7, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*8, x_5);
lean_ctor_set_uint8(x_27, sizeof(void*)*8 + 1, x_26);
x_28 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_27, x_1, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
uint8_t x_33; 
x_33 = l_Array_isEmpty___rarg(x_3);
if (x_33 == 0)
{
lean_object* x_34; 
lean_inc(x_6);
lean_inc(x_17);
x_34 = l_Lean_Elab_Term_tryPostponeIfMVar(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_10, 3);
lean_inc(x_36);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Array_empty___closed__1;
x_39 = 0;
x_40 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_3);
lean_ctor_set(x_40, 2, x_4);
lean_ctor_set(x_40, 3, x_37);
lean_ctor_set(x_40, 4, x_2);
lean_ctor_set(x_40, 5, x_38);
lean_ctor_set(x_40, 6, x_38);
lean_ctor_set(x_40, 7, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*8, x_5);
lean_ctor_set_uint8(x_40, sizeof(void*)*8 + 1, x_39);
x_41 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_40, x_1, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_10, 3);
lean_inc(x_46);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Array_empty___closed__1;
x_49 = 0;
x_50 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_3);
lean_ctor_set(x_50, 2, x_4);
lean_ctor_set(x_50, 3, x_47);
lean_ctor_set(x_50, 4, x_2);
lean_ctor_set(x_50, 5, x_48);
lean_ctor_set(x_50, 6, x_48);
lean_ctor_set(x_50, 7, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*8, x_5);
lean_ctor_set_uint8(x_50, sizeof(void*)*8 + 1, x_49);
x_51 = l___private_Lean_Elab_App_10__elabAppArgsAux___main(x_50, x_1, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
return x_51;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_13);
if (x_72 == 0)
{
return x_13;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_13, 0);
x_74 = lean_ctor_get(x_13, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_13);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l___private_Lean_Elab_App_11__elabAppArgs(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l___private_Lean_Elab_App_12__throwLValError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = l_Lean_indentExpr(x_1);
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_MessageData_ofList___closed__3;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_KernelException_toMessageData___closed__12;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_indentExpr(x_2);
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
}
lean_object* l___private_Lean_Elab_App_12__throwLValError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_12__throwLValError___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_12__throwLValError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_13__findMethod_x3f___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l___private_Lean_Elab_App_13__findMethod_x3f___main(x_1, x_8, x_2);
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
lean_object* l___private_Lean_Elab_App_13__findMethod_x3f___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_12 = l_Array_findSomeMAux___main___at___private_Lean_Elab_App_13__findMethod_x3f___main___spec__1(x_1, x_3, x_10, x_11);
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
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_13__findMethod_x3f___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeMAux___main___at___private_Lean_Elab_App_13__findMethod_x3f___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_13__findMethod_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_App_13__findMethod_x3f___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, type is not of the form (C ...) where C is a constant");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [..] notation, type is not of the form (C ...) where C is a constant");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure has only ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" field(s)");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, structure expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid projection, index must be greater than 0");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__20;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a valid \"field\" because environment does not contain '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__22;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__23;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("getOp");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [..] notation because environment does not contain '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__26;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_14__resolveLValAux___closed__27;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_14__resolveLValAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_49 = l___private_Lean_Elab_App_14__resolveLValAux___closed__15;
x_50 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_49, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
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
x_36 = l___private_Lean_Elab_App_14__resolveLValAux___closed__9;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l___private_Lean_Elab_App_14__resolveLValAux___closed__12;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
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
x_55 = l___private_Lean_Elab_App_14__resolveLValAux___closed__18;
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
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_free_object(x_63);
x_69 = lean_box(0);
lean_inc(x_62);
x_70 = lean_name_mk_string(x_69, x_62);
lean_inc(x_70);
x_71 = l_Lean_Name_append___main(x_61, x_70);
x_72 = l_Lean_Elab_Term_getCurrNamespace(x_4, x_5, x_6, x_7, x_8, x_9, x_66);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_71);
x_76 = l_Lean_Name_replacePrefix___main(x_71, x_74, x_69);
lean_dec(x_74);
x_77 = lean_ctor_get(x_6, 1);
lean_inc(x_77);
x_78 = lean_local_ctx_find_from_user_name(x_77, x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
lean_inc(x_61);
x_79 = l___private_Lean_Elab_App_13__findMethod_x3f___main(x_67, x_61, x_70);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_free_object(x_72);
lean_dec(x_61);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_62);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = l___private_Lean_Elab_App_14__resolveLValAux___closed__21;
x_83 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_85 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_86, 0, x_71);
x_87 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_89 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_89, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
lean_dec(x_6);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_71);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_91 = lean_ctor_get(x_79, 0);
lean_inc(x_91);
lean_dec(x_79);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_61);
lean_ctor_set(x_94, 2, x_93);
lean_ctor_set(x_72, 0, x_94);
return x_72;
}
}
else
{
lean_object* x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; 
x_95 = lean_ctor_get(x_78, 0);
lean_inc(x_95);
lean_dec(x_78);
x_96 = l_Lean_LocalDecl_binderInfo(x_95);
x_97 = 4;
x_98 = l_Lean_BinderInfo_beq(x_96, x_97);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_95);
lean_inc(x_61);
x_99 = l___private_Lean_Elab_App_13__findMethod_x3f___main(x_67, x_61, x_70);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_free_object(x_72);
lean_dec(x_61);
x_100 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_100, 0, x_62);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = l___private_Lean_Elab_App_14__resolveLValAux___closed__21;
x_103 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_105 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_106, 0, x_71);
x_107 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_109 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_109, x_4, x_5, x_6, x_7, x_8, x_9, x_75);
lean_dec(x_6);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_71);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_111 = lean_ctor_get(x_99, 0);
lean_inc(x_111);
lean_dec(x_99);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_61);
lean_ctor_set(x_114, 2, x_113);
lean_ctor_set(x_72, 0, x_114);
return x_72;
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_115 = l_Lean_LocalDecl_toExpr(x_95);
lean_dec(x_95);
x_116 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_116, 0, x_61);
lean_ctor_set(x_116, 1, x_71);
lean_ctor_set(x_116, 2, x_115);
lean_ctor_set(x_72, 0, x_116);
return x_72;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_72, 0);
x_118 = lean_ctor_get(x_72, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_72);
lean_inc(x_71);
x_119 = l_Lean_Name_replacePrefix___main(x_71, x_117, x_69);
lean_dec(x_117);
x_120 = lean_ctor_get(x_6, 1);
lean_inc(x_120);
x_121 = lean_local_ctx_find_from_user_name(x_120, x_119);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
lean_inc(x_61);
x_122 = l___private_Lean_Elab_App_13__findMethod_x3f___main(x_67, x_61, x_70);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_61);
x_123 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_123, 0, x_62);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = l___private_Lean_Elab_App_14__resolveLValAux___closed__21;
x_126 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_128 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_129, 0, x_71);
x_130 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_132 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_132, x_4, x_5, x_6, x_7, x_8, x_9, x_118);
lean_dec(x_6);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_71);
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
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_118);
return x_138;
}
}
else
{
lean_object* x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_121, 0);
lean_inc(x_139);
lean_dec(x_121);
x_140 = l_Lean_LocalDecl_binderInfo(x_139);
x_141 = 4;
x_142 = l_Lean_BinderInfo_beq(x_140, x_141);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_139);
lean_inc(x_61);
x_143 = l___private_Lean_Elab_App_13__findMethod_x3f___main(x_67, x_61, x_70);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_61);
x_144 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_144, 0, x_62);
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = l___private_Lean_Elab_App_14__resolveLValAux___closed__21;
x_147 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
x_148 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_149 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_150, 0, x_71);
x_151 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_153 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_153, x_4, x_5, x_6, x_7, x_8, x_9, x_118);
lean_dec(x_6);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_71);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_155 = lean_ctor_get(x_143, 0);
lean_inc(x_155);
lean_dec(x_143);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_61);
lean_ctor_set(x_158, 2, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_118);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_160 = l_Lean_LocalDecl_toExpr(x_139);
lean_dec(x_139);
x_161 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_161, 0, x_61);
lean_ctor_set(x_161, 1, x_71);
lean_ctor_set(x_161, 2, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_118);
return x_162;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_box(0);
lean_inc(x_62);
x_164 = lean_name_mk_string(x_163, x_62);
lean_inc(x_61);
lean_inc(x_67);
x_165 = l_Lean_findField_x3f___main(x_67, x_61, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
lean_free_object(x_63);
lean_inc(x_164);
x_166 = l_Lean_Name_append___main(x_61, x_164);
x_167 = l_Lean_Elab_Term_getCurrNamespace(x_4, x_5, x_6, x_7, x_8, x_9, x_66);
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_ctor_get(x_167, 0);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_166);
x_171 = l_Lean_Name_replacePrefix___main(x_166, x_169, x_163);
lean_dec(x_169);
x_172 = lean_ctor_get(x_6, 1);
lean_inc(x_172);
x_173 = lean_local_ctx_find_from_user_name(x_172, x_171);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; 
lean_inc(x_61);
x_174 = l___private_Lean_Elab_App_13__findMethod_x3f___main(x_67, x_61, x_164);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_free_object(x_167);
lean_dec(x_61);
x_175 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_175, 0, x_62);
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_175);
x_177 = l___private_Lean_Elab_App_14__resolveLValAux___closed__21;
x_178 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
x_179 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_180 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_181, 0, x_166);
x_182 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_183 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_184 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
x_185 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_184, x_4, x_5, x_6, x_7, x_8, x_9, x_170);
lean_dec(x_6);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_166);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_186 = lean_ctor_get(x_174, 0);
lean_inc(x_186);
lean_dec(x_174);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_61);
lean_ctor_set(x_189, 2, x_188);
lean_ctor_set(x_167, 0, x_189);
return x_167;
}
}
else
{
lean_object* x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_173, 0);
lean_inc(x_190);
lean_dec(x_173);
x_191 = l_Lean_LocalDecl_binderInfo(x_190);
x_192 = 4;
x_193 = l_Lean_BinderInfo_beq(x_191, x_192);
if (x_193 == 0)
{
lean_object* x_194; 
lean_dec(x_190);
lean_inc(x_61);
x_194 = l___private_Lean_Elab_App_13__findMethod_x3f___main(x_67, x_61, x_164);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_free_object(x_167);
lean_dec(x_61);
x_195 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_195, 0, x_62);
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_195);
x_197 = l___private_Lean_Elab_App_14__resolveLValAux___closed__21;
x_198 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
x_199 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_200 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_201, 0, x_166);
x_202 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_203 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_204 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
x_205 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_204, x_4, x_5, x_6, x_7, x_8, x_9, x_170);
lean_dec(x_6);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_166);
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
lean_ctor_set(x_167, 0, x_209);
return x_167;
}
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_164);
lean_dec(x_67);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_210 = l_Lean_LocalDecl_toExpr(x_190);
lean_dec(x_190);
x_211 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_211, 0, x_61);
lean_ctor_set(x_211, 1, x_166);
lean_ctor_set(x_211, 2, x_210);
lean_ctor_set(x_167, 0, x_211);
return x_167;
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_212 = lean_ctor_get(x_167, 0);
x_213 = lean_ctor_get(x_167, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_167);
lean_inc(x_166);
x_214 = l_Lean_Name_replacePrefix___main(x_166, x_212, x_163);
lean_dec(x_212);
x_215 = lean_ctor_get(x_6, 1);
lean_inc(x_215);
x_216 = lean_local_ctx_find_from_user_name(x_215, x_214);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; 
lean_inc(x_61);
x_217 = l___private_Lean_Elab_App_13__findMethod_x3f___main(x_67, x_61, x_164);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_61);
x_218 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_218, 0, x_62);
x_219 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_219, 0, x_218);
x_220 = l___private_Lean_Elab_App_14__resolveLValAux___closed__21;
x_221 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
x_222 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_223 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_224, 0, x_166);
x_225 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
x_226 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_227 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
x_228 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_227, x_4, x_5, x_6, x_7, x_8, x_9, x_213);
lean_dec(x_6);
return x_228;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_166);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_229 = lean_ctor_get(x_217, 0);
lean_inc(x_229);
lean_dec(x_217);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_61);
lean_ctor_set(x_232, 2, x_231);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_213);
return x_233;
}
}
else
{
lean_object* x_234; uint8_t x_235; uint8_t x_236; uint8_t x_237; 
x_234 = lean_ctor_get(x_216, 0);
lean_inc(x_234);
lean_dec(x_216);
x_235 = l_Lean_LocalDecl_binderInfo(x_234);
x_236 = 4;
x_237 = l_Lean_BinderInfo_beq(x_235, x_236);
if (x_237 == 0)
{
lean_object* x_238; 
lean_dec(x_234);
lean_inc(x_61);
x_238 = l___private_Lean_Elab_App_13__findMethod_x3f___main(x_67, x_61, x_164);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_61);
x_239 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_239, 0, x_62);
x_240 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_240, 0, x_239);
x_241 = l___private_Lean_Elab_App_14__resolveLValAux___closed__21;
x_242 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_240);
x_243 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_244 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_245, 0, x_166);
x_246 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_248 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
x_249 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_248, x_4, x_5, x_6, x_7, x_8, x_9, x_213);
lean_dec(x_6);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_166);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_250 = lean_ctor_get(x_238, 0);
lean_inc(x_250);
lean_dec(x_238);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_61);
lean_ctor_set(x_253, 2, x_252);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_213);
return x_254;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_164);
lean_dec(x_67);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_255 = l_Lean_LocalDecl_toExpr(x_234);
lean_dec(x_234);
x_256 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_256, 0, x_61);
lean_ctor_set(x_256, 1, x_166);
lean_ctor_set(x_256, 2, x_255);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_213);
return x_257;
}
}
}
}
else
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_67);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_258 = lean_ctor_get(x_165, 0);
lean_inc(x_258);
lean_dec(x_165);
x_259 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_61);
lean_ctor_set(x_259, 2, x_164);
lean_ctor_set(x_63, 0, x_259);
return x_63;
}
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_260 = lean_ctor_get(x_63, 0);
x_261 = lean_ctor_get(x_63, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_63);
x_262 = lean_ctor_get(x_260, 0);
lean_inc(x_262);
lean_dec(x_260);
lean_inc(x_61);
lean_inc(x_262);
x_263 = l_Lean_isStructure(x_262, x_61);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_264 = lean_box(0);
lean_inc(x_62);
x_265 = lean_name_mk_string(x_264, x_62);
lean_inc(x_265);
x_266 = l_Lean_Name_append___main(x_61, x_265);
x_267 = l_Lean_Elab_Term_getCurrNamespace(x_4, x_5, x_6, x_7, x_8, x_9, x_261);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_270 = x_267;
} else {
 lean_dec_ref(x_267);
 x_270 = lean_box(0);
}
lean_inc(x_266);
x_271 = l_Lean_Name_replacePrefix___main(x_266, x_268, x_264);
lean_dec(x_268);
x_272 = lean_ctor_get(x_6, 1);
lean_inc(x_272);
x_273 = lean_local_ctx_find_from_user_name(x_272, x_271);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; 
lean_inc(x_61);
x_274 = l___private_Lean_Elab_App_13__findMethod_x3f___main(x_262, x_61, x_265);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_270);
lean_dec(x_61);
x_275 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_275, 0, x_62);
x_276 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_276, 0, x_275);
x_277 = l___private_Lean_Elab_App_14__resolveLValAux___closed__21;
x_278 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_276);
x_279 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_280 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
x_281 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_281, 0, x_266);
x_282 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
x_283 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_284 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
x_285 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_284, x_4, x_5, x_6, x_7, x_8, x_9, x_269);
lean_dec(x_6);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_266);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_286 = lean_ctor_get(x_274, 0);
lean_inc(x_286);
lean_dec(x_274);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_61);
lean_ctor_set(x_289, 2, x_288);
if (lean_is_scalar(x_270)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_270;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_269);
return x_290;
}
}
else
{
lean_object* x_291; uint8_t x_292; uint8_t x_293; uint8_t x_294; 
x_291 = lean_ctor_get(x_273, 0);
lean_inc(x_291);
lean_dec(x_273);
x_292 = l_Lean_LocalDecl_binderInfo(x_291);
x_293 = 4;
x_294 = l_Lean_BinderInfo_beq(x_292, x_293);
if (x_294 == 0)
{
lean_object* x_295; 
lean_dec(x_291);
lean_inc(x_61);
x_295 = l___private_Lean_Elab_App_13__findMethod_x3f___main(x_262, x_61, x_265);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_270);
lean_dec(x_61);
x_296 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_296, 0, x_62);
x_297 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_297, 0, x_296);
x_298 = l___private_Lean_Elab_App_14__resolveLValAux___closed__21;
x_299 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_297);
x_300 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_301 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_302, 0, x_266);
x_303 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
x_304 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_305 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
x_306 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_305, x_4, x_5, x_6, x_7, x_8, x_9, x_269);
lean_dec(x_6);
return x_306;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_266);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_307 = lean_ctor_get(x_295, 0);
lean_inc(x_307);
lean_dec(x_295);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_61);
lean_ctor_set(x_310, 2, x_309);
if (lean_is_scalar(x_270)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_270;
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_269);
return x_311;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_265);
lean_dec(x_262);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_312 = l_Lean_LocalDecl_toExpr(x_291);
lean_dec(x_291);
x_313 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_313, 0, x_61);
lean_ctor_set(x_313, 1, x_266);
lean_ctor_set(x_313, 2, x_312);
if (lean_is_scalar(x_270)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_270;
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_269);
return x_314;
}
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_box(0);
lean_inc(x_62);
x_316 = lean_name_mk_string(x_315, x_62);
lean_inc(x_61);
lean_inc(x_262);
x_317 = l_Lean_findField_x3f___main(x_262, x_61, x_316);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_inc(x_316);
x_318 = l_Lean_Name_append___main(x_61, x_316);
x_319 = l_Lean_Elab_Term_getCurrNamespace(x_4, x_5, x_6, x_7, x_8, x_9, x_261);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_322 = x_319;
} else {
 lean_dec_ref(x_319);
 x_322 = lean_box(0);
}
lean_inc(x_318);
x_323 = l_Lean_Name_replacePrefix___main(x_318, x_320, x_315);
lean_dec(x_320);
x_324 = lean_ctor_get(x_6, 1);
lean_inc(x_324);
x_325 = lean_local_ctx_find_from_user_name(x_324, x_323);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; 
lean_inc(x_61);
x_326 = l___private_Lean_Elab_App_13__findMethod_x3f___main(x_262, x_61, x_316);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_322);
lean_dec(x_61);
x_327 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_327, 0, x_62);
x_328 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_328, 0, x_327);
x_329 = l___private_Lean_Elab_App_14__resolveLValAux___closed__21;
x_330 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_328);
x_331 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_332 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
x_333 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_333, 0, x_318);
x_334 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
x_335 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_336 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
x_337 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_336, x_4, x_5, x_6, x_7, x_8, x_9, x_321);
lean_dec(x_6);
return x_337;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_318);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_338 = lean_ctor_get(x_326, 0);
lean_inc(x_338);
lean_dec(x_326);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_61);
lean_ctor_set(x_341, 2, x_340);
if (lean_is_scalar(x_322)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_322;
}
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_321);
return x_342;
}
}
else
{
lean_object* x_343; uint8_t x_344; uint8_t x_345; uint8_t x_346; 
x_343 = lean_ctor_get(x_325, 0);
lean_inc(x_343);
lean_dec(x_325);
x_344 = l_Lean_LocalDecl_binderInfo(x_343);
x_345 = 4;
x_346 = l_Lean_BinderInfo_beq(x_344, x_345);
if (x_346 == 0)
{
lean_object* x_347; 
lean_dec(x_343);
lean_inc(x_61);
x_347 = l___private_Lean_Elab_App_13__findMethod_x3f___main(x_262, x_61, x_316);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_322);
lean_dec(x_61);
x_348 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_348, 0, x_62);
x_349 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_349, 0, x_348);
x_350 = l___private_Lean_Elab_App_14__resolveLValAux___closed__21;
x_351 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_349);
x_352 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_353 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
x_354 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_354, 0, x_318);
x_355 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set(x_355, 1, x_354);
x_356 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_357 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
x_358 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_357, x_4, x_5, x_6, x_7, x_8, x_9, x_321);
lean_dec(x_6);
return x_358;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_318);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_359 = lean_ctor_get(x_347, 0);
lean_inc(x_359);
lean_dec(x_347);
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_362 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_61);
lean_ctor_set(x_362, 2, x_361);
if (lean_is_scalar(x_322)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_322;
}
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_321);
return x_363;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_316);
lean_dec(x_262);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_364 = l_Lean_LocalDecl_toExpr(x_343);
lean_dec(x_343);
x_365 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_365, 0, x_61);
lean_ctor_set(x_365, 1, x_318);
lean_ctor_set(x_365, 2, x_364);
if (lean_is_scalar(x_322)) {
 x_366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_366 = x_322;
}
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_321);
return x_366;
}
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_262);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_367 = lean_ctor_get(x_317, 0);
lean_inc(x_367);
lean_dec(x_317);
x_368 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_61);
lean_ctor_set(x_368, 2, x_316);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_261);
return x_369;
}
}
}
}
default: 
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; 
x_370 = lean_ctor_get(x_17, 0);
lean_inc(x_370);
lean_dec(x_17);
x_371 = lean_ctor_get(x_3, 0);
lean_inc(x_371);
lean_dec(x_3);
x_372 = lean_st_ref_get(x_9, x_10);
x_373 = !lean_is_exclusive(x_372);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_374 = lean_ctor_get(x_372, 0);
x_375 = lean_ctor_get(x_372, 1);
x_376 = lean_ctor_get(x_374, 0);
lean_inc(x_376);
lean_dec(x_374);
x_377 = l___private_Lean_Elab_App_14__resolveLValAux___closed__25;
x_378 = lean_name_mk_string(x_370, x_377);
lean_inc(x_378);
x_379 = lean_environment_find(x_376, x_378);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_free_object(x_372);
lean_dec(x_371);
x_380 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_380, 0, x_378);
x_381 = l___private_Lean_Elab_App_14__resolveLValAux___closed__28;
x_382 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_380);
x_383 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_384 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
x_385 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_384, x_4, x_5, x_6, x_7, x_8, x_9, x_375);
lean_dec(x_6);
return x_385;
}
else
{
lean_object* x_386; 
lean_dec(x_379);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_386 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_386, 0, x_378);
lean_ctor_set(x_386, 1, x_371);
lean_ctor_set(x_372, 0, x_386);
return x_372;
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_387 = lean_ctor_get(x_372, 0);
x_388 = lean_ctor_get(x_372, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_372);
x_389 = lean_ctor_get(x_387, 0);
lean_inc(x_389);
lean_dec(x_387);
x_390 = l___private_Lean_Elab_App_14__resolveLValAux___closed__25;
x_391 = lean_name_mk_string(x_370, x_390);
lean_inc(x_391);
x_392 = lean_environment_find(x_389, x_391);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_371);
x_393 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_393, 0, x_391);
x_394 = l___private_Lean_Elab_App_14__resolveLValAux___closed__28;
x_395 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_393);
x_396 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_397 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_396);
x_398 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_397, x_4, x_5, x_6, x_7, x_8, x_9, x_388);
lean_dec(x_6);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; 
lean_dec(x_392);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_399 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_399, 0, x_391);
lean_ctor_set(x_399, 1, x_371);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_388);
return x_400;
}
}
}
}
}
else
{
lean_object* x_401; 
lean_dec(x_17);
x_401 = lean_box(0);
x_11 = x_401;
goto block_16;
}
block_16:
{
lean_dec(x_11);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = l___private_Lean_Elab_App_14__resolveLValAux___closed__6;
x_13 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_14 = l___private_Lean_Elab_App_14__resolveLValAux___closed__3;
x_15 = l___private_Lean_Elab_App_12__throwLValError___rarg(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_15;
}
}
}
}
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_14__resolveLValAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_15__resolveLValLoop___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l___private_Lean_Elab_App_15__resolveLValLoop___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_10, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_17, 2);
lean_dec(x_20);
x_21 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_17, 2, x_21);
x_22 = lean_st_ref_set(x_10, x_17, x_18);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_24 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(x_3, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_5);
x_27 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_5);
lean_inc(x_25);
x_29 = l_Lean_Elab_Term_tryPostponeIfMVar(x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_25);
lean_inc(x_1);
x_31 = l___private_Lean_Elab_App_14__resolveLValAux(x_1, x_25, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_10, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 2);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_st_ref_take(x_10, x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_39, 2);
lean_dec(x_42);
lean_ctor_set(x_39, 2, x_21);
x_43 = lean_st_ref_set(x_10, x_39, x_40);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_45 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_25, x_7, x_8, x_9, x_10, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_5);
x_48 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_47);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Array_forMAux___main___at___private_Lean_Elab_App_15__resolveLValLoop___main___spec__1(x_4, x_50, x_5, x_6, x_7, x_8, x_9, x_10, x_49);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_32);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_32);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_32);
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
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_48, 1);
lean_inc(x_60);
lean_dec(x_48);
x_61 = lean_ctor_get(x_46, 0);
lean_inc(x_61);
lean_dec(x_46);
x_62 = lean_array_push(x_4, x_32);
x_3 = x_61;
x_4 = x_62;
x_11 = x_60;
goto _start;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_45, 1);
lean_inc(x_65);
lean_dec(x_45);
x_66 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_65);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 0, x_64);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_39, 0);
x_72 = lean_ctor_get(x_39, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_39);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_21);
x_74 = lean_st_ref_set(x_10, x_73, x_40);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_76 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_25, x_7, x_8, x_9, x_10, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_5);
x_79 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_78);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_unsigned_to_nat(0u);
x_82 = l_Array_forMAux___main___at___private_Lean_Elab_App_15__resolveLValLoop___main___spec__1(x_4, x_81, x_5, x_6, x_7, x_8, x_9, x_10, x_80);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
 lean_ctor_set_tag(x_85, 1);
}
lean_ctor_set(x_85, 0, x_32);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_32);
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_88 = x_82;
} else {
 lean_dec_ref(x_82);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_79, 1);
lean_inc(x_90);
lean_dec(x_79);
x_91 = lean_ctor_get(x_77, 0);
lean_inc(x_91);
lean_dec(x_77);
x_92 = lean_array_push(x_4, x_32);
x_3 = x_91;
x_4 = x_92;
x_11 = x_90;
goto _start;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_ctor_get(x_76, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_76, 1);
lean_inc(x_95);
lean_dec(x_76);
x_96 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_95);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
 lean_ctor_set_tag(x_99, 1);
}
lean_ctor_set(x_99, 0, x_94);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_29);
if (x_100 == 0)
{
return x_29;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_29, 0);
x_102 = lean_ctor_get(x_29, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_29);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_104 = lean_ctor_get(x_24, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_24, 1);
lean_inc(x_105);
lean_dec(x_24);
x_106 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_105);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_106, 0);
lean_dec(x_108);
lean_ctor_set_tag(x_106, 1);
lean_ctor_set(x_106, 0, x_104);
return x_106;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_111 = lean_ctor_get(x_17, 0);
x_112 = lean_ctor_get(x_17, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_17);
x_113 = l_Lean_TraceState_Inhabited___closed__1;
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
lean_ctor_set(x_114, 2, x_113);
x_115 = lean_st_ref_set(x_10, x_114, x_18);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_117 = l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(x_3, x_7, x_8, x_9, x_10, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
lean_inc(x_5);
x_120 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_119);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
lean_inc(x_5);
lean_inc(x_118);
x_122 = l_Lean_Elab_Term_tryPostponeIfMVar(x_118, x_5, x_6, x_7, x_8, x_9, x_10, x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_118);
lean_inc(x_1);
x_124 = l___private_Lean_Elab_App_14__resolveLValAux(x_1, x_118, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_dec(x_118);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_st_ref_get(x_10, x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_128, 2);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_st_ref_take(x_10, x_129);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 x_136 = x_132;
} else {
 lean_dec_ref(x_132);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 3, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
lean_ctor_set(x_137, 2, x_113);
x_138 = lean_st_ref_set(x_10, x_137, x_133);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_140 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_118, x_7, x_8, x_9, x_10, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_5);
x_143 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_130, x_5, x_6, x_7, x_8, x_9, x_10, x_142);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_2);
lean_dec(x_1);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
x_145 = lean_unsigned_to_nat(0u);
x_146 = l_Array_forMAux___main___at___private_Lean_Elab_App_15__resolveLValLoop___main___spec__1(x_4, x_145, x_5, x_6, x_7, x_8, x_9, x_10, x_144);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
 lean_ctor_set_tag(x_149, 1);
}
lean_ctor_set(x_149, 0, x_125);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_125);
x_150 = lean_ctor_get(x_146, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_152 = x_146;
} else {
 lean_dec_ref(x_146);
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
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_143, 1);
lean_inc(x_154);
lean_dec(x_143);
x_155 = lean_ctor_get(x_141, 0);
lean_inc(x_155);
lean_dec(x_141);
x_156 = lean_array_push(x_4, x_125);
x_3 = x_155;
x_4 = x_156;
x_11 = x_154;
goto _start;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_125);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_158 = lean_ctor_get(x_140, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_140, 1);
lean_inc(x_159);
lean_dec(x_140);
x_160 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_130, x_5, x_6, x_7, x_8, x_9, x_10, x_159);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
 lean_ctor_set_tag(x_163, 1);
}
lean_ctor_set(x_163, 0, x_158);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_118);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_164 = lean_ctor_get(x_122, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_122, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_166 = x_122;
} else {
 lean_dec_ref(x_122);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_168 = lean_ctor_get(x_117, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_117, 1);
lean_inc(x_169);
lean_dec(x_117);
x_170 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_169);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
 lean_ctor_set_tag(x_173, 1);
}
lean_ctor_set(x_173, 0, x_168);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_15__resolveLValLoop___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forMAux___main___at___private_Lean_Elab_App_15__resolveLValLoop___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_App_15__resolveLValLoop___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_App_15__resolveLValLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_15__resolveLValLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_App_15__resolveLValLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_15__resolveLValLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_App_15__resolveLValLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_16__resolveLVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Array_empty___closed__1;
x_14 = l___private_Lean_Elab_App_15__resolveLValLoop___main(x_1, x_2, x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
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
lean_object* l___private_Lean_Elab_App_16__resolveLVal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_16__resolveLVal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("self");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_18 = l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__2;
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
x_25 = l___private_Lean_Elab_App_11__elabAppArgs(x_15, x_21, x_23, x_22, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
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
lean_object* _init_l___private_Lean_Elab_App_17__mkBaseProjections___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to access field in parent structure");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_17__mkBaseProjections___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_17__mkBaseProjections___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_17__mkBaseProjections___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_17__mkBaseProjections___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_17__mkBaseProjections(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_16 = l___private_Lean_Elab_App_17__mkBaseProjections___closed__3;
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
x_19 = l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1(x_3, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_19;
}
}
}
lean_object* l___private_Lean_Elab_App_17__mkBaseProjections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_17__mkBaseProjections(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_18__addLValArg___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, function '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_18__addLValArg___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_18__addLValArg___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not have explicit argument with type (");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_18__addLValArg___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_18__addLValArg___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ...)");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_18__addLValArg___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_18__addLValArg___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, insufficient number of arguments for '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_18__addLValArg___main___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_18__addLValArg___main___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_18__addLValArg___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
x_35 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_18__addLValArg___main___spec__1(x_27, x_6, x_34);
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
x_41 = l___private_Lean_Elab_App_18__addLValArg___main___closed__12;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_44 = lean_alloc_ctor(9, 2, 0);
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
x_17 = l___private_Lean_Elab_App_18__addLValArg___main___closed__3;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l___private_Lean_Elab_App_18__addLValArg___main___closed__6;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Lean_Elab_App_18__addLValArg___main___closed__9;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_25;
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_18__addLValArg___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_18__addLValArg___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_18__addLValArg___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_App_18__addLValArg___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_15;
}
}
lean_object* l___private_Lean_Elab_App_18__addLValArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_App_18__addLValArg___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
lean_object* l___private_Lean_Elab_App_18__addLValArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_App_18__addLValArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_15;
}
}
lean_object* _init_l___private_Lean_Elab_App_19__elabAppLValsAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("idx");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_19__elabAppLValsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_19__elabAppLValsAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_19__elabAppLValsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_App_11__elabAppArgs(x_5, x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_inc(x_5);
x_17 = l___private_Lean_Elab_App_16__resolveLVal(x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
switch (lean_obj_tag(x_18)) {
case 0:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 2);
lean_inc(x_22);
lean_dec(x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_23 = l___private_Lean_Elab_App_17__mkBaseProjections(x_20, x_21, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Name_append___main(x_20, x_22);
lean_dec(x_20);
x_27 = lean_box(0);
lean_inc(x_7);
x_28 = l_Lean_Elab_Term_mkConst(x_26, x_27, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_List_isEmpty___rarg(x_16);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_24);
x_33 = l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__2;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_mkOptionalNode___closed__2;
x_36 = lean_array_push(x_35, x_34);
x_37 = lean_box(0);
x_38 = l_Array_empty___closed__1;
x_39 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_40 = l___private_Lean_Elab_App_11__elabAppArgs(x_29, x_36, x_38, x_37, x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_30);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_5 = x_41;
x_6 = x_16;
x_13 = x_42;
goto _start;
}
else
{
uint8_t x_44; 
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
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_16);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_24);
x_49 = l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__2;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
lean_inc(x_7);
x_51 = l_Lean_Elab_Term_addNamedArg(x_1, x_50, x_7, x_8, x_9, x_10, x_11, x_12, x_30);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l___private_Lean_Elab_App_11__elabAppArgs(x_29, x_52, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_53);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_51);
if (x_55 == 0)
{
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_51, 0);
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_51);
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
uint8_t x_59; 
lean_dec(x_24);
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
x_59 = !lean_is_exclusive(x_28);
if (x_59 == 0)
{
return x_28;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_28, 0);
x_61 = lean_ctor_get(x_28, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_28);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_22);
lean_dec(x_20);
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
x_63 = !lean_is_exclusive(x_23);
if (x_63 == 0)
{
return x_23;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_23, 0);
x_65 = lean_ctor_get(x_23, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_23);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
case 1:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_17, 1);
lean_inc(x_67);
lean_dec(x_17);
x_68 = lean_ctor_get(x_18, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
lean_dec(x_18);
x_70 = l_Lean_mkProj(x_68, x_69, x_5);
x_5 = x_70;
x_6 = x_16;
x_13 = x_67;
goto _start;
}
case 2:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_17, 1);
lean_inc(x_72);
lean_dec(x_17);
x_73 = lean_ctor_get(x_18, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_18, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_18, 2);
lean_inc(x_75);
lean_dec(x_18);
x_76 = lean_name_eq(x_73, x_74);
if (x_76 == 0)
{
lean_object* x_77; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_77 = l___private_Lean_Elab_App_17__mkBaseProjections(x_73, x_74, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_72);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_box(0);
lean_inc(x_7);
lean_inc(x_75);
x_81 = l_Lean_Elab_Term_mkConst(x_75, x_80, x_7, x_8, x_9, x_10, x_11, x_12, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_List_isEmpty___rarg(x_16);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
lean_dec(x_75);
lean_dec(x_73);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_78);
x_86 = l_Lean_mkOptionalNode___closed__2;
x_87 = lean_array_push(x_86, x_85);
x_88 = lean_box(0);
x_89 = l_Array_empty___closed__1;
x_90 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_91 = l___private_Lean_Elab_App_11__elabAppArgs(x_82, x_89, x_87, x_88, x_90, x_7, x_8, x_9, x_10, x_11, x_12, x_83);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_5 = x_92;
x_6 = x_16;
x_13 = x_93;
goto _start;
}
else
{
uint8_t x_95; 
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
x_95 = !lean_is_exclusive(x_91);
if (x_95 == 0)
{
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_91, 0);
x_97 = lean_ctor_get(x_91, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_91);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; 
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_82);
x_99 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_82, x_7, x_8, x_9, x_10, x_11, x_12, x_83);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_1);
x_103 = l___private_Lean_Elab_App_18__addLValArg___main(x_73, x_75, x_78, x_2, x_102, x_1, x_100, x_7, x_8, x_9, x_10, x_11, x_12, x_101);
lean_dec(x_100);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l___private_Lean_Elab_App_11__elabAppArgs(x_82, x_1, x_104, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_105);
return x_106;
}
else
{
uint8_t x_107; 
lean_dec(x_82);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
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
uint8_t x_111; 
lean_dec(x_82);
lean_dec(x_78);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_99);
if (x_111 == 0)
{
return x_99;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_99, 0);
x_113 = lean_ctor_get(x_99, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_99);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_78);
lean_dec(x_75);
lean_dec(x_73);
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
x_119 = !lean_is_exclusive(x_77);
if (x_119 == 0)
{
return x_77;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_77, 0);
x_121 = lean_ctor_get(x_77, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_77);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_74);
x_123 = lean_box(0);
lean_inc(x_7);
lean_inc(x_75);
x_124 = l_Lean_Elab_Term_mkConst(x_75, x_123, x_7, x_8, x_9, x_10, x_11, x_12, x_72);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = l_List_isEmpty___rarg(x_16);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; 
lean_dec(x_75);
lean_dec(x_73);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_5);
x_129 = l_Lean_mkOptionalNode___closed__2;
x_130 = lean_array_push(x_129, x_128);
x_131 = lean_box(0);
x_132 = l_Array_empty___closed__1;
x_133 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_134 = l___private_Lean_Elab_App_11__elabAppArgs(x_125, x_132, x_130, x_131, x_133, x_7, x_8, x_9, x_10, x_11, x_12, x_126);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_5 = x_135;
x_6 = x_16;
x_13 = x_136;
goto _start;
}
else
{
uint8_t x_138; 
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
x_138 = !lean_is_exclusive(x_134);
if (x_138 == 0)
{
return x_134;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_134, 0);
x_140 = lean_ctor_get(x_134, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_134);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
lean_object* x_142; 
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_125);
x_142 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_125, x_7, x_8, x_9, x_10, x_11, x_12, x_126);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_1);
x_146 = l___private_Lean_Elab_App_18__addLValArg___main(x_73, x_75, x_5, x_2, x_145, x_1, x_143, x_7, x_8, x_9, x_10, x_11, x_12, x_144);
lean_dec(x_143);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l___private_Lean_Elab_App_11__elabAppArgs(x_125, x_1, x_147, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_148);
return x_149;
}
else
{
uint8_t x_150; 
lean_dec(x_125);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
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
uint8_t x_154; 
lean_dec(x_125);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_154 = !lean_is_exclusive(x_142);
if (x_154 == 0)
{
return x_142;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_142, 0);
x_156 = lean_ctor_get(x_142, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_142);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_124);
if (x_158 == 0)
{
return x_124;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_124, 0);
x_160 = lean_ctor_get(x_124, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_124);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
}
case 3:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_162 = lean_ctor_get(x_17, 1);
lean_inc(x_162);
lean_dec(x_17);
x_163 = lean_ctor_get(x_18, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_18, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_18, 2);
lean_inc(x_165);
lean_dec(x_18);
x_166 = l_List_isEmpty___rarg(x_16);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; 
lean_dec(x_164);
lean_dec(x_163);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_5);
x_168 = l_Lean_mkOptionalNode___closed__2;
x_169 = lean_array_push(x_168, x_167);
x_170 = lean_box(0);
x_171 = l_Array_empty___closed__1;
x_172 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_173 = l___private_Lean_Elab_App_11__elabAppArgs(x_165, x_171, x_169, x_170, x_172, x_7, x_8, x_9, x_10, x_11, x_12, x_162);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_5 = x_174;
x_6 = x_16;
x_13 = x_175;
goto _start;
}
else
{
uint8_t x_177; 
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
x_177 = !lean_is_exclusive(x_173);
if (x_177 == 0)
{
return x_173;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_173, 0);
x_179 = lean_ctor_get(x_173, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_173);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
else
{
lean_object* x_181; 
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_165);
x_181 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_165, x_7, x_8, x_9, x_10, x_11, x_12, x_162);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_1);
x_185 = l___private_Lean_Elab_App_18__addLValArg___main(x_163, x_164, x_5, x_2, x_184, x_1, x_182, x_7, x_8, x_9, x_10, x_11, x_12, x_183);
lean_dec(x_182);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l___private_Lean_Elab_App_11__elabAppArgs(x_165, x_1, x_186, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_187);
return x_188;
}
else
{
uint8_t x_189; 
lean_dec(x_165);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_185);
if (x_189 == 0)
{
return x_185;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_185, 0);
x_191 = lean_ctor_get(x_185, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_185);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_193 = !lean_is_exclusive(x_181);
if (x_193 == 0)
{
return x_181;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_181, 0);
x_195 = lean_ctor_get(x_181, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_181);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
}
default: 
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_17, 1);
lean_inc(x_197);
lean_dec(x_17);
x_198 = lean_ctor_get(x_18, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_18, 1);
lean_inc(x_199);
lean_dec(x_18);
x_200 = lean_box(0);
lean_inc(x_7);
x_201 = l_Lean_Elab_Term_mkConst(x_198, x_200, x_7, x_8, x_9, x_10, x_11, x_12, x_197);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = l_List_isEmpty___rarg(x_16);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; 
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_5);
x_206 = l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__2;
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
x_208 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_208, 0, x_199);
x_209 = l___private_Lean_Elab_App_19__elabAppLValsAux___main___closed__2;
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_208);
x_211 = l_Lean_mkAppStx___closed__9;
x_212 = lean_array_push(x_211, x_207);
x_213 = lean_array_push(x_212, x_210);
x_214 = lean_box(0);
x_215 = l_Array_empty___closed__1;
x_216 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_217 = l___private_Lean_Elab_App_11__elabAppArgs(x_202, x_213, x_215, x_214, x_216, x_7, x_8, x_9, x_10, x_11, x_12, x_203);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_5 = x_218;
x_6 = x_16;
x_13 = x_219;
goto _start;
}
else
{
uint8_t x_221; 
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
x_221 = !lean_is_exclusive(x_217);
if (x_221 == 0)
{
return x_217;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_217, 0);
x_223 = lean_ctor_get(x_217, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_217);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_16);
x_225 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_225, 0, x_5);
x_226 = l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__2;
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_225);
lean_inc(x_7);
x_228 = l_Lean_Elab_Term_addNamedArg(x_1, x_227, x_7, x_8, x_9, x_10, x_11, x_12, x_203);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_231, 0, x_199);
x_232 = l___private_Lean_Elab_App_19__elabAppLValsAux___main___closed__2;
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
lean_inc(x_7);
x_234 = l_Lean_Elab_Term_addNamedArg(x_229, x_233, x_7, x_8, x_9, x_10, x_11, x_12, x_230);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = l___private_Lean_Elab_App_11__elabAppArgs(x_202, x_235, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_236);
return x_237;
}
else
{
uint8_t x_238; 
lean_dec(x_202);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_238 = !lean_is_exclusive(x_234);
if (x_238 == 0)
{
return x_234;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_234, 0);
x_240 = lean_ctor_get(x_234, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_234);
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
lean_dec(x_202);
lean_dec(x_199);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_242 = !lean_is_exclusive(x_228);
if (x_242 == 0)
{
return x_228;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_228, 0);
x_244 = lean_ctor_get(x_228, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_228);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
}
else
{
uint8_t x_246; 
lean_dec(x_199);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_246 = !lean_is_exclusive(x_201);
if (x_246 == 0)
{
return x_201;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_201, 0);
x_248 = lean_ctor_get(x_201, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_201);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_250 = !lean_is_exclusive(x_17);
if (x_250 == 0)
{
return x_17;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_17, 0);
x_252 = lean_ctor_get(x_17, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_17);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_19__elabAppLValsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Elab_App_19__elabAppLValsAux___main(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l___private_Lean_Elab_App_19__elabAppLValsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_App_19__elabAppLValsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
lean_object* l___private_Lean_Elab_App_19__elabAppLValsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Elab_App_19__elabAppLValsAux(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* _init_l___private_Lean_Elab_App_20__elabAppLVals___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of field notation with `@` modifier");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_20__elabAppLVals___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_20__elabAppLVals___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_20__elabAppLVals___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_20__elabAppLVals___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_20__elabAppLVals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = l_List_isEmpty___rarg(x_2);
if (x_14 == 0)
{
if (x_6 == 0)
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_App_19__elabAppLValsAux___main(x_3, x_4, x_5, x_6, x_1, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_16 = l___private_Lean_Elab_App_20__elabAppLVals___closed__3;
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
x_22 = l___private_Lean_Elab_App_19__elabAppLValsAux___main(x_3, x_4, x_5, x_6, x_1, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_22;
}
}
}
lean_object* l___private_Lean_Elab_App_20__elabAppLVals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l___private_Lean_Elab_App_20__elabAppLVals(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_inc(x_6);
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
lean_dec(x_6);
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
lean_dec(x_6);
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
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1___rarg), 1, 0);
return x_7;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__2(lean_object* x_1) {
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
x_7 = l_List_map___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__2(x_5);
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
x_11 = l_List_map___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_51; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_List_map___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__2(x_19);
lean_inc(x_1);
x_21 = l_List_append___rarg(x_20, x_1);
x_22 = l_Lean_Elab_Term_saveAllState___rarg(x_9, x_10, x_11, x_12, x_13, x_14);
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
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_51 = l___private_Lean_Elab_App_20__elabAppLVals(x_18, x_21, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_25);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Elab_Term_saveAllState___rarg(x_9, x_10, x_11, x_12, x_13, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Elab_Term_SavedState_restore(x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_56);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 1);
x_60 = lean_ctor_get(x_57, 0);
lean_dec(x_60);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 0, x_52);
x_61 = lean_array_push(x_6, x_57);
x_6 = x_61;
x_7 = x_17;
x_14 = x_59;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_55);
x_65 = lean_array_push(x_6, x_64);
x_6 = x_65;
x_7 = x_17;
x_14 = x_63;
goto _start;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_51, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_51, 1);
lean_inc(x_68);
lean_dec(x_51);
x_26 = x_67;
x_27 = x_68;
goto block_50;
}
block_50:
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_25);
x_28 = l_Lean_Elab_Term_saveAllState___rarg(x_9, x_10, x_11, x_12, x_13, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Term_SavedState_restore(x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 1);
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 0, x_26);
x_35 = lean_array_push(x_6, x_31);
x_6 = x_35;
x_7 = x_17;
x_14 = x_33;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_29);
x_39 = lean_array_push(x_6, x_38);
x_6 = x_39;
x_7 = x_17;
x_14 = x_37;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_ctor_get(x_26, 0);
lean_inc(x_41);
x_42 = l_Lean_Elab_postponeExceptionId;
x_43 = lean_nat_dec_eq(x_41, x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_23);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_is_scalar(x_25)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_25;
 lean_ctor_set_tag(x_44, 1);
}
lean_ctor_set(x_44, 0, x_26);
lean_ctor_set(x_44, 1, x_27);
return x_44;
}
else
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_25);
x_45 = l_Lean_Elab_Term_SavedState_restore(x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 0, x_26);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_26);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_51; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_List_map___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__2(x_19);
lean_inc(x_1);
x_21 = l_List_append___rarg(x_20, x_1);
x_22 = l_Lean_Elab_Term_saveAllState___rarg(x_9, x_10, x_11, x_12, x_13, x_14);
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
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_51 = l___private_Lean_Elab_App_20__elabAppLVals(x_18, x_21, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_25);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Elab_Term_saveAllState___rarg(x_9, x_10, x_11, x_12, x_13, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Elab_Term_SavedState_restore(x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_56);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 1);
x_60 = lean_ctor_get(x_57, 0);
lean_dec(x_60);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 0, x_52);
x_61 = lean_array_push(x_6, x_57);
x_6 = x_61;
x_7 = x_17;
x_14 = x_59;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_52);
lean_ctor_set(x_64, 1, x_55);
x_65 = lean_array_push(x_6, x_64);
x_6 = x_65;
x_7 = x_17;
x_14 = x_63;
goto _start;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_51, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_51, 1);
lean_inc(x_68);
lean_dec(x_51);
x_26 = x_67;
x_27 = x_68;
goto block_50;
}
block_50:
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_25);
x_28 = l_Lean_Elab_Term_saveAllState___rarg(x_9, x_10, x_11, x_12, x_13, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Term_SavedState_restore(x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 1);
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 0, x_26);
x_35 = lean_array_push(x_6, x_31);
x_6 = x_35;
x_7 = x_17;
x_14 = x_33;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_29);
x_39 = lean_array_push(x_6, x_38);
x_6 = x_39;
x_7 = x_17;
x_14 = x_37;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_ctor_get(x_26, 0);
lean_inc(x_41);
x_42 = l_Lean_Elab_postponeExceptionId;
x_43 = lean_nat_dec_eq(x_41, x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_23);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
if (lean_is_scalar(x_25)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_25;
 lean_ctor_set_tag(x_44, 1);
}
lean_ctor_set(x_44, 0, x_26);
lean_ctor_set(x_44, 1, x_27);
return x_44;
}
else
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_25);
x_45 = l_Lean_Elab_Term_SavedState_restore(x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 0, x_26);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_26);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_App_21__elabAppFnId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_1, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_13, 3);
lean_inc(x_21);
x_22 = l_Lean_replaceRef(x_1, x_21);
lean_dec(x_1);
x_23 = l_Lean_replaceRef(x_22, x_21);
lean_dec(x_22);
x_24 = l_Lean_replaceRef(x_23, x_21);
lean_dec(x_21);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_24);
lean_inc(x_11);
lean_inc(x_9);
x_26 = l_Lean_Elab_Term_resolveName(x_16, x_17, x_2, x_9, x_10, x_11, x_12, x_25, x_14, x_15);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_List_lengthAux___main___rarg(x_27, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_dec_eq(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; 
x_34 = 0;
lean_ctor_set_uint8(x_9, sizeof(void*)*8 + 1, x_34);
x_35 = l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_8, x_27, x_9, x_10, x_11, x_12, x_13, x_14, x_28);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__4(x_3, x_4, x_5, x_6, x_7, x_8, x_27, x_9, x_10, x_11, x_12, x_13, x_14, x_28);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_37 = lean_ctor_get(x_9, 0);
x_38 = lean_ctor_get(x_9, 1);
x_39 = lean_ctor_get(x_9, 2);
x_40 = lean_ctor_get(x_9, 3);
x_41 = lean_ctor_get(x_9, 4);
x_42 = lean_ctor_get(x_9, 5);
x_43 = lean_ctor_get(x_9, 6);
x_44 = lean_ctor_get(x_9, 7);
x_45 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
x_46 = lean_ctor_get_uint8(x_9, sizeof(void*)*8 + 1);
x_47 = lean_ctor_get_uint8(x_9, sizeof(void*)*8 + 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_9);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_List_lengthAux___main___rarg(x_27, x_48);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_dec_eq(x_49, x_50);
lean_dec(x_49);
if (x_51 == 0)
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_52 = 0;
x_53 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_38);
lean_ctor_set(x_53, 2, x_39);
lean_ctor_set(x_53, 3, x_40);
lean_ctor_set(x_53, 4, x_41);
lean_ctor_set(x_53, 5, x_42);
lean_ctor_set(x_53, 6, x_43);
lean_ctor_set(x_53, 7, x_44);
lean_ctor_set_uint8(x_53, sizeof(void*)*8, x_45);
lean_ctor_set_uint8(x_53, sizeof(void*)*8 + 1, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*8 + 2, x_47);
x_54 = l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_8, x_27, x_53, x_10, x_11, x_12, x_13, x_14, x_28);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_55, 0, x_37);
lean_ctor_set(x_55, 1, x_38);
lean_ctor_set(x_55, 2, x_39);
lean_ctor_set(x_55, 3, x_40);
lean_ctor_set(x_55, 4, x_41);
lean_ctor_set(x_55, 5, x_42);
lean_ctor_set(x_55, 6, x_43);
lean_ctor_set(x_55, 7, x_44);
lean_ctor_set_uint8(x_55, sizeof(void*)*8, x_45);
lean_ctor_set_uint8(x_55, sizeof(void*)*8 + 1, x_46);
lean_ctor_set_uint8(x_55, sizeof(void*)*8 + 2, x_47);
x_56 = l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__4(x_3, x_4, x_5, x_6, x_7, x_8, x_27, x_55, x_10, x_11, x_12, x_13, x_14, x_28);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_26);
if (x_57 == 0)
{
return x_26;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_26, 0);
x_59 = lean_ctor_get(x_26, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_26);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1___rarg(x_15);
return x_61;
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__3(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_List_foldlM___main___at___private_Lean_Elab_App_21__elabAppFnId___spec__4(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
lean_object* l___private_Lean_Elab_App_21__elabAppFnId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = l___private_Lean_Elab_App_21__elabAppFnId(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__1(lean_object* x_1) {
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
x_9 = l_List_map___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__1(x_5);
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
x_15 = l_List_map___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__1(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
x_24 = l___private_Lean_Elab_App_22__elabAppFn___main(x_20, x_2, x_3, x_4, x_5, x_6, x_23, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
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
lean_object* _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("placeholders '_' cannot be used where a function is expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicitUniv");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected occurrence of named pattern");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("arrayRef");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namedPattern");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Expr_ctorName___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_351; lean_object* x_352; uint8_t x_353; 
lean_inc(x_1);
x_351 = l_Lean_Syntax_getKind(x_1);
x_352 = l_Lean_choiceKind;
x_353 = lean_name_eq(x_351, x_352);
lean_dec(x_351);
if (x_353 == 0)
{
uint8_t x_354; uint8_t x_1088; lean_object* x_1472; uint8_t x_1473; 
x_1472 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__13;
lean_inc(x_1);
x_1473 = l_Lean_Syntax_isOfKind(x_1, x_1472);
if (x_1473 == 0)
{
uint8_t x_1474; 
x_1474 = 0;
x_1088 = x_1474;
goto block_1471;
}
else
{
lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; uint8_t x_1478; 
x_1475 = l_Lean_Syntax_getArgs(x_1);
x_1476 = lean_array_get_size(x_1475);
lean_dec(x_1475);
x_1477 = lean_unsigned_to_nat(3u);
x_1478 = lean_nat_dec_eq(x_1476, x_1477);
lean_dec(x_1476);
x_1088 = x_1478;
goto block_1471;
}
block_1087:
{
if (x_354 == 0)
{
lean_object* x_355; uint8_t x_356; 
x_355 = l_Lean_identKind___closed__2;
lean_inc(x_1);
x_356 = l_Lean_Syntax_isOfKind(x_1, x_355);
if (x_356 == 0)
{
uint8_t x_357; uint8_t x_385; lean_object* x_741; uint8_t x_742; 
x_741 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__5;
lean_inc(x_1);
x_742 = l_Lean_Syntax_isOfKind(x_1, x_741);
if (x_742 == 0)
{
uint8_t x_743; 
x_743 = 0;
x_385 = x_743;
goto block_740;
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; uint8_t x_747; 
x_744 = l_Lean_Syntax_getArgs(x_1);
x_745 = lean_array_get_size(x_744);
lean_dec(x_744);
x_746 = lean_unsigned_to_nat(4u);
x_747 = lean_nat_dec_eq(x_745, x_746);
lean_dec(x_745);
x_385 = x_747;
goto block_740;
}
block_384:
{
if (x_357 == 0)
{
lean_object* x_358; uint8_t x_359; 
x_358 = l_Lean_mkHole___closed__2;
lean_inc(x_1);
x_359 = l_Lean_Syntax_isOfKind(x_1, x_358);
if (x_359 == 0)
{
uint8_t x_360; 
x_360 = 0;
x_16 = x_360;
goto block_350;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; 
x_361 = l_Lean_Syntax_getArgs(x_1);
x_362 = lean_array_get_size(x_361);
lean_dec(x_361);
x_363 = lean_unsigned_to_nat(1u);
x_364 = lean_nat_dec_eq(x_362, x_363);
lean_dec(x_362);
x_16 = x_364;
goto block_350;
}
}
else
{
lean_object* x_365; lean_object* x_366; uint8_t x_367; 
x_365 = lean_unsigned_to_nat(1u);
x_366 = l_Lean_Syntax_getArg(x_1, x_365);
lean_dec(x_1);
lean_inc(x_366);
x_367 = l_Lean_Syntax_isOfKind(x_366, x_355);
if (x_367 == 0)
{
lean_object* x_368; uint8_t x_369; 
x_368 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__5;
lean_inc(x_366);
x_369 = l_Lean_Syntax_isOfKind(x_366, x_368);
if (x_369 == 0)
{
lean_object* x_370; 
lean_dec(x_366);
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
x_370 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1___rarg(x_15);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; 
x_371 = l_Lean_Syntax_getArgs(x_366);
x_372 = lean_array_get_size(x_371);
lean_dec(x_371);
x_373 = lean_unsigned_to_nat(4u);
x_374 = lean_nat_dec_eq(x_372, x_373);
lean_dec(x_372);
if (x_374 == 0)
{
lean_object* x_375; 
lean_dec(x_366);
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
x_375 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1___rarg(x_15);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; uint8_t x_378; 
x_376 = lean_unsigned_to_nat(0u);
x_377 = l_Lean_Syntax_getArg(x_366, x_376);
x_378 = l_Lean_Syntax_isOfKind(x_377, x_355);
if (x_378 == 0)
{
lean_object* x_379; 
lean_dec(x_366);
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
x_379 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_21__elabAppFnId___spec__1___rarg(x_15);
return x_379;
}
else
{
uint8_t x_380; 
x_380 = 1;
x_1 = x_366;
x_6 = x_380;
goto _start;
}
}
}
}
else
{
uint8_t x_382; 
x_382 = 1;
x_1 = x_366;
x_6 = x_382;
goto _start;
}
}
}
block_740:
{
if (x_385 == 0)
{
lean_object* x_386; uint8_t x_387; 
x_386 = l___private_Lean_Elab_Term_14__isExplicit___closed__2;
lean_inc(x_1);
x_387 = l_Lean_Syntax_isOfKind(x_1, x_386);
if (x_387 == 0)
{
uint8_t x_388; 
x_388 = 0;
x_357 = x_388;
goto block_384;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; 
x_389 = l_Lean_Syntax_getArgs(x_1);
x_390 = lean_array_get_size(x_389);
lean_dec(x_389);
x_391 = lean_unsigned_to_nat(2u);
x_392 = lean_nat_dec_eq(x_390, x_391);
lean_dec(x_390);
x_357 = x_392;
goto block_384;
}
}
else
{
lean_object* x_393; lean_object* x_394; uint8_t x_395; 
x_393 = lean_unsigned_to_nat(0u);
x_394 = l_Lean_Syntax_getArg(x_1, x_393);
lean_inc(x_394);
x_395 = l_Lean_Syntax_isOfKind(x_394, x_355);
if (x_395 == 0)
{
uint8_t x_396; uint8_t x_397; 
lean_dec(x_394);
x_396 = l_List_isEmpty___rarg(x_2);
if (x_7 == 0)
{
uint8_t x_725; 
x_725 = 1;
x_397 = x_725;
goto block_724;
}
else
{
uint8_t x_726; 
x_726 = 0;
x_397 = x_726;
goto block_724;
}
block_724:
{
if (x_396 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_435; 
x_398 = lean_box(0);
x_399 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_399, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_402 = x_399;
} else {
 lean_dec_ref(x_399);
 x_402 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_435 = l_Lean_Elab_Term_elabTerm(x_1, x_398, x_397, x_9, x_10, x_11, x_12, x_13, x_14, x_401);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
lean_dec(x_435);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_438 = l___private_Lean_Elab_App_20__elabAppLVals(x_436, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_437);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; 
lean_dec(x_402);
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
lean_dec(x_438);
x_441 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_440);
x_442 = !lean_is_exclusive(x_441);
if (x_442 == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; 
x_443 = lean_ctor_get(x_441, 0);
x_444 = lean_ctor_get(x_441, 1);
x_445 = l_Lean_Elab_Term_SavedState_restore(x_400, x_9, x_10, x_11, x_12, x_13, x_14, x_444);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_446 = !lean_is_exclusive(x_445);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_ctor_get(x_445, 1);
x_448 = lean_ctor_get(x_445, 0);
lean_dec(x_448);
lean_ctor_set(x_445, 1, x_443);
lean_ctor_set(x_445, 0, x_439);
x_449 = lean_array_push(x_8, x_445);
lean_ctor_set(x_441, 1, x_447);
lean_ctor_set(x_441, 0, x_449);
return x_441;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_450 = lean_ctor_get(x_445, 1);
lean_inc(x_450);
lean_dec(x_445);
x_451 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_451, 0, x_439);
lean_ctor_set(x_451, 1, x_443);
x_452 = lean_array_push(x_8, x_451);
lean_ctor_set(x_441, 1, x_450);
lean_ctor_set(x_441, 0, x_452);
return x_441;
}
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_453 = lean_ctor_get(x_441, 0);
x_454 = lean_ctor_get(x_441, 1);
lean_inc(x_454);
lean_inc(x_453);
lean_dec(x_441);
x_455 = l_Lean_Elab_Term_SavedState_restore(x_400, x_9, x_10, x_11, x_12, x_13, x_14, x_454);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_456 = lean_ctor_get(x_455, 1);
lean_inc(x_456);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_457 = x_455;
} else {
 lean_dec_ref(x_455);
 x_457 = lean_box(0);
}
if (lean_is_scalar(x_457)) {
 x_458 = lean_alloc_ctor(0, 2, 0);
} else {
 x_458 = x_457;
}
lean_ctor_set(x_458, 0, x_439);
lean_ctor_set(x_458, 1, x_453);
x_459 = lean_array_push(x_8, x_458);
x_460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_460, 0, x_459);
lean_ctor_set(x_460, 1, x_456);
return x_460;
}
}
else
{
lean_object* x_461; lean_object* x_462; 
x_461 = lean_ctor_get(x_438, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_438, 1);
lean_inc(x_462);
lean_dec(x_438);
x_403 = x_461;
x_404 = x_462;
goto block_434;
}
}
else
{
lean_object* x_463; lean_object* x_464; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_463 = lean_ctor_get(x_435, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_435, 1);
lean_inc(x_464);
lean_dec(x_435);
x_403 = x_463;
x_404 = x_464;
goto block_434;
}
block_434:
{
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_405; uint8_t x_406; 
lean_dec(x_402);
x_405 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_404);
x_406 = !lean_is_exclusive(x_405);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; 
x_407 = lean_ctor_get(x_405, 0);
x_408 = lean_ctor_get(x_405, 1);
x_409 = l_Lean_Elab_Term_SavedState_restore(x_400, x_9, x_10, x_11, x_12, x_13, x_14, x_408);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_410 = !lean_is_exclusive(x_409);
if (x_410 == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_411 = lean_ctor_get(x_409, 1);
x_412 = lean_ctor_get(x_409, 0);
lean_dec(x_412);
lean_ctor_set_tag(x_409, 1);
lean_ctor_set(x_409, 1, x_407);
lean_ctor_set(x_409, 0, x_403);
x_413 = lean_array_push(x_8, x_409);
lean_ctor_set(x_405, 1, x_411);
lean_ctor_set(x_405, 0, x_413);
return x_405;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_409, 1);
lean_inc(x_414);
lean_dec(x_409);
x_415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_415, 0, x_403);
lean_ctor_set(x_415, 1, x_407);
x_416 = lean_array_push(x_8, x_415);
lean_ctor_set(x_405, 1, x_414);
lean_ctor_set(x_405, 0, x_416);
return x_405;
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_417 = lean_ctor_get(x_405, 0);
x_418 = lean_ctor_get(x_405, 1);
lean_inc(x_418);
lean_inc(x_417);
lean_dec(x_405);
x_419 = l_Lean_Elab_Term_SavedState_restore(x_400, x_9, x_10, x_11, x_12, x_13, x_14, x_418);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 x_421 = x_419;
} else {
 lean_dec_ref(x_419);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(1, 2, 0);
} else {
 x_422 = x_421;
 lean_ctor_set_tag(x_422, 1);
}
lean_ctor_set(x_422, 0, x_403);
lean_ctor_set(x_422, 1, x_417);
x_423 = lean_array_push(x_8, x_422);
x_424 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_420);
return x_424;
}
}
else
{
lean_object* x_425; lean_object* x_426; uint8_t x_427; 
lean_dec(x_8);
x_425 = lean_ctor_get(x_403, 0);
lean_inc(x_425);
x_426 = l_Lean_Elab_postponeExceptionId;
x_427 = lean_nat_dec_eq(x_425, x_426);
lean_dec(x_425);
if (x_427 == 0)
{
lean_object* x_428; 
lean_dec(x_400);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_402)) {
 x_428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_428 = x_402;
 lean_ctor_set_tag(x_428, 1);
}
lean_ctor_set(x_428, 0, x_403);
lean_ctor_set(x_428, 1, x_404);
return x_428;
}
else
{
lean_object* x_429; uint8_t x_430; 
lean_dec(x_402);
x_429 = l_Lean_Elab_Term_SavedState_restore(x_400, x_9, x_10, x_11, x_12, x_13, x_14, x_404);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_430 = !lean_is_exclusive(x_429);
if (x_430 == 0)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_429, 0);
lean_dec(x_431);
lean_ctor_set_tag(x_429, 1);
lean_ctor_set(x_429, 0, x_403);
return x_429;
}
else
{
lean_object* x_432; lean_object* x_433; 
x_432 = lean_ctor_get(x_429, 1);
lean_inc(x_432);
lean_dec(x_429);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_403);
lean_ctor_set(x_433, 1, x_432);
return x_433;
}
}
}
}
}
else
{
uint8_t x_465; 
x_465 = l_Array_isEmpty___rarg(x_3);
if (x_465 == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_503; 
x_466 = lean_box(0);
x_467 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_470 = x_467;
} else {
 lean_dec_ref(x_467);
 x_470 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_503 = l_Lean_Elab_Term_elabTerm(x_1, x_466, x_397, x_9, x_10, x_11, x_12, x_13, x_14, x_469);
if (lean_obj_tag(x_503) == 0)
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec(x_503);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_506 = l___private_Lean_Elab_App_20__elabAppLVals(x_504, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_505);
if (lean_obj_tag(x_506) == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; uint8_t x_510; 
lean_dec(x_470);
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
lean_dec(x_506);
x_509 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_508);
x_510 = !lean_is_exclusive(x_509);
if (x_510 == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; uint8_t x_514; 
x_511 = lean_ctor_get(x_509, 0);
x_512 = lean_ctor_get(x_509, 1);
x_513 = l_Lean_Elab_Term_SavedState_restore(x_468, x_9, x_10, x_11, x_12, x_13, x_14, x_512);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_514 = !lean_is_exclusive(x_513);
if (x_514 == 0)
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_515 = lean_ctor_get(x_513, 1);
x_516 = lean_ctor_get(x_513, 0);
lean_dec(x_516);
lean_ctor_set(x_513, 1, x_511);
lean_ctor_set(x_513, 0, x_507);
x_517 = lean_array_push(x_8, x_513);
lean_ctor_set(x_509, 1, x_515);
lean_ctor_set(x_509, 0, x_517);
return x_509;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_518 = lean_ctor_get(x_513, 1);
lean_inc(x_518);
lean_dec(x_513);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_507);
lean_ctor_set(x_519, 1, x_511);
x_520 = lean_array_push(x_8, x_519);
lean_ctor_set(x_509, 1, x_518);
lean_ctor_set(x_509, 0, x_520);
return x_509;
}
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_521 = lean_ctor_get(x_509, 0);
x_522 = lean_ctor_get(x_509, 1);
lean_inc(x_522);
lean_inc(x_521);
lean_dec(x_509);
x_523 = l_Lean_Elab_Term_SavedState_restore(x_468, x_9, x_10, x_11, x_12, x_13, x_14, x_522);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_524 = lean_ctor_get(x_523, 1);
lean_inc(x_524);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 x_525 = x_523;
} else {
 lean_dec_ref(x_523);
 x_525 = lean_box(0);
}
if (lean_is_scalar(x_525)) {
 x_526 = lean_alloc_ctor(0, 2, 0);
} else {
 x_526 = x_525;
}
lean_ctor_set(x_526, 0, x_507);
lean_ctor_set(x_526, 1, x_521);
x_527 = lean_array_push(x_8, x_526);
x_528 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_524);
return x_528;
}
}
else
{
lean_object* x_529; lean_object* x_530; 
x_529 = lean_ctor_get(x_506, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_506, 1);
lean_inc(x_530);
lean_dec(x_506);
x_471 = x_529;
x_472 = x_530;
goto block_502;
}
}
else
{
lean_object* x_531; lean_object* x_532; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_531 = lean_ctor_get(x_503, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_503, 1);
lean_inc(x_532);
lean_dec(x_503);
x_471 = x_531;
x_472 = x_532;
goto block_502;
}
block_502:
{
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_473; uint8_t x_474; 
lean_dec(x_470);
x_473 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_472);
x_474 = !lean_is_exclusive(x_473);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; 
x_475 = lean_ctor_get(x_473, 0);
x_476 = lean_ctor_get(x_473, 1);
x_477 = l_Lean_Elab_Term_SavedState_restore(x_468, x_9, x_10, x_11, x_12, x_13, x_14, x_476);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_478 = !lean_is_exclusive(x_477);
if (x_478 == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_477, 1);
x_480 = lean_ctor_get(x_477, 0);
lean_dec(x_480);
lean_ctor_set_tag(x_477, 1);
lean_ctor_set(x_477, 1, x_475);
lean_ctor_set(x_477, 0, x_471);
x_481 = lean_array_push(x_8, x_477);
lean_ctor_set(x_473, 1, x_479);
lean_ctor_set(x_473, 0, x_481);
return x_473;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_477, 1);
lean_inc(x_482);
lean_dec(x_477);
x_483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_483, 0, x_471);
lean_ctor_set(x_483, 1, x_475);
x_484 = lean_array_push(x_8, x_483);
lean_ctor_set(x_473, 1, x_482);
lean_ctor_set(x_473, 0, x_484);
return x_473;
}
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_485 = lean_ctor_get(x_473, 0);
x_486 = lean_ctor_get(x_473, 1);
lean_inc(x_486);
lean_inc(x_485);
lean_dec(x_473);
x_487 = l_Lean_Elab_Term_SavedState_restore(x_468, x_9, x_10, x_11, x_12, x_13, x_14, x_486);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_488 = lean_ctor_get(x_487, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_489 = x_487;
} else {
 lean_dec_ref(x_487);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 2, 0);
} else {
 x_490 = x_489;
 lean_ctor_set_tag(x_490, 1);
}
lean_ctor_set(x_490, 0, x_471);
lean_ctor_set(x_490, 1, x_485);
x_491 = lean_array_push(x_8, x_490);
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_491);
lean_ctor_set(x_492, 1, x_488);
return x_492;
}
}
else
{
lean_object* x_493; lean_object* x_494; uint8_t x_495; 
lean_dec(x_8);
x_493 = lean_ctor_get(x_471, 0);
lean_inc(x_493);
x_494 = l_Lean_Elab_postponeExceptionId;
x_495 = lean_nat_dec_eq(x_493, x_494);
lean_dec(x_493);
if (x_495 == 0)
{
lean_object* x_496; 
lean_dec(x_468);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_470)) {
 x_496 = lean_alloc_ctor(1, 2, 0);
} else {
 x_496 = x_470;
 lean_ctor_set_tag(x_496, 1);
}
lean_ctor_set(x_496, 0, x_471);
lean_ctor_set(x_496, 1, x_472);
return x_496;
}
else
{
lean_object* x_497; uint8_t x_498; 
lean_dec(x_470);
x_497 = l_Lean_Elab_Term_SavedState_restore(x_468, x_9, x_10, x_11, x_12, x_13, x_14, x_472);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_498 = !lean_is_exclusive(x_497);
if (x_498 == 0)
{
lean_object* x_499; 
x_499 = lean_ctor_get(x_497, 0);
lean_dec(x_499);
lean_ctor_set_tag(x_497, 1);
lean_ctor_set(x_497, 0, x_471);
return x_497;
}
else
{
lean_object* x_500; lean_object* x_501; 
x_500 = lean_ctor_get(x_497, 1);
lean_inc(x_500);
lean_dec(x_497);
x_501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_501, 0, x_471);
lean_ctor_set(x_501, 1, x_500);
return x_501;
}
}
}
}
}
else
{
uint8_t x_533; 
x_533 = l_Array_isEmpty___rarg(x_4);
if (x_533 == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_571; 
x_534 = lean_box(0);
x_535 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_538 = x_535;
} else {
 lean_dec_ref(x_535);
 x_538 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_571 = l_Lean_Elab_Term_elabTerm(x_1, x_534, x_397, x_9, x_10, x_11, x_12, x_13, x_14, x_537);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_571, 1);
lean_inc(x_573);
lean_dec(x_571);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_574 = l___private_Lean_Elab_App_20__elabAppLVals(x_572, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_573);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; uint8_t x_578; 
lean_dec(x_538);
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_574, 1);
lean_inc(x_576);
lean_dec(x_574);
x_577 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_576);
x_578 = !lean_is_exclusive(x_577);
if (x_578 == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; uint8_t x_582; 
x_579 = lean_ctor_get(x_577, 0);
x_580 = lean_ctor_get(x_577, 1);
x_581 = l_Lean_Elab_Term_SavedState_restore(x_536, x_9, x_10, x_11, x_12, x_13, x_14, x_580);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_582 = !lean_is_exclusive(x_581);
if (x_582 == 0)
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_581, 1);
x_584 = lean_ctor_get(x_581, 0);
lean_dec(x_584);
lean_ctor_set(x_581, 1, x_579);
lean_ctor_set(x_581, 0, x_575);
x_585 = lean_array_push(x_8, x_581);
lean_ctor_set(x_577, 1, x_583);
lean_ctor_set(x_577, 0, x_585);
return x_577;
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_586 = lean_ctor_get(x_581, 1);
lean_inc(x_586);
lean_dec(x_581);
x_587 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_587, 0, x_575);
lean_ctor_set(x_587, 1, x_579);
x_588 = lean_array_push(x_8, x_587);
lean_ctor_set(x_577, 1, x_586);
lean_ctor_set(x_577, 0, x_588);
return x_577;
}
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_589 = lean_ctor_get(x_577, 0);
x_590 = lean_ctor_get(x_577, 1);
lean_inc(x_590);
lean_inc(x_589);
lean_dec(x_577);
x_591 = l_Lean_Elab_Term_SavedState_restore(x_536, x_9, x_10, x_11, x_12, x_13, x_14, x_590);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_592 = lean_ctor_get(x_591, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 lean_ctor_release(x_591, 1);
 x_593 = x_591;
} else {
 lean_dec_ref(x_591);
 x_593 = lean_box(0);
}
if (lean_is_scalar(x_593)) {
 x_594 = lean_alloc_ctor(0, 2, 0);
} else {
 x_594 = x_593;
}
lean_ctor_set(x_594, 0, x_575);
lean_ctor_set(x_594, 1, x_589);
x_595 = lean_array_push(x_8, x_594);
x_596 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_596, 0, x_595);
lean_ctor_set(x_596, 1, x_592);
return x_596;
}
}
else
{
lean_object* x_597; lean_object* x_598; 
x_597 = lean_ctor_get(x_574, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_574, 1);
lean_inc(x_598);
lean_dec(x_574);
x_539 = x_597;
x_540 = x_598;
goto block_570;
}
}
else
{
lean_object* x_599; lean_object* x_600; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_599 = lean_ctor_get(x_571, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_571, 1);
lean_inc(x_600);
lean_dec(x_571);
x_539 = x_599;
x_540 = x_600;
goto block_570;
}
block_570:
{
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_541; uint8_t x_542; 
lean_dec(x_538);
x_541 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_540);
x_542 = !lean_is_exclusive(x_541);
if (x_542 == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; uint8_t x_546; 
x_543 = lean_ctor_get(x_541, 0);
x_544 = lean_ctor_get(x_541, 1);
x_545 = l_Lean_Elab_Term_SavedState_restore(x_536, x_9, x_10, x_11, x_12, x_13, x_14, x_544);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_546 = !lean_is_exclusive(x_545);
if (x_546 == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_547 = lean_ctor_get(x_545, 1);
x_548 = lean_ctor_get(x_545, 0);
lean_dec(x_548);
lean_ctor_set_tag(x_545, 1);
lean_ctor_set(x_545, 1, x_543);
lean_ctor_set(x_545, 0, x_539);
x_549 = lean_array_push(x_8, x_545);
lean_ctor_set(x_541, 1, x_547);
lean_ctor_set(x_541, 0, x_549);
return x_541;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_545, 1);
lean_inc(x_550);
lean_dec(x_545);
x_551 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_551, 0, x_539);
lean_ctor_set(x_551, 1, x_543);
x_552 = lean_array_push(x_8, x_551);
lean_ctor_set(x_541, 1, x_550);
lean_ctor_set(x_541, 0, x_552);
return x_541;
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_553 = lean_ctor_get(x_541, 0);
x_554 = lean_ctor_get(x_541, 1);
lean_inc(x_554);
lean_inc(x_553);
lean_dec(x_541);
x_555 = l_Lean_Elab_Term_SavedState_restore(x_536, x_9, x_10, x_11, x_12, x_13, x_14, x_554);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_556 = lean_ctor_get(x_555, 1);
lean_inc(x_556);
if (lean_is_exclusive(x_555)) {
 lean_ctor_release(x_555, 0);
 lean_ctor_release(x_555, 1);
 x_557 = x_555;
} else {
 lean_dec_ref(x_555);
 x_557 = lean_box(0);
}
if (lean_is_scalar(x_557)) {
 x_558 = lean_alloc_ctor(1, 2, 0);
} else {
 x_558 = x_557;
 lean_ctor_set_tag(x_558, 1);
}
lean_ctor_set(x_558, 0, x_539);
lean_ctor_set(x_558, 1, x_553);
x_559 = lean_array_push(x_8, x_558);
x_560 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_560, 0, x_559);
lean_ctor_set(x_560, 1, x_556);
return x_560;
}
}
else
{
lean_object* x_561; lean_object* x_562; uint8_t x_563; 
lean_dec(x_8);
x_561 = lean_ctor_get(x_539, 0);
lean_inc(x_561);
x_562 = l_Lean_Elab_postponeExceptionId;
x_563 = lean_nat_dec_eq(x_561, x_562);
lean_dec(x_561);
if (x_563 == 0)
{
lean_object* x_564; 
lean_dec(x_536);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_538)) {
 x_564 = lean_alloc_ctor(1, 2, 0);
} else {
 x_564 = x_538;
 lean_ctor_set_tag(x_564, 1);
}
lean_ctor_set(x_564, 0, x_539);
lean_ctor_set(x_564, 1, x_540);
return x_564;
}
else
{
lean_object* x_565; uint8_t x_566; 
lean_dec(x_538);
x_565 = l_Lean_Elab_Term_SavedState_restore(x_536, x_9, x_10, x_11, x_12, x_13, x_14, x_540);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_566 = !lean_is_exclusive(x_565);
if (x_566 == 0)
{
lean_object* x_567; 
x_567 = lean_ctor_get(x_565, 0);
lean_dec(x_567);
lean_ctor_set_tag(x_565, 1);
lean_ctor_set(x_565, 0, x_539);
return x_565;
}
else
{
lean_object* x_568; lean_object* x_569; 
x_568 = lean_ctor_get(x_565, 1);
lean_inc(x_568);
lean_dec(x_565);
x_569 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_569, 0, x_539);
lean_ctor_set(x_569, 1, x_568);
return x_569;
}
}
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
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; uint8_t x_637; lean_object* x_638; 
x_601 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_604 = x_601;
} else {
 lean_dec_ref(x_601);
 x_604 = lean_box(0);
}
x_637 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_638 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_637, x_9, x_10, x_11, x_12, x_13, x_14, x_603);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; uint8_t x_642; 
lean_dec(x_604);
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_638, 1);
lean_inc(x_640);
lean_dec(x_638);
x_641 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_640);
x_642 = !lean_is_exclusive(x_641);
if (x_642 == 0)
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; uint8_t x_646; 
x_643 = lean_ctor_get(x_641, 0);
x_644 = lean_ctor_get(x_641, 1);
x_645 = l_Lean_Elab_Term_SavedState_restore(x_602, x_9, x_10, x_11, x_12, x_13, x_14, x_644);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_646 = !lean_is_exclusive(x_645);
if (x_646 == 0)
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_647 = lean_ctor_get(x_645, 1);
x_648 = lean_ctor_get(x_645, 0);
lean_dec(x_648);
lean_ctor_set(x_645, 1, x_643);
lean_ctor_set(x_645, 0, x_639);
x_649 = lean_array_push(x_8, x_645);
lean_ctor_set(x_641, 1, x_647);
lean_ctor_set(x_641, 0, x_649);
return x_641;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_650 = lean_ctor_get(x_645, 1);
lean_inc(x_650);
lean_dec(x_645);
x_651 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_651, 0, x_639);
lean_ctor_set(x_651, 1, x_643);
x_652 = lean_array_push(x_8, x_651);
lean_ctor_set(x_641, 1, x_650);
lean_ctor_set(x_641, 0, x_652);
return x_641;
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_653 = lean_ctor_get(x_641, 0);
x_654 = lean_ctor_get(x_641, 1);
lean_inc(x_654);
lean_inc(x_653);
lean_dec(x_641);
x_655 = l_Lean_Elab_Term_SavedState_restore(x_602, x_9, x_10, x_11, x_12, x_13, x_14, x_654);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_656 = lean_ctor_get(x_655, 1);
lean_inc(x_656);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_657 = x_655;
} else {
 lean_dec_ref(x_655);
 x_657 = lean_box(0);
}
if (lean_is_scalar(x_657)) {
 x_658 = lean_alloc_ctor(0, 2, 0);
} else {
 x_658 = x_657;
}
lean_ctor_set(x_658, 0, x_639);
lean_ctor_set(x_658, 1, x_653);
x_659 = lean_array_push(x_8, x_658);
x_660 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_660, 0, x_659);
lean_ctor_set(x_660, 1, x_656);
return x_660;
}
}
else
{
lean_object* x_661; lean_object* x_662; 
x_661 = lean_ctor_get(x_638, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_638, 1);
lean_inc(x_662);
lean_dec(x_638);
x_605 = x_661;
x_606 = x_662;
goto block_636;
}
block_636:
{
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_607; uint8_t x_608; 
lean_dec(x_604);
x_607 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_606);
x_608 = !lean_is_exclusive(x_607);
if (x_608 == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; uint8_t x_612; 
x_609 = lean_ctor_get(x_607, 0);
x_610 = lean_ctor_get(x_607, 1);
x_611 = l_Lean_Elab_Term_SavedState_restore(x_602, x_9, x_10, x_11, x_12, x_13, x_14, x_610);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_612 = !lean_is_exclusive(x_611);
if (x_612 == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = lean_ctor_get(x_611, 1);
x_614 = lean_ctor_get(x_611, 0);
lean_dec(x_614);
lean_ctor_set_tag(x_611, 1);
lean_ctor_set(x_611, 1, x_609);
lean_ctor_set(x_611, 0, x_605);
x_615 = lean_array_push(x_8, x_611);
lean_ctor_set(x_607, 1, x_613);
lean_ctor_set(x_607, 0, x_615);
return x_607;
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_616 = lean_ctor_get(x_611, 1);
lean_inc(x_616);
lean_dec(x_611);
x_617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_617, 0, x_605);
lean_ctor_set(x_617, 1, x_609);
x_618 = lean_array_push(x_8, x_617);
lean_ctor_set(x_607, 1, x_616);
lean_ctor_set(x_607, 0, x_618);
return x_607;
}
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_619 = lean_ctor_get(x_607, 0);
x_620 = lean_ctor_get(x_607, 1);
lean_inc(x_620);
lean_inc(x_619);
lean_dec(x_607);
x_621 = l_Lean_Elab_Term_SavedState_restore(x_602, x_9, x_10, x_11, x_12, x_13, x_14, x_620);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_622 = lean_ctor_get(x_621, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 x_623 = x_621;
} else {
 lean_dec_ref(x_621);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(1, 2, 0);
} else {
 x_624 = x_623;
 lean_ctor_set_tag(x_624, 1);
}
lean_ctor_set(x_624, 0, x_605);
lean_ctor_set(x_624, 1, x_619);
x_625 = lean_array_push(x_8, x_624);
x_626 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_626, 0, x_625);
lean_ctor_set(x_626, 1, x_622);
return x_626;
}
}
else
{
lean_object* x_627; lean_object* x_628; uint8_t x_629; 
lean_dec(x_8);
x_627 = lean_ctor_get(x_605, 0);
lean_inc(x_627);
x_628 = l_Lean_Elab_postponeExceptionId;
x_629 = lean_nat_dec_eq(x_627, x_628);
lean_dec(x_627);
if (x_629 == 0)
{
lean_object* x_630; 
lean_dec(x_602);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_604)) {
 x_630 = lean_alloc_ctor(1, 2, 0);
} else {
 x_630 = x_604;
 lean_ctor_set_tag(x_630, 1);
}
lean_ctor_set(x_630, 0, x_605);
lean_ctor_set(x_630, 1, x_606);
return x_630;
}
else
{
lean_object* x_631; uint8_t x_632; 
lean_dec(x_604);
x_631 = l_Lean_Elab_Term_SavedState_restore(x_602, x_9, x_10, x_11, x_12, x_13, x_14, x_606);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_632 = !lean_is_exclusive(x_631);
if (x_632 == 0)
{
lean_object* x_633; 
x_633 = lean_ctor_get(x_631, 0);
lean_dec(x_633);
lean_ctor_set_tag(x_631, 1);
lean_ctor_set(x_631, 0, x_605);
return x_631;
}
else
{
lean_object* x_634; lean_object* x_635; 
x_634 = lean_ctor_get(x_631, 1);
lean_inc(x_634);
lean_dec(x_631);
x_635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_635, 0, x_605);
lean_ctor_set(x_635, 1, x_634);
return x_635;
}
}
}
}
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_699; 
x_663 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_663, 1);
lean_inc(x_665);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 x_666 = x_663;
} else {
 lean_dec_ref(x_663);
 x_666 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_699 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_397, x_9, x_10, x_11, x_12, x_13, x_14, x_665);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; uint8_t x_703; 
lean_dec(x_666);
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_699, 1);
lean_inc(x_701);
lean_dec(x_699);
x_702 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_701);
x_703 = !lean_is_exclusive(x_702);
if (x_703 == 0)
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; uint8_t x_707; 
x_704 = lean_ctor_get(x_702, 0);
x_705 = lean_ctor_get(x_702, 1);
x_706 = l_Lean_Elab_Term_SavedState_restore(x_664, x_9, x_10, x_11, x_12, x_13, x_14, x_705);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_707 = !lean_is_exclusive(x_706);
if (x_707 == 0)
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; 
x_708 = lean_ctor_get(x_706, 1);
x_709 = lean_ctor_get(x_706, 0);
lean_dec(x_709);
lean_ctor_set(x_706, 1, x_704);
lean_ctor_set(x_706, 0, x_700);
x_710 = lean_array_push(x_8, x_706);
lean_ctor_set(x_702, 1, x_708);
lean_ctor_set(x_702, 0, x_710);
return x_702;
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_711 = lean_ctor_get(x_706, 1);
lean_inc(x_711);
lean_dec(x_706);
x_712 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_712, 0, x_700);
lean_ctor_set(x_712, 1, x_704);
x_713 = lean_array_push(x_8, x_712);
lean_ctor_set(x_702, 1, x_711);
lean_ctor_set(x_702, 0, x_713);
return x_702;
}
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_714 = lean_ctor_get(x_702, 0);
x_715 = lean_ctor_get(x_702, 1);
lean_inc(x_715);
lean_inc(x_714);
lean_dec(x_702);
x_716 = l_Lean_Elab_Term_SavedState_restore(x_664, x_9, x_10, x_11, x_12, x_13, x_14, x_715);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_717 = lean_ctor_get(x_716, 1);
lean_inc(x_717);
if (lean_is_exclusive(x_716)) {
 lean_ctor_release(x_716, 0);
 lean_ctor_release(x_716, 1);
 x_718 = x_716;
} else {
 lean_dec_ref(x_716);
 x_718 = lean_box(0);
}
if (lean_is_scalar(x_718)) {
 x_719 = lean_alloc_ctor(0, 2, 0);
} else {
 x_719 = x_718;
}
lean_ctor_set(x_719, 0, x_700);
lean_ctor_set(x_719, 1, x_714);
x_720 = lean_array_push(x_8, x_719);
x_721 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_721, 0, x_720);
lean_ctor_set(x_721, 1, x_717);
return x_721;
}
}
else
{
lean_object* x_722; lean_object* x_723; 
x_722 = lean_ctor_get(x_699, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_699, 1);
lean_inc(x_723);
lean_dec(x_699);
x_667 = x_722;
x_668 = x_723;
goto block_698;
}
block_698:
{
if (lean_obj_tag(x_667) == 0)
{
lean_object* x_669; uint8_t x_670; 
lean_dec(x_666);
x_669 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_668);
x_670 = !lean_is_exclusive(x_669);
if (x_670 == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; uint8_t x_674; 
x_671 = lean_ctor_get(x_669, 0);
x_672 = lean_ctor_get(x_669, 1);
x_673 = l_Lean_Elab_Term_SavedState_restore(x_664, x_9, x_10, x_11, x_12, x_13, x_14, x_672);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_674 = !lean_is_exclusive(x_673);
if (x_674 == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_675 = lean_ctor_get(x_673, 1);
x_676 = lean_ctor_get(x_673, 0);
lean_dec(x_676);
lean_ctor_set_tag(x_673, 1);
lean_ctor_set(x_673, 1, x_671);
lean_ctor_set(x_673, 0, x_667);
x_677 = lean_array_push(x_8, x_673);
lean_ctor_set(x_669, 1, x_675);
lean_ctor_set(x_669, 0, x_677);
return x_669;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_678 = lean_ctor_get(x_673, 1);
lean_inc(x_678);
lean_dec(x_673);
x_679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_679, 0, x_667);
lean_ctor_set(x_679, 1, x_671);
x_680 = lean_array_push(x_8, x_679);
lean_ctor_set(x_669, 1, x_678);
lean_ctor_set(x_669, 0, x_680);
return x_669;
}
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_681 = lean_ctor_get(x_669, 0);
x_682 = lean_ctor_get(x_669, 1);
lean_inc(x_682);
lean_inc(x_681);
lean_dec(x_669);
x_683 = l_Lean_Elab_Term_SavedState_restore(x_664, x_9, x_10, x_11, x_12, x_13, x_14, x_682);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_684 = lean_ctor_get(x_683, 1);
lean_inc(x_684);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 lean_ctor_release(x_683, 1);
 x_685 = x_683;
} else {
 lean_dec_ref(x_683);
 x_685 = lean_box(0);
}
if (lean_is_scalar(x_685)) {
 x_686 = lean_alloc_ctor(1, 2, 0);
} else {
 x_686 = x_685;
 lean_ctor_set_tag(x_686, 1);
}
lean_ctor_set(x_686, 0, x_667);
lean_ctor_set(x_686, 1, x_681);
x_687 = lean_array_push(x_8, x_686);
x_688 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_688, 0, x_687);
lean_ctor_set(x_688, 1, x_684);
return x_688;
}
}
else
{
lean_object* x_689; lean_object* x_690; uint8_t x_691; 
lean_dec(x_8);
x_689 = lean_ctor_get(x_667, 0);
lean_inc(x_689);
x_690 = l_Lean_Elab_postponeExceptionId;
x_691 = lean_nat_dec_eq(x_689, x_690);
lean_dec(x_689);
if (x_691 == 0)
{
lean_object* x_692; 
lean_dec(x_664);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_666)) {
 x_692 = lean_alloc_ctor(1, 2, 0);
} else {
 x_692 = x_666;
 lean_ctor_set_tag(x_692, 1);
}
lean_ctor_set(x_692, 0, x_667);
lean_ctor_set(x_692, 1, x_668);
return x_692;
}
else
{
lean_object* x_693; uint8_t x_694; 
lean_dec(x_666);
x_693 = l_Lean_Elab_Term_SavedState_restore(x_664, x_9, x_10, x_11, x_12, x_13, x_14, x_668);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_694 = !lean_is_exclusive(x_693);
if (x_694 == 0)
{
lean_object* x_695; 
x_695 = lean_ctor_get(x_693, 0);
lean_dec(x_695);
lean_ctor_set_tag(x_693, 1);
lean_ctor_set(x_693, 0, x_667);
return x_693;
}
else
{
lean_object* x_696; lean_object* x_697; 
x_696 = lean_ctor_get(x_693, 1);
lean_inc(x_696);
lean_dec(x_693);
x_697 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_697, 0, x_667);
lean_ctor_set(x_697, 1, x_696);
return x_697;
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
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_727 = lean_unsigned_to_nat(2u);
x_728 = l_Lean_Syntax_getArg(x_1, x_727);
lean_dec(x_1);
x_729 = l_Lean_Syntax_getArgs(x_728);
lean_dec(x_728);
x_730 = l_Array_empty___closed__1;
x_731 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_727, x_729, x_393, x_730);
lean_dec(x_729);
lean_inc(x_9);
x_732 = l_Lean_Elab_Term_elabExplicitUnivs(x_731, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_731);
if (lean_obj_tag(x_732) == 0)
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; 
x_733 = lean_ctor_get(x_732, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_732, 1);
lean_inc(x_734);
lean_dec(x_732);
x_735 = l___private_Lean_Elab_App_21__elabAppFnId(x_394, x_733, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_734);
return x_735;
}
else
{
uint8_t x_736; 
lean_dec(x_394);
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
x_736 = !lean_is_exclusive(x_732);
if (x_736 == 0)
{
return x_732;
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_737 = lean_ctor_get(x_732, 0);
x_738 = lean_ctor_get(x_732, 1);
lean_inc(x_738);
lean_inc(x_737);
lean_dec(x_732);
x_739 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_739, 0, x_737);
lean_ctor_set(x_739, 1, x_738);
return x_739;
}
}
}
}
}
}
else
{
lean_object* x_748; lean_object* x_749; 
x_748 = lean_box(0);
x_749 = l___private_Lean_Elab_App_21__elabAppFnId(x_1, x_748, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_749;
}
}
else
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; uint8_t x_753; 
x_750 = lean_unsigned_to_nat(0u);
x_751 = l_Lean_Syntax_getArg(x_1, x_750);
x_752 = l_Lean_identKind___closed__2;
x_753 = l_Lean_Syntax_isOfKind(x_751, x_752);
if (x_753 == 0)
{
uint8_t x_754; uint8_t x_755; 
x_754 = l_List_isEmpty___rarg(x_2);
if (x_7 == 0)
{
uint8_t x_1083; 
x_1083 = 1;
x_755 = x_1083;
goto block_1082;
}
else
{
uint8_t x_1084; 
x_1084 = 0;
x_755 = x_1084;
goto block_1082;
}
block_1082:
{
if (x_754 == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_793; 
x_756 = lean_box(0);
x_757 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_758 = lean_ctor_get(x_757, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_757, 1);
lean_inc(x_759);
if (lean_is_exclusive(x_757)) {
 lean_ctor_release(x_757, 0);
 lean_ctor_release(x_757, 1);
 x_760 = x_757;
} else {
 lean_dec_ref(x_757);
 x_760 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_793 = l_Lean_Elab_Term_elabTerm(x_1, x_756, x_755, x_9, x_10, x_11, x_12, x_13, x_14, x_759);
if (lean_obj_tag(x_793) == 0)
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; 
x_794 = lean_ctor_get(x_793, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_793, 1);
lean_inc(x_795);
lean_dec(x_793);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_796 = l___private_Lean_Elab_App_20__elabAppLVals(x_794, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_795);
if (lean_obj_tag(x_796) == 0)
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; uint8_t x_800; 
lean_dec(x_760);
x_797 = lean_ctor_get(x_796, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_796, 1);
lean_inc(x_798);
lean_dec(x_796);
x_799 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_798);
x_800 = !lean_is_exclusive(x_799);
if (x_800 == 0)
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; uint8_t x_804; 
x_801 = lean_ctor_get(x_799, 0);
x_802 = lean_ctor_get(x_799, 1);
x_803 = l_Lean_Elab_Term_SavedState_restore(x_758, x_9, x_10, x_11, x_12, x_13, x_14, x_802);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_804 = !lean_is_exclusive(x_803);
if (x_804 == 0)
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_805 = lean_ctor_get(x_803, 1);
x_806 = lean_ctor_get(x_803, 0);
lean_dec(x_806);
lean_ctor_set(x_803, 1, x_801);
lean_ctor_set(x_803, 0, x_797);
x_807 = lean_array_push(x_8, x_803);
lean_ctor_set(x_799, 1, x_805);
lean_ctor_set(x_799, 0, x_807);
return x_799;
}
else
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_808 = lean_ctor_get(x_803, 1);
lean_inc(x_808);
lean_dec(x_803);
x_809 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_809, 0, x_797);
lean_ctor_set(x_809, 1, x_801);
x_810 = lean_array_push(x_8, x_809);
lean_ctor_set(x_799, 1, x_808);
lean_ctor_set(x_799, 0, x_810);
return x_799;
}
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; 
x_811 = lean_ctor_get(x_799, 0);
x_812 = lean_ctor_get(x_799, 1);
lean_inc(x_812);
lean_inc(x_811);
lean_dec(x_799);
x_813 = l_Lean_Elab_Term_SavedState_restore(x_758, x_9, x_10, x_11, x_12, x_13, x_14, x_812);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_814 = lean_ctor_get(x_813, 1);
lean_inc(x_814);
if (lean_is_exclusive(x_813)) {
 lean_ctor_release(x_813, 0);
 lean_ctor_release(x_813, 1);
 x_815 = x_813;
} else {
 lean_dec_ref(x_813);
 x_815 = lean_box(0);
}
if (lean_is_scalar(x_815)) {
 x_816 = lean_alloc_ctor(0, 2, 0);
} else {
 x_816 = x_815;
}
lean_ctor_set(x_816, 0, x_797);
lean_ctor_set(x_816, 1, x_811);
x_817 = lean_array_push(x_8, x_816);
x_818 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_818, 0, x_817);
lean_ctor_set(x_818, 1, x_814);
return x_818;
}
}
else
{
lean_object* x_819; lean_object* x_820; 
x_819 = lean_ctor_get(x_796, 0);
lean_inc(x_819);
x_820 = lean_ctor_get(x_796, 1);
lean_inc(x_820);
lean_dec(x_796);
x_761 = x_819;
x_762 = x_820;
goto block_792;
}
}
else
{
lean_object* x_821; lean_object* x_822; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_821 = lean_ctor_get(x_793, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_793, 1);
lean_inc(x_822);
lean_dec(x_793);
x_761 = x_821;
x_762 = x_822;
goto block_792;
}
block_792:
{
if (lean_obj_tag(x_761) == 0)
{
lean_object* x_763; uint8_t x_764; 
lean_dec(x_760);
x_763 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_762);
x_764 = !lean_is_exclusive(x_763);
if (x_764 == 0)
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; uint8_t x_768; 
x_765 = lean_ctor_get(x_763, 0);
x_766 = lean_ctor_get(x_763, 1);
x_767 = l_Lean_Elab_Term_SavedState_restore(x_758, x_9, x_10, x_11, x_12, x_13, x_14, x_766);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_768 = !lean_is_exclusive(x_767);
if (x_768 == 0)
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; 
x_769 = lean_ctor_get(x_767, 1);
x_770 = lean_ctor_get(x_767, 0);
lean_dec(x_770);
lean_ctor_set_tag(x_767, 1);
lean_ctor_set(x_767, 1, x_765);
lean_ctor_set(x_767, 0, x_761);
x_771 = lean_array_push(x_8, x_767);
lean_ctor_set(x_763, 1, x_769);
lean_ctor_set(x_763, 0, x_771);
return x_763;
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_772 = lean_ctor_get(x_767, 1);
lean_inc(x_772);
lean_dec(x_767);
x_773 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_773, 0, x_761);
lean_ctor_set(x_773, 1, x_765);
x_774 = lean_array_push(x_8, x_773);
lean_ctor_set(x_763, 1, x_772);
lean_ctor_set(x_763, 0, x_774);
return x_763;
}
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_775 = lean_ctor_get(x_763, 0);
x_776 = lean_ctor_get(x_763, 1);
lean_inc(x_776);
lean_inc(x_775);
lean_dec(x_763);
x_777 = l_Lean_Elab_Term_SavedState_restore(x_758, x_9, x_10, x_11, x_12, x_13, x_14, x_776);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_778 = lean_ctor_get(x_777, 1);
lean_inc(x_778);
if (lean_is_exclusive(x_777)) {
 lean_ctor_release(x_777, 0);
 lean_ctor_release(x_777, 1);
 x_779 = x_777;
} else {
 lean_dec_ref(x_777);
 x_779 = lean_box(0);
}
if (lean_is_scalar(x_779)) {
 x_780 = lean_alloc_ctor(1, 2, 0);
} else {
 x_780 = x_779;
 lean_ctor_set_tag(x_780, 1);
}
lean_ctor_set(x_780, 0, x_761);
lean_ctor_set(x_780, 1, x_775);
x_781 = lean_array_push(x_8, x_780);
x_782 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_778);
return x_782;
}
}
else
{
lean_object* x_783; lean_object* x_784; uint8_t x_785; 
lean_dec(x_8);
x_783 = lean_ctor_get(x_761, 0);
lean_inc(x_783);
x_784 = l_Lean_Elab_postponeExceptionId;
x_785 = lean_nat_dec_eq(x_783, x_784);
lean_dec(x_783);
if (x_785 == 0)
{
lean_object* x_786; 
lean_dec(x_758);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_760)) {
 x_786 = lean_alloc_ctor(1, 2, 0);
} else {
 x_786 = x_760;
 lean_ctor_set_tag(x_786, 1);
}
lean_ctor_set(x_786, 0, x_761);
lean_ctor_set(x_786, 1, x_762);
return x_786;
}
else
{
lean_object* x_787; uint8_t x_788; 
lean_dec(x_760);
x_787 = l_Lean_Elab_Term_SavedState_restore(x_758, x_9, x_10, x_11, x_12, x_13, x_14, x_762);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_788 = !lean_is_exclusive(x_787);
if (x_788 == 0)
{
lean_object* x_789; 
x_789 = lean_ctor_get(x_787, 0);
lean_dec(x_789);
lean_ctor_set_tag(x_787, 1);
lean_ctor_set(x_787, 0, x_761);
return x_787;
}
else
{
lean_object* x_790; lean_object* x_791; 
x_790 = lean_ctor_get(x_787, 1);
lean_inc(x_790);
lean_dec(x_787);
x_791 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_791, 0, x_761);
lean_ctor_set(x_791, 1, x_790);
return x_791;
}
}
}
}
}
else
{
uint8_t x_823; 
x_823 = l_Array_isEmpty___rarg(x_3);
if (x_823 == 0)
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_861; 
x_824 = lean_box(0);
x_825 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 x_828 = x_825;
} else {
 lean_dec_ref(x_825);
 x_828 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_861 = l_Lean_Elab_Term_elabTerm(x_1, x_824, x_755, x_9, x_10, x_11, x_12, x_13, x_14, x_827);
if (lean_obj_tag(x_861) == 0)
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; 
x_862 = lean_ctor_get(x_861, 0);
lean_inc(x_862);
x_863 = lean_ctor_get(x_861, 1);
lean_inc(x_863);
lean_dec(x_861);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_864 = l___private_Lean_Elab_App_20__elabAppLVals(x_862, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_863);
if (lean_obj_tag(x_864) == 0)
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; uint8_t x_868; 
lean_dec(x_828);
x_865 = lean_ctor_get(x_864, 0);
lean_inc(x_865);
x_866 = lean_ctor_get(x_864, 1);
lean_inc(x_866);
lean_dec(x_864);
x_867 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_866);
x_868 = !lean_is_exclusive(x_867);
if (x_868 == 0)
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; uint8_t x_872; 
x_869 = lean_ctor_get(x_867, 0);
x_870 = lean_ctor_get(x_867, 1);
x_871 = l_Lean_Elab_Term_SavedState_restore(x_826, x_9, x_10, x_11, x_12, x_13, x_14, x_870);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_872 = !lean_is_exclusive(x_871);
if (x_872 == 0)
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_873 = lean_ctor_get(x_871, 1);
x_874 = lean_ctor_get(x_871, 0);
lean_dec(x_874);
lean_ctor_set(x_871, 1, x_869);
lean_ctor_set(x_871, 0, x_865);
x_875 = lean_array_push(x_8, x_871);
lean_ctor_set(x_867, 1, x_873);
lean_ctor_set(x_867, 0, x_875);
return x_867;
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; 
x_876 = lean_ctor_get(x_871, 1);
lean_inc(x_876);
lean_dec(x_871);
x_877 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_877, 0, x_865);
lean_ctor_set(x_877, 1, x_869);
x_878 = lean_array_push(x_8, x_877);
lean_ctor_set(x_867, 1, x_876);
lean_ctor_set(x_867, 0, x_878);
return x_867;
}
}
else
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
x_879 = lean_ctor_get(x_867, 0);
x_880 = lean_ctor_get(x_867, 1);
lean_inc(x_880);
lean_inc(x_879);
lean_dec(x_867);
x_881 = l_Lean_Elab_Term_SavedState_restore(x_826, x_9, x_10, x_11, x_12, x_13, x_14, x_880);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_882 = lean_ctor_get(x_881, 1);
lean_inc(x_882);
if (lean_is_exclusive(x_881)) {
 lean_ctor_release(x_881, 0);
 lean_ctor_release(x_881, 1);
 x_883 = x_881;
} else {
 lean_dec_ref(x_881);
 x_883 = lean_box(0);
}
if (lean_is_scalar(x_883)) {
 x_884 = lean_alloc_ctor(0, 2, 0);
} else {
 x_884 = x_883;
}
lean_ctor_set(x_884, 0, x_865);
lean_ctor_set(x_884, 1, x_879);
x_885 = lean_array_push(x_8, x_884);
x_886 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_886, 0, x_885);
lean_ctor_set(x_886, 1, x_882);
return x_886;
}
}
else
{
lean_object* x_887; lean_object* x_888; 
x_887 = lean_ctor_get(x_864, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_864, 1);
lean_inc(x_888);
lean_dec(x_864);
x_829 = x_887;
x_830 = x_888;
goto block_860;
}
}
else
{
lean_object* x_889; lean_object* x_890; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_889 = lean_ctor_get(x_861, 0);
lean_inc(x_889);
x_890 = lean_ctor_get(x_861, 1);
lean_inc(x_890);
lean_dec(x_861);
x_829 = x_889;
x_830 = x_890;
goto block_860;
}
block_860:
{
if (lean_obj_tag(x_829) == 0)
{
lean_object* x_831; uint8_t x_832; 
lean_dec(x_828);
x_831 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_830);
x_832 = !lean_is_exclusive(x_831);
if (x_832 == 0)
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; uint8_t x_836; 
x_833 = lean_ctor_get(x_831, 0);
x_834 = lean_ctor_get(x_831, 1);
x_835 = l_Lean_Elab_Term_SavedState_restore(x_826, x_9, x_10, x_11, x_12, x_13, x_14, x_834);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_836 = !lean_is_exclusive(x_835);
if (x_836 == 0)
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; 
x_837 = lean_ctor_get(x_835, 1);
x_838 = lean_ctor_get(x_835, 0);
lean_dec(x_838);
lean_ctor_set_tag(x_835, 1);
lean_ctor_set(x_835, 1, x_833);
lean_ctor_set(x_835, 0, x_829);
x_839 = lean_array_push(x_8, x_835);
lean_ctor_set(x_831, 1, x_837);
lean_ctor_set(x_831, 0, x_839);
return x_831;
}
else
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; 
x_840 = lean_ctor_get(x_835, 1);
lean_inc(x_840);
lean_dec(x_835);
x_841 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_841, 0, x_829);
lean_ctor_set(x_841, 1, x_833);
x_842 = lean_array_push(x_8, x_841);
lean_ctor_set(x_831, 1, x_840);
lean_ctor_set(x_831, 0, x_842);
return x_831;
}
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; 
x_843 = lean_ctor_get(x_831, 0);
x_844 = lean_ctor_get(x_831, 1);
lean_inc(x_844);
lean_inc(x_843);
lean_dec(x_831);
x_845 = l_Lean_Elab_Term_SavedState_restore(x_826, x_9, x_10, x_11, x_12, x_13, x_14, x_844);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_846 = lean_ctor_get(x_845, 1);
lean_inc(x_846);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 lean_ctor_release(x_845, 1);
 x_847 = x_845;
} else {
 lean_dec_ref(x_845);
 x_847 = lean_box(0);
}
if (lean_is_scalar(x_847)) {
 x_848 = lean_alloc_ctor(1, 2, 0);
} else {
 x_848 = x_847;
 lean_ctor_set_tag(x_848, 1);
}
lean_ctor_set(x_848, 0, x_829);
lean_ctor_set(x_848, 1, x_843);
x_849 = lean_array_push(x_8, x_848);
x_850 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_850, 0, x_849);
lean_ctor_set(x_850, 1, x_846);
return x_850;
}
}
else
{
lean_object* x_851; lean_object* x_852; uint8_t x_853; 
lean_dec(x_8);
x_851 = lean_ctor_get(x_829, 0);
lean_inc(x_851);
x_852 = l_Lean_Elab_postponeExceptionId;
x_853 = lean_nat_dec_eq(x_851, x_852);
lean_dec(x_851);
if (x_853 == 0)
{
lean_object* x_854; 
lean_dec(x_826);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_828)) {
 x_854 = lean_alloc_ctor(1, 2, 0);
} else {
 x_854 = x_828;
 lean_ctor_set_tag(x_854, 1);
}
lean_ctor_set(x_854, 0, x_829);
lean_ctor_set(x_854, 1, x_830);
return x_854;
}
else
{
lean_object* x_855; uint8_t x_856; 
lean_dec(x_828);
x_855 = l_Lean_Elab_Term_SavedState_restore(x_826, x_9, x_10, x_11, x_12, x_13, x_14, x_830);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_856 = !lean_is_exclusive(x_855);
if (x_856 == 0)
{
lean_object* x_857; 
x_857 = lean_ctor_get(x_855, 0);
lean_dec(x_857);
lean_ctor_set_tag(x_855, 1);
lean_ctor_set(x_855, 0, x_829);
return x_855;
}
else
{
lean_object* x_858; lean_object* x_859; 
x_858 = lean_ctor_get(x_855, 1);
lean_inc(x_858);
lean_dec(x_855);
x_859 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_859, 0, x_829);
lean_ctor_set(x_859, 1, x_858);
return x_859;
}
}
}
}
}
else
{
uint8_t x_891; 
x_891 = l_Array_isEmpty___rarg(x_4);
if (x_891 == 0)
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_929; 
x_892 = lean_box(0);
x_893 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_894 = lean_ctor_get(x_893, 0);
lean_inc(x_894);
x_895 = lean_ctor_get(x_893, 1);
lean_inc(x_895);
if (lean_is_exclusive(x_893)) {
 lean_ctor_release(x_893, 0);
 lean_ctor_release(x_893, 1);
 x_896 = x_893;
} else {
 lean_dec_ref(x_893);
 x_896 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_929 = l_Lean_Elab_Term_elabTerm(x_1, x_892, x_755, x_9, x_10, x_11, x_12, x_13, x_14, x_895);
if (lean_obj_tag(x_929) == 0)
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; 
x_930 = lean_ctor_get(x_929, 0);
lean_inc(x_930);
x_931 = lean_ctor_get(x_929, 1);
lean_inc(x_931);
lean_dec(x_929);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_932 = l___private_Lean_Elab_App_20__elabAppLVals(x_930, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_931);
if (lean_obj_tag(x_932) == 0)
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; uint8_t x_936; 
lean_dec(x_896);
x_933 = lean_ctor_get(x_932, 0);
lean_inc(x_933);
x_934 = lean_ctor_get(x_932, 1);
lean_inc(x_934);
lean_dec(x_932);
x_935 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_934);
x_936 = !lean_is_exclusive(x_935);
if (x_936 == 0)
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; uint8_t x_940; 
x_937 = lean_ctor_get(x_935, 0);
x_938 = lean_ctor_get(x_935, 1);
x_939 = l_Lean_Elab_Term_SavedState_restore(x_894, x_9, x_10, x_11, x_12, x_13, x_14, x_938);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_940 = !lean_is_exclusive(x_939);
if (x_940 == 0)
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; 
x_941 = lean_ctor_get(x_939, 1);
x_942 = lean_ctor_get(x_939, 0);
lean_dec(x_942);
lean_ctor_set(x_939, 1, x_937);
lean_ctor_set(x_939, 0, x_933);
x_943 = lean_array_push(x_8, x_939);
lean_ctor_set(x_935, 1, x_941);
lean_ctor_set(x_935, 0, x_943);
return x_935;
}
else
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; 
x_944 = lean_ctor_get(x_939, 1);
lean_inc(x_944);
lean_dec(x_939);
x_945 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_945, 0, x_933);
lean_ctor_set(x_945, 1, x_937);
x_946 = lean_array_push(x_8, x_945);
lean_ctor_set(x_935, 1, x_944);
lean_ctor_set(x_935, 0, x_946);
return x_935;
}
}
else
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; 
x_947 = lean_ctor_get(x_935, 0);
x_948 = lean_ctor_get(x_935, 1);
lean_inc(x_948);
lean_inc(x_947);
lean_dec(x_935);
x_949 = l_Lean_Elab_Term_SavedState_restore(x_894, x_9, x_10, x_11, x_12, x_13, x_14, x_948);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_950 = lean_ctor_get(x_949, 1);
lean_inc(x_950);
if (lean_is_exclusive(x_949)) {
 lean_ctor_release(x_949, 0);
 lean_ctor_release(x_949, 1);
 x_951 = x_949;
} else {
 lean_dec_ref(x_949);
 x_951 = lean_box(0);
}
if (lean_is_scalar(x_951)) {
 x_952 = lean_alloc_ctor(0, 2, 0);
} else {
 x_952 = x_951;
}
lean_ctor_set(x_952, 0, x_933);
lean_ctor_set(x_952, 1, x_947);
x_953 = lean_array_push(x_8, x_952);
x_954 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_954, 0, x_953);
lean_ctor_set(x_954, 1, x_950);
return x_954;
}
}
else
{
lean_object* x_955; lean_object* x_956; 
x_955 = lean_ctor_get(x_932, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_932, 1);
lean_inc(x_956);
lean_dec(x_932);
x_897 = x_955;
x_898 = x_956;
goto block_928;
}
}
else
{
lean_object* x_957; lean_object* x_958; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_957 = lean_ctor_get(x_929, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_929, 1);
lean_inc(x_958);
lean_dec(x_929);
x_897 = x_957;
x_898 = x_958;
goto block_928;
}
block_928:
{
if (lean_obj_tag(x_897) == 0)
{
lean_object* x_899; uint8_t x_900; 
lean_dec(x_896);
x_899 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_898);
x_900 = !lean_is_exclusive(x_899);
if (x_900 == 0)
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; uint8_t x_904; 
x_901 = lean_ctor_get(x_899, 0);
x_902 = lean_ctor_get(x_899, 1);
x_903 = l_Lean_Elab_Term_SavedState_restore(x_894, x_9, x_10, x_11, x_12, x_13, x_14, x_902);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_904 = !lean_is_exclusive(x_903);
if (x_904 == 0)
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; 
x_905 = lean_ctor_get(x_903, 1);
x_906 = lean_ctor_get(x_903, 0);
lean_dec(x_906);
lean_ctor_set_tag(x_903, 1);
lean_ctor_set(x_903, 1, x_901);
lean_ctor_set(x_903, 0, x_897);
x_907 = lean_array_push(x_8, x_903);
lean_ctor_set(x_899, 1, x_905);
lean_ctor_set(x_899, 0, x_907);
return x_899;
}
else
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; 
x_908 = lean_ctor_get(x_903, 1);
lean_inc(x_908);
lean_dec(x_903);
x_909 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_909, 0, x_897);
lean_ctor_set(x_909, 1, x_901);
x_910 = lean_array_push(x_8, x_909);
lean_ctor_set(x_899, 1, x_908);
lean_ctor_set(x_899, 0, x_910);
return x_899;
}
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_911 = lean_ctor_get(x_899, 0);
x_912 = lean_ctor_get(x_899, 1);
lean_inc(x_912);
lean_inc(x_911);
lean_dec(x_899);
x_913 = l_Lean_Elab_Term_SavedState_restore(x_894, x_9, x_10, x_11, x_12, x_13, x_14, x_912);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_914 = lean_ctor_get(x_913, 1);
lean_inc(x_914);
if (lean_is_exclusive(x_913)) {
 lean_ctor_release(x_913, 0);
 lean_ctor_release(x_913, 1);
 x_915 = x_913;
} else {
 lean_dec_ref(x_913);
 x_915 = lean_box(0);
}
if (lean_is_scalar(x_915)) {
 x_916 = lean_alloc_ctor(1, 2, 0);
} else {
 x_916 = x_915;
 lean_ctor_set_tag(x_916, 1);
}
lean_ctor_set(x_916, 0, x_897);
lean_ctor_set(x_916, 1, x_911);
x_917 = lean_array_push(x_8, x_916);
x_918 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_918, 0, x_917);
lean_ctor_set(x_918, 1, x_914);
return x_918;
}
}
else
{
lean_object* x_919; lean_object* x_920; uint8_t x_921; 
lean_dec(x_8);
x_919 = lean_ctor_get(x_897, 0);
lean_inc(x_919);
x_920 = l_Lean_Elab_postponeExceptionId;
x_921 = lean_nat_dec_eq(x_919, x_920);
lean_dec(x_919);
if (x_921 == 0)
{
lean_object* x_922; 
lean_dec(x_894);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_896)) {
 x_922 = lean_alloc_ctor(1, 2, 0);
} else {
 x_922 = x_896;
 lean_ctor_set_tag(x_922, 1);
}
lean_ctor_set(x_922, 0, x_897);
lean_ctor_set(x_922, 1, x_898);
return x_922;
}
else
{
lean_object* x_923; uint8_t x_924; 
lean_dec(x_896);
x_923 = l_Lean_Elab_Term_SavedState_restore(x_894, x_9, x_10, x_11, x_12, x_13, x_14, x_898);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_924 = !lean_is_exclusive(x_923);
if (x_924 == 0)
{
lean_object* x_925; 
x_925 = lean_ctor_get(x_923, 0);
lean_dec(x_925);
lean_ctor_set_tag(x_923, 1);
lean_ctor_set(x_923, 0, x_897);
return x_923;
}
else
{
lean_object* x_926; lean_object* x_927; 
x_926 = lean_ctor_get(x_923, 1);
lean_inc(x_926);
lean_dec(x_923);
x_927 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_927, 0, x_897);
lean_ctor_set(x_927, 1, x_926);
return x_927;
}
}
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
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; uint8_t x_995; lean_object* x_996; 
x_959 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_960 = lean_ctor_get(x_959, 0);
lean_inc(x_960);
x_961 = lean_ctor_get(x_959, 1);
lean_inc(x_961);
if (lean_is_exclusive(x_959)) {
 lean_ctor_release(x_959, 0);
 lean_ctor_release(x_959, 1);
 x_962 = x_959;
} else {
 lean_dec_ref(x_959);
 x_962 = lean_box(0);
}
x_995 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_996 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_995, x_9, x_10, x_11, x_12, x_13, x_14, x_961);
if (lean_obj_tag(x_996) == 0)
{
lean_object* x_997; lean_object* x_998; lean_object* x_999; uint8_t x_1000; 
lean_dec(x_962);
x_997 = lean_ctor_get(x_996, 0);
lean_inc(x_997);
x_998 = lean_ctor_get(x_996, 1);
lean_inc(x_998);
lean_dec(x_996);
x_999 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_998);
x_1000 = !lean_is_exclusive(x_999);
if (x_1000 == 0)
{
lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; uint8_t x_1004; 
x_1001 = lean_ctor_get(x_999, 0);
x_1002 = lean_ctor_get(x_999, 1);
x_1003 = l_Lean_Elab_Term_SavedState_restore(x_960, x_9, x_10, x_11, x_12, x_13, x_14, x_1002);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1004 = !lean_is_exclusive(x_1003);
if (x_1004 == 0)
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; 
x_1005 = lean_ctor_get(x_1003, 1);
x_1006 = lean_ctor_get(x_1003, 0);
lean_dec(x_1006);
lean_ctor_set(x_1003, 1, x_1001);
lean_ctor_set(x_1003, 0, x_997);
x_1007 = lean_array_push(x_8, x_1003);
lean_ctor_set(x_999, 1, x_1005);
lean_ctor_set(x_999, 0, x_1007);
return x_999;
}
else
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
x_1008 = lean_ctor_get(x_1003, 1);
lean_inc(x_1008);
lean_dec(x_1003);
x_1009 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1009, 0, x_997);
lean_ctor_set(x_1009, 1, x_1001);
x_1010 = lean_array_push(x_8, x_1009);
lean_ctor_set(x_999, 1, x_1008);
lean_ctor_set(x_999, 0, x_1010);
return x_999;
}
}
else
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
x_1011 = lean_ctor_get(x_999, 0);
x_1012 = lean_ctor_get(x_999, 1);
lean_inc(x_1012);
lean_inc(x_1011);
lean_dec(x_999);
x_1013 = l_Lean_Elab_Term_SavedState_restore(x_960, x_9, x_10, x_11, x_12, x_13, x_14, x_1012);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1014 = lean_ctor_get(x_1013, 1);
lean_inc(x_1014);
if (lean_is_exclusive(x_1013)) {
 lean_ctor_release(x_1013, 0);
 lean_ctor_release(x_1013, 1);
 x_1015 = x_1013;
} else {
 lean_dec_ref(x_1013);
 x_1015 = lean_box(0);
}
if (lean_is_scalar(x_1015)) {
 x_1016 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1016 = x_1015;
}
lean_ctor_set(x_1016, 0, x_997);
lean_ctor_set(x_1016, 1, x_1011);
x_1017 = lean_array_push(x_8, x_1016);
x_1018 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1018, 0, x_1017);
lean_ctor_set(x_1018, 1, x_1014);
return x_1018;
}
}
else
{
lean_object* x_1019; lean_object* x_1020; 
x_1019 = lean_ctor_get(x_996, 0);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_996, 1);
lean_inc(x_1020);
lean_dec(x_996);
x_963 = x_1019;
x_964 = x_1020;
goto block_994;
}
block_994:
{
if (lean_obj_tag(x_963) == 0)
{
lean_object* x_965; uint8_t x_966; 
lean_dec(x_962);
x_965 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_964);
x_966 = !lean_is_exclusive(x_965);
if (x_966 == 0)
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; uint8_t x_970; 
x_967 = lean_ctor_get(x_965, 0);
x_968 = lean_ctor_get(x_965, 1);
x_969 = l_Lean_Elab_Term_SavedState_restore(x_960, x_9, x_10, x_11, x_12, x_13, x_14, x_968);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_970 = !lean_is_exclusive(x_969);
if (x_970 == 0)
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; 
x_971 = lean_ctor_get(x_969, 1);
x_972 = lean_ctor_get(x_969, 0);
lean_dec(x_972);
lean_ctor_set_tag(x_969, 1);
lean_ctor_set(x_969, 1, x_967);
lean_ctor_set(x_969, 0, x_963);
x_973 = lean_array_push(x_8, x_969);
lean_ctor_set(x_965, 1, x_971);
lean_ctor_set(x_965, 0, x_973);
return x_965;
}
else
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; 
x_974 = lean_ctor_get(x_969, 1);
lean_inc(x_974);
lean_dec(x_969);
x_975 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_975, 0, x_963);
lean_ctor_set(x_975, 1, x_967);
x_976 = lean_array_push(x_8, x_975);
lean_ctor_set(x_965, 1, x_974);
lean_ctor_set(x_965, 0, x_976);
return x_965;
}
}
else
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; 
x_977 = lean_ctor_get(x_965, 0);
x_978 = lean_ctor_get(x_965, 1);
lean_inc(x_978);
lean_inc(x_977);
lean_dec(x_965);
x_979 = l_Lean_Elab_Term_SavedState_restore(x_960, x_9, x_10, x_11, x_12, x_13, x_14, x_978);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_980 = lean_ctor_get(x_979, 1);
lean_inc(x_980);
if (lean_is_exclusive(x_979)) {
 lean_ctor_release(x_979, 0);
 lean_ctor_release(x_979, 1);
 x_981 = x_979;
} else {
 lean_dec_ref(x_979);
 x_981 = lean_box(0);
}
if (lean_is_scalar(x_981)) {
 x_982 = lean_alloc_ctor(1, 2, 0);
} else {
 x_982 = x_981;
 lean_ctor_set_tag(x_982, 1);
}
lean_ctor_set(x_982, 0, x_963);
lean_ctor_set(x_982, 1, x_977);
x_983 = lean_array_push(x_8, x_982);
x_984 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_984, 0, x_983);
lean_ctor_set(x_984, 1, x_980);
return x_984;
}
}
else
{
lean_object* x_985; lean_object* x_986; uint8_t x_987; 
lean_dec(x_8);
x_985 = lean_ctor_get(x_963, 0);
lean_inc(x_985);
x_986 = l_Lean_Elab_postponeExceptionId;
x_987 = lean_nat_dec_eq(x_985, x_986);
lean_dec(x_985);
if (x_987 == 0)
{
lean_object* x_988; 
lean_dec(x_960);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_962)) {
 x_988 = lean_alloc_ctor(1, 2, 0);
} else {
 x_988 = x_962;
 lean_ctor_set_tag(x_988, 1);
}
lean_ctor_set(x_988, 0, x_963);
lean_ctor_set(x_988, 1, x_964);
return x_988;
}
else
{
lean_object* x_989; uint8_t x_990; 
lean_dec(x_962);
x_989 = l_Lean_Elab_Term_SavedState_restore(x_960, x_9, x_10, x_11, x_12, x_13, x_14, x_964);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_990 = !lean_is_exclusive(x_989);
if (x_990 == 0)
{
lean_object* x_991; 
x_991 = lean_ctor_get(x_989, 0);
lean_dec(x_991);
lean_ctor_set_tag(x_989, 1);
lean_ctor_set(x_989, 0, x_963);
return x_989;
}
else
{
lean_object* x_992; lean_object* x_993; 
x_992 = lean_ctor_get(x_989, 1);
lean_inc(x_992);
lean_dec(x_989);
x_993 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_993, 0, x_963);
lean_ctor_set(x_993, 1, x_992);
return x_993;
}
}
}
}
}
else
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1057; 
x_1021 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1022 = lean_ctor_get(x_1021, 0);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_1021, 1);
lean_inc(x_1023);
if (lean_is_exclusive(x_1021)) {
 lean_ctor_release(x_1021, 0);
 lean_ctor_release(x_1021, 1);
 x_1024 = x_1021;
} else {
 lean_dec_ref(x_1021);
 x_1024 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1057 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_755, x_9, x_10, x_11, x_12, x_13, x_14, x_1023);
if (lean_obj_tag(x_1057) == 0)
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; uint8_t x_1061; 
lean_dec(x_1024);
x_1058 = lean_ctor_get(x_1057, 0);
lean_inc(x_1058);
x_1059 = lean_ctor_get(x_1057, 1);
lean_inc(x_1059);
lean_dec(x_1057);
x_1060 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1059);
x_1061 = !lean_is_exclusive(x_1060);
if (x_1061 == 0)
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; uint8_t x_1065; 
x_1062 = lean_ctor_get(x_1060, 0);
x_1063 = lean_ctor_get(x_1060, 1);
x_1064 = l_Lean_Elab_Term_SavedState_restore(x_1022, x_9, x_10, x_11, x_12, x_13, x_14, x_1063);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1065 = !lean_is_exclusive(x_1064);
if (x_1065 == 0)
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; 
x_1066 = lean_ctor_get(x_1064, 1);
x_1067 = lean_ctor_get(x_1064, 0);
lean_dec(x_1067);
lean_ctor_set(x_1064, 1, x_1062);
lean_ctor_set(x_1064, 0, x_1058);
x_1068 = lean_array_push(x_8, x_1064);
lean_ctor_set(x_1060, 1, x_1066);
lean_ctor_set(x_1060, 0, x_1068);
return x_1060;
}
else
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; 
x_1069 = lean_ctor_get(x_1064, 1);
lean_inc(x_1069);
lean_dec(x_1064);
x_1070 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1070, 0, x_1058);
lean_ctor_set(x_1070, 1, x_1062);
x_1071 = lean_array_push(x_8, x_1070);
lean_ctor_set(x_1060, 1, x_1069);
lean_ctor_set(x_1060, 0, x_1071);
return x_1060;
}
}
else
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
x_1072 = lean_ctor_get(x_1060, 0);
x_1073 = lean_ctor_get(x_1060, 1);
lean_inc(x_1073);
lean_inc(x_1072);
lean_dec(x_1060);
x_1074 = l_Lean_Elab_Term_SavedState_restore(x_1022, x_9, x_10, x_11, x_12, x_13, x_14, x_1073);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1075 = lean_ctor_get(x_1074, 1);
lean_inc(x_1075);
if (lean_is_exclusive(x_1074)) {
 lean_ctor_release(x_1074, 0);
 lean_ctor_release(x_1074, 1);
 x_1076 = x_1074;
} else {
 lean_dec_ref(x_1074);
 x_1076 = lean_box(0);
}
if (lean_is_scalar(x_1076)) {
 x_1077 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1077 = x_1076;
}
lean_ctor_set(x_1077, 0, x_1058);
lean_ctor_set(x_1077, 1, x_1072);
x_1078 = lean_array_push(x_8, x_1077);
x_1079 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1079, 0, x_1078);
lean_ctor_set(x_1079, 1, x_1075);
return x_1079;
}
}
else
{
lean_object* x_1080; lean_object* x_1081; 
x_1080 = lean_ctor_get(x_1057, 0);
lean_inc(x_1080);
x_1081 = lean_ctor_get(x_1057, 1);
lean_inc(x_1081);
lean_dec(x_1057);
x_1025 = x_1080;
x_1026 = x_1081;
goto block_1056;
}
block_1056:
{
if (lean_obj_tag(x_1025) == 0)
{
lean_object* x_1027; uint8_t x_1028; 
lean_dec(x_1024);
x_1027 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1026);
x_1028 = !lean_is_exclusive(x_1027);
if (x_1028 == 0)
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; uint8_t x_1032; 
x_1029 = lean_ctor_get(x_1027, 0);
x_1030 = lean_ctor_get(x_1027, 1);
x_1031 = l_Lean_Elab_Term_SavedState_restore(x_1022, x_9, x_10, x_11, x_12, x_13, x_14, x_1030);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1032 = !lean_is_exclusive(x_1031);
if (x_1032 == 0)
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; 
x_1033 = lean_ctor_get(x_1031, 1);
x_1034 = lean_ctor_get(x_1031, 0);
lean_dec(x_1034);
lean_ctor_set_tag(x_1031, 1);
lean_ctor_set(x_1031, 1, x_1029);
lean_ctor_set(x_1031, 0, x_1025);
x_1035 = lean_array_push(x_8, x_1031);
lean_ctor_set(x_1027, 1, x_1033);
lean_ctor_set(x_1027, 0, x_1035);
return x_1027;
}
else
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1036 = lean_ctor_get(x_1031, 1);
lean_inc(x_1036);
lean_dec(x_1031);
x_1037 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1037, 0, x_1025);
lean_ctor_set(x_1037, 1, x_1029);
x_1038 = lean_array_push(x_8, x_1037);
lean_ctor_set(x_1027, 1, x_1036);
lean_ctor_set(x_1027, 0, x_1038);
return x_1027;
}
}
else
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; 
x_1039 = lean_ctor_get(x_1027, 0);
x_1040 = lean_ctor_get(x_1027, 1);
lean_inc(x_1040);
lean_inc(x_1039);
lean_dec(x_1027);
x_1041 = l_Lean_Elab_Term_SavedState_restore(x_1022, x_9, x_10, x_11, x_12, x_13, x_14, x_1040);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1042 = lean_ctor_get(x_1041, 1);
lean_inc(x_1042);
if (lean_is_exclusive(x_1041)) {
 lean_ctor_release(x_1041, 0);
 lean_ctor_release(x_1041, 1);
 x_1043 = x_1041;
} else {
 lean_dec_ref(x_1041);
 x_1043 = lean_box(0);
}
if (lean_is_scalar(x_1043)) {
 x_1044 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1044 = x_1043;
 lean_ctor_set_tag(x_1044, 1);
}
lean_ctor_set(x_1044, 0, x_1025);
lean_ctor_set(x_1044, 1, x_1039);
x_1045 = lean_array_push(x_8, x_1044);
x_1046 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1046, 0, x_1045);
lean_ctor_set(x_1046, 1, x_1042);
return x_1046;
}
}
else
{
lean_object* x_1047; lean_object* x_1048; uint8_t x_1049; 
lean_dec(x_8);
x_1047 = lean_ctor_get(x_1025, 0);
lean_inc(x_1047);
x_1048 = l_Lean_Elab_postponeExceptionId;
x_1049 = lean_nat_dec_eq(x_1047, x_1048);
lean_dec(x_1047);
if (x_1049 == 0)
{
lean_object* x_1050; 
lean_dec(x_1022);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1024)) {
 x_1050 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1050 = x_1024;
 lean_ctor_set_tag(x_1050, 1);
}
lean_ctor_set(x_1050, 0, x_1025);
lean_ctor_set(x_1050, 1, x_1026);
return x_1050;
}
else
{
lean_object* x_1051; uint8_t x_1052; 
lean_dec(x_1024);
x_1051 = l_Lean_Elab_Term_SavedState_restore(x_1022, x_9, x_10, x_11, x_12, x_13, x_14, x_1026);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1052 = !lean_is_exclusive(x_1051);
if (x_1052 == 0)
{
lean_object* x_1053; 
x_1053 = lean_ctor_get(x_1051, 0);
lean_dec(x_1053);
lean_ctor_set_tag(x_1051, 1);
lean_ctor_set(x_1051, 0, x_1025);
return x_1051;
}
else
{
lean_object* x_1054; lean_object* x_1055; 
x_1054 = lean_ctor_get(x_1051, 1);
lean_inc(x_1054);
lean_dec(x_1051);
x_1055 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1055, 0, x_1025);
lean_ctor_set(x_1055, 1, x_1054);
return x_1055;
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
lean_object* x_1085; lean_object* x_1086; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1085 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__8;
x_1086 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1085, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1086;
}
}
}
block_1471:
{
if (x_1088 == 0)
{
lean_object* x_1089; uint8_t x_1090; 
x_1089 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__10;
lean_inc(x_1);
x_1090 = l_Lean_Syntax_isOfKind(x_1, x_1089);
if (x_1090 == 0)
{
lean_object* x_1091; uint8_t x_1092; 
x_1091 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__12;
lean_inc(x_1);
x_1092 = l_Lean_Syntax_isOfKind(x_1, x_1091);
if (x_1092 == 0)
{
uint8_t x_1093; 
x_1093 = 0;
x_354 = x_1093;
goto block_1087;
}
else
{
lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; uint8_t x_1097; 
x_1094 = l_Lean_Syntax_getArgs(x_1);
x_1095 = lean_array_get_size(x_1094);
lean_dec(x_1094);
x_1096 = lean_unsigned_to_nat(3u);
x_1097 = lean_nat_dec_eq(x_1095, x_1096);
lean_dec(x_1095);
x_354 = x_1097;
goto block_1087;
}
}
else
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; uint8_t x_1101; 
x_1098 = l_Lean_Syntax_getArgs(x_1);
x_1099 = lean_array_get_size(x_1098);
lean_dec(x_1098);
x_1100 = lean_unsigned_to_nat(4u);
x_1101 = lean_nat_dec_eq(x_1099, x_1100);
if (x_1101 == 0)
{
lean_object* x_1102; uint8_t x_1103; 
x_1102 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__12;
lean_inc(x_1);
x_1103 = l_Lean_Syntax_isOfKind(x_1, x_1102);
if (x_1103 == 0)
{
uint8_t x_1104; 
lean_dec(x_1099);
x_1104 = 0;
x_354 = x_1104;
goto block_1087;
}
else
{
lean_object* x_1105; uint8_t x_1106; 
x_1105 = lean_unsigned_to_nat(3u);
x_1106 = lean_nat_dec_eq(x_1099, x_1105);
lean_dec(x_1099);
x_354 = x_1106;
goto block_1087;
}
}
else
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; 
lean_dec(x_1099);
x_1107 = lean_unsigned_to_nat(0u);
x_1108 = l_Lean_Syntax_getArg(x_1, x_1107);
x_1109 = lean_unsigned_to_nat(2u);
x_1110 = l_Lean_Syntax_getArg(x_1, x_1109);
lean_dec(x_1);
x_1111 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1111, 0, x_1110);
x_1112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1112, 0, x_1111);
lean_ctor_set(x_1112, 1, x_2);
x_1 = x_1108;
x_2 = x_1112;
goto _start;
}
}
}
else
{
lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; uint8_t x_1119; 
x_1114 = lean_unsigned_to_nat(0u);
x_1115 = l_Lean_Syntax_getArg(x_1, x_1114);
x_1116 = lean_unsigned_to_nat(2u);
x_1117 = l_Lean_Syntax_getArg(x_1, x_1116);
x_1118 = l_Lean_fieldIdxKind___closed__2;
lean_inc(x_1117);
x_1119 = l_Lean_Syntax_isOfKind(x_1117, x_1118);
if (x_1119 == 0)
{
lean_object* x_1120; uint8_t x_1121; 
x_1120 = l_Lean_identKind___closed__2;
lean_inc(x_1117);
x_1121 = l_Lean_Syntax_isOfKind(x_1117, x_1120);
if (x_1121 == 0)
{
uint8_t x_1122; uint8_t x_1123; 
lean_dec(x_1117);
lean_dec(x_1115);
x_1122 = l_List_isEmpty___rarg(x_2);
if (x_7 == 0)
{
uint8_t x_1451; 
x_1451 = 1;
x_1123 = x_1451;
goto block_1450;
}
else
{
uint8_t x_1452; 
x_1452 = 0;
x_1123 = x_1452;
goto block_1450;
}
block_1450:
{
if (x_1122 == 0)
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1161; 
x_1124 = lean_box(0);
x_1125 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1126 = lean_ctor_get(x_1125, 0);
lean_inc(x_1126);
x_1127 = lean_ctor_get(x_1125, 1);
lean_inc(x_1127);
if (lean_is_exclusive(x_1125)) {
 lean_ctor_release(x_1125, 0);
 lean_ctor_release(x_1125, 1);
 x_1128 = x_1125;
} else {
 lean_dec_ref(x_1125);
 x_1128 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1161 = l_Lean_Elab_Term_elabTerm(x_1, x_1124, x_1123, x_9, x_10, x_11, x_12, x_13, x_14, x_1127);
if (lean_obj_tag(x_1161) == 0)
{
lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
x_1162 = lean_ctor_get(x_1161, 0);
lean_inc(x_1162);
x_1163 = lean_ctor_get(x_1161, 1);
lean_inc(x_1163);
lean_dec(x_1161);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1164 = l___private_Lean_Elab_App_20__elabAppLVals(x_1162, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_1163);
if (lean_obj_tag(x_1164) == 0)
{
lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; uint8_t x_1168; 
lean_dec(x_1128);
x_1165 = lean_ctor_get(x_1164, 0);
lean_inc(x_1165);
x_1166 = lean_ctor_get(x_1164, 1);
lean_inc(x_1166);
lean_dec(x_1164);
x_1167 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1166);
x_1168 = !lean_is_exclusive(x_1167);
if (x_1168 == 0)
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; uint8_t x_1172; 
x_1169 = lean_ctor_get(x_1167, 0);
x_1170 = lean_ctor_get(x_1167, 1);
x_1171 = l_Lean_Elab_Term_SavedState_restore(x_1126, x_9, x_10, x_11, x_12, x_13, x_14, x_1170);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1172 = !lean_is_exclusive(x_1171);
if (x_1172 == 0)
{
lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; 
x_1173 = lean_ctor_get(x_1171, 1);
x_1174 = lean_ctor_get(x_1171, 0);
lean_dec(x_1174);
lean_ctor_set(x_1171, 1, x_1169);
lean_ctor_set(x_1171, 0, x_1165);
x_1175 = lean_array_push(x_8, x_1171);
lean_ctor_set(x_1167, 1, x_1173);
lean_ctor_set(x_1167, 0, x_1175);
return x_1167;
}
else
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
x_1176 = lean_ctor_get(x_1171, 1);
lean_inc(x_1176);
lean_dec(x_1171);
x_1177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1177, 0, x_1165);
lean_ctor_set(x_1177, 1, x_1169);
x_1178 = lean_array_push(x_8, x_1177);
lean_ctor_set(x_1167, 1, x_1176);
lean_ctor_set(x_1167, 0, x_1178);
return x_1167;
}
}
else
{
lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1179 = lean_ctor_get(x_1167, 0);
x_1180 = lean_ctor_get(x_1167, 1);
lean_inc(x_1180);
lean_inc(x_1179);
lean_dec(x_1167);
x_1181 = l_Lean_Elab_Term_SavedState_restore(x_1126, x_9, x_10, x_11, x_12, x_13, x_14, x_1180);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1182 = lean_ctor_get(x_1181, 1);
lean_inc(x_1182);
if (lean_is_exclusive(x_1181)) {
 lean_ctor_release(x_1181, 0);
 lean_ctor_release(x_1181, 1);
 x_1183 = x_1181;
} else {
 lean_dec_ref(x_1181);
 x_1183 = lean_box(0);
}
if (lean_is_scalar(x_1183)) {
 x_1184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1184 = x_1183;
}
lean_ctor_set(x_1184, 0, x_1165);
lean_ctor_set(x_1184, 1, x_1179);
x_1185 = lean_array_push(x_8, x_1184);
x_1186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1186, 0, x_1185);
lean_ctor_set(x_1186, 1, x_1182);
return x_1186;
}
}
else
{
lean_object* x_1187; lean_object* x_1188; 
x_1187 = lean_ctor_get(x_1164, 0);
lean_inc(x_1187);
x_1188 = lean_ctor_get(x_1164, 1);
lean_inc(x_1188);
lean_dec(x_1164);
x_1129 = x_1187;
x_1130 = x_1188;
goto block_1160;
}
}
else
{
lean_object* x_1189; lean_object* x_1190; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1189 = lean_ctor_get(x_1161, 0);
lean_inc(x_1189);
x_1190 = lean_ctor_get(x_1161, 1);
lean_inc(x_1190);
lean_dec(x_1161);
x_1129 = x_1189;
x_1130 = x_1190;
goto block_1160;
}
block_1160:
{
if (lean_obj_tag(x_1129) == 0)
{
lean_object* x_1131; uint8_t x_1132; 
lean_dec(x_1128);
x_1131 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1130);
x_1132 = !lean_is_exclusive(x_1131);
if (x_1132 == 0)
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; uint8_t x_1136; 
x_1133 = lean_ctor_get(x_1131, 0);
x_1134 = lean_ctor_get(x_1131, 1);
x_1135 = l_Lean_Elab_Term_SavedState_restore(x_1126, x_9, x_10, x_11, x_12, x_13, x_14, x_1134);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1136 = !lean_is_exclusive(x_1135);
if (x_1136 == 0)
{
lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; 
x_1137 = lean_ctor_get(x_1135, 1);
x_1138 = lean_ctor_get(x_1135, 0);
lean_dec(x_1138);
lean_ctor_set_tag(x_1135, 1);
lean_ctor_set(x_1135, 1, x_1133);
lean_ctor_set(x_1135, 0, x_1129);
x_1139 = lean_array_push(x_8, x_1135);
lean_ctor_set(x_1131, 1, x_1137);
lean_ctor_set(x_1131, 0, x_1139);
return x_1131;
}
else
{
lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; 
x_1140 = lean_ctor_get(x_1135, 1);
lean_inc(x_1140);
lean_dec(x_1135);
x_1141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1141, 0, x_1129);
lean_ctor_set(x_1141, 1, x_1133);
x_1142 = lean_array_push(x_8, x_1141);
lean_ctor_set(x_1131, 1, x_1140);
lean_ctor_set(x_1131, 0, x_1142);
return x_1131;
}
}
else
{
lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
x_1143 = lean_ctor_get(x_1131, 0);
x_1144 = lean_ctor_get(x_1131, 1);
lean_inc(x_1144);
lean_inc(x_1143);
lean_dec(x_1131);
x_1145 = l_Lean_Elab_Term_SavedState_restore(x_1126, x_9, x_10, x_11, x_12, x_13, x_14, x_1144);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1146 = lean_ctor_get(x_1145, 1);
lean_inc(x_1146);
if (lean_is_exclusive(x_1145)) {
 lean_ctor_release(x_1145, 0);
 lean_ctor_release(x_1145, 1);
 x_1147 = x_1145;
} else {
 lean_dec_ref(x_1145);
 x_1147 = lean_box(0);
}
if (lean_is_scalar(x_1147)) {
 x_1148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1148 = x_1147;
 lean_ctor_set_tag(x_1148, 1);
}
lean_ctor_set(x_1148, 0, x_1129);
lean_ctor_set(x_1148, 1, x_1143);
x_1149 = lean_array_push(x_8, x_1148);
x_1150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1150, 0, x_1149);
lean_ctor_set(x_1150, 1, x_1146);
return x_1150;
}
}
else
{
lean_object* x_1151; lean_object* x_1152; uint8_t x_1153; 
lean_dec(x_8);
x_1151 = lean_ctor_get(x_1129, 0);
lean_inc(x_1151);
x_1152 = l_Lean_Elab_postponeExceptionId;
x_1153 = lean_nat_dec_eq(x_1151, x_1152);
lean_dec(x_1151);
if (x_1153 == 0)
{
lean_object* x_1154; 
lean_dec(x_1126);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1128)) {
 x_1154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1154 = x_1128;
 lean_ctor_set_tag(x_1154, 1);
}
lean_ctor_set(x_1154, 0, x_1129);
lean_ctor_set(x_1154, 1, x_1130);
return x_1154;
}
else
{
lean_object* x_1155; uint8_t x_1156; 
lean_dec(x_1128);
x_1155 = l_Lean_Elab_Term_SavedState_restore(x_1126, x_9, x_10, x_11, x_12, x_13, x_14, x_1130);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1156 = !lean_is_exclusive(x_1155);
if (x_1156 == 0)
{
lean_object* x_1157; 
x_1157 = lean_ctor_get(x_1155, 0);
lean_dec(x_1157);
lean_ctor_set_tag(x_1155, 1);
lean_ctor_set(x_1155, 0, x_1129);
return x_1155;
}
else
{
lean_object* x_1158; lean_object* x_1159; 
x_1158 = lean_ctor_get(x_1155, 1);
lean_inc(x_1158);
lean_dec(x_1155);
x_1159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1159, 0, x_1129);
lean_ctor_set(x_1159, 1, x_1158);
return x_1159;
}
}
}
}
}
else
{
uint8_t x_1191; 
x_1191 = l_Array_isEmpty___rarg(x_3);
if (x_1191 == 0)
{
lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1229; 
x_1192 = lean_box(0);
x_1193 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1194 = lean_ctor_get(x_1193, 0);
lean_inc(x_1194);
x_1195 = lean_ctor_get(x_1193, 1);
lean_inc(x_1195);
if (lean_is_exclusive(x_1193)) {
 lean_ctor_release(x_1193, 0);
 lean_ctor_release(x_1193, 1);
 x_1196 = x_1193;
} else {
 lean_dec_ref(x_1193);
 x_1196 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1229 = l_Lean_Elab_Term_elabTerm(x_1, x_1192, x_1123, x_9, x_10, x_11, x_12, x_13, x_14, x_1195);
if (lean_obj_tag(x_1229) == 0)
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; 
x_1230 = lean_ctor_get(x_1229, 0);
lean_inc(x_1230);
x_1231 = lean_ctor_get(x_1229, 1);
lean_inc(x_1231);
lean_dec(x_1229);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1232 = l___private_Lean_Elab_App_20__elabAppLVals(x_1230, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_1231);
if (lean_obj_tag(x_1232) == 0)
{
lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; uint8_t x_1236; 
lean_dec(x_1196);
x_1233 = lean_ctor_get(x_1232, 0);
lean_inc(x_1233);
x_1234 = lean_ctor_get(x_1232, 1);
lean_inc(x_1234);
lean_dec(x_1232);
x_1235 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1234);
x_1236 = !lean_is_exclusive(x_1235);
if (x_1236 == 0)
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; uint8_t x_1240; 
x_1237 = lean_ctor_get(x_1235, 0);
x_1238 = lean_ctor_get(x_1235, 1);
x_1239 = l_Lean_Elab_Term_SavedState_restore(x_1194, x_9, x_10, x_11, x_12, x_13, x_14, x_1238);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1240 = !lean_is_exclusive(x_1239);
if (x_1240 == 0)
{
lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; 
x_1241 = lean_ctor_get(x_1239, 1);
x_1242 = lean_ctor_get(x_1239, 0);
lean_dec(x_1242);
lean_ctor_set(x_1239, 1, x_1237);
lean_ctor_set(x_1239, 0, x_1233);
x_1243 = lean_array_push(x_8, x_1239);
lean_ctor_set(x_1235, 1, x_1241);
lean_ctor_set(x_1235, 0, x_1243);
return x_1235;
}
else
{
lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; 
x_1244 = lean_ctor_get(x_1239, 1);
lean_inc(x_1244);
lean_dec(x_1239);
x_1245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1245, 0, x_1233);
lean_ctor_set(x_1245, 1, x_1237);
x_1246 = lean_array_push(x_8, x_1245);
lean_ctor_set(x_1235, 1, x_1244);
lean_ctor_set(x_1235, 0, x_1246);
return x_1235;
}
}
else
{
lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; 
x_1247 = lean_ctor_get(x_1235, 0);
x_1248 = lean_ctor_get(x_1235, 1);
lean_inc(x_1248);
lean_inc(x_1247);
lean_dec(x_1235);
x_1249 = l_Lean_Elab_Term_SavedState_restore(x_1194, x_9, x_10, x_11, x_12, x_13, x_14, x_1248);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1250 = lean_ctor_get(x_1249, 1);
lean_inc(x_1250);
if (lean_is_exclusive(x_1249)) {
 lean_ctor_release(x_1249, 0);
 lean_ctor_release(x_1249, 1);
 x_1251 = x_1249;
} else {
 lean_dec_ref(x_1249);
 x_1251 = lean_box(0);
}
if (lean_is_scalar(x_1251)) {
 x_1252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1252 = x_1251;
}
lean_ctor_set(x_1252, 0, x_1233);
lean_ctor_set(x_1252, 1, x_1247);
x_1253 = lean_array_push(x_8, x_1252);
x_1254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1254, 0, x_1253);
lean_ctor_set(x_1254, 1, x_1250);
return x_1254;
}
}
else
{
lean_object* x_1255; lean_object* x_1256; 
x_1255 = lean_ctor_get(x_1232, 0);
lean_inc(x_1255);
x_1256 = lean_ctor_get(x_1232, 1);
lean_inc(x_1256);
lean_dec(x_1232);
x_1197 = x_1255;
x_1198 = x_1256;
goto block_1228;
}
}
else
{
lean_object* x_1257; lean_object* x_1258; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1257 = lean_ctor_get(x_1229, 0);
lean_inc(x_1257);
x_1258 = lean_ctor_get(x_1229, 1);
lean_inc(x_1258);
lean_dec(x_1229);
x_1197 = x_1257;
x_1198 = x_1258;
goto block_1228;
}
block_1228:
{
if (lean_obj_tag(x_1197) == 0)
{
lean_object* x_1199; uint8_t x_1200; 
lean_dec(x_1196);
x_1199 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1198);
x_1200 = !lean_is_exclusive(x_1199);
if (x_1200 == 0)
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; uint8_t x_1204; 
x_1201 = lean_ctor_get(x_1199, 0);
x_1202 = lean_ctor_get(x_1199, 1);
x_1203 = l_Lean_Elab_Term_SavedState_restore(x_1194, x_9, x_10, x_11, x_12, x_13, x_14, x_1202);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1204 = !lean_is_exclusive(x_1203);
if (x_1204 == 0)
{
lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; 
x_1205 = lean_ctor_get(x_1203, 1);
x_1206 = lean_ctor_get(x_1203, 0);
lean_dec(x_1206);
lean_ctor_set_tag(x_1203, 1);
lean_ctor_set(x_1203, 1, x_1201);
lean_ctor_set(x_1203, 0, x_1197);
x_1207 = lean_array_push(x_8, x_1203);
lean_ctor_set(x_1199, 1, x_1205);
lean_ctor_set(x_1199, 0, x_1207);
return x_1199;
}
else
{
lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; 
x_1208 = lean_ctor_get(x_1203, 1);
lean_inc(x_1208);
lean_dec(x_1203);
x_1209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1209, 0, x_1197);
lean_ctor_set(x_1209, 1, x_1201);
x_1210 = lean_array_push(x_8, x_1209);
lean_ctor_set(x_1199, 1, x_1208);
lean_ctor_set(x_1199, 0, x_1210);
return x_1199;
}
}
else
{
lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; 
x_1211 = lean_ctor_get(x_1199, 0);
x_1212 = lean_ctor_get(x_1199, 1);
lean_inc(x_1212);
lean_inc(x_1211);
lean_dec(x_1199);
x_1213 = l_Lean_Elab_Term_SavedState_restore(x_1194, x_9, x_10, x_11, x_12, x_13, x_14, x_1212);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1214 = lean_ctor_get(x_1213, 1);
lean_inc(x_1214);
if (lean_is_exclusive(x_1213)) {
 lean_ctor_release(x_1213, 0);
 lean_ctor_release(x_1213, 1);
 x_1215 = x_1213;
} else {
 lean_dec_ref(x_1213);
 x_1215 = lean_box(0);
}
if (lean_is_scalar(x_1215)) {
 x_1216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1216 = x_1215;
 lean_ctor_set_tag(x_1216, 1);
}
lean_ctor_set(x_1216, 0, x_1197);
lean_ctor_set(x_1216, 1, x_1211);
x_1217 = lean_array_push(x_8, x_1216);
x_1218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1218, 0, x_1217);
lean_ctor_set(x_1218, 1, x_1214);
return x_1218;
}
}
else
{
lean_object* x_1219; lean_object* x_1220; uint8_t x_1221; 
lean_dec(x_8);
x_1219 = lean_ctor_get(x_1197, 0);
lean_inc(x_1219);
x_1220 = l_Lean_Elab_postponeExceptionId;
x_1221 = lean_nat_dec_eq(x_1219, x_1220);
lean_dec(x_1219);
if (x_1221 == 0)
{
lean_object* x_1222; 
lean_dec(x_1194);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1196)) {
 x_1222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1222 = x_1196;
 lean_ctor_set_tag(x_1222, 1);
}
lean_ctor_set(x_1222, 0, x_1197);
lean_ctor_set(x_1222, 1, x_1198);
return x_1222;
}
else
{
lean_object* x_1223; uint8_t x_1224; 
lean_dec(x_1196);
x_1223 = l_Lean_Elab_Term_SavedState_restore(x_1194, x_9, x_10, x_11, x_12, x_13, x_14, x_1198);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1224 = !lean_is_exclusive(x_1223);
if (x_1224 == 0)
{
lean_object* x_1225; 
x_1225 = lean_ctor_get(x_1223, 0);
lean_dec(x_1225);
lean_ctor_set_tag(x_1223, 1);
lean_ctor_set(x_1223, 0, x_1197);
return x_1223;
}
else
{
lean_object* x_1226; lean_object* x_1227; 
x_1226 = lean_ctor_get(x_1223, 1);
lean_inc(x_1226);
lean_dec(x_1223);
x_1227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1227, 0, x_1197);
lean_ctor_set(x_1227, 1, x_1226);
return x_1227;
}
}
}
}
}
else
{
uint8_t x_1259; 
x_1259 = l_Array_isEmpty___rarg(x_4);
if (x_1259 == 0)
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1297; 
x_1260 = lean_box(0);
x_1261 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1262 = lean_ctor_get(x_1261, 0);
lean_inc(x_1262);
x_1263 = lean_ctor_get(x_1261, 1);
lean_inc(x_1263);
if (lean_is_exclusive(x_1261)) {
 lean_ctor_release(x_1261, 0);
 lean_ctor_release(x_1261, 1);
 x_1264 = x_1261;
} else {
 lean_dec_ref(x_1261);
 x_1264 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1297 = l_Lean_Elab_Term_elabTerm(x_1, x_1260, x_1123, x_9, x_10, x_11, x_12, x_13, x_14, x_1263);
if (lean_obj_tag(x_1297) == 0)
{
lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; 
x_1298 = lean_ctor_get(x_1297, 0);
lean_inc(x_1298);
x_1299 = lean_ctor_get(x_1297, 1);
lean_inc(x_1299);
lean_dec(x_1297);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1300 = l___private_Lean_Elab_App_20__elabAppLVals(x_1298, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_1299);
if (lean_obj_tag(x_1300) == 0)
{
lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; uint8_t x_1304; 
lean_dec(x_1264);
x_1301 = lean_ctor_get(x_1300, 0);
lean_inc(x_1301);
x_1302 = lean_ctor_get(x_1300, 1);
lean_inc(x_1302);
lean_dec(x_1300);
x_1303 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1302);
x_1304 = !lean_is_exclusive(x_1303);
if (x_1304 == 0)
{
lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; uint8_t x_1308; 
x_1305 = lean_ctor_get(x_1303, 0);
x_1306 = lean_ctor_get(x_1303, 1);
x_1307 = l_Lean_Elab_Term_SavedState_restore(x_1262, x_9, x_10, x_11, x_12, x_13, x_14, x_1306);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1308 = !lean_is_exclusive(x_1307);
if (x_1308 == 0)
{
lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; 
x_1309 = lean_ctor_get(x_1307, 1);
x_1310 = lean_ctor_get(x_1307, 0);
lean_dec(x_1310);
lean_ctor_set(x_1307, 1, x_1305);
lean_ctor_set(x_1307, 0, x_1301);
x_1311 = lean_array_push(x_8, x_1307);
lean_ctor_set(x_1303, 1, x_1309);
lean_ctor_set(x_1303, 0, x_1311);
return x_1303;
}
else
{
lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; 
x_1312 = lean_ctor_get(x_1307, 1);
lean_inc(x_1312);
lean_dec(x_1307);
x_1313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1313, 0, x_1301);
lean_ctor_set(x_1313, 1, x_1305);
x_1314 = lean_array_push(x_8, x_1313);
lean_ctor_set(x_1303, 1, x_1312);
lean_ctor_set(x_1303, 0, x_1314);
return x_1303;
}
}
else
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; 
x_1315 = lean_ctor_get(x_1303, 0);
x_1316 = lean_ctor_get(x_1303, 1);
lean_inc(x_1316);
lean_inc(x_1315);
lean_dec(x_1303);
x_1317 = l_Lean_Elab_Term_SavedState_restore(x_1262, x_9, x_10, x_11, x_12, x_13, x_14, x_1316);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1318 = lean_ctor_get(x_1317, 1);
lean_inc(x_1318);
if (lean_is_exclusive(x_1317)) {
 lean_ctor_release(x_1317, 0);
 lean_ctor_release(x_1317, 1);
 x_1319 = x_1317;
} else {
 lean_dec_ref(x_1317);
 x_1319 = lean_box(0);
}
if (lean_is_scalar(x_1319)) {
 x_1320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1320 = x_1319;
}
lean_ctor_set(x_1320, 0, x_1301);
lean_ctor_set(x_1320, 1, x_1315);
x_1321 = lean_array_push(x_8, x_1320);
x_1322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1322, 0, x_1321);
lean_ctor_set(x_1322, 1, x_1318);
return x_1322;
}
}
else
{
lean_object* x_1323; lean_object* x_1324; 
x_1323 = lean_ctor_get(x_1300, 0);
lean_inc(x_1323);
x_1324 = lean_ctor_get(x_1300, 1);
lean_inc(x_1324);
lean_dec(x_1300);
x_1265 = x_1323;
x_1266 = x_1324;
goto block_1296;
}
}
else
{
lean_object* x_1325; lean_object* x_1326; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1325 = lean_ctor_get(x_1297, 0);
lean_inc(x_1325);
x_1326 = lean_ctor_get(x_1297, 1);
lean_inc(x_1326);
lean_dec(x_1297);
x_1265 = x_1325;
x_1266 = x_1326;
goto block_1296;
}
block_1296:
{
if (lean_obj_tag(x_1265) == 0)
{
lean_object* x_1267; uint8_t x_1268; 
lean_dec(x_1264);
x_1267 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1266);
x_1268 = !lean_is_exclusive(x_1267);
if (x_1268 == 0)
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; uint8_t x_1272; 
x_1269 = lean_ctor_get(x_1267, 0);
x_1270 = lean_ctor_get(x_1267, 1);
x_1271 = l_Lean_Elab_Term_SavedState_restore(x_1262, x_9, x_10, x_11, x_12, x_13, x_14, x_1270);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1272 = !lean_is_exclusive(x_1271);
if (x_1272 == 0)
{
lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; 
x_1273 = lean_ctor_get(x_1271, 1);
x_1274 = lean_ctor_get(x_1271, 0);
lean_dec(x_1274);
lean_ctor_set_tag(x_1271, 1);
lean_ctor_set(x_1271, 1, x_1269);
lean_ctor_set(x_1271, 0, x_1265);
x_1275 = lean_array_push(x_8, x_1271);
lean_ctor_set(x_1267, 1, x_1273);
lean_ctor_set(x_1267, 0, x_1275);
return x_1267;
}
else
{
lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; 
x_1276 = lean_ctor_get(x_1271, 1);
lean_inc(x_1276);
lean_dec(x_1271);
x_1277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1277, 0, x_1265);
lean_ctor_set(x_1277, 1, x_1269);
x_1278 = lean_array_push(x_8, x_1277);
lean_ctor_set(x_1267, 1, x_1276);
lean_ctor_set(x_1267, 0, x_1278);
return x_1267;
}
}
else
{
lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; 
x_1279 = lean_ctor_get(x_1267, 0);
x_1280 = lean_ctor_get(x_1267, 1);
lean_inc(x_1280);
lean_inc(x_1279);
lean_dec(x_1267);
x_1281 = l_Lean_Elab_Term_SavedState_restore(x_1262, x_9, x_10, x_11, x_12, x_13, x_14, x_1280);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1282 = lean_ctor_get(x_1281, 1);
lean_inc(x_1282);
if (lean_is_exclusive(x_1281)) {
 lean_ctor_release(x_1281, 0);
 lean_ctor_release(x_1281, 1);
 x_1283 = x_1281;
} else {
 lean_dec_ref(x_1281);
 x_1283 = lean_box(0);
}
if (lean_is_scalar(x_1283)) {
 x_1284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1284 = x_1283;
 lean_ctor_set_tag(x_1284, 1);
}
lean_ctor_set(x_1284, 0, x_1265);
lean_ctor_set(x_1284, 1, x_1279);
x_1285 = lean_array_push(x_8, x_1284);
x_1286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1286, 0, x_1285);
lean_ctor_set(x_1286, 1, x_1282);
return x_1286;
}
}
else
{
lean_object* x_1287; lean_object* x_1288; uint8_t x_1289; 
lean_dec(x_8);
x_1287 = lean_ctor_get(x_1265, 0);
lean_inc(x_1287);
x_1288 = l_Lean_Elab_postponeExceptionId;
x_1289 = lean_nat_dec_eq(x_1287, x_1288);
lean_dec(x_1287);
if (x_1289 == 0)
{
lean_object* x_1290; 
lean_dec(x_1262);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1264)) {
 x_1290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1290 = x_1264;
 lean_ctor_set_tag(x_1290, 1);
}
lean_ctor_set(x_1290, 0, x_1265);
lean_ctor_set(x_1290, 1, x_1266);
return x_1290;
}
else
{
lean_object* x_1291; uint8_t x_1292; 
lean_dec(x_1264);
x_1291 = l_Lean_Elab_Term_SavedState_restore(x_1262, x_9, x_10, x_11, x_12, x_13, x_14, x_1266);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1292 = !lean_is_exclusive(x_1291);
if (x_1292 == 0)
{
lean_object* x_1293; 
x_1293 = lean_ctor_get(x_1291, 0);
lean_dec(x_1293);
lean_ctor_set_tag(x_1291, 1);
lean_ctor_set(x_1291, 0, x_1265);
return x_1291;
}
else
{
lean_object* x_1294; lean_object* x_1295; 
x_1294 = lean_ctor_get(x_1291, 1);
lean_inc(x_1294);
lean_dec(x_1291);
x_1295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1295, 0, x_1265);
lean_ctor_set(x_1295, 1, x_1294);
return x_1295;
}
}
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
lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; uint8_t x_1363; lean_object* x_1364; 
x_1327 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1328 = lean_ctor_get(x_1327, 0);
lean_inc(x_1328);
x_1329 = lean_ctor_get(x_1327, 1);
lean_inc(x_1329);
if (lean_is_exclusive(x_1327)) {
 lean_ctor_release(x_1327, 0);
 lean_ctor_release(x_1327, 1);
 x_1330 = x_1327;
} else {
 lean_dec_ref(x_1327);
 x_1330 = lean_box(0);
}
x_1363 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1364 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_1363, x_9, x_10, x_11, x_12, x_13, x_14, x_1329);
if (lean_obj_tag(x_1364) == 0)
{
lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; uint8_t x_1368; 
lean_dec(x_1330);
x_1365 = lean_ctor_get(x_1364, 0);
lean_inc(x_1365);
x_1366 = lean_ctor_get(x_1364, 1);
lean_inc(x_1366);
lean_dec(x_1364);
x_1367 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1366);
x_1368 = !lean_is_exclusive(x_1367);
if (x_1368 == 0)
{
lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; uint8_t x_1372; 
x_1369 = lean_ctor_get(x_1367, 0);
x_1370 = lean_ctor_get(x_1367, 1);
x_1371 = l_Lean_Elab_Term_SavedState_restore(x_1328, x_9, x_10, x_11, x_12, x_13, x_14, x_1370);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1372 = !lean_is_exclusive(x_1371);
if (x_1372 == 0)
{
lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; 
x_1373 = lean_ctor_get(x_1371, 1);
x_1374 = lean_ctor_get(x_1371, 0);
lean_dec(x_1374);
lean_ctor_set(x_1371, 1, x_1369);
lean_ctor_set(x_1371, 0, x_1365);
x_1375 = lean_array_push(x_8, x_1371);
lean_ctor_set(x_1367, 1, x_1373);
lean_ctor_set(x_1367, 0, x_1375);
return x_1367;
}
else
{
lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; 
x_1376 = lean_ctor_get(x_1371, 1);
lean_inc(x_1376);
lean_dec(x_1371);
x_1377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1377, 0, x_1365);
lean_ctor_set(x_1377, 1, x_1369);
x_1378 = lean_array_push(x_8, x_1377);
lean_ctor_set(x_1367, 1, x_1376);
lean_ctor_set(x_1367, 0, x_1378);
return x_1367;
}
}
else
{
lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; 
x_1379 = lean_ctor_get(x_1367, 0);
x_1380 = lean_ctor_get(x_1367, 1);
lean_inc(x_1380);
lean_inc(x_1379);
lean_dec(x_1367);
x_1381 = l_Lean_Elab_Term_SavedState_restore(x_1328, x_9, x_10, x_11, x_12, x_13, x_14, x_1380);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1382 = lean_ctor_get(x_1381, 1);
lean_inc(x_1382);
if (lean_is_exclusive(x_1381)) {
 lean_ctor_release(x_1381, 0);
 lean_ctor_release(x_1381, 1);
 x_1383 = x_1381;
} else {
 lean_dec_ref(x_1381);
 x_1383 = lean_box(0);
}
if (lean_is_scalar(x_1383)) {
 x_1384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1384 = x_1383;
}
lean_ctor_set(x_1384, 0, x_1365);
lean_ctor_set(x_1384, 1, x_1379);
x_1385 = lean_array_push(x_8, x_1384);
x_1386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1386, 0, x_1385);
lean_ctor_set(x_1386, 1, x_1382);
return x_1386;
}
}
else
{
lean_object* x_1387; lean_object* x_1388; 
x_1387 = lean_ctor_get(x_1364, 0);
lean_inc(x_1387);
x_1388 = lean_ctor_get(x_1364, 1);
lean_inc(x_1388);
lean_dec(x_1364);
x_1331 = x_1387;
x_1332 = x_1388;
goto block_1362;
}
block_1362:
{
if (lean_obj_tag(x_1331) == 0)
{
lean_object* x_1333; uint8_t x_1334; 
lean_dec(x_1330);
x_1333 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1332);
x_1334 = !lean_is_exclusive(x_1333);
if (x_1334 == 0)
{
lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; uint8_t x_1338; 
x_1335 = lean_ctor_get(x_1333, 0);
x_1336 = lean_ctor_get(x_1333, 1);
x_1337 = l_Lean_Elab_Term_SavedState_restore(x_1328, x_9, x_10, x_11, x_12, x_13, x_14, x_1336);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1338 = !lean_is_exclusive(x_1337);
if (x_1338 == 0)
{
lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; 
x_1339 = lean_ctor_get(x_1337, 1);
x_1340 = lean_ctor_get(x_1337, 0);
lean_dec(x_1340);
lean_ctor_set_tag(x_1337, 1);
lean_ctor_set(x_1337, 1, x_1335);
lean_ctor_set(x_1337, 0, x_1331);
x_1341 = lean_array_push(x_8, x_1337);
lean_ctor_set(x_1333, 1, x_1339);
lean_ctor_set(x_1333, 0, x_1341);
return x_1333;
}
else
{
lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; 
x_1342 = lean_ctor_get(x_1337, 1);
lean_inc(x_1342);
lean_dec(x_1337);
x_1343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1343, 0, x_1331);
lean_ctor_set(x_1343, 1, x_1335);
x_1344 = lean_array_push(x_8, x_1343);
lean_ctor_set(x_1333, 1, x_1342);
lean_ctor_set(x_1333, 0, x_1344);
return x_1333;
}
}
else
{
lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; 
x_1345 = lean_ctor_get(x_1333, 0);
x_1346 = lean_ctor_get(x_1333, 1);
lean_inc(x_1346);
lean_inc(x_1345);
lean_dec(x_1333);
x_1347 = l_Lean_Elab_Term_SavedState_restore(x_1328, x_9, x_10, x_11, x_12, x_13, x_14, x_1346);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1348 = lean_ctor_get(x_1347, 1);
lean_inc(x_1348);
if (lean_is_exclusive(x_1347)) {
 lean_ctor_release(x_1347, 0);
 lean_ctor_release(x_1347, 1);
 x_1349 = x_1347;
} else {
 lean_dec_ref(x_1347);
 x_1349 = lean_box(0);
}
if (lean_is_scalar(x_1349)) {
 x_1350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1350 = x_1349;
 lean_ctor_set_tag(x_1350, 1);
}
lean_ctor_set(x_1350, 0, x_1331);
lean_ctor_set(x_1350, 1, x_1345);
x_1351 = lean_array_push(x_8, x_1350);
x_1352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1352, 0, x_1351);
lean_ctor_set(x_1352, 1, x_1348);
return x_1352;
}
}
else
{
lean_object* x_1353; lean_object* x_1354; uint8_t x_1355; 
lean_dec(x_8);
x_1353 = lean_ctor_get(x_1331, 0);
lean_inc(x_1353);
x_1354 = l_Lean_Elab_postponeExceptionId;
x_1355 = lean_nat_dec_eq(x_1353, x_1354);
lean_dec(x_1353);
if (x_1355 == 0)
{
lean_object* x_1356; 
lean_dec(x_1328);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1330)) {
 x_1356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1356 = x_1330;
 lean_ctor_set_tag(x_1356, 1);
}
lean_ctor_set(x_1356, 0, x_1331);
lean_ctor_set(x_1356, 1, x_1332);
return x_1356;
}
else
{
lean_object* x_1357; uint8_t x_1358; 
lean_dec(x_1330);
x_1357 = l_Lean_Elab_Term_SavedState_restore(x_1328, x_9, x_10, x_11, x_12, x_13, x_14, x_1332);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1358 = !lean_is_exclusive(x_1357);
if (x_1358 == 0)
{
lean_object* x_1359; 
x_1359 = lean_ctor_get(x_1357, 0);
lean_dec(x_1359);
lean_ctor_set_tag(x_1357, 1);
lean_ctor_set(x_1357, 0, x_1331);
return x_1357;
}
else
{
lean_object* x_1360; lean_object* x_1361; 
x_1360 = lean_ctor_get(x_1357, 1);
lean_inc(x_1360);
lean_dec(x_1357);
x_1361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1361, 0, x_1331);
lean_ctor_set(x_1361, 1, x_1360);
return x_1361;
}
}
}
}
}
else
{
lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1425; 
x_1389 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1390 = lean_ctor_get(x_1389, 0);
lean_inc(x_1390);
x_1391 = lean_ctor_get(x_1389, 1);
lean_inc(x_1391);
if (lean_is_exclusive(x_1389)) {
 lean_ctor_release(x_1389, 0);
 lean_ctor_release(x_1389, 1);
 x_1392 = x_1389;
} else {
 lean_dec_ref(x_1389);
 x_1392 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1425 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_1123, x_9, x_10, x_11, x_12, x_13, x_14, x_1391);
if (lean_obj_tag(x_1425) == 0)
{
lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; uint8_t x_1429; 
lean_dec(x_1392);
x_1426 = lean_ctor_get(x_1425, 0);
lean_inc(x_1426);
x_1427 = lean_ctor_get(x_1425, 1);
lean_inc(x_1427);
lean_dec(x_1425);
x_1428 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1427);
x_1429 = !lean_is_exclusive(x_1428);
if (x_1429 == 0)
{
lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; uint8_t x_1433; 
x_1430 = lean_ctor_get(x_1428, 0);
x_1431 = lean_ctor_get(x_1428, 1);
x_1432 = l_Lean_Elab_Term_SavedState_restore(x_1390, x_9, x_10, x_11, x_12, x_13, x_14, x_1431);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1433 = !lean_is_exclusive(x_1432);
if (x_1433 == 0)
{
lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; 
x_1434 = lean_ctor_get(x_1432, 1);
x_1435 = lean_ctor_get(x_1432, 0);
lean_dec(x_1435);
lean_ctor_set(x_1432, 1, x_1430);
lean_ctor_set(x_1432, 0, x_1426);
x_1436 = lean_array_push(x_8, x_1432);
lean_ctor_set(x_1428, 1, x_1434);
lean_ctor_set(x_1428, 0, x_1436);
return x_1428;
}
else
{
lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; 
x_1437 = lean_ctor_get(x_1432, 1);
lean_inc(x_1437);
lean_dec(x_1432);
x_1438 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1438, 0, x_1426);
lean_ctor_set(x_1438, 1, x_1430);
x_1439 = lean_array_push(x_8, x_1438);
lean_ctor_set(x_1428, 1, x_1437);
lean_ctor_set(x_1428, 0, x_1439);
return x_1428;
}
}
else
{
lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; 
x_1440 = lean_ctor_get(x_1428, 0);
x_1441 = lean_ctor_get(x_1428, 1);
lean_inc(x_1441);
lean_inc(x_1440);
lean_dec(x_1428);
x_1442 = l_Lean_Elab_Term_SavedState_restore(x_1390, x_9, x_10, x_11, x_12, x_13, x_14, x_1441);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1443 = lean_ctor_get(x_1442, 1);
lean_inc(x_1443);
if (lean_is_exclusive(x_1442)) {
 lean_ctor_release(x_1442, 0);
 lean_ctor_release(x_1442, 1);
 x_1444 = x_1442;
} else {
 lean_dec_ref(x_1442);
 x_1444 = lean_box(0);
}
if (lean_is_scalar(x_1444)) {
 x_1445 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1445 = x_1444;
}
lean_ctor_set(x_1445, 0, x_1426);
lean_ctor_set(x_1445, 1, x_1440);
x_1446 = lean_array_push(x_8, x_1445);
x_1447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1447, 0, x_1446);
lean_ctor_set(x_1447, 1, x_1443);
return x_1447;
}
}
else
{
lean_object* x_1448; lean_object* x_1449; 
x_1448 = lean_ctor_get(x_1425, 0);
lean_inc(x_1448);
x_1449 = lean_ctor_get(x_1425, 1);
lean_inc(x_1449);
lean_dec(x_1425);
x_1393 = x_1448;
x_1394 = x_1449;
goto block_1424;
}
block_1424:
{
if (lean_obj_tag(x_1393) == 0)
{
lean_object* x_1395; uint8_t x_1396; 
lean_dec(x_1392);
x_1395 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1394);
x_1396 = !lean_is_exclusive(x_1395);
if (x_1396 == 0)
{
lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; uint8_t x_1400; 
x_1397 = lean_ctor_get(x_1395, 0);
x_1398 = lean_ctor_get(x_1395, 1);
x_1399 = l_Lean_Elab_Term_SavedState_restore(x_1390, x_9, x_10, x_11, x_12, x_13, x_14, x_1398);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1400 = !lean_is_exclusive(x_1399);
if (x_1400 == 0)
{
lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
x_1401 = lean_ctor_get(x_1399, 1);
x_1402 = lean_ctor_get(x_1399, 0);
lean_dec(x_1402);
lean_ctor_set_tag(x_1399, 1);
lean_ctor_set(x_1399, 1, x_1397);
lean_ctor_set(x_1399, 0, x_1393);
x_1403 = lean_array_push(x_8, x_1399);
lean_ctor_set(x_1395, 1, x_1401);
lean_ctor_set(x_1395, 0, x_1403);
return x_1395;
}
else
{
lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; 
x_1404 = lean_ctor_get(x_1399, 1);
lean_inc(x_1404);
lean_dec(x_1399);
x_1405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1405, 0, x_1393);
lean_ctor_set(x_1405, 1, x_1397);
x_1406 = lean_array_push(x_8, x_1405);
lean_ctor_set(x_1395, 1, x_1404);
lean_ctor_set(x_1395, 0, x_1406);
return x_1395;
}
}
else
{
lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; 
x_1407 = lean_ctor_get(x_1395, 0);
x_1408 = lean_ctor_get(x_1395, 1);
lean_inc(x_1408);
lean_inc(x_1407);
lean_dec(x_1395);
x_1409 = l_Lean_Elab_Term_SavedState_restore(x_1390, x_9, x_10, x_11, x_12, x_13, x_14, x_1408);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1410 = lean_ctor_get(x_1409, 1);
lean_inc(x_1410);
if (lean_is_exclusive(x_1409)) {
 lean_ctor_release(x_1409, 0);
 lean_ctor_release(x_1409, 1);
 x_1411 = x_1409;
} else {
 lean_dec_ref(x_1409);
 x_1411 = lean_box(0);
}
if (lean_is_scalar(x_1411)) {
 x_1412 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1412 = x_1411;
 lean_ctor_set_tag(x_1412, 1);
}
lean_ctor_set(x_1412, 0, x_1393);
lean_ctor_set(x_1412, 1, x_1407);
x_1413 = lean_array_push(x_8, x_1412);
x_1414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1414, 0, x_1413);
lean_ctor_set(x_1414, 1, x_1410);
return x_1414;
}
}
else
{
lean_object* x_1415; lean_object* x_1416; uint8_t x_1417; 
lean_dec(x_8);
x_1415 = lean_ctor_get(x_1393, 0);
lean_inc(x_1415);
x_1416 = l_Lean_Elab_postponeExceptionId;
x_1417 = lean_nat_dec_eq(x_1415, x_1416);
lean_dec(x_1415);
if (x_1417 == 0)
{
lean_object* x_1418; 
lean_dec(x_1390);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1392)) {
 x_1418 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1418 = x_1392;
 lean_ctor_set_tag(x_1418, 1);
}
lean_ctor_set(x_1418, 0, x_1393);
lean_ctor_set(x_1418, 1, x_1394);
return x_1418;
}
else
{
lean_object* x_1419; uint8_t x_1420; 
lean_dec(x_1392);
x_1419 = l_Lean_Elab_Term_SavedState_restore(x_1390, x_9, x_10, x_11, x_12, x_13, x_14, x_1394);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1420 = !lean_is_exclusive(x_1419);
if (x_1420 == 0)
{
lean_object* x_1421; 
x_1421 = lean_ctor_get(x_1419, 0);
lean_dec(x_1421);
lean_ctor_set_tag(x_1419, 1);
lean_ctor_set(x_1419, 0, x_1393);
return x_1419;
}
else
{
lean_object* x_1422; lean_object* x_1423; 
x_1422 = lean_ctor_get(x_1419, 1);
lean_inc(x_1422);
lean_dec(x_1419);
x_1423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1423, 0, x_1393);
lean_ctor_set(x_1423, 1, x_1422);
return x_1423;
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
lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; 
lean_dec(x_1);
x_1453 = l_Lean_Syntax_getId(x_1117);
lean_dec(x_1117);
x_1454 = l_Lean_Name_eraseMacroScopes(x_1453);
lean_dec(x_1453);
x_1455 = l_Lean_Name_components(x_1454);
x_1456 = l_List_map___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__1(x_1455);
x_1457 = l_List_append___rarg(x_1456, x_2);
x_1 = x_1115;
x_2 = x_1457;
goto _start;
}
}
else
{
lean_object* x_1459; lean_object* x_1460; 
lean_dec(x_1);
x_1459 = l_Lean_fieldIdxKind;
x_1460 = l_Lean_Syntax_isNatLitAux(x_1459, x_1117);
lean_dec(x_1117);
if (lean_obj_tag(x_1460) == 0)
{
lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; 
x_1461 = l_Nat_Inhabited;
x_1462 = l_Option_get_x21___rarg___closed__3;
x_1463 = lean_panic_fn(x_1461, x_1462);
x_1464 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1464, 0, x_1463);
x_1465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1465, 0, x_1464);
lean_ctor_set(x_1465, 1, x_2);
x_1 = x_1115;
x_2 = x_1465;
goto _start;
}
else
{
lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; 
x_1467 = lean_ctor_get(x_1460, 0);
lean_inc(x_1467);
lean_dec(x_1460);
x_1468 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1468, 0, x_1467);
x_1469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1469, 0, x_1468);
lean_ctor_set(x_1469, 1, x_2);
x_1 = x_1115;
x_2 = x_1469;
goto _start;
}
}
}
}
}
else
{
lean_object* x_1479; uint8_t x_1480; 
x_1479 = l_Lean_Syntax_getArgs(x_1);
x_1480 = !lean_is_exclusive(x_9);
if (x_1480 == 0)
{
uint8_t x_1481; lean_object* x_1482; lean_object* x_1483; 
x_1481 = 0;
lean_ctor_set_uint8(x_9, sizeof(void*)*8 + 1, x_1481);
x_1482 = lean_unsigned_to_nat(0u);
x_1483 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_1479, x_1482, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1479);
lean_dec(x_1);
return x_1483;
}
else
{
lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; uint8_t x_1492; uint8_t x_1493; uint8_t x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; 
x_1484 = lean_ctor_get(x_9, 0);
x_1485 = lean_ctor_get(x_9, 1);
x_1486 = lean_ctor_get(x_9, 2);
x_1487 = lean_ctor_get(x_9, 3);
x_1488 = lean_ctor_get(x_9, 4);
x_1489 = lean_ctor_get(x_9, 5);
x_1490 = lean_ctor_get(x_9, 6);
x_1491 = lean_ctor_get(x_9, 7);
x_1492 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
x_1493 = lean_ctor_get_uint8(x_9, sizeof(void*)*8 + 2);
lean_inc(x_1491);
lean_inc(x_1490);
lean_inc(x_1489);
lean_inc(x_1488);
lean_inc(x_1487);
lean_inc(x_1486);
lean_inc(x_1485);
lean_inc(x_1484);
lean_dec(x_9);
x_1494 = 0;
x_1495 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_1495, 0, x_1484);
lean_ctor_set(x_1495, 1, x_1485);
lean_ctor_set(x_1495, 2, x_1486);
lean_ctor_set(x_1495, 3, x_1487);
lean_ctor_set(x_1495, 4, x_1488);
lean_ctor_set(x_1495, 5, x_1489);
lean_ctor_set(x_1495, 6, x_1490);
lean_ctor_set(x_1495, 7, x_1491);
lean_ctor_set_uint8(x_1495, sizeof(void*)*8, x_1492);
lean_ctor_set_uint8(x_1495, sizeof(void*)*8 + 1, x_1494);
lean_ctor_set_uint8(x_1495, sizeof(void*)*8 + 2, x_1493);
x_1496 = lean_unsigned_to_nat(0u);
x_1497 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_1479, x_1496, x_8, x_1495, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1479);
lean_dec(x_1);
return x_1497;
}
}
block_350:
{
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; 
x_17 = l_List_isEmpty___rarg(x_2);
if (x_7 == 0)
{
uint8_t x_346; 
x_346 = 1;
x_18 = x_346;
goto block_345;
}
else
{
uint8_t x_347; 
x_347 = 0;
x_18 = x_347;
goto block_345;
}
block_345:
{
if (x_17 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_56; 
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
x_56 = l_Lean_Elab_Term_elabTerm(x_1, x_19, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_22);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_59 = l___private_Lean_Elab_App_20__elabAppLVals(x_57, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_23);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_61);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
x_66 = l_Lean_Elab_Term_SavedState_restore(x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_65);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 1);
x_69 = lean_ctor_get(x_66, 0);
lean_dec(x_69);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_66, 0, x_60);
x_70 = lean_array_push(x_8, x_66);
lean_ctor_set(x_62, 1, x_68);
lean_ctor_set(x_62, 0, x_70);
return x_62;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_60);
lean_ctor_set(x_72, 1, x_64);
x_73 = lean_array_push(x_8, x_72);
lean_ctor_set(x_62, 1, x_71);
lean_ctor_set(x_62, 0, x_73);
return x_62;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_62, 0);
x_75 = lean_ctor_get(x_62, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_62);
x_76 = l_Lean_Elab_Term_SavedState_restore(x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_75);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_60);
lean_ctor_set(x_79, 1, x_74);
x_80 = lean_array_push(x_8, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_77);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_59, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_59, 1);
lean_inc(x_83);
lean_dec(x_59);
x_24 = x_82;
x_25 = x_83;
goto block_55;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = lean_ctor_get(x_56, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_56, 1);
lean_inc(x_85);
lean_dec(x_56);
x_24 = x_84;
x_25 = x_85;
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
}
else
{
uint8_t x_86; 
x_86 = l_Array_isEmpty___rarg(x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_124; 
x_87 = lean_box(0);
x_88 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_124 = l_Lean_Elab_Term_elabTerm(x_1, x_87, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_90);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_127 = l___private_Lean_Elab_App_20__elabAppLVals(x_125, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
lean_dec(x_91);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_129);
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_132 = lean_ctor_get(x_130, 0);
x_133 = lean_ctor_get(x_130, 1);
x_134 = l_Lean_Elab_Term_SavedState_restore(x_89, x_9, x_10, x_11, x_12, x_13, x_14, x_133);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_134, 1);
x_137 = lean_ctor_get(x_134, 0);
lean_dec(x_137);
lean_ctor_set(x_134, 1, x_132);
lean_ctor_set(x_134, 0, x_128);
x_138 = lean_array_push(x_8, x_134);
lean_ctor_set(x_130, 1, x_136);
lean_ctor_set(x_130, 0, x_138);
return x_130;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_134, 1);
lean_inc(x_139);
lean_dec(x_134);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_128);
lean_ctor_set(x_140, 1, x_132);
x_141 = lean_array_push(x_8, x_140);
lean_ctor_set(x_130, 1, x_139);
lean_ctor_set(x_130, 0, x_141);
return x_130;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_130, 0);
x_143 = lean_ctor_get(x_130, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_130);
x_144 = l_Lean_Elab_Term_SavedState_restore(x_89, x_9, x_10, x_11, x_12, x_13, x_14, x_143);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_128);
lean_ctor_set(x_147, 1, x_142);
x_148 = lean_array_push(x_8, x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_145);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_127, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_127, 1);
lean_inc(x_151);
lean_dec(x_127);
x_92 = x_150;
x_93 = x_151;
goto block_123;
}
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = lean_ctor_get(x_124, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_124, 1);
lean_inc(x_153);
lean_dec(x_124);
x_92 = x_152;
x_93 = x_153;
goto block_123;
}
block_123:
{
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_94; uint8_t x_95; 
lean_dec(x_91);
x_94 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_93);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
x_98 = l_Lean_Elab_Term_SavedState_restore(x_89, x_9, x_10, x_11, x_12, x_13, x_14, x_97);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_98, 1);
x_101 = lean_ctor_get(x_98, 0);
lean_dec(x_101);
lean_ctor_set_tag(x_98, 1);
lean_ctor_set(x_98, 1, x_96);
lean_ctor_set(x_98, 0, x_92);
x_102 = lean_array_push(x_8, x_98);
lean_ctor_set(x_94, 1, x_100);
lean_ctor_set(x_94, 0, x_102);
return x_94;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_dec(x_98);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_92);
lean_ctor_set(x_104, 1, x_96);
x_105 = lean_array_push(x_8, x_104);
lean_ctor_set(x_94, 1, x_103);
lean_ctor_set(x_94, 0, x_105);
return x_94;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_106 = lean_ctor_get(x_94, 0);
x_107 = lean_ctor_get(x_94, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_94);
x_108 = l_Lean_Elab_Term_SavedState_restore(x_89, x_9, x_10, x_11, x_12, x_13, x_14, x_107);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
 lean_ctor_set_tag(x_111, 1);
}
lean_ctor_set(x_111, 0, x_92);
lean_ctor_set(x_111, 1, x_106);
x_112 = lean_array_push(x_8, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_109);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_8);
x_114 = lean_ctor_get(x_92, 0);
lean_inc(x_114);
x_115 = l_Lean_Elab_postponeExceptionId;
x_116 = lean_nat_dec_eq(x_114, x_115);
lean_dec(x_114);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_89);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_91)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_91;
 lean_ctor_set_tag(x_117, 1);
}
lean_ctor_set(x_117, 0, x_92);
lean_ctor_set(x_117, 1, x_93);
return x_117;
}
else
{
lean_object* x_118; uint8_t x_119; 
lean_dec(x_91);
x_118 = l_Lean_Elab_Term_SavedState_restore(x_89, x_9, x_10, x_11, x_12, x_13, x_14, x_93);
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
lean_ctor_set(x_118, 0, x_92);
return x_118;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_92);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
}
else
{
uint8_t x_154; 
x_154 = l_Array_isEmpty___rarg(x_4);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_192; 
x_155 = lean_box(0);
x_156 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_192 = l_Lean_Elab_Term_elabTerm(x_1, x_155, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_158);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_195 = l___private_Lean_Elab_App_20__elabAppLVals(x_193, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_194);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_dec(x_159);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_197);
x_199 = !lean_is_exclusive(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_200 = lean_ctor_get(x_198, 0);
x_201 = lean_ctor_get(x_198, 1);
x_202 = l_Lean_Elab_Term_SavedState_restore(x_157, x_9, x_10, x_11, x_12, x_13, x_14, x_201);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_202, 1);
x_205 = lean_ctor_get(x_202, 0);
lean_dec(x_205);
lean_ctor_set(x_202, 1, x_200);
lean_ctor_set(x_202, 0, x_196);
x_206 = lean_array_push(x_8, x_202);
lean_ctor_set(x_198, 1, x_204);
lean_ctor_set(x_198, 0, x_206);
return x_198;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_202, 1);
lean_inc(x_207);
lean_dec(x_202);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_196);
lean_ctor_set(x_208, 1, x_200);
x_209 = lean_array_push(x_8, x_208);
lean_ctor_set(x_198, 1, x_207);
lean_ctor_set(x_198, 0, x_209);
return x_198;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_210 = lean_ctor_get(x_198, 0);
x_211 = lean_ctor_get(x_198, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_198);
x_212 = l_Lean_Elab_Term_SavedState_restore(x_157, x_9, x_10, x_11, x_12, x_13, x_14, x_211);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_214 = x_212;
} else {
 lean_dec_ref(x_212);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_196);
lean_ctor_set(x_215, 1, x_210);
x_216 = lean_array_push(x_8, x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_213);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_195, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_195, 1);
lean_inc(x_219);
lean_dec(x_195);
x_160 = x_218;
x_161 = x_219;
goto block_191;
}
}
else
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_220 = lean_ctor_get(x_192, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_192, 1);
lean_inc(x_221);
lean_dec(x_192);
x_160 = x_220;
x_161 = x_221;
goto block_191;
}
block_191:
{
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_162; uint8_t x_163; 
lean_dec(x_159);
x_162 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_161);
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_164 = lean_ctor_get(x_162, 0);
x_165 = lean_ctor_get(x_162, 1);
x_166 = l_Lean_Elab_Term_SavedState_restore(x_157, x_9, x_10, x_11, x_12, x_13, x_14, x_165);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_166, 1);
x_169 = lean_ctor_get(x_166, 0);
lean_dec(x_169);
lean_ctor_set_tag(x_166, 1);
lean_ctor_set(x_166, 1, x_164);
lean_ctor_set(x_166, 0, x_160);
x_170 = lean_array_push(x_8, x_166);
lean_ctor_set(x_162, 1, x_168);
lean_ctor_set(x_162, 0, x_170);
return x_162;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_166, 1);
lean_inc(x_171);
lean_dec(x_166);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_160);
lean_ctor_set(x_172, 1, x_164);
x_173 = lean_array_push(x_8, x_172);
lean_ctor_set(x_162, 1, x_171);
lean_ctor_set(x_162, 0, x_173);
return x_162;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_174 = lean_ctor_get(x_162, 0);
x_175 = lean_ctor_get(x_162, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_162);
x_176 = l_Lean_Elab_Term_SavedState_restore(x_157, x_9, x_10, x_11, x_12, x_13, x_14, x_175);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_178 = x_176;
} else {
 lean_dec_ref(x_176);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
 lean_ctor_set_tag(x_179, 1);
}
lean_ctor_set(x_179, 0, x_160);
lean_ctor_set(x_179, 1, x_174);
x_180 = lean_array_push(x_8, x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_177);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_dec(x_8);
x_182 = lean_ctor_get(x_160, 0);
lean_inc(x_182);
x_183 = l_Lean_Elab_postponeExceptionId;
x_184 = lean_nat_dec_eq(x_182, x_183);
lean_dec(x_182);
if (x_184 == 0)
{
lean_object* x_185; 
lean_dec(x_157);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_159)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_159;
 lean_ctor_set_tag(x_185, 1);
}
lean_ctor_set(x_185, 0, x_160);
lean_ctor_set(x_185, 1, x_161);
return x_185;
}
else
{
lean_object* x_186; uint8_t x_187; 
lean_dec(x_159);
x_186 = l_Lean_Elab_Term_SavedState_restore(x_157, x_9, x_10, x_11, x_12, x_13, x_14, x_161);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_186, 0);
lean_dec(x_188);
lean_ctor_set_tag(x_186, 1);
lean_ctor_set(x_186, 0, x_160);
return x_186;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_160);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
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
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_258; lean_object* x_259; 
x_222 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_225 = x_222;
} else {
 lean_dec_ref(x_222);
 x_225 = lean_box(0);
}
x_258 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_259 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_258, x_9, x_10, x_11, x_12, x_13, x_14, x_224);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
lean_dec(x_225);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_261);
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_264 = lean_ctor_get(x_262, 0);
x_265 = lean_ctor_get(x_262, 1);
x_266 = l_Lean_Elab_Term_SavedState_restore(x_223, x_9, x_10, x_11, x_12, x_13, x_14, x_265);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_267 = !lean_is_exclusive(x_266);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_266, 1);
x_269 = lean_ctor_get(x_266, 0);
lean_dec(x_269);
lean_ctor_set(x_266, 1, x_264);
lean_ctor_set(x_266, 0, x_260);
x_270 = lean_array_push(x_8, x_266);
lean_ctor_set(x_262, 1, x_268);
lean_ctor_set(x_262, 0, x_270);
return x_262;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_266, 1);
lean_inc(x_271);
lean_dec(x_266);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_260);
lean_ctor_set(x_272, 1, x_264);
x_273 = lean_array_push(x_8, x_272);
lean_ctor_set(x_262, 1, x_271);
lean_ctor_set(x_262, 0, x_273);
return x_262;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_274 = lean_ctor_get(x_262, 0);
x_275 = lean_ctor_get(x_262, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_262);
x_276 = l_Lean_Elab_Term_SavedState_restore(x_223, x_9, x_10, x_11, x_12, x_13, x_14, x_275);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_278 = x_276;
} else {
 lean_dec_ref(x_276);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_260);
lean_ctor_set(x_279, 1, x_274);
x_280 = lean_array_push(x_8, x_279);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_277);
return x_281;
}
}
else
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_259, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_259, 1);
lean_inc(x_283);
lean_dec(x_259);
x_226 = x_282;
x_227 = x_283;
goto block_257;
}
block_257:
{
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_228; uint8_t x_229; 
lean_dec(x_225);
x_228 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_227);
x_229 = !lean_is_exclusive(x_228);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_230 = lean_ctor_get(x_228, 0);
x_231 = lean_ctor_get(x_228, 1);
x_232 = l_Lean_Elab_Term_SavedState_restore(x_223, x_9, x_10, x_11, x_12, x_13, x_14, x_231);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_233 = !lean_is_exclusive(x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_232, 1);
x_235 = lean_ctor_get(x_232, 0);
lean_dec(x_235);
lean_ctor_set_tag(x_232, 1);
lean_ctor_set(x_232, 1, x_230);
lean_ctor_set(x_232, 0, x_226);
x_236 = lean_array_push(x_8, x_232);
lean_ctor_set(x_228, 1, x_234);
lean_ctor_set(x_228, 0, x_236);
return x_228;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_232, 1);
lean_inc(x_237);
lean_dec(x_232);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_226);
lean_ctor_set(x_238, 1, x_230);
x_239 = lean_array_push(x_8, x_238);
lean_ctor_set(x_228, 1, x_237);
lean_ctor_set(x_228, 0, x_239);
return x_228;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_240 = lean_ctor_get(x_228, 0);
x_241 = lean_ctor_get(x_228, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_228);
x_242 = l_Lean_Elab_Term_SavedState_restore(x_223, x_9, x_10, x_11, x_12, x_13, x_14, x_241);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_244 = x_242;
} else {
 lean_dec_ref(x_242);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
 lean_ctor_set_tag(x_245, 1);
}
lean_ctor_set(x_245, 0, x_226);
lean_ctor_set(x_245, 1, x_240);
x_246 = lean_array_push(x_8, x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_243);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; uint8_t x_250; 
lean_dec(x_8);
x_248 = lean_ctor_get(x_226, 0);
lean_inc(x_248);
x_249 = l_Lean_Elab_postponeExceptionId;
x_250 = lean_nat_dec_eq(x_248, x_249);
lean_dec(x_248);
if (x_250 == 0)
{
lean_object* x_251; 
lean_dec(x_223);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_225)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_225;
 lean_ctor_set_tag(x_251, 1);
}
lean_ctor_set(x_251, 0, x_226);
lean_ctor_set(x_251, 1, x_227);
return x_251;
}
else
{
lean_object* x_252; uint8_t x_253; 
lean_dec(x_225);
x_252 = l_Lean_Elab_Term_SavedState_restore(x_223, x_9, x_10, x_11, x_12, x_13, x_14, x_227);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_253 = !lean_is_exclusive(x_252);
if (x_253 == 0)
{
lean_object* x_254; 
x_254 = lean_ctor_get(x_252, 0);
lean_dec(x_254);
lean_ctor_set_tag(x_252, 1);
lean_ctor_set(x_252, 0, x_226);
return x_252;
}
else
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_252, 1);
lean_inc(x_255);
lean_dec(x_252);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_226);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_320; 
x_284 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_287 = x_284;
} else {
 lean_dec_ref(x_284);
 x_287 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_320 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_286);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
lean_dec(x_287);
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_323 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_322);
x_324 = !lean_is_exclusive(x_323);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_325 = lean_ctor_get(x_323, 0);
x_326 = lean_ctor_get(x_323, 1);
x_327 = l_Lean_Elab_Term_SavedState_restore(x_285, x_9, x_10, x_11, x_12, x_13, x_14, x_326);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_328 = !lean_is_exclusive(x_327);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_327, 1);
x_330 = lean_ctor_get(x_327, 0);
lean_dec(x_330);
lean_ctor_set(x_327, 1, x_325);
lean_ctor_set(x_327, 0, x_321);
x_331 = lean_array_push(x_8, x_327);
lean_ctor_set(x_323, 1, x_329);
lean_ctor_set(x_323, 0, x_331);
return x_323;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_327, 1);
lean_inc(x_332);
lean_dec(x_327);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_321);
lean_ctor_set(x_333, 1, x_325);
x_334 = lean_array_push(x_8, x_333);
lean_ctor_set(x_323, 1, x_332);
lean_ctor_set(x_323, 0, x_334);
return x_323;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_335 = lean_ctor_get(x_323, 0);
x_336 = lean_ctor_get(x_323, 1);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_323);
x_337 = l_Lean_Elab_Term_SavedState_restore(x_285, x_9, x_10, x_11, x_12, x_13, x_14, x_336);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_338 = lean_ctor_get(x_337, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_339 = x_337;
} else {
 lean_dec_ref(x_337);
 x_339 = lean_box(0);
}
if (lean_is_scalar(x_339)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_339;
}
lean_ctor_set(x_340, 0, x_321);
lean_ctor_set(x_340, 1, x_335);
x_341 = lean_array_push(x_8, x_340);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_338);
return x_342;
}
}
else
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_ctor_get(x_320, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_320, 1);
lean_inc(x_344);
lean_dec(x_320);
x_288 = x_343;
x_289 = x_344;
goto block_319;
}
block_319:
{
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_290; uint8_t x_291; 
lean_dec(x_287);
x_290 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_289);
x_291 = !lean_is_exclusive(x_290);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_292 = lean_ctor_get(x_290, 0);
x_293 = lean_ctor_get(x_290, 1);
x_294 = l_Lean_Elab_Term_SavedState_restore(x_285, x_9, x_10, x_11, x_12, x_13, x_14, x_293);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_295 = !lean_is_exclusive(x_294);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_294, 1);
x_297 = lean_ctor_get(x_294, 0);
lean_dec(x_297);
lean_ctor_set_tag(x_294, 1);
lean_ctor_set(x_294, 1, x_292);
lean_ctor_set(x_294, 0, x_288);
x_298 = lean_array_push(x_8, x_294);
lean_ctor_set(x_290, 1, x_296);
lean_ctor_set(x_290, 0, x_298);
return x_290;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_294, 1);
lean_inc(x_299);
lean_dec(x_294);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_288);
lean_ctor_set(x_300, 1, x_292);
x_301 = lean_array_push(x_8, x_300);
lean_ctor_set(x_290, 1, x_299);
lean_ctor_set(x_290, 0, x_301);
return x_290;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_302 = lean_ctor_get(x_290, 0);
x_303 = lean_ctor_get(x_290, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_290);
x_304 = l_Lean_Elab_Term_SavedState_restore(x_285, x_9, x_10, x_11, x_12, x_13, x_14, x_303);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_306 = x_304;
} else {
 lean_dec_ref(x_304);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 2, 0);
} else {
 x_307 = x_306;
 lean_ctor_set_tag(x_307, 1);
}
lean_ctor_set(x_307, 0, x_288);
lean_ctor_set(x_307, 1, x_302);
x_308 = lean_array_push(x_8, x_307);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_305);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; uint8_t x_312; 
lean_dec(x_8);
x_310 = lean_ctor_get(x_288, 0);
lean_inc(x_310);
x_311 = l_Lean_Elab_postponeExceptionId;
x_312 = lean_nat_dec_eq(x_310, x_311);
lean_dec(x_310);
if (x_312 == 0)
{
lean_object* x_313; 
lean_dec(x_285);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_287)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_287;
 lean_ctor_set_tag(x_313, 1);
}
lean_ctor_set(x_313, 0, x_288);
lean_ctor_set(x_313, 1, x_289);
return x_313;
}
else
{
lean_object* x_314; uint8_t x_315; 
lean_dec(x_287);
x_314 = l_Lean_Elab_Term_SavedState_restore(x_285, x_9, x_10, x_11, x_12, x_13, x_14, x_289);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_315 = !lean_is_exclusive(x_314);
if (x_315 == 0)
{
lean_object* x_316; 
x_316 = lean_ctor_get(x_314, 0);
lean_dec(x_316);
lean_ctor_set_tag(x_314, 1);
lean_ctor_set(x_314, 0, x_288);
return x_314;
}
else
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_ctor_get(x_314, 1);
lean_inc(x_317);
lean_dec(x_314);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_288);
lean_ctor_set(x_318, 1, x_317);
return x_318;
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
lean_object* x_348; lean_object* x_349; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_348 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__3;
x_349 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_348, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_349;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_22__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_1);
return x_18;
}
}
lean_object* l___private_Lean_Elab_App_22__elabAppFn___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = l___private_Lean_Elab_App_22__elabAppFn___main(x_1, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
lean_object* l___private_Lean_Elab_App_22__elabAppFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_App_22__elabAppFn___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
lean_object* l___private_Lean_Elab_App_22__elabAppFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = l___private_Lean_Elab_App_22__elabAppFn(x_1, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_App_23__getSuccess___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; 
x_7 = lean_array_fget(x_1, x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_7);
x_8 = lean_nat_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_11 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_fswap(x_1, x_2, x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_16 = lean_nat_add(x_3, x_14);
lean_dec(x_3);
x_1 = x_13;
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
lean_dec(x_2);
x_2 = x_19;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_App_23__getSuccess(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_filterAux___main___at___private_Lean_Elab_App_23__getSuccess___spec__1(x_1, x_2, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_24__toMessageData___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_24__toMessageData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_24__toMessageData___spec__1___rarg___boxed), 3, 0);
return x_5;
}
}
lean_object* _init_l___private_Lean_Elab_App_24__toMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Syntax_6__formatInfo___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_24__toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_24__toMessageData___spec__1___rarg(x_6, x_7, x_8);
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
x_23 = l___private_Lean_Elab_App_24__toMessageData___closed__1;
x_24 = lean_alloc_ctor(9, 2, 0);
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
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Exception_toMessageData(x_1);
x_33 = lean_alloc_ctor(9, 2, 0);
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
x_49 = l___private_Lean_Elab_App_24__toMessageData___closed__1;
x_50 = lean_alloc_ctor(9, 2, 0);
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
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Exception_toMessageData(x_1);
x_59 = lean_alloc_ctor(9, 2, 0);
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
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_24__toMessageData___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_24__toMessageData___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_24__toMessageData___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_24__toMessageData___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_24__toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_24__toMessageData(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_25__mergeFailures___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_33 = l___private_Lean_Elab_App_24__toMessageData(x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* _init_l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("overloaded, errors ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_25__mergeFailures___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = x_1;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_App_25__mergeFailures___spec__1), 9, 2);
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
x_16 = l_Lean_MessageData_ofArray(x_14);
lean_dec(x_14);
x_17 = l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__3;
x_18 = lean_alloc_ctor(9, 2, 0);
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
lean_object* l___private_Lean_Elab_App_25__mergeFailures(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_25__mergeFailures___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_26__elabAppAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* _init_l___private_Lean_Elab_App_26__elabAppAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous, possible interpretations ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_26__elabAppAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_26__elabAppAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_26__elabAppAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_26__elabAppAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_26__elabAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_15 = l___private_Lean_Elab_App_22__elabAppFn___main(x_1, x_12, x_2, x_3, x_4, x_13, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_22 = l_Array_filterAux___main___at___private_Lean_Elab_App_23__getSuccess___spec__1(x_16, x_21, x_21);
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
x_31 = l___private_Lean_Elab_App_25__mergeFailures___rarg(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
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
x_40 = l___private_Lean_Elab_App_25__mergeFailures___rarg(x_16, x_5, x_6, x_7, x_8, x_39, x_10, x_17);
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
x_44 = l_Array_umapMAux___main___at___private_Lean_Elab_App_26__elabAppAux___spec__1(x_41, x_42, x_21, x_43);
x_45 = x_44;
x_46 = l_Lean_MessageData_ofArray(x_45);
lean_dec(x_45);
x_47 = l___private_Lean_Elab_App_26__elabAppAux___closed__3;
x_48 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_1, x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_9);
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
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_1);
x_53 = l_Lean_Elab_Term_TermElabResult_inhabited;
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_array_get(x_53, x_16, x_54);
lean_dec(x_16);
x_56 = l_Lean_Elab_Term_applyResult(x_55, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_15);
if (x_57 == 0)
{
return x_15;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_15, 0);
x_59 = lean_ctor_get(x_15, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_15);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namedArgument");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ellipsis");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected '..'");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__7() {
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
lean_object* _init_l_Lean_Elab_Term_expandApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'..' is only allowed in patterns");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_expandApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_expandApp___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_expandApp___closed__3() {
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
lean_dec(x_9);
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
lean_dec(x_9);
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
lean_dec(x_9);
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
lean_dec(x_7);
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
x_19 = l___private_Lean_Elab_App_26__elabAppAux(x_16, x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
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
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabApp___closed__1() {
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
lean_object* l___private_Lean_Elab_App_27__elabAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Array_empty___closed__1;
x_11 = l___private_Lean_Elab_App_26__elabAppAux(x_1, x_10, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_27__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1() {
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
x_10 = l___private_Lean_Elab_App_27__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1() {
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
x_3 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__12;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_27__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1() {
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
x_3 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1;
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
x_50 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__5;
lean_inc(x_13);
x_51 = l_Lean_Syntax_isOfKind(x_13, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_1);
x_52 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__20;
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
x_63 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__20;
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
x_74 = l___private_Lean_Elab_App_27__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_74;
}
}
}
}
else
{
lean_object* x_75; 
lean_dec(x_13);
x_75 = l___private_Lean_Elab_App_27__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1() {
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
x_10 = l___private_Lean_Elab_App_27__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1() {
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
x_10 = l___private_Lean_Elab_App_27__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabProj___closed__1() {
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
x_3 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__13;
x_4 = l___regBuiltin_Lean_Elab_Term_elabProj___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_27__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1() {
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
x_3 = l___private_Lean_Elab_App_22__elabAppFn___main___closed__10;
x_4 = l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_28__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1;
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
l___private_Lean_Elab_App_4__tryCoeFun___closed__1 = _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_4__tryCoeFun___closed__1);
l___private_Lean_Elab_App_4__tryCoeFun___closed__2 = _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_4__tryCoeFun___closed__2);
l___private_Lean_Elab_App_4__tryCoeFun___closed__3 = _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_4__tryCoeFun___closed__3);
l___private_Lean_Elab_App_4__tryCoeFun___closed__4 = _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_4__tryCoeFun___closed__4);
l___private_Lean_Elab_App_4__tryCoeFun___closed__5 = _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_4__tryCoeFun___closed__5);
l___private_Lean_Elab_App_4__tryCoeFun___closed__6 = _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_4__tryCoeFun___closed__6);
l___private_Lean_Elab_App_4__tryCoeFun___closed__7 = _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_4__tryCoeFun___closed__7);
l___private_Lean_Elab_App_4__tryCoeFun___closed__8 = _init_l___private_Lean_Elab_App_4__tryCoeFun___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_4__tryCoeFun___closed__8);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__2 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__2);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__4 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__4);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__5 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__5);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__7 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__7);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__8 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__8);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__10 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__10);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__11 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__11);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__13 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__13();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__13);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__14 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__14();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__14);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__17 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__17();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__17);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__18 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__18();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__18);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__19 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__19();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__19);
l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__20 = _init_l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__20();
lean_mark_persistent(l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__20);
l___private_Lean_Elab_App_11__elabAppArgs___closed__1 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__1);
l___private_Lean_Elab_App_11__elabAppArgs___closed__2 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__2);
l___private_Lean_Elab_App_11__elabAppArgs___closed__3 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__3);
l___private_Lean_Elab_App_11__elabAppArgs___closed__4 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__4);
l___private_Lean_Elab_App_11__elabAppArgs___closed__5 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__5);
l___private_Lean_Elab_App_11__elabAppArgs___closed__6 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__6);
l___private_Lean_Elab_App_11__elabAppArgs___closed__7 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__7);
l___private_Lean_Elab_App_11__elabAppArgs___closed__8 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__8);
l___private_Lean_Elab_App_11__elabAppArgs___closed__9 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__9);
l___private_Lean_Elab_App_11__elabAppArgs___closed__10 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__10);
l___private_Lean_Elab_App_11__elabAppArgs___closed__11 = _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_11__elabAppArgs___closed__11);
l___private_Lean_Elab_App_14__resolveLValAux___closed__1 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__1);
l___private_Lean_Elab_App_14__resolveLValAux___closed__2 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__2);
l___private_Lean_Elab_App_14__resolveLValAux___closed__3 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__3);
l___private_Lean_Elab_App_14__resolveLValAux___closed__4 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__4);
l___private_Lean_Elab_App_14__resolveLValAux___closed__5 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__5);
l___private_Lean_Elab_App_14__resolveLValAux___closed__6 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__6);
l___private_Lean_Elab_App_14__resolveLValAux___closed__7 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__7);
l___private_Lean_Elab_App_14__resolveLValAux___closed__8 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__8);
l___private_Lean_Elab_App_14__resolveLValAux___closed__9 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__9);
l___private_Lean_Elab_App_14__resolveLValAux___closed__10 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__10);
l___private_Lean_Elab_App_14__resolveLValAux___closed__11 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__11);
l___private_Lean_Elab_App_14__resolveLValAux___closed__12 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__12);
l___private_Lean_Elab_App_14__resolveLValAux___closed__13 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__13();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__13);
l___private_Lean_Elab_App_14__resolveLValAux___closed__14 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__14();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__14);
l___private_Lean_Elab_App_14__resolveLValAux___closed__15 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__15();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__15);
l___private_Lean_Elab_App_14__resolveLValAux___closed__16 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__16();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__16);
l___private_Lean_Elab_App_14__resolveLValAux___closed__17 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__17();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__17);
l___private_Lean_Elab_App_14__resolveLValAux___closed__18 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__18();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__18);
l___private_Lean_Elab_App_14__resolveLValAux___closed__19 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__19();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__19);
l___private_Lean_Elab_App_14__resolveLValAux___closed__20 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__20();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__20);
l___private_Lean_Elab_App_14__resolveLValAux___closed__21 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__21();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__21);
l___private_Lean_Elab_App_14__resolveLValAux___closed__22 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__22();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__22);
l___private_Lean_Elab_App_14__resolveLValAux___closed__23 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__23();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__23);
l___private_Lean_Elab_App_14__resolveLValAux___closed__24 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__24();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__24);
l___private_Lean_Elab_App_14__resolveLValAux___closed__25 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__25();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__25);
l___private_Lean_Elab_App_14__resolveLValAux___closed__26 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__26();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__26);
l___private_Lean_Elab_App_14__resolveLValAux___closed__27 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__27();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__27);
l___private_Lean_Elab_App_14__resolveLValAux___closed__28 = _init_l___private_Lean_Elab_App_14__resolveLValAux___closed__28();
lean_mark_persistent(l___private_Lean_Elab_App_14__resolveLValAux___closed__28);
l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__1 = _init_l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__1);
l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__2 = _init_l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__2();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_App_17__mkBaseProjections___spec__1___closed__2);
l___private_Lean_Elab_App_17__mkBaseProjections___closed__1 = _init_l___private_Lean_Elab_App_17__mkBaseProjections___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_17__mkBaseProjections___closed__1);
l___private_Lean_Elab_App_17__mkBaseProjections___closed__2 = _init_l___private_Lean_Elab_App_17__mkBaseProjections___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_17__mkBaseProjections___closed__2);
l___private_Lean_Elab_App_17__mkBaseProjections___closed__3 = _init_l___private_Lean_Elab_App_17__mkBaseProjections___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_17__mkBaseProjections___closed__3);
l___private_Lean_Elab_App_18__addLValArg___main___closed__1 = _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_18__addLValArg___main___closed__1);
l___private_Lean_Elab_App_18__addLValArg___main___closed__2 = _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_18__addLValArg___main___closed__2);
l___private_Lean_Elab_App_18__addLValArg___main___closed__3 = _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_18__addLValArg___main___closed__3);
l___private_Lean_Elab_App_18__addLValArg___main___closed__4 = _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_18__addLValArg___main___closed__4);
l___private_Lean_Elab_App_18__addLValArg___main___closed__5 = _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_18__addLValArg___main___closed__5);
l___private_Lean_Elab_App_18__addLValArg___main___closed__6 = _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_18__addLValArg___main___closed__6);
l___private_Lean_Elab_App_18__addLValArg___main___closed__7 = _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_18__addLValArg___main___closed__7);
l___private_Lean_Elab_App_18__addLValArg___main___closed__8 = _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_18__addLValArg___main___closed__8);
l___private_Lean_Elab_App_18__addLValArg___main___closed__9 = _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_18__addLValArg___main___closed__9);
l___private_Lean_Elab_App_18__addLValArg___main___closed__10 = _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_18__addLValArg___main___closed__10);
l___private_Lean_Elab_App_18__addLValArg___main___closed__11 = _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_18__addLValArg___main___closed__11);
l___private_Lean_Elab_App_18__addLValArg___main___closed__12 = _init_l___private_Lean_Elab_App_18__addLValArg___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_18__addLValArg___main___closed__12);
l___private_Lean_Elab_App_19__elabAppLValsAux___main___closed__1 = _init_l___private_Lean_Elab_App_19__elabAppLValsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_19__elabAppLValsAux___main___closed__1);
l___private_Lean_Elab_App_19__elabAppLValsAux___main___closed__2 = _init_l___private_Lean_Elab_App_19__elabAppLValsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_19__elabAppLValsAux___main___closed__2);
l___private_Lean_Elab_App_20__elabAppLVals___closed__1 = _init_l___private_Lean_Elab_App_20__elabAppLVals___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_20__elabAppLVals___closed__1);
l___private_Lean_Elab_App_20__elabAppLVals___closed__2 = _init_l___private_Lean_Elab_App_20__elabAppLVals___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_20__elabAppLVals___closed__2);
l___private_Lean_Elab_App_20__elabAppLVals___closed__3 = _init_l___private_Lean_Elab_App_20__elabAppLVals___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_20__elabAppLVals___closed__3);
l___private_Lean_Elab_App_22__elabAppFn___main___closed__1 = _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_22__elabAppFn___main___closed__1);
l___private_Lean_Elab_App_22__elabAppFn___main___closed__2 = _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_22__elabAppFn___main___closed__2);
l___private_Lean_Elab_App_22__elabAppFn___main___closed__3 = _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_22__elabAppFn___main___closed__3);
l___private_Lean_Elab_App_22__elabAppFn___main___closed__4 = _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_22__elabAppFn___main___closed__4);
l___private_Lean_Elab_App_22__elabAppFn___main___closed__5 = _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_22__elabAppFn___main___closed__5);
l___private_Lean_Elab_App_22__elabAppFn___main___closed__6 = _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_22__elabAppFn___main___closed__6);
l___private_Lean_Elab_App_22__elabAppFn___main___closed__7 = _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_22__elabAppFn___main___closed__7);
l___private_Lean_Elab_App_22__elabAppFn___main___closed__8 = _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_22__elabAppFn___main___closed__8);
l___private_Lean_Elab_App_22__elabAppFn___main___closed__9 = _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_22__elabAppFn___main___closed__9);
l___private_Lean_Elab_App_22__elabAppFn___main___closed__10 = _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_22__elabAppFn___main___closed__10);
l___private_Lean_Elab_App_22__elabAppFn___main___closed__11 = _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_22__elabAppFn___main___closed__11);
l___private_Lean_Elab_App_22__elabAppFn___main___closed__12 = _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_22__elabAppFn___main___closed__12);
l___private_Lean_Elab_App_22__elabAppFn___main___closed__13 = _init_l___private_Lean_Elab_App_22__elabAppFn___main___closed__13();
lean_mark_persistent(l___private_Lean_Elab_App_22__elabAppFn___main___closed__13);
l___private_Lean_Elab_App_24__toMessageData___closed__1 = _init_l___private_Lean_Elab_App_24__toMessageData___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_24__toMessageData___closed__1);
l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__1 = _init_l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__1);
l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__2 = _init_l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__2);
l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__3 = _init_l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_25__mergeFailures___rarg___closed__3);
l___private_Lean_Elab_App_26__elabAppAux___closed__1 = _init_l___private_Lean_Elab_App_26__elabAppAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_26__elabAppAux___closed__1);
l___private_Lean_Elab_App_26__elabAppAux___closed__2 = _init_l___private_Lean_Elab_App_26__elabAppAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_26__elabAppAux___closed__2);
l___private_Lean_Elab_App_26__elabAppAux___closed__3 = _init_l___private_Lean_Elab_App_26__elabAppAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_26__elabAppAux___closed__3);
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
res = l___private_Lean_Elab_App_28__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
