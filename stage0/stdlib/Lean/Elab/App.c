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
lean_object* l___private_Lean_Elab_App_17__resolveLVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg___closed__5;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_7__hasOnlyTypeMVar___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_elabForall___spec__1___rarg(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_13__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__23;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__13;
extern lean_object* l___private_Lean_Elab_SyntheticMVars_9__synthesizeSyntheticMVarsStep___closed__9;
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
lean_object* l___private_Lean_Elab_Term_17__elabTermAux___main(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__3;
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__1;
lean_object* l___private_Lean_Elab_App_9__nextArgIsHole___boxed(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__5;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(lean_object*, lean_object*);
extern lean_object* l_Lean_fieldIdxKind___closed__2;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___closed__12;
lean_object* l___private_Lean_Elab_App_16__resolveLValLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__21;
lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___closed__2;
lean_object* l___private_Lean_Elab_App_28__mergeFailures(lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_19__addLValArg___main___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwUnsupportedSyntax___rarg___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_17__elabTermAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
lean_object* l___private_Lean_Elab_App_18__mkBaseProjections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__6;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___closed__3;
extern lean_object* l_Lean_identKind___closed__2;
lean_object* l___private_Lean_Meta_InferType_22__isTypeFormerTypeImp___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__5;
extern lean_object* l_Prod_HasRepr___rarg___closed__1;
lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppLVals___closed__3;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__7;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_App_5__getForallBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__6;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp___closed__1;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__17;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_App_9__nextArgIsHole(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_12__throwLValError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_16__resolveLValLoop___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__mkBaseProjections___closed__2;
lean_object* l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_goalsToMessageData___closed__1;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_23__elabAppFn___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__10;
lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___closed__13;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__8;
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__6;
lean_object* l___regBuiltin_Lean_Elab_Term_elabApp(lean_object*);
lean_object* l___private_Lean_Elab_App_26__toMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent(lean_object*);
uint8_t l_Array_contains___at_Lean_Elab_Term_logUnassignedUsingErrorContext___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* lean_local_ctx_find_from_user_name(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_hasToString(lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__27;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_App_18__mkBaseProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__mkBaseProjections___closed__1;
lean_object* l___private_Lean_Elab_App_13__findMethod_x3f___main(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__9;
lean_object* l_Lean_Expr_getOptParamDefault_x3f(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___closed__1;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_29__elabAppAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_3__mkArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_InferType_4__getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_13__findMethod_x3f___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_15__consumeImplicits___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__2;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__6;
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_23__elabAppFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_6__hasTypeMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_App_25__getSuccess___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_NamedArg_inhabited;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__1;
extern lean_object* l_Lean_mkAppStx___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__5;
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_30__elabAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__3;
lean_object* l___private_Lean_Elab_App_22__elabAppFnId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___closed__8;
lean_object* l___private_Lean_Elab_App_19__addLValArg___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__addLValArg___main___closed__10;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__14;
lean_object* l_Lean_Elab_Term_registerMVarErrorContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__28;
lean_object* l___private_Lean_Elab_App_16__resolveLValLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__3;
lean_object* l___private_Lean_Elab_App_29__elabAppAux___closed__3;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__5;
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___closed__9;
lean_object* l___private_Lean_Elab_App_29__elabAppAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock___closed__2;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__18;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_SyntheticMVars_9__synthesizeSyntheticMVarsStep___closed__10;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__15;
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__addLValArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1;
lean_object* l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__3;
lean_object* l___private_Lean_Elab_App_6__hasTypeMVar___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__13;
uint8_t l___private_Lean_Elab_App_7__hasOnlyTypeMVar(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___closed__4;
lean_object* l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrNamespace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__7;
extern lean_object* l_Lean_choiceKind___closed__2;
lean_object* l___private_Lean_Elab_App_15__consumeImplicits___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_Inhabited;
extern lean_object* l___private_Lean_Syntax_6__formatInfo___closed__1;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__6;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__7;
lean_object* l___private_Lean_Elab_App_5__getForallBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___closed__3;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__5;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_copyInfo(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__14;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__20;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__25;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__3;
lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___closed__1;
lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Term_10__isExplicit___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_28__mergeFailures___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__7;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___closed__5;
lean_object* l_Lean_Elab_Term_NamedArg_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_Arg_hasToString(lean_object*);
lean_object* l___private_Lean_Elab_App_26__toMessageData___closed__1;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__8;
extern lean_object* l_Std_PersistentArray_Stats_toString___closed__4;
lean_object* l___private_Lean_Elab_App_29__elabAppAux___closed__1;
lean_object* l_Nat_repr(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1;
lean_object* l___private_Lean_Elab_App_15__consumeImplicits___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l___private_Lean_Elab_App_12__throwLValError(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabExplicit(lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__4;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__22;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_26__toMessageData___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_29__elabAppAux___closed__2;
lean_object* l___private_Lean_Elab_App_16__resolveLValLoop___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabNamedPattern(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_19__addLValArg___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
lean_object* l_Lean_FindMVar_main___main___at___private_Lean_Elab_App_7__hasOnlyTypeMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_14__useImplicitLambda_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_App_6__hasTypeMVar(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addNamedArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___closed__6;
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_26__toMessageData___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__4;
lean_object* l_Lean_Elab_Term_elabIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_Elab_Term_elabApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_22__elabAppFnId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_12__whnfEasyCases___main___at___private_Lean_Meta_WHNF_17__whnfCoreImp___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__addLValArg___main___closed__3;
lean_object* l___private_Lean_Elab_App_26__toMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__3;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_8__propagateExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Elab_Term_elabChoice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__2;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_20__elabAppLValsAux___main(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_2__elabArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_18__mkBaseProjections___closed__3;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__1;
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
extern lean_object* l_Lean_importModules___closed__1;
extern lean_object* l_Lean_formatEntry___closed__1;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_TermElabResult_inhabited;
lean_object* l___private_Lean_Elab_App_17__resolveLVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_26__toMessageData___spec__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
lean_object* l___private_Lean_Elab_App_31__regTraceClasses(lean_object*);
lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___closed__10;
lean_object* l___regBuiltin_Lean_Elab_Term_elabProj___closed__1;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAutoParam(lean_object*);
lean_object* l_Lean_Elab_Term_elabNamedPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_22__elabAppFnId___spec__1___rarg(lean_object*);
lean_object* l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__addLValArg___main___closed__7;
lean_object* l_Lean_Name_replacePrefix___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_1__ensureArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
lean_object* l_Lean_Elab_Term_mkConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__addLValArg___main___closed__5;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Term_elabProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__3;
lean_object* l_Lean_Elab_setMacroStackOption(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Term_mkFreshUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_22__elabAppFnId___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_1__ensureArgType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_23__elabAppFn___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__16;
extern lean_object* l_Lean_mkAppStx___closed__5;
lean_object* l_Lean_Elab_Term_elabApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_23__elabAppFn___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getParentStructures(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__2;
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__8;
extern lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
extern lean_object* l_Lean_Elab_postponeExceptionId;
lean_object* l___private_Lean_Elab_App_24__isSuccess___boxed(lean_object*);
lean_object* l___private_Lean_Elab_App_20__elabAppLValsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_saveAllState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l___private_Lean_Elab_App_19__addLValArg___main___closed__2;
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__1;
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
lean_object* l___private_Lean_Elab_App_16__resolveLValLoop___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_5__getForallBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__20;
lean_object* l___private_Lean_Elab_App_19__addLValArg___main___closed__9;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_getRef(lean_object*);
lean_object* l___private_Lean_Elab_App_4__tryCoeFun___closed__2;
lean_object* l___private_Lean_Elab_App_12__throwLValError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_27__toMessageList___boxed(lean_object*);
lean_object* l___private_Lean_Elab_App_19__addLValArg___main___closed__4;
extern lean_object* l_Lean_mkHole___closed__1;
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_25__getSuccess(lean_object*);
lean_object* l_Lean_Elab_Term_elabExplicitUnivs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1___closed__2;
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabChoice___closed__1;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__19;
lean_object* l___private_Lean_Elab_App_23__elabAppFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_App_23__elabAppFn___main___spec__1(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__addLValArg___main___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__1;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Term_addNamedArg___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__addLValArg___main___closed__8;
lean_object* l_Lean_Expr_consumeMData___main(lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__5;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__addLValArg___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_List_map___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__2(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1;
lean_object* l_Lean_Elab_Term_registerSyntheticMVarWithCurrRef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__4;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isOptParam(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_inhabited___closed__1;
lean_object* l___private_Lean_Elab_App_21__elabAppLVals___closed__1;
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l___private_Lean_Elab_App_19__addLValArg___main___closed__6;
lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___closed__7;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_22__elabAppFnId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_App_24__isSuccess(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppLVals___closed__2;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__2;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_elabExplicitUnivs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Elab_App_8__propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at___private_Lean_Elab_App_13__findMethod_x3f___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__11;
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__26;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__11;
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_28__mergeFailures___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__addLValArg___main___closed__12;
extern lean_object* l_Nat_Inhabited;
lean_object* l___private_Lean_Elab_App_20__elabAppLValsAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__9;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_applyResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__8;
lean_object* l___private_Lean_Elab_App_15__consumeImplicits(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_26__toMessageData___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__4;
lean_object* l_Lean_Elab_Term_expandApp___closed__2;
lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___closed__11;
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_elabIdent___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_21__elabAppLVals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_13__findMethod_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasTypeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_14__resolveLValAux___closed__12;
lean_object* l_Lean_Elab_logException___at___private_Lean_Elab_Term_6__exceptionToSorry___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findField_x3f___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_19__addLValArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_16__resolveLValLoop___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l___private_Lean_Elab_App_19__addLValArg___main___closed__11;
lean_object* l___private_Lean_Elab_App_21__elabAppLVals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
lean_object* l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__2;
lean_object* l_Lean_Elab_Term_addNamedArg___closed__4;
lean_object* l_Lean_Elab_Term_elabExplicitUnivs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1___closed__1;
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_11__elabAppArgs___closed__2;
lean_object* l___private_Lean_Elab_App_11__elabAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__7;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_20__elabAppLValsAux(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_Arg_inhabited;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_App_27__toMessageList(lean_object*);
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
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
x_10 = l_Lean_Elab_Term_mkFreshUserName(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_4__tryCoeFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_inc(x_3);
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
x_71 = l___private_Lean_Elab_App_4__tryCoeFun___closed__8;
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
x_79 = l___private_Lean_Elab_App_4__tryCoeFun___closed__5;
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
x_45 = l___private_Lean_Elab_App_4__tryCoeFun___closed__5;
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
x_47 = l___private_Lean_Elab_App_4__tryCoeFun___closed__7;
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
lean_dec(x_3);
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
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Meta_InferType_22__isTypeFormerTypeImp___main(x_10, x_4, x_5, x_6, x_7, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_27 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_14__useImplicitLambda_x3f___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint64_t x_130; lean_object* x_131; lean_object* x_132; 
x_127 = lean_ctor_get(x_28, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_28, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_28, 2);
lean_inc(x_129);
x_130 = lean_ctor_get_uint64(x_28, sizeof(void*)*3);
x_131 = lean_unsigned_to_nat(0u);
x_132 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__3(x_127, x_16, x_131);
if (lean_obj_tag(x_132) == 0)
{
uint8_t x_133; 
x_133 = (uint8_t)((x_130 << 24) >> 61);
switch (x_133) {
case 0:
{
lean_object* x_134; uint8_t x_135; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_134 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_135 = !lean_is_exclusive(x_1);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_136 = lean_ctor_get(x_1, 7);
lean_dec(x_136);
x_137 = lean_ctor_get(x_1, 6);
lean_dec(x_137);
x_138 = lean_ctor_get(x_1, 5);
lean_dec(x_138);
x_139 = lean_ctor_get(x_1, 4);
lean_dec(x_139);
x_140 = lean_ctor_get(x_1, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_1, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_1, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_1, 0);
lean_dec(x_143);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_144; uint8_t x_145; lean_object* x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_134, 1);
lean_inc(x_144);
lean_dec(x_134);
x_145 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_ctor_set_uint8(x_1, sizeof(void*)*8 + 1, x_145);
x_146 = lean_array_get_size(x_12);
x_147 = lean_nat_dec_lt(x_15, x_146);
lean_dec(x_146);
if (x_147 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_148; 
x_148 = l_Lean_Expr_getOptParamDefault_x3f(x_128);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
x_149 = l_Lean_Expr_getAutoParamTactic_x3f(x_128);
if (lean_obj_tag(x_149) == 0)
{
uint8_t x_150; 
lean_dec(x_1);
lean_dec(x_129);
lean_dec(x_128);
x_150 = l_Array_isEmpty___rarg(x_16);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_151 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_151, 0, x_127);
x_152 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_153 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_155 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = x_16;
x_157 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_131, x_156);
x_158 = x_157;
x_159 = l_Array_toList___rarg(x_158);
lean_dec(x_158);
x_160 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_159);
x_161 = l_Array_HasRepr___rarg___closed__1;
x_162 = lean_string_append(x_161, x_160);
lean_dec(x_160);
x_163 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_165, 0, x_155);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_165, x_4, x_5, x_6, x_7, x_8, x_9, x_144);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_166;
}
else
{
lean_object* x_167; uint8_t x_168; 
lean_dec(x_127);
lean_dec(x_16);
x_167 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_168 = l_Lean_checkTraceOption(x_22, x_167);
lean_dec(x_22);
if (x_168 == 0)
{
lean_object* x_169; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_169 = x_144;
goto block_181;
}
else
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_13, 0);
lean_inc(x_182);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_183 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_182, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_144);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_169 = x_184;
goto block_181;
}
else
{
uint8_t x_185; 
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
x_185 = !lean_is_exclusive(x_183);
if (x_185 == 0)
{
return x_183;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_183, 0);
x_187 = lean_ctor_get(x_183, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_183);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
block_181:
{
lean_object* x_170; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_170 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_169);
lean_dec(x_17);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
lean_inc(x_2);
x_172 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__5(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_171);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_172, 0);
lean_dec(x_174);
lean_ctor_set(x_172, 0, x_2);
return x_172;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_2);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
else
{
uint8_t x_177; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_177 = !lean_is_exclusive(x_170);
if (x_177 == 0)
{
return x_170;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_170, 0);
x_179 = lean_ctor_get(x_170, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_170);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_inc(x_2);
x_189 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_189, 0, x_2);
x_190 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_167, x_189, x_4, x_5, x_6, x_7, x_8, x_9, x_144);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec(x_190);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_192 = x_191;
goto block_204;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_13, 0);
lean_inc(x_205);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_206 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_205, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_191);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
x_192 = x_207;
goto block_204;
}
else
{
uint8_t x_208; 
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
x_208 = !lean_is_exclusive(x_206);
if (x_208 == 0)
{
return x_206;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_206, 0);
x_210 = lean_ctor_get(x_206, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_206);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
block_204:
{
lean_object* x_193; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_193 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_192);
lean_dec(x_17);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
lean_inc(x_2);
x_195 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__6(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_194);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_196 = !lean_is_exclusive(x_195);
if (x_196 == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_195, 0);
lean_dec(x_197);
lean_ctor_set(x_195, 0, x_2);
return x_195;
}
else
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
lean_dec(x_195);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_2);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
else
{
uint8_t x_200; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_200 = !lean_is_exclusive(x_193);
if (x_200 == 0)
{
return x_193;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_193, 0);
x_202 = lean_ctor_get(x_193, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_193);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
}
}
}
else
{
lean_object* x_212; 
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_212 = lean_ctor_get(x_149, 0);
lean_inc(x_212);
lean_dec(x_149);
if (lean_obj_tag(x_212) == 4)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
lean_dec(x_212);
x_214 = lean_st_ref_get(x_9, x_144);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
lean_dec(x_215);
x_218 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_217, x_213);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_1);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_11);
lean_dec(x_2);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
lean_dec(x_218);
x_220 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_220, 0, x_219);
x_221 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_221, 0, x_220);
x_222 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_221, x_4, x_5, x_6, x_7, x_8, x_9, x_216);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_222;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_223 = lean_ctor_get(x_218, 0);
lean_inc(x_223);
lean_dec(x_218);
x_224 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_216);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_226 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_225);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec(x_226);
x_228 = l_Lean_Syntax_getArgs(x_223);
lean_dec(x_223);
x_229 = l_Array_empty___closed__1;
x_230 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_228, x_228, x_131, x_229);
lean_dec(x_228);
x_231 = l_Lean_nullKind___closed__2;
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
x_233 = lean_array_push(x_229, x_232);
x_234 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__5;
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_233);
x_236 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_237 = lean_array_push(x_236, x_235);
x_238 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_239 = lean_array_push(x_237, x_238);
x_240 = l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock___closed__2;
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
x_242 = lean_array_push(x_229, x_241);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_231);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_array_push(x_229, x_243);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_234);
lean_ctor_set(x_245, 1, x_244);
x_246 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_247 = lean_array_push(x_246, x_245);
x_248 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = l_Lean_Syntax_copyInfo(x_249, x_11);
lean_dec(x_11);
x_251 = l_Lean_Expr_getAppNumArgsAux___main(x_128, x_131);
x_252 = lean_nat_sub(x_251, x_131);
lean_dec(x_251);
x_253 = lean_unsigned_to_nat(1u);
x_254 = lean_nat_sub(x_252, x_253);
lean_dec(x_252);
x_255 = l_Lean_Expr_getRevArg_x21___main(x_128, x_254);
lean_dec(x_128);
x_256 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_256, 0, x_250);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_257 = l___private_Lean_Elab_App_2__elabArg(x_2, x_256, x_255, x_4, x_5, x_6, x_7, x_8, x_9, x_227);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
lean_inc(x_258);
x_260 = l_Lean_mkApp(x_2, x_258);
x_261 = lean_expr_instantiate1(x_129, x_258);
lean_dec(x_258);
lean_dec(x_129);
x_2 = x_260;
x_3 = x_261;
x_10 = x_259;
goto _start;
}
else
{
uint8_t x_263; 
lean_dec(x_1);
lean_dec(x_129);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_263 = !lean_is_exclusive(x_257);
if (x_263 == 0)
{
return x_257;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_257, 0);
x_265 = lean_ctor_get(x_257, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_257);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
}
else
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_212);
lean_dec(x_1);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_11);
lean_dec(x_2);
x_267 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_268 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_267, x_4, x_5, x_6, x_7, x_8, x_9, x_144);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_268;
}
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_269 = lean_ctor_get(x_148, 0);
lean_inc(x_269);
lean_dec(x_148);
lean_inc(x_269);
x_270 = l_Lean_mkApp(x_2, x_269);
x_271 = lean_expr_instantiate1(x_129, x_269);
lean_dec(x_269);
lean_dec(x_129);
x_2 = x_270;
x_3 = x_271;
x_10 = x_144;
goto _start;
}
}
else
{
uint8_t x_273; 
lean_dec(x_1);
lean_dec(x_129);
lean_dec(x_128);
x_273 = l_Array_isEmpty___rarg(x_16);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_274 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_274, 0, x_127);
x_275 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_276 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
x_277 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_278 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
x_279 = x_16;
x_280 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_131, x_279);
x_281 = x_280;
x_282 = l_Array_toList___rarg(x_281);
lean_dec(x_281);
x_283 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_282);
x_284 = l_Array_HasRepr___rarg___closed__1;
x_285 = lean_string_append(x_284, x_283);
lean_dec(x_283);
x_286 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_286, 0, x_285);
x_287 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_287, 0, x_286);
x_288 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_288, 0, x_278);
lean_ctor_set(x_288, 1, x_287);
x_289 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_288, x_4, x_5, x_6, x_7, x_8, x_9, x_144);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_289;
}
else
{
lean_object* x_290; uint8_t x_291; 
lean_dec(x_127);
lean_dec(x_16);
x_290 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_291 = l_Lean_checkTraceOption(x_22, x_290);
lean_dec(x_22);
if (x_291 == 0)
{
lean_object* x_292; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_292 = x_144;
goto block_304;
}
else
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_13, 0);
lean_inc(x_305);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_306 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_305, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_144);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; 
x_307 = lean_ctor_get(x_306, 1);
lean_inc(x_307);
lean_dec(x_306);
x_292 = x_307;
goto block_304;
}
else
{
uint8_t x_308; 
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
x_308 = !lean_is_exclusive(x_306);
if (x_308 == 0)
{
return x_306;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_306, 0);
x_310 = lean_ctor_get(x_306, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_306);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
block_304:
{
lean_object* x_293; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_293 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_292);
lean_dec(x_17);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_294 = lean_ctor_get(x_293, 1);
lean_inc(x_294);
lean_dec(x_293);
lean_inc(x_2);
x_295 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__7(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_294);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_296 = !lean_is_exclusive(x_295);
if (x_296 == 0)
{
lean_object* x_297; 
x_297 = lean_ctor_get(x_295, 0);
lean_dec(x_297);
lean_ctor_set(x_295, 0, x_2);
return x_295;
}
else
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_295, 1);
lean_inc(x_298);
lean_dec(x_295);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_2);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
else
{
uint8_t x_300; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_300 = !lean_is_exclusive(x_293);
if (x_300 == 0)
{
return x_293;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_293, 0);
x_302 = lean_ctor_get(x_293, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_293);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_inc(x_2);
x_312 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_312, 0, x_2);
x_313 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_290, x_312, x_4, x_5, x_6, x_7, x_8, x_9, x_144);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec(x_313);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_315 = x_314;
goto block_327;
}
else
{
lean_object* x_328; lean_object* x_329; 
x_328 = lean_ctor_get(x_13, 0);
lean_inc(x_328);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_329 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_328, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_314);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; 
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
lean_dec(x_329);
x_315 = x_330;
goto block_327;
}
else
{
uint8_t x_331; 
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
x_331 = !lean_is_exclusive(x_329);
if (x_331 == 0)
{
return x_329;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_329, 0);
x_333 = lean_ctor_get(x_329, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_329);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
}
block_327:
{
lean_object* x_316; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_316 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_315);
lean_dec(x_17);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
lean_dec(x_316);
lean_inc(x_2);
x_318 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__8(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_317);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_319 = !lean_is_exclusive(x_318);
if (x_319 == 0)
{
lean_object* x_320; 
x_320 = lean_ctor_get(x_318, 0);
lean_dec(x_320);
lean_ctor_set(x_318, 0, x_2);
return x_318;
}
else
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_ctor_get(x_318, 1);
lean_inc(x_321);
lean_dec(x_318);
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_2);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
else
{
uint8_t x_323; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_323 = !lean_is_exclusive(x_316);
if (x_323 == 0)
{
return x_316;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_316, 0);
x_325 = lean_ctor_get(x_316, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_316);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
}
}
}
}
}
}
else
{
lean_object* x_335; lean_object* x_336; 
lean_dec(x_1);
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_3);
x_335 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_336 = l___private_Lean_Elab_App_2__elabArg(x_2, x_335, x_128, x_4, x_5, x_6, x_7, x_8, x_9, x_144);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec(x_336);
x_339 = lean_unsigned_to_nat(1u);
x_340 = lean_nat_add(x_15, x_339);
lean_dec(x_15);
x_341 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_341, 0, x_11);
lean_ctor_set(x_341, 1, x_12);
lean_ctor_set(x_341, 2, x_13);
lean_ctor_set(x_341, 3, x_340);
lean_ctor_set(x_341, 4, x_16);
lean_ctor_set(x_341, 5, x_17);
lean_ctor_set(x_341, 6, x_18);
lean_ctor_set(x_341, 7, x_19);
lean_ctor_set_uint8(x_341, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_341, sizeof(void*)*8 + 1, x_145);
lean_inc(x_337);
x_342 = l_Lean_mkApp(x_2, x_337);
x_343 = lean_expr_instantiate1(x_129, x_337);
lean_dec(x_337);
lean_dec(x_129);
x_1 = x_341;
x_2 = x_342;
x_3 = x_343;
x_10 = x_338;
goto _start;
}
else
{
uint8_t x_345; 
lean_dec(x_129);
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
x_345 = !lean_is_exclusive(x_336);
if (x_345 == 0)
{
return x_336;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_336, 0);
x_347 = lean_ctor_get(x_336, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_336);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
}
}
else
{
uint8_t x_349; 
lean_free_object(x_1);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
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
x_349 = !lean_is_exclusive(x_134);
if (x_349 == 0)
{
return x_134;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_134, 0);
x_351 = lean_ctor_get(x_134, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_134);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
return x_352;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_353; uint8_t x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_353 = lean_ctor_get(x_134, 1);
lean_inc(x_353);
lean_dec(x_134);
x_354 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_355 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_355, 0, x_11);
lean_ctor_set(x_355, 1, x_12);
lean_ctor_set(x_355, 2, x_13);
lean_ctor_set(x_355, 3, x_15);
lean_ctor_set(x_355, 4, x_16);
lean_ctor_set(x_355, 5, x_17);
lean_ctor_set(x_355, 6, x_18);
lean_ctor_set(x_355, 7, x_19);
lean_ctor_set_uint8(x_355, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_355, sizeof(void*)*8 + 1, x_354);
x_356 = lean_array_get_size(x_12);
x_357 = lean_nat_dec_lt(x_15, x_356);
lean_dec(x_356);
if (x_357 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_358; 
x_358 = l_Lean_Expr_getOptParamDefault_x3f(x_128);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; 
x_359 = l_Lean_Expr_getAutoParamTactic_x3f(x_128);
if (lean_obj_tag(x_359) == 0)
{
uint8_t x_360; 
lean_dec(x_355);
lean_dec(x_129);
lean_dec(x_128);
x_360 = l_Array_isEmpty___rarg(x_16);
if (x_360 == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_361 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_361, 0, x_127);
x_362 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_363 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_361);
x_364 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_365 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
x_366 = x_16;
x_367 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_131, x_366);
x_368 = x_367;
x_369 = l_Array_toList___rarg(x_368);
lean_dec(x_368);
x_370 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_369);
x_371 = l_Array_HasRepr___rarg___closed__1;
x_372 = lean_string_append(x_371, x_370);
lean_dec(x_370);
x_373 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_373, 0, x_372);
x_374 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_374, 0, x_373);
x_375 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_375, 0, x_365);
lean_ctor_set(x_375, 1, x_374);
x_376 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_375, x_4, x_5, x_6, x_7, x_8, x_9, x_353);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_376;
}
else
{
lean_object* x_377; uint8_t x_378; 
lean_dec(x_127);
lean_dec(x_16);
x_377 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_378 = l_Lean_checkTraceOption(x_22, x_377);
lean_dec(x_22);
if (x_378 == 0)
{
lean_object* x_379; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_379 = x_353;
goto block_390;
}
else
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_ctor_get(x_13, 0);
lean_inc(x_391);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_392 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_391, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_353);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; 
x_393 = lean_ctor_get(x_392, 1);
lean_inc(x_393);
lean_dec(x_392);
x_379 = x_393;
goto block_390;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
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
x_394 = lean_ctor_get(x_392, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_392, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_392)) {
 lean_ctor_release(x_392, 0);
 lean_ctor_release(x_392, 1);
 x_396 = x_392;
} else {
 lean_dec_ref(x_392);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 2, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_394);
lean_ctor_set(x_397, 1, x_395);
return x_397;
}
}
block_390:
{
lean_object* x_380; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_380 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_379);
lean_dec(x_17);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
lean_dec(x_380);
lean_inc(x_2);
x_382 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__5(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_381);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_384 = x_382;
} else {
 lean_dec_ref(x_382);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_2);
lean_ctor_set(x_385, 1, x_383);
return x_385;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_386 = lean_ctor_get(x_380, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_380, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_388 = x_380;
} else {
 lean_dec_ref(x_380);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(1, 2, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_387);
return x_389;
}
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_inc(x_2);
x_398 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_398, 0, x_2);
x_399 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_377, x_398, x_4, x_5, x_6, x_7, x_8, x_9, x_353);
x_400 = lean_ctor_get(x_399, 1);
lean_inc(x_400);
lean_dec(x_399);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_401 = x_400;
goto block_412;
}
else
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_ctor_get(x_13, 0);
lean_inc(x_413);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_414 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_413, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_400);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; 
x_415 = lean_ctor_get(x_414, 1);
lean_inc(x_415);
lean_dec(x_414);
x_401 = x_415;
goto block_412;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
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
x_416 = lean_ctor_get(x_414, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_414, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_418 = x_414;
} else {
 lean_dec_ref(x_414);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(1, 2, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_416);
lean_ctor_set(x_419, 1, x_417);
return x_419;
}
}
block_412:
{
lean_object* x_402; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_402 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_401);
lean_dec(x_17);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_403 = lean_ctor_get(x_402, 1);
lean_inc(x_403);
lean_dec(x_402);
lean_inc(x_2);
x_404 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__6(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_403);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_405 = lean_ctor_get(x_404, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_406 = x_404;
} else {
 lean_dec_ref(x_404);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_2);
lean_ctor_set(x_407, 1, x_405);
return x_407;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_408 = lean_ctor_get(x_402, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_402, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 x_410 = x_402;
} else {
 lean_dec_ref(x_402);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(1, 2, 0);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_408);
lean_ctor_set(x_411, 1, x_409);
return x_411;
}
}
}
}
}
else
{
lean_object* x_420; 
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_420 = lean_ctor_get(x_359, 0);
lean_inc(x_420);
lean_dec(x_359);
if (lean_obj_tag(x_420) == 4)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
lean_dec(x_420);
x_422 = lean_st_ref_get(x_9, x_353);
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
lean_dec(x_422);
x_425 = lean_ctor_get(x_423, 0);
lean_inc(x_425);
lean_dec(x_423);
x_426 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_425, x_421);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
lean_dec(x_355);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_11);
lean_dec(x_2);
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
lean_dec(x_426);
x_428 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_428, 0, x_427);
x_429 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_429, 0, x_428);
x_430 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_429, x_4, x_5, x_6, x_7, x_8, x_9, x_424);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_430;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_431 = lean_ctor_get(x_426, 0);
lean_inc(x_431);
lean_dec(x_426);
x_432 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_424);
x_433 = lean_ctor_get(x_432, 1);
lean_inc(x_433);
lean_dec(x_432);
x_434 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_433);
x_435 = lean_ctor_get(x_434, 1);
lean_inc(x_435);
lean_dec(x_434);
x_436 = l_Lean_Syntax_getArgs(x_431);
lean_dec(x_431);
x_437 = l_Array_empty___closed__1;
x_438 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_436, x_436, x_131, x_437);
lean_dec(x_436);
x_439 = l_Lean_nullKind___closed__2;
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_438);
x_441 = lean_array_push(x_437, x_440);
x_442 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__5;
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_441);
x_444 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_445 = lean_array_push(x_444, x_443);
x_446 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_447 = lean_array_push(x_445, x_446);
x_448 = l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock___closed__2;
x_449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_447);
x_450 = lean_array_push(x_437, x_449);
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_439);
lean_ctor_set(x_451, 1, x_450);
x_452 = lean_array_push(x_437, x_451);
x_453 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_453, 0, x_442);
lean_ctor_set(x_453, 1, x_452);
x_454 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_455 = lean_array_push(x_454, x_453);
x_456 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_457 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_457, 0, x_456);
lean_ctor_set(x_457, 1, x_455);
x_458 = l_Lean_Syntax_copyInfo(x_457, x_11);
lean_dec(x_11);
x_459 = l_Lean_Expr_getAppNumArgsAux___main(x_128, x_131);
x_460 = lean_nat_sub(x_459, x_131);
lean_dec(x_459);
x_461 = lean_unsigned_to_nat(1u);
x_462 = lean_nat_sub(x_460, x_461);
lean_dec(x_460);
x_463 = l_Lean_Expr_getRevArg_x21___main(x_128, x_462);
lean_dec(x_128);
x_464 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_464, 0, x_458);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_465 = l___private_Lean_Elab_App_2__elabArg(x_2, x_464, x_463, x_4, x_5, x_6, x_7, x_8, x_9, x_435);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
lean_inc(x_466);
x_468 = l_Lean_mkApp(x_2, x_466);
x_469 = lean_expr_instantiate1(x_129, x_466);
lean_dec(x_466);
lean_dec(x_129);
x_1 = x_355;
x_2 = x_468;
x_3 = x_469;
x_10 = x_467;
goto _start;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_355);
lean_dec(x_129);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_471 = lean_ctor_get(x_465, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_465, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_473 = x_465;
} else {
 lean_dec_ref(x_465);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 2, 0);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_471);
lean_ctor_set(x_474, 1, x_472);
return x_474;
}
}
}
else
{
lean_object* x_475; lean_object* x_476; 
lean_dec(x_420);
lean_dec(x_355);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_11);
lean_dec(x_2);
x_475 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_476 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_475, x_4, x_5, x_6, x_7, x_8, x_9, x_353);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_476;
}
}
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_477 = lean_ctor_get(x_358, 0);
lean_inc(x_477);
lean_dec(x_358);
lean_inc(x_477);
x_478 = l_Lean_mkApp(x_2, x_477);
x_479 = lean_expr_instantiate1(x_129, x_477);
lean_dec(x_477);
lean_dec(x_129);
x_1 = x_355;
x_2 = x_478;
x_3 = x_479;
x_10 = x_353;
goto _start;
}
}
else
{
uint8_t x_481; 
lean_dec(x_355);
lean_dec(x_129);
lean_dec(x_128);
x_481 = l_Array_isEmpty___rarg(x_16);
if (x_481 == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_482 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_482, 0, x_127);
x_483 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_484 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_482);
x_485 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_486 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
x_487 = x_16;
x_488 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_131, x_487);
x_489 = x_488;
x_490 = l_Array_toList___rarg(x_489);
lean_dec(x_489);
x_491 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_490);
x_492 = l_Array_HasRepr___rarg___closed__1;
x_493 = lean_string_append(x_492, x_491);
lean_dec(x_491);
x_494 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_494, 0, x_493);
x_495 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_495, 0, x_494);
x_496 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_496, 0, x_486);
lean_ctor_set(x_496, 1, x_495);
x_497 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_496, x_4, x_5, x_6, x_7, x_8, x_9, x_353);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_497;
}
else
{
lean_object* x_498; uint8_t x_499; 
lean_dec(x_127);
lean_dec(x_16);
x_498 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_499 = l_Lean_checkTraceOption(x_22, x_498);
lean_dec(x_22);
if (x_499 == 0)
{
lean_object* x_500; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_500 = x_353;
goto block_511;
}
else
{
lean_object* x_512; lean_object* x_513; 
x_512 = lean_ctor_get(x_13, 0);
lean_inc(x_512);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_513 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_512, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_353);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; 
x_514 = lean_ctor_get(x_513, 1);
lean_inc(x_514);
lean_dec(x_513);
x_500 = x_514;
goto block_511;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
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
x_515 = lean_ctor_get(x_513, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_513, 1);
lean_inc(x_516);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_517 = x_513;
} else {
 lean_dec_ref(x_513);
 x_517 = lean_box(0);
}
if (lean_is_scalar(x_517)) {
 x_518 = lean_alloc_ctor(1, 2, 0);
} else {
 x_518 = x_517;
}
lean_ctor_set(x_518, 0, x_515);
lean_ctor_set(x_518, 1, x_516);
return x_518;
}
}
block_511:
{
lean_object* x_501; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_501 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_500);
lean_dec(x_17);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_502 = lean_ctor_get(x_501, 1);
lean_inc(x_502);
lean_dec(x_501);
lean_inc(x_2);
x_503 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__7(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_502);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_504 = lean_ctor_get(x_503, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 lean_ctor_release(x_503, 1);
 x_505 = x_503;
} else {
 lean_dec_ref(x_503);
 x_505 = lean_box(0);
}
if (lean_is_scalar(x_505)) {
 x_506 = lean_alloc_ctor(0, 2, 0);
} else {
 x_506 = x_505;
}
lean_ctor_set(x_506, 0, x_2);
lean_ctor_set(x_506, 1, x_504);
return x_506;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_507 = lean_ctor_get(x_501, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_501, 1);
lean_inc(x_508);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_509 = x_501;
} else {
 lean_dec_ref(x_501);
 x_509 = lean_box(0);
}
if (lean_is_scalar(x_509)) {
 x_510 = lean_alloc_ctor(1, 2, 0);
} else {
 x_510 = x_509;
}
lean_ctor_set(x_510, 0, x_507);
lean_ctor_set(x_510, 1, x_508);
return x_510;
}
}
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_inc(x_2);
x_519 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_519, 0, x_2);
x_520 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_498, x_519, x_4, x_5, x_6, x_7, x_8, x_9, x_353);
x_521 = lean_ctor_get(x_520, 1);
lean_inc(x_521);
lean_dec(x_520);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_522 = x_521;
goto block_533;
}
else
{
lean_object* x_534; lean_object* x_535; 
x_534 = lean_ctor_get(x_13, 0);
lean_inc(x_534);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_535 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_534, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_521);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; 
x_536 = lean_ctor_get(x_535, 1);
lean_inc(x_536);
lean_dec(x_535);
x_522 = x_536;
goto block_533;
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
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
x_537 = lean_ctor_get(x_535, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_535, 1);
lean_inc(x_538);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_539 = x_535;
} else {
 lean_dec_ref(x_535);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 2, 0);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_537);
lean_ctor_set(x_540, 1, x_538);
return x_540;
}
}
block_533:
{
lean_object* x_523; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_523 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_522);
lean_dec(x_17);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_524 = lean_ctor_get(x_523, 1);
lean_inc(x_524);
lean_dec(x_523);
lean_inc(x_2);
x_525 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__8(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_524);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_526 = lean_ctor_get(x_525, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 lean_ctor_release(x_525, 1);
 x_527 = x_525;
} else {
 lean_dec_ref(x_525);
 x_527 = lean_box(0);
}
if (lean_is_scalar(x_527)) {
 x_528 = lean_alloc_ctor(0, 2, 0);
} else {
 x_528 = x_527;
}
lean_ctor_set(x_528, 0, x_2);
lean_ctor_set(x_528, 1, x_526);
return x_528;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_529 = lean_ctor_get(x_523, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_523, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 x_531 = x_523;
} else {
 lean_dec_ref(x_523);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_531)) {
 x_532 = lean_alloc_ctor(1, 2, 0);
} else {
 x_532 = x_531;
}
lean_ctor_set(x_532, 0, x_529);
lean_ctor_set(x_532, 1, x_530);
return x_532;
}
}
}
}
}
}
else
{
lean_object* x_541; lean_object* x_542; 
lean_dec(x_355);
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_3);
x_541 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_542 = l___private_Lean_Elab_App_2__elabArg(x_2, x_541, x_128, x_4, x_5, x_6, x_7, x_8, x_9, x_353);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_542, 1);
lean_inc(x_544);
lean_dec(x_542);
x_545 = lean_unsigned_to_nat(1u);
x_546 = lean_nat_add(x_15, x_545);
lean_dec(x_15);
x_547 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_547, 0, x_11);
lean_ctor_set(x_547, 1, x_12);
lean_ctor_set(x_547, 2, x_13);
lean_ctor_set(x_547, 3, x_546);
lean_ctor_set(x_547, 4, x_16);
lean_ctor_set(x_547, 5, x_17);
lean_ctor_set(x_547, 6, x_18);
lean_ctor_set(x_547, 7, x_19);
lean_ctor_set_uint8(x_547, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_547, sizeof(void*)*8 + 1, x_354);
lean_inc(x_543);
x_548 = l_Lean_mkApp(x_2, x_543);
x_549 = lean_expr_instantiate1(x_129, x_543);
lean_dec(x_543);
lean_dec(x_129);
x_1 = x_547;
x_2 = x_548;
x_3 = x_549;
x_10 = x_544;
goto _start;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
lean_dec(x_129);
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
x_551 = lean_ctor_get(x_542, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_542, 1);
lean_inc(x_552);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 lean_ctor_release(x_542, 1);
 x_553 = x_542;
} else {
 lean_dec_ref(x_542);
 x_553 = lean_box(0);
}
if (lean_is_scalar(x_553)) {
 x_554 = lean_alloc_ctor(1, 2, 0);
} else {
 x_554 = x_553;
}
lean_ctor_set(x_554, 0, x_551);
lean_ctor_set(x_554, 1, x_552);
return x_554;
}
}
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
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
x_555 = lean_ctor_get(x_134, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_134, 1);
lean_inc(x_556);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_557 = x_134;
} else {
 lean_dec_ref(x_134);
 x_557 = lean_box(0);
}
if (lean_is_scalar(x_557)) {
 x_558 = lean_alloc_ctor(1, 2, 0);
} else {
 x_558 = x_557;
}
lean_ctor_set(x_558, 0, x_555);
lean_ctor_set(x_558, 1, x_556);
return x_558;
}
}
}
case 1:
{
if (x_14 == 0)
{
lean_object* x_559; lean_object* x_560; uint8_t x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_575; 
lean_dec(x_127);
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
 x_559 = x_1;
} else {
 lean_dec_ref(x_1);
 x_559 = lean_box(0);
}
x_560 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_560, 0, x_128);
x_561 = 0;
x_562 = lean_box(0);
lean_inc(x_6);
x_563 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_560, x_561, x_562, x_6, x_7, x_8, x_9, x_29);
x_564 = lean_ctor_get(x_563, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_563, 1);
lean_inc(x_565);
lean_dec(x_563);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_564);
x_575 = l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__9(x_564, x_4, x_5, x_6, x_7, x_8, x_9, x_565);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; uint8_t x_577; 
x_576 = lean_ctor_get(x_575, 0);
lean_inc(x_576);
x_577 = lean_unbox(x_576);
lean_dec(x_576);
if (x_577 == 0)
{
lean_object* x_578; 
x_578 = lean_ctor_get(x_575, 1);
lean_inc(x_578);
lean_dec(x_575);
x_566 = x_18;
x_567 = x_578;
goto block_574;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_579 = lean_ctor_get(x_575, 1);
lean_inc(x_579);
lean_dec(x_575);
x_580 = l_Lean_Expr_mvarId_x21(x_564);
x_581 = lean_array_push(x_18, x_580);
x_566 = x_581;
x_567 = x_579;
goto block_574;
}
}
else
{
uint8_t x_582; 
lean_dec(x_564);
lean_dec(x_559);
lean_dec(x_129);
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
x_582 = !lean_is_exclusive(x_575);
if (x_582 == 0)
{
return x_575;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_575, 0);
x_584 = lean_ctor_get(x_575, 1);
lean_inc(x_584);
lean_inc(x_583);
lean_dec(x_575);
x_585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set(x_585, 1, x_584);
return x_585;
}
}
block_574:
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_568 = l_Lean_Expr_mvarId_x21(x_564);
x_569 = lean_array_push(x_19, x_568);
if (lean_is_scalar(x_559)) {
 x_570 = lean_alloc_ctor(0, 8, 2);
} else {
 x_570 = x_559;
}
lean_ctor_set(x_570, 0, x_11);
lean_ctor_set(x_570, 1, x_12);
lean_ctor_set(x_570, 2, x_13);
lean_ctor_set(x_570, 3, x_15);
lean_ctor_set(x_570, 4, x_16);
lean_ctor_set(x_570, 5, x_17);
lean_ctor_set(x_570, 6, x_566);
lean_ctor_set(x_570, 7, x_569);
lean_ctor_set_uint8(x_570, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_570, sizeof(void*)*8 + 1, x_21);
lean_inc(x_564);
x_571 = l_Lean_mkApp(x_2, x_564);
x_572 = lean_expr_instantiate1(x_129, x_564);
lean_dec(x_564);
lean_dec(x_129);
x_1 = x_570;
x_2 = x_571;
x_3 = x_572;
x_10 = x_567;
goto _start;
}
}
else
{
lean_object* x_586; uint8_t x_587; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_586 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_587 = !lean_is_exclusive(x_1);
if (x_587 == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_588 = lean_ctor_get(x_1, 7);
lean_dec(x_588);
x_589 = lean_ctor_get(x_1, 6);
lean_dec(x_589);
x_590 = lean_ctor_get(x_1, 5);
lean_dec(x_590);
x_591 = lean_ctor_get(x_1, 4);
lean_dec(x_591);
x_592 = lean_ctor_get(x_1, 3);
lean_dec(x_592);
x_593 = lean_ctor_get(x_1, 2);
lean_dec(x_593);
x_594 = lean_ctor_get(x_1, 1);
lean_dec(x_594);
x_595 = lean_ctor_get(x_1, 0);
lean_dec(x_595);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_596; lean_object* x_597; uint8_t x_598; 
x_596 = lean_ctor_get(x_586, 1);
lean_inc(x_596);
lean_dec(x_586);
x_597 = lean_array_get_size(x_12);
x_598 = lean_nat_dec_lt(x_15, x_597);
lean_dec(x_597);
if (x_598 == 0)
{
uint8_t x_599; 
lean_free_object(x_1);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_599 = l_Array_isEmpty___rarg(x_16);
if (x_599 == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_600 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_600, 0, x_127);
x_601 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_602 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_602, 0, x_601);
lean_ctor_set(x_602, 1, x_600);
x_603 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_604 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_603);
x_605 = x_16;
x_606 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_131, x_605);
x_607 = x_606;
x_608 = l_Array_toList___rarg(x_607);
lean_dec(x_607);
x_609 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_608);
x_610 = l_Array_HasRepr___rarg___closed__1;
x_611 = lean_string_append(x_610, x_609);
lean_dec(x_609);
x_612 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_612, 0, x_611);
x_613 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_613, 0, x_612);
x_614 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_614, 0, x_604);
lean_ctor_set(x_614, 1, x_613);
x_615 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_614, x_4, x_5, x_6, x_7, x_8, x_9, x_596);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_615;
}
else
{
lean_object* x_616; uint8_t x_617; 
lean_dec(x_127);
lean_dec(x_16);
x_616 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_617 = l_Lean_checkTraceOption(x_22, x_616);
lean_dec(x_22);
if (x_617 == 0)
{
lean_object* x_618; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_618 = x_596;
goto block_630;
}
else
{
lean_object* x_631; lean_object* x_632; 
x_631 = lean_ctor_get(x_13, 0);
lean_inc(x_631);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_632 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_631, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_596);
if (lean_obj_tag(x_632) == 0)
{
lean_object* x_633; 
x_633 = lean_ctor_get(x_632, 1);
lean_inc(x_633);
lean_dec(x_632);
x_618 = x_633;
goto block_630;
}
else
{
uint8_t x_634; 
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
x_634 = !lean_is_exclusive(x_632);
if (x_634 == 0)
{
return x_632;
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_635 = lean_ctor_get(x_632, 0);
x_636 = lean_ctor_get(x_632, 1);
lean_inc(x_636);
lean_inc(x_635);
lean_dec(x_632);
x_637 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_637, 0, x_635);
lean_ctor_set(x_637, 1, x_636);
return x_637;
}
}
}
block_630:
{
lean_object* x_619; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_619 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_618);
lean_dec(x_17);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; lean_object* x_621; uint8_t x_622; 
x_620 = lean_ctor_get(x_619, 1);
lean_inc(x_620);
lean_dec(x_619);
lean_inc(x_2);
x_621 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__10(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_620);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_622 = !lean_is_exclusive(x_621);
if (x_622 == 0)
{
lean_object* x_623; 
x_623 = lean_ctor_get(x_621, 0);
lean_dec(x_623);
lean_ctor_set(x_621, 0, x_2);
return x_621;
}
else
{
lean_object* x_624; lean_object* x_625; 
x_624 = lean_ctor_get(x_621, 1);
lean_inc(x_624);
lean_dec(x_621);
x_625 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_625, 0, x_2);
lean_ctor_set(x_625, 1, x_624);
return x_625;
}
}
else
{
uint8_t x_626; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_626 = !lean_is_exclusive(x_619);
if (x_626 == 0)
{
return x_619;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_627 = lean_ctor_get(x_619, 0);
x_628 = lean_ctor_get(x_619, 1);
lean_inc(x_628);
lean_inc(x_627);
lean_dec(x_619);
x_629 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_629, 0, x_627);
lean_ctor_set(x_629, 1, x_628);
return x_629;
}
}
}
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
lean_inc(x_2);
x_638 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_638, 0, x_2);
x_639 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_616, x_638, x_4, x_5, x_6, x_7, x_8, x_9, x_596);
x_640 = lean_ctor_get(x_639, 1);
lean_inc(x_640);
lean_dec(x_639);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_641 = x_640;
goto block_653;
}
else
{
lean_object* x_654; lean_object* x_655; 
x_654 = lean_ctor_get(x_13, 0);
lean_inc(x_654);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_655 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_654, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_640);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; 
x_656 = lean_ctor_get(x_655, 1);
lean_inc(x_656);
lean_dec(x_655);
x_641 = x_656;
goto block_653;
}
else
{
uint8_t x_657; 
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
x_657 = !lean_is_exclusive(x_655);
if (x_657 == 0)
{
return x_655;
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_658 = lean_ctor_get(x_655, 0);
x_659 = lean_ctor_get(x_655, 1);
lean_inc(x_659);
lean_inc(x_658);
lean_dec(x_655);
x_660 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_660, 0, x_658);
lean_ctor_set(x_660, 1, x_659);
return x_660;
}
}
}
block_653:
{
lean_object* x_642; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_642 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_641);
lean_dec(x_17);
if (lean_obj_tag(x_642) == 0)
{
lean_object* x_643; lean_object* x_644; uint8_t x_645; 
x_643 = lean_ctor_get(x_642, 1);
lean_inc(x_643);
lean_dec(x_642);
lean_inc(x_2);
x_644 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__11(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_643);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_645 = !lean_is_exclusive(x_644);
if (x_645 == 0)
{
lean_object* x_646; 
x_646 = lean_ctor_get(x_644, 0);
lean_dec(x_646);
lean_ctor_set(x_644, 0, x_2);
return x_644;
}
else
{
lean_object* x_647; lean_object* x_648; 
x_647 = lean_ctor_get(x_644, 1);
lean_inc(x_647);
lean_dec(x_644);
x_648 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_648, 0, x_2);
lean_ctor_set(x_648, 1, x_647);
return x_648;
}
}
else
{
uint8_t x_649; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_649 = !lean_is_exclusive(x_642);
if (x_649 == 0)
{
return x_642;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_650 = lean_ctor_get(x_642, 0);
x_651 = lean_ctor_get(x_642, 1);
lean_inc(x_651);
lean_inc(x_650);
lean_dec(x_642);
x_652 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_652, 0, x_650);
lean_ctor_set(x_652, 1, x_651);
return x_652;
}
}
}
}
}
}
else
{
lean_object* x_661; lean_object* x_662; 
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_3);
x_661 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_662 = l___private_Lean_Elab_App_2__elabArg(x_2, x_661, x_128, x_4, x_5, x_6, x_7, x_8, x_9, x_596);
if (lean_obj_tag(x_662) == 0)
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; uint8_t x_667; lean_object* x_668; lean_object* x_669; 
x_663 = lean_ctor_get(x_662, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_662, 1);
lean_inc(x_664);
lean_dec(x_662);
x_665 = lean_unsigned_to_nat(1u);
x_666 = lean_nat_add(x_15, x_665);
lean_dec(x_15);
x_667 = 1;
lean_ctor_set(x_1, 3, x_666);
lean_ctor_set_uint8(x_1, sizeof(void*)*8 + 1, x_667);
lean_inc(x_663);
x_668 = l_Lean_mkApp(x_2, x_663);
x_669 = lean_expr_instantiate1(x_129, x_663);
lean_dec(x_663);
lean_dec(x_129);
x_2 = x_668;
x_3 = x_669;
x_10 = x_664;
goto _start;
}
else
{
uint8_t x_671; 
lean_free_object(x_1);
lean_dec(x_129);
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
x_671 = !lean_is_exclusive(x_662);
if (x_671 == 0)
{
return x_662;
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_672 = lean_ctor_get(x_662, 0);
x_673 = lean_ctor_get(x_662, 1);
lean_inc(x_673);
lean_inc(x_672);
lean_dec(x_662);
x_674 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_674, 0, x_672);
lean_ctor_set(x_674, 1, x_673);
return x_674;
}
}
}
}
else
{
uint8_t x_675; 
lean_free_object(x_1);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
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
x_675 = !lean_is_exclusive(x_586);
if (x_675 == 0)
{
return x_586;
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_676 = lean_ctor_get(x_586, 0);
x_677 = lean_ctor_get(x_586, 1);
lean_inc(x_677);
lean_inc(x_676);
lean_dec(x_586);
x_678 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_678, 0, x_676);
lean_ctor_set(x_678, 1, x_677);
return x_678;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_679; lean_object* x_680; uint8_t x_681; 
x_679 = lean_ctor_get(x_586, 1);
lean_inc(x_679);
lean_dec(x_586);
x_680 = lean_array_get_size(x_12);
x_681 = lean_nat_dec_lt(x_15, x_680);
lean_dec(x_680);
if (x_681 == 0)
{
uint8_t x_682; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_682 = l_Array_isEmpty___rarg(x_16);
if (x_682 == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_683 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_683, 0, x_127);
x_684 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_685 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_685, 0, x_684);
lean_ctor_set(x_685, 1, x_683);
x_686 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_687 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_687, 0, x_685);
lean_ctor_set(x_687, 1, x_686);
x_688 = x_16;
x_689 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_131, x_688);
x_690 = x_689;
x_691 = l_Array_toList___rarg(x_690);
lean_dec(x_690);
x_692 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_691);
x_693 = l_Array_HasRepr___rarg___closed__1;
x_694 = lean_string_append(x_693, x_692);
lean_dec(x_692);
x_695 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_695, 0, x_694);
x_696 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_696, 0, x_695);
x_697 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_697, 0, x_687);
lean_ctor_set(x_697, 1, x_696);
x_698 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_697, x_4, x_5, x_6, x_7, x_8, x_9, x_679);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_698;
}
else
{
lean_object* x_699; uint8_t x_700; 
lean_dec(x_127);
lean_dec(x_16);
x_699 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_700 = l_Lean_checkTraceOption(x_22, x_699);
lean_dec(x_22);
if (x_700 == 0)
{
lean_object* x_701; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_701 = x_679;
goto block_712;
}
else
{
lean_object* x_713; lean_object* x_714; 
x_713 = lean_ctor_get(x_13, 0);
lean_inc(x_713);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_714 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_713, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_679);
if (lean_obj_tag(x_714) == 0)
{
lean_object* x_715; 
x_715 = lean_ctor_get(x_714, 1);
lean_inc(x_715);
lean_dec(x_714);
x_701 = x_715;
goto block_712;
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
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
x_716 = lean_ctor_get(x_714, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_714, 1);
lean_inc(x_717);
if (lean_is_exclusive(x_714)) {
 lean_ctor_release(x_714, 0);
 lean_ctor_release(x_714, 1);
 x_718 = x_714;
} else {
 lean_dec_ref(x_714);
 x_718 = lean_box(0);
}
if (lean_is_scalar(x_718)) {
 x_719 = lean_alloc_ctor(1, 2, 0);
} else {
 x_719 = x_718;
}
lean_ctor_set(x_719, 0, x_716);
lean_ctor_set(x_719, 1, x_717);
return x_719;
}
}
block_712:
{
lean_object* x_702; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_702 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_701);
lean_dec(x_17);
if (lean_obj_tag(x_702) == 0)
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_703 = lean_ctor_get(x_702, 1);
lean_inc(x_703);
lean_dec(x_702);
lean_inc(x_2);
x_704 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__10(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_703);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_705 = lean_ctor_get(x_704, 1);
lean_inc(x_705);
if (lean_is_exclusive(x_704)) {
 lean_ctor_release(x_704, 0);
 lean_ctor_release(x_704, 1);
 x_706 = x_704;
} else {
 lean_dec_ref(x_704);
 x_706 = lean_box(0);
}
if (lean_is_scalar(x_706)) {
 x_707 = lean_alloc_ctor(0, 2, 0);
} else {
 x_707 = x_706;
}
lean_ctor_set(x_707, 0, x_2);
lean_ctor_set(x_707, 1, x_705);
return x_707;
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_708 = lean_ctor_get(x_702, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_702, 1);
lean_inc(x_709);
if (lean_is_exclusive(x_702)) {
 lean_ctor_release(x_702, 0);
 lean_ctor_release(x_702, 1);
 x_710 = x_702;
} else {
 lean_dec_ref(x_702);
 x_710 = lean_box(0);
}
if (lean_is_scalar(x_710)) {
 x_711 = lean_alloc_ctor(1, 2, 0);
} else {
 x_711 = x_710;
}
lean_ctor_set(x_711, 0, x_708);
lean_ctor_set(x_711, 1, x_709);
return x_711;
}
}
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; 
lean_inc(x_2);
x_720 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_720, 0, x_2);
x_721 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_699, x_720, x_4, x_5, x_6, x_7, x_8, x_9, x_679);
x_722 = lean_ctor_get(x_721, 1);
lean_inc(x_722);
lean_dec(x_721);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_723 = x_722;
goto block_734;
}
else
{
lean_object* x_735; lean_object* x_736; 
x_735 = lean_ctor_get(x_13, 0);
lean_inc(x_735);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_736 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_735, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_722);
if (lean_obj_tag(x_736) == 0)
{
lean_object* x_737; 
x_737 = lean_ctor_get(x_736, 1);
lean_inc(x_737);
lean_dec(x_736);
x_723 = x_737;
goto block_734;
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; 
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
x_738 = lean_ctor_get(x_736, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_736, 1);
lean_inc(x_739);
if (lean_is_exclusive(x_736)) {
 lean_ctor_release(x_736, 0);
 lean_ctor_release(x_736, 1);
 x_740 = x_736;
} else {
 lean_dec_ref(x_736);
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
block_734:
{
lean_object* x_724; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_724 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_723);
lean_dec(x_17);
if (lean_obj_tag(x_724) == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
x_725 = lean_ctor_get(x_724, 1);
lean_inc(x_725);
lean_dec(x_724);
lean_inc(x_2);
x_726 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__11(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_725);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_727 = lean_ctor_get(x_726, 1);
lean_inc(x_727);
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 lean_ctor_release(x_726, 1);
 x_728 = x_726;
} else {
 lean_dec_ref(x_726);
 x_728 = lean_box(0);
}
if (lean_is_scalar(x_728)) {
 x_729 = lean_alloc_ctor(0, 2, 0);
} else {
 x_729 = x_728;
}
lean_ctor_set(x_729, 0, x_2);
lean_ctor_set(x_729, 1, x_727);
return x_729;
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_730 = lean_ctor_get(x_724, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_724, 1);
lean_inc(x_731);
if (lean_is_exclusive(x_724)) {
 lean_ctor_release(x_724, 0);
 lean_ctor_release(x_724, 1);
 x_732 = x_724;
} else {
 lean_dec_ref(x_724);
 x_732 = lean_box(0);
}
if (lean_is_scalar(x_732)) {
 x_733 = lean_alloc_ctor(1, 2, 0);
} else {
 x_733 = x_732;
}
lean_ctor_set(x_733, 0, x_730);
lean_ctor_set(x_733, 1, x_731);
return x_733;
}
}
}
}
}
else
{
lean_object* x_742; lean_object* x_743; 
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_3);
x_742 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_743 = l___private_Lean_Elab_App_2__elabArg(x_2, x_742, x_128, x_4, x_5, x_6, x_7, x_8, x_9, x_679);
if (lean_obj_tag(x_743) == 0)
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; uint8_t x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
x_744 = lean_ctor_get(x_743, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_743, 1);
lean_inc(x_745);
lean_dec(x_743);
x_746 = lean_unsigned_to_nat(1u);
x_747 = lean_nat_add(x_15, x_746);
lean_dec(x_15);
x_748 = 1;
x_749 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_749, 0, x_11);
lean_ctor_set(x_749, 1, x_12);
lean_ctor_set(x_749, 2, x_13);
lean_ctor_set(x_749, 3, x_747);
lean_ctor_set(x_749, 4, x_16);
lean_ctor_set(x_749, 5, x_17);
lean_ctor_set(x_749, 6, x_18);
lean_ctor_set(x_749, 7, x_19);
lean_ctor_set_uint8(x_749, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_749, sizeof(void*)*8 + 1, x_748);
lean_inc(x_744);
x_750 = l_Lean_mkApp(x_2, x_744);
x_751 = lean_expr_instantiate1(x_129, x_744);
lean_dec(x_744);
lean_dec(x_129);
x_1 = x_749;
x_2 = x_750;
x_3 = x_751;
x_10 = x_745;
goto _start;
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; 
lean_dec(x_129);
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
x_753 = lean_ctor_get(x_743, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_743, 1);
lean_inc(x_754);
if (lean_is_exclusive(x_743)) {
 lean_ctor_release(x_743, 0);
 lean_ctor_release(x_743, 1);
 x_755 = x_743;
} else {
 lean_dec_ref(x_743);
 x_755 = lean_box(0);
}
if (lean_is_scalar(x_755)) {
 x_756 = lean_alloc_ctor(1, 2, 0);
} else {
 x_756 = x_755;
}
lean_ctor_set(x_756, 0, x_753);
lean_ctor_set(x_756, 1, x_754);
return x_756;
}
}
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
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
x_757 = lean_ctor_get(x_586, 0);
lean_inc(x_757);
x_758 = lean_ctor_get(x_586, 1);
lean_inc(x_758);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 x_759 = x_586;
} else {
 lean_dec_ref(x_586);
 x_759 = lean_box(0);
}
if (lean_is_scalar(x_759)) {
 x_760 = lean_alloc_ctor(1, 2, 0);
} else {
 x_760 = x_759;
}
lean_ctor_set(x_760, 0, x_757);
lean_ctor_set(x_760, 1, x_758);
return x_760;
}
}
}
}
case 2:
{
lean_object* x_761; uint8_t x_762; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_761 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_762 = !lean_is_exclusive(x_1);
if (x_762 == 0)
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; 
x_763 = lean_ctor_get(x_1, 7);
lean_dec(x_763);
x_764 = lean_ctor_get(x_1, 6);
lean_dec(x_764);
x_765 = lean_ctor_get(x_1, 5);
lean_dec(x_765);
x_766 = lean_ctor_get(x_1, 4);
lean_dec(x_766);
x_767 = lean_ctor_get(x_1, 3);
lean_dec(x_767);
x_768 = lean_ctor_get(x_1, 2);
lean_dec(x_768);
x_769 = lean_ctor_get(x_1, 1);
lean_dec(x_769);
x_770 = lean_ctor_get(x_1, 0);
lean_dec(x_770);
if (lean_obj_tag(x_761) == 0)
{
lean_object* x_771; uint8_t x_772; lean_object* x_773; uint8_t x_774; 
x_771 = lean_ctor_get(x_761, 1);
lean_inc(x_771);
lean_dec(x_761);
x_772 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_ctor_set_uint8(x_1, sizeof(void*)*8 + 1, x_772);
x_773 = lean_array_get_size(x_12);
x_774 = lean_nat_dec_lt(x_15, x_773);
lean_dec(x_773);
if (x_774 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_775; 
x_775 = l_Lean_Expr_getOptParamDefault_x3f(x_128);
if (lean_obj_tag(x_775) == 0)
{
lean_object* x_776; 
x_776 = l_Lean_Expr_getAutoParamTactic_x3f(x_128);
if (lean_obj_tag(x_776) == 0)
{
uint8_t x_777; 
lean_dec(x_1);
lean_dec(x_129);
lean_dec(x_128);
x_777 = l_Array_isEmpty___rarg(x_16);
if (x_777 == 0)
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_778 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_778, 0, x_127);
x_779 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_780 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_780, 0, x_779);
lean_ctor_set(x_780, 1, x_778);
x_781 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_782 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_782, 0, x_780);
lean_ctor_set(x_782, 1, x_781);
x_783 = x_16;
x_784 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_131, x_783);
x_785 = x_784;
x_786 = l_Array_toList___rarg(x_785);
lean_dec(x_785);
x_787 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_786);
x_788 = l_Array_HasRepr___rarg___closed__1;
x_789 = lean_string_append(x_788, x_787);
lean_dec(x_787);
x_790 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_790, 0, x_789);
x_791 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_791, 0, x_790);
x_792 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_792, 0, x_782);
lean_ctor_set(x_792, 1, x_791);
x_793 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_792, x_4, x_5, x_6, x_7, x_8, x_9, x_771);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_793;
}
else
{
lean_object* x_794; uint8_t x_795; 
lean_dec(x_127);
lean_dec(x_16);
x_794 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_795 = l_Lean_checkTraceOption(x_22, x_794);
lean_dec(x_22);
if (x_795 == 0)
{
lean_object* x_796; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_796 = x_771;
goto block_808;
}
else
{
lean_object* x_809; lean_object* x_810; 
x_809 = lean_ctor_get(x_13, 0);
lean_inc(x_809);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_810 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_809, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_771);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; 
x_811 = lean_ctor_get(x_810, 1);
lean_inc(x_811);
lean_dec(x_810);
x_796 = x_811;
goto block_808;
}
else
{
uint8_t x_812; 
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
x_812 = !lean_is_exclusive(x_810);
if (x_812 == 0)
{
return x_810;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_813 = lean_ctor_get(x_810, 0);
x_814 = lean_ctor_get(x_810, 1);
lean_inc(x_814);
lean_inc(x_813);
lean_dec(x_810);
x_815 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_815, 0, x_813);
lean_ctor_set(x_815, 1, x_814);
return x_815;
}
}
}
block_808:
{
lean_object* x_797; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_797 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_796);
lean_dec(x_17);
if (lean_obj_tag(x_797) == 0)
{
lean_object* x_798; lean_object* x_799; uint8_t x_800; 
x_798 = lean_ctor_get(x_797, 1);
lean_inc(x_798);
lean_dec(x_797);
lean_inc(x_2);
x_799 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__12(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_798);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_800 = !lean_is_exclusive(x_799);
if (x_800 == 0)
{
lean_object* x_801; 
x_801 = lean_ctor_get(x_799, 0);
lean_dec(x_801);
lean_ctor_set(x_799, 0, x_2);
return x_799;
}
else
{
lean_object* x_802; lean_object* x_803; 
x_802 = lean_ctor_get(x_799, 1);
lean_inc(x_802);
lean_dec(x_799);
x_803 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_803, 0, x_2);
lean_ctor_set(x_803, 1, x_802);
return x_803;
}
}
else
{
uint8_t x_804; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_804 = !lean_is_exclusive(x_797);
if (x_804 == 0)
{
return x_797;
}
else
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_805 = lean_ctor_get(x_797, 0);
x_806 = lean_ctor_get(x_797, 1);
lean_inc(x_806);
lean_inc(x_805);
lean_dec(x_797);
x_807 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_807, 0, x_805);
lean_ctor_set(x_807, 1, x_806);
return x_807;
}
}
}
}
else
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
lean_inc(x_2);
x_816 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_816, 0, x_2);
x_817 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_794, x_816, x_4, x_5, x_6, x_7, x_8, x_9, x_771);
x_818 = lean_ctor_get(x_817, 1);
lean_inc(x_818);
lean_dec(x_817);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_819 = x_818;
goto block_831;
}
else
{
lean_object* x_832; lean_object* x_833; 
x_832 = lean_ctor_get(x_13, 0);
lean_inc(x_832);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_833 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_832, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_818);
if (lean_obj_tag(x_833) == 0)
{
lean_object* x_834; 
x_834 = lean_ctor_get(x_833, 1);
lean_inc(x_834);
lean_dec(x_833);
x_819 = x_834;
goto block_831;
}
else
{
uint8_t x_835; 
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
x_835 = !lean_is_exclusive(x_833);
if (x_835 == 0)
{
return x_833;
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; 
x_836 = lean_ctor_get(x_833, 0);
x_837 = lean_ctor_get(x_833, 1);
lean_inc(x_837);
lean_inc(x_836);
lean_dec(x_833);
x_838 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_838, 0, x_836);
lean_ctor_set(x_838, 1, x_837);
return x_838;
}
}
}
block_831:
{
lean_object* x_820; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_820 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_819);
lean_dec(x_17);
if (lean_obj_tag(x_820) == 0)
{
lean_object* x_821; lean_object* x_822; uint8_t x_823; 
x_821 = lean_ctor_get(x_820, 1);
lean_inc(x_821);
lean_dec(x_820);
lean_inc(x_2);
x_822 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__13(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_821);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_823 = !lean_is_exclusive(x_822);
if (x_823 == 0)
{
lean_object* x_824; 
x_824 = lean_ctor_get(x_822, 0);
lean_dec(x_824);
lean_ctor_set(x_822, 0, x_2);
return x_822;
}
else
{
lean_object* x_825; lean_object* x_826; 
x_825 = lean_ctor_get(x_822, 1);
lean_inc(x_825);
lean_dec(x_822);
x_826 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_826, 0, x_2);
lean_ctor_set(x_826, 1, x_825);
return x_826;
}
}
else
{
uint8_t x_827; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_827 = !lean_is_exclusive(x_820);
if (x_827 == 0)
{
return x_820;
}
else
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; 
x_828 = lean_ctor_get(x_820, 0);
x_829 = lean_ctor_get(x_820, 1);
lean_inc(x_829);
lean_inc(x_828);
lean_dec(x_820);
x_830 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_830, 0, x_828);
lean_ctor_set(x_830, 1, x_829);
return x_830;
}
}
}
}
}
}
else
{
lean_object* x_839; 
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_839 = lean_ctor_get(x_776, 0);
lean_inc(x_839);
lean_dec(x_776);
if (lean_obj_tag(x_839) == 4)
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; 
x_840 = lean_ctor_get(x_839, 0);
lean_inc(x_840);
lean_dec(x_839);
x_841 = lean_st_ref_get(x_9, x_771);
x_842 = lean_ctor_get(x_841, 0);
lean_inc(x_842);
x_843 = lean_ctor_get(x_841, 1);
lean_inc(x_843);
lean_dec(x_841);
x_844 = lean_ctor_get(x_842, 0);
lean_inc(x_844);
lean_dec(x_842);
x_845 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_844, x_840);
if (lean_obj_tag(x_845) == 0)
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; 
lean_dec(x_1);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_11);
lean_dec(x_2);
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
lean_dec(x_845);
x_847 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_847, 0, x_846);
x_848 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_848, 0, x_847);
x_849 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_848, x_4, x_5, x_6, x_7, x_8, x_9, x_843);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_849;
}
else
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; 
x_850 = lean_ctor_get(x_845, 0);
lean_inc(x_850);
lean_dec(x_845);
x_851 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_843);
x_852 = lean_ctor_get(x_851, 1);
lean_inc(x_852);
lean_dec(x_851);
x_853 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_852);
x_854 = lean_ctor_get(x_853, 1);
lean_inc(x_854);
lean_dec(x_853);
x_855 = l_Lean_Syntax_getArgs(x_850);
lean_dec(x_850);
x_856 = l_Array_empty___closed__1;
x_857 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_855, x_855, x_131, x_856);
lean_dec(x_855);
x_858 = l_Lean_nullKind___closed__2;
x_859 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_859, 0, x_858);
lean_ctor_set(x_859, 1, x_857);
x_860 = lean_array_push(x_856, x_859);
x_861 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__5;
x_862 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_862, 0, x_861);
lean_ctor_set(x_862, 1, x_860);
x_863 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_864 = lean_array_push(x_863, x_862);
x_865 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_866 = lean_array_push(x_864, x_865);
x_867 = l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock___closed__2;
x_868 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_868, 0, x_867);
lean_ctor_set(x_868, 1, x_866);
x_869 = lean_array_push(x_856, x_868);
x_870 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_870, 0, x_858);
lean_ctor_set(x_870, 1, x_869);
x_871 = lean_array_push(x_856, x_870);
x_872 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_872, 0, x_861);
lean_ctor_set(x_872, 1, x_871);
x_873 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_874 = lean_array_push(x_873, x_872);
x_875 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_876 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_876, 0, x_875);
lean_ctor_set(x_876, 1, x_874);
x_877 = l_Lean_Syntax_copyInfo(x_876, x_11);
lean_dec(x_11);
x_878 = l_Lean_Expr_getAppNumArgsAux___main(x_128, x_131);
x_879 = lean_nat_sub(x_878, x_131);
lean_dec(x_878);
x_880 = lean_unsigned_to_nat(1u);
x_881 = lean_nat_sub(x_879, x_880);
lean_dec(x_879);
x_882 = l_Lean_Expr_getRevArg_x21___main(x_128, x_881);
lean_dec(x_128);
x_883 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_883, 0, x_877);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_884 = l___private_Lean_Elab_App_2__elabArg(x_2, x_883, x_882, x_4, x_5, x_6, x_7, x_8, x_9, x_854);
if (lean_obj_tag(x_884) == 0)
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; 
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_884, 1);
lean_inc(x_886);
lean_dec(x_884);
lean_inc(x_885);
x_887 = l_Lean_mkApp(x_2, x_885);
x_888 = lean_expr_instantiate1(x_129, x_885);
lean_dec(x_885);
lean_dec(x_129);
x_2 = x_887;
x_3 = x_888;
x_10 = x_886;
goto _start;
}
else
{
uint8_t x_890; 
lean_dec(x_1);
lean_dec(x_129);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_890 = !lean_is_exclusive(x_884);
if (x_890 == 0)
{
return x_884;
}
else
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; 
x_891 = lean_ctor_get(x_884, 0);
x_892 = lean_ctor_get(x_884, 1);
lean_inc(x_892);
lean_inc(x_891);
lean_dec(x_884);
x_893 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_893, 0, x_891);
lean_ctor_set(x_893, 1, x_892);
return x_893;
}
}
}
}
else
{
lean_object* x_894; lean_object* x_895; 
lean_dec(x_839);
lean_dec(x_1);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_11);
lean_dec(x_2);
x_894 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_895 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_894, x_4, x_5, x_6, x_7, x_8, x_9, x_771);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_895;
}
}
}
else
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_896 = lean_ctor_get(x_775, 0);
lean_inc(x_896);
lean_dec(x_775);
lean_inc(x_896);
x_897 = l_Lean_mkApp(x_2, x_896);
x_898 = lean_expr_instantiate1(x_129, x_896);
lean_dec(x_896);
lean_dec(x_129);
x_2 = x_897;
x_3 = x_898;
x_10 = x_771;
goto _start;
}
}
else
{
uint8_t x_900; 
lean_dec(x_1);
lean_dec(x_129);
lean_dec(x_128);
x_900 = l_Array_isEmpty___rarg(x_16);
if (x_900 == 0)
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_901 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_901, 0, x_127);
x_902 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_903 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_903, 0, x_902);
lean_ctor_set(x_903, 1, x_901);
x_904 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_905 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_905, 0, x_903);
lean_ctor_set(x_905, 1, x_904);
x_906 = x_16;
x_907 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_131, x_906);
x_908 = x_907;
x_909 = l_Array_toList___rarg(x_908);
lean_dec(x_908);
x_910 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_909);
x_911 = l_Array_HasRepr___rarg___closed__1;
x_912 = lean_string_append(x_911, x_910);
lean_dec(x_910);
x_913 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_913, 0, x_912);
x_914 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_914, 0, x_913);
x_915 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_915, 0, x_905);
lean_ctor_set(x_915, 1, x_914);
x_916 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_915, x_4, x_5, x_6, x_7, x_8, x_9, x_771);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_916;
}
else
{
lean_object* x_917; uint8_t x_918; 
lean_dec(x_127);
lean_dec(x_16);
x_917 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_918 = l_Lean_checkTraceOption(x_22, x_917);
lean_dec(x_22);
if (x_918 == 0)
{
lean_object* x_919; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_919 = x_771;
goto block_931;
}
else
{
lean_object* x_932; lean_object* x_933; 
x_932 = lean_ctor_get(x_13, 0);
lean_inc(x_932);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_933 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_932, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_771);
if (lean_obj_tag(x_933) == 0)
{
lean_object* x_934; 
x_934 = lean_ctor_get(x_933, 1);
lean_inc(x_934);
lean_dec(x_933);
x_919 = x_934;
goto block_931;
}
else
{
uint8_t x_935; 
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
x_935 = !lean_is_exclusive(x_933);
if (x_935 == 0)
{
return x_933;
}
else
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_936 = lean_ctor_get(x_933, 0);
x_937 = lean_ctor_get(x_933, 1);
lean_inc(x_937);
lean_inc(x_936);
lean_dec(x_933);
x_938 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_938, 0, x_936);
lean_ctor_set(x_938, 1, x_937);
return x_938;
}
}
}
block_931:
{
lean_object* x_920; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_920 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_919);
lean_dec(x_17);
if (lean_obj_tag(x_920) == 0)
{
lean_object* x_921; lean_object* x_922; uint8_t x_923; 
x_921 = lean_ctor_get(x_920, 1);
lean_inc(x_921);
lean_dec(x_920);
lean_inc(x_2);
x_922 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__14(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_921);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_923 = !lean_is_exclusive(x_922);
if (x_923 == 0)
{
lean_object* x_924; 
x_924 = lean_ctor_get(x_922, 0);
lean_dec(x_924);
lean_ctor_set(x_922, 0, x_2);
return x_922;
}
else
{
lean_object* x_925; lean_object* x_926; 
x_925 = lean_ctor_get(x_922, 1);
lean_inc(x_925);
lean_dec(x_922);
x_926 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_926, 0, x_2);
lean_ctor_set(x_926, 1, x_925);
return x_926;
}
}
else
{
uint8_t x_927; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_927 = !lean_is_exclusive(x_920);
if (x_927 == 0)
{
return x_920;
}
else
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; 
x_928 = lean_ctor_get(x_920, 0);
x_929 = lean_ctor_get(x_920, 1);
lean_inc(x_929);
lean_inc(x_928);
lean_dec(x_920);
x_930 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_930, 0, x_928);
lean_ctor_set(x_930, 1, x_929);
return x_930;
}
}
}
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
lean_inc(x_2);
x_939 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_939, 0, x_2);
x_940 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_917, x_939, x_4, x_5, x_6, x_7, x_8, x_9, x_771);
x_941 = lean_ctor_get(x_940, 1);
lean_inc(x_941);
lean_dec(x_940);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_942 = x_941;
goto block_954;
}
else
{
lean_object* x_955; lean_object* x_956; 
x_955 = lean_ctor_get(x_13, 0);
lean_inc(x_955);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_956 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_955, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_941);
if (lean_obj_tag(x_956) == 0)
{
lean_object* x_957; 
x_957 = lean_ctor_get(x_956, 1);
lean_inc(x_957);
lean_dec(x_956);
x_942 = x_957;
goto block_954;
}
else
{
uint8_t x_958; 
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
x_958 = !lean_is_exclusive(x_956);
if (x_958 == 0)
{
return x_956;
}
else
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; 
x_959 = lean_ctor_get(x_956, 0);
x_960 = lean_ctor_get(x_956, 1);
lean_inc(x_960);
lean_inc(x_959);
lean_dec(x_956);
x_961 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_961, 0, x_959);
lean_ctor_set(x_961, 1, x_960);
return x_961;
}
}
}
block_954:
{
lean_object* x_943; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_943 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_942);
lean_dec(x_17);
if (lean_obj_tag(x_943) == 0)
{
lean_object* x_944; lean_object* x_945; uint8_t x_946; 
x_944 = lean_ctor_get(x_943, 1);
lean_inc(x_944);
lean_dec(x_943);
lean_inc(x_2);
x_945 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__15(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_944);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_946 = !lean_is_exclusive(x_945);
if (x_946 == 0)
{
lean_object* x_947; 
x_947 = lean_ctor_get(x_945, 0);
lean_dec(x_947);
lean_ctor_set(x_945, 0, x_2);
return x_945;
}
else
{
lean_object* x_948; lean_object* x_949; 
x_948 = lean_ctor_get(x_945, 1);
lean_inc(x_948);
lean_dec(x_945);
x_949 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_949, 0, x_2);
lean_ctor_set(x_949, 1, x_948);
return x_949;
}
}
else
{
uint8_t x_950; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_950 = !lean_is_exclusive(x_943);
if (x_950 == 0)
{
return x_943;
}
else
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; 
x_951 = lean_ctor_get(x_943, 0);
x_952 = lean_ctor_get(x_943, 1);
lean_inc(x_952);
lean_inc(x_951);
lean_dec(x_943);
x_953 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_953, 0, x_951);
lean_ctor_set(x_953, 1, x_952);
return x_953;
}
}
}
}
}
}
}
else
{
lean_object* x_962; lean_object* x_963; 
lean_dec(x_1);
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_3);
x_962 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_963 = l___private_Lean_Elab_App_2__elabArg(x_2, x_962, x_128, x_4, x_5, x_6, x_7, x_8, x_9, x_771);
if (lean_obj_tag(x_963) == 0)
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; 
x_964 = lean_ctor_get(x_963, 0);
lean_inc(x_964);
x_965 = lean_ctor_get(x_963, 1);
lean_inc(x_965);
lean_dec(x_963);
x_966 = lean_unsigned_to_nat(1u);
x_967 = lean_nat_add(x_15, x_966);
lean_dec(x_15);
x_968 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_968, 0, x_11);
lean_ctor_set(x_968, 1, x_12);
lean_ctor_set(x_968, 2, x_13);
lean_ctor_set(x_968, 3, x_967);
lean_ctor_set(x_968, 4, x_16);
lean_ctor_set(x_968, 5, x_17);
lean_ctor_set(x_968, 6, x_18);
lean_ctor_set(x_968, 7, x_19);
lean_ctor_set_uint8(x_968, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_968, sizeof(void*)*8 + 1, x_772);
lean_inc(x_964);
x_969 = l_Lean_mkApp(x_2, x_964);
x_970 = lean_expr_instantiate1(x_129, x_964);
lean_dec(x_964);
lean_dec(x_129);
x_1 = x_968;
x_2 = x_969;
x_3 = x_970;
x_10 = x_965;
goto _start;
}
else
{
uint8_t x_972; 
lean_dec(x_129);
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
x_972 = !lean_is_exclusive(x_963);
if (x_972 == 0)
{
return x_963;
}
else
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; 
x_973 = lean_ctor_get(x_963, 0);
x_974 = lean_ctor_get(x_963, 1);
lean_inc(x_974);
lean_inc(x_973);
lean_dec(x_963);
x_975 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_975, 0, x_973);
lean_ctor_set(x_975, 1, x_974);
return x_975;
}
}
}
}
else
{
uint8_t x_976; 
lean_free_object(x_1);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
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
x_976 = !lean_is_exclusive(x_761);
if (x_976 == 0)
{
return x_761;
}
else
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; 
x_977 = lean_ctor_get(x_761, 0);
x_978 = lean_ctor_get(x_761, 1);
lean_inc(x_978);
lean_inc(x_977);
lean_dec(x_761);
x_979 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_979, 0, x_977);
lean_ctor_set(x_979, 1, x_978);
return x_979;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_761) == 0)
{
lean_object* x_980; uint8_t x_981; lean_object* x_982; lean_object* x_983; uint8_t x_984; 
x_980 = lean_ctor_get(x_761, 1);
lean_inc(x_980);
lean_dec(x_761);
x_981 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_982 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_982, 0, x_11);
lean_ctor_set(x_982, 1, x_12);
lean_ctor_set(x_982, 2, x_13);
lean_ctor_set(x_982, 3, x_15);
lean_ctor_set(x_982, 4, x_16);
lean_ctor_set(x_982, 5, x_17);
lean_ctor_set(x_982, 6, x_18);
lean_ctor_set(x_982, 7, x_19);
lean_ctor_set_uint8(x_982, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_982, sizeof(void*)*8 + 1, x_981);
x_983 = lean_array_get_size(x_12);
x_984 = lean_nat_dec_lt(x_15, x_983);
lean_dec(x_983);
if (x_984 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_985; 
x_985 = l_Lean_Expr_getOptParamDefault_x3f(x_128);
if (lean_obj_tag(x_985) == 0)
{
lean_object* x_986; 
x_986 = l_Lean_Expr_getAutoParamTactic_x3f(x_128);
if (lean_obj_tag(x_986) == 0)
{
uint8_t x_987; 
lean_dec(x_982);
lean_dec(x_129);
lean_dec(x_128);
x_987 = l_Array_isEmpty___rarg(x_16);
if (x_987 == 0)
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_988 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_988, 0, x_127);
x_989 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_990 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_990, 0, x_989);
lean_ctor_set(x_990, 1, x_988);
x_991 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_992 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_992, 0, x_990);
lean_ctor_set(x_992, 1, x_991);
x_993 = x_16;
x_994 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_131, x_993);
x_995 = x_994;
x_996 = l_Array_toList___rarg(x_995);
lean_dec(x_995);
x_997 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_996);
x_998 = l_Array_HasRepr___rarg___closed__1;
x_999 = lean_string_append(x_998, x_997);
lean_dec(x_997);
x_1000 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1000, 0, x_999);
x_1001 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1001, 0, x_1000);
x_1002 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1002, 0, x_992);
lean_ctor_set(x_1002, 1, x_1001);
x_1003 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1002, x_4, x_5, x_6, x_7, x_8, x_9, x_980);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1003;
}
else
{
lean_object* x_1004; uint8_t x_1005; 
lean_dec(x_127);
lean_dec(x_16);
x_1004 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1005 = l_Lean_checkTraceOption(x_22, x_1004);
lean_dec(x_22);
if (x_1005 == 0)
{
lean_object* x_1006; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1006 = x_980;
goto block_1017;
}
else
{
lean_object* x_1018; lean_object* x_1019; 
x_1018 = lean_ctor_get(x_13, 0);
lean_inc(x_1018);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1019 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1018, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_980);
if (lean_obj_tag(x_1019) == 0)
{
lean_object* x_1020; 
x_1020 = lean_ctor_get(x_1019, 1);
lean_inc(x_1020);
lean_dec(x_1019);
x_1006 = x_1020;
goto block_1017;
}
else
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; 
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
x_1021 = lean_ctor_get(x_1019, 0);
lean_inc(x_1021);
x_1022 = lean_ctor_get(x_1019, 1);
lean_inc(x_1022);
if (lean_is_exclusive(x_1019)) {
 lean_ctor_release(x_1019, 0);
 lean_ctor_release(x_1019, 1);
 x_1023 = x_1019;
} else {
 lean_dec_ref(x_1019);
 x_1023 = lean_box(0);
}
if (lean_is_scalar(x_1023)) {
 x_1024 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1024 = x_1023;
}
lean_ctor_set(x_1024, 0, x_1021);
lean_ctor_set(x_1024, 1, x_1022);
return x_1024;
}
}
block_1017:
{
lean_object* x_1007; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1007 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1006);
lean_dec(x_17);
if (lean_obj_tag(x_1007) == 0)
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1008 = lean_ctor_get(x_1007, 1);
lean_inc(x_1008);
lean_dec(x_1007);
lean_inc(x_2);
x_1009 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__12(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1008);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1010 = lean_ctor_get(x_1009, 1);
lean_inc(x_1010);
if (lean_is_exclusive(x_1009)) {
 lean_ctor_release(x_1009, 0);
 lean_ctor_release(x_1009, 1);
 x_1011 = x_1009;
} else {
 lean_dec_ref(x_1009);
 x_1011 = lean_box(0);
}
if (lean_is_scalar(x_1011)) {
 x_1012 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1012 = x_1011;
}
lean_ctor_set(x_1012, 0, x_2);
lean_ctor_set(x_1012, 1, x_1010);
return x_1012;
}
else
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1013 = lean_ctor_get(x_1007, 0);
lean_inc(x_1013);
x_1014 = lean_ctor_get(x_1007, 1);
lean_inc(x_1014);
if (lean_is_exclusive(x_1007)) {
 lean_ctor_release(x_1007, 0);
 lean_ctor_release(x_1007, 1);
 x_1015 = x_1007;
} else {
 lean_dec_ref(x_1007);
 x_1015 = lean_box(0);
}
if (lean_is_scalar(x_1015)) {
 x_1016 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1016 = x_1015;
}
lean_ctor_set(x_1016, 0, x_1013);
lean_ctor_set(x_1016, 1, x_1014);
return x_1016;
}
}
}
else
{
lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; 
lean_inc(x_2);
x_1025 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1025, 0, x_2);
x_1026 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1004, x_1025, x_4, x_5, x_6, x_7, x_8, x_9, x_980);
x_1027 = lean_ctor_get(x_1026, 1);
lean_inc(x_1027);
lean_dec(x_1026);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1028 = x_1027;
goto block_1039;
}
else
{
lean_object* x_1040; lean_object* x_1041; 
x_1040 = lean_ctor_get(x_13, 0);
lean_inc(x_1040);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1041 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1040, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1027);
if (lean_obj_tag(x_1041) == 0)
{
lean_object* x_1042; 
x_1042 = lean_ctor_get(x_1041, 1);
lean_inc(x_1042);
lean_dec(x_1041);
x_1028 = x_1042;
goto block_1039;
}
else
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; 
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
x_1043 = lean_ctor_get(x_1041, 0);
lean_inc(x_1043);
x_1044 = lean_ctor_get(x_1041, 1);
lean_inc(x_1044);
if (lean_is_exclusive(x_1041)) {
 lean_ctor_release(x_1041, 0);
 lean_ctor_release(x_1041, 1);
 x_1045 = x_1041;
} else {
 lean_dec_ref(x_1041);
 x_1045 = lean_box(0);
}
if (lean_is_scalar(x_1045)) {
 x_1046 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1046 = x_1045;
}
lean_ctor_set(x_1046, 0, x_1043);
lean_ctor_set(x_1046, 1, x_1044);
return x_1046;
}
}
block_1039:
{
lean_object* x_1029; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1029 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1028);
lean_dec(x_17);
if (lean_obj_tag(x_1029) == 0)
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
x_1030 = lean_ctor_get(x_1029, 1);
lean_inc(x_1030);
lean_dec(x_1029);
lean_inc(x_2);
x_1031 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__13(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1030);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1032 = lean_ctor_get(x_1031, 1);
lean_inc(x_1032);
if (lean_is_exclusive(x_1031)) {
 lean_ctor_release(x_1031, 0);
 lean_ctor_release(x_1031, 1);
 x_1033 = x_1031;
} else {
 lean_dec_ref(x_1031);
 x_1033 = lean_box(0);
}
if (lean_is_scalar(x_1033)) {
 x_1034 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1034 = x_1033;
}
lean_ctor_set(x_1034, 0, x_2);
lean_ctor_set(x_1034, 1, x_1032);
return x_1034;
}
else
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1035 = lean_ctor_get(x_1029, 0);
lean_inc(x_1035);
x_1036 = lean_ctor_get(x_1029, 1);
lean_inc(x_1036);
if (lean_is_exclusive(x_1029)) {
 lean_ctor_release(x_1029, 0);
 lean_ctor_release(x_1029, 1);
 x_1037 = x_1029;
} else {
 lean_dec_ref(x_1029);
 x_1037 = lean_box(0);
}
if (lean_is_scalar(x_1037)) {
 x_1038 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1038 = x_1037;
}
lean_ctor_set(x_1038, 0, x_1035);
lean_ctor_set(x_1038, 1, x_1036);
return x_1038;
}
}
}
}
}
else
{
lean_object* x_1047; 
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_1047 = lean_ctor_get(x_986, 0);
lean_inc(x_1047);
lean_dec(x_986);
if (lean_obj_tag(x_1047) == 4)
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; 
x_1048 = lean_ctor_get(x_1047, 0);
lean_inc(x_1048);
lean_dec(x_1047);
x_1049 = lean_st_ref_get(x_9, x_980);
x_1050 = lean_ctor_get(x_1049, 0);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1049, 1);
lean_inc(x_1051);
lean_dec(x_1049);
x_1052 = lean_ctor_get(x_1050, 0);
lean_inc(x_1052);
lean_dec(x_1050);
x_1053 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1052, x_1048);
if (lean_obj_tag(x_1053) == 0)
{
lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; 
lean_dec(x_982);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_11);
lean_dec(x_2);
x_1054 = lean_ctor_get(x_1053, 0);
lean_inc(x_1054);
lean_dec(x_1053);
x_1055 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1055, 0, x_1054);
x_1056 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1056, 0, x_1055);
x_1057 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1056, x_4, x_5, x_6, x_7, x_8, x_9, x_1051);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1057;
}
else
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; 
x_1058 = lean_ctor_get(x_1053, 0);
lean_inc(x_1058);
lean_dec(x_1053);
x_1059 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_1051);
x_1060 = lean_ctor_get(x_1059, 1);
lean_inc(x_1060);
lean_dec(x_1059);
x_1061 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_1060);
x_1062 = lean_ctor_get(x_1061, 1);
lean_inc(x_1062);
lean_dec(x_1061);
x_1063 = l_Lean_Syntax_getArgs(x_1058);
lean_dec(x_1058);
x_1064 = l_Array_empty___closed__1;
x_1065 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1063, x_1063, x_131, x_1064);
lean_dec(x_1063);
x_1066 = l_Lean_nullKind___closed__2;
x_1067 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1067, 0, x_1066);
lean_ctor_set(x_1067, 1, x_1065);
x_1068 = lean_array_push(x_1064, x_1067);
x_1069 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__5;
x_1070 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1070, 0, x_1069);
lean_ctor_set(x_1070, 1, x_1068);
x_1071 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_1072 = lean_array_push(x_1071, x_1070);
x_1073 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1074 = lean_array_push(x_1072, x_1073);
x_1075 = l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock___closed__2;
x_1076 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1076, 0, x_1075);
lean_ctor_set(x_1076, 1, x_1074);
x_1077 = lean_array_push(x_1064, x_1076);
x_1078 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1078, 0, x_1066);
lean_ctor_set(x_1078, 1, x_1077);
x_1079 = lean_array_push(x_1064, x_1078);
x_1080 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1080, 0, x_1069);
lean_ctor_set(x_1080, 1, x_1079);
x_1081 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1082 = lean_array_push(x_1081, x_1080);
x_1083 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_1084 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1084, 0, x_1083);
lean_ctor_set(x_1084, 1, x_1082);
x_1085 = l_Lean_Syntax_copyInfo(x_1084, x_11);
lean_dec(x_11);
x_1086 = l_Lean_Expr_getAppNumArgsAux___main(x_128, x_131);
x_1087 = lean_nat_sub(x_1086, x_131);
lean_dec(x_1086);
x_1088 = lean_unsigned_to_nat(1u);
x_1089 = lean_nat_sub(x_1087, x_1088);
lean_dec(x_1087);
x_1090 = l_Lean_Expr_getRevArg_x21___main(x_128, x_1089);
lean_dec(x_128);
x_1091 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1091, 0, x_1085);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1092 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1091, x_1090, x_4, x_5, x_6, x_7, x_8, x_9, x_1062);
if (lean_obj_tag(x_1092) == 0)
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
x_1093 = lean_ctor_get(x_1092, 0);
lean_inc(x_1093);
x_1094 = lean_ctor_get(x_1092, 1);
lean_inc(x_1094);
lean_dec(x_1092);
lean_inc(x_1093);
x_1095 = l_Lean_mkApp(x_2, x_1093);
x_1096 = lean_expr_instantiate1(x_129, x_1093);
lean_dec(x_1093);
lean_dec(x_129);
x_1 = x_982;
x_2 = x_1095;
x_3 = x_1096;
x_10 = x_1094;
goto _start;
}
else
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; 
lean_dec(x_982);
lean_dec(x_129);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1098 = lean_ctor_get(x_1092, 0);
lean_inc(x_1098);
x_1099 = lean_ctor_get(x_1092, 1);
lean_inc(x_1099);
if (lean_is_exclusive(x_1092)) {
 lean_ctor_release(x_1092, 0);
 lean_ctor_release(x_1092, 1);
 x_1100 = x_1092;
} else {
 lean_dec_ref(x_1092);
 x_1100 = lean_box(0);
}
if (lean_is_scalar(x_1100)) {
 x_1101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1101 = x_1100;
}
lean_ctor_set(x_1101, 0, x_1098);
lean_ctor_set(x_1101, 1, x_1099);
return x_1101;
}
}
}
else
{
lean_object* x_1102; lean_object* x_1103; 
lean_dec(x_1047);
lean_dec(x_982);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_11);
lean_dec(x_2);
x_1102 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1103 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1102, x_4, x_5, x_6, x_7, x_8, x_9, x_980);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1103;
}
}
}
else
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_1104 = lean_ctor_get(x_985, 0);
lean_inc(x_1104);
lean_dec(x_985);
lean_inc(x_1104);
x_1105 = l_Lean_mkApp(x_2, x_1104);
x_1106 = lean_expr_instantiate1(x_129, x_1104);
lean_dec(x_1104);
lean_dec(x_129);
x_1 = x_982;
x_2 = x_1105;
x_3 = x_1106;
x_10 = x_980;
goto _start;
}
}
else
{
uint8_t x_1108; 
lean_dec(x_982);
lean_dec(x_129);
lean_dec(x_128);
x_1108 = l_Array_isEmpty___rarg(x_16);
if (x_1108 == 0)
{
lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_1109 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1109, 0, x_127);
x_1110 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1111 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1111, 0, x_1110);
lean_ctor_set(x_1111, 1, x_1109);
x_1112 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1113 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1113, 0, x_1111);
lean_ctor_set(x_1113, 1, x_1112);
x_1114 = x_16;
x_1115 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_131, x_1114);
x_1116 = x_1115;
x_1117 = l_Array_toList___rarg(x_1116);
lean_dec(x_1116);
x_1118 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_1117);
x_1119 = l_Array_HasRepr___rarg___closed__1;
x_1120 = lean_string_append(x_1119, x_1118);
lean_dec(x_1118);
x_1121 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1121, 0, x_1120);
x_1122 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1122, 0, x_1121);
x_1123 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1123, 0, x_1113);
lean_ctor_set(x_1123, 1, x_1122);
x_1124 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1123, x_4, x_5, x_6, x_7, x_8, x_9, x_980);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1124;
}
else
{
lean_object* x_1125; uint8_t x_1126; 
lean_dec(x_127);
lean_dec(x_16);
x_1125 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1126 = l_Lean_checkTraceOption(x_22, x_1125);
lean_dec(x_22);
if (x_1126 == 0)
{
lean_object* x_1127; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1127 = x_980;
goto block_1138;
}
else
{
lean_object* x_1139; lean_object* x_1140; 
x_1139 = lean_ctor_get(x_13, 0);
lean_inc(x_1139);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1140 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1139, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_980);
if (lean_obj_tag(x_1140) == 0)
{
lean_object* x_1141; 
x_1141 = lean_ctor_get(x_1140, 1);
lean_inc(x_1141);
lean_dec(x_1140);
x_1127 = x_1141;
goto block_1138;
}
else
{
lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; 
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
x_1142 = lean_ctor_get(x_1140, 0);
lean_inc(x_1142);
x_1143 = lean_ctor_get(x_1140, 1);
lean_inc(x_1143);
if (lean_is_exclusive(x_1140)) {
 lean_ctor_release(x_1140, 0);
 lean_ctor_release(x_1140, 1);
 x_1144 = x_1140;
} else {
 lean_dec_ref(x_1140);
 x_1144 = lean_box(0);
}
if (lean_is_scalar(x_1144)) {
 x_1145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1145 = x_1144;
}
lean_ctor_set(x_1145, 0, x_1142);
lean_ctor_set(x_1145, 1, x_1143);
return x_1145;
}
}
block_1138:
{
lean_object* x_1128; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1128 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1127);
lean_dec(x_17);
if (lean_obj_tag(x_1128) == 0)
{
lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; 
x_1129 = lean_ctor_get(x_1128, 1);
lean_inc(x_1129);
lean_dec(x_1128);
lean_inc(x_2);
x_1130 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__14(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1129);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1131 = lean_ctor_get(x_1130, 1);
lean_inc(x_1131);
if (lean_is_exclusive(x_1130)) {
 lean_ctor_release(x_1130, 0);
 lean_ctor_release(x_1130, 1);
 x_1132 = x_1130;
} else {
 lean_dec_ref(x_1130);
 x_1132 = lean_box(0);
}
if (lean_is_scalar(x_1132)) {
 x_1133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1133 = x_1132;
}
lean_ctor_set(x_1133, 0, x_2);
lean_ctor_set(x_1133, 1, x_1131);
return x_1133;
}
else
{
lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1134 = lean_ctor_get(x_1128, 0);
lean_inc(x_1134);
x_1135 = lean_ctor_get(x_1128, 1);
lean_inc(x_1135);
if (lean_is_exclusive(x_1128)) {
 lean_ctor_release(x_1128, 0);
 lean_ctor_release(x_1128, 1);
 x_1136 = x_1128;
} else {
 lean_dec_ref(x_1128);
 x_1136 = lean_box(0);
}
if (lean_is_scalar(x_1136)) {
 x_1137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1137 = x_1136;
}
lean_ctor_set(x_1137, 0, x_1134);
lean_ctor_set(x_1137, 1, x_1135);
return x_1137;
}
}
}
else
{
lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; 
lean_inc(x_2);
x_1146 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1146, 0, x_2);
x_1147 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1125, x_1146, x_4, x_5, x_6, x_7, x_8, x_9, x_980);
x_1148 = lean_ctor_get(x_1147, 1);
lean_inc(x_1148);
lean_dec(x_1147);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1149 = x_1148;
goto block_1160;
}
else
{
lean_object* x_1161; lean_object* x_1162; 
x_1161 = lean_ctor_get(x_13, 0);
lean_inc(x_1161);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1162 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1161, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1148);
if (lean_obj_tag(x_1162) == 0)
{
lean_object* x_1163; 
x_1163 = lean_ctor_get(x_1162, 1);
lean_inc(x_1163);
lean_dec(x_1162);
x_1149 = x_1163;
goto block_1160;
}
else
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
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
x_1164 = lean_ctor_get(x_1162, 0);
lean_inc(x_1164);
x_1165 = lean_ctor_get(x_1162, 1);
lean_inc(x_1165);
if (lean_is_exclusive(x_1162)) {
 lean_ctor_release(x_1162, 0);
 lean_ctor_release(x_1162, 1);
 x_1166 = x_1162;
} else {
 lean_dec_ref(x_1162);
 x_1166 = lean_box(0);
}
if (lean_is_scalar(x_1166)) {
 x_1167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1167 = x_1166;
}
lean_ctor_set(x_1167, 0, x_1164);
lean_ctor_set(x_1167, 1, x_1165);
return x_1167;
}
}
block_1160:
{
lean_object* x_1150; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1150 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1149);
lean_dec(x_17);
if (lean_obj_tag(x_1150) == 0)
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
x_1151 = lean_ctor_get(x_1150, 1);
lean_inc(x_1151);
lean_dec(x_1150);
lean_inc(x_2);
x_1152 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__15(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1151);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1153 = lean_ctor_get(x_1152, 1);
lean_inc(x_1153);
if (lean_is_exclusive(x_1152)) {
 lean_ctor_release(x_1152, 0);
 lean_ctor_release(x_1152, 1);
 x_1154 = x_1152;
} else {
 lean_dec_ref(x_1152);
 x_1154 = lean_box(0);
}
if (lean_is_scalar(x_1154)) {
 x_1155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1155 = x_1154;
}
lean_ctor_set(x_1155, 0, x_2);
lean_ctor_set(x_1155, 1, x_1153);
return x_1155;
}
else
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1156 = lean_ctor_get(x_1150, 0);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1150, 1);
lean_inc(x_1157);
if (lean_is_exclusive(x_1150)) {
 lean_ctor_release(x_1150, 0);
 lean_ctor_release(x_1150, 1);
 x_1158 = x_1150;
} else {
 lean_dec_ref(x_1150);
 x_1158 = lean_box(0);
}
if (lean_is_scalar(x_1158)) {
 x_1159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1159 = x_1158;
}
lean_ctor_set(x_1159, 0, x_1156);
lean_ctor_set(x_1159, 1, x_1157);
return x_1159;
}
}
}
}
}
}
else
{
lean_object* x_1168; lean_object* x_1169; 
lean_dec(x_982);
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_3);
x_1168 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1169 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1168, x_128, x_4, x_5, x_6, x_7, x_8, x_9, x_980);
if (lean_obj_tag(x_1169) == 0)
{
lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; 
x_1170 = lean_ctor_get(x_1169, 0);
lean_inc(x_1170);
x_1171 = lean_ctor_get(x_1169, 1);
lean_inc(x_1171);
lean_dec(x_1169);
x_1172 = lean_unsigned_to_nat(1u);
x_1173 = lean_nat_add(x_15, x_1172);
lean_dec(x_15);
x_1174 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1174, 0, x_11);
lean_ctor_set(x_1174, 1, x_12);
lean_ctor_set(x_1174, 2, x_13);
lean_ctor_set(x_1174, 3, x_1173);
lean_ctor_set(x_1174, 4, x_16);
lean_ctor_set(x_1174, 5, x_17);
lean_ctor_set(x_1174, 6, x_18);
lean_ctor_set(x_1174, 7, x_19);
lean_ctor_set_uint8(x_1174, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1174, sizeof(void*)*8 + 1, x_981);
lean_inc(x_1170);
x_1175 = l_Lean_mkApp(x_2, x_1170);
x_1176 = lean_expr_instantiate1(x_129, x_1170);
lean_dec(x_1170);
lean_dec(x_129);
x_1 = x_1174;
x_2 = x_1175;
x_3 = x_1176;
x_10 = x_1171;
goto _start;
}
else
{
lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; 
lean_dec(x_129);
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
x_1178 = lean_ctor_get(x_1169, 0);
lean_inc(x_1178);
x_1179 = lean_ctor_get(x_1169, 1);
lean_inc(x_1179);
if (lean_is_exclusive(x_1169)) {
 lean_ctor_release(x_1169, 0);
 lean_ctor_release(x_1169, 1);
 x_1180 = x_1169;
} else {
 lean_dec_ref(x_1169);
 x_1180 = lean_box(0);
}
if (lean_is_scalar(x_1180)) {
 x_1181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1181 = x_1180;
}
lean_ctor_set(x_1181, 0, x_1178);
lean_ctor_set(x_1181, 1, x_1179);
return x_1181;
}
}
}
else
{
lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
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
x_1182 = lean_ctor_get(x_761, 0);
lean_inc(x_1182);
x_1183 = lean_ctor_get(x_761, 1);
lean_inc(x_1183);
if (lean_is_exclusive(x_761)) {
 lean_ctor_release(x_761, 0);
 lean_ctor_release(x_761, 1);
 x_1184 = x_761;
} else {
 lean_dec_ref(x_761);
 x_1184 = lean_box(0);
}
if (lean_is_scalar(x_1184)) {
 x_1185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1185 = x_1184;
}
lean_ctor_set(x_1185, 0, x_1182);
lean_ctor_set(x_1185, 1, x_1183);
return x_1185;
}
}
}
case 3:
{
if (x_14 == 0)
{
uint8_t x_1186; 
lean_dec(x_127);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_3);
x_1186 = !lean_is_exclusive(x_1);
if (x_1186 == 0)
{
lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; uint8_t x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; 
x_1187 = lean_ctor_get(x_1, 7);
lean_dec(x_1187);
x_1188 = lean_ctor_get(x_1, 6);
lean_dec(x_1188);
x_1189 = lean_ctor_get(x_1, 5);
lean_dec(x_1189);
x_1190 = lean_ctor_get(x_1, 4);
lean_dec(x_1190);
x_1191 = lean_ctor_get(x_1, 3);
lean_dec(x_1191);
x_1192 = lean_ctor_get(x_1, 2);
lean_dec(x_1192);
x_1193 = lean_ctor_get(x_1, 1);
lean_dec(x_1193);
x_1194 = lean_ctor_get(x_1, 0);
lean_dec(x_1194);
x_1195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1195, 0, x_128);
x_1196 = 1;
x_1197 = lean_box(0);
lean_inc(x_6);
x_1198 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_1195, x_1196, x_1197, x_6, x_7, x_8, x_9, x_29);
x_1199 = lean_ctor_get(x_1198, 0);
lean_inc(x_1199);
x_1200 = lean_ctor_get(x_1198, 1);
lean_inc(x_1200);
lean_dec(x_1198);
x_1201 = l_Lean_Expr_mvarId_x21(x_1199);
x_1202 = lean_array_push(x_17, x_1201);
lean_ctor_set(x_1, 5, x_1202);
lean_inc(x_1199);
x_1203 = l_Lean_mkApp(x_2, x_1199);
x_1204 = lean_expr_instantiate1(x_129, x_1199);
lean_dec(x_1199);
lean_dec(x_129);
x_2 = x_1203;
x_3 = x_1204;
x_10 = x_1200;
goto _start;
}
else
{
lean_object* x_1206; uint8_t x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
lean_dec(x_1);
x_1206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1206, 0, x_128);
x_1207 = 1;
x_1208 = lean_box(0);
lean_inc(x_6);
x_1209 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_1206, x_1207, x_1208, x_6, x_7, x_8, x_9, x_29);
x_1210 = lean_ctor_get(x_1209, 0);
lean_inc(x_1210);
x_1211 = lean_ctor_get(x_1209, 1);
lean_inc(x_1211);
lean_dec(x_1209);
x_1212 = l_Lean_Expr_mvarId_x21(x_1210);
x_1213 = lean_array_push(x_17, x_1212);
x_1214 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1214, 0, x_11);
lean_ctor_set(x_1214, 1, x_12);
lean_ctor_set(x_1214, 2, x_13);
lean_ctor_set(x_1214, 3, x_15);
lean_ctor_set(x_1214, 4, x_16);
lean_ctor_set(x_1214, 5, x_1213);
lean_ctor_set(x_1214, 6, x_18);
lean_ctor_set(x_1214, 7, x_19);
lean_ctor_set_uint8(x_1214, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1214, sizeof(void*)*8 + 1, x_21);
lean_inc(x_1210);
x_1215 = l_Lean_mkApp(x_2, x_1210);
x_1216 = lean_expr_instantiate1(x_129, x_1210);
lean_dec(x_1210);
lean_dec(x_129);
x_1 = x_1214;
x_2 = x_1215;
x_3 = x_1216;
x_10 = x_1211;
goto _start;
}
}
else
{
uint8_t x_1218; 
x_1218 = l___private_Lean_Elab_App_9__nextArgIsHole(x_1);
if (x_1218 == 0)
{
lean_object* x_1219; uint8_t x_1220; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_1219 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_1220 = !lean_is_exclusive(x_1);
if (x_1220 == 0)
{
lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; 
x_1221 = lean_ctor_get(x_1, 7);
lean_dec(x_1221);
x_1222 = lean_ctor_get(x_1, 6);
lean_dec(x_1222);
x_1223 = lean_ctor_get(x_1, 5);
lean_dec(x_1223);
x_1224 = lean_ctor_get(x_1, 4);
lean_dec(x_1224);
x_1225 = lean_ctor_get(x_1, 3);
lean_dec(x_1225);
x_1226 = lean_ctor_get(x_1, 2);
lean_dec(x_1226);
x_1227 = lean_ctor_get(x_1, 1);
lean_dec(x_1227);
x_1228 = lean_ctor_get(x_1, 0);
lean_dec(x_1228);
if (lean_obj_tag(x_1219) == 0)
{
lean_object* x_1229; lean_object* x_1230; uint8_t x_1231; 
x_1229 = lean_ctor_get(x_1219, 1);
lean_inc(x_1229);
lean_dec(x_1219);
x_1230 = lean_array_get_size(x_12);
x_1231 = lean_nat_dec_lt(x_15, x_1230);
lean_dec(x_1230);
if (x_1231 == 0)
{
uint8_t x_1232; 
lean_free_object(x_1);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_1232 = l_Array_isEmpty___rarg(x_16);
if (x_1232 == 0)
{
lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_1233 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1233, 0, x_127);
x_1234 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1235 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1235, 0, x_1234);
lean_ctor_set(x_1235, 1, x_1233);
x_1236 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1237 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1237, 0, x_1235);
lean_ctor_set(x_1237, 1, x_1236);
x_1238 = x_16;
x_1239 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_131, x_1238);
x_1240 = x_1239;
x_1241 = l_Array_toList___rarg(x_1240);
lean_dec(x_1240);
x_1242 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_1241);
x_1243 = l_Array_HasRepr___rarg___closed__1;
x_1244 = lean_string_append(x_1243, x_1242);
lean_dec(x_1242);
x_1245 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1245, 0, x_1244);
x_1246 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1246, 0, x_1245);
x_1247 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1247, 0, x_1237);
lean_ctor_set(x_1247, 1, x_1246);
x_1248 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1247, x_4, x_5, x_6, x_7, x_8, x_9, x_1229);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1248;
}
else
{
lean_object* x_1249; uint8_t x_1250; 
lean_dec(x_127);
lean_dec(x_16);
x_1249 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1250 = l_Lean_checkTraceOption(x_22, x_1249);
lean_dec(x_22);
if (x_1250 == 0)
{
lean_object* x_1251; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1251 = x_1229;
goto block_1263;
}
else
{
lean_object* x_1264; lean_object* x_1265; 
x_1264 = lean_ctor_get(x_13, 0);
lean_inc(x_1264);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1265 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1264, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1229);
if (lean_obj_tag(x_1265) == 0)
{
lean_object* x_1266; 
x_1266 = lean_ctor_get(x_1265, 1);
lean_inc(x_1266);
lean_dec(x_1265);
x_1251 = x_1266;
goto block_1263;
}
else
{
uint8_t x_1267; 
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
x_1267 = !lean_is_exclusive(x_1265);
if (x_1267 == 0)
{
return x_1265;
}
else
{
lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; 
x_1268 = lean_ctor_get(x_1265, 0);
x_1269 = lean_ctor_get(x_1265, 1);
lean_inc(x_1269);
lean_inc(x_1268);
lean_dec(x_1265);
x_1270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1270, 0, x_1268);
lean_ctor_set(x_1270, 1, x_1269);
return x_1270;
}
}
}
block_1263:
{
lean_object* x_1252; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1252 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1251);
lean_dec(x_17);
if (lean_obj_tag(x_1252) == 0)
{
lean_object* x_1253; lean_object* x_1254; uint8_t x_1255; 
x_1253 = lean_ctor_get(x_1252, 1);
lean_inc(x_1253);
lean_dec(x_1252);
lean_inc(x_2);
x_1254 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__16(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1253);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1255 = !lean_is_exclusive(x_1254);
if (x_1255 == 0)
{
lean_object* x_1256; 
x_1256 = lean_ctor_get(x_1254, 0);
lean_dec(x_1256);
lean_ctor_set(x_1254, 0, x_2);
return x_1254;
}
else
{
lean_object* x_1257; lean_object* x_1258; 
x_1257 = lean_ctor_get(x_1254, 1);
lean_inc(x_1257);
lean_dec(x_1254);
x_1258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1258, 0, x_2);
lean_ctor_set(x_1258, 1, x_1257);
return x_1258;
}
}
else
{
uint8_t x_1259; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1259 = !lean_is_exclusive(x_1252);
if (x_1259 == 0)
{
return x_1252;
}
else
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; 
x_1260 = lean_ctor_get(x_1252, 0);
x_1261 = lean_ctor_get(x_1252, 1);
lean_inc(x_1261);
lean_inc(x_1260);
lean_dec(x_1252);
x_1262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1262, 0, x_1260);
lean_ctor_set(x_1262, 1, x_1261);
return x_1262;
}
}
}
}
else
{
lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; 
lean_inc(x_2);
x_1271 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1271, 0, x_2);
x_1272 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1249, x_1271, x_4, x_5, x_6, x_7, x_8, x_9, x_1229);
x_1273 = lean_ctor_get(x_1272, 1);
lean_inc(x_1273);
lean_dec(x_1272);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1274 = x_1273;
goto block_1286;
}
else
{
lean_object* x_1287; lean_object* x_1288; 
x_1287 = lean_ctor_get(x_13, 0);
lean_inc(x_1287);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1288 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1287, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1273);
if (lean_obj_tag(x_1288) == 0)
{
lean_object* x_1289; 
x_1289 = lean_ctor_get(x_1288, 1);
lean_inc(x_1289);
lean_dec(x_1288);
x_1274 = x_1289;
goto block_1286;
}
else
{
uint8_t x_1290; 
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
x_1290 = !lean_is_exclusive(x_1288);
if (x_1290 == 0)
{
return x_1288;
}
else
{
lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; 
x_1291 = lean_ctor_get(x_1288, 0);
x_1292 = lean_ctor_get(x_1288, 1);
lean_inc(x_1292);
lean_inc(x_1291);
lean_dec(x_1288);
x_1293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1293, 0, x_1291);
lean_ctor_set(x_1293, 1, x_1292);
return x_1293;
}
}
}
block_1286:
{
lean_object* x_1275; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1275 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1274);
lean_dec(x_17);
if (lean_obj_tag(x_1275) == 0)
{
lean_object* x_1276; lean_object* x_1277; uint8_t x_1278; 
x_1276 = lean_ctor_get(x_1275, 1);
lean_inc(x_1276);
lean_dec(x_1275);
lean_inc(x_2);
x_1277 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__17(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1276);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1278 = !lean_is_exclusive(x_1277);
if (x_1278 == 0)
{
lean_object* x_1279; 
x_1279 = lean_ctor_get(x_1277, 0);
lean_dec(x_1279);
lean_ctor_set(x_1277, 0, x_2);
return x_1277;
}
else
{
lean_object* x_1280; lean_object* x_1281; 
x_1280 = lean_ctor_get(x_1277, 1);
lean_inc(x_1280);
lean_dec(x_1277);
x_1281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1281, 0, x_2);
lean_ctor_set(x_1281, 1, x_1280);
return x_1281;
}
}
else
{
uint8_t x_1282; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1282 = !lean_is_exclusive(x_1275);
if (x_1282 == 0)
{
return x_1275;
}
else
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; 
x_1283 = lean_ctor_get(x_1275, 0);
x_1284 = lean_ctor_get(x_1275, 1);
lean_inc(x_1284);
lean_inc(x_1283);
lean_dec(x_1275);
x_1285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1285, 0, x_1283);
lean_ctor_set(x_1285, 1, x_1284);
return x_1285;
}
}
}
}
}
}
else
{
lean_object* x_1294; lean_object* x_1295; 
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_3);
x_1294 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1295 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1294, x_128, x_4, x_5, x_6, x_7, x_8, x_9, x_1229);
if (lean_obj_tag(x_1295) == 0)
{
lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; uint8_t x_1300; lean_object* x_1301; lean_object* x_1302; 
x_1296 = lean_ctor_get(x_1295, 0);
lean_inc(x_1296);
x_1297 = lean_ctor_get(x_1295, 1);
lean_inc(x_1297);
lean_dec(x_1295);
x_1298 = lean_unsigned_to_nat(1u);
x_1299 = lean_nat_add(x_15, x_1298);
lean_dec(x_15);
x_1300 = 1;
lean_ctor_set(x_1, 3, x_1299);
lean_ctor_set_uint8(x_1, sizeof(void*)*8 + 1, x_1300);
lean_inc(x_1296);
x_1301 = l_Lean_mkApp(x_2, x_1296);
x_1302 = lean_expr_instantiate1(x_129, x_1296);
lean_dec(x_1296);
lean_dec(x_129);
x_2 = x_1301;
x_3 = x_1302;
x_10 = x_1297;
goto _start;
}
else
{
uint8_t x_1304; 
lean_free_object(x_1);
lean_dec(x_129);
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
x_1304 = !lean_is_exclusive(x_1295);
if (x_1304 == 0)
{
return x_1295;
}
else
{
lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; 
x_1305 = lean_ctor_get(x_1295, 0);
x_1306 = lean_ctor_get(x_1295, 1);
lean_inc(x_1306);
lean_inc(x_1305);
lean_dec(x_1295);
x_1307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1307, 0, x_1305);
lean_ctor_set(x_1307, 1, x_1306);
return x_1307;
}
}
}
}
else
{
uint8_t x_1308; 
lean_free_object(x_1);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
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
x_1308 = !lean_is_exclusive(x_1219);
if (x_1308 == 0)
{
return x_1219;
}
else
{
lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; 
x_1309 = lean_ctor_get(x_1219, 0);
x_1310 = lean_ctor_get(x_1219, 1);
lean_inc(x_1310);
lean_inc(x_1309);
lean_dec(x_1219);
x_1311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1311, 0, x_1309);
lean_ctor_set(x_1311, 1, x_1310);
return x_1311;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_1219) == 0)
{
lean_object* x_1312; lean_object* x_1313; uint8_t x_1314; 
x_1312 = lean_ctor_get(x_1219, 1);
lean_inc(x_1312);
lean_dec(x_1219);
x_1313 = lean_array_get_size(x_12);
x_1314 = lean_nat_dec_lt(x_15, x_1313);
lean_dec(x_1313);
if (x_1314 == 0)
{
uint8_t x_1315; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_1315 = l_Array_isEmpty___rarg(x_16);
if (x_1315 == 0)
{
lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_1316 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1316, 0, x_127);
x_1317 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1318 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1318, 0, x_1317);
lean_ctor_set(x_1318, 1, x_1316);
x_1319 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1320 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1320, 0, x_1318);
lean_ctor_set(x_1320, 1, x_1319);
x_1321 = x_16;
x_1322 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_131, x_1321);
x_1323 = x_1322;
x_1324 = l_Array_toList___rarg(x_1323);
lean_dec(x_1323);
x_1325 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_1324);
x_1326 = l_Array_HasRepr___rarg___closed__1;
x_1327 = lean_string_append(x_1326, x_1325);
lean_dec(x_1325);
x_1328 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1328, 0, x_1327);
x_1329 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1329, 0, x_1328);
x_1330 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1330, 0, x_1320);
lean_ctor_set(x_1330, 1, x_1329);
x_1331 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1330, x_4, x_5, x_6, x_7, x_8, x_9, x_1312);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1331;
}
else
{
lean_object* x_1332; uint8_t x_1333; 
lean_dec(x_127);
lean_dec(x_16);
x_1332 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1333 = l_Lean_checkTraceOption(x_22, x_1332);
lean_dec(x_22);
if (x_1333 == 0)
{
lean_object* x_1334; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1334 = x_1312;
goto block_1345;
}
else
{
lean_object* x_1346; lean_object* x_1347; 
x_1346 = lean_ctor_get(x_13, 0);
lean_inc(x_1346);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1347 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1346, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1312);
if (lean_obj_tag(x_1347) == 0)
{
lean_object* x_1348; 
x_1348 = lean_ctor_get(x_1347, 1);
lean_inc(x_1348);
lean_dec(x_1347);
x_1334 = x_1348;
goto block_1345;
}
else
{
lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; 
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
x_1349 = lean_ctor_get(x_1347, 0);
lean_inc(x_1349);
x_1350 = lean_ctor_get(x_1347, 1);
lean_inc(x_1350);
if (lean_is_exclusive(x_1347)) {
 lean_ctor_release(x_1347, 0);
 lean_ctor_release(x_1347, 1);
 x_1351 = x_1347;
} else {
 lean_dec_ref(x_1347);
 x_1351 = lean_box(0);
}
if (lean_is_scalar(x_1351)) {
 x_1352 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1352 = x_1351;
}
lean_ctor_set(x_1352, 0, x_1349);
lean_ctor_set(x_1352, 1, x_1350);
return x_1352;
}
}
block_1345:
{
lean_object* x_1335; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1335 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1334);
lean_dec(x_17);
if (lean_obj_tag(x_1335) == 0)
{
lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; lean_object* x_1340; 
x_1336 = lean_ctor_get(x_1335, 1);
lean_inc(x_1336);
lean_dec(x_1335);
lean_inc(x_2);
x_1337 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__16(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1336);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1338 = lean_ctor_get(x_1337, 1);
lean_inc(x_1338);
if (lean_is_exclusive(x_1337)) {
 lean_ctor_release(x_1337, 0);
 lean_ctor_release(x_1337, 1);
 x_1339 = x_1337;
} else {
 lean_dec_ref(x_1337);
 x_1339 = lean_box(0);
}
if (lean_is_scalar(x_1339)) {
 x_1340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1340 = x_1339;
}
lean_ctor_set(x_1340, 0, x_2);
lean_ctor_set(x_1340, 1, x_1338);
return x_1340;
}
else
{
lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1341 = lean_ctor_get(x_1335, 0);
lean_inc(x_1341);
x_1342 = lean_ctor_get(x_1335, 1);
lean_inc(x_1342);
if (lean_is_exclusive(x_1335)) {
 lean_ctor_release(x_1335, 0);
 lean_ctor_release(x_1335, 1);
 x_1343 = x_1335;
} else {
 lean_dec_ref(x_1335);
 x_1343 = lean_box(0);
}
if (lean_is_scalar(x_1343)) {
 x_1344 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1344 = x_1343;
}
lean_ctor_set(x_1344, 0, x_1341);
lean_ctor_set(x_1344, 1, x_1342);
return x_1344;
}
}
}
else
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; 
lean_inc(x_2);
x_1353 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1353, 0, x_2);
x_1354 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1332, x_1353, x_4, x_5, x_6, x_7, x_8, x_9, x_1312);
x_1355 = lean_ctor_get(x_1354, 1);
lean_inc(x_1355);
lean_dec(x_1354);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1356 = x_1355;
goto block_1367;
}
else
{
lean_object* x_1368; lean_object* x_1369; 
x_1368 = lean_ctor_get(x_13, 0);
lean_inc(x_1368);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1369 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1368, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1355);
if (lean_obj_tag(x_1369) == 0)
{
lean_object* x_1370; 
x_1370 = lean_ctor_get(x_1369, 1);
lean_inc(x_1370);
lean_dec(x_1369);
x_1356 = x_1370;
goto block_1367;
}
else
{
lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
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
x_1371 = lean_ctor_get(x_1369, 0);
lean_inc(x_1371);
x_1372 = lean_ctor_get(x_1369, 1);
lean_inc(x_1372);
if (lean_is_exclusive(x_1369)) {
 lean_ctor_release(x_1369, 0);
 lean_ctor_release(x_1369, 1);
 x_1373 = x_1369;
} else {
 lean_dec_ref(x_1369);
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
block_1367:
{
lean_object* x_1357; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1357 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1356);
lean_dec(x_17);
if (lean_obj_tag(x_1357) == 0)
{
lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; 
x_1358 = lean_ctor_get(x_1357, 1);
lean_inc(x_1358);
lean_dec(x_1357);
lean_inc(x_2);
x_1359 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__17(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1358);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1360 = lean_ctor_get(x_1359, 1);
lean_inc(x_1360);
if (lean_is_exclusive(x_1359)) {
 lean_ctor_release(x_1359, 0);
 lean_ctor_release(x_1359, 1);
 x_1361 = x_1359;
} else {
 lean_dec_ref(x_1359);
 x_1361 = lean_box(0);
}
if (lean_is_scalar(x_1361)) {
 x_1362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1362 = x_1361;
}
lean_ctor_set(x_1362, 0, x_2);
lean_ctor_set(x_1362, 1, x_1360);
return x_1362;
}
else
{
lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1363 = lean_ctor_get(x_1357, 0);
lean_inc(x_1363);
x_1364 = lean_ctor_get(x_1357, 1);
lean_inc(x_1364);
if (lean_is_exclusive(x_1357)) {
 lean_ctor_release(x_1357, 0);
 lean_ctor_release(x_1357, 1);
 x_1365 = x_1357;
} else {
 lean_dec_ref(x_1357);
 x_1365 = lean_box(0);
}
if (lean_is_scalar(x_1365)) {
 x_1366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1366 = x_1365;
}
lean_ctor_set(x_1366, 0, x_1363);
lean_ctor_set(x_1366, 1, x_1364);
return x_1366;
}
}
}
}
}
else
{
lean_object* x_1375; lean_object* x_1376; 
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_3);
x_1375 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1376 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1375, x_128, x_4, x_5, x_6, x_7, x_8, x_9, x_1312);
if (lean_obj_tag(x_1376) == 0)
{
lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; uint8_t x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; 
x_1377 = lean_ctor_get(x_1376, 0);
lean_inc(x_1377);
x_1378 = lean_ctor_get(x_1376, 1);
lean_inc(x_1378);
lean_dec(x_1376);
x_1379 = lean_unsigned_to_nat(1u);
x_1380 = lean_nat_add(x_15, x_1379);
lean_dec(x_15);
x_1381 = 1;
x_1382 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1382, 0, x_11);
lean_ctor_set(x_1382, 1, x_12);
lean_ctor_set(x_1382, 2, x_13);
lean_ctor_set(x_1382, 3, x_1380);
lean_ctor_set(x_1382, 4, x_16);
lean_ctor_set(x_1382, 5, x_17);
lean_ctor_set(x_1382, 6, x_18);
lean_ctor_set(x_1382, 7, x_19);
lean_ctor_set_uint8(x_1382, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1382, sizeof(void*)*8 + 1, x_1381);
lean_inc(x_1377);
x_1383 = l_Lean_mkApp(x_2, x_1377);
x_1384 = lean_expr_instantiate1(x_129, x_1377);
lean_dec(x_1377);
lean_dec(x_129);
x_1 = x_1382;
x_2 = x_1383;
x_3 = x_1384;
x_10 = x_1378;
goto _start;
}
else
{
lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; 
lean_dec(x_129);
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
x_1386 = lean_ctor_get(x_1376, 0);
lean_inc(x_1386);
x_1387 = lean_ctor_get(x_1376, 1);
lean_inc(x_1387);
if (lean_is_exclusive(x_1376)) {
 lean_ctor_release(x_1376, 0);
 lean_ctor_release(x_1376, 1);
 x_1388 = x_1376;
} else {
 lean_dec_ref(x_1376);
 x_1388 = lean_box(0);
}
if (lean_is_scalar(x_1388)) {
 x_1389 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1389 = x_1388;
}
lean_ctor_set(x_1389, 0, x_1386);
lean_ctor_set(x_1389, 1, x_1387);
return x_1389;
}
}
}
else
{
lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
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
x_1390 = lean_ctor_get(x_1219, 0);
lean_inc(x_1390);
x_1391 = lean_ctor_get(x_1219, 1);
lean_inc(x_1391);
if (lean_is_exclusive(x_1219)) {
 lean_ctor_release(x_1219, 0);
 lean_ctor_release(x_1219, 1);
 x_1392 = x_1219;
} else {
 lean_dec_ref(x_1219);
 x_1392 = lean_box(0);
}
if (lean_is_scalar(x_1392)) {
 x_1393 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1393 = x_1392;
}
lean_ctor_set(x_1393, 0, x_1390);
lean_ctor_set(x_1393, 1, x_1391);
return x_1393;
}
}
}
else
{
uint8_t x_1394; 
lean_dec(x_127);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_3);
x_1394 = !lean_is_exclusive(x_1);
if (x_1394 == 0)
{
lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; uint8_t x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; 
x_1395 = lean_ctor_get(x_1, 7);
lean_dec(x_1395);
x_1396 = lean_ctor_get(x_1, 6);
lean_dec(x_1396);
x_1397 = lean_ctor_get(x_1, 5);
lean_dec(x_1397);
x_1398 = lean_ctor_get(x_1, 4);
lean_dec(x_1398);
x_1399 = lean_ctor_get(x_1, 3);
lean_dec(x_1399);
x_1400 = lean_ctor_get(x_1, 2);
lean_dec(x_1400);
x_1401 = lean_ctor_get(x_1, 1);
lean_dec(x_1401);
x_1402 = lean_ctor_get(x_1, 0);
lean_dec(x_1402);
x_1403 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1403, 0, x_128);
x_1404 = 1;
x_1405 = lean_box(0);
lean_inc(x_6);
x_1406 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_1403, x_1404, x_1405, x_6, x_7, x_8, x_9, x_29);
x_1407 = lean_ctor_get(x_1406, 0);
lean_inc(x_1407);
x_1408 = lean_ctor_get(x_1406, 1);
lean_inc(x_1408);
lean_dec(x_1406);
x_1409 = lean_unsigned_to_nat(1u);
x_1410 = lean_nat_add(x_15, x_1409);
lean_dec(x_15);
x_1411 = l_Lean_Expr_mvarId_x21(x_1407);
x_1412 = lean_array_push(x_17, x_1411);
lean_ctor_set(x_1, 5, x_1412);
lean_ctor_set(x_1, 3, x_1410);
lean_inc(x_1407);
x_1413 = l_Lean_mkApp(x_2, x_1407);
x_1414 = lean_expr_instantiate1(x_129, x_1407);
lean_dec(x_1407);
lean_dec(x_129);
x_2 = x_1413;
x_3 = x_1414;
x_10 = x_1408;
goto _start;
}
else
{
lean_object* x_1416; uint8_t x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; 
lean_dec(x_1);
x_1416 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1416, 0, x_128);
x_1417 = 1;
x_1418 = lean_box(0);
lean_inc(x_6);
x_1419 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_1416, x_1417, x_1418, x_6, x_7, x_8, x_9, x_29);
x_1420 = lean_ctor_get(x_1419, 0);
lean_inc(x_1420);
x_1421 = lean_ctor_get(x_1419, 1);
lean_inc(x_1421);
lean_dec(x_1419);
x_1422 = lean_unsigned_to_nat(1u);
x_1423 = lean_nat_add(x_15, x_1422);
lean_dec(x_15);
x_1424 = l_Lean_Expr_mvarId_x21(x_1420);
x_1425 = lean_array_push(x_17, x_1424);
x_1426 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1426, 0, x_11);
lean_ctor_set(x_1426, 1, x_12);
lean_ctor_set(x_1426, 2, x_13);
lean_ctor_set(x_1426, 3, x_1423);
lean_ctor_set(x_1426, 4, x_16);
lean_ctor_set(x_1426, 5, x_1425);
lean_ctor_set(x_1426, 6, x_18);
lean_ctor_set(x_1426, 7, x_19);
lean_ctor_set_uint8(x_1426, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1426, sizeof(void*)*8 + 1, x_21);
lean_inc(x_1420);
x_1427 = l_Lean_mkApp(x_2, x_1420);
x_1428 = lean_expr_instantiate1(x_129, x_1420);
lean_dec(x_1420);
lean_dec(x_129);
x_1 = x_1426;
x_2 = x_1427;
x_3 = x_1428;
x_10 = x_1421;
goto _start;
}
}
}
}
default: 
{
lean_object* x_1430; uint8_t x_1431; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_1430 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_1431 = !lean_is_exclusive(x_1);
if (x_1431 == 0)
{
lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; 
x_1432 = lean_ctor_get(x_1, 7);
lean_dec(x_1432);
x_1433 = lean_ctor_get(x_1, 6);
lean_dec(x_1433);
x_1434 = lean_ctor_get(x_1, 5);
lean_dec(x_1434);
x_1435 = lean_ctor_get(x_1, 4);
lean_dec(x_1435);
x_1436 = lean_ctor_get(x_1, 3);
lean_dec(x_1436);
x_1437 = lean_ctor_get(x_1, 2);
lean_dec(x_1437);
x_1438 = lean_ctor_get(x_1, 1);
lean_dec(x_1438);
x_1439 = lean_ctor_get(x_1, 0);
lean_dec(x_1439);
if (lean_obj_tag(x_1430) == 0)
{
lean_object* x_1440; uint8_t x_1441; lean_object* x_1442; uint8_t x_1443; 
x_1440 = lean_ctor_get(x_1430, 1);
lean_inc(x_1440);
lean_dec(x_1430);
x_1441 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_ctor_set_uint8(x_1, sizeof(void*)*8 + 1, x_1441);
x_1442 = lean_array_get_size(x_12);
x_1443 = lean_nat_dec_lt(x_15, x_1442);
lean_dec(x_1442);
if (x_1443 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_1444; 
x_1444 = l_Lean_Expr_getOptParamDefault_x3f(x_128);
if (lean_obj_tag(x_1444) == 0)
{
lean_object* x_1445; 
x_1445 = l_Lean_Expr_getAutoParamTactic_x3f(x_128);
if (lean_obj_tag(x_1445) == 0)
{
uint8_t x_1446; 
lean_dec(x_1);
lean_dec(x_129);
lean_dec(x_128);
x_1446 = l_Array_isEmpty___rarg(x_16);
if (x_1446 == 0)
{
lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_1447 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1447, 0, x_127);
x_1448 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1449 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1449, 0, x_1448);
lean_ctor_set(x_1449, 1, x_1447);
x_1450 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1451 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1451, 0, x_1449);
lean_ctor_set(x_1451, 1, x_1450);
x_1452 = x_16;
x_1453 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_131, x_1452);
x_1454 = x_1453;
x_1455 = l_Array_toList___rarg(x_1454);
lean_dec(x_1454);
x_1456 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_1455);
x_1457 = l_Array_HasRepr___rarg___closed__1;
x_1458 = lean_string_append(x_1457, x_1456);
lean_dec(x_1456);
x_1459 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1459, 0, x_1458);
x_1460 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1460, 0, x_1459);
x_1461 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1461, 0, x_1451);
lean_ctor_set(x_1461, 1, x_1460);
x_1462 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1461, x_4, x_5, x_6, x_7, x_8, x_9, x_1440);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1462;
}
else
{
lean_object* x_1463; uint8_t x_1464; 
lean_dec(x_127);
lean_dec(x_16);
x_1463 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1464 = l_Lean_checkTraceOption(x_22, x_1463);
lean_dec(x_22);
if (x_1464 == 0)
{
lean_object* x_1465; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1465 = x_1440;
goto block_1477;
}
else
{
lean_object* x_1478; lean_object* x_1479; 
x_1478 = lean_ctor_get(x_13, 0);
lean_inc(x_1478);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1479 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1478, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1440);
if (lean_obj_tag(x_1479) == 0)
{
lean_object* x_1480; 
x_1480 = lean_ctor_get(x_1479, 1);
lean_inc(x_1480);
lean_dec(x_1479);
x_1465 = x_1480;
goto block_1477;
}
else
{
uint8_t x_1481; 
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
x_1481 = !lean_is_exclusive(x_1479);
if (x_1481 == 0)
{
return x_1479;
}
else
{
lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; 
x_1482 = lean_ctor_get(x_1479, 0);
x_1483 = lean_ctor_get(x_1479, 1);
lean_inc(x_1483);
lean_inc(x_1482);
lean_dec(x_1479);
x_1484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1484, 0, x_1482);
lean_ctor_set(x_1484, 1, x_1483);
return x_1484;
}
}
}
block_1477:
{
lean_object* x_1466; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1466 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1465);
lean_dec(x_17);
if (lean_obj_tag(x_1466) == 0)
{
lean_object* x_1467; lean_object* x_1468; uint8_t x_1469; 
x_1467 = lean_ctor_get(x_1466, 1);
lean_inc(x_1467);
lean_dec(x_1466);
lean_inc(x_2);
x_1468 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__18(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1467);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1469 = !lean_is_exclusive(x_1468);
if (x_1469 == 0)
{
lean_object* x_1470; 
x_1470 = lean_ctor_get(x_1468, 0);
lean_dec(x_1470);
lean_ctor_set(x_1468, 0, x_2);
return x_1468;
}
else
{
lean_object* x_1471; lean_object* x_1472; 
x_1471 = lean_ctor_get(x_1468, 1);
lean_inc(x_1471);
lean_dec(x_1468);
x_1472 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1472, 0, x_2);
lean_ctor_set(x_1472, 1, x_1471);
return x_1472;
}
}
else
{
uint8_t x_1473; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1473 = !lean_is_exclusive(x_1466);
if (x_1473 == 0)
{
return x_1466;
}
else
{
lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; 
x_1474 = lean_ctor_get(x_1466, 0);
x_1475 = lean_ctor_get(x_1466, 1);
lean_inc(x_1475);
lean_inc(x_1474);
lean_dec(x_1466);
x_1476 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1476, 0, x_1474);
lean_ctor_set(x_1476, 1, x_1475);
return x_1476;
}
}
}
}
else
{
lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; 
lean_inc(x_2);
x_1485 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1485, 0, x_2);
x_1486 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1463, x_1485, x_4, x_5, x_6, x_7, x_8, x_9, x_1440);
x_1487 = lean_ctor_get(x_1486, 1);
lean_inc(x_1487);
lean_dec(x_1486);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1488 = x_1487;
goto block_1500;
}
else
{
lean_object* x_1501; lean_object* x_1502; 
x_1501 = lean_ctor_get(x_13, 0);
lean_inc(x_1501);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1502 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1501, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1487);
if (lean_obj_tag(x_1502) == 0)
{
lean_object* x_1503; 
x_1503 = lean_ctor_get(x_1502, 1);
lean_inc(x_1503);
lean_dec(x_1502);
x_1488 = x_1503;
goto block_1500;
}
else
{
uint8_t x_1504; 
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
x_1504 = !lean_is_exclusive(x_1502);
if (x_1504 == 0)
{
return x_1502;
}
else
{
lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; 
x_1505 = lean_ctor_get(x_1502, 0);
x_1506 = lean_ctor_get(x_1502, 1);
lean_inc(x_1506);
lean_inc(x_1505);
lean_dec(x_1502);
x_1507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1507, 0, x_1505);
lean_ctor_set(x_1507, 1, x_1506);
return x_1507;
}
}
}
block_1500:
{
lean_object* x_1489; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1489 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1488);
lean_dec(x_17);
if (lean_obj_tag(x_1489) == 0)
{
lean_object* x_1490; lean_object* x_1491; uint8_t x_1492; 
x_1490 = lean_ctor_get(x_1489, 1);
lean_inc(x_1490);
lean_dec(x_1489);
lean_inc(x_2);
x_1491 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__19(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1490);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1492 = !lean_is_exclusive(x_1491);
if (x_1492 == 0)
{
lean_object* x_1493; 
x_1493 = lean_ctor_get(x_1491, 0);
lean_dec(x_1493);
lean_ctor_set(x_1491, 0, x_2);
return x_1491;
}
else
{
lean_object* x_1494; lean_object* x_1495; 
x_1494 = lean_ctor_get(x_1491, 1);
lean_inc(x_1494);
lean_dec(x_1491);
x_1495 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1495, 0, x_2);
lean_ctor_set(x_1495, 1, x_1494);
return x_1495;
}
}
else
{
uint8_t x_1496; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1496 = !lean_is_exclusive(x_1489);
if (x_1496 == 0)
{
return x_1489;
}
else
{
lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; 
x_1497 = lean_ctor_get(x_1489, 0);
x_1498 = lean_ctor_get(x_1489, 1);
lean_inc(x_1498);
lean_inc(x_1497);
lean_dec(x_1489);
x_1499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1499, 0, x_1497);
lean_ctor_set(x_1499, 1, x_1498);
return x_1499;
}
}
}
}
}
}
else
{
lean_object* x_1508; 
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_1508 = lean_ctor_get(x_1445, 0);
lean_inc(x_1508);
lean_dec(x_1445);
if (lean_obj_tag(x_1508) == 4)
{
lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; 
x_1509 = lean_ctor_get(x_1508, 0);
lean_inc(x_1509);
lean_dec(x_1508);
x_1510 = lean_st_ref_get(x_9, x_1440);
x_1511 = lean_ctor_get(x_1510, 0);
lean_inc(x_1511);
x_1512 = lean_ctor_get(x_1510, 1);
lean_inc(x_1512);
lean_dec(x_1510);
x_1513 = lean_ctor_get(x_1511, 0);
lean_inc(x_1513);
lean_dec(x_1511);
x_1514 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1513, x_1509);
if (lean_obj_tag(x_1514) == 0)
{
lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; 
lean_dec(x_1);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_11);
lean_dec(x_2);
x_1515 = lean_ctor_get(x_1514, 0);
lean_inc(x_1515);
lean_dec(x_1514);
x_1516 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1516, 0, x_1515);
x_1517 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1517, 0, x_1516);
x_1518 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1517, x_4, x_5, x_6, x_7, x_8, x_9, x_1512);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1518;
}
else
{
lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; 
x_1519 = lean_ctor_get(x_1514, 0);
lean_inc(x_1519);
lean_dec(x_1514);
x_1520 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_1512);
x_1521 = lean_ctor_get(x_1520, 1);
lean_inc(x_1521);
lean_dec(x_1520);
x_1522 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_1521);
x_1523 = lean_ctor_get(x_1522, 1);
lean_inc(x_1523);
lean_dec(x_1522);
x_1524 = l_Lean_Syntax_getArgs(x_1519);
lean_dec(x_1519);
x_1525 = l_Array_empty___closed__1;
x_1526 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1524, x_1524, x_131, x_1525);
lean_dec(x_1524);
x_1527 = l_Lean_nullKind___closed__2;
x_1528 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1528, 0, x_1527);
lean_ctor_set(x_1528, 1, x_1526);
x_1529 = lean_array_push(x_1525, x_1528);
x_1530 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__5;
x_1531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1531, 0, x_1530);
lean_ctor_set(x_1531, 1, x_1529);
x_1532 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_1533 = lean_array_push(x_1532, x_1531);
x_1534 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1535 = lean_array_push(x_1533, x_1534);
x_1536 = l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock___closed__2;
x_1537 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1537, 0, x_1536);
lean_ctor_set(x_1537, 1, x_1535);
x_1538 = lean_array_push(x_1525, x_1537);
x_1539 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1539, 0, x_1527);
lean_ctor_set(x_1539, 1, x_1538);
x_1540 = lean_array_push(x_1525, x_1539);
x_1541 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1541, 0, x_1530);
lean_ctor_set(x_1541, 1, x_1540);
x_1542 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1543 = lean_array_push(x_1542, x_1541);
x_1544 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_1545 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1545, 0, x_1544);
lean_ctor_set(x_1545, 1, x_1543);
x_1546 = l_Lean_Syntax_copyInfo(x_1545, x_11);
lean_dec(x_11);
x_1547 = l_Lean_Expr_getAppNumArgsAux___main(x_128, x_131);
x_1548 = lean_nat_sub(x_1547, x_131);
lean_dec(x_1547);
x_1549 = lean_unsigned_to_nat(1u);
x_1550 = lean_nat_sub(x_1548, x_1549);
lean_dec(x_1548);
x_1551 = l_Lean_Expr_getRevArg_x21___main(x_128, x_1550);
lean_dec(x_128);
x_1552 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1552, 0, x_1546);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1553 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1552, x_1551, x_4, x_5, x_6, x_7, x_8, x_9, x_1523);
if (lean_obj_tag(x_1553) == 0)
{
lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; 
x_1554 = lean_ctor_get(x_1553, 0);
lean_inc(x_1554);
x_1555 = lean_ctor_get(x_1553, 1);
lean_inc(x_1555);
lean_dec(x_1553);
lean_inc(x_1554);
x_1556 = l_Lean_mkApp(x_2, x_1554);
x_1557 = lean_expr_instantiate1(x_129, x_1554);
lean_dec(x_1554);
lean_dec(x_129);
x_2 = x_1556;
x_3 = x_1557;
x_10 = x_1555;
goto _start;
}
else
{
uint8_t x_1559; 
lean_dec(x_1);
lean_dec(x_129);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1559 = !lean_is_exclusive(x_1553);
if (x_1559 == 0)
{
return x_1553;
}
else
{
lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; 
x_1560 = lean_ctor_get(x_1553, 0);
x_1561 = lean_ctor_get(x_1553, 1);
lean_inc(x_1561);
lean_inc(x_1560);
lean_dec(x_1553);
x_1562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1562, 0, x_1560);
lean_ctor_set(x_1562, 1, x_1561);
return x_1562;
}
}
}
}
else
{
lean_object* x_1563; lean_object* x_1564; 
lean_dec(x_1508);
lean_dec(x_1);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_11);
lean_dec(x_2);
x_1563 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1564 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1563, x_4, x_5, x_6, x_7, x_8, x_9, x_1440);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1564;
}
}
}
else
{
lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_1565 = lean_ctor_get(x_1444, 0);
lean_inc(x_1565);
lean_dec(x_1444);
lean_inc(x_1565);
x_1566 = l_Lean_mkApp(x_2, x_1565);
x_1567 = lean_expr_instantiate1(x_129, x_1565);
lean_dec(x_1565);
lean_dec(x_129);
x_2 = x_1566;
x_3 = x_1567;
x_10 = x_1440;
goto _start;
}
}
else
{
uint8_t x_1569; 
lean_dec(x_1);
lean_dec(x_129);
lean_dec(x_128);
x_1569 = l_Array_isEmpty___rarg(x_16);
if (x_1569 == 0)
{
lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_1570 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1570, 0, x_127);
x_1571 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1572 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1572, 0, x_1571);
lean_ctor_set(x_1572, 1, x_1570);
x_1573 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1574 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1574, 0, x_1572);
lean_ctor_set(x_1574, 1, x_1573);
x_1575 = x_16;
x_1576 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_131, x_1575);
x_1577 = x_1576;
x_1578 = l_Array_toList___rarg(x_1577);
lean_dec(x_1577);
x_1579 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_1578);
x_1580 = l_Array_HasRepr___rarg___closed__1;
x_1581 = lean_string_append(x_1580, x_1579);
lean_dec(x_1579);
x_1582 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1582, 0, x_1581);
x_1583 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1583, 0, x_1582);
x_1584 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1584, 0, x_1574);
lean_ctor_set(x_1584, 1, x_1583);
x_1585 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1584, x_4, x_5, x_6, x_7, x_8, x_9, x_1440);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1585;
}
else
{
lean_object* x_1586; uint8_t x_1587; 
lean_dec(x_127);
lean_dec(x_16);
x_1586 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1587 = l_Lean_checkTraceOption(x_22, x_1586);
lean_dec(x_22);
if (x_1587 == 0)
{
lean_object* x_1588; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1588 = x_1440;
goto block_1600;
}
else
{
lean_object* x_1601; lean_object* x_1602; 
x_1601 = lean_ctor_get(x_13, 0);
lean_inc(x_1601);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1602 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1601, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1440);
if (lean_obj_tag(x_1602) == 0)
{
lean_object* x_1603; 
x_1603 = lean_ctor_get(x_1602, 1);
lean_inc(x_1603);
lean_dec(x_1602);
x_1588 = x_1603;
goto block_1600;
}
else
{
uint8_t x_1604; 
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
x_1604 = !lean_is_exclusive(x_1602);
if (x_1604 == 0)
{
return x_1602;
}
else
{
lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; 
x_1605 = lean_ctor_get(x_1602, 0);
x_1606 = lean_ctor_get(x_1602, 1);
lean_inc(x_1606);
lean_inc(x_1605);
lean_dec(x_1602);
x_1607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1607, 0, x_1605);
lean_ctor_set(x_1607, 1, x_1606);
return x_1607;
}
}
}
block_1600:
{
lean_object* x_1589; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1589 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1588);
lean_dec(x_17);
if (lean_obj_tag(x_1589) == 0)
{
lean_object* x_1590; lean_object* x_1591; uint8_t x_1592; 
x_1590 = lean_ctor_get(x_1589, 1);
lean_inc(x_1590);
lean_dec(x_1589);
lean_inc(x_2);
x_1591 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__20(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1590);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1592 = !lean_is_exclusive(x_1591);
if (x_1592 == 0)
{
lean_object* x_1593; 
x_1593 = lean_ctor_get(x_1591, 0);
lean_dec(x_1593);
lean_ctor_set(x_1591, 0, x_2);
return x_1591;
}
else
{
lean_object* x_1594; lean_object* x_1595; 
x_1594 = lean_ctor_get(x_1591, 1);
lean_inc(x_1594);
lean_dec(x_1591);
x_1595 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1595, 0, x_2);
lean_ctor_set(x_1595, 1, x_1594);
return x_1595;
}
}
else
{
uint8_t x_1596; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1596 = !lean_is_exclusive(x_1589);
if (x_1596 == 0)
{
return x_1589;
}
else
{
lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; 
x_1597 = lean_ctor_get(x_1589, 0);
x_1598 = lean_ctor_get(x_1589, 1);
lean_inc(x_1598);
lean_inc(x_1597);
lean_dec(x_1589);
x_1599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1599, 0, x_1597);
lean_ctor_set(x_1599, 1, x_1598);
return x_1599;
}
}
}
}
else
{
lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; 
lean_inc(x_2);
x_1608 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1608, 0, x_2);
x_1609 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1586, x_1608, x_4, x_5, x_6, x_7, x_8, x_9, x_1440);
x_1610 = lean_ctor_get(x_1609, 1);
lean_inc(x_1610);
lean_dec(x_1609);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1611 = x_1610;
goto block_1623;
}
else
{
lean_object* x_1624; lean_object* x_1625; 
x_1624 = lean_ctor_get(x_13, 0);
lean_inc(x_1624);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1625 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1624, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1610);
if (lean_obj_tag(x_1625) == 0)
{
lean_object* x_1626; 
x_1626 = lean_ctor_get(x_1625, 1);
lean_inc(x_1626);
lean_dec(x_1625);
x_1611 = x_1626;
goto block_1623;
}
else
{
uint8_t x_1627; 
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
x_1627 = !lean_is_exclusive(x_1625);
if (x_1627 == 0)
{
return x_1625;
}
else
{
lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; 
x_1628 = lean_ctor_get(x_1625, 0);
x_1629 = lean_ctor_get(x_1625, 1);
lean_inc(x_1629);
lean_inc(x_1628);
lean_dec(x_1625);
x_1630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1630, 0, x_1628);
lean_ctor_set(x_1630, 1, x_1629);
return x_1630;
}
}
}
block_1623:
{
lean_object* x_1612; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1612 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1611);
lean_dec(x_17);
if (lean_obj_tag(x_1612) == 0)
{
lean_object* x_1613; lean_object* x_1614; uint8_t x_1615; 
x_1613 = lean_ctor_get(x_1612, 1);
lean_inc(x_1613);
lean_dec(x_1612);
lean_inc(x_2);
x_1614 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__21(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1613);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1615 = !lean_is_exclusive(x_1614);
if (x_1615 == 0)
{
lean_object* x_1616; 
x_1616 = lean_ctor_get(x_1614, 0);
lean_dec(x_1616);
lean_ctor_set(x_1614, 0, x_2);
return x_1614;
}
else
{
lean_object* x_1617; lean_object* x_1618; 
x_1617 = lean_ctor_get(x_1614, 1);
lean_inc(x_1617);
lean_dec(x_1614);
x_1618 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1618, 0, x_2);
lean_ctor_set(x_1618, 1, x_1617);
return x_1618;
}
}
else
{
uint8_t x_1619; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1619 = !lean_is_exclusive(x_1612);
if (x_1619 == 0)
{
return x_1612;
}
else
{
lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; 
x_1620 = lean_ctor_get(x_1612, 0);
x_1621 = lean_ctor_get(x_1612, 1);
lean_inc(x_1621);
lean_inc(x_1620);
lean_dec(x_1612);
x_1622 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1622, 0, x_1620);
lean_ctor_set(x_1622, 1, x_1621);
return x_1622;
}
}
}
}
}
}
}
else
{
lean_object* x_1631; lean_object* x_1632; 
lean_dec(x_1);
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_3);
x_1631 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1632 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1631, x_128, x_4, x_5, x_6, x_7, x_8, x_9, x_1440);
if (lean_obj_tag(x_1632) == 0)
{
lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; 
x_1633 = lean_ctor_get(x_1632, 0);
lean_inc(x_1633);
x_1634 = lean_ctor_get(x_1632, 1);
lean_inc(x_1634);
lean_dec(x_1632);
x_1635 = lean_unsigned_to_nat(1u);
x_1636 = lean_nat_add(x_15, x_1635);
lean_dec(x_15);
x_1637 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1637, 0, x_11);
lean_ctor_set(x_1637, 1, x_12);
lean_ctor_set(x_1637, 2, x_13);
lean_ctor_set(x_1637, 3, x_1636);
lean_ctor_set(x_1637, 4, x_16);
lean_ctor_set(x_1637, 5, x_17);
lean_ctor_set(x_1637, 6, x_18);
lean_ctor_set(x_1637, 7, x_19);
lean_ctor_set_uint8(x_1637, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1637, sizeof(void*)*8 + 1, x_1441);
lean_inc(x_1633);
x_1638 = l_Lean_mkApp(x_2, x_1633);
x_1639 = lean_expr_instantiate1(x_129, x_1633);
lean_dec(x_1633);
lean_dec(x_129);
x_1 = x_1637;
x_2 = x_1638;
x_3 = x_1639;
x_10 = x_1634;
goto _start;
}
else
{
uint8_t x_1641; 
lean_dec(x_129);
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
x_1641 = !lean_is_exclusive(x_1632);
if (x_1641 == 0)
{
return x_1632;
}
else
{
lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; 
x_1642 = lean_ctor_get(x_1632, 0);
x_1643 = lean_ctor_get(x_1632, 1);
lean_inc(x_1643);
lean_inc(x_1642);
lean_dec(x_1632);
x_1644 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1644, 0, x_1642);
lean_ctor_set(x_1644, 1, x_1643);
return x_1644;
}
}
}
}
else
{
uint8_t x_1645; 
lean_free_object(x_1);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
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
x_1645 = !lean_is_exclusive(x_1430);
if (x_1645 == 0)
{
return x_1430;
}
else
{
lean_object* x_1646; lean_object* x_1647; lean_object* x_1648; 
x_1646 = lean_ctor_get(x_1430, 0);
x_1647 = lean_ctor_get(x_1430, 1);
lean_inc(x_1647);
lean_inc(x_1646);
lean_dec(x_1430);
x_1648 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1648, 0, x_1646);
lean_ctor_set(x_1648, 1, x_1647);
return x_1648;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_1430) == 0)
{
lean_object* x_1649; uint8_t x_1650; lean_object* x_1651; lean_object* x_1652; uint8_t x_1653; 
x_1649 = lean_ctor_get(x_1430, 1);
lean_inc(x_1649);
lean_dec(x_1430);
x_1650 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_1651 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1651, 0, x_11);
lean_ctor_set(x_1651, 1, x_12);
lean_ctor_set(x_1651, 2, x_13);
lean_ctor_set(x_1651, 3, x_15);
lean_ctor_set(x_1651, 4, x_16);
lean_ctor_set(x_1651, 5, x_17);
lean_ctor_set(x_1651, 6, x_18);
lean_ctor_set(x_1651, 7, x_19);
lean_ctor_set_uint8(x_1651, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1651, sizeof(void*)*8 + 1, x_1650);
x_1652 = lean_array_get_size(x_12);
x_1653 = lean_nat_dec_lt(x_15, x_1652);
lean_dec(x_1652);
if (x_1653 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_1654; 
x_1654 = l_Lean_Expr_getOptParamDefault_x3f(x_128);
if (lean_obj_tag(x_1654) == 0)
{
lean_object* x_1655; 
x_1655 = l_Lean_Expr_getAutoParamTactic_x3f(x_128);
if (lean_obj_tag(x_1655) == 0)
{
uint8_t x_1656; 
lean_dec(x_1651);
lean_dec(x_129);
lean_dec(x_128);
x_1656 = l_Array_isEmpty___rarg(x_16);
if (x_1656 == 0)
{
lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_1657 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1657, 0, x_127);
x_1658 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1659 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1659, 0, x_1658);
lean_ctor_set(x_1659, 1, x_1657);
x_1660 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1661 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1661, 0, x_1659);
lean_ctor_set(x_1661, 1, x_1660);
x_1662 = x_16;
x_1663 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_131, x_1662);
x_1664 = x_1663;
x_1665 = l_Array_toList___rarg(x_1664);
lean_dec(x_1664);
x_1666 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_1665);
x_1667 = l_Array_HasRepr___rarg___closed__1;
x_1668 = lean_string_append(x_1667, x_1666);
lean_dec(x_1666);
x_1669 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1669, 0, x_1668);
x_1670 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1670, 0, x_1669);
x_1671 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1671, 0, x_1661);
lean_ctor_set(x_1671, 1, x_1670);
x_1672 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1671, x_4, x_5, x_6, x_7, x_8, x_9, x_1649);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1672;
}
else
{
lean_object* x_1673; uint8_t x_1674; 
lean_dec(x_127);
lean_dec(x_16);
x_1673 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1674 = l_Lean_checkTraceOption(x_22, x_1673);
lean_dec(x_22);
if (x_1674 == 0)
{
lean_object* x_1675; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1675 = x_1649;
goto block_1686;
}
else
{
lean_object* x_1687; lean_object* x_1688; 
x_1687 = lean_ctor_get(x_13, 0);
lean_inc(x_1687);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1688 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1687, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1649);
if (lean_obj_tag(x_1688) == 0)
{
lean_object* x_1689; 
x_1689 = lean_ctor_get(x_1688, 1);
lean_inc(x_1689);
lean_dec(x_1688);
x_1675 = x_1689;
goto block_1686;
}
else
{
lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; 
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
x_1690 = lean_ctor_get(x_1688, 0);
lean_inc(x_1690);
x_1691 = lean_ctor_get(x_1688, 1);
lean_inc(x_1691);
if (lean_is_exclusive(x_1688)) {
 lean_ctor_release(x_1688, 0);
 lean_ctor_release(x_1688, 1);
 x_1692 = x_1688;
} else {
 lean_dec_ref(x_1688);
 x_1692 = lean_box(0);
}
if (lean_is_scalar(x_1692)) {
 x_1693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1693 = x_1692;
}
lean_ctor_set(x_1693, 0, x_1690);
lean_ctor_set(x_1693, 1, x_1691);
return x_1693;
}
}
block_1686:
{
lean_object* x_1676; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1676 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1675);
lean_dec(x_17);
if (lean_obj_tag(x_1676) == 0)
{
lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; 
x_1677 = lean_ctor_get(x_1676, 1);
lean_inc(x_1677);
lean_dec(x_1676);
lean_inc(x_2);
x_1678 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__18(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1677);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1679 = lean_ctor_get(x_1678, 1);
lean_inc(x_1679);
if (lean_is_exclusive(x_1678)) {
 lean_ctor_release(x_1678, 0);
 lean_ctor_release(x_1678, 1);
 x_1680 = x_1678;
} else {
 lean_dec_ref(x_1678);
 x_1680 = lean_box(0);
}
if (lean_is_scalar(x_1680)) {
 x_1681 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1681 = x_1680;
}
lean_ctor_set(x_1681, 0, x_2);
lean_ctor_set(x_1681, 1, x_1679);
return x_1681;
}
else
{
lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1682 = lean_ctor_get(x_1676, 0);
lean_inc(x_1682);
x_1683 = lean_ctor_get(x_1676, 1);
lean_inc(x_1683);
if (lean_is_exclusive(x_1676)) {
 lean_ctor_release(x_1676, 0);
 lean_ctor_release(x_1676, 1);
 x_1684 = x_1676;
} else {
 lean_dec_ref(x_1676);
 x_1684 = lean_box(0);
}
if (lean_is_scalar(x_1684)) {
 x_1685 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1685 = x_1684;
}
lean_ctor_set(x_1685, 0, x_1682);
lean_ctor_set(x_1685, 1, x_1683);
return x_1685;
}
}
}
else
{
lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; 
lean_inc(x_2);
x_1694 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1694, 0, x_2);
x_1695 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1673, x_1694, x_4, x_5, x_6, x_7, x_8, x_9, x_1649);
x_1696 = lean_ctor_get(x_1695, 1);
lean_inc(x_1696);
lean_dec(x_1695);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1697 = x_1696;
goto block_1708;
}
else
{
lean_object* x_1709; lean_object* x_1710; 
x_1709 = lean_ctor_get(x_13, 0);
lean_inc(x_1709);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1710 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1709, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1696);
if (lean_obj_tag(x_1710) == 0)
{
lean_object* x_1711; 
x_1711 = lean_ctor_get(x_1710, 1);
lean_inc(x_1711);
lean_dec(x_1710);
x_1697 = x_1711;
goto block_1708;
}
else
{
lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; 
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
x_1712 = lean_ctor_get(x_1710, 0);
lean_inc(x_1712);
x_1713 = lean_ctor_get(x_1710, 1);
lean_inc(x_1713);
if (lean_is_exclusive(x_1710)) {
 lean_ctor_release(x_1710, 0);
 lean_ctor_release(x_1710, 1);
 x_1714 = x_1710;
} else {
 lean_dec_ref(x_1710);
 x_1714 = lean_box(0);
}
if (lean_is_scalar(x_1714)) {
 x_1715 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1715 = x_1714;
}
lean_ctor_set(x_1715, 0, x_1712);
lean_ctor_set(x_1715, 1, x_1713);
return x_1715;
}
}
block_1708:
{
lean_object* x_1698; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1698 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1697);
lean_dec(x_17);
if (lean_obj_tag(x_1698) == 0)
{
lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; 
x_1699 = lean_ctor_get(x_1698, 1);
lean_inc(x_1699);
lean_dec(x_1698);
lean_inc(x_2);
x_1700 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__19(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1699);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1701 = lean_ctor_get(x_1700, 1);
lean_inc(x_1701);
if (lean_is_exclusive(x_1700)) {
 lean_ctor_release(x_1700, 0);
 lean_ctor_release(x_1700, 1);
 x_1702 = x_1700;
} else {
 lean_dec_ref(x_1700);
 x_1702 = lean_box(0);
}
if (lean_is_scalar(x_1702)) {
 x_1703 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1703 = x_1702;
}
lean_ctor_set(x_1703, 0, x_2);
lean_ctor_set(x_1703, 1, x_1701);
return x_1703;
}
else
{
lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1704 = lean_ctor_get(x_1698, 0);
lean_inc(x_1704);
x_1705 = lean_ctor_get(x_1698, 1);
lean_inc(x_1705);
if (lean_is_exclusive(x_1698)) {
 lean_ctor_release(x_1698, 0);
 lean_ctor_release(x_1698, 1);
 x_1706 = x_1698;
} else {
 lean_dec_ref(x_1698);
 x_1706 = lean_box(0);
}
if (lean_is_scalar(x_1706)) {
 x_1707 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1707 = x_1706;
}
lean_ctor_set(x_1707, 0, x_1704);
lean_ctor_set(x_1707, 1, x_1705);
return x_1707;
}
}
}
}
}
else
{
lean_object* x_1716; 
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_1716 = lean_ctor_get(x_1655, 0);
lean_inc(x_1716);
lean_dec(x_1655);
if (lean_obj_tag(x_1716) == 4)
{
lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; 
x_1717 = lean_ctor_get(x_1716, 0);
lean_inc(x_1717);
lean_dec(x_1716);
x_1718 = lean_st_ref_get(x_9, x_1649);
x_1719 = lean_ctor_get(x_1718, 0);
lean_inc(x_1719);
x_1720 = lean_ctor_get(x_1718, 1);
lean_inc(x_1720);
lean_dec(x_1718);
x_1721 = lean_ctor_get(x_1719, 0);
lean_inc(x_1721);
lean_dec(x_1719);
x_1722 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_1721, x_1717);
if (lean_obj_tag(x_1722) == 0)
{
lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; 
lean_dec(x_1651);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_11);
lean_dec(x_2);
x_1723 = lean_ctor_get(x_1722, 0);
lean_inc(x_1723);
lean_dec(x_1722);
x_1724 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1724, 0, x_1723);
x_1725 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1725, 0, x_1724);
x_1726 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1725, x_4, x_5, x_6, x_7, x_8, x_9, x_1720);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1726;
}
else
{
lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; 
x_1727 = lean_ctor_get(x_1722, 0);
lean_inc(x_1727);
lean_dec(x_1722);
x_1728 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_1720);
x_1729 = lean_ctor_get(x_1728, 1);
lean_inc(x_1729);
lean_dec(x_1728);
x_1730 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_1729);
x_1731 = lean_ctor_get(x_1730, 1);
lean_inc(x_1731);
lean_dec(x_1730);
x_1732 = l_Lean_Syntax_getArgs(x_1727);
lean_dec(x_1727);
x_1733 = l_Array_empty___closed__1;
x_1734 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1732, x_1732, x_131, x_1733);
lean_dec(x_1732);
x_1735 = l_Lean_nullKind___closed__2;
x_1736 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1736, 0, x_1735);
lean_ctor_set(x_1736, 1, x_1734);
x_1737 = lean_array_push(x_1733, x_1736);
x_1738 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__5;
x_1739 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1739, 0, x_1738);
lean_ctor_set(x_1739, 1, x_1737);
x_1740 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_1741 = lean_array_push(x_1740, x_1739);
x_1742 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_1743 = lean_array_push(x_1741, x_1742);
x_1744 = l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock___closed__2;
x_1745 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1745, 0, x_1744);
lean_ctor_set(x_1745, 1, x_1743);
x_1746 = lean_array_push(x_1733, x_1745);
x_1747 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1747, 0, x_1735);
lean_ctor_set(x_1747, 1, x_1746);
x_1748 = lean_array_push(x_1733, x_1747);
x_1749 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1749, 0, x_1738);
lean_ctor_set(x_1749, 1, x_1748);
x_1750 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_1751 = lean_array_push(x_1750, x_1749);
x_1752 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_1753 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1753, 0, x_1752);
lean_ctor_set(x_1753, 1, x_1751);
x_1754 = l_Lean_Syntax_copyInfo(x_1753, x_11);
lean_dec(x_11);
x_1755 = l_Lean_Expr_getAppNumArgsAux___main(x_128, x_131);
x_1756 = lean_nat_sub(x_1755, x_131);
lean_dec(x_1755);
x_1757 = lean_unsigned_to_nat(1u);
x_1758 = lean_nat_sub(x_1756, x_1757);
lean_dec(x_1756);
x_1759 = l_Lean_Expr_getRevArg_x21___main(x_128, x_1758);
lean_dec(x_128);
x_1760 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1760, 0, x_1754);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1761 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1760, x_1759, x_4, x_5, x_6, x_7, x_8, x_9, x_1731);
if (lean_obj_tag(x_1761) == 0)
{
lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; 
x_1762 = lean_ctor_get(x_1761, 0);
lean_inc(x_1762);
x_1763 = lean_ctor_get(x_1761, 1);
lean_inc(x_1763);
lean_dec(x_1761);
lean_inc(x_1762);
x_1764 = l_Lean_mkApp(x_2, x_1762);
x_1765 = lean_expr_instantiate1(x_129, x_1762);
lean_dec(x_1762);
lean_dec(x_129);
x_1 = x_1651;
x_2 = x_1764;
x_3 = x_1765;
x_10 = x_1763;
goto _start;
}
else
{
lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; 
lean_dec(x_1651);
lean_dec(x_129);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1767 = lean_ctor_get(x_1761, 0);
lean_inc(x_1767);
x_1768 = lean_ctor_get(x_1761, 1);
lean_inc(x_1768);
if (lean_is_exclusive(x_1761)) {
 lean_ctor_release(x_1761, 0);
 lean_ctor_release(x_1761, 1);
 x_1769 = x_1761;
} else {
 lean_dec_ref(x_1761);
 x_1769 = lean_box(0);
}
if (lean_is_scalar(x_1769)) {
 x_1770 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1770 = x_1769;
}
lean_ctor_set(x_1770, 0, x_1767);
lean_ctor_set(x_1770, 1, x_1768);
return x_1770;
}
}
}
else
{
lean_object* x_1771; lean_object* x_1772; 
lean_dec(x_1716);
lean_dec(x_1651);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_11);
lean_dec(x_2);
x_1771 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_1772 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1771, x_4, x_5, x_6, x_7, x_8, x_9, x_1649);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1772;
}
}
}
else
{
lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_1773 = lean_ctor_get(x_1654, 0);
lean_inc(x_1773);
lean_dec(x_1654);
lean_inc(x_1773);
x_1774 = l_Lean_mkApp(x_2, x_1773);
x_1775 = lean_expr_instantiate1(x_129, x_1773);
lean_dec(x_1773);
lean_dec(x_129);
x_1 = x_1651;
x_2 = x_1774;
x_3 = x_1775;
x_10 = x_1649;
goto _start;
}
}
else
{
uint8_t x_1777; 
lean_dec(x_1651);
lean_dec(x_129);
lean_dec(x_128);
x_1777 = l_Array_isEmpty___rarg(x_16);
if (x_1777 == 0)
{
lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_1778 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_1778, 0, x_127);
x_1779 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_1780 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1780, 0, x_1779);
lean_ctor_set(x_1780, 1, x_1778);
x_1781 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_1782 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1782, 0, x_1780);
lean_ctor_set(x_1782, 1, x_1781);
x_1783 = x_16;
x_1784 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_131, x_1783);
x_1785 = x_1784;
x_1786 = l_Array_toList___rarg(x_1785);
lean_dec(x_1785);
x_1787 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_1786);
x_1788 = l_Array_HasRepr___rarg___closed__1;
x_1789 = lean_string_append(x_1788, x_1787);
lean_dec(x_1787);
x_1790 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1790, 0, x_1789);
x_1791 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1791, 0, x_1790);
x_1792 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1792, 0, x_1782);
lean_ctor_set(x_1792, 1, x_1791);
x_1793 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1792, x_4, x_5, x_6, x_7, x_8, x_9, x_1649);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_1793;
}
else
{
lean_object* x_1794; uint8_t x_1795; 
lean_dec(x_127);
lean_dec(x_16);
x_1794 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1795 = l_Lean_checkTraceOption(x_22, x_1794);
lean_dec(x_22);
if (x_1795 == 0)
{
lean_object* x_1796; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1796 = x_1649;
goto block_1807;
}
else
{
lean_object* x_1808; lean_object* x_1809; 
x_1808 = lean_ctor_get(x_13, 0);
lean_inc(x_1808);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1809 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1808, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1649);
if (lean_obj_tag(x_1809) == 0)
{
lean_object* x_1810; 
x_1810 = lean_ctor_get(x_1809, 1);
lean_inc(x_1810);
lean_dec(x_1809);
x_1796 = x_1810;
goto block_1807;
}
else
{
lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; lean_object* x_1814; 
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
x_1811 = lean_ctor_get(x_1809, 0);
lean_inc(x_1811);
x_1812 = lean_ctor_get(x_1809, 1);
lean_inc(x_1812);
if (lean_is_exclusive(x_1809)) {
 lean_ctor_release(x_1809, 0);
 lean_ctor_release(x_1809, 1);
 x_1813 = x_1809;
} else {
 lean_dec_ref(x_1809);
 x_1813 = lean_box(0);
}
if (lean_is_scalar(x_1813)) {
 x_1814 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1814 = x_1813;
}
lean_ctor_set(x_1814, 0, x_1811);
lean_ctor_set(x_1814, 1, x_1812);
return x_1814;
}
}
block_1807:
{
lean_object* x_1797; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1797 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1796);
lean_dec(x_17);
if (lean_obj_tag(x_1797) == 0)
{
lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; 
x_1798 = lean_ctor_get(x_1797, 1);
lean_inc(x_1798);
lean_dec(x_1797);
lean_inc(x_2);
x_1799 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__20(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1798);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1800 = lean_ctor_get(x_1799, 1);
lean_inc(x_1800);
if (lean_is_exclusive(x_1799)) {
 lean_ctor_release(x_1799, 0);
 lean_ctor_release(x_1799, 1);
 x_1801 = x_1799;
} else {
 lean_dec_ref(x_1799);
 x_1801 = lean_box(0);
}
if (lean_is_scalar(x_1801)) {
 x_1802 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1802 = x_1801;
}
lean_ctor_set(x_1802, 0, x_2);
lean_ctor_set(x_1802, 1, x_1800);
return x_1802;
}
else
{
lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1803 = lean_ctor_get(x_1797, 0);
lean_inc(x_1803);
x_1804 = lean_ctor_get(x_1797, 1);
lean_inc(x_1804);
if (lean_is_exclusive(x_1797)) {
 lean_ctor_release(x_1797, 0);
 lean_ctor_release(x_1797, 1);
 x_1805 = x_1797;
} else {
 lean_dec_ref(x_1797);
 x_1805 = lean_box(0);
}
if (lean_is_scalar(x_1805)) {
 x_1806 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1806 = x_1805;
}
lean_ctor_set(x_1806, 0, x_1803);
lean_ctor_set(x_1806, 1, x_1804);
return x_1806;
}
}
}
else
{
lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; 
lean_inc(x_2);
x_1815 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1815, 0, x_2);
x_1816 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1794, x_1815, x_4, x_5, x_6, x_7, x_8, x_9, x_1649);
x_1817 = lean_ctor_get(x_1816, 1);
lean_inc(x_1817);
lean_dec(x_1816);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1818 = x_1817;
goto block_1829;
}
else
{
lean_object* x_1830; lean_object* x_1831; 
x_1830 = lean_ctor_get(x_13, 0);
lean_inc(x_1830);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1831 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1830, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1817);
if (lean_obj_tag(x_1831) == 0)
{
lean_object* x_1832; 
x_1832 = lean_ctor_get(x_1831, 1);
lean_inc(x_1832);
lean_dec(x_1831);
x_1818 = x_1832;
goto block_1829;
}
else
{
lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; 
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
x_1833 = lean_ctor_get(x_1831, 0);
lean_inc(x_1833);
x_1834 = lean_ctor_get(x_1831, 1);
lean_inc(x_1834);
if (lean_is_exclusive(x_1831)) {
 lean_ctor_release(x_1831, 0);
 lean_ctor_release(x_1831, 1);
 x_1835 = x_1831;
} else {
 lean_dec_ref(x_1831);
 x_1835 = lean_box(0);
}
if (lean_is_scalar(x_1835)) {
 x_1836 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1836 = x_1835;
}
lean_ctor_set(x_1836, 0, x_1833);
lean_ctor_set(x_1836, 1, x_1834);
return x_1836;
}
}
block_1829:
{
lean_object* x_1819; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1819 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1818);
lean_dec(x_17);
if (lean_obj_tag(x_1819) == 0)
{
lean_object* x_1820; lean_object* x_1821; lean_object* x_1822; lean_object* x_1823; lean_object* x_1824; 
x_1820 = lean_ctor_get(x_1819, 1);
lean_inc(x_1820);
lean_dec(x_1819);
lean_inc(x_2);
x_1821 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__21(x_2, x_11, x_19, x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_1820);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1822 = lean_ctor_get(x_1821, 1);
lean_inc(x_1822);
if (lean_is_exclusive(x_1821)) {
 lean_ctor_release(x_1821, 0);
 lean_ctor_release(x_1821, 1);
 x_1823 = x_1821;
} else {
 lean_dec_ref(x_1821);
 x_1823 = lean_box(0);
}
if (lean_is_scalar(x_1823)) {
 x_1824 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1824 = x_1823;
}
lean_ctor_set(x_1824, 0, x_2);
lean_ctor_set(x_1824, 1, x_1822);
return x_1824;
}
else
{
lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1825 = lean_ctor_get(x_1819, 0);
lean_inc(x_1825);
x_1826 = lean_ctor_get(x_1819, 1);
lean_inc(x_1826);
if (lean_is_exclusive(x_1819)) {
 lean_ctor_release(x_1819, 0);
 lean_ctor_release(x_1819, 1);
 x_1827 = x_1819;
} else {
 lean_dec_ref(x_1819);
 x_1827 = lean_box(0);
}
if (lean_is_scalar(x_1827)) {
 x_1828 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1828 = x_1827;
}
lean_ctor_set(x_1828, 0, x_1825);
lean_ctor_set(x_1828, 1, x_1826);
return x_1828;
}
}
}
}
}
}
else
{
lean_object* x_1837; lean_object* x_1838; 
lean_dec(x_1651);
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_3);
x_1837 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1838 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1837, x_128, x_4, x_5, x_6, x_7, x_8, x_9, x_1649);
if (lean_obj_tag(x_1838) == 0)
{
lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; 
x_1839 = lean_ctor_get(x_1838, 0);
lean_inc(x_1839);
x_1840 = lean_ctor_get(x_1838, 1);
lean_inc(x_1840);
lean_dec(x_1838);
x_1841 = lean_unsigned_to_nat(1u);
x_1842 = lean_nat_add(x_15, x_1841);
lean_dec(x_15);
x_1843 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1843, 0, x_11);
lean_ctor_set(x_1843, 1, x_12);
lean_ctor_set(x_1843, 2, x_13);
lean_ctor_set(x_1843, 3, x_1842);
lean_ctor_set(x_1843, 4, x_16);
lean_ctor_set(x_1843, 5, x_17);
lean_ctor_set(x_1843, 6, x_18);
lean_ctor_set(x_1843, 7, x_19);
lean_ctor_set_uint8(x_1843, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1843, sizeof(void*)*8 + 1, x_1650);
lean_inc(x_1839);
x_1844 = l_Lean_mkApp(x_2, x_1839);
x_1845 = lean_expr_instantiate1(x_129, x_1839);
lean_dec(x_1839);
lean_dec(x_129);
x_1 = x_1843;
x_2 = x_1844;
x_3 = x_1845;
x_10 = x_1840;
goto _start;
}
else
{
lean_object* x_1847; lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; 
lean_dec(x_129);
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
x_1847 = lean_ctor_get(x_1838, 0);
lean_inc(x_1847);
x_1848 = lean_ctor_get(x_1838, 1);
lean_inc(x_1848);
if (lean_is_exclusive(x_1838)) {
 lean_ctor_release(x_1838, 0);
 lean_ctor_release(x_1838, 1);
 x_1849 = x_1838;
} else {
 lean_dec_ref(x_1838);
 x_1849 = lean_box(0);
}
if (lean_is_scalar(x_1849)) {
 x_1850 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1850 = x_1849;
}
lean_ctor_set(x_1850, 0, x_1847);
lean_ctor_set(x_1850, 1, x_1848);
return x_1850;
}
}
}
else
{
lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
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
x_1851 = lean_ctor_get(x_1430, 0);
lean_inc(x_1851);
x_1852 = lean_ctor_get(x_1430, 1);
lean_inc(x_1852);
if (lean_is_exclusive(x_1430)) {
 lean_ctor_release(x_1430, 0);
 lean_ctor_release(x_1430, 1);
 x_1853 = x_1430;
} else {
 lean_dec_ref(x_1430);
 x_1853 = lean_box(0);
}
if (lean_is_scalar(x_1853)) {
 x_1854 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1854 = x_1853;
}
lean_ctor_set(x_1854, 0, x_1851);
lean_ctor_set(x_1854, 1, x_1852);
return x_1854;
}
}
}
}
}
else
{
lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; 
lean_dec(x_127);
lean_dec(x_22);
lean_dec(x_3);
x_1855 = lean_ctor_get(x_132, 0);
lean_inc(x_1855);
lean_dec(x_132);
x_1856 = l_Lean_Elab_Term_NamedArg_inhabited;
x_1857 = lean_array_get(x_1856, x_16, x_1855);
x_1858 = l_Array_eraseIdx___rarg(x_16, x_1855);
lean_dec(x_1855);
x_1859 = lean_ctor_get(x_1857, 1);
lean_inc(x_1859);
lean_dec(x_1857);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_1860 = l___private_Lean_Elab_App_2__elabArg(x_2, x_1859, x_128, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_1860) == 0)
{
lean_object* x_1861; lean_object* x_1862; lean_object* x_1863; uint8_t x_1864; 
x_1861 = lean_ctor_get(x_1860, 0);
lean_inc(x_1861);
x_1862 = lean_ctor_get(x_1860, 1);
lean_inc(x_1862);
lean_dec(x_1860);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_1863 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_1862);
x_1864 = !lean_is_exclusive(x_1);
if (x_1864 == 0)
{
lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; 
x_1865 = lean_ctor_get(x_1, 7);
lean_dec(x_1865);
x_1866 = lean_ctor_get(x_1, 6);
lean_dec(x_1866);
x_1867 = lean_ctor_get(x_1, 5);
lean_dec(x_1867);
x_1868 = lean_ctor_get(x_1, 4);
lean_dec(x_1868);
x_1869 = lean_ctor_get(x_1, 3);
lean_dec(x_1869);
x_1870 = lean_ctor_get(x_1, 2);
lean_dec(x_1870);
x_1871 = lean_ctor_get(x_1, 1);
lean_dec(x_1871);
x_1872 = lean_ctor_get(x_1, 0);
lean_dec(x_1872);
if (lean_obj_tag(x_1863) == 0)
{
lean_object* x_1873; uint8_t x_1874; lean_object* x_1875; lean_object* x_1876; 
x_1873 = lean_ctor_get(x_1863, 1);
lean_inc(x_1873);
lean_dec(x_1863);
x_1874 = 1;
lean_ctor_set(x_1, 4, x_1858);
lean_ctor_set_uint8(x_1, sizeof(void*)*8 + 1, x_1874);
lean_inc(x_1861);
x_1875 = l_Lean_mkApp(x_2, x_1861);
x_1876 = lean_expr_instantiate1(x_129, x_1861);
lean_dec(x_1861);
lean_dec(x_129);
x_2 = x_1875;
x_3 = x_1876;
x_10 = x_1873;
goto _start;
}
else
{
uint8_t x_1878; 
lean_free_object(x_1);
lean_dec(x_1861);
lean_dec(x_1858);
lean_dec(x_129);
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
x_1878 = !lean_is_exclusive(x_1863);
if (x_1878 == 0)
{
return x_1863;
}
else
{
lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; 
x_1879 = lean_ctor_get(x_1863, 0);
x_1880 = lean_ctor_get(x_1863, 1);
lean_inc(x_1880);
lean_inc(x_1879);
lean_dec(x_1863);
x_1881 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1881, 0, x_1879);
lean_ctor_set(x_1881, 1, x_1880);
return x_1881;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_1863) == 0)
{
lean_object* x_1882; uint8_t x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; 
x_1882 = lean_ctor_get(x_1863, 1);
lean_inc(x_1882);
lean_dec(x_1863);
x_1883 = 1;
x_1884 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1884, 0, x_11);
lean_ctor_set(x_1884, 1, x_12);
lean_ctor_set(x_1884, 2, x_13);
lean_ctor_set(x_1884, 3, x_15);
lean_ctor_set(x_1884, 4, x_1858);
lean_ctor_set(x_1884, 5, x_17);
lean_ctor_set(x_1884, 6, x_18);
lean_ctor_set(x_1884, 7, x_19);
lean_ctor_set_uint8(x_1884, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1884, sizeof(void*)*8 + 1, x_1883);
lean_inc(x_1861);
x_1885 = l_Lean_mkApp(x_2, x_1861);
x_1886 = lean_expr_instantiate1(x_129, x_1861);
lean_dec(x_1861);
lean_dec(x_129);
x_1 = x_1884;
x_2 = x_1885;
x_3 = x_1886;
x_10 = x_1882;
goto _start;
}
else
{
lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; 
lean_dec(x_1861);
lean_dec(x_1858);
lean_dec(x_129);
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
x_1888 = lean_ctor_get(x_1863, 0);
lean_inc(x_1888);
x_1889 = lean_ctor_get(x_1863, 1);
lean_inc(x_1889);
if (lean_is_exclusive(x_1863)) {
 lean_ctor_release(x_1863, 0);
 lean_ctor_release(x_1863, 1);
 x_1890 = x_1863;
} else {
 lean_dec_ref(x_1863);
 x_1890 = lean_box(0);
}
if (lean_is_scalar(x_1890)) {
 x_1891 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1891 = x_1890;
}
lean_ctor_set(x_1891, 0, x_1888);
lean_ctor_set(x_1891, 1, x_1889);
return x_1891;
}
}
}
else
{
uint8_t x_1892; 
lean_dec(x_1858);
lean_dec(x_129);
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
x_1892 = !lean_is_exclusive(x_1860);
if (x_1892 == 0)
{
return x_1860;
}
else
{
lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; 
x_1893 = lean_ctor_get(x_1860, 0);
x_1894 = lean_ctor_get(x_1860, 1);
lean_inc(x_1894);
lean_inc(x_1893);
lean_dec(x_1860);
x_1895 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1895, 0, x_1893);
lean_ctor_set(x_1895, 1, x_1894);
return x_1895;
}
}
}
}
else
{
lean_object* x_1896; 
lean_dec(x_1);
x_1896 = lean_box(0);
x_30 = x_1896;
goto block_126;
}
block_126:
{
lean_object* x_31; uint8_t x_74; 
lean_dec(x_30);
x_74 = l_Array_isEmpty___rarg(x_16);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_22);
lean_dec(x_3);
x_75 = lean_box(0);
x_31 = x_75;
goto block_73;
}
else
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_array_get_size(x_12);
x_77 = lean_nat_dec_eq(x_15, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_22);
lean_dec(x_3);
x_78 = lean_box(0);
x_31 = x_78;
goto block_73;
}
else
{
lean_object* x_79; uint8_t x_80; 
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
x_79 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_80 = l_Lean_checkTraceOption(x_22, x_79);
lean_dec(x_22);
if (x_80 == 0)
{
lean_object* x_81; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_81 = x_29;
goto block_94;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_13, 0);
lean_inc(x_95);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_96 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_95, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_81 = x_97;
goto block_94;
}
else
{
uint8_t x_98; 
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
x_98 = !lean_is_exclusive(x_96);
if (x_98 == 0)
{
return x_96;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_96, 0);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_96);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
block_94:
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_83 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_82, x_4, x_5, x_6, x_7, x_8, x_9, x_81);
lean_dec(x_17);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
lean_inc(x_2);
x_85 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(x_2, x_11, x_19, x_82, x_4, x_5, x_6, x_7, x_8, x_9, x_84);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
lean_ctor_set(x_85, 0, x_2);
return x_85;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_2);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_83);
if (x_90 == 0)
{
return x_83;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_83, 0);
x_92 = lean_ctor_get(x_83, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_83);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_inc(x_2);
x_102 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_102, 0, x_2);
x_103 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_79, x_102, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_105 = x_104;
goto block_118;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_13, 0);
lean_inc(x_119);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_120 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_119, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_104);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_105 = x_121;
goto block_118;
}
else
{
uint8_t x_122; 
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
x_122 = !lean_is_exclusive(x_120);
if (x_122 == 0)
{
return x_120;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_120, 0);
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_120);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
block_118:
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_107 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_106, x_4, x_5, x_6, x_7, x_8, x_9, x_105);
lean_dec(x_17);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
lean_inc(x_2);
x_109 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_2, x_11, x_19, x_106, x_4, x_5, x_6, x_7, x_8, x_9, x_108);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_109, 0);
lean_dec(x_111);
lean_ctor_set(x_109, 0, x_2);
return x_109;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_2);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_107);
if (x_114 == 0)
{
return x_107;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_107, 0);
x_116 = lean_ctor_get(x_107, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_107);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
}
block_73:
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_31);
x_32 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_33 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_17);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = 1;
x_36 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_37 = l___private_Lean_Elab_SyntheticMVars_13__synthesizeSyntheticMVarsAux___main(x_35, x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Array_empty___closed__1;
x_40 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_40, 0, x_11);
lean_ctor_set(x_40, 1, x_12);
lean_ctor_set(x_40, 2, x_13);
lean_ctor_set(x_40, 3, x_15);
lean_ctor_set(x_40, 4, x_16);
lean_ctor_set(x_40, 5, x_39);
lean_ctor_set(x_40, 6, x_18);
lean_ctor_set(x_40, 7, x_19);
lean_ctor_set_uint8(x_40, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_40, sizeof(void*)*8 + 1, x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_14__useImplicitLambda_x3f___spec__1(x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 7)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_1 = x_40;
x_3 = x_42;
x_10 = x_43;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_46 = l___private_Lean_Elab_App_4__tryCoeFun(x_42, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_47);
x_49 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_1 = x_40;
x_2 = x_47;
x_3 = x_50;
x_10 = x_51;
goto _start;
}
else
{
uint8_t x_53; 
lean_dec(x_47);
lean_dec(x_40);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_49);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_40);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_46);
if (x_57 == 0)
{
return x_46;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_46);
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
lean_dec(x_40);
lean_dec(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_41);
if (x_61 == 0)
{
return x_41;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_41, 0);
x_63 = lean_ctor_get(x_41, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_41);
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
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_18);
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
x_65 = !lean_is_exclusive(x_37);
if (x_65 == 0)
{
return x_37;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_37, 0);
x_67 = lean_ctor_get(x_37, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_37);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_19);
lean_dec(x_18);
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
x_69 = !lean_is_exclusive(x_33);
if (x_69 == 0)
{
return x_33;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_33, 0);
x_71 = lean_ctor_get(x_33, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_33);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
}
else
{
uint8_t x_1897; 
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
x_1897 = !lean_is_exclusive(x_27);
if (x_1897 == 0)
{
return x_27;
}
else
{
lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; 
x_1898 = lean_ctor_get(x_27, 0);
x_1899 = lean_ctor_get(x_27, 1);
lean_inc(x_1899);
lean_inc(x_1898);
lean_dec(x_27);
x_1900 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1900, 0, x_1898);
lean_ctor_set(x_1900, 1, x_1899);
return x_1900;
}
}
}
else
{
uint8_t x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; 
x_1901 = lean_ctor_get_uint8(x_1, sizeof(void*)*8 + 1);
x_1902 = lean_ctor_get(x_8, 0);
x_1903 = lean_ctor_get(x_8, 1);
x_1904 = lean_ctor_get(x_8, 2);
x_1905 = lean_ctor_get(x_8, 3);
lean_inc(x_1905);
lean_inc(x_1904);
lean_inc(x_1903);
lean_inc(x_1902);
lean_dec(x_8);
x_1906 = l_Lean_replaceRef(x_11, x_1905);
x_1907 = l_Lean_replaceRef(x_1906, x_1905);
lean_dec(x_1906);
x_1908 = l_Lean_replaceRef(x_1907, x_1905);
lean_dec(x_1905);
lean_dec(x_1907);
lean_inc(x_1902);
x_1909 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1909, 0, x_1902);
lean_ctor_set(x_1909, 1, x_1903);
lean_ctor_set(x_1909, 2, x_1904);
lean_ctor_set(x_1909, 3, x_1908);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_1910 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_14__useImplicitLambda_x3f___spec__1(x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_10);
if (lean_obj_tag(x_1910) == 0)
{
lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; 
x_1911 = lean_ctor_get(x_1910, 0);
lean_inc(x_1911);
x_1912 = lean_ctor_get(x_1910, 1);
lean_inc(x_1912);
lean_dec(x_1910);
if (lean_obj_tag(x_1911) == 7)
{
lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; uint64_t x_2011; lean_object* x_2012; lean_object* x_2013; 
x_2008 = lean_ctor_get(x_1911, 0);
lean_inc(x_2008);
x_2009 = lean_ctor_get(x_1911, 1);
lean_inc(x_2009);
x_2010 = lean_ctor_get(x_1911, 2);
lean_inc(x_2010);
x_2011 = lean_ctor_get_uint64(x_1911, sizeof(void*)*3);
x_2012 = lean_unsigned_to_nat(0u);
x_2013 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__3(x_2008, x_16, x_2012);
if (lean_obj_tag(x_2013) == 0)
{
uint8_t x_2014; 
x_2014 = (uint8_t)((x_2011 << 24) >> 61);
switch (x_2014) {
case 0:
{
lean_object* x_2015; lean_object* x_2016; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_2015 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1911, x_4, x_5, x_6, x_7, x_1909, x_9, x_1912);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_2016 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2016 = lean_box(0);
}
if (lean_obj_tag(x_2015) == 0)
{
lean_object* x_2017; uint8_t x_2018; lean_object* x_2019; lean_object* x_2020; uint8_t x_2021; 
x_2017 = lean_ctor_get(x_2015, 1);
lean_inc(x_2017);
lean_dec(x_2015);
x_2018 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
if (lean_is_scalar(x_2016)) {
 x_2019 = lean_alloc_ctor(0, 8, 2);
} else {
 x_2019 = x_2016;
}
lean_ctor_set(x_2019, 0, x_11);
lean_ctor_set(x_2019, 1, x_12);
lean_ctor_set(x_2019, 2, x_13);
lean_ctor_set(x_2019, 3, x_15);
lean_ctor_set(x_2019, 4, x_16);
lean_ctor_set(x_2019, 5, x_17);
lean_ctor_set(x_2019, 6, x_18);
lean_ctor_set(x_2019, 7, x_19);
lean_ctor_set_uint8(x_2019, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2019, sizeof(void*)*8 + 1, x_2018);
x_2020 = lean_array_get_size(x_12);
x_2021 = lean_nat_dec_lt(x_15, x_2020);
lean_dec(x_2020);
if (x_2021 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_2022; 
x_2022 = l_Lean_Expr_getOptParamDefault_x3f(x_2009);
if (lean_obj_tag(x_2022) == 0)
{
lean_object* x_2023; 
x_2023 = l_Lean_Expr_getAutoParamTactic_x3f(x_2009);
if (lean_obj_tag(x_2023) == 0)
{
uint8_t x_2024; 
lean_dec(x_2019);
lean_dec(x_2010);
lean_dec(x_2009);
x_2024 = l_Array_isEmpty___rarg(x_16);
if (x_2024 == 0)
{
lean_object* x_2025; lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; lean_object* x_2029; lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; lean_object* x_2033; lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; 
lean_dec(x_1902);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_2025 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2025, 0, x_2008);
x_2026 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_2027 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2027, 0, x_2026);
lean_ctor_set(x_2027, 1, x_2025);
x_2028 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_2029 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2029, 0, x_2027);
lean_ctor_set(x_2029, 1, x_2028);
x_2030 = x_16;
x_2031 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_2012, x_2030);
x_2032 = x_2031;
x_2033 = l_Array_toList___rarg(x_2032);
lean_dec(x_2032);
x_2034 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_2033);
x_2035 = l_Array_HasRepr___rarg___closed__1;
x_2036 = lean_string_append(x_2035, x_2034);
lean_dec(x_2034);
x_2037 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2037, 0, x_2036);
x_2038 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2038, 0, x_2037);
x_2039 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2039, 0, x_2029);
lean_ctor_set(x_2039, 1, x_2038);
x_2040 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2039, x_4, x_5, x_6, x_7, x_1909, x_9, x_2017);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2040;
}
else
{
lean_object* x_2041; uint8_t x_2042; 
lean_dec(x_2008);
lean_dec(x_16);
x_2041 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2042 = l_Lean_checkTraceOption(x_1902, x_2041);
lean_dec(x_1902);
if (x_2042 == 0)
{
lean_object* x_2043; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2043 = x_2017;
goto block_2054;
}
else
{
lean_object* x_2055; lean_object* x_2056; 
x_2055 = lean_ctor_get(x_13, 0);
lean_inc(x_2055);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_2056 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2055, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_2017);
if (lean_obj_tag(x_2056) == 0)
{
lean_object* x_2057; 
x_2057 = lean_ctor_get(x_2056, 1);
lean_inc(x_2057);
lean_dec(x_2056);
x_2043 = x_2057;
goto block_2054;
}
else
{
lean_object* x_2058; lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2058 = lean_ctor_get(x_2056, 0);
lean_inc(x_2058);
x_2059 = lean_ctor_get(x_2056, 1);
lean_inc(x_2059);
if (lean_is_exclusive(x_2056)) {
 lean_ctor_release(x_2056, 0);
 lean_ctor_release(x_2056, 1);
 x_2060 = x_2056;
} else {
 lean_dec_ref(x_2056);
 x_2060 = lean_box(0);
}
if (lean_is_scalar(x_2060)) {
 x_2061 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2061 = x_2060;
}
lean_ctor_set(x_2061, 0, x_2058);
lean_ctor_set(x_2061, 1, x_2059);
return x_2061;
}
}
block_2054:
{
lean_object* x_2044; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2044 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2043);
lean_dec(x_17);
if (lean_obj_tag(x_2044) == 0)
{
lean_object* x_2045; lean_object* x_2046; lean_object* x_2047; lean_object* x_2048; lean_object* x_2049; 
x_2045 = lean_ctor_get(x_2044, 1);
lean_inc(x_2045);
lean_dec(x_2044);
lean_inc(x_2);
x_2046 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__5(x_2, x_11, x_19, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2045);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2047 = lean_ctor_get(x_2046, 1);
lean_inc(x_2047);
if (lean_is_exclusive(x_2046)) {
 lean_ctor_release(x_2046, 0);
 lean_ctor_release(x_2046, 1);
 x_2048 = x_2046;
} else {
 lean_dec_ref(x_2046);
 x_2048 = lean_box(0);
}
if (lean_is_scalar(x_2048)) {
 x_2049 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2049 = x_2048;
}
lean_ctor_set(x_2049, 0, x_2);
lean_ctor_set(x_2049, 1, x_2047);
return x_2049;
}
else
{
lean_object* x_2050; lean_object* x_2051; lean_object* x_2052; lean_object* x_2053; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2050 = lean_ctor_get(x_2044, 0);
lean_inc(x_2050);
x_2051 = lean_ctor_get(x_2044, 1);
lean_inc(x_2051);
if (lean_is_exclusive(x_2044)) {
 lean_ctor_release(x_2044, 0);
 lean_ctor_release(x_2044, 1);
 x_2052 = x_2044;
} else {
 lean_dec_ref(x_2044);
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
}
else
{
lean_object* x_2062; lean_object* x_2063; lean_object* x_2064; lean_object* x_2065; 
lean_inc(x_2);
x_2062 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2062, 0, x_2);
x_2063 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2041, x_2062, x_4, x_5, x_6, x_7, x_1909, x_9, x_2017);
x_2064 = lean_ctor_get(x_2063, 1);
lean_inc(x_2064);
lean_dec(x_2063);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2065 = x_2064;
goto block_2076;
}
else
{
lean_object* x_2077; lean_object* x_2078; 
x_2077 = lean_ctor_get(x_13, 0);
lean_inc(x_2077);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_2078 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2077, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_2064);
if (lean_obj_tag(x_2078) == 0)
{
lean_object* x_2079; 
x_2079 = lean_ctor_get(x_2078, 1);
lean_inc(x_2079);
lean_dec(x_2078);
x_2065 = x_2079;
goto block_2076;
}
else
{
lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; lean_object* x_2083; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2080 = lean_ctor_get(x_2078, 0);
lean_inc(x_2080);
x_2081 = lean_ctor_get(x_2078, 1);
lean_inc(x_2081);
if (lean_is_exclusive(x_2078)) {
 lean_ctor_release(x_2078, 0);
 lean_ctor_release(x_2078, 1);
 x_2082 = x_2078;
} else {
 lean_dec_ref(x_2078);
 x_2082 = lean_box(0);
}
if (lean_is_scalar(x_2082)) {
 x_2083 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2083 = x_2082;
}
lean_ctor_set(x_2083, 0, x_2080);
lean_ctor_set(x_2083, 1, x_2081);
return x_2083;
}
}
block_2076:
{
lean_object* x_2066; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2066 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2065);
lean_dec(x_17);
if (lean_obj_tag(x_2066) == 0)
{
lean_object* x_2067; lean_object* x_2068; lean_object* x_2069; lean_object* x_2070; lean_object* x_2071; 
x_2067 = lean_ctor_get(x_2066, 1);
lean_inc(x_2067);
lean_dec(x_2066);
lean_inc(x_2);
x_2068 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__6(x_2, x_11, x_19, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2067);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2069 = lean_ctor_get(x_2068, 1);
lean_inc(x_2069);
if (lean_is_exclusive(x_2068)) {
 lean_ctor_release(x_2068, 0);
 lean_ctor_release(x_2068, 1);
 x_2070 = x_2068;
} else {
 lean_dec_ref(x_2068);
 x_2070 = lean_box(0);
}
if (lean_is_scalar(x_2070)) {
 x_2071 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2071 = x_2070;
}
lean_ctor_set(x_2071, 0, x_2);
lean_ctor_set(x_2071, 1, x_2069);
return x_2071;
}
else
{
lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2072 = lean_ctor_get(x_2066, 0);
lean_inc(x_2072);
x_2073 = lean_ctor_get(x_2066, 1);
lean_inc(x_2073);
if (lean_is_exclusive(x_2066)) {
 lean_ctor_release(x_2066, 0);
 lean_ctor_release(x_2066, 1);
 x_2074 = x_2066;
} else {
 lean_dec_ref(x_2066);
 x_2074 = lean_box(0);
}
if (lean_is_scalar(x_2074)) {
 x_2075 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2075 = x_2074;
}
lean_ctor_set(x_2075, 0, x_2072);
lean_ctor_set(x_2075, 1, x_2073);
return x_2075;
}
}
}
}
}
else
{
lean_object* x_2084; 
lean_dec(x_2008);
lean_dec(x_1902);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_2084 = lean_ctor_get(x_2023, 0);
lean_inc(x_2084);
lean_dec(x_2023);
if (lean_obj_tag(x_2084) == 4)
{
lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; lean_object* x_2090; 
x_2085 = lean_ctor_get(x_2084, 0);
lean_inc(x_2085);
lean_dec(x_2084);
x_2086 = lean_st_ref_get(x_9, x_2017);
x_2087 = lean_ctor_get(x_2086, 0);
lean_inc(x_2087);
x_2088 = lean_ctor_get(x_2086, 1);
lean_inc(x_2088);
lean_dec(x_2086);
x_2089 = lean_ctor_get(x_2087, 0);
lean_inc(x_2089);
lean_dec(x_2087);
x_2090 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_2089, x_2085);
if (lean_obj_tag(x_2090) == 0)
{
lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; lean_object* x_2094; 
lean_dec(x_2019);
lean_dec(x_2010);
lean_dec(x_2009);
lean_dec(x_11);
lean_dec(x_2);
x_2091 = lean_ctor_get(x_2090, 0);
lean_inc(x_2091);
lean_dec(x_2090);
x_2092 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2092, 0, x_2091);
x_2093 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2093, 0, x_2092);
x_2094 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2093, x_4, x_5, x_6, x_7, x_1909, x_9, x_2088);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2094;
}
else
{
lean_object* x_2095; lean_object* x_2096; lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; lean_object* x_2100; lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; lean_object* x_2109; lean_object* x_2110; lean_object* x_2111; lean_object* x_2112; lean_object* x_2113; lean_object* x_2114; lean_object* x_2115; lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; 
x_2095 = lean_ctor_get(x_2090, 0);
lean_inc(x_2095);
lean_dec(x_2090);
x_2096 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_1909, x_9, x_2088);
x_2097 = lean_ctor_get(x_2096, 1);
lean_inc(x_2097);
lean_dec(x_2096);
x_2098 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_2097);
x_2099 = lean_ctor_get(x_2098, 1);
lean_inc(x_2099);
lean_dec(x_2098);
x_2100 = l_Lean_Syntax_getArgs(x_2095);
lean_dec(x_2095);
x_2101 = l_Array_empty___closed__1;
x_2102 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2100, x_2100, x_2012, x_2101);
lean_dec(x_2100);
x_2103 = l_Lean_nullKind___closed__2;
x_2104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2104, 0, x_2103);
lean_ctor_set(x_2104, 1, x_2102);
x_2105 = lean_array_push(x_2101, x_2104);
x_2106 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__5;
x_2107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2107, 0, x_2106);
lean_ctor_set(x_2107, 1, x_2105);
x_2108 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_2109 = lean_array_push(x_2108, x_2107);
x_2110 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_2111 = lean_array_push(x_2109, x_2110);
x_2112 = l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock___closed__2;
x_2113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2113, 0, x_2112);
lean_ctor_set(x_2113, 1, x_2111);
x_2114 = lean_array_push(x_2101, x_2113);
x_2115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2115, 0, x_2103);
lean_ctor_set(x_2115, 1, x_2114);
x_2116 = lean_array_push(x_2101, x_2115);
x_2117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2117, 0, x_2106);
lean_ctor_set(x_2117, 1, x_2116);
x_2118 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_2119 = lean_array_push(x_2118, x_2117);
x_2120 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_2121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2121, 0, x_2120);
lean_ctor_set(x_2121, 1, x_2119);
x_2122 = l_Lean_Syntax_copyInfo(x_2121, x_11);
lean_dec(x_11);
x_2123 = l_Lean_Expr_getAppNumArgsAux___main(x_2009, x_2012);
x_2124 = lean_nat_sub(x_2123, x_2012);
lean_dec(x_2123);
x_2125 = lean_unsigned_to_nat(1u);
x_2126 = lean_nat_sub(x_2124, x_2125);
lean_dec(x_2124);
x_2127 = l_Lean_Expr_getRevArg_x21___main(x_2009, x_2126);
lean_dec(x_2009);
x_2128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2128, 0, x_2122);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2129 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2128, x_2127, x_4, x_5, x_6, x_7, x_1909, x_9, x_2099);
if (lean_obj_tag(x_2129) == 0)
{
lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; lean_object* x_2133; 
x_2130 = lean_ctor_get(x_2129, 0);
lean_inc(x_2130);
x_2131 = lean_ctor_get(x_2129, 1);
lean_inc(x_2131);
lean_dec(x_2129);
lean_inc(x_2130);
x_2132 = l_Lean_mkApp(x_2, x_2130);
x_2133 = lean_expr_instantiate1(x_2010, x_2130);
lean_dec(x_2130);
lean_dec(x_2010);
x_1 = x_2019;
x_2 = x_2132;
x_3 = x_2133;
x_8 = x_1909;
x_10 = x_2131;
goto _start;
}
else
{
lean_object* x_2135; lean_object* x_2136; lean_object* x_2137; lean_object* x_2138; 
lean_dec(x_2019);
lean_dec(x_2010);
lean_dec(x_1909);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2135 = lean_ctor_get(x_2129, 0);
lean_inc(x_2135);
x_2136 = lean_ctor_get(x_2129, 1);
lean_inc(x_2136);
if (lean_is_exclusive(x_2129)) {
 lean_ctor_release(x_2129, 0);
 lean_ctor_release(x_2129, 1);
 x_2137 = x_2129;
} else {
 lean_dec_ref(x_2129);
 x_2137 = lean_box(0);
}
if (lean_is_scalar(x_2137)) {
 x_2138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2138 = x_2137;
}
lean_ctor_set(x_2138, 0, x_2135);
lean_ctor_set(x_2138, 1, x_2136);
return x_2138;
}
}
}
else
{
lean_object* x_2139; lean_object* x_2140; 
lean_dec(x_2084);
lean_dec(x_2019);
lean_dec(x_2010);
lean_dec(x_2009);
lean_dec(x_11);
lean_dec(x_2);
x_2139 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_2140 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2139, x_4, x_5, x_6, x_7, x_1909, x_9, x_2017);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2140;
}
}
}
else
{
lean_object* x_2141; lean_object* x_2142; lean_object* x_2143; 
lean_dec(x_2009);
lean_dec(x_2008);
lean_dec(x_1902);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_2141 = lean_ctor_get(x_2022, 0);
lean_inc(x_2141);
lean_dec(x_2022);
lean_inc(x_2141);
x_2142 = l_Lean_mkApp(x_2, x_2141);
x_2143 = lean_expr_instantiate1(x_2010, x_2141);
lean_dec(x_2141);
lean_dec(x_2010);
x_1 = x_2019;
x_2 = x_2142;
x_3 = x_2143;
x_8 = x_1909;
x_10 = x_2017;
goto _start;
}
}
else
{
uint8_t x_2145; 
lean_dec(x_2019);
lean_dec(x_2010);
lean_dec(x_2009);
x_2145 = l_Array_isEmpty___rarg(x_16);
if (x_2145 == 0)
{
lean_object* x_2146; lean_object* x_2147; lean_object* x_2148; lean_object* x_2149; lean_object* x_2150; lean_object* x_2151; lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; lean_object* x_2155; lean_object* x_2156; lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; 
lean_dec(x_1902);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_2146 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2146, 0, x_2008);
x_2147 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_2148 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2148, 0, x_2147);
lean_ctor_set(x_2148, 1, x_2146);
x_2149 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_2150 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2150, 0, x_2148);
lean_ctor_set(x_2150, 1, x_2149);
x_2151 = x_16;
x_2152 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_2012, x_2151);
x_2153 = x_2152;
x_2154 = l_Array_toList___rarg(x_2153);
lean_dec(x_2153);
x_2155 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_2154);
x_2156 = l_Array_HasRepr___rarg___closed__1;
x_2157 = lean_string_append(x_2156, x_2155);
lean_dec(x_2155);
x_2158 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2158, 0, x_2157);
x_2159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2159, 0, x_2158);
x_2160 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2160, 0, x_2150);
lean_ctor_set(x_2160, 1, x_2159);
x_2161 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2160, x_4, x_5, x_6, x_7, x_1909, x_9, x_2017);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2161;
}
else
{
lean_object* x_2162; uint8_t x_2163; 
lean_dec(x_2008);
lean_dec(x_16);
x_2162 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2163 = l_Lean_checkTraceOption(x_1902, x_2162);
lean_dec(x_1902);
if (x_2163 == 0)
{
lean_object* x_2164; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2164 = x_2017;
goto block_2175;
}
else
{
lean_object* x_2176; lean_object* x_2177; 
x_2176 = lean_ctor_get(x_13, 0);
lean_inc(x_2176);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_2177 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2176, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_2017);
if (lean_obj_tag(x_2177) == 0)
{
lean_object* x_2178; 
x_2178 = lean_ctor_get(x_2177, 1);
lean_inc(x_2178);
lean_dec(x_2177);
x_2164 = x_2178;
goto block_2175;
}
else
{
lean_object* x_2179; lean_object* x_2180; lean_object* x_2181; lean_object* x_2182; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2179 = lean_ctor_get(x_2177, 0);
lean_inc(x_2179);
x_2180 = lean_ctor_get(x_2177, 1);
lean_inc(x_2180);
if (lean_is_exclusive(x_2177)) {
 lean_ctor_release(x_2177, 0);
 lean_ctor_release(x_2177, 1);
 x_2181 = x_2177;
} else {
 lean_dec_ref(x_2177);
 x_2181 = lean_box(0);
}
if (lean_is_scalar(x_2181)) {
 x_2182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2182 = x_2181;
}
lean_ctor_set(x_2182, 0, x_2179);
lean_ctor_set(x_2182, 1, x_2180);
return x_2182;
}
}
block_2175:
{
lean_object* x_2165; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2165 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2164);
lean_dec(x_17);
if (lean_obj_tag(x_2165) == 0)
{
lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; lean_object* x_2170; 
x_2166 = lean_ctor_get(x_2165, 1);
lean_inc(x_2166);
lean_dec(x_2165);
lean_inc(x_2);
x_2167 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__7(x_2, x_11, x_19, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2166);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2168 = lean_ctor_get(x_2167, 1);
lean_inc(x_2168);
if (lean_is_exclusive(x_2167)) {
 lean_ctor_release(x_2167, 0);
 lean_ctor_release(x_2167, 1);
 x_2169 = x_2167;
} else {
 lean_dec_ref(x_2167);
 x_2169 = lean_box(0);
}
if (lean_is_scalar(x_2169)) {
 x_2170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2170 = x_2169;
}
lean_ctor_set(x_2170, 0, x_2);
lean_ctor_set(x_2170, 1, x_2168);
return x_2170;
}
else
{
lean_object* x_2171; lean_object* x_2172; lean_object* x_2173; lean_object* x_2174; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2171 = lean_ctor_get(x_2165, 0);
lean_inc(x_2171);
x_2172 = lean_ctor_get(x_2165, 1);
lean_inc(x_2172);
if (lean_is_exclusive(x_2165)) {
 lean_ctor_release(x_2165, 0);
 lean_ctor_release(x_2165, 1);
 x_2173 = x_2165;
} else {
 lean_dec_ref(x_2165);
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
}
else
{
lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; lean_object* x_2186; 
lean_inc(x_2);
x_2183 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2183, 0, x_2);
x_2184 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2162, x_2183, x_4, x_5, x_6, x_7, x_1909, x_9, x_2017);
x_2185 = lean_ctor_get(x_2184, 1);
lean_inc(x_2185);
lean_dec(x_2184);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2186 = x_2185;
goto block_2197;
}
else
{
lean_object* x_2198; lean_object* x_2199; 
x_2198 = lean_ctor_get(x_13, 0);
lean_inc(x_2198);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_2199 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2198, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_2185);
if (lean_obj_tag(x_2199) == 0)
{
lean_object* x_2200; 
x_2200 = lean_ctor_get(x_2199, 1);
lean_inc(x_2200);
lean_dec(x_2199);
x_2186 = x_2200;
goto block_2197;
}
else
{
lean_object* x_2201; lean_object* x_2202; lean_object* x_2203; lean_object* x_2204; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2201 = lean_ctor_get(x_2199, 0);
lean_inc(x_2201);
x_2202 = lean_ctor_get(x_2199, 1);
lean_inc(x_2202);
if (lean_is_exclusive(x_2199)) {
 lean_ctor_release(x_2199, 0);
 lean_ctor_release(x_2199, 1);
 x_2203 = x_2199;
} else {
 lean_dec_ref(x_2199);
 x_2203 = lean_box(0);
}
if (lean_is_scalar(x_2203)) {
 x_2204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2204 = x_2203;
}
lean_ctor_set(x_2204, 0, x_2201);
lean_ctor_set(x_2204, 1, x_2202);
return x_2204;
}
}
block_2197:
{
lean_object* x_2187; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2187 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2186);
lean_dec(x_17);
if (lean_obj_tag(x_2187) == 0)
{
lean_object* x_2188; lean_object* x_2189; lean_object* x_2190; lean_object* x_2191; lean_object* x_2192; 
x_2188 = lean_ctor_get(x_2187, 1);
lean_inc(x_2188);
lean_dec(x_2187);
lean_inc(x_2);
x_2189 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__8(x_2, x_11, x_19, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2188);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2190 = lean_ctor_get(x_2189, 1);
lean_inc(x_2190);
if (lean_is_exclusive(x_2189)) {
 lean_ctor_release(x_2189, 0);
 lean_ctor_release(x_2189, 1);
 x_2191 = x_2189;
} else {
 lean_dec_ref(x_2189);
 x_2191 = lean_box(0);
}
if (lean_is_scalar(x_2191)) {
 x_2192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2192 = x_2191;
}
lean_ctor_set(x_2192, 0, x_2);
lean_ctor_set(x_2192, 1, x_2190);
return x_2192;
}
else
{
lean_object* x_2193; lean_object* x_2194; lean_object* x_2195; lean_object* x_2196; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2193 = lean_ctor_get(x_2187, 0);
lean_inc(x_2193);
x_2194 = lean_ctor_get(x_2187, 1);
lean_inc(x_2194);
if (lean_is_exclusive(x_2187)) {
 lean_ctor_release(x_2187, 0);
 lean_ctor_release(x_2187, 1);
 x_2195 = x_2187;
} else {
 lean_dec_ref(x_2187);
 x_2195 = lean_box(0);
}
if (lean_is_scalar(x_2195)) {
 x_2196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2196 = x_2195;
}
lean_ctor_set(x_2196, 0, x_2193);
lean_ctor_set(x_2196, 1, x_2194);
return x_2196;
}
}
}
}
}
}
else
{
lean_object* x_2205; lean_object* x_2206; 
lean_dec(x_2019);
lean_dec(x_2008);
lean_dec(x_1902);
lean_dec(x_3);
x_2205 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2206 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2205, x_2009, x_4, x_5, x_6, x_7, x_1909, x_9, x_2017);
if (lean_obj_tag(x_2206) == 0)
{
lean_object* x_2207; lean_object* x_2208; lean_object* x_2209; lean_object* x_2210; lean_object* x_2211; lean_object* x_2212; lean_object* x_2213; 
x_2207 = lean_ctor_get(x_2206, 0);
lean_inc(x_2207);
x_2208 = lean_ctor_get(x_2206, 1);
lean_inc(x_2208);
lean_dec(x_2206);
x_2209 = lean_unsigned_to_nat(1u);
x_2210 = lean_nat_add(x_15, x_2209);
lean_dec(x_15);
x_2211 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_2211, 0, x_11);
lean_ctor_set(x_2211, 1, x_12);
lean_ctor_set(x_2211, 2, x_13);
lean_ctor_set(x_2211, 3, x_2210);
lean_ctor_set(x_2211, 4, x_16);
lean_ctor_set(x_2211, 5, x_17);
lean_ctor_set(x_2211, 6, x_18);
lean_ctor_set(x_2211, 7, x_19);
lean_ctor_set_uint8(x_2211, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2211, sizeof(void*)*8 + 1, x_2018);
lean_inc(x_2207);
x_2212 = l_Lean_mkApp(x_2, x_2207);
x_2213 = lean_expr_instantiate1(x_2010, x_2207);
lean_dec(x_2207);
lean_dec(x_2010);
x_1 = x_2211;
x_2 = x_2212;
x_3 = x_2213;
x_8 = x_1909;
x_10 = x_2208;
goto _start;
}
else
{
lean_object* x_2215; lean_object* x_2216; lean_object* x_2217; lean_object* x_2218; 
lean_dec(x_2010);
lean_dec(x_1909);
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
x_2215 = lean_ctor_get(x_2206, 0);
lean_inc(x_2215);
x_2216 = lean_ctor_get(x_2206, 1);
lean_inc(x_2216);
if (lean_is_exclusive(x_2206)) {
 lean_ctor_release(x_2206, 0);
 lean_ctor_release(x_2206, 1);
 x_2217 = x_2206;
} else {
 lean_dec_ref(x_2206);
 x_2217 = lean_box(0);
}
if (lean_is_scalar(x_2217)) {
 x_2218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2218 = x_2217;
}
lean_ctor_set(x_2218, 0, x_2215);
lean_ctor_set(x_2218, 1, x_2216);
return x_2218;
}
}
}
else
{
lean_object* x_2219; lean_object* x_2220; lean_object* x_2221; lean_object* x_2222; 
lean_dec(x_2016);
lean_dec(x_2010);
lean_dec(x_2009);
lean_dec(x_2008);
lean_dec(x_1909);
lean_dec(x_1902);
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
x_2219 = lean_ctor_get(x_2015, 0);
lean_inc(x_2219);
x_2220 = lean_ctor_get(x_2015, 1);
lean_inc(x_2220);
if (lean_is_exclusive(x_2015)) {
 lean_ctor_release(x_2015, 0);
 lean_ctor_release(x_2015, 1);
 x_2221 = x_2015;
} else {
 lean_dec_ref(x_2015);
 x_2221 = lean_box(0);
}
if (lean_is_scalar(x_2221)) {
 x_2222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2222 = x_2221;
}
lean_ctor_set(x_2222, 0, x_2219);
lean_ctor_set(x_2222, 1, x_2220);
return x_2222;
}
}
case 1:
{
if (x_14 == 0)
{
lean_object* x_2223; lean_object* x_2224; uint8_t x_2225; lean_object* x_2226; lean_object* x_2227; lean_object* x_2228; lean_object* x_2229; lean_object* x_2230; lean_object* x_2231; lean_object* x_2239; 
lean_dec(x_2008);
lean_dec(x_1911);
lean_dec(x_1902);
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
 x_2223 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2223 = lean_box(0);
}
x_2224 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2224, 0, x_2009);
x_2225 = 0;
x_2226 = lean_box(0);
lean_inc(x_6);
x_2227 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_2224, x_2225, x_2226, x_6, x_7, x_1909, x_9, x_1912);
x_2228 = lean_ctor_get(x_2227, 0);
lean_inc(x_2228);
x_2229 = lean_ctor_get(x_2227, 1);
lean_inc(x_2229);
lean_dec(x_2227);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2228);
x_2239 = l_Lean_Meta_isTypeFormer___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__9(x_2228, x_4, x_5, x_6, x_7, x_1909, x_9, x_2229);
if (lean_obj_tag(x_2239) == 0)
{
lean_object* x_2240; uint8_t x_2241; 
x_2240 = lean_ctor_get(x_2239, 0);
lean_inc(x_2240);
x_2241 = lean_unbox(x_2240);
lean_dec(x_2240);
if (x_2241 == 0)
{
lean_object* x_2242; 
x_2242 = lean_ctor_get(x_2239, 1);
lean_inc(x_2242);
lean_dec(x_2239);
x_2230 = x_18;
x_2231 = x_2242;
goto block_2238;
}
else
{
lean_object* x_2243; lean_object* x_2244; lean_object* x_2245; 
x_2243 = lean_ctor_get(x_2239, 1);
lean_inc(x_2243);
lean_dec(x_2239);
x_2244 = l_Lean_Expr_mvarId_x21(x_2228);
x_2245 = lean_array_push(x_18, x_2244);
x_2230 = x_2245;
x_2231 = x_2243;
goto block_2238;
}
}
else
{
lean_object* x_2246; lean_object* x_2247; lean_object* x_2248; lean_object* x_2249; 
lean_dec(x_2228);
lean_dec(x_2223);
lean_dec(x_2010);
lean_dec(x_1909);
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
x_2246 = lean_ctor_get(x_2239, 0);
lean_inc(x_2246);
x_2247 = lean_ctor_get(x_2239, 1);
lean_inc(x_2247);
if (lean_is_exclusive(x_2239)) {
 lean_ctor_release(x_2239, 0);
 lean_ctor_release(x_2239, 1);
 x_2248 = x_2239;
} else {
 lean_dec_ref(x_2239);
 x_2248 = lean_box(0);
}
if (lean_is_scalar(x_2248)) {
 x_2249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2249 = x_2248;
}
lean_ctor_set(x_2249, 0, x_2246);
lean_ctor_set(x_2249, 1, x_2247);
return x_2249;
}
block_2238:
{
lean_object* x_2232; lean_object* x_2233; lean_object* x_2234; lean_object* x_2235; lean_object* x_2236; 
x_2232 = l_Lean_Expr_mvarId_x21(x_2228);
x_2233 = lean_array_push(x_19, x_2232);
if (lean_is_scalar(x_2223)) {
 x_2234 = lean_alloc_ctor(0, 8, 2);
} else {
 x_2234 = x_2223;
}
lean_ctor_set(x_2234, 0, x_11);
lean_ctor_set(x_2234, 1, x_12);
lean_ctor_set(x_2234, 2, x_13);
lean_ctor_set(x_2234, 3, x_15);
lean_ctor_set(x_2234, 4, x_16);
lean_ctor_set(x_2234, 5, x_17);
lean_ctor_set(x_2234, 6, x_2230);
lean_ctor_set(x_2234, 7, x_2233);
lean_ctor_set_uint8(x_2234, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2234, sizeof(void*)*8 + 1, x_1901);
lean_inc(x_2228);
x_2235 = l_Lean_mkApp(x_2, x_2228);
x_2236 = lean_expr_instantiate1(x_2010, x_2228);
lean_dec(x_2228);
lean_dec(x_2010);
x_1 = x_2234;
x_2 = x_2235;
x_3 = x_2236;
x_8 = x_1909;
x_10 = x_2231;
goto _start;
}
}
else
{
lean_object* x_2250; lean_object* x_2251; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_2250 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1911, x_4, x_5, x_6, x_7, x_1909, x_9, x_1912);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_2251 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2251 = lean_box(0);
}
if (lean_obj_tag(x_2250) == 0)
{
lean_object* x_2252; lean_object* x_2253; uint8_t x_2254; 
x_2252 = lean_ctor_get(x_2250, 1);
lean_inc(x_2252);
lean_dec(x_2250);
x_2253 = lean_array_get_size(x_12);
x_2254 = lean_nat_dec_lt(x_15, x_2253);
lean_dec(x_2253);
if (x_2254 == 0)
{
uint8_t x_2255; 
lean_dec(x_2251);
lean_dec(x_2010);
lean_dec(x_2009);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_2255 = l_Array_isEmpty___rarg(x_16);
if (x_2255 == 0)
{
lean_object* x_2256; lean_object* x_2257; lean_object* x_2258; lean_object* x_2259; lean_object* x_2260; lean_object* x_2261; lean_object* x_2262; lean_object* x_2263; lean_object* x_2264; lean_object* x_2265; lean_object* x_2266; lean_object* x_2267; lean_object* x_2268; lean_object* x_2269; lean_object* x_2270; lean_object* x_2271; 
lean_dec(x_1902);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_2256 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2256, 0, x_2008);
x_2257 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_2258 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2258, 0, x_2257);
lean_ctor_set(x_2258, 1, x_2256);
x_2259 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_2260 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2260, 0, x_2258);
lean_ctor_set(x_2260, 1, x_2259);
x_2261 = x_16;
x_2262 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_2012, x_2261);
x_2263 = x_2262;
x_2264 = l_Array_toList___rarg(x_2263);
lean_dec(x_2263);
x_2265 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_2264);
x_2266 = l_Array_HasRepr___rarg___closed__1;
x_2267 = lean_string_append(x_2266, x_2265);
lean_dec(x_2265);
x_2268 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2268, 0, x_2267);
x_2269 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2269, 0, x_2268);
x_2270 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2270, 0, x_2260);
lean_ctor_set(x_2270, 1, x_2269);
x_2271 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2270, x_4, x_5, x_6, x_7, x_1909, x_9, x_2252);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2271;
}
else
{
lean_object* x_2272; uint8_t x_2273; 
lean_dec(x_2008);
lean_dec(x_16);
x_2272 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2273 = l_Lean_checkTraceOption(x_1902, x_2272);
lean_dec(x_1902);
if (x_2273 == 0)
{
lean_object* x_2274; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2274 = x_2252;
goto block_2285;
}
else
{
lean_object* x_2286; lean_object* x_2287; 
x_2286 = lean_ctor_get(x_13, 0);
lean_inc(x_2286);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_2287 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2286, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_2252);
if (lean_obj_tag(x_2287) == 0)
{
lean_object* x_2288; 
x_2288 = lean_ctor_get(x_2287, 1);
lean_inc(x_2288);
lean_dec(x_2287);
x_2274 = x_2288;
goto block_2285;
}
else
{
lean_object* x_2289; lean_object* x_2290; lean_object* x_2291; lean_object* x_2292; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2289 = lean_ctor_get(x_2287, 0);
lean_inc(x_2289);
x_2290 = lean_ctor_get(x_2287, 1);
lean_inc(x_2290);
if (lean_is_exclusive(x_2287)) {
 lean_ctor_release(x_2287, 0);
 lean_ctor_release(x_2287, 1);
 x_2291 = x_2287;
} else {
 lean_dec_ref(x_2287);
 x_2291 = lean_box(0);
}
if (lean_is_scalar(x_2291)) {
 x_2292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2292 = x_2291;
}
lean_ctor_set(x_2292, 0, x_2289);
lean_ctor_set(x_2292, 1, x_2290);
return x_2292;
}
}
block_2285:
{
lean_object* x_2275; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2275 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2274);
lean_dec(x_17);
if (lean_obj_tag(x_2275) == 0)
{
lean_object* x_2276; lean_object* x_2277; lean_object* x_2278; lean_object* x_2279; lean_object* x_2280; 
x_2276 = lean_ctor_get(x_2275, 1);
lean_inc(x_2276);
lean_dec(x_2275);
lean_inc(x_2);
x_2277 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__10(x_2, x_11, x_19, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2276);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2278 = lean_ctor_get(x_2277, 1);
lean_inc(x_2278);
if (lean_is_exclusive(x_2277)) {
 lean_ctor_release(x_2277, 0);
 lean_ctor_release(x_2277, 1);
 x_2279 = x_2277;
} else {
 lean_dec_ref(x_2277);
 x_2279 = lean_box(0);
}
if (lean_is_scalar(x_2279)) {
 x_2280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2280 = x_2279;
}
lean_ctor_set(x_2280, 0, x_2);
lean_ctor_set(x_2280, 1, x_2278);
return x_2280;
}
else
{
lean_object* x_2281; lean_object* x_2282; lean_object* x_2283; lean_object* x_2284; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2281 = lean_ctor_get(x_2275, 0);
lean_inc(x_2281);
x_2282 = lean_ctor_get(x_2275, 1);
lean_inc(x_2282);
if (lean_is_exclusive(x_2275)) {
 lean_ctor_release(x_2275, 0);
 lean_ctor_release(x_2275, 1);
 x_2283 = x_2275;
} else {
 lean_dec_ref(x_2275);
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
}
else
{
lean_object* x_2293; lean_object* x_2294; lean_object* x_2295; lean_object* x_2296; 
lean_inc(x_2);
x_2293 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2293, 0, x_2);
x_2294 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2272, x_2293, x_4, x_5, x_6, x_7, x_1909, x_9, x_2252);
x_2295 = lean_ctor_get(x_2294, 1);
lean_inc(x_2295);
lean_dec(x_2294);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2296 = x_2295;
goto block_2307;
}
else
{
lean_object* x_2308; lean_object* x_2309; 
x_2308 = lean_ctor_get(x_13, 0);
lean_inc(x_2308);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_2309 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2308, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_2295);
if (lean_obj_tag(x_2309) == 0)
{
lean_object* x_2310; 
x_2310 = lean_ctor_get(x_2309, 1);
lean_inc(x_2310);
lean_dec(x_2309);
x_2296 = x_2310;
goto block_2307;
}
else
{
lean_object* x_2311; lean_object* x_2312; lean_object* x_2313; lean_object* x_2314; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2311 = lean_ctor_get(x_2309, 0);
lean_inc(x_2311);
x_2312 = lean_ctor_get(x_2309, 1);
lean_inc(x_2312);
if (lean_is_exclusive(x_2309)) {
 lean_ctor_release(x_2309, 0);
 lean_ctor_release(x_2309, 1);
 x_2313 = x_2309;
} else {
 lean_dec_ref(x_2309);
 x_2313 = lean_box(0);
}
if (lean_is_scalar(x_2313)) {
 x_2314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2314 = x_2313;
}
lean_ctor_set(x_2314, 0, x_2311);
lean_ctor_set(x_2314, 1, x_2312);
return x_2314;
}
}
block_2307:
{
lean_object* x_2297; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2297 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2296);
lean_dec(x_17);
if (lean_obj_tag(x_2297) == 0)
{
lean_object* x_2298; lean_object* x_2299; lean_object* x_2300; lean_object* x_2301; lean_object* x_2302; 
x_2298 = lean_ctor_get(x_2297, 1);
lean_inc(x_2298);
lean_dec(x_2297);
lean_inc(x_2);
x_2299 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__11(x_2, x_11, x_19, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2298);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2300 = lean_ctor_get(x_2299, 1);
lean_inc(x_2300);
if (lean_is_exclusive(x_2299)) {
 lean_ctor_release(x_2299, 0);
 lean_ctor_release(x_2299, 1);
 x_2301 = x_2299;
} else {
 lean_dec_ref(x_2299);
 x_2301 = lean_box(0);
}
if (lean_is_scalar(x_2301)) {
 x_2302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2302 = x_2301;
}
lean_ctor_set(x_2302, 0, x_2);
lean_ctor_set(x_2302, 1, x_2300);
return x_2302;
}
else
{
lean_object* x_2303; lean_object* x_2304; lean_object* x_2305; lean_object* x_2306; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2303 = lean_ctor_get(x_2297, 0);
lean_inc(x_2303);
x_2304 = lean_ctor_get(x_2297, 1);
lean_inc(x_2304);
if (lean_is_exclusive(x_2297)) {
 lean_ctor_release(x_2297, 0);
 lean_ctor_release(x_2297, 1);
 x_2305 = x_2297;
} else {
 lean_dec_ref(x_2297);
 x_2305 = lean_box(0);
}
if (lean_is_scalar(x_2305)) {
 x_2306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2306 = x_2305;
}
lean_ctor_set(x_2306, 0, x_2303);
lean_ctor_set(x_2306, 1, x_2304);
return x_2306;
}
}
}
}
}
else
{
lean_object* x_2315; lean_object* x_2316; 
lean_dec(x_2008);
lean_dec(x_1902);
lean_dec(x_3);
x_2315 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2316 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2315, x_2009, x_4, x_5, x_6, x_7, x_1909, x_9, x_2252);
if (lean_obj_tag(x_2316) == 0)
{
lean_object* x_2317; lean_object* x_2318; lean_object* x_2319; lean_object* x_2320; uint8_t x_2321; lean_object* x_2322; lean_object* x_2323; lean_object* x_2324; 
x_2317 = lean_ctor_get(x_2316, 0);
lean_inc(x_2317);
x_2318 = lean_ctor_get(x_2316, 1);
lean_inc(x_2318);
lean_dec(x_2316);
x_2319 = lean_unsigned_to_nat(1u);
x_2320 = lean_nat_add(x_15, x_2319);
lean_dec(x_15);
x_2321 = 1;
if (lean_is_scalar(x_2251)) {
 x_2322 = lean_alloc_ctor(0, 8, 2);
} else {
 x_2322 = x_2251;
}
lean_ctor_set(x_2322, 0, x_11);
lean_ctor_set(x_2322, 1, x_12);
lean_ctor_set(x_2322, 2, x_13);
lean_ctor_set(x_2322, 3, x_2320);
lean_ctor_set(x_2322, 4, x_16);
lean_ctor_set(x_2322, 5, x_17);
lean_ctor_set(x_2322, 6, x_18);
lean_ctor_set(x_2322, 7, x_19);
lean_ctor_set_uint8(x_2322, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2322, sizeof(void*)*8 + 1, x_2321);
lean_inc(x_2317);
x_2323 = l_Lean_mkApp(x_2, x_2317);
x_2324 = lean_expr_instantiate1(x_2010, x_2317);
lean_dec(x_2317);
lean_dec(x_2010);
x_1 = x_2322;
x_2 = x_2323;
x_3 = x_2324;
x_8 = x_1909;
x_10 = x_2318;
goto _start;
}
else
{
lean_object* x_2326; lean_object* x_2327; lean_object* x_2328; lean_object* x_2329; 
lean_dec(x_2251);
lean_dec(x_2010);
lean_dec(x_1909);
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
x_2326 = lean_ctor_get(x_2316, 0);
lean_inc(x_2326);
x_2327 = lean_ctor_get(x_2316, 1);
lean_inc(x_2327);
if (lean_is_exclusive(x_2316)) {
 lean_ctor_release(x_2316, 0);
 lean_ctor_release(x_2316, 1);
 x_2328 = x_2316;
} else {
 lean_dec_ref(x_2316);
 x_2328 = lean_box(0);
}
if (lean_is_scalar(x_2328)) {
 x_2329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2329 = x_2328;
}
lean_ctor_set(x_2329, 0, x_2326);
lean_ctor_set(x_2329, 1, x_2327);
return x_2329;
}
}
}
else
{
lean_object* x_2330; lean_object* x_2331; lean_object* x_2332; lean_object* x_2333; 
lean_dec(x_2251);
lean_dec(x_2010);
lean_dec(x_2009);
lean_dec(x_2008);
lean_dec(x_1909);
lean_dec(x_1902);
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
x_2330 = lean_ctor_get(x_2250, 0);
lean_inc(x_2330);
x_2331 = lean_ctor_get(x_2250, 1);
lean_inc(x_2331);
if (lean_is_exclusive(x_2250)) {
 lean_ctor_release(x_2250, 0);
 lean_ctor_release(x_2250, 1);
 x_2332 = x_2250;
} else {
 lean_dec_ref(x_2250);
 x_2332 = lean_box(0);
}
if (lean_is_scalar(x_2332)) {
 x_2333 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2333 = x_2332;
}
lean_ctor_set(x_2333, 0, x_2330);
lean_ctor_set(x_2333, 1, x_2331);
return x_2333;
}
}
}
case 2:
{
lean_object* x_2334; lean_object* x_2335; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_2334 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1911, x_4, x_5, x_6, x_7, x_1909, x_9, x_1912);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_2335 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2335 = lean_box(0);
}
if (lean_obj_tag(x_2334) == 0)
{
lean_object* x_2336; uint8_t x_2337; lean_object* x_2338; lean_object* x_2339; uint8_t x_2340; 
x_2336 = lean_ctor_get(x_2334, 1);
lean_inc(x_2336);
lean_dec(x_2334);
x_2337 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
if (lean_is_scalar(x_2335)) {
 x_2338 = lean_alloc_ctor(0, 8, 2);
} else {
 x_2338 = x_2335;
}
lean_ctor_set(x_2338, 0, x_11);
lean_ctor_set(x_2338, 1, x_12);
lean_ctor_set(x_2338, 2, x_13);
lean_ctor_set(x_2338, 3, x_15);
lean_ctor_set(x_2338, 4, x_16);
lean_ctor_set(x_2338, 5, x_17);
lean_ctor_set(x_2338, 6, x_18);
lean_ctor_set(x_2338, 7, x_19);
lean_ctor_set_uint8(x_2338, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2338, sizeof(void*)*8 + 1, x_2337);
x_2339 = lean_array_get_size(x_12);
x_2340 = lean_nat_dec_lt(x_15, x_2339);
lean_dec(x_2339);
if (x_2340 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_2341; 
x_2341 = l_Lean_Expr_getOptParamDefault_x3f(x_2009);
if (lean_obj_tag(x_2341) == 0)
{
lean_object* x_2342; 
x_2342 = l_Lean_Expr_getAutoParamTactic_x3f(x_2009);
if (lean_obj_tag(x_2342) == 0)
{
uint8_t x_2343; 
lean_dec(x_2338);
lean_dec(x_2010);
lean_dec(x_2009);
x_2343 = l_Array_isEmpty___rarg(x_16);
if (x_2343 == 0)
{
lean_object* x_2344; lean_object* x_2345; lean_object* x_2346; lean_object* x_2347; lean_object* x_2348; lean_object* x_2349; lean_object* x_2350; lean_object* x_2351; lean_object* x_2352; lean_object* x_2353; lean_object* x_2354; lean_object* x_2355; lean_object* x_2356; lean_object* x_2357; lean_object* x_2358; lean_object* x_2359; 
lean_dec(x_1902);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_2344 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2344, 0, x_2008);
x_2345 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_2346 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2346, 0, x_2345);
lean_ctor_set(x_2346, 1, x_2344);
x_2347 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_2348 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2348, 0, x_2346);
lean_ctor_set(x_2348, 1, x_2347);
x_2349 = x_16;
x_2350 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_2012, x_2349);
x_2351 = x_2350;
x_2352 = l_Array_toList___rarg(x_2351);
lean_dec(x_2351);
x_2353 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_2352);
x_2354 = l_Array_HasRepr___rarg___closed__1;
x_2355 = lean_string_append(x_2354, x_2353);
lean_dec(x_2353);
x_2356 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2356, 0, x_2355);
x_2357 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2357, 0, x_2356);
x_2358 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2358, 0, x_2348);
lean_ctor_set(x_2358, 1, x_2357);
x_2359 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2358, x_4, x_5, x_6, x_7, x_1909, x_9, x_2336);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2359;
}
else
{
lean_object* x_2360; uint8_t x_2361; 
lean_dec(x_2008);
lean_dec(x_16);
x_2360 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2361 = l_Lean_checkTraceOption(x_1902, x_2360);
lean_dec(x_1902);
if (x_2361 == 0)
{
lean_object* x_2362; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2362 = x_2336;
goto block_2373;
}
else
{
lean_object* x_2374; lean_object* x_2375; 
x_2374 = lean_ctor_get(x_13, 0);
lean_inc(x_2374);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_2375 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2374, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_2336);
if (lean_obj_tag(x_2375) == 0)
{
lean_object* x_2376; 
x_2376 = lean_ctor_get(x_2375, 1);
lean_inc(x_2376);
lean_dec(x_2375);
x_2362 = x_2376;
goto block_2373;
}
else
{
lean_object* x_2377; lean_object* x_2378; lean_object* x_2379; lean_object* x_2380; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2377 = lean_ctor_get(x_2375, 0);
lean_inc(x_2377);
x_2378 = lean_ctor_get(x_2375, 1);
lean_inc(x_2378);
if (lean_is_exclusive(x_2375)) {
 lean_ctor_release(x_2375, 0);
 lean_ctor_release(x_2375, 1);
 x_2379 = x_2375;
} else {
 lean_dec_ref(x_2375);
 x_2379 = lean_box(0);
}
if (lean_is_scalar(x_2379)) {
 x_2380 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2380 = x_2379;
}
lean_ctor_set(x_2380, 0, x_2377);
lean_ctor_set(x_2380, 1, x_2378);
return x_2380;
}
}
block_2373:
{
lean_object* x_2363; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2363 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2362);
lean_dec(x_17);
if (lean_obj_tag(x_2363) == 0)
{
lean_object* x_2364; lean_object* x_2365; lean_object* x_2366; lean_object* x_2367; lean_object* x_2368; 
x_2364 = lean_ctor_get(x_2363, 1);
lean_inc(x_2364);
lean_dec(x_2363);
lean_inc(x_2);
x_2365 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__12(x_2, x_11, x_19, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2364);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2366 = lean_ctor_get(x_2365, 1);
lean_inc(x_2366);
if (lean_is_exclusive(x_2365)) {
 lean_ctor_release(x_2365, 0);
 lean_ctor_release(x_2365, 1);
 x_2367 = x_2365;
} else {
 lean_dec_ref(x_2365);
 x_2367 = lean_box(0);
}
if (lean_is_scalar(x_2367)) {
 x_2368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2368 = x_2367;
}
lean_ctor_set(x_2368, 0, x_2);
lean_ctor_set(x_2368, 1, x_2366);
return x_2368;
}
else
{
lean_object* x_2369; lean_object* x_2370; lean_object* x_2371; lean_object* x_2372; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2369 = lean_ctor_get(x_2363, 0);
lean_inc(x_2369);
x_2370 = lean_ctor_get(x_2363, 1);
lean_inc(x_2370);
if (lean_is_exclusive(x_2363)) {
 lean_ctor_release(x_2363, 0);
 lean_ctor_release(x_2363, 1);
 x_2371 = x_2363;
} else {
 lean_dec_ref(x_2363);
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
}
else
{
lean_object* x_2381; lean_object* x_2382; lean_object* x_2383; lean_object* x_2384; 
lean_inc(x_2);
x_2381 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2381, 0, x_2);
x_2382 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2360, x_2381, x_4, x_5, x_6, x_7, x_1909, x_9, x_2336);
x_2383 = lean_ctor_get(x_2382, 1);
lean_inc(x_2383);
lean_dec(x_2382);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2384 = x_2383;
goto block_2395;
}
else
{
lean_object* x_2396; lean_object* x_2397; 
x_2396 = lean_ctor_get(x_13, 0);
lean_inc(x_2396);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_2397 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2396, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_2383);
if (lean_obj_tag(x_2397) == 0)
{
lean_object* x_2398; 
x_2398 = lean_ctor_get(x_2397, 1);
lean_inc(x_2398);
lean_dec(x_2397);
x_2384 = x_2398;
goto block_2395;
}
else
{
lean_object* x_2399; lean_object* x_2400; lean_object* x_2401; lean_object* x_2402; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2399 = lean_ctor_get(x_2397, 0);
lean_inc(x_2399);
x_2400 = lean_ctor_get(x_2397, 1);
lean_inc(x_2400);
if (lean_is_exclusive(x_2397)) {
 lean_ctor_release(x_2397, 0);
 lean_ctor_release(x_2397, 1);
 x_2401 = x_2397;
} else {
 lean_dec_ref(x_2397);
 x_2401 = lean_box(0);
}
if (lean_is_scalar(x_2401)) {
 x_2402 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2402 = x_2401;
}
lean_ctor_set(x_2402, 0, x_2399);
lean_ctor_set(x_2402, 1, x_2400);
return x_2402;
}
}
block_2395:
{
lean_object* x_2385; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2385 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2384);
lean_dec(x_17);
if (lean_obj_tag(x_2385) == 0)
{
lean_object* x_2386; lean_object* x_2387; lean_object* x_2388; lean_object* x_2389; lean_object* x_2390; 
x_2386 = lean_ctor_get(x_2385, 1);
lean_inc(x_2386);
lean_dec(x_2385);
lean_inc(x_2);
x_2387 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__13(x_2, x_11, x_19, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2386);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2388 = lean_ctor_get(x_2387, 1);
lean_inc(x_2388);
if (lean_is_exclusive(x_2387)) {
 lean_ctor_release(x_2387, 0);
 lean_ctor_release(x_2387, 1);
 x_2389 = x_2387;
} else {
 lean_dec_ref(x_2387);
 x_2389 = lean_box(0);
}
if (lean_is_scalar(x_2389)) {
 x_2390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2390 = x_2389;
}
lean_ctor_set(x_2390, 0, x_2);
lean_ctor_set(x_2390, 1, x_2388);
return x_2390;
}
else
{
lean_object* x_2391; lean_object* x_2392; lean_object* x_2393; lean_object* x_2394; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2391 = lean_ctor_get(x_2385, 0);
lean_inc(x_2391);
x_2392 = lean_ctor_get(x_2385, 1);
lean_inc(x_2392);
if (lean_is_exclusive(x_2385)) {
 lean_ctor_release(x_2385, 0);
 lean_ctor_release(x_2385, 1);
 x_2393 = x_2385;
} else {
 lean_dec_ref(x_2385);
 x_2393 = lean_box(0);
}
if (lean_is_scalar(x_2393)) {
 x_2394 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2394 = x_2393;
}
lean_ctor_set(x_2394, 0, x_2391);
lean_ctor_set(x_2394, 1, x_2392);
return x_2394;
}
}
}
}
}
else
{
lean_object* x_2403; 
lean_dec(x_2008);
lean_dec(x_1902);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_2403 = lean_ctor_get(x_2342, 0);
lean_inc(x_2403);
lean_dec(x_2342);
if (lean_obj_tag(x_2403) == 4)
{
lean_object* x_2404; lean_object* x_2405; lean_object* x_2406; lean_object* x_2407; lean_object* x_2408; lean_object* x_2409; 
x_2404 = lean_ctor_get(x_2403, 0);
lean_inc(x_2404);
lean_dec(x_2403);
x_2405 = lean_st_ref_get(x_9, x_2336);
x_2406 = lean_ctor_get(x_2405, 0);
lean_inc(x_2406);
x_2407 = lean_ctor_get(x_2405, 1);
lean_inc(x_2407);
lean_dec(x_2405);
x_2408 = lean_ctor_get(x_2406, 0);
lean_inc(x_2408);
lean_dec(x_2406);
x_2409 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_2408, x_2404);
if (lean_obj_tag(x_2409) == 0)
{
lean_object* x_2410; lean_object* x_2411; lean_object* x_2412; lean_object* x_2413; 
lean_dec(x_2338);
lean_dec(x_2010);
lean_dec(x_2009);
lean_dec(x_11);
lean_dec(x_2);
x_2410 = lean_ctor_get(x_2409, 0);
lean_inc(x_2410);
lean_dec(x_2409);
x_2411 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2411, 0, x_2410);
x_2412 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2412, 0, x_2411);
x_2413 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2412, x_4, x_5, x_6, x_7, x_1909, x_9, x_2407);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2413;
}
else
{
lean_object* x_2414; lean_object* x_2415; lean_object* x_2416; lean_object* x_2417; lean_object* x_2418; lean_object* x_2419; lean_object* x_2420; lean_object* x_2421; lean_object* x_2422; lean_object* x_2423; lean_object* x_2424; lean_object* x_2425; lean_object* x_2426; lean_object* x_2427; lean_object* x_2428; lean_object* x_2429; lean_object* x_2430; lean_object* x_2431; lean_object* x_2432; lean_object* x_2433; lean_object* x_2434; lean_object* x_2435; lean_object* x_2436; lean_object* x_2437; lean_object* x_2438; lean_object* x_2439; lean_object* x_2440; lean_object* x_2441; lean_object* x_2442; lean_object* x_2443; lean_object* x_2444; lean_object* x_2445; lean_object* x_2446; lean_object* x_2447; lean_object* x_2448; 
x_2414 = lean_ctor_get(x_2409, 0);
lean_inc(x_2414);
lean_dec(x_2409);
x_2415 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_1909, x_9, x_2407);
x_2416 = lean_ctor_get(x_2415, 1);
lean_inc(x_2416);
lean_dec(x_2415);
x_2417 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_2416);
x_2418 = lean_ctor_get(x_2417, 1);
lean_inc(x_2418);
lean_dec(x_2417);
x_2419 = l_Lean_Syntax_getArgs(x_2414);
lean_dec(x_2414);
x_2420 = l_Array_empty___closed__1;
x_2421 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2419, x_2419, x_2012, x_2420);
lean_dec(x_2419);
x_2422 = l_Lean_nullKind___closed__2;
x_2423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2423, 0, x_2422);
lean_ctor_set(x_2423, 1, x_2421);
x_2424 = lean_array_push(x_2420, x_2423);
x_2425 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__5;
x_2426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2426, 0, x_2425);
lean_ctor_set(x_2426, 1, x_2424);
x_2427 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_2428 = lean_array_push(x_2427, x_2426);
x_2429 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_2430 = lean_array_push(x_2428, x_2429);
x_2431 = l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock___closed__2;
x_2432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2432, 0, x_2431);
lean_ctor_set(x_2432, 1, x_2430);
x_2433 = lean_array_push(x_2420, x_2432);
x_2434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2434, 0, x_2422);
lean_ctor_set(x_2434, 1, x_2433);
x_2435 = lean_array_push(x_2420, x_2434);
x_2436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2436, 0, x_2425);
lean_ctor_set(x_2436, 1, x_2435);
x_2437 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_2438 = lean_array_push(x_2437, x_2436);
x_2439 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_2440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2440, 0, x_2439);
lean_ctor_set(x_2440, 1, x_2438);
x_2441 = l_Lean_Syntax_copyInfo(x_2440, x_11);
lean_dec(x_11);
x_2442 = l_Lean_Expr_getAppNumArgsAux___main(x_2009, x_2012);
x_2443 = lean_nat_sub(x_2442, x_2012);
lean_dec(x_2442);
x_2444 = lean_unsigned_to_nat(1u);
x_2445 = lean_nat_sub(x_2443, x_2444);
lean_dec(x_2443);
x_2446 = l_Lean_Expr_getRevArg_x21___main(x_2009, x_2445);
lean_dec(x_2009);
x_2447 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2447, 0, x_2441);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2448 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2447, x_2446, x_4, x_5, x_6, x_7, x_1909, x_9, x_2418);
if (lean_obj_tag(x_2448) == 0)
{
lean_object* x_2449; lean_object* x_2450; lean_object* x_2451; lean_object* x_2452; 
x_2449 = lean_ctor_get(x_2448, 0);
lean_inc(x_2449);
x_2450 = lean_ctor_get(x_2448, 1);
lean_inc(x_2450);
lean_dec(x_2448);
lean_inc(x_2449);
x_2451 = l_Lean_mkApp(x_2, x_2449);
x_2452 = lean_expr_instantiate1(x_2010, x_2449);
lean_dec(x_2449);
lean_dec(x_2010);
x_1 = x_2338;
x_2 = x_2451;
x_3 = x_2452;
x_8 = x_1909;
x_10 = x_2450;
goto _start;
}
else
{
lean_object* x_2454; lean_object* x_2455; lean_object* x_2456; lean_object* x_2457; 
lean_dec(x_2338);
lean_dec(x_2010);
lean_dec(x_1909);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2454 = lean_ctor_get(x_2448, 0);
lean_inc(x_2454);
x_2455 = lean_ctor_get(x_2448, 1);
lean_inc(x_2455);
if (lean_is_exclusive(x_2448)) {
 lean_ctor_release(x_2448, 0);
 lean_ctor_release(x_2448, 1);
 x_2456 = x_2448;
} else {
 lean_dec_ref(x_2448);
 x_2456 = lean_box(0);
}
if (lean_is_scalar(x_2456)) {
 x_2457 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2457 = x_2456;
}
lean_ctor_set(x_2457, 0, x_2454);
lean_ctor_set(x_2457, 1, x_2455);
return x_2457;
}
}
}
else
{
lean_object* x_2458; lean_object* x_2459; 
lean_dec(x_2403);
lean_dec(x_2338);
lean_dec(x_2010);
lean_dec(x_2009);
lean_dec(x_11);
lean_dec(x_2);
x_2458 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_2459 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2458, x_4, x_5, x_6, x_7, x_1909, x_9, x_2336);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2459;
}
}
}
else
{
lean_object* x_2460; lean_object* x_2461; lean_object* x_2462; 
lean_dec(x_2009);
lean_dec(x_2008);
lean_dec(x_1902);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_2460 = lean_ctor_get(x_2341, 0);
lean_inc(x_2460);
lean_dec(x_2341);
lean_inc(x_2460);
x_2461 = l_Lean_mkApp(x_2, x_2460);
x_2462 = lean_expr_instantiate1(x_2010, x_2460);
lean_dec(x_2460);
lean_dec(x_2010);
x_1 = x_2338;
x_2 = x_2461;
x_3 = x_2462;
x_8 = x_1909;
x_10 = x_2336;
goto _start;
}
}
else
{
uint8_t x_2464; 
lean_dec(x_2338);
lean_dec(x_2010);
lean_dec(x_2009);
x_2464 = l_Array_isEmpty___rarg(x_16);
if (x_2464 == 0)
{
lean_object* x_2465; lean_object* x_2466; lean_object* x_2467; lean_object* x_2468; lean_object* x_2469; lean_object* x_2470; lean_object* x_2471; lean_object* x_2472; lean_object* x_2473; lean_object* x_2474; lean_object* x_2475; lean_object* x_2476; lean_object* x_2477; lean_object* x_2478; lean_object* x_2479; lean_object* x_2480; 
lean_dec(x_1902);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_2465 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2465, 0, x_2008);
x_2466 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_2467 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2467, 0, x_2466);
lean_ctor_set(x_2467, 1, x_2465);
x_2468 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_2469 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2469, 0, x_2467);
lean_ctor_set(x_2469, 1, x_2468);
x_2470 = x_16;
x_2471 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_2012, x_2470);
x_2472 = x_2471;
x_2473 = l_Array_toList___rarg(x_2472);
lean_dec(x_2472);
x_2474 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_2473);
x_2475 = l_Array_HasRepr___rarg___closed__1;
x_2476 = lean_string_append(x_2475, x_2474);
lean_dec(x_2474);
x_2477 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2477, 0, x_2476);
x_2478 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2478, 0, x_2477);
x_2479 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2479, 0, x_2469);
lean_ctor_set(x_2479, 1, x_2478);
x_2480 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2479, x_4, x_5, x_6, x_7, x_1909, x_9, x_2336);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2480;
}
else
{
lean_object* x_2481; uint8_t x_2482; 
lean_dec(x_2008);
lean_dec(x_16);
x_2481 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2482 = l_Lean_checkTraceOption(x_1902, x_2481);
lean_dec(x_1902);
if (x_2482 == 0)
{
lean_object* x_2483; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2483 = x_2336;
goto block_2494;
}
else
{
lean_object* x_2495; lean_object* x_2496; 
x_2495 = lean_ctor_get(x_13, 0);
lean_inc(x_2495);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_2496 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2495, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_2336);
if (lean_obj_tag(x_2496) == 0)
{
lean_object* x_2497; 
x_2497 = lean_ctor_get(x_2496, 1);
lean_inc(x_2497);
lean_dec(x_2496);
x_2483 = x_2497;
goto block_2494;
}
else
{
lean_object* x_2498; lean_object* x_2499; lean_object* x_2500; lean_object* x_2501; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2498 = lean_ctor_get(x_2496, 0);
lean_inc(x_2498);
x_2499 = lean_ctor_get(x_2496, 1);
lean_inc(x_2499);
if (lean_is_exclusive(x_2496)) {
 lean_ctor_release(x_2496, 0);
 lean_ctor_release(x_2496, 1);
 x_2500 = x_2496;
} else {
 lean_dec_ref(x_2496);
 x_2500 = lean_box(0);
}
if (lean_is_scalar(x_2500)) {
 x_2501 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2501 = x_2500;
}
lean_ctor_set(x_2501, 0, x_2498);
lean_ctor_set(x_2501, 1, x_2499);
return x_2501;
}
}
block_2494:
{
lean_object* x_2484; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2484 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2483);
lean_dec(x_17);
if (lean_obj_tag(x_2484) == 0)
{
lean_object* x_2485; lean_object* x_2486; lean_object* x_2487; lean_object* x_2488; lean_object* x_2489; 
x_2485 = lean_ctor_get(x_2484, 1);
lean_inc(x_2485);
lean_dec(x_2484);
lean_inc(x_2);
x_2486 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__14(x_2, x_11, x_19, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2485);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2487 = lean_ctor_get(x_2486, 1);
lean_inc(x_2487);
if (lean_is_exclusive(x_2486)) {
 lean_ctor_release(x_2486, 0);
 lean_ctor_release(x_2486, 1);
 x_2488 = x_2486;
} else {
 lean_dec_ref(x_2486);
 x_2488 = lean_box(0);
}
if (lean_is_scalar(x_2488)) {
 x_2489 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2489 = x_2488;
}
lean_ctor_set(x_2489, 0, x_2);
lean_ctor_set(x_2489, 1, x_2487);
return x_2489;
}
else
{
lean_object* x_2490; lean_object* x_2491; lean_object* x_2492; lean_object* x_2493; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2490 = lean_ctor_get(x_2484, 0);
lean_inc(x_2490);
x_2491 = lean_ctor_get(x_2484, 1);
lean_inc(x_2491);
if (lean_is_exclusive(x_2484)) {
 lean_ctor_release(x_2484, 0);
 lean_ctor_release(x_2484, 1);
 x_2492 = x_2484;
} else {
 lean_dec_ref(x_2484);
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
}
else
{
lean_object* x_2502; lean_object* x_2503; lean_object* x_2504; lean_object* x_2505; 
lean_inc(x_2);
x_2502 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2502, 0, x_2);
x_2503 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2481, x_2502, x_4, x_5, x_6, x_7, x_1909, x_9, x_2336);
x_2504 = lean_ctor_get(x_2503, 1);
lean_inc(x_2504);
lean_dec(x_2503);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2505 = x_2504;
goto block_2516;
}
else
{
lean_object* x_2517; lean_object* x_2518; 
x_2517 = lean_ctor_get(x_13, 0);
lean_inc(x_2517);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_2518 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2517, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_2504);
if (lean_obj_tag(x_2518) == 0)
{
lean_object* x_2519; 
x_2519 = lean_ctor_get(x_2518, 1);
lean_inc(x_2519);
lean_dec(x_2518);
x_2505 = x_2519;
goto block_2516;
}
else
{
lean_object* x_2520; lean_object* x_2521; lean_object* x_2522; lean_object* x_2523; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2520 = lean_ctor_get(x_2518, 0);
lean_inc(x_2520);
x_2521 = lean_ctor_get(x_2518, 1);
lean_inc(x_2521);
if (lean_is_exclusive(x_2518)) {
 lean_ctor_release(x_2518, 0);
 lean_ctor_release(x_2518, 1);
 x_2522 = x_2518;
} else {
 lean_dec_ref(x_2518);
 x_2522 = lean_box(0);
}
if (lean_is_scalar(x_2522)) {
 x_2523 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2523 = x_2522;
}
lean_ctor_set(x_2523, 0, x_2520);
lean_ctor_set(x_2523, 1, x_2521);
return x_2523;
}
}
block_2516:
{
lean_object* x_2506; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2506 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2505);
lean_dec(x_17);
if (lean_obj_tag(x_2506) == 0)
{
lean_object* x_2507; lean_object* x_2508; lean_object* x_2509; lean_object* x_2510; lean_object* x_2511; 
x_2507 = lean_ctor_get(x_2506, 1);
lean_inc(x_2507);
lean_dec(x_2506);
lean_inc(x_2);
x_2508 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__15(x_2, x_11, x_19, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2507);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2509 = lean_ctor_get(x_2508, 1);
lean_inc(x_2509);
if (lean_is_exclusive(x_2508)) {
 lean_ctor_release(x_2508, 0);
 lean_ctor_release(x_2508, 1);
 x_2510 = x_2508;
} else {
 lean_dec_ref(x_2508);
 x_2510 = lean_box(0);
}
if (lean_is_scalar(x_2510)) {
 x_2511 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2511 = x_2510;
}
lean_ctor_set(x_2511, 0, x_2);
lean_ctor_set(x_2511, 1, x_2509);
return x_2511;
}
else
{
lean_object* x_2512; lean_object* x_2513; lean_object* x_2514; lean_object* x_2515; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2512 = lean_ctor_get(x_2506, 0);
lean_inc(x_2512);
x_2513 = lean_ctor_get(x_2506, 1);
lean_inc(x_2513);
if (lean_is_exclusive(x_2506)) {
 lean_ctor_release(x_2506, 0);
 lean_ctor_release(x_2506, 1);
 x_2514 = x_2506;
} else {
 lean_dec_ref(x_2506);
 x_2514 = lean_box(0);
}
if (lean_is_scalar(x_2514)) {
 x_2515 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2515 = x_2514;
}
lean_ctor_set(x_2515, 0, x_2512);
lean_ctor_set(x_2515, 1, x_2513);
return x_2515;
}
}
}
}
}
}
else
{
lean_object* x_2524; lean_object* x_2525; 
lean_dec(x_2338);
lean_dec(x_2008);
lean_dec(x_1902);
lean_dec(x_3);
x_2524 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2525 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2524, x_2009, x_4, x_5, x_6, x_7, x_1909, x_9, x_2336);
if (lean_obj_tag(x_2525) == 0)
{
lean_object* x_2526; lean_object* x_2527; lean_object* x_2528; lean_object* x_2529; lean_object* x_2530; lean_object* x_2531; lean_object* x_2532; 
x_2526 = lean_ctor_get(x_2525, 0);
lean_inc(x_2526);
x_2527 = lean_ctor_get(x_2525, 1);
lean_inc(x_2527);
lean_dec(x_2525);
x_2528 = lean_unsigned_to_nat(1u);
x_2529 = lean_nat_add(x_15, x_2528);
lean_dec(x_15);
x_2530 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_2530, 0, x_11);
lean_ctor_set(x_2530, 1, x_12);
lean_ctor_set(x_2530, 2, x_13);
lean_ctor_set(x_2530, 3, x_2529);
lean_ctor_set(x_2530, 4, x_16);
lean_ctor_set(x_2530, 5, x_17);
lean_ctor_set(x_2530, 6, x_18);
lean_ctor_set(x_2530, 7, x_19);
lean_ctor_set_uint8(x_2530, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2530, sizeof(void*)*8 + 1, x_2337);
lean_inc(x_2526);
x_2531 = l_Lean_mkApp(x_2, x_2526);
x_2532 = lean_expr_instantiate1(x_2010, x_2526);
lean_dec(x_2526);
lean_dec(x_2010);
x_1 = x_2530;
x_2 = x_2531;
x_3 = x_2532;
x_8 = x_1909;
x_10 = x_2527;
goto _start;
}
else
{
lean_object* x_2534; lean_object* x_2535; lean_object* x_2536; lean_object* x_2537; 
lean_dec(x_2010);
lean_dec(x_1909);
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
x_2534 = lean_ctor_get(x_2525, 0);
lean_inc(x_2534);
x_2535 = lean_ctor_get(x_2525, 1);
lean_inc(x_2535);
if (lean_is_exclusive(x_2525)) {
 lean_ctor_release(x_2525, 0);
 lean_ctor_release(x_2525, 1);
 x_2536 = x_2525;
} else {
 lean_dec_ref(x_2525);
 x_2536 = lean_box(0);
}
if (lean_is_scalar(x_2536)) {
 x_2537 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2537 = x_2536;
}
lean_ctor_set(x_2537, 0, x_2534);
lean_ctor_set(x_2537, 1, x_2535);
return x_2537;
}
}
}
else
{
lean_object* x_2538; lean_object* x_2539; lean_object* x_2540; lean_object* x_2541; 
lean_dec(x_2335);
lean_dec(x_2010);
lean_dec(x_2009);
lean_dec(x_2008);
lean_dec(x_1909);
lean_dec(x_1902);
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
x_2538 = lean_ctor_get(x_2334, 0);
lean_inc(x_2538);
x_2539 = lean_ctor_get(x_2334, 1);
lean_inc(x_2539);
if (lean_is_exclusive(x_2334)) {
 lean_ctor_release(x_2334, 0);
 lean_ctor_release(x_2334, 1);
 x_2540 = x_2334;
} else {
 lean_dec_ref(x_2334);
 x_2540 = lean_box(0);
}
if (lean_is_scalar(x_2540)) {
 x_2541 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2541 = x_2540;
}
lean_ctor_set(x_2541, 0, x_2538);
lean_ctor_set(x_2541, 1, x_2539);
return x_2541;
}
}
case 3:
{
if (x_14 == 0)
{
lean_object* x_2542; lean_object* x_2543; uint8_t x_2544; lean_object* x_2545; lean_object* x_2546; lean_object* x_2547; lean_object* x_2548; lean_object* x_2549; lean_object* x_2550; lean_object* x_2551; lean_object* x_2552; lean_object* x_2553; 
lean_dec(x_2008);
lean_dec(x_1911);
lean_dec(x_1902);
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
 x_2542 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2542 = lean_box(0);
}
x_2543 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2543, 0, x_2009);
x_2544 = 1;
x_2545 = lean_box(0);
lean_inc(x_6);
x_2546 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_2543, x_2544, x_2545, x_6, x_7, x_1909, x_9, x_1912);
x_2547 = lean_ctor_get(x_2546, 0);
lean_inc(x_2547);
x_2548 = lean_ctor_get(x_2546, 1);
lean_inc(x_2548);
lean_dec(x_2546);
x_2549 = l_Lean_Expr_mvarId_x21(x_2547);
x_2550 = lean_array_push(x_17, x_2549);
if (lean_is_scalar(x_2542)) {
 x_2551 = lean_alloc_ctor(0, 8, 2);
} else {
 x_2551 = x_2542;
}
lean_ctor_set(x_2551, 0, x_11);
lean_ctor_set(x_2551, 1, x_12);
lean_ctor_set(x_2551, 2, x_13);
lean_ctor_set(x_2551, 3, x_15);
lean_ctor_set(x_2551, 4, x_16);
lean_ctor_set(x_2551, 5, x_2550);
lean_ctor_set(x_2551, 6, x_18);
lean_ctor_set(x_2551, 7, x_19);
lean_ctor_set_uint8(x_2551, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2551, sizeof(void*)*8 + 1, x_1901);
lean_inc(x_2547);
x_2552 = l_Lean_mkApp(x_2, x_2547);
x_2553 = lean_expr_instantiate1(x_2010, x_2547);
lean_dec(x_2547);
lean_dec(x_2010);
x_1 = x_2551;
x_2 = x_2552;
x_3 = x_2553;
x_8 = x_1909;
x_10 = x_2548;
goto _start;
}
else
{
uint8_t x_2555; 
x_2555 = l___private_Lean_Elab_App_9__nextArgIsHole(x_1);
if (x_2555 == 0)
{
lean_object* x_2556; lean_object* x_2557; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_2556 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1911, x_4, x_5, x_6, x_7, x_1909, x_9, x_1912);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_2557 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2557 = lean_box(0);
}
if (lean_obj_tag(x_2556) == 0)
{
lean_object* x_2558; lean_object* x_2559; uint8_t x_2560; 
x_2558 = lean_ctor_get(x_2556, 1);
lean_inc(x_2558);
lean_dec(x_2556);
x_2559 = lean_array_get_size(x_12);
x_2560 = lean_nat_dec_lt(x_15, x_2559);
lean_dec(x_2559);
if (x_2560 == 0)
{
uint8_t x_2561; 
lean_dec(x_2557);
lean_dec(x_2010);
lean_dec(x_2009);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
x_2561 = l_Array_isEmpty___rarg(x_16);
if (x_2561 == 0)
{
lean_object* x_2562; lean_object* x_2563; lean_object* x_2564; lean_object* x_2565; lean_object* x_2566; lean_object* x_2567; lean_object* x_2568; lean_object* x_2569; lean_object* x_2570; lean_object* x_2571; lean_object* x_2572; lean_object* x_2573; lean_object* x_2574; lean_object* x_2575; lean_object* x_2576; lean_object* x_2577; 
lean_dec(x_1902);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_2562 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2562, 0, x_2008);
x_2563 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_2564 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2564, 0, x_2563);
lean_ctor_set(x_2564, 1, x_2562);
x_2565 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_2566 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2566, 0, x_2564);
lean_ctor_set(x_2566, 1, x_2565);
x_2567 = x_16;
x_2568 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_2012, x_2567);
x_2569 = x_2568;
x_2570 = l_Array_toList___rarg(x_2569);
lean_dec(x_2569);
x_2571 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_2570);
x_2572 = l_Array_HasRepr___rarg___closed__1;
x_2573 = lean_string_append(x_2572, x_2571);
lean_dec(x_2571);
x_2574 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2574, 0, x_2573);
x_2575 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2575, 0, x_2574);
x_2576 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2576, 0, x_2566);
lean_ctor_set(x_2576, 1, x_2575);
x_2577 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2576, x_4, x_5, x_6, x_7, x_1909, x_9, x_2558);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2577;
}
else
{
lean_object* x_2578; uint8_t x_2579; 
lean_dec(x_2008);
lean_dec(x_16);
x_2578 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2579 = l_Lean_checkTraceOption(x_1902, x_2578);
lean_dec(x_1902);
if (x_2579 == 0)
{
lean_object* x_2580; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2580 = x_2558;
goto block_2591;
}
else
{
lean_object* x_2592; lean_object* x_2593; 
x_2592 = lean_ctor_get(x_13, 0);
lean_inc(x_2592);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_2593 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2592, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_2558);
if (lean_obj_tag(x_2593) == 0)
{
lean_object* x_2594; 
x_2594 = lean_ctor_get(x_2593, 1);
lean_inc(x_2594);
lean_dec(x_2593);
x_2580 = x_2594;
goto block_2591;
}
else
{
lean_object* x_2595; lean_object* x_2596; lean_object* x_2597; lean_object* x_2598; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2595 = lean_ctor_get(x_2593, 0);
lean_inc(x_2595);
x_2596 = lean_ctor_get(x_2593, 1);
lean_inc(x_2596);
if (lean_is_exclusive(x_2593)) {
 lean_ctor_release(x_2593, 0);
 lean_ctor_release(x_2593, 1);
 x_2597 = x_2593;
} else {
 lean_dec_ref(x_2593);
 x_2597 = lean_box(0);
}
if (lean_is_scalar(x_2597)) {
 x_2598 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2598 = x_2597;
}
lean_ctor_set(x_2598, 0, x_2595);
lean_ctor_set(x_2598, 1, x_2596);
return x_2598;
}
}
block_2591:
{
lean_object* x_2581; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2581 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2580);
lean_dec(x_17);
if (lean_obj_tag(x_2581) == 0)
{
lean_object* x_2582; lean_object* x_2583; lean_object* x_2584; lean_object* x_2585; lean_object* x_2586; 
x_2582 = lean_ctor_get(x_2581, 1);
lean_inc(x_2582);
lean_dec(x_2581);
lean_inc(x_2);
x_2583 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__16(x_2, x_11, x_19, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2582);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2584 = lean_ctor_get(x_2583, 1);
lean_inc(x_2584);
if (lean_is_exclusive(x_2583)) {
 lean_ctor_release(x_2583, 0);
 lean_ctor_release(x_2583, 1);
 x_2585 = x_2583;
} else {
 lean_dec_ref(x_2583);
 x_2585 = lean_box(0);
}
if (lean_is_scalar(x_2585)) {
 x_2586 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2586 = x_2585;
}
lean_ctor_set(x_2586, 0, x_2);
lean_ctor_set(x_2586, 1, x_2584);
return x_2586;
}
else
{
lean_object* x_2587; lean_object* x_2588; lean_object* x_2589; lean_object* x_2590; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2587 = lean_ctor_get(x_2581, 0);
lean_inc(x_2587);
x_2588 = lean_ctor_get(x_2581, 1);
lean_inc(x_2588);
if (lean_is_exclusive(x_2581)) {
 lean_ctor_release(x_2581, 0);
 lean_ctor_release(x_2581, 1);
 x_2589 = x_2581;
} else {
 lean_dec_ref(x_2581);
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
}
else
{
lean_object* x_2599; lean_object* x_2600; lean_object* x_2601; lean_object* x_2602; 
lean_inc(x_2);
x_2599 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2599, 0, x_2);
x_2600 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2578, x_2599, x_4, x_5, x_6, x_7, x_1909, x_9, x_2558);
x_2601 = lean_ctor_get(x_2600, 1);
lean_inc(x_2601);
lean_dec(x_2600);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2602 = x_2601;
goto block_2613;
}
else
{
lean_object* x_2614; lean_object* x_2615; 
x_2614 = lean_ctor_get(x_13, 0);
lean_inc(x_2614);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_2615 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2614, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_2601);
if (lean_obj_tag(x_2615) == 0)
{
lean_object* x_2616; 
x_2616 = lean_ctor_get(x_2615, 1);
lean_inc(x_2616);
lean_dec(x_2615);
x_2602 = x_2616;
goto block_2613;
}
else
{
lean_object* x_2617; lean_object* x_2618; lean_object* x_2619; lean_object* x_2620; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2617 = lean_ctor_get(x_2615, 0);
lean_inc(x_2617);
x_2618 = lean_ctor_get(x_2615, 1);
lean_inc(x_2618);
if (lean_is_exclusive(x_2615)) {
 lean_ctor_release(x_2615, 0);
 lean_ctor_release(x_2615, 1);
 x_2619 = x_2615;
} else {
 lean_dec_ref(x_2615);
 x_2619 = lean_box(0);
}
if (lean_is_scalar(x_2619)) {
 x_2620 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2620 = x_2619;
}
lean_ctor_set(x_2620, 0, x_2617);
lean_ctor_set(x_2620, 1, x_2618);
return x_2620;
}
}
block_2613:
{
lean_object* x_2603; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2603 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2602);
lean_dec(x_17);
if (lean_obj_tag(x_2603) == 0)
{
lean_object* x_2604; lean_object* x_2605; lean_object* x_2606; lean_object* x_2607; lean_object* x_2608; 
x_2604 = lean_ctor_get(x_2603, 1);
lean_inc(x_2604);
lean_dec(x_2603);
lean_inc(x_2);
x_2605 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__17(x_2, x_11, x_19, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2604);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2606 = lean_ctor_get(x_2605, 1);
lean_inc(x_2606);
if (lean_is_exclusive(x_2605)) {
 lean_ctor_release(x_2605, 0);
 lean_ctor_release(x_2605, 1);
 x_2607 = x_2605;
} else {
 lean_dec_ref(x_2605);
 x_2607 = lean_box(0);
}
if (lean_is_scalar(x_2607)) {
 x_2608 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2608 = x_2607;
}
lean_ctor_set(x_2608, 0, x_2);
lean_ctor_set(x_2608, 1, x_2606);
return x_2608;
}
else
{
lean_object* x_2609; lean_object* x_2610; lean_object* x_2611; lean_object* x_2612; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2609 = lean_ctor_get(x_2603, 0);
lean_inc(x_2609);
x_2610 = lean_ctor_get(x_2603, 1);
lean_inc(x_2610);
if (lean_is_exclusive(x_2603)) {
 lean_ctor_release(x_2603, 0);
 lean_ctor_release(x_2603, 1);
 x_2611 = x_2603;
} else {
 lean_dec_ref(x_2603);
 x_2611 = lean_box(0);
}
if (lean_is_scalar(x_2611)) {
 x_2612 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2612 = x_2611;
}
lean_ctor_set(x_2612, 0, x_2609);
lean_ctor_set(x_2612, 1, x_2610);
return x_2612;
}
}
}
}
}
else
{
lean_object* x_2621; lean_object* x_2622; 
lean_dec(x_2008);
lean_dec(x_1902);
lean_dec(x_3);
x_2621 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2622 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2621, x_2009, x_4, x_5, x_6, x_7, x_1909, x_9, x_2558);
if (lean_obj_tag(x_2622) == 0)
{
lean_object* x_2623; lean_object* x_2624; lean_object* x_2625; lean_object* x_2626; uint8_t x_2627; lean_object* x_2628; lean_object* x_2629; lean_object* x_2630; 
x_2623 = lean_ctor_get(x_2622, 0);
lean_inc(x_2623);
x_2624 = lean_ctor_get(x_2622, 1);
lean_inc(x_2624);
lean_dec(x_2622);
x_2625 = lean_unsigned_to_nat(1u);
x_2626 = lean_nat_add(x_15, x_2625);
lean_dec(x_15);
x_2627 = 1;
if (lean_is_scalar(x_2557)) {
 x_2628 = lean_alloc_ctor(0, 8, 2);
} else {
 x_2628 = x_2557;
}
lean_ctor_set(x_2628, 0, x_11);
lean_ctor_set(x_2628, 1, x_12);
lean_ctor_set(x_2628, 2, x_13);
lean_ctor_set(x_2628, 3, x_2626);
lean_ctor_set(x_2628, 4, x_16);
lean_ctor_set(x_2628, 5, x_17);
lean_ctor_set(x_2628, 6, x_18);
lean_ctor_set(x_2628, 7, x_19);
lean_ctor_set_uint8(x_2628, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2628, sizeof(void*)*8 + 1, x_2627);
lean_inc(x_2623);
x_2629 = l_Lean_mkApp(x_2, x_2623);
x_2630 = lean_expr_instantiate1(x_2010, x_2623);
lean_dec(x_2623);
lean_dec(x_2010);
x_1 = x_2628;
x_2 = x_2629;
x_3 = x_2630;
x_8 = x_1909;
x_10 = x_2624;
goto _start;
}
else
{
lean_object* x_2632; lean_object* x_2633; lean_object* x_2634; lean_object* x_2635; 
lean_dec(x_2557);
lean_dec(x_2010);
lean_dec(x_1909);
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
x_2632 = lean_ctor_get(x_2622, 0);
lean_inc(x_2632);
x_2633 = lean_ctor_get(x_2622, 1);
lean_inc(x_2633);
if (lean_is_exclusive(x_2622)) {
 lean_ctor_release(x_2622, 0);
 lean_ctor_release(x_2622, 1);
 x_2634 = x_2622;
} else {
 lean_dec_ref(x_2622);
 x_2634 = lean_box(0);
}
if (lean_is_scalar(x_2634)) {
 x_2635 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2635 = x_2634;
}
lean_ctor_set(x_2635, 0, x_2632);
lean_ctor_set(x_2635, 1, x_2633);
return x_2635;
}
}
}
else
{
lean_object* x_2636; lean_object* x_2637; lean_object* x_2638; lean_object* x_2639; 
lean_dec(x_2557);
lean_dec(x_2010);
lean_dec(x_2009);
lean_dec(x_2008);
lean_dec(x_1909);
lean_dec(x_1902);
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
x_2636 = lean_ctor_get(x_2556, 0);
lean_inc(x_2636);
x_2637 = lean_ctor_get(x_2556, 1);
lean_inc(x_2637);
if (lean_is_exclusive(x_2556)) {
 lean_ctor_release(x_2556, 0);
 lean_ctor_release(x_2556, 1);
 x_2638 = x_2556;
} else {
 lean_dec_ref(x_2556);
 x_2638 = lean_box(0);
}
if (lean_is_scalar(x_2638)) {
 x_2639 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2639 = x_2638;
}
lean_ctor_set(x_2639, 0, x_2636);
lean_ctor_set(x_2639, 1, x_2637);
return x_2639;
}
}
else
{
lean_object* x_2640; lean_object* x_2641; uint8_t x_2642; lean_object* x_2643; lean_object* x_2644; lean_object* x_2645; lean_object* x_2646; lean_object* x_2647; lean_object* x_2648; lean_object* x_2649; lean_object* x_2650; lean_object* x_2651; lean_object* x_2652; lean_object* x_2653; 
lean_dec(x_2008);
lean_dec(x_1911);
lean_dec(x_1902);
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
 x_2640 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2640 = lean_box(0);
}
x_2641 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2641, 0, x_2009);
x_2642 = 1;
x_2643 = lean_box(0);
lean_inc(x_6);
x_2644 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_2641, x_2642, x_2643, x_6, x_7, x_1909, x_9, x_1912);
x_2645 = lean_ctor_get(x_2644, 0);
lean_inc(x_2645);
x_2646 = lean_ctor_get(x_2644, 1);
lean_inc(x_2646);
lean_dec(x_2644);
x_2647 = lean_unsigned_to_nat(1u);
x_2648 = lean_nat_add(x_15, x_2647);
lean_dec(x_15);
x_2649 = l_Lean_Expr_mvarId_x21(x_2645);
x_2650 = lean_array_push(x_17, x_2649);
if (lean_is_scalar(x_2640)) {
 x_2651 = lean_alloc_ctor(0, 8, 2);
} else {
 x_2651 = x_2640;
}
lean_ctor_set(x_2651, 0, x_11);
lean_ctor_set(x_2651, 1, x_12);
lean_ctor_set(x_2651, 2, x_13);
lean_ctor_set(x_2651, 3, x_2648);
lean_ctor_set(x_2651, 4, x_16);
lean_ctor_set(x_2651, 5, x_2650);
lean_ctor_set(x_2651, 6, x_18);
lean_ctor_set(x_2651, 7, x_19);
lean_ctor_set_uint8(x_2651, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2651, sizeof(void*)*8 + 1, x_1901);
lean_inc(x_2645);
x_2652 = l_Lean_mkApp(x_2, x_2645);
x_2653 = lean_expr_instantiate1(x_2010, x_2645);
lean_dec(x_2645);
lean_dec(x_2010);
x_1 = x_2651;
x_2 = x_2652;
x_3 = x_2653;
x_8 = x_1909;
x_10 = x_2646;
goto _start;
}
}
}
default: 
{
lean_object* x_2655; lean_object* x_2656; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_2655 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1911, x_4, x_5, x_6, x_7, x_1909, x_9, x_1912);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_2656 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2656 = lean_box(0);
}
if (lean_obj_tag(x_2655) == 0)
{
lean_object* x_2657; uint8_t x_2658; lean_object* x_2659; lean_object* x_2660; uint8_t x_2661; 
x_2657 = lean_ctor_get(x_2655, 1);
lean_inc(x_2657);
lean_dec(x_2655);
x_2658 = 1;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
if (lean_is_scalar(x_2656)) {
 x_2659 = lean_alloc_ctor(0, 8, 2);
} else {
 x_2659 = x_2656;
}
lean_ctor_set(x_2659, 0, x_11);
lean_ctor_set(x_2659, 1, x_12);
lean_ctor_set(x_2659, 2, x_13);
lean_ctor_set(x_2659, 3, x_15);
lean_ctor_set(x_2659, 4, x_16);
lean_ctor_set(x_2659, 5, x_17);
lean_ctor_set(x_2659, 6, x_18);
lean_ctor_set(x_2659, 7, x_19);
lean_ctor_set_uint8(x_2659, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2659, sizeof(void*)*8 + 1, x_2658);
x_2660 = lean_array_get_size(x_12);
x_2661 = lean_nat_dec_lt(x_15, x_2660);
lean_dec(x_2660);
if (x_2661 == 0)
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_2662; 
x_2662 = l_Lean_Expr_getOptParamDefault_x3f(x_2009);
if (lean_obj_tag(x_2662) == 0)
{
lean_object* x_2663; 
x_2663 = l_Lean_Expr_getAutoParamTactic_x3f(x_2009);
if (lean_obj_tag(x_2663) == 0)
{
uint8_t x_2664; 
lean_dec(x_2659);
lean_dec(x_2010);
lean_dec(x_2009);
x_2664 = l_Array_isEmpty___rarg(x_16);
if (x_2664 == 0)
{
lean_object* x_2665; lean_object* x_2666; lean_object* x_2667; lean_object* x_2668; lean_object* x_2669; lean_object* x_2670; lean_object* x_2671; lean_object* x_2672; lean_object* x_2673; lean_object* x_2674; lean_object* x_2675; lean_object* x_2676; lean_object* x_2677; lean_object* x_2678; lean_object* x_2679; lean_object* x_2680; 
lean_dec(x_1902);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_2665 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2665, 0, x_2008);
x_2666 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_2667 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2667, 0, x_2666);
lean_ctor_set(x_2667, 1, x_2665);
x_2668 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_2669 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2669, 0, x_2667);
lean_ctor_set(x_2669, 1, x_2668);
x_2670 = x_16;
x_2671 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_2012, x_2670);
x_2672 = x_2671;
x_2673 = l_Array_toList___rarg(x_2672);
lean_dec(x_2672);
x_2674 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_2673);
x_2675 = l_Array_HasRepr___rarg___closed__1;
x_2676 = lean_string_append(x_2675, x_2674);
lean_dec(x_2674);
x_2677 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2677, 0, x_2676);
x_2678 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2678, 0, x_2677);
x_2679 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2679, 0, x_2669);
lean_ctor_set(x_2679, 1, x_2678);
x_2680 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2679, x_4, x_5, x_6, x_7, x_1909, x_9, x_2657);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2680;
}
else
{
lean_object* x_2681; uint8_t x_2682; 
lean_dec(x_2008);
lean_dec(x_16);
x_2681 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2682 = l_Lean_checkTraceOption(x_1902, x_2681);
lean_dec(x_1902);
if (x_2682 == 0)
{
lean_object* x_2683; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2683 = x_2657;
goto block_2694;
}
else
{
lean_object* x_2695; lean_object* x_2696; 
x_2695 = lean_ctor_get(x_13, 0);
lean_inc(x_2695);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_2696 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2695, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_2657);
if (lean_obj_tag(x_2696) == 0)
{
lean_object* x_2697; 
x_2697 = lean_ctor_get(x_2696, 1);
lean_inc(x_2697);
lean_dec(x_2696);
x_2683 = x_2697;
goto block_2694;
}
else
{
lean_object* x_2698; lean_object* x_2699; lean_object* x_2700; lean_object* x_2701; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2698 = lean_ctor_get(x_2696, 0);
lean_inc(x_2698);
x_2699 = lean_ctor_get(x_2696, 1);
lean_inc(x_2699);
if (lean_is_exclusive(x_2696)) {
 lean_ctor_release(x_2696, 0);
 lean_ctor_release(x_2696, 1);
 x_2700 = x_2696;
} else {
 lean_dec_ref(x_2696);
 x_2700 = lean_box(0);
}
if (lean_is_scalar(x_2700)) {
 x_2701 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2701 = x_2700;
}
lean_ctor_set(x_2701, 0, x_2698);
lean_ctor_set(x_2701, 1, x_2699);
return x_2701;
}
}
block_2694:
{
lean_object* x_2684; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2684 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2683);
lean_dec(x_17);
if (lean_obj_tag(x_2684) == 0)
{
lean_object* x_2685; lean_object* x_2686; lean_object* x_2687; lean_object* x_2688; lean_object* x_2689; 
x_2685 = lean_ctor_get(x_2684, 1);
lean_inc(x_2685);
lean_dec(x_2684);
lean_inc(x_2);
x_2686 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__18(x_2, x_11, x_19, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2685);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2687 = lean_ctor_get(x_2686, 1);
lean_inc(x_2687);
if (lean_is_exclusive(x_2686)) {
 lean_ctor_release(x_2686, 0);
 lean_ctor_release(x_2686, 1);
 x_2688 = x_2686;
} else {
 lean_dec_ref(x_2686);
 x_2688 = lean_box(0);
}
if (lean_is_scalar(x_2688)) {
 x_2689 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2689 = x_2688;
}
lean_ctor_set(x_2689, 0, x_2);
lean_ctor_set(x_2689, 1, x_2687);
return x_2689;
}
else
{
lean_object* x_2690; lean_object* x_2691; lean_object* x_2692; lean_object* x_2693; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2690 = lean_ctor_get(x_2684, 0);
lean_inc(x_2690);
x_2691 = lean_ctor_get(x_2684, 1);
lean_inc(x_2691);
if (lean_is_exclusive(x_2684)) {
 lean_ctor_release(x_2684, 0);
 lean_ctor_release(x_2684, 1);
 x_2692 = x_2684;
} else {
 lean_dec_ref(x_2684);
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
}
else
{
lean_object* x_2702; lean_object* x_2703; lean_object* x_2704; lean_object* x_2705; 
lean_inc(x_2);
x_2702 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2702, 0, x_2);
x_2703 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2681, x_2702, x_4, x_5, x_6, x_7, x_1909, x_9, x_2657);
x_2704 = lean_ctor_get(x_2703, 1);
lean_inc(x_2704);
lean_dec(x_2703);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2705 = x_2704;
goto block_2716;
}
else
{
lean_object* x_2717; lean_object* x_2718; 
x_2717 = lean_ctor_get(x_13, 0);
lean_inc(x_2717);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_2718 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2717, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_2704);
if (lean_obj_tag(x_2718) == 0)
{
lean_object* x_2719; 
x_2719 = lean_ctor_get(x_2718, 1);
lean_inc(x_2719);
lean_dec(x_2718);
x_2705 = x_2719;
goto block_2716;
}
else
{
lean_object* x_2720; lean_object* x_2721; lean_object* x_2722; lean_object* x_2723; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2720 = lean_ctor_get(x_2718, 0);
lean_inc(x_2720);
x_2721 = lean_ctor_get(x_2718, 1);
lean_inc(x_2721);
if (lean_is_exclusive(x_2718)) {
 lean_ctor_release(x_2718, 0);
 lean_ctor_release(x_2718, 1);
 x_2722 = x_2718;
} else {
 lean_dec_ref(x_2718);
 x_2722 = lean_box(0);
}
if (lean_is_scalar(x_2722)) {
 x_2723 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2723 = x_2722;
}
lean_ctor_set(x_2723, 0, x_2720);
lean_ctor_set(x_2723, 1, x_2721);
return x_2723;
}
}
block_2716:
{
lean_object* x_2706; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2706 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2705);
lean_dec(x_17);
if (lean_obj_tag(x_2706) == 0)
{
lean_object* x_2707; lean_object* x_2708; lean_object* x_2709; lean_object* x_2710; lean_object* x_2711; 
x_2707 = lean_ctor_get(x_2706, 1);
lean_inc(x_2707);
lean_dec(x_2706);
lean_inc(x_2);
x_2708 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__19(x_2, x_11, x_19, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2707);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2709 = lean_ctor_get(x_2708, 1);
lean_inc(x_2709);
if (lean_is_exclusive(x_2708)) {
 lean_ctor_release(x_2708, 0);
 lean_ctor_release(x_2708, 1);
 x_2710 = x_2708;
} else {
 lean_dec_ref(x_2708);
 x_2710 = lean_box(0);
}
if (lean_is_scalar(x_2710)) {
 x_2711 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2711 = x_2710;
}
lean_ctor_set(x_2711, 0, x_2);
lean_ctor_set(x_2711, 1, x_2709);
return x_2711;
}
else
{
lean_object* x_2712; lean_object* x_2713; lean_object* x_2714; lean_object* x_2715; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2712 = lean_ctor_get(x_2706, 0);
lean_inc(x_2712);
x_2713 = lean_ctor_get(x_2706, 1);
lean_inc(x_2713);
if (lean_is_exclusive(x_2706)) {
 lean_ctor_release(x_2706, 0);
 lean_ctor_release(x_2706, 1);
 x_2714 = x_2706;
} else {
 lean_dec_ref(x_2706);
 x_2714 = lean_box(0);
}
if (lean_is_scalar(x_2714)) {
 x_2715 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2715 = x_2714;
}
lean_ctor_set(x_2715, 0, x_2712);
lean_ctor_set(x_2715, 1, x_2713);
return x_2715;
}
}
}
}
}
else
{
lean_object* x_2724; 
lean_dec(x_2008);
lean_dec(x_1902);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_3);
x_2724 = lean_ctor_get(x_2663, 0);
lean_inc(x_2724);
lean_dec(x_2663);
if (lean_obj_tag(x_2724) == 4)
{
lean_object* x_2725; lean_object* x_2726; lean_object* x_2727; lean_object* x_2728; lean_object* x_2729; lean_object* x_2730; 
x_2725 = lean_ctor_get(x_2724, 0);
lean_inc(x_2725);
lean_dec(x_2724);
x_2726 = lean_st_ref_get(x_9, x_2657);
x_2727 = lean_ctor_get(x_2726, 0);
lean_inc(x_2727);
x_2728 = lean_ctor_get(x_2726, 1);
lean_inc(x_2728);
lean_dec(x_2726);
x_2729 = lean_ctor_get(x_2727, 0);
lean_inc(x_2729);
lean_dec(x_2727);
x_2730 = l___private_Lean_Elab_Util_1__evalSyntaxConstantUnsafe(x_2729, x_2725);
if (lean_obj_tag(x_2730) == 0)
{
lean_object* x_2731; lean_object* x_2732; lean_object* x_2733; lean_object* x_2734; 
lean_dec(x_2659);
lean_dec(x_2010);
lean_dec(x_2009);
lean_dec(x_11);
lean_dec(x_2);
x_2731 = lean_ctor_get(x_2730, 0);
lean_inc(x_2731);
lean_dec(x_2730);
x_2732 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2732, 0, x_2731);
x_2733 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2733, 0, x_2732);
x_2734 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2733, x_4, x_5, x_6, x_7, x_1909, x_9, x_2728);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2734;
}
else
{
lean_object* x_2735; lean_object* x_2736; lean_object* x_2737; lean_object* x_2738; lean_object* x_2739; lean_object* x_2740; lean_object* x_2741; lean_object* x_2742; lean_object* x_2743; lean_object* x_2744; lean_object* x_2745; lean_object* x_2746; lean_object* x_2747; lean_object* x_2748; lean_object* x_2749; lean_object* x_2750; lean_object* x_2751; lean_object* x_2752; lean_object* x_2753; lean_object* x_2754; lean_object* x_2755; lean_object* x_2756; lean_object* x_2757; lean_object* x_2758; lean_object* x_2759; lean_object* x_2760; lean_object* x_2761; lean_object* x_2762; lean_object* x_2763; lean_object* x_2764; lean_object* x_2765; lean_object* x_2766; lean_object* x_2767; lean_object* x_2768; lean_object* x_2769; 
x_2735 = lean_ctor_get(x_2730, 0);
lean_inc(x_2735);
lean_dec(x_2730);
x_2736 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_1909, x_9, x_2728);
x_2737 = lean_ctor_get(x_2736, 1);
lean_inc(x_2737);
lean_dec(x_2736);
x_2738 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_2737);
x_2739 = lean_ctor_get(x_2738, 1);
lean_inc(x_2739);
lean_dec(x_2738);
x_2740 = l_Lean_Syntax_getArgs(x_2735);
lean_dec(x_2735);
x_2741 = l_Array_empty___closed__1;
x_2742 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2740, x_2740, x_2012, x_2741);
lean_dec(x_2740);
x_2743 = l_Lean_nullKind___closed__2;
x_2744 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2744, 0, x_2743);
lean_ctor_set(x_2744, 1, x_2742);
x_2745 = lean_array_push(x_2741, x_2744);
x_2746 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__5;
x_2747 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2747, 0, x_2746);
lean_ctor_set(x_2747, 1, x_2745);
x_2748 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__4;
x_2749 = lean_array_push(x_2748, x_2747);
x_2750 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__16;
x_2751 = lean_array_push(x_2749, x_2750);
x_2752 = l___regBuiltin_Lean_Elab_Tactic_evalNestedTacticBlock___closed__2;
x_2753 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2753, 0, x_2752);
lean_ctor_set(x_2753, 1, x_2751);
x_2754 = lean_array_push(x_2741, x_2753);
x_2755 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2755, 0, x_2743);
lean_ctor_set(x_2755, 1, x_2754);
x_2756 = lean_array_push(x_2741, x_2755);
x_2757 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2757, 0, x_2746);
lean_ctor_set(x_2757, 1, x_2756);
x_2758 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__15;
x_2759 = lean_array_push(x_2758, x_2757);
x_2760 = l___regBuiltin_Lean_Elab_Term_elabByTactic___closed__2;
x_2761 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2761, 0, x_2760);
lean_ctor_set(x_2761, 1, x_2759);
x_2762 = l_Lean_Syntax_copyInfo(x_2761, x_11);
lean_dec(x_11);
x_2763 = l_Lean_Expr_getAppNumArgsAux___main(x_2009, x_2012);
x_2764 = lean_nat_sub(x_2763, x_2012);
lean_dec(x_2763);
x_2765 = lean_unsigned_to_nat(1u);
x_2766 = lean_nat_sub(x_2764, x_2765);
lean_dec(x_2764);
x_2767 = l_Lean_Expr_getRevArg_x21___main(x_2009, x_2766);
lean_dec(x_2009);
x_2768 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2768, 0, x_2762);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2769 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2768, x_2767, x_4, x_5, x_6, x_7, x_1909, x_9, x_2739);
if (lean_obj_tag(x_2769) == 0)
{
lean_object* x_2770; lean_object* x_2771; lean_object* x_2772; lean_object* x_2773; 
x_2770 = lean_ctor_get(x_2769, 0);
lean_inc(x_2770);
x_2771 = lean_ctor_get(x_2769, 1);
lean_inc(x_2771);
lean_dec(x_2769);
lean_inc(x_2770);
x_2772 = l_Lean_mkApp(x_2, x_2770);
x_2773 = lean_expr_instantiate1(x_2010, x_2770);
lean_dec(x_2770);
lean_dec(x_2010);
x_1 = x_2659;
x_2 = x_2772;
x_3 = x_2773;
x_8 = x_1909;
x_10 = x_2771;
goto _start;
}
else
{
lean_object* x_2775; lean_object* x_2776; lean_object* x_2777; lean_object* x_2778; 
lean_dec(x_2659);
lean_dec(x_2010);
lean_dec(x_1909);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2775 = lean_ctor_get(x_2769, 0);
lean_inc(x_2775);
x_2776 = lean_ctor_get(x_2769, 1);
lean_inc(x_2776);
if (lean_is_exclusive(x_2769)) {
 lean_ctor_release(x_2769, 0);
 lean_ctor_release(x_2769, 1);
 x_2777 = x_2769;
} else {
 lean_dec_ref(x_2769);
 x_2777 = lean_box(0);
}
if (lean_is_scalar(x_2777)) {
 x_2778 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2778 = x_2777;
}
lean_ctor_set(x_2778, 0, x_2775);
lean_ctor_set(x_2778, 1, x_2776);
return x_2778;
}
}
}
else
{
lean_object* x_2779; lean_object* x_2780; 
lean_dec(x_2724);
lean_dec(x_2659);
lean_dec(x_2010);
lean_dec(x_2009);
lean_dec(x_11);
lean_dec(x_2);
x_2779 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__12;
x_2780 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2779, x_4, x_5, x_6, x_7, x_1909, x_9, x_2657);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2780;
}
}
}
else
{
lean_object* x_2781; lean_object* x_2782; lean_object* x_2783; 
lean_dec(x_2009);
lean_dec(x_2008);
lean_dec(x_1902);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
x_2781 = lean_ctor_get(x_2662, 0);
lean_inc(x_2781);
lean_dec(x_2662);
lean_inc(x_2781);
x_2782 = l_Lean_mkApp(x_2, x_2781);
x_2783 = lean_expr_instantiate1(x_2010, x_2781);
lean_dec(x_2781);
lean_dec(x_2010);
x_1 = x_2659;
x_2 = x_2782;
x_3 = x_2783;
x_8 = x_1909;
x_10 = x_2657;
goto _start;
}
}
else
{
uint8_t x_2785; 
lean_dec(x_2659);
lean_dec(x_2010);
lean_dec(x_2009);
x_2785 = l_Array_isEmpty___rarg(x_16);
if (x_2785 == 0)
{
lean_object* x_2786; lean_object* x_2787; lean_object* x_2788; lean_object* x_2789; lean_object* x_2790; lean_object* x_2791; lean_object* x_2792; lean_object* x_2793; lean_object* x_2794; lean_object* x_2795; lean_object* x_2796; lean_object* x_2797; lean_object* x_2798; lean_object* x_2799; lean_object* x_2800; lean_object* x_2801; 
lean_dec(x_1902);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_2786 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2786, 0, x_2008);
x_2787 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__6;
x_2788 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2788, 0, x_2787);
lean_ctor_set(x_2788, 1, x_2786);
x_2789 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__9;
x_2790 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2790, 0, x_2788);
lean_ctor_set(x_2790, 1, x_2789);
x_2791 = x_16;
x_2792 = l_Array_umapMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__4(x_2012, x_2791);
x_2793 = x_2792;
x_2794 = l_Array_toList___rarg(x_2793);
lean_dec(x_2793);
x_2795 = l_List_toString___at_Lean_OpenDecl_HasToString___spec__2(x_2794);
x_2796 = l_Array_HasRepr___rarg___closed__1;
x_2797 = lean_string_append(x_2796, x_2795);
lean_dec(x_2795);
x_2798 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2798, 0, x_2797);
x_2799 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2799, 0, x_2798);
x_2800 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2800, 0, x_2790);
lean_ctor_set(x_2800, 1, x_2799);
x_2801 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_2800, x_4, x_5, x_6, x_7, x_1909, x_9, x_2657);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_2801;
}
else
{
lean_object* x_2802; uint8_t x_2803; 
lean_dec(x_2008);
lean_dec(x_16);
x_2802 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_2803 = l_Lean_checkTraceOption(x_1902, x_2802);
lean_dec(x_1902);
if (x_2803 == 0)
{
lean_object* x_2804; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2804 = x_2657;
goto block_2815;
}
else
{
lean_object* x_2816; lean_object* x_2817; 
x_2816 = lean_ctor_get(x_13, 0);
lean_inc(x_2816);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_2817 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2816, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_2657);
if (lean_obj_tag(x_2817) == 0)
{
lean_object* x_2818; 
x_2818 = lean_ctor_get(x_2817, 1);
lean_inc(x_2818);
lean_dec(x_2817);
x_2804 = x_2818;
goto block_2815;
}
else
{
lean_object* x_2819; lean_object* x_2820; lean_object* x_2821; lean_object* x_2822; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2819 = lean_ctor_get(x_2817, 0);
lean_inc(x_2819);
x_2820 = lean_ctor_get(x_2817, 1);
lean_inc(x_2820);
if (lean_is_exclusive(x_2817)) {
 lean_ctor_release(x_2817, 0);
 lean_ctor_release(x_2817, 1);
 x_2821 = x_2817;
} else {
 lean_dec_ref(x_2817);
 x_2821 = lean_box(0);
}
if (lean_is_scalar(x_2821)) {
 x_2822 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2822 = x_2821;
}
lean_ctor_set(x_2822, 0, x_2819);
lean_ctor_set(x_2822, 1, x_2820);
return x_2822;
}
}
block_2815:
{
lean_object* x_2805; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2805 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2804);
lean_dec(x_17);
if (lean_obj_tag(x_2805) == 0)
{
lean_object* x_2806; lean_object* x_2807; lean_object* x_2808; lean_object* x_2809; lean_object* x_2810; 
x_2806 = lean_ctor_get(x_2805, 1);
lean_inc(x_2806);
lean_dec(x_2805);
lean_inc(x_2);
x_2807 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__20(x_2, x_11, x_19, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2806);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2808 = lean_ctor_get(x_2807, 1);
lean_inc(x_2808);
if (lean_is_exclusive(x_2807)) {
 lean_ctor_release(x_2807, 0);
 lean_ctor_release(x_2807, 1);
 x_2809 = x_2807;
} else {
 lean_dec_ref(x_2807);
 x_2809 = lean_box(0);
}
if (lean_is_scalar(x_2809)) {
 x_2810 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2810 = x_2809;
}
lean_ctor_set(x_2810, 0, x_2);
lean_ctor_set(x_2810, 1, x_2808);
return x_2810;
}
else
{
lean_object* x_2811; lean_object* x_2812; lean_object* x_2813; lean_object* x_2814; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2811 = lean_ctor_get(x_2805, 0);
lean_inc(x_2811);
x_2812 = lean_ctor_get(x_2805, 1);
lean_inc(x_2812);
if (lean_is_exclusive(x_2805)) {
 lean_ctor_release(x_2805, 0);
 lean_ctor_release(x_2805, 1);
 x_2813 = x_2805;
} else {
 lean_dec_ref(x_2805);
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
}
else
{
lean_object* x_2823; lean_object* x_2824; lean_object* x_2825; lean_object* x_2826; 
lean_inc(x_2);
x_2823 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2823, 0, x_2);
x_2824 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_2802, x_2823, x_4, x_5, x_6, x_7, x_1909, x_9, x_2657);
x_2825 = lean_ctor_get(x_2824, 1);
lean_inc(x_2825);
lean_dec(x_2824);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_2826 = x_2825;
goto block_2837;
}
else
{
lean_object* x_2838; lean_object* x_2839; 
x_2838 = lean_ctor_get(x_13, 0);
lean_inc(x_2838);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_2839 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2838, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_2825);
if (lean_obj_tag(x_2839) == 0)
{
lean_object* x_2840; 
x_2840 = lean_ctor_get(x_2839, 1);
lean_inc(x_2840);
lean_dec(x_2839);
x_2826 = x_2840;
goto block_2837;
}
else
{
lean_object* x_2841; lean_object* x_2842; lean_object* x_2843; lean_object* x_2844; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2841 = lean_ctor_get(x_2839, 0);
lean_inc(x_2841);
x_2842 = lean_ctor_get(x_2839, 1);
lean_inc(x_2842);
if (lean_is_exclusive(x_2839)) {
 lean_ctor_release(x_2839, 0);
 lean_ctor_release(x_2839, 1);
 x_2843 = x_2839;
} else {
 lean_dec_ref(x_2839);
 x_2843 = lean_box(0);
}
if (lean_is_scalar(x_2843)) {
 x_2844 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2844 = x_2843;
}
lean_ctor_set(x_2844, 0, x_2841);
lean_ctor_set(x_2844, 1, x_2842);
return x_2844;
}
}
block_2837:
{
lean_object* x_2827; 
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_2827 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2826);
lean_dec(x_17);
if (lean_obj_tag(x_2827) == 0)
{
lean_object* x_2828; lean_object* x_2829; lean_object* x_2830; lean_object* x_2831; lean_object* x_2832; 
x_2828 = lean_ctor_get(x_2827, 1);
lean_inc(x_2828);
lean_dec(x_2827);
lean_inc(x_2);
x_2829 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__21(x_2, x_11, x_19, x_2012, x_4, x_5, x_6, x_7, x_1909, x_9, x_2828);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_2830 = lean_ctor_get(x_2829, 1);
lean_inc(x_2830);
if (lean_is_exclusive(x_2829)) {
 lean_ctor_release(x_2829, 0);
 lean_ctor_release(x_2829, 1);
 x_2831 = x_2829;
} else {
 lean_dec_ref(x_2829);
 x_2831 = lean_box(0);
}
if (lean_is_scalar(x_2831)) {
 x_2832 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2832 = x_2831;
}
lean_ctor_set(x_2832, 0, x_2);
lean_ctor_set(x_2832, 1, x_2830);
return x_2832;
}
else
{
lean_object* x_2833; lean_object* x_2834; lean_object* x_2835; lean_object* x_2836; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2833 = lean_ctor_get(x_2827, 0);
lean_inc(x_2833);
x_2834 = lean_ctor_get(x_2827, 1);
lean_inc(x_2834);
if (lean_is_exclusive(x_2827)) {
 lean_ctor_release(x_2827, 0);
 lean_ctor_release(x_2827, 1);
 x_2835 = x_2827;
} else {
 lean_dec_ref(x_2827);
 x_2835 = lean_box(0);
}
if (lean_is_scalar(x_2835)) {
 x_2836 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2836 = x_2835;
}
lean_ctor_set(x_2836, 0, x_2833);
lean_ctor_set(x_2836, 1, x_2834);
return x_2836;
}
}
}
}
}
}
else
{
lean_object* x_2845; lean_object* x_2846; 
lean_dec(x_2659);
lean_dec(x_2008);
lean_dec(x_1902);
lean_dec(x_3);
x_2845 = lean_array_fget(x_12, x_15);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2846 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2845, x_2009, x_4, x_5, x_6, x_7, x_1909, x_9, x_2657);
if (lean_obj_tag(x_2846) == 0)
{
lean_object* x_2847; lean_object* x_2848; lean_object* x_2849; lean_object* x_2850; lean_object* x_2851; lean_object* x_2852; lean_object* x_2853; 
x_2847 = lean_ctor_get(x_2846, 0);
lean_inc(x_2847);
x_2848 = lean_ctor_get(x_2846, 1);
lean_inc(x_2848);
lean_dec(x_2846);
x_2849 = lean_unsigned_to_nat(1u);
x_2850 = lean_nat_add(x_15, x_2849);
lean_dec(x_15);
x_2851 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_2851, 0, x_11);
lean_ctor_set(x_2851, 1, x_12);
lean_ctor_set(x_2851, 2, x_13);
lean_ctor_set(x_2851, 3, x_2850);
lean_ctor_set(x_2851, 4, x_16);
lean_ctor_set(x_2851, 5, x_17);
lean_ctor_set(x_2851, 6, x_18);
lean_ctor_set(x_2851, 7, x_19);
lean_ctor_set_uint8(x_2851, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2851, sizeof(void*)*8 + 1, x_2658);
lean_inc(x_2847);
x_2852 = l_Lean_mkApp(x_2, x_2847);
x_2853 = lean_expr_instantiate1(x_2010, x_2847);
lean_dec(x_2847);
lean_dec(x_2010);
x_1 = x_2851;
x_2 = x_2852;
x_3 = x_2853;
x_8 = x_1909;
x_10 = x_2848;
goto _start;
}
else
{
lean_object* x_2855; lean_object* x_2856; lean_object* x_2857; lean_object* x_2858; 
lean_dec(x_2010);
lean_dec(x_1909);
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
x_2855 = lean_ctor_get(x_2846, 0);
lean_inc(x_2855);
x_2856 = lean_ctor_get(x_2846, 1);
lean_inc(x_2856);
if (lean_is_exclusive(x_2846)) {
 lean_ctor_release(x_2846, 0);
 lean_ctor_release(x_2846, 1);
 x_2857 = x_2846;
} else {
 lean_dec_ref(x_2846);
 x_2857 = lean_box(0);
}
if (lean_is_scalar(x_2857)) {
 x_2858 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2858 = x_2857;
}
lean_ctor_set(x_2858, 0, x_2855);
lean_ctor_set(x_2858, 1, x_2856);
return x_2858;
}
}
}
else
{
lean_object* x_2859; lean_object* x_2860; lean_object* x_2861; lean_object* x_2862; 
lean_dec(x_2656);
lean_dec(x_2010);
lean_dec(x_2009);
lean_dec(x_2008);
lean_dec(x_1909);
lean_dec(x_1902);
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
x_2859 = lean_ctor_get(x_2655, 0);
lean_inc(x_2859);
x_2860 = lean_ctor_get(x_2655, 1);
lean_inc(x_2860);
if (lean_is_exclusive(x_2655)) {
 lean_ctor_release(x_2655, 0);
 lean_ctor_release(x_2655, 1);
 x_2861 = x_2655;
} else {
 lean_dec_ref(x_2655);
 x_2861 = lean_box(0);
}
if (lean_is_scalar(x_2861)) {
 x_2862 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2862 = x_2861;
}
lean_ctor_set(x_2862, 0, x_2859);
lean_ctor_set(x_2862, 1, x_2860);
return x_2862;
}
}
}
}
else
{
lean_object* x_2863; lean_object* x_2864; lean_object* x_2865; lean_object* x_2866; lean_object* x_2867; lean_object* x_2868; 
lean_dec(x_2008);
lean_dec(x_1902);
lean_dec(x_3);
x_2863 = lean_ctor_get(x_2013, 0);
lean_inc(x_2863);
lean_dec(x_2013);
x_2864 = l_Lean_Elab_Term_NamedArg_inhabited;
x_2865 = lean_array_get(x_2864, x_16, x_2863);
x_2866 = l_Array_eraseIdx___rarg(x_16, x_2863);
lean_dec(x_2863);
x_2867 = lean_ctor_get(x_2865, 1);
lean_inc(x_2867);
lean_dec(x_2865);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_2868 = l___private_Lean_Elab_App_2__elabArg(x_2, x_2867, x_2009, x_4, x_5, x_6, x_7, x_1909, x_9, x_1912);
if (lean_obj_tag(x_2868) == 0)
{
lean_object* x_2869; lean_object* x_2870; lean_object* x_2871; lean_object* x_2872; 
x_2869 = lean_ctor_get(x_2868, 0);
lean_inc(x_2869);
x_2870 = lean_ctor_get(x_2868, 1);
lean_inc(x_2870);
lean_dec(x_2868);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_2871 = l___private_Lean_Elab_App_8__propagateExpectedType(x_1, x_1911, x_4, x_5, x_6, x_7, x_1909, x_9, x_2870);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 lean_ctor_release(x_1, 4);
 lean_ctor_release(x_1, 5);
 lean_ctor_release(x_1, 6);
 lean_ctor_release(x_1, 7);
 x_2872 = x_1;
} else {
 lean_dec_ref(x_1);
 x_2872 = lean_box(0);
}
if (lean_obj_tag(x_2871) == 0)
{
lean_object* x_2873; uint8_t x_2874; lean_object* x_2875; lean_object* x_2876; lean_object* x_2877; 
x_2873 = lean_ctor_get(x_2871, 1);
lean_inc(x_2873);
lean_dec(x_2871);
x_2874 = 1;
if (lean_is_scalar(x_2872)) {
 x_2875 = lean_alloc_ctor(0, 8, 2);
} else {
 x_2875 = x_2872;
}
lean_ctor_set(x_2875, 0, x_11);
lean_ctor_set(x_2875, 1, x_12);
lean_ctor_set(x_2875, 2, x_13);
lean_ctor_set(x_2875, 3, x_15);
lean_ctor_set(x_2875, 4, x_2866);
lean_ctor_set(x_2875, 5, x_17);
lean_ctor_set(x_2875, 6, x_18);
lean_ctor_set(x_2875, 7, x_19);
lean_ctor_set_uint8(x_2875, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_2875, sizeof(void*)*8 + 1, x_2874);
lean_inc(x_2869);
x_2876 = l_Lean_mkApp(x_2, x_2869);
x_2877 = lean_expr_instantiate1(x_2010, x_2869);
lean_dec(x_2869);
lean_dec(x_2010);
x_1 = x_2875;
x_2 = x_2876;
x_3 = x_2877;
x_8 = x_1909;
x_10 = x_2873;
goto _start;
}
else
{
lean_object* x_2879; lean_object* x_2880; lean_object* x_2881; lean_object* x_2882; 
lean_dec(x_2872);
lean_dec(x_2869);
lean_dec(x_2866);
lean_dec(x_2010);
lean_dec(x_1909);
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
x_2879 = lean_ctor_get(x_2871, 0);
lean_inc(x_2879);
x_2880 = lean_ctor_get(x_2871, 1);
lean_inc(x_2880);
if (lean_is_exclusive(x_2871)) {
 lean_ctor_release(x_2871, 0);
 lean_ctor_release(x_2871, 1);
 x_2881 = x_2871;
} else {
 lean_dec_ref(x_2871);
 x_2881 = lean_box(0);
}
if (lean_is_scalar(x_2881)) {
 x_2882 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2882 = x_2881;
}
lean_ctor_set(x_2882, 0, x_2879);
lean_ctor_set(x_2882, 1, x_2880);
return x_2882;
}
}
else
{
lean_object* x_2883; lean_object* x_2884; lean_object* x_2885; lean_object* x_2886; 
lean_dec(x_2866);
lean_dec(x_2010);
lean_dec(x_1911);
lean_dec(x_1909);
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
x_2883 = lean_ctor_get(x_2868, 0);
lean_inc(x_2883);
x_2884 = lean_ctor_get(x_2868, 1);
lean_inc(x_2884);
if (lean_is_exclusive(x_2868)) {
 lean_ctor_release(x_2868, 0);
 lean_ctor_release(x_2868, 1);
 x_2885 = x_2868;
} else {
 lean_dec_ref(x_2868);
 x_2885 = lean_box(0);
}
if (lean_is_scalar(x_2885)) {
 x_2886 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2886 = x_2885;
}
lean_ctor_set(x_2886, 0, x_2883);
lean_ctor_set(x_2886, 1, x_2884);
return x_2886;
}
}
}
else
{
lean_object* x_2887; 
lean_dec(x_1);
x_2887 = lean_box(0);
x_1913 = x_2887;
goto block_2007;
}
block_2007:
{
lean_object* x_1914; uint8_t x_1957; 
lean_dec(x_1913);
x_1957 = l_Array_isEmpty___rarg(x_16);
if (x_1957 == 0)
{
lean_object* x_1958; 
lean_dec(x_1902);
lean_dec(x_3);
x_1958 = lean_box(0);
x_1914 = x_1958;
goto block_1956;
}
else
{
lean_object* x_1959; uint8_t x_1960; 
x_1959 = lean_array_get_size(x_12);
x_1960 = lean_nat_dec_eq(x_15, x_1959);
lean_dec(x_1959);
if (x_1960 == 0)
{
lean_object* x_1961; 
lean_dec(x_1902);
lean_dec(x_3);
x_1961 = lean_box(0);
x_1914 = x_1961;
goto block_1956;
}
else
{
lean_object* x_1962; uint8_t x_1963; 
lean_dec(x_1911);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
x_1962 = l___private_Lean_Elab_App_10__elabAppArgsAux___main___closed__3;
x_1963 = l_Lean_checkTraceOption(x_1902, x_1962);
lean_dec(x_1902);
if (x_1963 == 0)
{
lean_object* x_1964; 
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1964 = x_1912;
goto block_1976;
}
else
{
lean_object* x_1977; lean_object* x_1978; 
x_1977 = lean_ctor_get(x_13, 0);
lean_inc(x_1977);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_1978 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_1977, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_1912);
if (lean_obj_tag(x_1978) == 0)
{
lean_object* x_1979; 
x_1979 = lean_ctor_get(x_1978, 1);
lean_inc(x_1979);
lean_dec(x_1978);
x_1964 = x_1979;
goto block_1976;
}
else
{
lean_object* x_1980; lean_object* x_1981; lean_object* x_1982; lean_object* x_1983; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1980 = lean_ctor_get(x_1978, 0);
lean_inc(x_1980);
x_1981 = lean_ctor_get(x_1978, 1);
lean_inc(x_1981);
if (lean_is_exclusive(x_1978)) {
 lean_ctor_release(x_1978, 0);
 lean_ctor_release(x_1978, 1);
 x_1982 = x_1978;
} else {
 lean_dec_ref(x_1978);
 x_1982 = lean_box(0);
}
if (lean_is_scalar(x_1982)) {
 x_1983 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1983 = x_1982;
}
lean_ctor_set(x_1983, 0, x_1980);
lean_ctor_set(x_1983, 1, x_1981);
return x_1983;
}
}
block_1976:
{
lean_object* x_1965; lean_object* x_1966; 
x_1965 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1966 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1965, x_4, x_5, x_6, x_7, x_1909, x_9, x_1964);
lean_dec(x_17);
if (lean_obj_tag(x_1966) == 0)
{
lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; lean_object* x_1971; 
x_1967 = lean_ctor_get(x_1966, 1);
lean_inc(x_1967);
lean_dec(x_1966);
lean_inc(x_2);
x_1968 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__1(x_2, x_11, x_19, x_1965, x_4, x_5, x_6, x_7, x_1909, x_9, x_1967);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1969 = lean_ctor_get(x_1968, 1);
lean_inc(x_1969);
if (lean_is_exclusive(x_1968)) {
 lean_ctor_release(x_1968, 0);
 lean_ctor_release(x_1968, 1);
 x_1970 = x_1968;
} else {
 lean_dec_ref(x_1968);
 x_1970 = lean_box(0);
}
if (lean_is_scalar(x_1970)) {
 x_1971 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1971 = x_1970;
}
lean_ctor_set(x_1971, 0, x_2);
lean_ctor_set(x_1971, 1, x_1969);
return x_1971;
}
else
{
lean_object* x_1972; lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1972 = lean_ctor_get(x_1966, 0);
lean_inc(x_1972);
x_1973 = lean_ctor_get(x_1966, 1);
lean_inc(x_1973);
if (lean_is_exclusive(x_1966)) {
 lean_ctor_release(x_1966, 0);
 lean_ctor_release(x_1966, 1);
 x_1974 = x_1966;
} else {
 lean_dec_ref(x_1966);
 x_1974 = lean_box(0);
}
if (lean_is_scalar(x_1974)) {
 x_1975 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1975 = x_1974;
}
lean_ctor_set(x_1975, 0, x_1972);
lean_ctor_set(x_1975, 1, x_1973);
return x_1975;
}
}
}
else
{
lean_object* x_1984; lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; 
lean_inc(x_2);
x_1984 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1984, 0, x_2);
x_1985 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_1962, x_1984, x_4, x_5, x_6, x_7, x_1909, x_9, x_1912);
x_1986 = lean_ctor_get(x_1985, 1);
lean_inc(x_1986);
lean_dec(x_1985);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_3);
x_1987 = x_1986;
goto block_1999;
}
else
{
lean_object* x_2000; lean_object* x_2001; 
x_2000 = lean_ctor_get(x_13, 0);
lean_inc(x_2000);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_2001 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_2000, x_3, x_4, x_5, x_6, x_7, x_1909, x_9, x_1986);
if (lean_obj_tag(x_2001) == 0)
{
lean_object* x_2002; 
x_2002 = lean_ctor_get(x_2001, 1);
lean_inc(x_2002);
lean_dec(x_2001);
x_1987 = x_2002;
goto block_1999;
}
else
{
lean_object* x_2003; lean_object* x_2004; lean_object* x_2005; lean_object* x_2006; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2003 = lean_ctor_get(x_2001, 0);
lean_inc(x_2003);
x_2004 = lean_ctor_get(x_2001, 1);
lean_inc(x_2004);
if (lean_is_exclusive(x_2001)) {
 lean_ctor_release(x_2001, 0);
 lean_ctor_release(x_2001, 1);
 x_2005 = x_2001;
} else {
 lean_dec_ref(x_2001);
 x_2005 = lean_box(0);
}
if (lean_is_scalar(x_2005)) {
 x_2006 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2006 = x_2005;
}
lean_ctor_set(x_2006, 0, x_2003);
lean_ctor_set(x_2006, 1, x_2004);
return x_2006;
}
}
block_1999:
{
lean_object* x_1988; lean_object* x_1989; 
x_1988 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1989 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1988, x_4, x_5, x_6, x_7, x_1909, x_9, x_1987);
lean_dec(x_17);
if (lean_obj_tag(x_1989) == 0)
{
lean_object* x_1990; lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; 
x_1990 = lean_ctor_get(x_1989, 1);
lean_inc(x_1990);
lean_dec(x_1989);
lean_inc(x_2);
x_1991 = l_Array_forMAux___main___at___private_Lean_Elab_App_10__elabAppArgsAux___main___spec__2(x_2, x_11, x_19, x_1988, x_4, x_5, x_6, x_7, x_1909, x_9, x_1990);
lean_dec(x_9);
lean_dec(x_1909);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
x_1992 = lean_ctor_get(x_1991, 1);
lean_inc(x_1992);
if (lean_is_exclusive(x_1991)) {
 lean_ctor_release(x_1991, 0);
 lean_ctor_release(x_1991, 1);
 x_1993 = x_1991;
} else {
 lean_dec_ref(x_1991);
 x_1993 = lean_box(0);
}
if (lean_is_scalar(x_1993)) {
 x_1994 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1994 = x_1993;
}
lean_ctor_set(x_1994, 0, x_2);
lean_ctor_set(x_1994, 1, x_1992);
return x_1994;
}
else
{
lean_object* x_1995; lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; 
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1995 = lean_ctor_get(x_1989, 0);
lean_inc(x_1995);
x_1996 = lean_ctor_get(x_1989, 1);
lean_inc(x_1996);
if (lean_is_exclusive(x_1989)) {
 lean_ctor_release(x_1989, 0);
 lean_ctor_release(x_1989, 1);
 x_1997 = x_1989;
} else {
 lean_dec_ref(x_1989);
 x_1997 = lean_box(0);
}
if (lean_is_scalar(x_1997)) {
 x_1998 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1998 = x_1997;
}
lean_ctor_set(x_1998, 0, x_1995);
lean_ctor_set(x_1998, 1, x_1996);
return x_1998;
}
}
}
}
}
block_1956:
{
lean_object* x_1915; lean_object* x_1916; 
lean_dec(x_1914);
x_1915 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1916 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_17, x_1915, x_4, x_5, x_6, x_7, x_1909, x_9, x_1912);
lean_dec(x_17);
if (lean_obj_tag(x_1916) == 0)
{
lean_object* x_1917; uint8_t x_1918; lean_object* x_1919; lean_object* x_1920; 
x_1917 = lean_ctor_get(x_1916, 1);
lean_inc(x_1917);
lean_dec(x_1916);
x_1918 = 1;
x_1919 = lean_box(0);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_1920 = l___private_Lean_Elab_SyntheticMVars_13__synthesizeSyntheticMVarsAux___main(x_1918, x_1919, x_4, x_5, x_6, x_7, x_1909, x_9, x_1917);
if (lean_obj_tag(x_1920) == 0)
{
lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; 
x_1921 = lean_ctor_get(x_1920, 1);
lean_inc(x_1921);
lean_dec(x_1920);
x_1922 = l_Array_empty___closed__1;
x_1923 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1923, 0, x_11);
lean_ctor_set(x_1923, 1, x_12);
lean_ctor_set(x_1923, 2, x_13);
lean_ctor_set(x_1923, 3, x_15);
lean_ctor_set(x_1923, 4, x_16);
lean_ctor_set(x_1923, 5, x_1922);
lean_ctor_set(x_1923, 6, x_18);
lean_ctor_set(x_1923, 7, x_19);
lean_ctor_set_uint8(x_1923, sizeof(void*)*8, x_14);
lean_ctor_set_uint8(x_1923, sizeof(void*)*8 + 1, x_1901);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
x_1924 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_14__useImplicitLambda_x3f___spec__1(x_1911, x_4, x_5, x_6, x_7, x_1909, x_9, x_1921);
if (lean_obj_tag(x_1924) == 0)
{
lean_object* x_1925; 
x_1925 = lean_ctor_get(x_1924, 0);
lean_inc(x_1925);
if (lean_obj_tag(x_1925) == 7)
{
lean_object* x_1926; 
x_1926 = lean_ctor_get(x_1924, 1);
lean_inc(x_1926);
lean_dec(x_1924);
x_1 = x_1923;
x_3 = x_1925;
x_8 = x_1909;
x_10 = x_1926;
goto _start;
}
else
{
lean_object* x_1928; lean_object* x_1929; 
x_1928 = lean_ctor_get(x_1924, 1);
lean_inc(x_1928);
lean_dec(x_1924);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_1929 = l___private_Lean_Elab_App_4__tryCoeFun(x_1925, x_2, x_4, x_5, x_6, x_7, x_1909, x_9, x_1928);
if (lean_obj_tag(x_1929) == 0)
{
lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; 
x_1930 = lean_ctor_get(x_1929, 0);
lean_inc(x_1930);
x_1931 = lean_ctor_get(x_1929, 1);
lean_inc(x_1931);
lean_dec(x_1929);
lean_inc(x_9);
lean_inc(x_1909);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1930);
x_1932 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_1930, x_4, x_5, x_6, x_7, x_1909, x_9, x_1931);
if (lean_obj_tag(x_1932) == 0)
{
lean_object* x_1933; lean_object* x_1934; 
x_1933 = lean_ctor_get(x_1932, 0);
lean_inc(x_1933);
x_1934 = lean_ctor_get(x_1932, 1);
lean_inc(x_1934);
lean_dec(x_1932);
x_1 = x_1923;
x_2 = x_1930;
x_3 = x_1933;
x_8 = x_1909;
x_10 = x_1934;
goto _start;
}
else
{
lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; 
lean_dec(x_1930);
lean_dec(x_1923);
lean_dec(x_1909);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1936 = lean_ctor_get(x_1932, 0);
lean_inc(x_1936);
x_1937 = lean_ctor_get(x_1932, 1);
lean_inc(x_1937);
if (lean_is_exclusive(x_1932)) {
 lean_ctor_release(x_1932, 0);
 lean_ctor_release(x_1932, 1);
 x_1938 = x_1932;
} else {
 lean_dec_ref(x_1932);
 x_1938 = lean_box(0);
}
if (lean_is_scalar(x_1938)) {
 x_1939 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1939 = x_1938;
}
lean_ctor_set(x_1939, 0, x_1936);
lean_ctor_set(x_1939, 1, x_1937);
return x_1939;
}
}
else
{
lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; 
lean_dec(x_1923);
lean_dec(x_1909);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1940 = lean_ctor_get(x_1929, 0);
lean_inc(x_1940);
x_1941 = lean_ctor_get(x_1929, 1);
lean_inc(x_1941);
if (lean_is_exclusive(x_1929)) {
 lean_ctor_release(x_1929, 0);
 lean_ctor_release(x_1929, 1);
 x_1942 = x_1929;
} else {
 lean_dec_ref(x_1929);
 x_1942 = lean_box(0);
}
if (lean_is_scalar(x_1942)) {
 x_1943 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1943 = x_1942;
}
lean_ctor_set(x_1943, 0, x_1940);
lean_ctor_set(x_1943, 1, x_1941);
return x_1943;
}
}
}
else
{
lean_object* x_1944; lean_object* x_1945; lean_object* x_1946; lean_object* x_1947; 
lean_dec(x_1923);
lean_dec(x_1909);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1944 = lean_ctor_get(x_1924, 0);
lean_inc(x_1944);
x_1945 = lean_ctor_get(x_1924, 1);
lean_inc(x_1945);
if (lean_is_exclusive(x_1924)) {
 lean_ctor_release(x_1924, 0);
 lean_ctor_release(x_1924, 1);
 x_1946 = x_1924;
} else {
 lean_dec_ref(x_1924);
 x_1946 = lean_box(0);
}
if (lean_is_scalar(x_1946)) {
 x_1947 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1947 = x_1946;
}
lean_ctor_set(x_1947, 0, x_1944);
lean_ctor_set(x_1947, 1, x_1945);
return x_1947;
}
}
else
{
lean_object* x_1948; lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; 
lean_dec(x_1911);
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_18);
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
x_1948 = lean_ctor_get(x_1920, 0);
lean_inc(x_1948);
x_1949 = lean_ctor_get(x_1920, 1);
lean_inc(x_1949);
if (lean_is_exclusive(x_1920)) {
 lean_ctor_release(x_1920, 0);
 lean_ctor_release(x_1920, 1);
 x_1950 = x_1920;
} else {
 lean_dec_ref(x_1920);
 x_1950 = lean_box(0);
}
if (lean_is_scalar(x_1950)) {
 x_1951 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1951 = x_1950;
}
lean_ctor_set(x_1951, 0, x_1948);
lean_ctor_set(x_1951, 1, x_1949);
return x_1951;
}
}
else
{
lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; 
lean_dec(x_1911);
lean_dec(x_1909);
lean_dec(x_19);
lean_dec(x_18);
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
x_1952 = lean_ctor_get(x_1916, 0);
lean_inc(x_1952);
x_1953 = lean_ctor_get(x_1916, 1);
lean_inc(x_1953);
if (lean_is_exclusive(x_1916)) {
 lean_ctor_release(x_1916, 0);
 lean_ctor_release(x_1916, 1);
 x_1954 = x_1916;
} else {
 lean_dec_ref(x_1916);
 x_1954 = lean_box(0);
}
if (lean_is_scalar(x_1954)) {
 x_1955 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1955 = x_1954;
}
lean_ctor_set(x_1955, 0, x_1952);
lean_ctor_set(x_1955, 1, x_1953);
return x_1955;
}
}
}
}
else
{
lean_object* x_2888; lean_object* x_2889; lean_object* x_2890; lean_object* x_2891; 
lean_dec(x_1909);
lean_dec(x_1902);
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
x_2888 = lean_ctor_get(x_1910, 0);
lean_inc(x_2888);
x_2889 = lean_ctor_get(x_1910, 1);
lean_inc(x_2889);
if (lean_is_exclusive(x_1910)) {
 lean_ctor_release(x_1910, 0);
 lean_ctor_release(x_1910, 1);
 x_2890 = x_1910;
} else {
 lean_dec_ref(x_1910);
 x_2890 = lean_box(0);
}
if (lean_is_scalar(x_2890)) {
 x_2891 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2891 = x_2890;
}
lean_ctor_set(x_2891, 0, x_2888);
lean_ctor_set(x_2891, 1, x_2889);
return x_2891;
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
lean_dec(x_2);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_11__elabAppArgs___closed__5;
x_2 = l___private_Lean_Elab_SyntheticMVars_9__synthesizeSyntheticMVarsStep___closed__9;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_11__elabAppArgs___closed__6;
x_2 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_11__elabAppArgs___closed__5;
x_2 = l___private_Lean_Elab_SyntheticMVars_9__synthesizeSyntheticMVarsStep___closed__10;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_11__elabAppArgs___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_App_11__elabAppArgs___closed__8;
x_2 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_3 = lean_alloc_ctor(10, 2, 0);
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
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
x_58 = l___private_Lean_Elab_App_11__elabAppArgs___closed__7;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
x_60 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(10, 2, 0);
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
x_65 = l___private_Lean_Elab_App_11__elabAppArgs___closed__9;
x_66 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_56);
x_67 = l___private_Lean_Meta_ExprDefEq_8__checkTypesAndAssign___closed__7;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(10, 2, 0);
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
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l___private_Lean_Elab_App_14__resolveLValAux___closed__12;
x_39 = lean_alloc_ctor(10, 2, 0);
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
x_83 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_85 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_86, 0, x_71);
x_87 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_89 = lean_alloc_ctor(10, 2, 0);
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
x_103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_105 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_106, 0, x_71);
x_107 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_109 = lean_alloc_ctor(10, 2, 0);
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
x_126 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
x_127 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_128 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_129, 0, x_71);
x_130 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_132 = lean_alloc_ctor(10, 2, 0);
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
x_147 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
x_148 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_149 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_150, 0, x_71);
x_151 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_153 = lean_alloc_ctor(10, 2, 0);
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
x_178 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
x_179 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_180 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_181, 0, x_166);
x_182 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_183 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_184 = lean_alloc_ctor(10, 2, 0);
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
x_198 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
x_199 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_200 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_201, 0, x_166);
x_202 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_203 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_204 = lean_alloc_ctor(10, 2, 0);
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
x_221 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
x_222 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_223 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_224, 0, x_166);
x_225 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
x_226 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_227 = lean_alloc_ctor(10, 2, 0);
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
x_242 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_240);
x_243 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_244 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_245, 0, x_166);
x_246 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_248 = lean_alloc_ctor(10, 2, 0);
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
x_278 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_276);
x_279 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_280 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
x_281 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_281, 0, x_266);
x_282 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
x_283 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_284 = lean_alloc_ctor(10, 2, 0);
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
x_299 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_297);
x_300 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_301 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_302, 0, x_266);
x_303 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
x_304 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_305 = lean_alloc_ctor(10, 2, 0);
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
x_330 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_328);
x_331 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_332 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
x_333 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_333, 0, x_318);
x_334 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
x_335 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_336 = lean_alloc_ctor(10, 2, 0);
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
x_351 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_349);
x_352 = l___private_Lean_Elab_App_14__resolveLValAux___closed__24;
x_353 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
x_354 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_354, 0, x_318);
x_355 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set(x_355, 1, x_354);
x_356 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_357 = lean_alloc_ctor(10, 2, 0);
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
x_382 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_380);
x_383 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_384 = lean_alloc_ctor(10, 2, 0);
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
x_395 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_393);
x_396 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_397 = lean_alloc_ctor(10, 2, 0);
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
lean_object* l___private_Lean_Elab_App_15__consumeImplicits___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_11);
lean_ctor_set(x_10, 0, x_29);
return x_10;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint64_t x_33; uint8_t x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_dec(x_10);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_11, 2);
lean_inc(x_32);
x_33 = lean_ctor_get_uint64(x_11, sizeof(void*)*3);
x_34 = (uint8_t)((x_33 << 24) >> 61);
x_35 = l_Lean_BinderInfo_isExplicit(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_11);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_37 = 0;
x_38 = lean_box(0);
lean_inc(x_5);
x_39 = l___private_Lean_Meta_Basic_4__mkFreshExprMVarImpl(x_36, x_37, x_38, x_5, x_6, x_7, x_8, x_30);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_40);
x_42 = l_Lean_mkApp(x_1, x_40);
x_43 = lean_expr_instantiate1(x_32, x_40);
lean_dec(x_40);
lean_dec(x_32);
x_1 = x_42;
x_2 = x_43;
x_9 = x_41;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_11);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_30);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_10);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_10, 0);
lean_dec(x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_11);
lean_ctor_set(x_10, 0, x_49);
return x_10;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_10, 1);
lean_inc(x_50);
lean_dec(x_10);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_11);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_10);
if (x_53 == 0)
{
return x_10;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_10, 0);
x_55 = lean_ctor_get(x_10, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_10);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
lean_object* l___private_Lean_Elab_App_15__consumeImplicits___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_15__consumeImplicits___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_15__consumeImplicits(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_15__consumeImplicits___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Elab_App_15__consumeImplicits___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_15__consumeImplicits(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_16__resolveLValLoop___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_15 = l_Lean_Elab_logException___at___private_Lean_Elab_Term_6__exceptionToSorry___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_App_16__resolveLValLoop___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l___private_Lean_Elab_App_15__consumeImplicits___main(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_20 = l___private_Lean_Elab_App_14__resolveLValAux(x_16, x_17, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
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
x_32 = l_Array_forMAux___main___at___private_Lean_Elab_App_16__resolveLValLoop___main___spec__1(x_4, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
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
x_57 = l___private_Lean_Elab_App_14__resolveLValAux(x_53, x_54, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_56);
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
x_69 = l_Array_forMAux___main___at___private_Lean_Elab_App_16__resolveLValLoop___main___spec__1(x_4, x_68, x_5, x_6, x_7, x_8, x_9, x_10, x_67);
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
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_App_16__resolveLValLoop___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forMAux___main___at___private_Lean_Elab_App_16__resolveLValLoop___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l___private_Lean_Elab_App_16__resolveLValLoop___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_App_16__resolveLValLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_16__resolveLValLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_App_16__resolveLValLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_16__resolveLValLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_App_16__resolveLValLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l___private_Lean_Elab_App_17__resolveLVal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
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
x_14 = l___private_Lean_Elab_App_16__resolveLValLoop___main(x_2, x_1, x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
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
lean_object* l___private_Lean_Elab_App_17__resolveLVal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_17__resolveLVal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("self");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_18 = l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1___closed__2;
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
lean_object* _init_l___private_Lean_Elab_App_18__mkBaseProjections___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to access field in parent structure");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_18__mkBaseProjections___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_18__mkBaseProjections___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_18__mkBaseProjections___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_18__mkBaseProjections___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_18__mkBaseProjections(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_16 = l___private_Lean_Elab_App_18__mkBaseProjections___closed__3;
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
x_19 = l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1(x_3, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_19;
}
}
}
lean_object* l___private_Lean_Elab_App_18__mkBaseProjections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_App_18__mkBaseProjections(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_19__addLValArg___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, function '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_19__addLValArg___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_19__addLValArg___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not have explicit argument with type (");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_19__addLValArg___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_19__addLValArg___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ...)");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_19__addLValArg___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_19__addLValArg___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field notation, insufficient number of arguments for '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_19__addLValArg___main___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_19__addLValArg___main___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_19__addLValArg___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
x_35 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_19__addLValArg___main___spec__1(x_27, x_6, x_34);
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
x_41 = l___private_Lean_Elab_App_19__addLValArg___main___closed__12;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
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
x_17 = l___private_Lean_Elab_App_19__addLValArg___main___closed__3;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l___private_Lean_Elab_App_19__addLValArg___main___closed__6;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Lean_Elab_App_19__addLValArg___main___closed__9;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_25;
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_App_19__addLValArg___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_App_19__addLValArg___main___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_App_19__addLValArg___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_App_19__addLValArg___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_15;
}
}
lean_object* l___private_Lean_Elab_App_19__addLValArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_App_19__addLValArg___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
lean_object* l___private_Lean_Elab_App_19__addLValArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_App_19__addLValArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_15;
}
}
lean_object* _init_l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("idx");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_20__elabAppLValsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_17 = l___private_Lean_Elab_App_17__resolveLVal(x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_25 = l___private_Lean_Elab_App_18__mkBaseProjections(x_22, x_23, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
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
x_35 = l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1___closed__2;
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
x_42 = l___private_Lean_Elab_App_11__elabAppArgs(x_31, x_38, x_40, x_39, x_41, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
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
x_51 = l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1___closed__2;
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
x_56 = l___private_Lean_Elab_App_11__elabAppArgs(x_31, x_54, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_55);
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
x_81 = l___private_Lean_Elab_App_18__mkBaseProjections(x_77, x_78, x_76, x_7, x_8, x_9, x_10, x_11, x_12, x_75);
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
x_95 = l___private_Lean_Elab_App_11__elabAppArgs(x_86, x_93, x_91, x_92, x_94, x_7, x_8, x_9, x_10, x_11, x_12, x_87);
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
x_103 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_86, x_7, x_8, x_9, x_10, x_11, x_12, x_87);
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
x_107 = l___private_Lean_Elab_App_19__addLValArg___main(x_77, x_79, x_82, x_2, x_106, x_1, x_104, x_7, x_8, x_9, x_10, x_11, x_12, x_105);
lean_dec(x_104);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l___private_Lean_Elab_App_11__elabAppArgs(x_86, x_1, x_108, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_109);
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
x_138 = l___private_Lean_Elab_App_11__elabAppArgs(x_129, x_136, x_134, x_135, x_137, x_7, x_8, x_9, x_10, x_11, x_12, x_130);
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
x_146 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_129, x_7, x_8, x_9, x_10, x_11, x_12, x_130);
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
x_150 = l___private_Lean_Elab_App_19__addLValArg___main(x_77, x_79, x_76, x_2, x_149, x_1, x_147, x_7, x_8, x_9, x_10, x_11, x_12, x_148);
lean_dec(x_147);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = l___private_Lean_Elab_App_11__elabAppArgs(x_129, x_1, x_151, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_152);
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
x_178 = l___private_Lean_Elab_App_11__elabAppArgs(x_170, x_176, x_174, x_175, x_177, x_7, x_8, x_9, x_10, x_11, x_12, x_166);
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
x_186 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_170, x_7, x_8, x_9, x_10, x_11, x_12, x_166);
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
x_190 = l___private_Lean_Elab_App_19__addLValArg___main(x_168, x_169, x_167, x_2, x_189, x_1, x_187, x_7, x_8, x_9, x_10, x_11, x_12, x_188);
lean_dec(x_187);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = l___private_Lean_Elab_App_11__elabAppArgs(x_170, x_1, x_191, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_192);
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
x_212 = l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1___closed__2;
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
x_214 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_214, 0, x_205);
x_215 = l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__2;
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
x_223 = l___private_Lean_Elab_App_11__elabAppArgs(x_208, x_219, x_221, x_220, x_222, x_7, x_8, x_9, x_10, x_11, x_12, x_209);
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
x_232 = l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1___closed__2;
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
x_238 = l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__2;
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
x_243 = l___private_Lean_Elab_App_11__elabAppArgs(x_208, x_241, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_242);
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
lean_object* l___private_Lean_Elab_App_20__elabAppLValsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Elab_App_20__elabAppLValsAux___main(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l___private_Lean_Elab_App_20__elabAppLValsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_App_20__elabAppLValsAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
lean_object* l___private_Lean_Elab_App_20__elabAppLValsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Elab_App_20__elabAppLValsAux(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* _init_l___private_Lean_Elab_App_21__elabAppLVals___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of field notation with `@` modifier");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_21__elabAppLVals___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_21__elabAppLVals___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_21__elabAppLVals___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_21__elabAppLVals___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_21__elabAppLVals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = l_List_isEmpty___rarg(x_2);
if (x_14 == 0)
{
if (x_6 == 0)
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_App_20__elabAppLValsAux___main(x_3, x_4, x_5, x_6, x_1, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_16 = l___private_Lean_Elab_App_21__elabAppLVals___closed__3;
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
x_22 = l___private_Lean_Elab_App_20__elabAppLValsAux___main(x_3, x_4, x_5, x_6, x_1, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_22;
}
}
}
lean_object* l___private_Lean_Elab_App_21__elabAppLVals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l___private_Lean_Elab_App_21__elabAppLVals(x_1, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_22__elabAppFnId___spec__1___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_22__elabAppFnId___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_22__elabAppFnId___spec__1___rarg), 1, 0);
return x_7;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__2(lean_object* x_1) {
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
x_7 = l_List_map___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__2(x_5);
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
x_11 = l_List_map___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
x_21 = l_List_map___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__2(x_20);
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
x_52 = l___private_Lean_Elab_App_21__elabAppLVals(x_19, x_22, x_2, x_3, x_4, x_5, x_9, x_10, x_11, x_12, x_13, x_14, x_25);
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
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_52, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_4);
x_70 = l_Lean_Elab_Term_ensureHasType(x_4, x_68, x_9, x_10, x_11, x_12, x_13, x_14, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_26);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Elab_Term_SavedState_restore(x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_75);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 1);
x_79 = lean_ctor_get(x_76, 0);
lean_dec(x_79);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 0, x_71);
x_80 = lean_array_push(x_7, x_76);
x_7 = x_80;
x_8 = x_18;
x_15 = x_78;
goto _start;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
lean_dec(x_76);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_71);
lean_ctor_set(x_83, 1, x_74);
x_84 = lean_array_push(x_7, x_83);
x_7 = x_84;
x_8 = x_18;
x_15 = x_82;
goto _start;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_70, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_70, 1);
lean_inc(x_87);
lean_dec(x_70);
x_27 = x_86;
x_28 = x_87;
goto block_51;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_52, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_52, 1);
lean_inc(x_89);
lean_dec(x_52);
x_27 = x_88;
x_28 = x_89;
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
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
x_21 = l_List_map___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__2(x_20);
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
x_52 = l___private_Lean_Elab_App_21__elabAppLVals(x_19, x_22, x_2, x_3, x_4, x_5, x_9, x_10, x_11, x_12, x_13, x_14, x_25);
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
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_52, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_4);
x_70 = l_Lean_Elab_Term_ensureHasType(x_4, x_68, x_9, x_10, x_11, x_12, x_13, x_14, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_26);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Elab_Term_SavedState_restore(x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_75);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 1);
x_79 = lean_ctor_get(x_76, 0);
lean_dec(x_79);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 0, x_71);
x_80 = lean_array_push(x_7, x_76);
x_7 = x_80;
x_8 = x_18;
x_15 = x_78;
goto _start;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
lean_dec(x_76);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_71);
lean_ctor_set(x_83, 1, x_74);
x_84 = lean_array_push(x_7, x_83);
x_7 = x_84;
x_8 = x_18;
x_15 = x_82;
goto _start;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_70, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_70, 1);
lean_inc(x_87);
lean_dec(x_70);
x_27 = x_86;
x_28 = x_87;
goto block_51;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_52, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_52, 1);
lean_inc(x_89);
lean_dec(x_52);
x_27 = x_88;
x_28 = x_89;
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
lean_object* l___private_Lean_Elab_App_22__elabAppFnId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
x_54 = l_List_foldlM___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_43, x_9, x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_29);
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
x_57 = l_List_foldlM___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__3(x_3, x_4, x_5, x_6, x_7, x_43, x_9, x_28, x_56, x_11, x_12, x_13, x_14, x_15, x_29);
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
x_67 = l_List_foldlM___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__4(x_3, x_4, x_5, x_6, x_7, x_43, x_9, x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_29);
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
x_70 = l_List_foldlM___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__4(x_3, x_4, x_5, x_6, x_7, x_43, x_9, x_28, x_69, x_11, x_12, x_13, x_14, x_15, x_29);
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
x_78 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_22__elabAppFnId___spec__1___rarg(x_16);
return x_78;
}
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_22__elabAppFnId___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_22__elabAppFnId___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_List_foldlM___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__3(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_List_foldlM___main___at___private_Lean_Elab_App_22__elabAppFnId___spec__4(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
lean_object* l___private_Lean_Elab_App_22__elabAppFnId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = lean_unbox(x_8);
lean_dec(x_8);
x_19 = l___private_Lean_Elab_App_22__elabAppFnId(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_App_23__elabAppFn___main___spec__1(lean_object* x_1) {
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
x_9 = l_List_map___main___at___private_Lean_Elab_App_23__elabAppFn___main___spec__1(x_5);
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
x_15 = l_List_map___main___at___private_Lean_Elab_App_23__elabAppFn___main___spec__1(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_23__elabAppFn___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
x_24 = l___private_Lean_Elab_App_23__elabAppFn___main(x_20, x_2, x_3, x_4, x_5, x_6, x_23, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
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
lean_object* _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("placeholders '_' cannot be used where a function is expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicitUniv");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected occurrence of named pattern");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("arrayRef");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namedPattern");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Lean_Expr_ctorName___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_App_23__elabAppFn___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_381; lean_object* x_382; uint8_t x_383; 
lean_inc(x_1);
x_381 = l_Lean_Syntax_getKind(x_1);
x_382 = l_Lean_choiceKind;
x_383 = lean_name_eq(x_381, x_382);
lean_dec(x_381);
if (x_383 == 0)
{
uint8_t x_384; uint8_t x_1180; lean_object* x_1594; uint8_t x_1595; 
x_1594 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__13;
lean_inc(x_1);
x_1595 = l_Lean_Syntax_isOfKind(x_1, x_1594);
if (x_1595 == 0)
{
uint8_t x_1596; 
x_1596 = 0;
x_1180 = x_1596;
goto block_1593;
}
else
{
lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; uint8_t x_1600; 
x_1597 = l_Lean_Syntax_getArgs(x_1);
x_1598 = lean_array_get_size(x_1597);
lean_dec(x_1597);
x_1599 = lean_unsigned_to_nat(3u);
x_1600 = lean_nat_dec_eq(x_1598, x_1599);
lean_dec(x_1598);
x_1180 = x_1600;
goto block_1593;
}
block_1179:
{
if (x_384 == 0)
{
lean_object* x_385; uint8_t x_386; 
x_385 = l_Lean_identKind___closed__2;
lean_inc(x_1);
x_386 = l_Lean_Syntax_isOfKind(x_1, x_385);
if (x_386 == 0)
{
uint8_t x_387; uint8_t x_417; lean_object* x_803; uint8_t x_804; 
x_803 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__5;
lean_inc(x_1);
x_804 = l_Lean_Syntax_isOfKind(x_1, x_803);
if (x_804 == 0)
{
uint8_t x_805; 
x_805 = 0;
x_417 = x_805;
goto block_802;
}
else
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; uint8_t x_809; 
x_806 = l_Lean_Syntax_getArgs(x_1);
x_807 = lean_array_get_size(x_806);
lean_dec(x_806);
x_808 = lean_unsigned_to_nat(4u);
x_809 = lean_nat_dec_eq(x_807, x_808);
lean_dec(x_807);
x_417 = x_809;
goto block_802;
}
block_416:
{
if (x_387 == 0)
{
lean_object* x_388; uint8_t x_389; 
x_388 = l_Lean_mkHole___closed__2;
lean_inc(x_1);
x_389 = l_Lean_Syntax_isOfKind(x_1, x_388);
if (x_389 == 0)
{
uint8_t x_390; 
x_390 = 0;
x_16 = x_390;
goto block_380;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; 
x_391 = l_Lean_Syntax_getArgs(x_1);
x_392 = lean_array_get_size(x_391);
lean_dec(x_391);
x_393 = lean_unsigned_to_nat(1u);
x_394 = lean_nat_dec_eq(x_392, x_393);
lean_dec(x_392);
x_16 = x_394;
goto block_380;
}
}
else
{
lean_object* x_395; lean_object* x_396; uint8_t x_397; uint8_t x_406; 
x_395 = lean_unsigned_to_nat(1u);
x_396 = l_Lean_Syntax_getArg(x_1, x_395);
lean_dec(x_1);
lean_inc(x_396);
x_406 = l_Lean_Syntax_isOfKind(x_396, x_385);
if (x_406 == 0)
{
lean_object* x_407; uint8_t x_408; 
x_407 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__5;
lean_inc(x_396);
x_408 = l_Lean_Syntax_isOfKind(x_396, x_407);
if (x_408 == 0)
{
uint8_t x_409; 
x_409 = 0;
x_397 = x_409;
goto block_405;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
x_410 = l_Lean_Syntax_getArgs(x_396);
x_411 = lean_array_get_size(x_410);
lean_dec(x_410);
x_412 = lean_unsigned_to_nat(4u);
x_413 = lean_nat_dec_eq(x_411, x_412);
lean_dec(x_411);
x_397 = x_413;
goto block_405;
}
}
else
{
uint8_t x_414; 
x_414 = 1;
x_1 = x_396;
x_6 = x_414;
goto _start;
}
block_405:
{
if (x_397 == 0)
{
lean_object* x_398; 
lean_dec(x_396);
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
x_398 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_22__elabAppFnId___spec__1___rarg(x_15);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; uint8_t x_401; 
x_399 = lean_unsigned_to_nat(0u);
x_400 = l_Lean_Syntax_getArg(x_396, x_399);
x_401 = l_Lean_Syntax_isOfKind(x_400, x_385);
if (x_401 == 0)
{
lean_object* x_402; 
lean_dec(x_396);
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
x_402 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_App_22__elabAppFnId___spec__1___rarg(x_15);
return x_402;
}
else
{
uint8_t x_403; 
x_403 = 1;
x_1 = x_396;
x_6 = x_403;
goto _start;
}
}
}
}
}
block_802:
{
if (x_417 == 0)
{
lean_object* x_418; uint8_t x_419; 
x_418 = l___private_Lean_Elab_Term_10__isExplicit___closed__2;
lean_inc(x_1);
x_419 = l_Lean_Syntax_isOfKind(x_1, x_418);
if (x_419 == 0)
{
uint8_t x_420; 
x_420 = 0;
x_387 = x_420;
goto block_416;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
x_421 = l_Lean_Syntax_getArgs(x_1);
x_422 = lean_array_get_size(x_421);
lean_dec(x_421);
x_423 = lean_unsigned_to_nat(2u);
x_424 = lean_nat_dec_eq(x_422, x_423);
lean_dec(x_422);
x_387 = x_424;
goto block_416;
}
}
else
{
lean_object* x_425; lean_object* x_426; uint8_t x_427; 
x_425 = lean_unsigned_to_nat(0u);
x_426 = l_Lean_Syntax_getArg(x_1, x_425);
lean_inc(x_426);
x_427 = l_Lean_Syntax_isOfKind(x_426, x_385);
if (x_427 == 0)
{
uint8_t x_428; uint8_t x_429; 
lean_dec(x_426);
x_428 = l_List_isEmpty___rarg(x_2);
if (x_7 == 0)
{
uint8_t x_787; 
x_787 = 1;
x_429 = x_787;
goto block_786;
}
else
{
uint8_t x_788; 
x_788 = 0;
x_429 = x_788;
goto block_786;
}
block_786:
{
if (x_428 == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_467; lean_object* x_468; lean_object* x_490; 
x_430 = lean_box(0);
x_431 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_434 = x_431;
} else {
 lean_dec_ref(x_431);
 x_434 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_490 = l_Lean_Elab_Term_elabTerm(x_1, x_430, x_429, x_9, x_10, x_11, x_12, x_13, x_14, x_433);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec(x_490);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_493 = l___private_Lean_Elab_App_21__elabAppLVals(x_491, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_492);
if (lean_obj_tag(x_493) == 0)
{
if (x_7 == 0)
{
lean_object* x_494; lean_object* x_495; 
lean_dec(x_434);
lean_dec(x_5);
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
lean_dec(x_493);
x_467 = x_494;
x_468 = x_495;
goto block_489;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = lean_ctor_get(x_493, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_493, 1);
lean_inc(x_497);
lean_dec(x_493);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_498 = l_Lean_Elab_Term_ensureHasType(x_5, x_496, x_9, x_10, x_11, x_12, x_13, x_14, x_497);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; 
lean_dec(x_434);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
lean_dec(x_498);
x_467 = x_499;
x_468 = x_500;
goto block_489;
}
else
{
lean_object* x_501; lean_object* x_502; 
x_501 = lean_ctor_get(x_498, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_498, 1);
lean_inc(x_502);
lean_dec(x_498);
x_435 = x_501;
x_436 = x_502;
goto block_466;
}
}
}
else
{
lean_object* x_503; lean_object* x_504; 
lean_dec(x_5);
x_503 = lean_ctor_get(x_493, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_493, 1);
lean_inc(x_504);
lean_dec(x_493);
x_435 = x_503;
x_436 = x_504;
goto block_466;
}
}
else
{
lean_object* x_505; lean_object* x_506; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_505 = lean_ctor_get(x_490, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_490, 1);
lean_inc(x_506);
lean_dec(x_490);
x_435 = x_505;
x_436 = x_506;
goto block_466;
}
block_466:
{
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_437; uint8_t x_438; 
lean_dec(x_434);
x_437 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_436);
x_438 = !lean_is_exclusive(x_437);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; 
x_439 = lean_ctor_get(x_437, 0);
x_440 = lean_ctor_get(x_437, 1);
x_441 = l_Lean_Elab_Term_SavedState_restore(x_432, x_9, x_10, x_11, x_12, x_13, x_14, x_440);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_442 = !lean_is_exclusive(x_441);
if (x_442 == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_441, 1);
x_444 = lean_ctor_get(x_441, 0);
lean_dec(x_444);
lean_ctor_set_tag(x_441, 1);
lean_ctor_set(x_441, 1, x_439);
lean_ctor_set(x_441, 0, x_435);
x_445 = lean_array_push(x_8, x_441);
lean_ctor_set(x_437, 1, x_443);
lean_ctor_set(x_437, 0, x_445);
return x_437;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_446 = lean_ctor_get(x_441, 1);
lean_inc(x_446);
lean_dec(x_441);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_435);
lean_ctor_set(x_447, 1, x_439);
x_448 = lean_array_push(x_8, x_447);
lean_ctor_set(x_437, 1, x_446);
lean_ctor_set(x_437, 0, x_448);
return x_437;
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_449 = lean_ctor_get(x_437, 0);
x_450 = lean_ctor_get(x_437, 1);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_437);
x_451 = l_Lean_Elab_Term_SavedState_restore(x_432, x_9, x_10, x_11, x_12, x_13, x_14, x_450);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_452 = lean_ctor_get(x_451, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_453 = x_451;
} else {
 lean_dec_ref(x_451);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 2, 0);
} else {
 x_454 = x_453;
 lean_ctor_set_tag(x_454, 1);
}
lean_ctor_set(x_454, 0, x_435);
lean_ctor_set(x_454, 1, x_449);
x_455 = lean_array_push(x_8, x_454);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_452);
return x_456;
}
}
else
{
lean_object* x_457; lean_object* x_458; uint8_t x_459; 
lean_dec(x_8);
x_457 = lean_ctor_get(x_435, 0);
lean_inc(x_457);
x_458 = l_Lean_Elab_postponeExceptionId;
x_459 = lean_nat_dec_eq(x_457, x_458);
lean_dec(x_457);
if (x_459 == 0)
{
lean_object* x_460; 
lean_dec(x_432);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_434)) {
 x_460 = lean_alloc_ctor(1, 2, 0);
} else {
 x_460 = x_434;
 lean_ctor_set_tag(x_460, 1);
}
lean_ctor_set(x_460, 0, x_435);
lean_ctor_set(x_460, 1, x_436);
return x_460;
}
else
{
lean_object* x_461; uint8_t x_462; 
lean_dec(x_434);
x_461 = l_Lean_Elab_Term_SavedState_restore(x_432, x_9, x_10, x_11, x_12, x_13, x_14, x_436);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_462 = !lean_is_exclusive(x_461);
if (x_462 == 0)
{
lean_object* x_463; 
x_463 = lean_ctor_get(x_461, 0);
lean_dec(x_463);
lean_ctor_set_tag(x_461, 1);
lean_ctor_set(x_461, 0, x_435);
return x_461;
}
else
{
lean_object* x_464; lean_object* x_465; 
x_464 = lean_ctor_get(x_461, 1);
lean_inc(x_464);
lean_dec(x_461);
x_465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_465, 0, x_435);
lean_ctor_set(x_465, 1, x_464);
return x_465;
}
}
}
}
block_489:
{
lean_object* x_469; uint8_t x_470; 
x_469 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_468);
x_470 = !lean_is_exclusive(x_469);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; uint8_t x_474; 
x_471 = lean_ctor_get(x_469, 0);
x_472 = lean_ctor_get(x_469, 1);
x_473 = l_Lean_Elab_Term_SavedState_restore(x_432, x_9, x_10, x_11, x_12, x_13, x_14, x_472);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_474 = !lean_is_exclusive(x_473);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_473, 1);
x_476 = lean_ctor_get(x_473, 0);
lean_dec(x_476);
lean_ctor_set(x_473, 1, x_471);
lean_ctor_set(x_473, 0, x_467);
x_477 = lean_array_push(x_8, x_473);
lean_ctor_set(x_469, 1, x_475);
lean_ctor_set(x_469, 0, x_477);
return x_469;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_478 = lean_ctor_get(x_473, 1);
lean_inc(x_478);
lean_dec(x_473);
x_479 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_479, 0, x_467);
lean_ctor_set(x_479, 1, x_471);
x_480 = lean_array_push(x_8, x_479);
lean_ctor_set(x_469, 1, x_478);
lean_ctor_set(x_469, 0, x_480);
return x_469;
}
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_481 = lean_ctor_get(x_469, 0);
x_482 = lean_ctor_get(x_469, 1);
lean_inc(x_482);
lean_inc(x_481);
lean_dec(x_469);
x_483 = l_Lean_Elab_Term_SavedState_restore(x_432, x_9, x_10, x_11, x_12, x_13, x_14, x_482);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_484 = lean_ctor_get(x_483, 1);
lean_inc(x_484);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_485 = x_483;
} else {
 lean_dec_ref(x_483);
 x_485 = lean_box(0);
}
if (lean_is_scalar(x_485)) {
 x_486 = lean_alloc_ctor(0, 2, 0);
} else {
 x_486 = x_485;
}
lean_ctor_set(x_486, 0, x_467);
lean_ctor_set(x_486, 1, x_481);
x_487 = lean_array_push(x_8, x_486);
x_488 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_484);
return x_488;
}
}
}
else
{
uint8_t x_507; 
x_507 = l_Array_isEmpty___rarg(x_3);
if (x_507 == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_545; lean_object* x_546; lean_object* x_568; 
x_508 = lean_box(0);
x_509 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_509, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_512 = x_509;
} else {
 lean_dec_ref(x_509);
 x_512 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_568 = l_Lean_Elab_Term_elabTerm(x_1, x_508, x_429, x_9, x_10, x_11, x_12, x_13, x_14, x_511);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_568, 1);
lean_inc(x_570);
lean_dec(x_568);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_571 = l___private_Lean_Elab_App_21__elabAppLVals(x_569, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_570);
if (lean_obj_tag(x_571) == 0)
{
if (x_7 == 0)
{
lean_object* x_572; lean_object* x_573; 
lean_dec(x_512);
lean_dec(x_5);
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_571, 1);
lean_inc(x_573);
lean_dec(x_571);
x_545 = x_572;
x_546 = x_573;
goto block_567;
}
else
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_574 = lean_ctor_get(x_571, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_571, 1);
lean_inc(x_575);
lean_dec(x_571);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_576 = l_Lean_Elab_Term_ensureHasType(x_5, x_574, x_9, x_10, x_11, x_12, x_13, x_14, x_575);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; lean_object* x_578; 
lean_dec(x_512);
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_576, 1);
lean_inc(x_578);
lean_dec(x_576);
x_545 = x_577;
x_546 = x_578;
goto block_567;
}
else
{
lean_object* x_579; lean_object* x_580; 
x_579 = lean_ctor_get(x_576, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_576, 1);
lean_inc(x_580);
lean_dec(x_576);
x_513 = x_579;
x_514 = x_580;
goto block_544;
}
}
}
else
{
lean_object* x_581; lean_object* x_582; 
lean_dec(x_5);
x_581 = lean_ctor_get(x_571, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_571, 1);
lean_inc(x_582);
lean_dec(x_571);
x_513 = x_581;
x_514 = x_582;
goto block_544;
}
}
else
{
lean_object* x_583; lean_object* x_584; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_583 = lean_ctor_get(x_568, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_568, 1);
lean_inc(x_584);
lean_dec(x_568);
x_513 = x_583;
x_514 = x_584;
goto block_544;
}
block_544:
{
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_515; uint8_t x_516; 
lean_dec(x_512);
x_515 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_514);
x_516 = !lean_is_exclusive(x_515);
if (x_516 == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; 
x_517 = lean_ctor_get(x_515, 0);
x_518 = lean_ctor_get(x_515, 1);
x_519 = l_Lean_Elab_Term_SavedState_restore(x_510, x_9, x_10, x_11, x_12, x_13, x_14, x_518);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_520 = !lean_is_exclusive(x_519);
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_521 = lean_ctor_get(x_519, 1);
x_522 = lean_ctor_get(x_519, 0);
lean_dec(x_522);
lean_ctor_set_tag(x_519, 1);
lean_ctor_set(x_519, 1, x_517);
lean_ctor_set(x_519, 0, x_513);
x_523 = lean_array_push(x_8, x_519);
lean_ctor_set(x_515, 1, x_521);
lean_ctor_set(x_515, 0, x_523);
return x_515;
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_524 = lean_ctor_get(x_519, 1);
lean_inc(x_524);
lean_dec(x_519);
x_525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_525, 0, x_513);
lean_ctor_set(x_525, 1, x_517);
x_526 = lean_array_push(x_8, x_525);
lean_ctor_set(x_515, 1, x_524);
lean_ctor_set(x_515, 0, x_526);
return x_515;
}
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_527 = lean_ctor_get(x_515, 0);
x_528 = lean_ctor_get(x_515, 1);
lean_inc(x_528);
lean_inc(x_527);
lean_dec(x_515);
x_529 = l_Lean_Elab_Term_SavedState_restore(x_510, x_9, x_10, x_11, x_12, x_13, x_14, x_528);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_530 = lean_ctor_get(x_529, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 x_531 = x_529;
} else {
 lean_dec_ref(x_529);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_531)) {
 x_532 = lean_alloc_ctor(1, 2, 0);
} else {
 x_532 = x_531;
 lean_ctor_set_tag(x_532, 1);
}
lean_ctor_set(x_532, 0, x_513);
lean_ctor_set(x_532, 1, x_527);
x_533 = lean_array_push(x_8, x_532);
x_534 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_534, 0, x_533);
lean_ctor_set(x_534, 1, x_530);
return x_534;
}
}
else
{
lean_object* x_535; lean_object* x_536; uint8_t x_537; 
lean_dec(x_8);
x_535 = lean_ctor_get(x_513, 0);
lean_inc(x_535);
x_536 = l_Lean_Elab_postponeExceptionId;
x_537 = lean_nat_dec_eq(x_535, x_536);
lean_dec(x_535);
if (x_537 == 0)
{
lean_object* x_538; 
lean_dec(x_510);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_512)) {
 x_538 = lean_alloc_ctor(1, 2, 0);
} else {
 x_538 = x_512;
 lean_ctor_set_tag(x_538, 1);
}
lean_ctor_set(x_538, 0, x_513);
lean_ctor_set(x_538, 1, x_514);
return x_538;
}
else
{
lean_object* x_539; uint8_t x_540; 
lean_dec(x_512);
x_539 = l_Lean_Elab_Term_SavedState_restore(x_510, x_9, x_10, x_11, x_12, x_13, x_14, x_514);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_540 = !lean_is_exclusive(x_539);
if (x_540 == 0)
{
lean_object* x_541; 
x_541 = lean_ctor_get(x_539, 0);
lean_dec(x_541);
lean_ctor_set_tag(x_539, 1);
lean_ctor_set(x_539, 0, x_513);
return x_539;
}
else
{
lean_object* x_542; lean_object* x_543; 
x_542 = lean_ctor_get(x_539, 1);
lean_inc(x_542);
lean_dec(x_539);
x_543 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_543, 0, x_513);
lean_ctor_set(x_543, 1, x_542);
return x_543;
}
}
}
}
block_567:
{
lean_object* x_547; uint8_t x_548; 
x_547 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_546);
x_548 = !lean_is_exclusive(x_547);
if (x_548 == 0)
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; uint8_t x_552; 
x_549 = lean_ctor_get(x_547, 0);
x_550 = lean_ctor_get(x_547, 1);
x_551 = l_Lean_Elab_Term_SavedState_restore(x_510, x_9, x_10, x_11, x_12, x_13, x_14, x_550);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_552 = !lean_is_exclusive(x_551);
if (x_552 == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_551, 1);
x_554 = lean_ctor_get(x_551, 0);
lean_dec(x_554);
lean_ctor_set(x_551, 1, x_549);
lean_ctor_set(x_551, 0, x_545);
x_555 = lean_array_push(x_8, x_551);
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
x_557 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_557, 0, x_545);
lean_ctor_set(x_557, 1, x_549);
x_558 = lean_array_push(x_8, x_557);
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
x_561 = l_Lean_Elab_Term_SavedState_restore(x_510, x_9, x_10, x_11, x_12, x_13, x_14, x_560);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
 x_564 = lean_alloc_ctor(0, 2, 0);
} else {
 x_564 = x_563;
}
lean_ctor_set(x_564, 0, x_545);
lean_ctor_set(x_564, 1, x_559);
x_565 = lean_array_push(x_8, x_564);
x_566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_562);
return x_566;
}
}
}
else
{
uint8_t x_585; 
x_585 = l_Array_isEmpty___rarg(x_4);
if (x_585 == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_623; lean_object* x_624; lean_object* x_646; 
x_586 = lean_box(0);
x_587 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_590 = x_587;
} else {
 lean_dec_ref(x_587);
 x_590 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_646 = l_Lean_Elab_Term_elabTerm(x_1, x_586, x_429, x_9, x_10, x_11, x_12, x_13, x_14, x_589);
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_647 = lean_ctor_get(x_646, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_646, 1);
lean_inc(x_648);
lean_dec(x_646);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_649 = l___private_Lean_Elab_App_21__elabAppLVals(x_647, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_648);
if (lean_obj_tag(x_649) == 0)
{
if (x_7 == 0)
{
lean_object* x_650; lean_object* x_651; 
lean_dec(x_590);
lean_dec(x_5);
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_649, 1);
lean_inc(x_651);
lean_dec(x_649);
x_623 = x_650;
x_624 = x_651;
goto block_645;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_652 = lean_ctor_get(x_649, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_649, 1);
lean_inc(x_653);
lean_dec(x_649);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_654 = l_Lean_Elab_Term_ensureHasType(x_5, x_652, x_9, x_10, x_11, x_12, x_13, x_14, x_653);
if (lean_obj_tag(x_654) == 0)
{
lean_object* x_655; lean_object* x_656; 
lean_dec(x_590);
x_655 = lean_ctor_get(x_654, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_654, 1);
lean_inc(x_656);
lean_dec(x_654);
x_623 = x_655;
x_624 = x_656;
goto block_645;
}
else
{
lean_object* x_657; lean_object* x_658; 
x_657 = lean_ctor_get(x_654, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_654, 1);
lean_inc(x_658);
lean_dec(x_654);
x_591 = x_657;
x_592 = x_658;
goto block_622;
}
}
}
else
{
lean_object* x_659; lean_object* x_660; 
lean_dec(x_5);
x_659 = lean_ctor_get(x_649, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_649, 1);
lean_inc(x_660);
lean_dec(x_649);
x_591 = x_659;
x_592 = x_660;
goto block_622;
}
}
else
{
lean_object* x_661; lean_object* x_662; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_661 = lean_ctor_get(x_646, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_646, 1);
lean_inc(x_662);
lean_dec(x_646);
x_591 = x_661;
x_592 = x_662;
goto block_622;
}
block_622:
{
if (lean_obj_tag(x_591) == 0)
{
lean_object* x_593; uint8_t x_594; 
lean_dec(x_590);
x_593 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_592);
x_594 = !lean_is_exclusive(x_593);
if (x_594 == 0)
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; uint8_t x_598; 
x_595 = lean_ctor_get(x_593, 0);
x_596 = lean_ctor_get(x_593, 1);
x_597 = l_Lean_Elab_Term_SavedState_restore(x_588, x_9, x_10, x_11, x_12, x_13, x_14, x_596);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_598 = !lean_is_exclusive(x_597);
if (x_598 == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_599 = lean_ctor_get(x_597, 1);
x_600 = lean_ctor_get(x_597, 0);
lean_dec(x_600);
lean_ctor_set_tag(x_597, 1);
lean_ctor_set(x_597, 1, x_595);
lean_ctor_set(x_597, 0, x_591);
x_601 = lean_array_push(x_8, x_597);
lean_ctor_set(x_593, 1, x_599);
lean_ctor_set(x_593, 0, x_601);
return x_593;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_597, 1);
lean_inc(x_602);
lean_dec(x_597);
x_603 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_603, 0, x_591);
lean_ctor_set(x_603, 1, x_595);
x_604 = lean_array_push(x_8, x_603);
lean_ctor_set(x_593, 1, x_602);
lean_ctor_set(x_593, 0, x_604);
return x_593;
}
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_605 = lean_ctor_get(x_593, 0);
x_606 = lean_ctor_get(x_593, 1);
lean_inc(x_606);
lean_inc(x_605);
lean_dec(x_593);
x_607 = l_Lean_Elab_Term_SavedState_restore(x_588, x_9, x_10, x_11, x_12, x_13, x_14, x_606);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_608 = lean_ctor_get(x_607, 1);
lean_inc(x_608);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 lean_ctor_release(x_607, 1);
 x_609 = x_607;
} else {
 lean_dec_ref(x_607);
 x_609 = lean_box(0);
}
if (lean_is_scalar(x_609)) {
 x_610 = lean_alloc_ctor(1, 2, 0);
} else {
 x_610 = x_609;
 lean_ctor_set_tag(x_610, 1);
}
lean_ctor_set(x_610, 0, x_591);
lean_ctor_set(x_610, 1, x_605);
x_611 = lean_array_push(x_8, x_610);
x_612 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_612, 0, x_611);
lean_ctor_set(x_612, 1, x_608);
return x_612;
}
}
else
{
lean_object* x_613; lean_object* x_614; uint8_t x_615; 
lean_dec(x_8);
x_613 = lean_ctor_get(x_591, 0);
lean_inc(x_613);
x_614 = l_Lean_Elab_postponeExceptionId;
x_615 = lean_nat_dec_eq(x_613, x_614);
lean_dec(x_613);
if (x_615 == 0)
{
lean_object* x_616; 
lean_dec(x_588);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_590)) {
 x_616 = lean_alloc_ctor(1, 2, 0);
} else {
 x_616 = x_590;
 lean_ctor_set_tag(x_616, 1);
}
lean_ctor_set(x_616, 0, x_591);
lean_ctor_set(x_616, 1, x_592);
return x_616;
}
else
{
lean_object* x_617; uint8_t x_618; 
lean_dec(x_590);
x_617 = l_Lean_Elab_Term_SavedState_restore(x_588, x_9, x_10, x_11, x_12, x_13, x_14, x_592);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_618 = !lean_is_exclusive(x_617);
if (x_618 == 0)
{
lean_object* x_619; 
x_619 = lean_ctor_get(x_617, 0);
lean_dec(x_619);
lean_ctor_set_tag(x_617, 1);
lean_ctor_set(x_617, 0, x_591);
return x_617;
}
else
{
lean_object* x_620; lean_object* x_621; 
x_620 = lean_ctor_get(x_617, 1);
lean_inc(x_620);
lean_dec(x_617);
x_621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_621, 0, x_591);
lean_ctor_set(x_621, 1, x_620);
return x_621;
}
}
}
}
block_645:
{
lean_object* x_625; uint8_t x_626; 
x_625 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_624);
x_626 = !lean_is_exclusive(x_625);
if (x_626 == 0)
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; uint8_t x_630; 
x_627 = lean_ctor_get(x_625, 0);
x_628 = lean_ctor_get(x_625, 1);
x_629 = l_Lean_Elab_Term_SavedState_restore(x_588, x_9, x_10, x_11, x_12, x_13, x_14, x_628);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_630 = !lean_is_exclusive(x_629);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_631 = lean_ctor_get(x_629, 1);
x_632 = lean_ctor_get(x_629, 0);
lean_dec(x_632);
lean_ctor_set(x_629, 1, x_627);
lean_ctor_set(x_629, 0, x_623);
x_633 = lean_array_push(x_8, x_629);
lean_ctor_set(x_625, 1, x_631);
lean_ctor_set(x_625, 0, x_633);
return x_625;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_634 = lean_ctor_get(x_629, 1);
lean_inc(x_634);
lean_dec(x_629);
x_635 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_635, 0, x_623);
lean_ctor_set(x_635, 1, x_627);
x_636 = lean_array_push(x_8, x_635);
lean_ctor_set(x_625, 1, x_634);
lean_ctor_set(x_625, 0, x_636);
return x_625;
}
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_637 = lean_ctor_get(x_625, 0);
x_638 = lean_ctor_get(x_625, 1);
lean_inc(x_638);
lean_inc(x_637);
lean_dec(x_625);
x_639 = l_Lean_Elab_Term_SavedState_restore(x_588, x_9, x_10, x_11, x_12, x_13, x_14, x_638);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_640 = lean_ctor_get(x_639, 1);
lean_inc(x_640);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 lean_ctor_release(x_639, 1);
 x_641 = x_639;
} else {
 lean_dec_ref(x_639);
 x_641 = lean_box(0);
}
if (lean_is_scalar(x_641)) {
 x_642 = lean_alloc_ctor(0, 2, 0);
} else {
 x_642 = x_641;
}
lean_ctor_set(x_642, 0, x_623);
lean_ctor_set(x_642, 1, x_637);
x_643 = lean_array_push(x_8, x_642);
x_644 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_644, 0, x_643);
lean_ctor_set(x_644, 1, x_640);
return x_644;
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
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; uint8_t x_699; lean_object* x_700; 
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
x_699 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_700 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_699, x_9, x_10, x_11, x_12, x_13, x_14, x_665);
if (lean_obj_tag(x_700) == 0)
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; uint8_t x_704; 
lean_dec(x_666);
x_701 = lean_ctor_get(x_700, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_700, 1);
lean_inc(x_702);
lean_dec(x_700);
x_703 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_702);
x_704 = !lean_is_exclusive(x_703);
if (x_704 == 0)
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; uint8_t x_708; 
x_705 = lean_ctor_get(x_703, 0);
x_706 = lean_ctor_get(x_703, 1);
x_707 = l_Lean_Elab_Term_SavedState_restore(x_664, x_9, x_10, x_11, x_12, x_13, x_14, x_706);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_708 = !lean_is_exclusive(x_707);
if (x_708 == 0)
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = lean_ctor_get(x_707, 1);
x_710 = lean_ctor_get(x_707, 0);
lean_dec(x_710);
lean_ctor_set(x_707, 1, x_705);
lean_ctor_set(x_707, 0, x_701);
x_711 = lean_array_push(x_8, x_707);
lean_ctor_set(x_703, 1, x_709);
lean_ctor_set(x_703, 0, x_711);
return x_703;
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; 
x_712 = lean_ctor_get(x_707, 1);
lean_inc(x_712);
lean_dec(x_707);
x_713 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_713, 0, x_701);
lean_ctor_set(x_713, 1, x_705);
x_714 = lean_array_push(x_8, x_713);
lean_ctor_set(x_703, 1, x_712);
lean_ctor_set(x_703, 0, x_714);
return x_703;
}
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; 
x_715 = lean_ctor_get(x_703, 0);
x_716 = lean_ctor_get(x_703, 1);
lean_inc(x_716);
lean_inc(x_715);
lean_dec(x_703);
x_717 = l_Lean_Elab_Term_SavedState_restore(x_664, x_9, x_10, x_11, x_12, x_13, x_14, x_716);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_718 = lean_ctor_get(x_717, 1);
lean_inc(x_718);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 lean_ctor_release(x_717, 1);
 x_719 = x_717;
} else {
 lean_dec_ref(x_717);
 x_719 = lean_box(0);
}
if (lean_is_scalar(x_719)) {
 x_720 = lean_alloc_ctor(0, 2, 0);
} else {
 x_720 = x_719;
}
lean_ctor_set(x_720, 0, x_701);
lean_ctor_set(x_720, 1, x_715);
x_721 = lean_array_push(x_8, x_720);
x_722 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_722, 0, x_721);
lean_ctor_set(x_722, 1, x_718);
return x_722;
}
}
else
{
lean_object* x_723; lean_object* x_724; 
x_723 = lean_ctor_get(x_700, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_700, 1);
lean_inc(x_724);
lean_dec(x_700);
x_667 = x_723;
x_668 = x_724;
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
else
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_761; 
x_725 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_726 = lean_ctor_get(x_725, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_725, 1);
lean_inc(x_727);
if (lean_is_exclusive(x_725)) {
 lean_ctor_release(x_725, 0);
 lean_ctor_release(x_725, 1);
 x_728 = x_725;
} else {
 lean_dec_ref(x_725);
 x_728 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_761 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_429, x_9, x_10, x_11, x_12, x_13, x_14, x_727);
if (lean_obj_tag(x_761) == 0)
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; uint8_t x_765; 
lean_dec(x_728);
x_762 = lean_ctor_get(x_761, 0);
lean_inc(x_762);
x_763 = lean_ctor_get(x_761, 1);
lean_inc(x_763);
lean_dec(x_761);
x_764 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_763);
x_765 = !lean_is_exclusive(x_764);
if (x_765 == 0)
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; uint8_t x_769; 
x_766 = lean_ctor_get(x_764, 0);
x_767 = lean_ctor_get(x_764, 1);
x_768 = l_Lean_Elab_Term_SavedState_restore(x_726, x_9, x_10, x_11, x_12, x_13, x_14, x_767);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_769 = !lean_is_exclusive(x_768);
if (x_769 == 0)
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; 
x_770 = lean_ctor_get(x_768, 1);
x_771 = lean_ctor_get(x_768, 0);
lean_dec(x_771);
lean_ctor_set(x_768, 1, x_766);
lean_ctor_set(x_768, 0, x_762);
x_772 = lean_array_push(x_8, x_768);
lean_ctor_set(x_764, 1, x_770);
lean_ctor_set(x_764, 0, x_772);
return x_764;
}
else
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_773 = lean_ctor_get(x_768, 1);
lean_inc(x_773);
lean_dec(x_768);
x_774 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_774, 0, x_762);
lean_ctor_set(x_774, 1, x_766);
x_775 = lean_array_push(x_8, x_774);
lean_ctor_set(x_764, 1, x_773);
lean_ctor_set(x_764, 0, x_775);
return x_764;
}
}
else
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
x_776 = lean_ctor_get(x_764, 0);
x_777 = lean_ctor_get(x_764, 1);
lean_inc(x_777);
lean_inc(x_776);
lean_dec(x_764);
x_778 = l_Lean_Elab_Term_SavedState_restore(x_726, x_9, x_10, x_11, x_12, x_13, x_14, x_777);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_779 = lean_ctor_get(x_778, 1);
lean_inc(x_779);
if (lean_is_exclusive(x_778)) {
 lean_ctor_release(x_778, 0);
 lean_ctor_release(x_778, 1);
 x_780 = x_778;
} else {
 lean_dec_ref(x_778);
 x_780 = lean_box(0);
}
if (lean_is_scalar(x_780)) {
 x_781 = lean_alloc_ctor(0, 2, 0);
} else {
 x_781 = x_780;
}
lean_ctor_set(x_781, 0, x_762);
lean_ctor_set(x_781, 1, x_776);
x_782 = lean_array_push(x_8, x_781);
x_783 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_783, 0, x_782);
lean_ctor_set(x_783, 1, x_779);
return x_783;
}
}
else
{
lean_object* x_784; lean_object* x_785; 
x_784 = lean_ctor_get(x_761, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_761, 1);
lean_inc(x_785);
lean_dec(x_761);
x_729 = x_784;
x_730 = x_785;
goto block_760;
}
block_760:
{
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_731; uint8_t x_732; 
lean_dec(x_728);
x_731 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_730);
x_732 = !lean_is_exclusive(x_731);
if (x_732 == 0)
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; uint8_t x_736; 
x_733 = lean_ctor_get(x_731, 0);
x_734 = lean_ctor_get(x_731, 1);
x_735 = l_Lean_Elab_Term_SavedState_restore(x_726, x_9, x_10, x_11, x_12, x_13, x_14, x_734);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_736 = !lean_is_exclusive(x_735);
if (x_736 == 0)
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_737 = lean_ctor_get(x_735, 1);
x_738 = lean_ctor_get(x_735, 0);
lean_dec(x_738);
lean_ctor_set_tag(x_735, 1);
lean_ctor_set(x_735, 1, x_733);
lean_ctor_set(x_735, 0, x_729);
x_739 = lean_array_push(x_8, x_735);
lean_ctor_set(x_731, 1, x_737);
lean_ctor_set(x_731, 0, x_739);
return x_731;
}
else
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_740 = lean_ctor_get(x_735, 1);
lean_inc(x_740);
lean_dec(x_735);
x_741 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_741, 0, x_729);
lean_ctor_set(x_741, 1, x_733);
x_742 = lean_array_push(x_8, x_741);
lean_ctor_set(x_731, 1, x_740);
lean_ctor_set(x_731, 0, x_742);
return x_731;
}
}
else
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_743 = lean_ctor_get(x_731, 0);
x_744 = lean_ctor_get(x_731, 1);
lean_inc(x_744);
lean_inc(x_743);
lean_dec(x_731);
x_745 = l_Lean_Elab_Term_SavedState_restore(x_726, x_9, x_10, x_11, x_12, x_13, x_14, x_744);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_746 = lean_ctor_get(x_745, 1);
lean_inc(x_746);
if (lean_is_exclusive(x_745)) {
 lean_ctor_release(x_745, 0);
 lean_ctor_release(x_745, 1);
 x_747 = x_745;
} else {
 lean_dec_ref(x_745);
 x_747 = lean_box(0);
}
if (lean_is_scalar(x_747)) {
 x_748 = lean_alloc_ctor(1, 2, 0);
} else {
 x_748 = x_747;
 lean_ctor_set_tag(x_748, 1);
}
lean_ctor_set(x_748, 0, x_729);
lean_ctor_set(x_748, 1, x_743);
x_749 = lean_array_push(x_8, x_748);
x_750 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_750, 0, x_749);
lean_ctor_set(x_750, 1, x_746);
return x_750;
}
}
else
{
lean_object* x_751; lean_object* x_752; uint8_t x_753; 
lean_dec(x_8);
x_751 = lean_ctor_get(x_729, 0);
lean_inc(x_751);
x_752 = l_Lean_Elab_postponeExceptionId;
x_753 = lean_nat_dec_eq(x_751, x_752);
lean_dec(x_751);
if (x_753 == 0)
{
lean_object* x_754; 
lean_dec(x_726);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_728)) {
 x_754 = lean_alloc_ctor(1, 2, 0);
} else {
 x_754 = x_728;
 lean_ctor_set_tag(x_754, 1);
}
lean_ctor_set(x_754, 0, x_729);
lean_ctor_set(x_754, 1, x_730);
return x_754;
}
else
{
lean_object* x_755; uint8_t x_756; 
lean_dec(x_728);
x_755 = l_Lean_Elab_Term_SavedState_restore(x_726, x_9, x_10, x_11, x_12, x_13, x_14, x_730);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_756 = !lean_is_exclusive(x_755);
if (x_756 == 0)
{
lean_object* x_757; 
x_757 = lean_ctor_get(x_755, 0);
lean_dec(x_757);
lean_ctor_set_tag(x_755, 1);
lean_ctor_set(x_755, 0, x_729);
return x_755;
}
else
{
lean_object* x_758; lean_object* x_759; 
x_758 = lean_ctor_get(x_755, 1);
lean_inc(x_758);
lean_dec(x_755);
x_759 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_759, 0, x_729);
lean_ctor_set(x_759, 1, x_758);
return x_759;
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
lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_789 = lean_unsigned_to_nat(2u);
x_790 = l_Lean_Syntax_getArg(x_1, x_789);
lean_dec(x_1);
x_791 = l_Lean_Syntax_getArgs(x_790);
lean_dec(x_790);
x_792 = l_Array_empty___closed__1;
x_793 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_789, x_791, x_425, x_792);
lean_dec(x_791);
x_794 = l_Lean_Elab_Term_elabExplicitUnivs(x_793, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_793);
if (lean_obj_tag(x_794) == 0)
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_795 = lean_ctor_get(x_794, 0);
lean_inc(x_795);
x_796 = lean_ctor_get(x_794, 1);
lean_inc(x_796);
lean_dec(x_794);
x_797 = l___private_Lean_Elab_App_22__elabAppFnId(x_426, x_795, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_796);
return x_797;
}
else
{
uint8_t x_798; 
lean_dec(x_426);
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
x_798 = !lean_is_exclusive(x_794);
if (x_798 == 0)
{
return x_794;
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_799 = lean_ctor_get(x_794, 0);
x_800 = lean_ctor_get(x_794, 1);
lean_inc(x_800);
lean_inc(x_799);
lean_dec(x_794);
x_801 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_801, 0, x_799);
lean_ctor_set(x_801, 1, x_800);
return x_801;
}
}
}
}
}
}
else
{
lean_object* x_810; lean_object* x_811; 
x_810 = lean_box(0);
x_811 = l___private_Lean_Elab_App_22__elabAppFnId(x_1, x_810, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_811;
}
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; uint8_t x_815; 
x_812 = lean_unsigned_to_nat(0u);
x_813 = l_Lean_Syntax_getArg(x_1, x_812);
x_814 = l_Lean_identKind___closed__2;
x_815 = l_Lean_Syntax_isOfKind(x_813, x_814);
if (x_815 == 0)
{
uint8_t x_816; uint8_t x_817; 
x_816 = l_List_isEmpty___rarg(x_2);
if (x_7 == 0)
{
uint8_t x_1175; 
x_1175 = 1;
x_817 = x_1175;
goto block_1174;
}
else
{
uint8_t x_1176; 
x_1176 = 0;
x_817 = x_1176;
goto block_1174;
}
block_1174:
{
if (x_816 == 0)
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_855; lean_object* x_856; lean_object* x_878; 
x_818 = lean_box(0);
x_819 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_819, 1);
lean_inc(x_821);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 x_822 = x_819;
} else {
 lean_dec_ref(x_819);
 x_822 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_878 = l_Lean_Elab_Term_elabTerm(x_1, x_818, x_817, x_9, x_10, x_11, x_12, x_13, x_14, x_821);
if (lean_obj_tag(x_878) == 0)
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; 
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_881 = l___private_Lean_Elab_App_21__elabAppLVals(x_879, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_880);
if (lean_obj_tag(x_881) == 0)
{
if (x_7 == 0)
{
lean_object* x_882; lean_object* x_883; 
lean_dec(x_822);
lean_dec(x_5);
x_882 = lean_ctor_get(x_881, 0);
lean_inc(x_882);
x_883 = lean_ctor_get(x_881, 1);
lean_inc(x_883);
lean_dec(x_881);
x_855 = x_882;
x_856 = x_883;
goto block_877;
}
else
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; 
x_884 = lean_ctor_get(x_881, 0);
lean_inc(x_884);
x_885 = lean_ctor_get(x_881, 1);
lean_inc(x_885);
lean_dec(x_881);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_886 = l_Lean_Elab_Term_ensureHasType(x_5, x_884, x_9, x_10, x_11, x_12, x_13, x_14, x_885);
if (lean_obj_tag(x_886) == 0)
{
lean_object* x_887; lean_object* x_888; 
lean_dec(x_822);
x_887 = lean_ctor_get(x_886, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_886, 1);
lean_inc(x_888);
lean_dec(x_886);
x_855 = x_887;
x_856 = x_888;
goto block_877;
}
else
{
lean_object* x_889; lean_object* x_890; 
x_889 = lean_ctor_get(x_886, 0);
lean_inc(x_889);
x_890 = lean_ctor_get(x_886, 1);
lean_inc(x_890);
lean_dec(x_886);
x_823 = x_889;
x_824 = x_890;
goto block_854;
}
}
}
else
{
lean_object* x_891; lean_object* x_892; 
lean_dec(x_5);
x_891 = lean_ctor_get(x_881, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_881, 1);
lean_inc(x_892);
lean_dec(x_881);
x_823 = x_891;
x_824 = x_892;
goto block_854;
}
}
else
{
lean_object* x_893; lean_object* x_894; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_893 = lean_ctor_get(x_878, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_878, 1);
lean_inc(x_894);
lean_dec(x_878);
x_823 = x_893;
x_824 = x_894;
goto block_854;
}
block_854:
{
if (lean_obj_tag(x_823) == 0)
{
lean_object* x_825; uint8_t x_826; 
lean_dec(x_822);
x_825 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_824);
x_826 = !lean_is_exclusive(x_825);
if (x_826 == 0)
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; uint8_t x_830; 
x_827 = lean_ctor_get(x_825, 0);
x_828 = lean_ctor_get(x_825, 1);
x_829 = l_Lean_Elab_Term_SavedState_restore(x_820, x_9, x_10, x_11, x_12, x_13, x_14, x_828);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_830 = !lean_is_exclusive(x_829);
if (x_830 == 0)
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_831 = lean_ctor_get(x_829, 1);
x_832 = lean_ctor_get(x_829, 0);
lean_dec(x_832);
lean_ctor_set_tag(x_829, 1);
lean_ctor_set(x_829, 1, x_827);
lean_ctor_set(x_829, 0, x_823);
x_833 = lean_array_push(x_8, x_829);
lean_ctor_set(x_825, 1, x_831);
lean_ctor_set(x_825, 0, x_833);
return x_825;
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; 
x_834 = lean_ctor_get(x_829, 1);
lean_inc(x_834);
lean_dec(x_829);
x_835 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_835, 0, x_823);
lean_ctor_set(x_835, 1, x_827);
x_836 = lean_array_push(x_8, x_835);
lean_ctor_set(x_825, 1, x_834);
lean_ctor_set(x_825, 0, x_836);
return x_825;
}
}
else
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; 
x_837 = lean_ctor_get(x_825, 0);
x_838 = lean_ctor_get(x_825, 1);
lean_inc(x_838);
lean_inc(x_837);
lean_dec(x_825);
x_839 = l_Lean_Elab_Term_SavedState_restore(x_820, x_9, x_10, x_11, x_12, x_13, x_14, x_838);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_840 = lean_ctor_get(x_839, 1);
lean_inc(x_840);
if (lean_is_exclusive(x_839)) {
 lean_ctor_release(x_839, 0);
 lean_ctor_release(x_839, 1);
 x_841 = x_839;
} else {
 lean_dec_ref(x_839);
 x_841 = lean_box(0);
}
if (lean_is_scalar(x_841)) {
 x_842 = lean_alloc_ctor(1, 2, 0);
} else {
 x_842 = x_841;
 lean_ctor_set_tag(x_842, 1);
}
lean_ctor_set(x_842, 0, x_823);
lean_ctor_set(x_842, 1, x_837);
x_843 = lean_array_push(x_8, x_842);
x_844 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_844, 0, x_843);
lean_ctor_set(x_844, 1, x_840);
return x_844;
}
}
else
{
lean_object* x_845; lean_object* x_846; uint8_t x_847; 
lean_dec(x_8);
x_845 = lean_ctor_get(x_823, 0);
lean_inc(x_845);
x_846 = l_Lean_Elab_postponeExceptionId;
x_847 = lean_nat_dec_eq(x_845, x_846);
lean_dec(x_845);
if (x_847 == 0)
{
lean_object* x_848; 
lean_dec(x_820);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_822)) {
 x_848 = lean_alloc_ctor(1, 2, 0);
} else {
 x_848 = x_822;
 lean_ctor_set_tag(x_848, 1);
}
lean_ctor_set(x_848, 0, x_823);
lean_ctor_set(x_848, 1, x_824);
return x_848;
}
else
{
lean_object* x_849; uint8_t x_850; 
lean_dec(x_822);
x_849 = l_Lean_Elab_Term_SavedState_restore(x_820, x_9, x_10, x_11, x_12, x_13, x_14, x_824);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_850 = !lean_is_exclusive(x_849);
if (x_850 == 0)
{
lean_object* x_851; 
x_851 = lean_ctor_get(x_849, 0);
lean_dec(x_851);
lean_ctor_set_tag(x_849, 1);
lean_ctor_set(x_849, 0, x_823);
return x_849;
}
else
{
lean_object* x_852; lean_object* x_853; 
x_852 = lean_ctor_get(x_849, 1);
lean_inc(x_852);
lean_dec(x_849);
x_853 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_853, 0, x_823);
lean_ctor_set(x_853, 1, x_852);
return x_853;
}
}
}
}
block_877:
{
lean_object* x_857; uint8_t x_858; 
x_857 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_856);
x_858 = !lean_is_exclusive(x_857);
if (x_858 == 0)
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; uint8_t x_862; 
x_859 = lean_ctor_get(x_857, 0);
x_860 = lean_ctor_get(x_857, 1);
x_861 = l_Lean_Elab_Term_SavedState_restore(x_820, x_9, x_10, x_11, x_12, x_13, x_14, x_860);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_862 = !lean_is_exclusive(x_861);
if (x_862 == 0)
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; 
x_863 = lean_ctor_get(x_861, 1);
x_864 = lean_ctor_get(x_861, 0);
lean_dec(x_864);
lean_ctor_set(x_861, 1, x_859);
lean_ctor_set(x_861, 0, x_855);
x_865 = lean_array_push(x_8, x_861);
lean_ctor_set(x_857, 1, x_863);
lean_ctor_set(x_857, 0, x_865);
return x_857;
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; 
x_866 = lean_ctor_get(x_861, 1);
lean_inc(x_866);
lean_dec(x_861);
x_867 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_867, 0, x_855);
lean_ctor_set(x_867, 1, x_859);
x_868 = lean_array_push(x_8, x_867);
lean_ctor_set(x_857, 1, x_866);
lean_ctor_set(x_857, 0, x_868);
return x_857;
}
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
x_869 = lean_ctor_get(x_857, 0);
x_870 = lean_ctor_get(x_857, 1);
lean_inc(x_870);
lean_inc(x_869);
lean_dec(x_857);
x_871 = l_Lean_Elab_Term_SavedState_restore(x_820, x_9, x_10, x_11, x_12, x_13, x_14, x_870);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_872 = lean_ctor_get(x_871, 1);
lean_inc(x_872);
if (lean_is_exclusive(x_871)) {
 lean_ctor_release(x_871, 0);
 lean_ctor_release(x_871, 1);
 x_873 = x_871;
} else {
 lean_dec_ref(x_871);
 x_873 = lean_box(0);
}
if (lean_is_scalar(x_873)) {
 x_874 = lean_alloc_ctor(0, 2, 0);
} else {
 x_874 = x_873;
}
lean_ctor_set(x_874, 0, x_855);
lean_ctor_set(x_874, 1, x_869);
x_875 = lean_array_push(x_8, x_874);
x_876 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_876, 0, x_875);
lean_ctor_set(x_876, 1, x_872);
return x_876;
}
}
}
else
{
uint8_t x_895; 
x_895 = l_Array_isEmpty___rarg(x_3);
if (x_895 == 0)
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_933; lean_object* x_934; lean_object* x_956; 
x_896 = lean_box(0);
x_897 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_898 = lean_ctor_get(x_897, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_897, 1);
lean_inc(x_899);
if (lean_is_exclusive(x_897)) {
 lean_ctor_release(x_897, 0);
 lean_ctor_release(x_897, 1);
 x_900 = x_897;
} else {
 lean_dec_ref(x_897);
 x_900 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_956 = l_Lean_Elab_Term_elabTerm(x_1, x_896, x_817, x_9, x_10, x_11, x_12, x_13, x_14, x_899);
if (lean_obj_tag(x_956) == 0)
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; 
x_957 = lean_ctor_get(x_956, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_956, 1);
lean_inc(x_958);
lean_dec(x_956);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_959 = l___private_Lean_Elab_App_21__elabAppLVals(x_957, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_958);
if (lean_obj_tag(x_959) == 0)
{
if (x_7 == 0)
{
lean_object* x_960; lean_object* x_961; 
lean_dec(x_900);
lean_dec(x_5);
x_960 = lean_ctor_get(x_959, 0);
lean_inc(x_960);
x_961 = lean_ctor_get(x_959, 1);
lean_inc(x_961);
lean_dec(x_959);
x_933 = x_960;
x_934 = x_961;
goto block_955;
}
else
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; 
x_962 = lean_ctor_get(x_959, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_959, 1);
lean_inc(x_963);
lean_dec(x_959);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_964 = l_Lean_Elab_Term_ensureHasType(x_5, x_962, x_9, x_10, x_11, x_12, x_13, x_14, x_963);
if (lean_obj_tag(x_964) == 0)
{
lean_object* x_965; lean_object* x_966; 
lean_dec(x_900);
x_965 = lean_ctor_get(x_964, 0);
lean_inc(x_965);
x_966 = lean_ctor_get(x_964, 1);
lean_inc(x_966);
lean_dec(x_964);
x_933 = x_965;
x_934 = x_966;
goto block_955;
}
else
{
lean_object* x_967; lean_object* x_968; 
x_967 = lean_ctor_get(x_964, 0);
lean_inc(x_967);
x_968 = lean_ctor_get(x_964, 1);
lean_inc(x_968);
lean_dec(x_964);
x_901 = x_967;
x_902 = x_968;
goto block_932;
}
}
}
else
{
lean_object* x_969; lean_object* x_970; 
lean_dec(x_5);
x_969 = lean_ctor_get(x_959, 0);
lean_inc(x_969);
x_970 = lean_ctor_get(x_959, 1);
lean_inc(x_970);
lean_dec(x_959);
x_901 = x_969;
x_902 = x_970;
goto block_932;
}
}
else
{
lean_object* x_971; lean_object* x_972; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_971 = lean_ctor_get(x_956, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_956, 1);
lean_inc(x_972);
lean_dec(x_956);
x_901 = x_971;
x_902 = x_972;
goto block_932;
}
block_932:
{
if (lean_obj_tag(x_901) == 0)
{
lean_object* x_903; uint8_t x_904; 
lean_dec(x_900);
x_903 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_902);
x_904 = !lean_is_exclusive(x_903);
if (x_904 == 0)
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; uint8_t x_908; 
x_905 = lean_ctor_get(x_903, 0);
x_906 = lean_ctor_get(x_903, 1);
x_907 = l_Lean_Elab_Term_SavedState_restore(x_898, x_9, x_10, x_11, x_12, x_13, x_14, x_906);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_908 = !lean_is_exclusive(x_907);
if (x_908 == 0)
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; 
x_909 = lean_ctor_get(x_907, 1);
x_910 = lean_ctor_get(x_907, 0);
lean_dec(x_910);
lean_ctor_set_tag(x_907, 1);
lean_ctor_set(x_907, 1, x_905);
lean_ctor_set(x_907, 0, x_901);
x_911 = lean_array_push(x_8, x_907);
lean_ctor_set(x_903, 1, x_909);
lean_ctor_set(x_903, 0, x_911);
return x_903;
}
else
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; 
x_912 = lean_ctor_get(x_907, 1);
lean_inc(x_912);
lean_dec(x_907);
x_913 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_913, 0, x_901);
lean_ctor_set(x_913, 1, x_905);
x_914 = lean_array_push(x_8, x_913);
lean_ctor_set(x_903, 1, x_912);
lean_ctor_set(x_903, 0, x_914);
return x_903;
}
}
else
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_915 = lean_ctor_get(x_903, 0);
x_916 = lean_ctor_get(x_903, 1);
lean_inc(x_916);
lean_inc(x_915);
lean_dec(x_903);
x_917 = l_Lean_Elab_Term_SavedState_restore(x_898, x_9, x_10, x_11, x_12, x_13, x_14, x_916);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_918 = lean_ctor_get(x_917, 1);
lean_inc(x_918);
if (lean_is_exclusive(x_917)) {
 lean_ctor_release(x_917, 0);
 lean_ctor_release(x_917, 1);
 x_919 = x_917;
} else {
 lean_dec_ref(x_917);
 x_919 = lean_box(0);
}
if (lean_is_scalar(x_919)) {
 x_920 = lean_alloc_ctor(1, 2, 0);
} else {
 x_920 = x_919;
 lean_ctor_set_tag(x_920, 1);
}
lean_ctor_set(x_920, 0, x_901);
lean_ctor_set(x_920, 1, x_915);
x_921 = lean_array_push(x_8, x_920);
x_922 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_922, 0, x_921);
lean_ctor_set(x_922, 1, x_918);
return x_922;
}
}
else
{
lean_object* x_923; lean_object* x_924; uint8_t x_925; 
lean_dec(x_8);
x_923 = lean_ctor_get(x_901, 0);
lean_inc(x_923);
x_924 = l_Lean_Elab_postponeExceptionId;
x_925 = lean_nat_dec_eq(x_923, x_924);
lean_dec(x_923);
if (x_925 == 0)
{
lean_object* x_926; 
lean_dec(x_898);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_900)) {
 x_926 = lean_alloc_ctor(1, 2, 0);
} else {
 x_926 = x_900;
 lean_ctor_set_tag(x_926, 1);
}
lean_ctor_set(x_926, 0, x_901);
lean_ctor_set(x_926, 1, x_902);
return x_926;
}
else
{
lean_object* x_927; uint8_t x_928; 
lean_dec(x_900);
x_927 = l_Lean_Elab_Term_SavedState_restore(x_898, x_9, x_10, x_11, x_12, x_13, x_14, x_902);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_928 = !lean_is_exclusive(x_927);
if (x_928 == 0)
{
lean_object* x_929; 
x_929 = lean_ctor_get(x_927, 0);
lean_dec(x_929);
lean_ctor_set_tag(x_927, 1);
lean_ctor_set(x_927, 0, x_901);
return x_927;
}
else
{
lean_object* x_930; lean_object* x_931; 
x_930 = lean_ctor_get(x_927, 1);
lean_inc(x_930);
lean_dec(x_927);
x_931 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_931, 0, x_901);
lean_ctor_set(x_931, 1, x_930);
return x_931;
}
}
}
}
block_955:
{
lean_object* x_935; uint8_t x_936; 
x_935 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_934);
x_936 = !lean_is_exclusive(x_935);
if (x_936 == 0)
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; uint8_t x_940; 
x_937 = lean_ctor_get(x_935, 0);
x_938 = lean_ctor_get(x_935, 1);
x_939 = l_Lean_Elab_Term_SavedState_restore(x_898, x_9, x_10, x_11, x_12, x_13, x_14, x_938);
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
x_949 = l_Lean_Elab_Term_SavedState_restore(x_898, x_9, x_10, x_11, x_12, x_13, x_14, x_948);
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
}
else
{
uint8_t x_973; 
x_973 = l_Array_isEmpty___rarg(x_4);
if (x_973 == 0)
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_1011; lean_object* x_1012; lean_object* x_1034; 
x_974 = lean_box(0);
x_975 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_976 = lean_ctor_get(x_975, 0);
lean_inc(x_976);
x_977 = lean_ctor_get(x_975, 1);
lean_inc(x_977);
if (lean_is_exclusive(x_975)) {
 lean_ctor_release(x_975, 0);
 lean_ctor_release(x_975, 1);
 x_978 = x_975;
} else {
 lean_dec_ref(x_975);
 x_978 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1034 = l_Lean_Elab_Term_elabTerm(x_1, x_974, x_817, x_9, x_10, x_11, x_12, x_13, x_14, x_977);
if (lean_obj_tag(x_1034) == 0)
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; 
x_1035 = lean_ctor_get(x_1034, 0);
lean_inc(x_1035);
x_1036 = lean_ctor_get(x_1034, 1);
lean_inc(x_1036);
lean_dec(x_1034);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_1037 = l___private_Lean_Elab_App_21__elabAppLVals(x_1035, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_1036);
if (lean_obj_tag(x_1037) == 0)
{
if (x_7 == 0)
{
lean_object* x_1038; lean_object* x_1039; 
lean_dec(x_978);
lean_dec(x_5);
x_1038 = lean_ctor_get(x_1037, 0);
lean_inc(x_1038);
x_1039 = lean_ctor_get(x_1037, 1);
lean_inc(x_1039);
lean_dec(x_1037);
x_1011 = x_1038;
x_1012 = x_1039;
goto block_1033;
}
else
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
x_1040 = lean_ctor_get(x_1037, 0);
lean_inc(x_1040);
x_1041 = lean_ctor_get(x_1037, 1);
lean_inc(x_1041);
lean_dec(x_1037);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_1042 = l_Lean_Elab_Term_ensureHasType(x_5, x_1040, x_9, x_10, x_11, x_12, x_13, x_14, x_1041);
if (lean_obj_tag(x_1042) == 0)
{
lean_object* x_1043; lean_object* x_1044; 
lean_dec(x_978);
x_1043 = lean_ctor_get(x_1042, 0);
lean_inc(x_1043);
x_1044 = lean_ctor_get(x_1042, 1);
lean_inc(x_1044);
lean_dec(x_1042);
x_1011 = x_1043;
x_1012 = x_1044;
goto block_1033;
}
else
{
lean_object* x_1045; lean_object* x_1046; 
x_1045 = lean_ctor_get(x_1042, 0);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_1042, 1);
lean_inc(x_1046);
lean_dec(x_1042);
x_979 = x_1045;
x_980 = x_1046;
goto block_1010;
}
}
}
else
{
lean_object* x_1047; lean_object* x_1048; 
lean_dec(x_5);
x_1047 = lean_ctor_get(x_1037, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1037, 1);
lean_inc(x_1048);
lean_dec(x_1037);
x_979 = x_1047;
x_980 = x_1048;
goto block_1010;
}
}
else
{
lean_object* x_1049; lean_object* x_1050; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1049 = lean_ctor_get(x_1034, 0);
lean_inc(x_1049);
x_1050 = lean_ctor_get(x_1034, 1);
lean_inc(x_1050);
lean_dec(x_1034);
x_979 = x_1049;
x_980 = x_1050;
goto block_1010;
}
block_1010:
{
if (lean_obj_tag(x_979) == 0)
{
lean_object* x_981; uint8_t x_982; 
lean_dec(x_978);
x_981 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_980);
x_982 = !lean_is_exclusive(x_981);
if (x_982 == 0)
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; uint8_t x_986; 
x_983 = lean_ctor_get(x_981, 0);
x_984 = lean_ctor_get(x_981, 1);
x_985 = l_Lean_Elab_Term_SavedState_restore(x_976, x_9, x_10, x_11, x_12, x_13, x_14, x_984);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_986 = !lean_is_exclusive(x_985);
if (x_986 == 0)
{
lean_object* x_987; lean_object* x_988; lean_object* x_989; 
x_987 = lean_ctor_get(x_985, 1);
x_988 = lean_ctor_get(x_985, 0);
lean_dec(x_988);
lean_ctor_set_tag(x_985, 1);
lean_ctor_set(x_985, 1, x_983);
lean_ctor_set(x_985, 0, x_979);
x_989 = lean_array_push(x_8, x_985);
lean_ctor_set(x_981, 1, x_987);
lean_ctor_set(x_981, 0, x_989);
return x_981;
}
else
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; 
x_990 = lean_ctor_get(x_985, 1);
lean_inc(x_990);
lean_dec(x_985);
x_991 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_991, 0, x_979);
lean_ctor_set(x_991, 1, x_983);
x_992 = lean_array_push(x_8, x_991);
lean_ctor_set(x_981, 1, x_990);
lean_ctor_set(x_981, 0, x_992);
return x_981;
}
}
else
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; 
x_993 = lean_ctor_get(x_981, 0);
x_994 = lean_ctor_get(x_981, 1);
lean_inc(x_994);
lean_inc(x_993);
lean_dec(x_981);
x_995 = l_Lean_Elab_Term_SavedState_restore(x_976, x_9, x_10, x_11, x_12, x_13, x_14, x_994);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_996 = lean_ctor_get(x_995, 1);
lean_inc(x_996);
if (lean_is_exclusive(x_995)) {
 lean_ctor_release(x_995, 0);
 lean_ctor_release(x_995, 1);
 x_997 = x_995;
} else {
 lean_dec_ref(x_995);
 x_997 = lean_box(0);
}
if (lean_is_scalar(x_997)) {
 x_998 = lean_alloc_ctor(1, 2, 0);
} else {
 x_998 = x_997;
 lean_ctor_set_tag(x_998, 1);
}
lean_ctor_set(x_998, 0, x_979);
lean_ctor_set(x_998, 1, x_993);
x_999 = lean_array_push(x_8, x_998);
x_1000 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1000, 0, x_999);
lean_ctor_set(x_1000, 1, x_996);
return x_1000;
}
}
else
{
lean_object* x_1001; lean_object* x_1002; uint8_t x_1003; 
lean_dec(x_8);
x_1001 = lean_ctor_get(x_979, 0);
lean_inc(x_1001);
x_1002 = l_Lean_Elab_postponeExceptionId;
x_1003 = lean_nat_dec_eq(x_1001, x_1002);
lean_dec(x_1001);
if (x_1003 == 0)
{
lean_object* x_1004; 
lean_dec(x_976);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_978)) {
 x_1004 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1004 = x_978;
 lean_ctor_set_tag(x_1004, 1);
}
lean_ctor_set(x_1004, 0, x_979);
lean_ctor_set(x_1004, 1, x_980);
return x_1004;
}
else
{
lean_object* x_1005; uint8_t x_1006; 
lean_dec(x_978);
x_1005 = l_Lean_Elab_Term_SavedState_restore(x_976, x_9, x_10, x_11, x_12, x_13, x_14, x_980);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1006 = !lean_is_exclusive(x_1005);
if (x_1006 == 0)
{
lean_object* x_1007; 
x_1007 = lean_ctor_get(x_1005, 0);
lean_dec(x_1007);
lean_ctor_set_tag(x_1005, 1);
lean_ctor_set(x_1005, 0, x_979);
return x_1005;
}
else
{
lean_object* x_1008; lean_object* x_1009; 
x_1008 = lean_ctor_get(x_1005, 1);
lean_inc(x_1008);
lean_dec(x_1005);
x_1009 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1009, 0, x_979);
lean_ctor_set(x_1009, 1, x_1008);
return x_1009;
}
}
}
}
block_1033:
{
lean_object* x_1013; uint8_t x_1014; 
x_1013 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1012);
x_1014 = !lean_is_exclusive(x_1013);
if (x_1014 == 0)
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; uint8_t x_1018; 
x_1015 = lean_ctor_get(x_1013, 0);
x_1016 = lean_ctor_get(x_1013, 1);
x_1017 = l_Lean_Elab_Term_SavedState_restore(x_976, x_9, x_10, x_11, x_12, x_13, x_14, x_1016);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1018 = !lean_is_exclusive(x_1017);
if (x_1018 == 0)
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
x_1019 = lean_ctor_get(x_1017, 1);
x_1020 = lean_ctor_get(x_1017, 0);
lean_dec(x_1020);
lean_ctor_set(x_1017, 1, x_1015);
lean_ctor_set(x_1017, 0, x_1011);
x_1021 = lean_array_push(x_8, x_1017);
lean_ctor_set(x_1013, 1, x_1019);
lean_ctor_set(x_1013, 0, x_1021);
return x_1013;
}
else
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; 
x_1022 = lean_ctor_get(x_1017, 1);
lean_inc(x_1022);
lean_dec(x_1017);
x_1023 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1023, 0, x_1011);
lean_ctor_set(x_1023, 1, x_1015);
x_1024 = lean_array_push(x_8, x_1023);
lean_ctor_set(x_1013, 1, x_1022);
lean_ctor_set(x_1013, 0, x_1024);
return x_1013;
}
}
else
{
lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1025 = lean_ctor_get(x_1013, 0);
x_1026 = lean_ctor_get(x_1013, 1);
lean_inc(x_1026);
lean_inc(x_1025);
lean_dec(x_1013);
x_1027 = l_Lean_Elab_Term_SavedState_restore(x_976, x_9, x_10, x_11, x_12, x_13, x_14, x_1026);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1028 = lean_ctor_get(x_1027, 1);
lean_inc(x_1028);
if (lean_is_exclusive(x_1027)) {
 lean_ctor_release(x_1027, 0);
 lean_ctor_release(x_1027, 1);
 x_1029 = x_1027;
} else {
 lean_dec_ref(x_1027);
 x_1029 = lean_box(0);
}
if (lean_is_scalar(x_1029)) {
 x_1030 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1030 = x_1029;
}
lean_ctor_set(x_1030, 0, x_1011);
lean_ctor_set(x_1030, 1, x_1025);
x_1031 = lean_array_push(x_8, x_1030);
x_1032 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1032, 0, x_1031);
lean_ctor_set(x_1032, 1, x_1028);
return x_1032;
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
lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; uint8_t x_1087; lean_object* x_1088; 
x_1051 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1052 = lean_ctor_get(x_1051, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1051, 1);
lean_inc(x_1053);
if (lean_is_exclusive(x_1051)) {
 lean_ctor_release(x_1051, 0);
 lean_ctor_release(x_1051, 1);
 x_1054 = x_1051;
} else {
 lean_dec_ref(x_1051);
 x_1054 = lean_box(0);
}
x_1087 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1088 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_1087, x_9, x_10, x_11, x_12, x_13, x_14, x_1053);
if (lean_obj_tag(x_1088) == 0)
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; uint8_t x_1092; 
lean_dec(x_1054);
x_1089 = lean_ctor_get(x_1088, 0);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_1088, 1);
lean_inc(x_1090);
lean_dec(x_1088);
x_1091 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1090);
x_1092 = !lean_is_exclusive(x_1091);
if (x_1092 == 0)
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; uint8_t x_1096; 
x_1093 = lean_ctor_get(x_1091, 0);
x_1094 = lean_ctor_get(x_1091, 1);
x_1095 = l_Lean_Elab_Term_SavedState_restore(x_1052, x_9, x_10, x_11, x_12, x_13, x_14, x_1094);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1096 = !lean_is_exclusive(x_1095);
if (x_1096 == 0)
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; 
x_1097 = lean_ctor_get(x_1095, 1);
x_1098 = lean_ctor_get(x_1095, 0);
lean_dec(x_1098);
lean_ctor_set(x_1095, 1, x_1093);
lean_ctor_set(x_1095, 0, x_1089);
x_1099 = lean_array_push(x_8, x_1095);
lean_ctor_set(x_1091, 1, x_1097);
lean_ctor_set(x_1091, 0, x_1099);
return x_1091;
}
else
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; 
x_1100 = lean_ctor_get(x_1095, 1);
lean_inc(x_1100);
lean_dec(x_1095);
x_1101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1101, 0, x_1089);
lean_ctor_set(x_1101, 1, x_1093);
x_1102 = lean_array_push(x_8, x_1101);
lean_ctor_set(x_1091, 1, x_1100);
lean_ctor_set(x_1091, 0, x_1102);
return x_1091;
}
}
else
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; 
x_1103 = lean_ctor_get(x_1091, 0);
x_1104 = lean_ctor_get(x_1091, 1);
lean_inc(x_1104);
lean_inc(x_1103);
lean_dec(x_1091);
x_1105 = l_Lean_Elab_Term_SavedState_restore(x_1052, x_9, x_10, x_11, x_12, x_13, x_14, x_1104);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1106 = lean_ctor_get(x_1105, 1);
lean_inc(x_1106);
if (lean_is_exclusive(x_1105)) {
 lean_ctor_release(x_1105, 0);
 lean_ctor_release(x_1105, 1);
 x_1107 = x_1105;
} else {
 lean_dec_ref(x_1105);
 x_1107 = lean_box(0);
}
if (lean_is_scalar(x_1107)) {
 x_1108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1108 = x_1107;
}
lean_ctor_set(x_1108, 0, x_1089);
lean_ctor_set(x_1108, 1, x_1103);
x_1109 = lean_array_push(x_8, x_1108);
x_1110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1110, 0, x_1109);
lean_ctor_set(x_1110, 1, x_1106);
return x_1110;
}
}
else
{
lean_object* x_1111; lean_object* x_1112; 
x_1111 = lean_ctor_get(x_1088, 0);
lean_inc(x_1111);
x_1112 = lean_ctor_get(x_1088, 1);
lean_inc(x_1112);
lean_dec(x_1088);
x_1055 = x_1111;
x_1056 = x_1112;
goto block_1086;
}
block_1086:
{
if (lean_obj_tag(x_1055) == 0)
{
lean_object* x_1057; uint8_t x_1058; 
lean_dec(x_1054);
x_1057 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1056);
x_1058 = !lean_is_exclusive(x_1057);
if (x_1058 == 0)
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; uint8_t x_1062; 
x_1059 = lean_ctor_get(x_1057, 0);
x_1060 = lean_ctor_get(x_1057, 1);
x_1061 = l_Lean_Elab_Term_SavedState_restore(x_1052, x_9, x_10, x_11, x_12, x_13, x_14, x_1060);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1062 = !lean_is_exclusive(x_1061);
if (x_1062 == 0)
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
x_1063 = lean_ctor_get(x_1061, 1);
x_1064 = lean_ctor_get(x_1061, 0);
lean_dec(x_1064);
lean_ctor_set_tag(x_1061, 1);
lean_ctor_set(x_1061, 1, x_1059);
lean_ctor_set(x_1061, 0, x_1055);
x_1065 = lean_array_push(x_8, x_1061);
lean_ctor_set(x_1057, 1, x_1063);
lean_ctor_set(x_1057, 0, x_1065);
return x_1057;
}
else
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; 
x_1066 = lean_ctor_get(x_1061, 1);
lean_inc(x_1066);
lean_dec(x_1061);
x_1067 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1067, 0, x_1055);
lean_ctor_set(x_1067, 1, x_1059);
x_1068 = lean_array_push(x_8, x_1067);
lean_ctor_set(x_1057, 1, x_1066);
lean_ctor_set(x_1057, 0, x_1068);
return x_1057;
}
}
else
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
x_1069 = lean_ctor_get(x_1057, 0);
x_1070 = lean_ctor_get(x_1057, 1);
lean_inc(x_1070);
lean_inc(x_1069);
lean_dec(x_1057);
x_1071 = l_Lean_Elab_Term_SavedState_restore(x_1052, x_9, x_10, x_11, x_12, x_13, x_14, x_1070);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1072 = lean_ctor_get(x_1071, 1);
lean_inc(x_1072);
if (lean_is_exclusive(x_1071)) {
 lean_ctor_release(x_1071, 0);
 lean_ctor_release(x_1071, 1);
 x_1073 = x_1071;
} else {
 lean_dec_ref(x_1071);
 x_1073 = lean_box(0);
}
if (lean_is_scalar(x_1073)) {
 x_1074 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1074 = x_1073;
 lean_ctor_set_tag(x_1074, 1);
}
lean_ctor_set(x_1074, 0, x_1055);
lean_ctor_set(x_1074, 1, x_1069);
x_1075 = lean_array_push(x_8, x_1074);
x_1076 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1076, 0, x_1075);
lean_ctor_set(x_1076, 1, x_1072);
return x_1076;
}
}
else
{
lean_object* x_1077; lean_object* x_1078; uint8_t x_1079; 
lean_dec(x_8);
x_1077 = lean_ctor_get(x_1055, 0);
lean_inc(x_1077);
x_1078 = l_Lean_Elab_postponeExceptionId;
x_1079 = lean_nat_dec_eq(x_1077, x_1078);
lean_dec(x_1077);
if (x_1079 == 0)
{
lean_object* x_1080; 
lean_dec(x_1052);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1054)) {
 x_1080 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1080 = x_1054;
 lean_ctor_set_tag(x_1080, 1);
}
lean_ctor_set(x_1080, 0, x_1055);
lean_ctor_set(x_1080, 1, x_1056);
return x_1080;
}
else
{
lean_object* x_1081; uint8_t x_1082; 
lean_dec(x_1054);
x_1081 = l_Lean_Elab_Term_SavedState_restore(x_1052, x_9, x_10, x_11, x_12, x_13, x_14, x_1056);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1082 = !lean_is_exclusive(x_1081);
if (x_1082 == 0)
{
lean_object* x_1083; 
x_1083 = lean_ctor_get(x_1081, 0);
lean_dec(x_1083);
lean_ctor_set_tag(x_1081, 1);
lean_ctor_set(x_1081, 0, x_1055);
return x_1081;
}
else
{
lean_object* x_1084; lean_object* x_1085; 
x_1084 = lean_ctor_get(x_1081, 1);
lean_inc(x_1084);
lean_dec(x_1081);
x_1085 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1085, 0, x_1055);
lean_ctor_set(x_1085, 1, x_1084);
return x_1085;
}
}
}
}
}
else
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1149; 
x_1113 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1114 = lean_ctor_get(x_1113, 0);
lean_inc(x_1114);
x_1115 = lean_ctor_get(x_1113, 1);
lean_inc(x_1115);
if (lean_is_exclusive(x_1113)) {
 lean_ctor_release(x_1113, 0);
 lean_ctor_release(x_1113, 1);
 x_1116 = x_1113;
} else {
 lean_dec_ref(x_1113);
 x_1116 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1149 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_817, x_9, x_10, x_11, x_12, x_13, x_14, x_1115);
if (lean_obj_tag(x_1149) == 0)
{
lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; uint8_t x_1153; 
lean_dec(x_1116);
x_1150 = lean_ctor_get(x_1149, 0);
lean_inc(x_1150);
x_1151 = lean_ctor_get(x_1149, 1);
lean_inc(x_1151);
lean_dec(x_1149);
x_1152 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1151);
x_1153 = !lean_is_exclusive(x_1152);
if (x_1153 == 0)
{
lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; uint8_t x_1157; 
x_1154 = lean_ctor_get(x_1152, 0);
x_1155 = lean_ctor_get(x_1152, 1);
x_1156 = l_Lean_Elab_Term_SavedState_restore(x_1114, x_9, x_10, x_11, x_12, x_13, x_14, x_1155);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1157 = !lean_is_exclusive(x_1156);
if (x_1157 == 0)
{
lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; 
x_1158 = lean_ctor_get(x_1156, 1);
x_1159 = lean_ctor_get(x_1156, 0);
lean_dec(x_1159);
lean_ctor_set(x_1156, 1, x_1154);
lean_ctor_set(x_1156, 0, x_1150);
x_1160 = lean_array_push(x_8, x_1156);
lean_ctor_set(x_1152, 1, x_1158);
lean_ctor_set(x_1152, 0, x_1160);
return x_1152;
}
else
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; 
x_1161 = lean_ctor_get(x_1156, 1);
lean_inc(x_1161);
lean_dec(x_1156);
x_1162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1162, 0, x_1150);
lean_ctor_set(x_1162, 1, x_1154);
x_1163 = lean_array_push(x_8, x_1162);
lean_ctor_set(x_1152, 1, x_1161);
lean_ctor_set(x_1152, 0, x_1163);
return x_1152;
}
}
else
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; 
x_1164 = lean_ctor_get(x_1152, 0);
x_1165 = lean_ctor_get(x_1152, 1);
lean_inc(x_1165);
lean_inc(x_1164);
lean_dec(x_1152);
x_1166 = l_Lean_Elab_Term_SavedState_restore(x_1114, x_9, x_10, x_11, x_12, x_13, x_14, x_1165);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1167 = lean_ctor_get(x_1166, 1);
lean_inc(x_1167);
if (lean_is_exclusive(x_1166)) {
 lean_ctor_release(x_1166, 0);
 lean_ctor_release(x_1166, 1);
 x_1168 = x_1166;
} else {
 lean_dec_ref(x_1166);
 x_1168 = lean_box(0);
}
if (lean_is_scalar(x_1168)) {
 x_1169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1169 = x_1168;
}
lean_ctor_set(x_1169, 0, x_1150);
lean_ctor_set(x_1169, 1, x_1164);
x_1170 = lean_array_push(x_8, x_1169);
x_1171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1171, 0, x_1170);
lean_ctor_set(x_1171, 1, x_1167);
return x_1171;
}
}
else
{
lean_object* x_1172; lean_object* x_1173; 
x_1172 = lean_ctor_get(x_1149, 0);
lean_inc(x_1172);
x_1173 = lean_ctor_get(x_1149, 1);
lean_inc(x_1173);
lean_dec(x_1149);
x_1117 = x_1172;
x_1118 = x_1173;
goto block_1148;
}
block_1148:
{
if (lean_obj_tag(x_1117) == 0)
{
lean_object* x_1119; uint8_t x_1120; 
lean_dec(x_1116);
x_1119 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1118);
x_1120 = !lean_is_exclusive(x_1119);
if (x_1120 == 0)
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; uint8_t x_1124; 
x_1121 = lean_ctor_get(x_1119, 0);
x_1122 = lean_ctor_get(x_1119, 1);
x_1123 = l_Lean_Elab_Term_SavedState_restore(x_1114, x_9, x_10, x_11, x_12, x_13, x_14, x_1122);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1124 = !lean_is_exclusive(x_1123);
if (x_1124 == 0)
{
lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; 
x_1125 = lean_ctor_get(x_1123, 1);
x_1126 = lean_ctor_get(x_1123, 0);
lean_dec(x_1126);
lean_ctor_set_tag(x_1123, 1);
lean_ctor_set(x_1123, 1, x_1121);
lean_ctor_set(x_1123, 0, x_1117);
x_1127 = lean_array_push(x_8, x_1123);
lean_ctor_set(x_1119, 1, x_1125);
lean_ctor_set(x_1119, 0, x_1127);
return x_1119;
}
else
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; 
x_1128 = lean_ctor_get(x_1123, 1);
lean_inc(x_1128);
lean_dec(x_1123);
x_1129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1129, 0, x_1117);
lean_ctor_set(x_1129, 1, x_1121);
x_1130 = lean_array_push(x_8, x_1129);
lean_ctor_set(x_1119, 1, x_1128);
lean_ctor_set(x_1119, 0, x_1130);
return x_1119;
}
}
else
{
lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; 
x_1131 = lean_ctor_get(x_1119, 0);
x_1132 = lean_ctor_get(x_1119, 1);
lean_inc(x_1132);
lean_inc(x_1131);
lean_dec(x_1119);
x_1133 = l_Lean_Elab_Term_SavedState_restore(x_1114, x_9, x_10, x_11, x_12, x_13, x_14, x_1132);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1134 = lean_ctor_get(x_1133, 1);
lean_inc(x_1134);
if (lean_is_exclusive(x_1133)) {
 lean_ctor_release(x_1133, 0);
 lean_ctor_release(x_1133, 1);
 x_1135 = x_1133;
} else {
 lean_dec_ref(x_1133);
 x_1135 = lean_box(0);
}
if (lean_is_scalar(x_1135)) {
 x_1136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1136 = x_1135;
 lean_ctor_set_tag(x_1136, 1);
}
lean_ctor_set(x_1136, 0, x_1117);
lean_ctor_set(x_1136, 1, x_1131);
x_1137 = lean_array_push(x_8, x_1136);
x_1138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1138, 0, x_1137);
lean_ctor_set(x_1138, 1, x_1134);
return x_1138;
}
}
else
{
lean_object* x_1139; lean_object* x_1140; uint8_t x_1141; 
lean_dec(x_8);
x_1139 = lean_ctor_get(x_1117, 0);
lean_inc(x_1139);
x_1140 = l_Lean_Elab_postponeExceptionId;
x_1141 = lean_nat_dec_eq(x_1139, x_1140);
lean_dec(x_1139);
if (x_1141 == 0)
{
lean_object* x_1142; 
lean_dec(x_1114);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1116)) {
 x_1142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1142 = x_1116;
 lean_ctor_set_tag(x_1142, 1);
}
lean_ctor_set(x_1142, 0, x_1117);
lean_ctor_set(x_1142, 1, x_1118);
return x_1142;
}
else
{
lean_object* x_1143; uint8_t x_1144; 
lean_dec(x_1116);
x_1143 = l_Lean_Elab_Term_SavedState_restore(x_1114, x_9, x_10, x_11, x_12, x_13, x_14, x_1118);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1144 = !lean_is_exclusive(x_1143);
if (x_1144 == 0)
{
lean_object* x_1145; 
x_1145 = lean_ctor_get(x_1143, 0);
lean_dec(x_1145);
lean_ctor_set_tag(x_1143, 1);
lean_ctor_set(x_1143, 0, x_1117);
return x_1143;
}
else
{
lean_object* x_1146; lean_object* x_1147; 
x_1146 = lean_ctor_get(x_1143, 1);
lean_inc(x_1146);
lean_dec(x_1143);
x_1147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1147, 0, x_1117);
lean_ctor_set(x_1147, 1, x_1146);
return x_1147;
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
lean_object* x_1177; lean_object* x_1178; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1177 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__8;
x_1178 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_1177, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_1178;
}
}
}
block_1593:
{
if (x_1180 == 0)
{
lean_object* x_1181; uint8_t x_1182; 
x_1181 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__10;
lean_inc(x_1);
x_1182 = l_Lean_Syntax_isOfKind(x_1, x_1181);
if (x_1182 == 0)
{
lean_object* x_1183; uint8_t x_1184; 
x_1183 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__12;
lean_inc(x_1);
x_1184 = l_Lean_Syntax_isOfKind(x_1, x_1183);
if (x_1184 == 0)
{
uint8_t x_1185; 
x_1185 = 0;
x_384 = x_1185;
goto block_1179;
}
else
{
lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; uint8_t x_1189; 
x_1186 = l_Lean_Syntax_getArgs(x_1);
x_1187 = lean_array_get_size(x_1186);
lean_dec(x_1186);
x_1188 = lean_unsigned_to_nat(3u);
x_1189 = lean_nat_dec_eq(x_1187, x_1188);
lean_dec(x_1187);
x_384 = x_1189;
goto block_1179;
}
}
else
{
lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; uint8_t x_1193; 
x_1190 = l_Lean_Syntax_getArgs(x_1);
x_1191 = lean_array_get_size(x_1190);
lean_dec(x_1190);
x_1192 = lean_unsigned_to_nat(4u);
x_1193 = lean_nat_dec_eq(x_1191, x_1192);
if (x_1193 == 0)
{
lean_object* x_1194; uint8_t x_1195; 
x_1194 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__12;
lean_inc(x_1);
x_1195 = l_Lean_Syntax_isOfKind(x_1, x_1194);
if (x_1195 == 0)
{
uint8_t x_1196; 
lean_dec(x_1191);
x_1196 = 0;
x_384 = x_1196;
goto block_1179;
}
else
{
lean_object* x_1197; uint8_t x_1198; 
x_1197 = lean_unsigned_to_nat(3u);
x_1198 = lean_nat_dec_eq(x_1191, x_1197);
lean_dec(x_1191);
x_384 = x_1198;
goto block_1179;
}
}
else
{
lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; 
lean_dec(x_1191);
x_1199 = lean_unsigned_to_nat(0u);
x_1200 = l_Lean_Syntax_getArg(x_1, x_1199);
x_1201 = lean_unsigned_to_nat(2u);
x_1202 = l_Lean_Syntax_getArg(x_1, x_1201);
lean_dec(x_1);
x_1203 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1203, 0, x_1202);
x_1204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1204, 0, x_1203);
lean_ctor_set(x_1204, 1, x_2);
x_1 = x_1200;
x_2 = x_1204;
goto _start;
}
}
}
else
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; uint8_t x_1211; 
x_1206 = lean_unsigned_to_nat(0u);
x_1207 = l_Lean_Syntax_getArg(x_1, x_1206);
x_1208 = lean_unsigned_to_nat(2u);
x_1209 = l_Lean_Syntax_getArg(x_1, x_1208);
x_1210 = l_Lean_fieldIdxKind___closed__2;
lean_inc(x_1209);
x_1211 = l_Lean_Syntax_isOfKind(x_1209, x_1210);
if (x_1211 == 0)
{
lean_object* x_1212; uint8_t x_1213; 
x_1212 = l_Lean_identKind___closed__2;
lean_inc(x_1209);
x_1213 = l_Lean_Syntax_isOfKind(x_1209, x_1212);
if (x_1213 == 0)
{
uint8_t x_1214; uint8_t x_1215; 
lean_dec(x_1209);
lean_dec(x_1207);
x_1214 = l_List_isEmpty___rarg(x_2);
if (x_7 == 0)
{
uint8_t x_1573; 
x_1573 = 1;
x_1215 = x_1573;
goto block_1572;
}
else
{
uint8_t x_1574; 
x_1574 = 0;
x_1215 = x_1574;
goto block_1572;
}
block_1572:
{
if (x_1214 == 0)
{
lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; lean_object* x_1253; lean_object* x_1254; lean_object* x_1276; 
x_1216 = lean_box(0);
x_1217 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1218 = lean_ctor_get(x_1217, 0);
lean_inc(x_1218);
x_1219 = lean_ctor_get(x_1217, 1);
lean_inc(x_1219);
if (lean_is_exclusive(x_1217)) {
 lean_ctor_release(x_1217, 0);
 lean_ctor_release(x_1217, 1);
 x_1220 = x_1217;
} else {
 lean_dec_ref(x_1217);
 x_1220 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1276 = l_Lean_Elab_Term_elabTerm(x_1, x_1216, x_1215, x_9, x_10, x_11, x_12, x_13, x_14, x_1219);
if (lean_obj_tag(x_1276) == 0)
{
lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; 
x_1277 = lean_ctor_get(x_1276, 0);
lean_inc(x_1277);
x_1278 = lean_ctor_get(x_1276, 1);
lean_inc(x_1278);
lean_dec(x_1276);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_1279 = l___private_Lean_Elab_App_21__elabAppLVals(x_1277, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_1278);
if (lean_obj_tag(x_1279) == 0)
{
if (x_7 == 0)
{
lean_object* x_1280; lean_object* x_1281; 
lean_dec(x_1220);
lean_dec(x_5);
x_1280 = lean_ctor_get(x_1279, 0);
lean_inc(x_1280);
x_1281 = lean_ctor_get(x_1279, 1);
lean_inc(x_1281);
lean_dec(x_1279);
x_1253 = x_1280;
x_1254 = x_1281;
goto block_1275;
}
else
{
lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; 
x_1282 = lean_ctor_get(x_1279, 0);
lean_inc(x_1282);
x_1283 = lean_ctor_get(x_1279, 1);
lean_inc(x_1283);
lean_dec(x_1279);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_1284 = l_Lean_Elab_Term_ensureHasType(x_5, x_1282, x_9, x_10, x_11, x_12, x_13, x_14, x_1283);
if (lean_obj_tag(x_1284) == 0)
{
lean_object* x_1285; lean_object* x_1286; 
lean_dec(x_1220);
x_1285 = lean_ctor_get(x_1284, 0);
lean_inc(x_1285);
x_1286 = lean_ctor_get(x_1284, 1);
lean_inc(x_1286);
lean_dec(x_1284);
x_1253 = x_1285;
x_1254 = x_1286;
goto block_1275;
}
else
{
lean_object* x_1287; lean_object* x_1288; 
x_1287 = lean_ctor_get(x_1284, 0);
lean_inc(x_1287);
x_1288 = lean_ctor_get(x_1284, 1);
lean_inc(x_1288);
lean_dec(x_1284);
x_1221 = x_1287;
x_1222 = x_1288;
goto block_1252;
}
}
}
else
{
lean_object* x_1289; lean_object* x_1290; 
lean_dec(x_5);
x_1289 = lean_ctor_get(x_1279, 0);
lean_inc(x_1289);
x_1290 = lean_ctor_get(x_1279, 1);
lean_inc(x_1290);
lean_dec(x_1279);
x_1221 = x_1289;
x_1222 = x_1290;
goto block_1252;
}
}
else
{
lean_object* x_1291; lean_object* x_1292; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1291 = lean_ctor_get(x_1276, 0);
lean_inc(x_1291);
x_1292 = lean_ctor_get(x_1276, 1);
lean_inc(x_1292);
lean_dec(x_1276);
x_1221 = x_1291;
x_1222 = x_1292;
goto block_1252;
}
block_1252:
{
if (lean_obj_tag(x_1221) == 0)
{
lean_object* x_1223; uint8_t x_1224; 
lean_dec(x_1220);
x_1223 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1222);
x_1224 = !lean_is_exclusive(x_1223);
if (x_1224 == 0)
{
lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; uint8_t x_1228; 
x_1225 = lean_ctor_get(x_1223, 0);
x_1226 = lean_ctor_get(x_1223, 1);
x_1227 = l_Lean_Elab_Term_SavedState_restore(x_1218, x_9, x_10, x_11, x_12, x_13, x_14, x_1226);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1228 = !lean_is_exclusive(x_1227);
if (x_1228 == 0)
{
lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; 
x_1229 = lean_ctor_get(x_1227, 1);
x_1230 = lean_ctor_get(x_1227, 0);
lean_dec(x_1230);
lean_ctor_set_tag(x_1227, 1);
lean_ctor_set(x_1227, 1, x_1225);
lean_ctor_set(x_1227, 0, x_1221);
x_1231 = lean_array_push(x_8, x_1227);
lean_ctor_set(x_1223, 1, x_1229);
lean_ctor_set(x_1223, 0, x_1231);
return x_1223;
}
else
{
lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; 
x_1232 = lean_ctor_get(x_1227, 1);
lean_inc(x_1232);
lean_dec(x_1227);
x_1233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1233, 0, x_1221);
lean_ctor_set(x_1233, 1, x_1225);
x_1234 = lean_array_push(x_8, x_1233);
lean_ctor_set(x_1223, 1, x_1232);
lean_ctor_set(x_1223, 0, x_1234);
return x_1223;
}
}
else
{
lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; 
x_1235 = lean_ctor_get(x_1223, 0);
x_1236 = lean_ctor_get(x_1223, 1);
lean_inc(x_1236);
lean_inc(x_1235);
lean_dec(x_1223);
x_1237 = l_Lean_Elab_Term_SavedState_restore(x_1218, x_9, x_10, x_11, x_12, x_13, x_14, x_1236);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1238 = lean_ctor_get(x_1237, 1);
lean_inc(x_1238);
if (lean_is_exclusive(x_1237)) {
 lean_ctor_release(x_1237, 0);
 lean_ctor_release(x_1237, 1);
 x_1239 = x_1237;
} else {
 lean_dec_ref(x_1237);
 x_1239 = lean_box(0);
}
if (lean_is_scalar(x_1239)) {
 x_1240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1240 = x_1239;
 lean_ctor_set_tag(x_1240, 1);
}
lean_ctor_set(x_1240, 0, x_1221);
lean_ctor_set(x_1240, 1, x_1235);
x_1241 = lean_array_push(x_8, x_1240);
x_1242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1242, 0, x_1241);
lean_ctor_set(x_1242, 1, x_1238);
return x_1242;
}
}
else
{
lean_object* x_1243; lean_object* x_1244; uint8_t x_1245; 
lean_dec(x_8);
x_1243 = lean_ctor_get(x_1221, 0);
lean_inc(x_1243);
x_1244 = l_Lean_Elab_postponeExceptionId;
x_1245 = lean_nat_dec_eq(x_1243, x_1244);
lean_dec(x_1243);
if (x_1245 == 0)
{
lean_object* x_1246; 
lean_dec(x_1218);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1220)) {
 x_1246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1246 = x_1220;
 lean_ctor_set_tag(x_1246, 1);
}
lean_ctor_set(x_1246, 0, x_1221);
lean_ctor_set(x_1246, 1, x_1222);
return x_1246;
}
else
{
lean_object* x_1247; uint8_t x_1248; 
lean_dec(x_1220);
x_1247 = l_Lean_Elab_Term_SavedState_restore(x_1218, x_9, x_10, x_11, x_12, x_13, x_14, x_1222);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1248 = !lean_is_exclusive(x_1247);
if (x_1248 == 0)
{
lean_object* x_1249; 
x_1249 = lean_ctor_get(x_1247, 0);
lean_dec(x_1249);
lean_ctor_set_tag(x_1247, 1);
lean_ctor_set(x_1247, 0, x_1221);
return x_1247;
}
else
{
lean_object* x_1250; lean_object* x_1251; 
x_1250 = lean_ctor_get(x_1247, 1);
lean_inc(x_1250);
lean_dec(x_1247);
x_1251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1251, 0, x_1221);
lean_ctor_set(x_1251, 1, x_1250);
return x_1251;
}
}
}
}
block_1275:
{
lean_object* x_1255; uint8_t x_1256; 
x_1255 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1254);
x_1256 = !lean_is_exclusive(x_1255);
if (x_1256 == 0)
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; uint8_t x_1260; 
x_1257 = lean_ctor_get(x_1255, 0);
x_1258 = lean_ctor_get(x_1255, 1);
x_1259 = l_Lean_Elab_Term_SavedState_restore(x_1218, x_9, x_10, x_11, x_12, x_13, x_14, x_1258);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1260 = !lean_is_exclusive(x_1259);
if (x_1260 == 0)
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; 
x_1261 = lean_ctor_get(x_1259, 1);
x_1262 = lean_ctor_get(x_1259, 0);
lean_dec(x_1262);
lean_ctor_set(x_1259, 1, x_1257);
lean_ctor_set(x_1259, 0, x_1253);
x_1263 = lean_array_push(x_8, x_1259);
lean_ctor_set(x_1255, 1, x_1261);
lean_ctor_set(x_1255, 0, x_1263);
return x_1255;
}
else
{
lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; 
x_1264 = lean_ctor_get(x_1259, 1);
lean_inc(x_1264);
lean_dec(x_1259);
x_1265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1265, 0, x_1253);
lean_ctor_set(x_1265, 1, x_1257);
x_1266 = lean_array_push(x_8, x_1265);
lean_ctor_set(x_1255, 1, x_1264);
lean_ctor_set(x_1255, 0, x_1266);
return x_1255;
}
}
else
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; 
x_1267 = lean_ctor_get(x_1255, 0);
x_1268 = lean_ctor_get(x_1255, 1);
lean_inc(x_1268);
lean_inc(x_1267);
lean_dec(x_1255);
x_1269 = l_Lean_Elab_Term_SavedState_restore(x_1218, x_9, x_10, x_11, x_12, x_13, x_14, x_1268);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1270 = lean_ctor_get(x_1269, 1);
lean_inc(x_1270);
if (lean_is_exclusive(x_1269)) {
 lean_ctor_release(x_1269, 0);
 lean_ctor_release(x_1269, 1);
 x_1271 = x_1269;
} else {
 lean_dec_ref(x_1269);
 x_1271 = lean_box(0);
}
if (lean_is_scalar(x_1271)) {
 x_1272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1272 = x_1271;
}
lean_ctor_set(x_1272, 0, x_1253);
lean_ctor_set(x_1272, 1, x_1267);
x_1273 = lean_array_push(x_8, x_1272);
x_1274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1274, 0, x_1273);
lean_ctor_set(x_1274, 1, x_1270);
return x_1274;
}
}
}
else
{
uint8_t x_1293; 
x_1293 = l_Array_isEmpty___rarg(x_3);
if (x_1293 == 0)
{
lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1331; lean_object* x_1332; lean_object* x_1354; 
x_1294 = lean_box(0);
x_1295 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1296 = lean_ctor_get(x_1295, 0);
lean_inc(x_1296);
x_1297 = lean_ctor_get(x_1295, 1);
lean_inc(x_1297);
if (lean_is_exclusive(x_1295)) {
 lean_ctor_release(x_1295, 0);
 lean_ctor_release(x_1295, 1);
 x_1298 = x_1295;
} else {
 lean_dec_ref(x_1295);
 x_1298 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1354 = l_Lean_Elab_Term_elabTerm(x_1, x_1294, x_1215, x_9, x_10, x_11, x_12, x_13, x_14, x_1297);
if (lean_obj_tag(x_1354) == 0)
{
lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; 
x_1355 = lean_ctor_get(x_1354, 0);
lean_inc(x_1355);
x_1356 = lean_ctor_get(x_1354, 1);
lean_inc(x_1356);
lean_dec(x_1354);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_1357 = l___private_Lean_Elab_App_21__elabAppLVals(x_1355, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_1356);
if (lean_obj_tag(x_1357) == 0)
{
if (x_7 == 0)
{
lean_object* x_1358; lean_object* x_1359; 
lean_dec(x_1298);
lean_dec(x_5);
x_1358 = lean_ctor_get(x_1357, 0);
lean_inc(x_1358);
x_1359 = lean_ctor_get(x_1357, 1);
lean_inc(x_1359);
lean_dec(x_1357);
x_1331 = x_1358;
x_1332 = x_1359;
goto block_1353;
}
else
{
lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; 
x_1360 = lean_ctor_get(x_1357, 0);
lean_inc(x_1360);
x_1361 = lean_ctor_get(x_1357, 1);
lean_inc(x_1361);
lean_dec(x_1357);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_1362 = l_Lean_Elab_Term_ensureHasType(x_5, x_1360, x_9, x_10, x_11, x_12, x_13, x_14, x_1361);
if (lean_obj_tag(x_1362) == 0)
{
lean_object* x_1363; lean_object* x_1364; 
lean_dec(x_1298);
x_1363 = lean_ctor_get(x_1362, 0);
lean_inc(x_1363);
x_1364 = lean_ctor_get(x_1362, 1);
lean_inc(x_1364);
lean_dec(x_1362);
x_1331 = x_1363;
x_1332 = x_1364;
goto block_1353;
}
else
{
lean_object* x_1365; lean_object* x_1366; 
x_1365 = lean_ctor_get(x_1362, 0);
lean_inc(x_1365);
x_1366 = lean_ctor_get(x_1362, 1);
lean_inc(x_1366);
lean_dec(x_1362);
x_1299 = x_1365;
x_1300 = x_1366;
goto block_1330;
}
}
}
else
{
lean_object* x_1367; lean_object* x_1368; 
lean_dec(x_5);
x_1367 = lean_ctor_get(x_1357, 0);
lean_inc(x_1367);
x_1368 = lean_ctor_get(x_1357, 1);
lean_inc(x_1368);
lean_dec(x_1357);
x_1299 = x_1367;
x_1300 = x_1368;
goto block_1330;
}
}
else
{
lean_object* x_1369; lean_object* x_1370; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1369 = lean_ctor_get(x_1354, 0);
lean_inc(x_1369);
x_1370 = lean_ctor_get(x_1354, 1);
lean_inc(x_1370);
lean_dec(x_1354);
x_1299 = x_1369;
x_1300 = x_1370;
goto block_1330;
}
block_1330:
{
if (lean_obj_tag(x_1299) == 0)
{
lean_object* x_1301; uint8_t x_1302; 
lean_dec(x_1298);
x_1301 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1300);
x_1302 = !lean_is_exclusive(x_1301);
if (x_1302 == 0)
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; uint8_t x_1306; 
x_1303 = lean_ctor_get(x_1301, 0);
x_1304 = lean_ctor_get(x_1301, 1);
x_1305 = l_Lean_Elab_Term_SavedState_restore(x_1296, x_9, x_10, x_11, x_12, x_13, x_14, x_1304);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1306 = !lean_is_exclusive(x_1305);
if (x_1306 == 0)
{
lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; 
x_1307 = lean_ctor_get(x_1305, 1);
x_1308 = lean_ctor_get(x_1305, 0);
lean_dec(x_1308);
lean_ctor_set_tag(x_1305, 1);
lean_ctor_set(x_1305, 1, x_1303);
lean_ctor_set(x_1305, 0, x_1299);
x_1309 = lean_array_push(x_8, x_1305);
lean_ctor_set(x_1301, 1, x_1307);
lean_ctor_set(x_1301, 0, x_1309);
return x_1301;
}
else
{
lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; 
x_1310 = lean_ctor_get(x_1305, 1);
lean_inc(x_1310);
lean_dec(x_1305);
x_1311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1311, 0, x_1299);
lean_ctor_set(x_1311, 1, x_1303);
x_1312 = lean_array_push(x_8, x_1311);
lean_ctor_set(x_1301, 1, x_1310);
lean_ctor_set(x_1301, 0, x_1312);
return x_1301;
}
}
else
{
lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; 
x_1313 = lean_ctor_get(x_1301, 0);
x_1314 = lean_ctor_get(x_1301, 1);
lean_inc(x_1314);
lean_inc(x_1313);
lean_dec(x_1301);
x_1315 = l_Lean_Elab_Term_SavedState_restore(x_1296, x_9, x_10, x_11, x_12, x_13, x_14, x_1314);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1316 = lean_ctor_get(x_1315, 1);
lean_inc(x_1316);
if (lean_is_exclusive(x_1315)) {
 lean_ctor_release(x_1315, 0);
 lean_ctor_release(x_1315, 1);
 x_1317 = x_1315;
} else {
 lean_dec_ref(x_1315);
 x_1317 = lean_box(0);
}
if (lean_is_scalar(x_1317)) {
 x_1318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1318 = x_1317;
 lean_ctor_set_tag(x_1318, 1);
}
lean_ctor_set(x_1318, 0, x_1299);
lean_ctor_set(x_1318, 1, x_1313);
x_1319 = lean_array_push(x_8, x_1318);
x_1320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1320, 0, x_1319);
lean_ctor_set(x_1320, 1, x_1316);
return x_1320;
}
}
else
{
lean_object* x_1321; lean_object* x_1322; uint8_t x_1323; 
lean_dec(x_8);
x_1321 = lean_ctor_get(x_1299, 0);
lean_inc(x_1321);
x_1322 = l_Lean_Elab_postponeExceptionId;
x_1323 = lean_nat_dec_eq(x_1321, x_1322);
lean_dec(x_1321);
if (x_1323 == 0)
{
lean_object* x_1324; 
lean_dec(x_1296);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1298)) {
 x_1324 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1324 = x_1298;
 lean_ctor_set_tag(x_1324, 1);
}
lean_ctor_set(x_1324, 0, x_1299);
lean_ctor_set(x_1324, 1, x_1300);
return x_1324;
}
else
{
lean_object* x_1325; uint8_t x_1326; 
lean_dec(x_1298);
x_1325 = l_Lean_Elab_Term_SavedState_restore(x_1296, x_9, x_10, x_11, x_12, x_13, x_14, x_1300);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1326 = !lean_is_exclusive(x_1325);
if (x_1326 == 0)
{
lean_object* x_1327; 
x_1327 = lean_ctor_get(x_1325, 0);
lean_dec(x_1327);
lean_ctor_set_tag(x_1325, 1);
lean_ctor_set(x_1325, 0, x_1299);
return x_1325;
}
else
{
lean_object* x_1328; lean_object* x_1329; 
x_1328 = lean_ctor_get(x_1325, 1);
lean_inc(x_1328);
lean_dec(x_1325);
x_1329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1329, 0, x_1299);
lean_ctor_set(x_1329, 1, x_1328);
return x_1329;
}
}
}
}
block_1353:
{
lean_object* x_1333; uint8_t x_1334; 
x_1333 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1332);
x_1334 = !lean_is_exclusive(x_1333);
if (x_1334 == 0)
{
lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; uint8_t x_1338; 
x_1335 = lean_ctor_get(x_1333, 0);
x_1336 = lean_ctor_get(x_1333, 1);
x_1337 = l_Lean_Elab_Term_SavedState_restore(x_1296, x_9, x_10, x_11, x_12, x_13, x_14, x_1336);
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
x_1343 = lean_alloc_ctor(0, 2, 0);
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
x_1347 = l_Lean_Elab_Term_SavedState_restore(x_1296, x_9, x_10, x_11, x_12, x_13, x_14, x_1346);
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
 x_1350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1350 = x_1349;
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
}
else
{
uint8_t x_1371; 
x_1371 = l_Array_isEmpty___rarg(x_4);
if (x_1371 == 0)
{
lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; lean_object* x_1409; lean_object* x_1410; lean_object* x_1432; 
x_1372 = lean_box(0);
x_1373 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1374 = lean_ctor_get(x_1373, 0);
lean_inc(x_1374);
x_1375 = lean_ctor_get(x_1373, 1);
lean_inc(x_1375);
if (lean_is_exclusive(x_1373)) {
 lean_ctor_release(x_1373, 0);
 lean_ctor_release(x_1373, 1);
 x_1376 = x_1373;
} else {
 lean_dec_ref(x_1373);
 x_1376 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1432 = l_Lean_Elab_Term_elabTerm(x_1, x_1372, x_1215, x_9, x_10, x_11, x_12, x_13, x_14, x_1375);
if (lean_obj_tag(x_1432) == 0)
{
lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; 
x_1433 = lean_ctor_get(x_1432, 0);
lean_inc(x_1433);
x_1434 = lean_ctor_get(x_1432, 1);
lean_inc(x_1434);
lean_dec(x_1432);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_1435 = l___private_Lean_Elab_App_21__elabAppLVals(x_1433, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_1434);
if (lean_obj_tag(x_1435) == 0)
{
if (x_7 == 0)
{
lean_object* x_1436; lean_object* x_1437; 
lean_dec(x_1376);
lean_dec(x_5);
x_1436 = lean_ctor_get(x_1435, 0);
lean_inc(x_1436);
x_1437 = lean_ctor_get(x_1435, 1);
lean_inc(x_1437);
lean_dec(x_1435);
x_1409 = x_1436;
x_1410 = x_1437;
goto block_1431;
}
else
{
lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; 
x_1438 = lean_ctor_get(x_1435, 0);
lean_inc(x_1438);
x_1439 = lean_ctor_get(x_1435, 1);
lean_inc(x_1439);
lean_dec(x_1435);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
x_1440 = l_Lean_Elab_Term_ensureHasType(x_5, x_1438, x_9, x_10, x_11, x_12, x_13, x_14, x_1439);
if (lean_obj_tag(x_1440) == 0)
{
lean_object* x_1441; lean_object* x_1442; 
lean_dec(x_1376);
x_1441 = lean_ctor_get(x_1440, 0);
lean_inc(x_1441);
x_1442 = lean_ctor_get(x_1440, 1);
lean_inc(x_1442);
lean_dec(x_1440);
x_1409 = x_1441;
x_1410 = x_1442;
goto block_1431;
}
else
{
lean_object* x_1443; lean_object* x_1444; 
x_1443 = lean_ctor_get(x_1440, 0);
lean_inc(x_1443);
x_1444 = lean_ctor_get(x_1440, 1);
lean_inc(x_1444);
lean_dec(x_1440);
x_1377 = x_1443;
x_1378 = x_1444;
goto block_1408;
}
}
}
else
{
lean_object* x_1445; lean_object* x_1446; 
lean_dec(x_5);
x_1445 = lean_ctor_get(x_1435, 0);
lean_inc(x_1445);
x_1446 = lean_ctor_get(x_1435, 1);
lean_inc(x_1446);
lean_dec(x_1435);
x_1377 = x_1445;
x_1378 = x_1446;
goto block_1408;
}
}
else
{
lean_object* x_1447; lean_object* x_1448; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1447 = lean_ctor_get(x_1432, 0);
lean_inc(x_1447);
x_1448 = lean_ctor_get(x_1432, 1);
lean_inc(x_1448);
lean_dec(x_1432);
x_1377 = x_1447;
x_1378 = x_1448;
goto block_1408;
}
block_1408:
{
if (lean_obj_tag(x_1377) == 0)
{
lean_object* x_1379; uint8_t x_1380; 
lean_dec(x_1376);
x_1379 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1378);
x_1380 = !lean_is_exclusive(x_1379);
if (x_1380 == 0)
{
lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; uint8_t x_1384; 
x_1381 = lean_ctor_get(x_1379, 0);
x_1382 = lean_ctor_get(x_1379, 1);
x_1383 = l_Lean_Elab_Term_SavedState_restore(x_1374, x_9, x_10, x_11, x_12, x_13, x_14, x_1382);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1384 = !lean_is_exclusive(x_1383);
if (x_1384 == 0)
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; 
x_1385 = lean_ctor_get(x_1383, 1);
x_1386 = lean_ctor_get(x_1383, 0);
lean_dec(x_1386);
lean_ctor_set_tag(x_1383, 1);
lean_ctor_set(x_1383, 1, x_1381);
lean_ctor_set(x_1383, 0, x_1377);
x_1387 = lean_array_push(x_8, x_1383);
lean_ctor_set(x_1379, 1, x_1385);
lean_ctor_set(x_1379, 0, x_1387);
return x_1379;
}
else
{
lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; 
x_1388 = lean_ctor_get(x_1383, 1);
lean_inc(x_1388);
lean_dec(x_1383);
x_1389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1389, 0, x_1377);
lean_ctor_set(x_1389, 1, x_1381);
x_1390 = lean_array_push(x_8, x_1389);
lean_ctor_set(x_1379, 1, x_1388);
lean_ctor_set(x_1379, 0, x_1390);
return x_1379;
}
}
else
{
lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; 
x_1391 = lean_ctor_get(x_1379, 0);
x_1392 = lean_ctor_get(x_1379, 1);
lean_inc(x_1392);
lean_inc(x_1391);
lean_dec(x_1379);
x_1393 = l_Lean_Elab_Term_SavedState_restore(x_1374, x_9, x_10, x_11, x_12, x_13, x_14, x_1392);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1394 = lean_ctor_get(x_1393, 1);
lean_inc(x_1394);
if (lean_is_exclusive(x_1393)) {
 lean_ctor_release(x_1393, 0);
 lean_ctor_release(x_1393, 1);
 x_1395 = x_1393;
} else {
 lean_dec_ref(x_1393);
 x_1395 = lean_box(0);
}
if (lean_is_scalar(x_1395)) {
 x_1396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1396 = x_1395;
 lean_ctor_set_tag(x_1396, 1);
}
lean_ctor_set(x_1396, 0, x_1377);
lean_ctor_set(x_1396, 1, x_1391);
x_1397 = lean_array_push(x_8, x_1396);
x_1398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1398, 0, x_1397);
lean_ctor_set(x_1398, 1, x_1394);
return x_1398;
}
}
else
{
lean_object* x_1399; lean_object* x_1400; uint8_t x_1401; 
lean_dec(x_8);
x_1399 = lean_ctor_get(x_1377, 0);
lean_inc(x_1399);
x_1400 = l_Lean_Elab_postponeExceptionId;
x_1401 = lean_nat_dec_eq(x_1399, x_1400);
lean_dec(x_1399);
if (x_1401 == 0)
{
lean_object* x_1402; 
lean_dec(x_1374);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1376)) {
 x_1402 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1402 = x_1376;
 lean_ctor_set_tag(x_1402, 1);
}
lean_ctor_set(x_1402, 0, x_1377);
lean_ctor_set(x_1402, 1, x_1378);
return x_1402;
}
else
{
lean_object* x_1403; uint8_t x_1404; 
lean_dec(x_1376);
x_1403 = l_Lean_Elab_Term_SavedState_restore(x_1374, x_9, x_10, x_11, x_12, x_13, x_14, x_1378);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1404 = !lean_is_exclusive(x_1403);
if (x_1404 == 0)
{
lean_object* x_1405; 
x_1405 = lean_ctor_get(x_1403, 0);
lean_dec(x_1405);
lean_ctor_set_tag(x_1403, 1);
lean_ctor_set(x_1403, 0, x_1377);
return x_1403;
}
else
{
lean_object* x_1406; lean_object* x_1407; 
x_1406 = lean_ctor_get(x_1403, 1);
lean_inc(x_1406);
lean_dec(x_1403);
x_1407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1407, 0, x_1377);
lean_ctor_set(x_1407, 1, x_1406);
return x_1407;
}
}
}
}
block_1431:
{
lean_object* x_1411; uint8_t x_1412; 
x_1411 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1410);
x_1412 = !lean_is_exclusive(x_1411);
if (x_1412 == 0)
{
lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; uint8_t x_1416; 
x_1413 = lean_ctor_get(x_1411, 0);
x_1414 = lean_ctor_get(x_1411, 1);
x_1415 = l_Lean_Elab_Term_SavedState_restore(x_1374, x_9, x_10, x_11, x_12, x_13, x_14, x_1414);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1416 = !lean_is_exclusive(x_1415);
if (x_1416 == 0)
{
lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; 
x_1417 = lean_ctor_get(x_1415, 1);
x_1418 = lean_ctor_get(x_1415, 0);
lean_dec(x_1418);
lean_ctor_set(x_1415, 1, x_1413);
lean_ctor_set(x_1415, 0, x_1409);
x_1419 = lean_array_push(x_8, x_1415);
lean_ctor_set(x_1411, 1, x_1417);
lean_ctor_set(x_1411, 0, x_1419);
return x_1411;
}
else
{
lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; 
x_1420 = lean_ctor_get(x_1415, 1);
lean_inc(x_1420);
lean_dec(x_1415);
x_1421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1421, 0, x_1409);
lean_ctor_set(x_1421, 1, x_1413);
x_1422 = lean_array_push(x_8, x_1421);
lean_ctor_set(x_1411, 1, x_1420);
lean_ctor_set(x_1411, 0, x_1422);
return x_1411;
}
}
else
{
lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; 
x_1423 = lean_ctor_get(x_1411, 0);
x_1424 = lean_ctor_get(x_1411, 1);
lean_inc(x_1424);
lean_inc(x_1423);
lean_dec(x_1411);
x_1425 = l_Lean_Elab_Term_SavedState_restore(x_1374, x_9, x_10, x_11, x_12, x_13, x_14, x_1424);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1426 = lean_ctor_get(x_1425, 1);
lean_inc(x_1426);
if (lean_is_exclusive(x_1425)) {
 lean_ctor_release(x_1425, 0);
 lean_ctor_release(x_1425, 1);
 x_1427 = x_1425;
} else {
 lean_dec_ref(x_1425);
 x_1427 = lean_box(0);
}
if (lean_is_scalar(x_1427)) {
 x_1428 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1428 = x_1427;
}
lean_ctor_set(x_1428, 0, x_1409);
lean_ctor_set(x_1428, 1, x_1423);
x_1429 = lean_array_push(x_8, x_1428);
x_1430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1430, 0, x_1429);
lean_ctor_set(x_1430, 1, x_1426);
return x_1430;
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
lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; uint8_t x_1485; lean_object* x_1486; 
x_1449 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1450 = lean_ctor_get(x_1449, 0);
lean_inc(x_1450);
x_1451 = lean_ctor_get(x_1449, 1);
lean_inc(x_1451);
if (lean_is_exclusive(x_1449)) {
 lean_ctor_release(x_1449, 0);
 lean_ctor_release(x_1449, 1);
 x_1452 = x_1449;
} else {
 lean_dec_ref(x_1449);
 x_1452 = lean_box(0);
}
x_1485 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1486 = l_Lean_Elab_Term_elabTerm(x_1, x_5, x_1485, x_9, x_10, x_11, x_12, x_13, x_14, x_1451);
if (lean_obj_tag(x_1486) == 0)
{
lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; uint8_t x_1490; 
lean_dec(x_1452);
x_1487 = lean_ctor_get(x_1486, 0);
lean_inc(x_1487);
x_1488 = lean_ctor_get(x_1486, 1);
lean_inc(x_1488);
lean_dec(x_1486);
x_1489 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1488);
x_1490 = !lean_is_exclusive(x_1489);
if (x_1490 == 0)
{
lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; uint8_t x_1494; 
x_1491 = lean_ctor_get(x_1489, 0);
x_1492 = lean_ctor_get(x_1489, 1);
x_1493 = l_Lean_Elab_Term_SavedState_restore(x_1450, x_9, x_10, x_11, x_12, x_13, x_14, x_1492);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1494 = !lean_is_exclusive(x_1493);
if (x_1494 == 0)
{
lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; 
x_1495 = lean_ctor_get(x_1493, 1);
x_1496 = lean_ctor_get(x_1493, 0);
lean_dec(x_1496);
lean_ctor_set(x_1493, 1, x_1491);
lean_ctor_set(x_1493, 0, x_1487);
x_1497 = lean_array_push(x_8, x_1493);
lean_ctor_set(x_1489, 1, x_1495);
lean_ctor_set(x_1489, 0, x_1497);
return x_1489;
}
else
{
lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; 
x_1498 = lean_ctor_get(x_1493, 1);
lean_inc(x_1498);
lean_dec(x_1493);
x_1499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1499, 0, x_1487);
lean_ctor_set(x_1499, 1, x_1491);
x_1500 = lean_array_push(x_8, x_1499);
lean_ctor_set(x_1489, 1, x_1498);
lean_ctor_set(x_1489, 0, x_1500);
return x_1489;
}
}
else
{
lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; 
x_1501 = lean_ctor_get(x_1489, 0);
x_1502 = lean_ctor_get(x_1489, 1);
lean_inc(x_1502);
lean_inc(x_1501);
lean_dec(x_1489);
x_1503 = l_Lean_Elab_Term_SavedState_restore(x_1450, x_9, x_10, x_11, x_12, x_13, x_14, x_1502);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1504 = lean_ctor_get(x_1503, 1);
lean_inc(x_1504);
if (lean_is_exclusive(x_1503)) {
 lean_ctor_release(x_1503, 0);
 lean_ctor_release(x_1503, 1);
 x_1505 = x_1503;
} else {
 lean_dec_ref(x_1503);
 x_1505 = lean_box(0);
}
if (lean_is_scalar(x_1505)) {
 x_1506 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1506 = x_1505;
}
lean_ctor_set(x_1506, 0, x_1487);
lean_ctor_set(x_1506, 1, x_1501);
x_1507 = lean_array_push(x_8, x_1506);
x_1508 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1508, 0, x_1507);
lean_ctor_set(x_1508, 1, x_1504);
return x_1508;
}
}
else
{
lean_object* x_1509; lean_object* x_1510; 
x_1509 = lean_ctor_get(x_1486, 0);
lean_inc(x_1509);
x_1510 = lean_ctor_get(x_1486, 1);
lean_inc(x_1510);
lean_dec(x_1486);
x_1453 = x_1509;
x_1454 = x_1510;
goto block_1484;
}
block_1484:
{
if (lean_obj_tag(x_1453) == 0)
{
lean_object* x_1455; uint8_t x_1456; 
lean_dec(x_1452);
x_1455 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1454);
x_1456 = !lean_is_exclusive(x_1455);
if (x_1456 == 0)
{
lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; uint8_t x_1460; 
x_1457 = lean_ctor_get(x_1455, 0);
x_1458 = lean_ctor_get(x_1455, 1);
x_1459 = l_Lean_Elab_Term_SavedState_restore(x_1450, x_9, x_10, x_11, x_12, x_13, x_14, x_1458);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1460 = !lean_is_exclusive(x_1459);
if (x_1460 == 0)
{
lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; 
x_1461 = lean_ctor_get(x_1459, 1);
x_1462 = lean_ctor_get(x_1459, 0);
lean_dec(x_1462);
lean_ctor_set_tag(x_1459, 1);
lean_ctor_set(x_1459, 1, x_1457);
lean_ctor_set(x_1459, 0, x_1453);
x_1463 = lean_array_push(x_8, x_1459);
lean_ctor_set(x_1455, 1, x_1461);
lean_ctor_set(x_1455, 0, x_1463);
return x_1455;
}
else
{
lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; 
x_1464 = lean_ctor_get(x_1459, 1);
lean_inc(x_1464);
lean_dec(x_1459);
x_1465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1465, 0, x_1453);
lean_ctor_set(x_1465, 1, x_1457);
x_1466 = lean_array_push(x_8, x_1465);
lean_ctor_set(x_1455, 1, x_1464);
lean_ctor_set(x_1455, 0, x_1466);
return x_1455;
}
}
else
{
lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; 
x_1467 = lean_ctor_get(x_1455, 0);
x_1468 = lean_ctor_get(x_1455, 1);
lean_inc(x_1468);
lean_inc(x_1467);
lean_dec(x_1455);
x_1469 = l_Lean_Elab_Term_SavedState_restore(x_1450, x_9, x_10, x_11, x_12, x_13, x_14, x_1468);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1470 = lean_ctor_get(x_1469, 1);
lean_inc(x_1470);
if (lean_is_exclusive(x_1469)) {
 lean_ctor_release(x_1469, 0);
 lean_ctor_release(x_1469, 1);
 x_1471 = x_1469;
} else {
 lean_dec_ref(x_1469);
 x_1471 = lean_box(0);
}
if (lean_is_scalar(x_1471)) {
 x_1472 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1472 = x_1471;
 lean_ctor_set_tag(x_1472, 1);
}
lean_ctor_set(x_1472, 0, x_1453);
lean_ctor_set(x_1472, 1, x_1467);
x_1473 = lean_array_push(x_8, x_1472);
x_1474 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1474, 0, x_1473);
lean_ctor_set(x_1474, 1, x_1470);
return x_1474;
}
}
else
{
lean_object* x_1475; lean_object* x_1476; uint8_t x_1477; 
lean_dec(x_8);
x_1475 = lean_ctor_get(x_1453, 0);
lean_inc(x_1475);
x_1476 = l_Lean_Elab_postponeExceptionId;
x_1477 = lean_nat_dec_eq(x_1475, x_1476);
lean_dec(x_1475);
if (x_1477 == 0)
{
lean_object* x_1478; 
lean_dec(x_1450);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1452)) {
 x_1478 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1478 = x_1452;
 lean_ctor_set_tag(x_1478, 1);
}
lean_ctor_set(x_1478, 0, x_1453);
lean_ctor_set(x_1478, 1, x_1454);
return x_1478;
}
else
{
lean_object* x_1479; uint8_t x_1480; 
lean_dec(x_1452);
x_1479 = l_Lean_Elab_Term_SavedState_restore(x_1450, x_9, x_10, x_11, x_12, x_13, x_14, x_1454);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1480 = !lean_is_exclusive(x_1479);
if (x_1480 == 0)
{
lean_object* x_1481; 
x_1481 = lean_ctor_get(x_1479, 0);
lean_dec(x_1481);
lean_ctor_set_tag(x_1479, 1);
lean_ctor_set(x_1479, 0, x_1453);
return x_1479;
}
else
{
lean_object* x_1482; lean_object* x_1483; 
x_1482 = lean_ctor_get(x_1479, 1);
lean_inc(x_1482);
lean_dec(x_1479);
x_1483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1483, 0, x_1453);
lean_ctor_set(x_1483, 1, x_1482);
return x_1483;
}
}
}
}
}
else
{
lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1547; 
x_1511 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_1512 = lean_ctor_get(x_1511, 0);
lean_inc(x_1512);
x_1513 = lean_ctor_get(x_1511, 1);
lean_inc(x_1513);
if (lean_is_exclusive(x_1511)) {
 lean_ctor_release(x_1511, 0);
 lean_ctor_release(x_1511, 1);
 x_1514 = x_1511;
} else {
 lean_dec_ref(x_1511);
 x_1514 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_1547 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_1215, x_9, x_10, x_11, x_12, x_13, x_14, x_1513);
if (lean_obj_tag(x_1547) == 0)
{
lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; uint8_t x_1551; 
lean_dec(x_1514);
x_1548 = lean_ctor_get(x_1547, 0);
lean_inc(x_1548);
x_1549 = lean_ctor_get(x_1547, 1);
lean_inc(x_1549);
lean_dec(x_1547);
x_1550 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1549);
x_1551 = !lean_is_exclusive(x_1550);
if (x_1551 == 0)
{
lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; uint8_t x_1555; 
x_1552 = lean_ctor_get(x_1550, 0);
x_1553 = lean_ctor_get(x_1550, 1);
x_1554 = l_Lean_Elab_Term_SavedState_restore(x_1512, x_9, x_10, x_11, x_12, x_13, x_14, x_1553);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1555 = !lean_is_exclusive(x_1554);
if (x_1555 == 0)
{
lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; 
x_1556 = lean_ctor_get(x_1554, 1);
x_1557 = lean_ctor_get(x_1554, 0);
lean_dec(x_1557);
lean_ctor_set(x_1554, 1, x_1552);
lean_ctor_set(x_1554, 0, x_1548);
x_1558 = lean_array_push(x_8, x_1554);
lean_ctor_set(x_1550, 1, x_1556);
lean_ctor_set(x_1550, 0, x_1558);
return x_1550;
}
else
{
lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; 
x_1559 = lean_ctor_get(x_1554, 1);
lean_inc(x_1559);
lean_dec(x_1554);
x_1560 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1560, 0, x_1548);
lean_ctor_set(x_1560, 1, x_1552);
x_1561 = lean_array_push(x_8, x_1560);
lean_ctor_set(x_1550, 1, x_1559);
lean_ctor_set(x_1550, 0, x_1561);
return x_1550;
}
}
else
{
lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; 
x_1562 = lean_ctor_get(x_1550, 0);
x_1563 = lean_ctor_get(x_1550, 1);
lean_inc(x_1563);
lean_inc(x_1562);
lean_dec(x_1550);
x_1564 = l_Lean_Elab_Term_SavedState_restore(x_1512, x_9, x_10, x_11, x_12, x_13, x_14, x_1563);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1565 = lean_ctor_get(x_1564, 1);
lean_inc(x_1565);
if (lean_is_exclusive(x_1564)) {
 lean_ctor_release(x_1564, 0);
 lean_ctor_release(x_1564, 1);
 x_1566 = x_1564;
} else {
 lean_dec_ref(x_1564);
 x_1566 = lean_box(0);
}
if (lean_is_scalar(x_1566)) {
 x_1567 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1567 = x_1566;
}
lean_ctor_set(x_1567, 0, x_1548);
lean_ctor_set(x_1567, 1, x_1562);
x_1568 = lean_array_push(x_8, x_1567);
x_1569 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1569, 0, x_1568);
lean_ctor_set(x_1569, 1, x_1565);
return x_1569;
}
}
else
{
lean_object* x_1570; lean_object* x_1571; 
x_1570 = lean_ctor_get(x_1547, 0);
lean_inc(x_1570);
x_1571 = lean_ctor_get(x_1547, 1);
lean_inc(x_1571);
lean_dec(x_1547);
x_1515 = x_1570;
x_1516 = x_1571;
goto block_1546;
}
block_1546:
{
if (lean_obj_tag(x_1515) == 0)
{
lean_object* x_1517; uint8_t x_1518; 
lean_dec(x_1514);
x_1517 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_1516);
x_1518 = !lean_is_exclusive(x_1517);
if (x_1518 == 0)
{
lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; uint8_t x_1522; 
x_1519 = lean_ctor_get(x_1517, 0);
x_1520 = lean_ctor_get(x_1517, 1);
x_1521 = l_Lean_Elab_Term_SavedState_restore(x_1512, x_9, x_10, x_11, x_12, x_13, x_14, x_1520);
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
lean_ctor_set_tag(x_1521, 1);
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
x_1527 = lean_alloc_ctor(1, 2, 0);
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
x_1531 = l_Lean_Elab_Term_SavedState_restore(x_1512, x_9, x_10, x_11, x_12, x_13, x_14, x_1530);
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
 x_1534 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1534 = x_1533;
 lean_ctor_set_tag(x_1534, 1);
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
lean_object* x_1537; lean_object* x_1538; uint8_t x_1539; 
lean_dec(x_8);
x_1537 = lean_ctor_get(x_1515, 0);
lean_inc(x_1537);
x_1538 = l_Lean_Elab_postponeExceptionId;
x_1539 = lean_nat_dec_eq(x_1537, x_1538);
lean_dec(x_1537);
if (x_1539 == 0)
{
lean_object* x_1540; 
lean_dec(x_1512);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_1514)) {
 x_1540 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1540 = x_1514;
 lean_ctor_set_tag(x_1540, 1);
}
lean_ctor_set(x_1540, 0, x_1515);
lean_ctor_set(x_1540, 1, x_1516);
return x_1540;
}
else
{
lean_object* x_1541; uint8_t x_1542; 
lean_dec(x_1514);
x_1541 = l_Lean_Elab_Term_SavedState_restore(x_1512, x_9, x_10, x_11, x_12, x_13, x_14, x_1516);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1542 = !lean_is_exclusive(x_1541);
if (x_1542 == 0)
{
lean_object* x_1543; 
x_1543 = lean_ctor_get(x_1541, 0);
lean_dec(x_1543);
lean_ctor_set_tag(x_1541, 1);
lean_ctor_set(x_1541, 0, x_1515);
return x_1541;
}
else
{
lean_object* x_1544; lean_object* x_1545; 
x_1544 = lean_ctor_get(x_1541, 1);
lean_inc(x_1544);
lean_dec(x_1541);
x_1545 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1545, 0, x_1515);
lean_ctor_set(x_1545, 1, x_1544);
return x_1545;
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
lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; 
lean_dec(x_1);
x_1575 = l_Lean_Syntax_getId(x_1209);
lean_dec(x_1209);
x_1576 = l_Lean_Name_eraseMacroScopes(x_1575);
lean_dec(x_1575);
x_1577 = l_Lean_Name_components(x_1576);
x_1578 = l_List_map___main___at___private_Lean_Elab_App_23__elabAppFn___main___spec__1(x_1577);
x_1579 = l_List_append___rarg(x_1578, x_2);
x_1 = x_1207;
x_2 = x_1579;
goto _start;
}
}
else
{
lean_object* x_1581; lean_object* x_1582; 
lean_dec(x_1);
x_1581 = l_Lean_fieldIdxKind;
x_1582 = l_Lean_Syntax_isNatLitAux(x_1581, x_1209);
lean_dec(x_1209);
if (lean_obj_tag(x_1582) == 0)
{
lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; 
x_1583 = l_Nat_Inhabited;
x_1584 = l_Option_get_x21___rarg___closed__3;
x_1585 = lean_panic_fn(x_1583, x_1584);
x_1586 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1586, 0, x_1585);
x_1587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1587, 0, x_1586);
lean_ctor_set(x_1587, 1, x_2);
x_1 = x_1207;
x_2 = x_1587;
goto _start;
}
else
{
lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; 
x_1589 = lean_ctor_get(x_1582, 0);
lean_inc(x_1589);
lean_dec(x_1582);
x_1590 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1590, 0, x_1589);
x_1591 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1591, 0, x_1590);
lean_ctor_set(x_1591, 1, x_2);
x_1 = x_1207;
x_2 = x_1591;
goto _start;
}
}
}
}
}
else
{
lean_object* x_1601; uint8_t x_1602; 
x_1601 = l_Lean_Syntax_getArgs(x_1);
x_1602 = !lean_is_exclusive(x_9);
if (x_1602 == 0)
{
uint8_t x_1603; lean_object* x_1604; lean_object* x_1605; 
x_1603 = 0;
lean_ctor_set_uint8(x_9, sizeof(void*)*8 + 1, x_1603);
x_1604 = lean_unsigned_to_nat(0u);
x_1605 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_23__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_1601, x_1604, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1601);
lean_dec(x_1);
return x_1605;
}
else
{
lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; uint8_t x_1614; uint8_t x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; 
x_1606 = lean_ctor_get(x_9, 0);
x_1607 = lean_ctor_get(x_9, 1);
x_1608 = lean_ctor_get(x_9, 2);
x_1609 = lean_ctor_get(x_9, 3);
x_1610 = lean_ctor_get(x_9, 4);
x_1611 = lean_ctor_get(x_9, 5);
x_1612 = lean_ctor_get(x_9, 6);
x_1613 = lean_ctor_get(x_9, 7);
x_1614 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
lean_inc(x_1613);
lean_inc(x_1612);
lean_inc(x_1611);
lean_inc(x_1610);
lean_inc(x_1609);
lean_inc(x_1608);
lean_inc(x_1607);
lean_inc(x_1606);
lean_dec(x_9);
x_1615 = 0;
x_1616 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_1616, 0, x_1606);
lean_ctor_set(x_1616, 1, x_1607);
lean_ctor_set(x_1616, 2, x_1608);
lean_ctor_set(x_1616, 3, x_1609);
lean_ctor_set(x_1616, 4, x_1610);
lean_ctor_set(x_1616, 5, x_1611);
lean_ctor_set(x_1616, 6, x_1612);
lean_ctor_set(x_1616, 7, x_1613);
lean_ctor_set_uint8(x_1616, sizeof(void*)*8, x_1614);
lean_ctor_set_uint8(x_1616, sizeof(void*)*8 + 1, x_1615);
x_1617 = lean_unsigned_to_nat(0u);
x_1618 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_23__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_1601, x_1617, x_8, x_1616, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1601);
lean_dec(x_1);
return x_1618;
}
}
block_380:
{
if (x_16 == 0)
{
uint8_t x_17; uint8_t x_18; 
x_17 = l_List_isEmpty___rarg(x_2);
if (x_7 == 0)
{
uint8_t x_376; 
x_376 = 1;
x_18 = x_376;
goto block_375;
}
else
{
uint8_t x_377; 
x_377 = 0;
x_18 = x_377;
goto block_375;
}
block_375:
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
x_82 = l___private_Lean_Elab_App_21__elabAppLVals(x_80, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_81);
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
x_87 = l_Lean_Elab_Term_ensureHasType(x_5, x_85, x_9, x_10, x_11, x_12, x_13, x_14, x_86);
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
x_160 = l___private_Lean_Elab_App_21__elabAppLVals(x_158, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_159);
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
x_165 = l_Lean_Elab_Term_ensureHasType(x_5, x_163, x_9, x_10, x_11, x_12, x_13, x_14, x_164);
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
x_238 = l___private_Lean_Elab_App_21__elabAppLVals(x_236, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_237);
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
x_243 = l_Lean_Elab_Term_ensureHasType(x_5, x_241, x_9, x_10, x_11, x_12, x_13, x_14, x_242);
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
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_350; 
x_314 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_15);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_317 = x_314;
} else {
 lean_dec_ref(x_314);
 x_317 = lean_box(0);
}
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_350 = l_Lean_Elab_Term_elabTermEnsuringType(x_1, x_5, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_316);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
lean_dec(x_317);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_353 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_352);
x_354 = !lean_is_exclusive(x_353);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; 
x_355 = lean_ctor_get(x_353, 0);
x_356 = lean_ctor_get(x_353, 1);
x_357 = l_Lean_Elab_Term_SavedState_restore(x_315, x_9, x_10, x_11, x_12, x_13, x_14, x_356);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_358 = !lean_is_exclusive(x_357);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_357, 1);
x_360 = lean_ctor_get(x_357, 0);
lean_dec(x_360);
lean_ctor_set(x_357, 1, x_355);
lean_ctor_set(x_357, 0, x_351);
x_361 = lean_array_push(x_8, x_357);
lean_ctor_set(x_353, 1, x_359);
lean_ctor_set(x_353, 0, x_361);
return x_353;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_357, 1);
lean_inc(x_362);
lean_dec(x_357);
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_351);
lean_ctor_set(x_363, 1, x_355);
x_364 = lean_array_push(x_8, x_363);
lean_ctor_set(x_353, 1, x_362);
lean_ctor_set(x_353, 0, x_364);
return x_353;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_365 = lean_ctor_get(x_353, 0);
x_366 = lean_ctor_get(x_353, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_353);
x_367 = l_Lean_Elab_Term_SavedState_restore(x_315, x_9, x_10, x_11, x_12, x_13, x_14, x_366);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
lean_ctor_set(x_370, 0, x_351);
lean_ctor_set(x_370, 1, x_365);
x_371 = lean_array_push(x_8, x_370);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_368);
return x_372;
}
}
else
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_ctor_get(x_350, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_350, 1);
lean_inc(x_374);
lean_dec(x_350);
x_318 = x_373;
x_319 = x_374;
goto block_349;
}
block_349:
{
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_320; uint8_t x_321; 
lean_dec(x_317);
x_320 = l_Lean_Elab_Term_saveAllState___rarg(x_10, x_11, x_12, x_13, x_14, x_319);
x_321 = !lean_is_exclusive(x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
x_322 = lean_ctor_get(x_320, 0);
x_323 = lean_ctor_get(x_320, 1);
x_324 = l_Lean_Elab_Term_SavedState_restore(x_315, x_9, x_10, x_11, x_12, x_13, x_14, x_323);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_325 = !lean_is_exclusive(x_324);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_324, 1);
x_327 = lean_ctor_get(x_324, 0);
lean_dec(x_327);
lean_ctor_set_tag(x_324, 1);
lean_ctor_set(x_324, 1, x_322);
lean_ctor_set(x_324, 0, x_318);
x_328 = lean_array_push(x_8, x_324);
lean_ctor_set(x_320, 1, x_326);
lean_ctor_set(x_320, 0, x_328);
return x_320;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_324, 1);
lean_inc(x_329);
lean_dec(x_324);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_318);
lean_ctor_set(x_330, 1, x_322);
x_331 = lean_array_push(x_8, x_330);
lean_ctor_set(x_320, 1, x_329);
lean_ctor_set(x_320, 0, x_331);
return x_320;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_332 = lean_ctor_get(x_320, 0);
x_333 = lean_ctor_get(x_320, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_320);
x_334 = l_Lean_Elab_Term_SavedState_restore(x_315, x_9, x_10, x_11, x_12, x_13, x_14, x_333);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_335 = lean_ctor_get(x_334, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_336 = x_334;
} else {
 lean_dec_ref(x_334);
 x_336 = lean_box(0);
}
if (lean_is_scalar(x_336)) {
 x_337 = lean_alloc_ctor(1, 2, 0);
} else {
 x_337 = x_336;
 lean_ctor_set_tag(x_337, 1);
}
lean_ctor_set(x_337, 0, x_318);
lean_ctor_set(x_337, 1, x_332);
x_338 = lean_array_push(x_8, x_337);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_335);
return x_339;
}
}
else
{
lean_object* x_340; lean_object* x_341; uint8_t x_342; 
lean_dec(x_8);
x_340 = lean_ctor_get(x_318, 0);
lean_inc(x_340);
x_341 = l_Lean_Elab_postponeExceptionId;
x_342 = lean_nat_dec_eq(x_340, x_341);
lean_dec(x_340);
if (x_342 == 0)
{
lean_object* x_343; 
lean_dec(x_315);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
if (lean_is_scalar(x_317)) {
 x_343 = lean_alloc_ctor(1, 2, 0);
} else {
 x_343 = x_317;
 lean_ctor_set_tag(x_343, 1);
}
lean_ctor_set(x_343, 0, x_318);
lean_ctor_set(x_343, 1, x_319);
return x_343;
}
else
{
lean_object* x_344; uint8_t x_345; 
lean_dec(x_317);
x_344 = l_Lean_Elab_Term_SavedState_restore(x_315, x_9, x_10, x_11, x_12, x_13, x_14, x_319);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_345 = !lean_is_exclusive(x_344);
if (x_345 == 0)
{
lean_object* x_346; 
x_346 = lean_ctor_get(x_344, 0);
lean_dec(x_346);
lean_ctor_set_tag(x_344, 1);
lean_ctor_set(x_344, 0, x_318);
return x_344;
}
else
{
lean_object* x_347; lean_object* x_348; 
x_347 = lean_ctor_get(x_344, 1);
lean_inc(x_347);
lean_dec(x_344);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_318);
lean_ctor_set(x_348, 1, x_347);
return x_348;
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
lean_object* x_378; lean_object* x_379; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_378 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__3;
x_379 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_378, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_379;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_App_23__elabAppFn___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_6);
lean_dec(x_6);
x_18 = l_Array_iterateMAux___main___at___private_Lean_Elab_App_23__elabAppFn___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_1);
return x_18;
}
}
lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = l___private_Lean_Elab_App_23__elabAppFn___main(x_1, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
lean_object* l___private_Lean_Elab_App_23__elabAppFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_App_23__elabAppFn___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
lean_object* l___private_Lean_Elab_App_23__elabAppFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = l___private_Lean_Elab_App_23__elabAppFn(x_1, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_18;
}
}
uint8_t l___private_Lean_Elab_App_24__isSuccess(lean_object* x_1) {
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
lean_object* l___private_Lean_Elab_App_24__isSuccess___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_App_24__isSuccess(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_App_25__getSuccess___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l___private_Lean_Elab_App_24__isSuccess(x_7);
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
lean_object* l___private_Lean_Elab_App_25__getSuccess(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_filterAux___main___at___private_Lean_Elab_App_25__getSuccess___spec__1(x_1, x_2, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_26__toMessageData___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_26__toMessageData___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_26__toMessageData___spec__1___rarg___boxed), 3, 0);
return x_5;
}
}
lean_object* _init_l___private_Lean_Elab_App_26__toMessageData___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Syntax_6__formatInfo___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_26__toMessageData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_26__toMessageData___spec__1___rarg(x_6, x_7, x_8);
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
x_23 = l___private_Lean_Elab_App_26__toMessageData___closed__1;
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
x_49 = l___private_Lean_Elab_App_26__toMessageData___closed__1;
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
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_26__toMessageData___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_26__toMessageData___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_26__toMessageData___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getRefPos___at___private_Lean_Elab_App_26__toMessageData___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_26__toMessageData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_App_26__toMessageData(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_App_27__toMessageList(lean_object* x_1) {
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
lean_object* l___private_Lean_Elab_App_27__toMessageList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_App_27__toMessageList(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_28__mergeFailures___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_33 = l___private_Lean_Elab_App_26__toMessageData(x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* _init_l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("overloaded, errors ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_28__mergeFailures___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = x_1;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_App_28__mergeFailures___spec__1), 9, 2);
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
x_16 = l___private_Lean_Elab_App_27__toMessageList(x_14);
lean_dec(x_14);
x_17 = l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__3;
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
lean_object* l___private_Lean_Elab_App_28__mergeFailures(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_App_28__mergeFailures___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_App_29__elabAppAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* _init_l___private_Lean_Elab_App_29__elabAppAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous, possible interpretations ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_App_29__elabAppAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_29__elabAppAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_App_29__elabAppAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_29__elabAppAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_App_29__elabAppAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_15 = l___private_Lean_Elab_App_23__elabAppFn___main(x_1, x_12, x_2, x_3, x_4, x_13, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_22 = l_Array_filterAux___main___at___private_Lean_Elab_App_25__getSuccess___spec__1(x_16, x_21, x_21);
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
x_31 = l___private_Lean_Elab_App_28__mergeFailures___rarg(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
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
x_40 = l___private_Lean_Elab_App_28__mergeFailures___rarg(x_16, x_5, x_6, x_7, x_8, x_39, x_10, x_17);
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
x_44 = l_Array_umapMAux___main___at___private_Lean_Elab_App_29__elabAppAux___spec__1(x_41, x_42, x_21, x_43);
x_45 = x_44;
x_46 = l___private_Lean_Elab_App_27__toMessageList(x_45);
lean_dec(x_45);
x_47 = l___private_Lean_Elab_App_29__elabAppAux___closed__3;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_17__elabTermAux___main___spec__1___rarg(x_1, x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
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
x_30 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_17__elabTermAux___main___spec__1___rarg(x_15, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_62 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_17__elabTermAux___main___spec__1___rarg(x_15, x_61, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_30 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_17__elabTermAux___main___spec__1___rarg(x_15, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_62 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_17__elabTermAux___main___spec__1___rarg(x_15, x_61, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_30 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_17__elabTermAux___main___spec__1___rarg(x_15, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_62 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_17__elabTermAux___main___spec__1___rarg(x_15, x_61, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_46 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_17__elabTermAux___main___spec__1___rarg(x_44, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_19 = l___private_Lean_Elab_App_29__elabAppAux(x_16, x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
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
lean_object* l___private_Lean_Elab_App_30__elabAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Array_empty___closed__1;
x_11 = l___private_Lean_Elab_App_29__elabAppAux(x_1, x_10, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_elabIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_30__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_10 = l___private_Lean_Elab_App_30__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_3 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__12;
x_4 = l___regBuiltin_Lean_Elab_Term_elabNamedPattern___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabExplicitUniv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_30__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_3 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Term_elabExplicitUniv___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabExplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_77; uint8_t x_78; 
x_77 = l___private_Lean_Elab_Term_10__isExplicit___closed__2;
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
x_50 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__5;
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
x_73 = l___private_Lean_Elab_Term_17__elabTermAux___main(x_2, x_71, x_72, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_73;
}
else
{
lean_object* x_74; 
lean_dec(x_13);
x_74 = l___private_Lean_Elab_App_30__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_74;
}
}
}
}
else
{
lean_object* x_75; 
lean_dec(x_13);
x_75 = l___private_Lean_Elab_App_30__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_75;
}
block_47:
{
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = 1;
x_16 = 0;
x_17 = l___private_Lean_Elab_Term_17__elabTermAux___main(x_2, x_15, x_16, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_23 = l___private_Lean_Elab_Term_17__elabTermAux___main(x_2, x_21, x_22, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_30 = l___private_Lean_Elab_Term_17__elabTermAux___main(x_2, x_28, x_29, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_37 = l___private_Lean_Elab_Term_17__elabTermAux___main(x_2, x_35, x_36, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_43 = l___private_Lean_Elab_Term_17__elabTermAux___main(x_2, x_41, x_42, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_43;
}
else
{
uint8_t x_44; uint8_t x_45; lean_object* x_46; 
lean_dec(x_13);
x_44 = 1;
x_45 = 0;
x_46 = l___private_Lean_Elab_Term_17__elabTermAux___main(x_2, x_44, x_45, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_3 = l___private_Lean_Elab_Term_10__isExplicit___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_elabExplicit___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_30__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_10 = l___private_Lean_Elab_App_30__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_3 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__13;
x_4 = l___regBuiltin_Lean_Elab_Term_elabProj___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_elabArrayRef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_App_30__elabAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_3 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__10;
x_4 = l___regBuiltin_Lean_Elab_Term_elabArrayRef___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_App_31__regTraceClasses(lean_object* x_1) {
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
l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1___closed__1 = _init_l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1___closed__1);
l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1___closed__2 = _init_l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1___closed__2();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_App_18__mkBaseProjections___spec__1___closed__2);
l___private_Lean_Elab_App_18__mkBaseProjections___closed__1 = _init_l___private_Lean_Elab_App_18__mkBaseProjections___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_18__mkBaseProjections___closed__1);
l___private_Lean_Elab_App_18__mkBaseProjections___closed__2 = _init_l___private_Lean_Elab_App_18__mkBaseProjections___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_18__mkBaseProjections___closed__2);
l___private_Lean_Elab_App_18__mkBaseProjections___closed__3 = _init_l___private_Lean_Elab_App_18__mkBaseProjections___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_18__mkBaseProjections___closed__3);
l___private_Lean_Elab_App_19__addLValArg___main___closed__1 = _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_19__addLValArg___main___closed__1);
l___private_Lean_Elab_App_19__addLValArg___main___closed__2 = _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_19__addLValArg___main___closed__2);
l___private_Lean_Elab_App_19__addLValArg___main___closed__3 = _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_19__addLValArg___main___closed__3);
l___private_Lean_Elab_App_19__addLValArg___main___closed__4 = _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_19__addLValArg___main___closed__4);
l___private_Lean_Elab_App_19__addLValArg___main___closed__5 = _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_19__addLValArg___main___closed__5);
l___private_Lean_Elab_App_19__addLValArg___main___closed__6 = _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_19__addLValArg___main___closed__6);
l___private_Lean_Elab_App_19__addLValArg___main___closed__7 = _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_19__addLValArg___main___closed__7);
l___private_Lean_Elab_App_19__addLValArg___main___closed__8 = _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_19__addLValArg___main___closed__8);
l___private_Lean_Elab_App_19__addLValArg___main___closed__9 = _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_19__addLValArg___main___closed__9);
l___private_Lean_Elab_App_19__addLValArg___main___closed__10 = _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_19__addLValArg___main___closed__10);
l___private_Lean_Elab_App_19__addLValArg___main___closed__11 = _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_19__addLValArg___main___closed__11);
l___private_Lean_Elab_App_19__addLValArg___main___closed__12 = _init_l___private_Lean_Elab_App_19__addLValArg___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_19__addLValArg___main___closed__12);
l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__1 = _init_l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__1);
l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__2 = _init_l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__2);
l___private_Lean_Elab_App_21__elabAppLVals___closed__1 = _init_l___private_Lean_Elab_App_21__elabAppLVals___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_21__elabAppLVals___closed__1);
l___private_Lean_Elab_App_21__elabAppLVals___closed__2 = _init_l___private_Lean_Elab_App_21__elabAppLVals___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_21__elabAppLVals___closed__2);
l___private_Lean_Elab_App_21__elabAppLVals___closed__3 = _init_l___private_Lean_Elab_App_21__elabAppLVals___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_21__elabAppLVals___closed__3);
l___private_Lean_Elab_App_23__elabAppFn___main___closed__1 = _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_23__elabAppFn___main___closed__1);
l___private_Lean_Elab_App_23__elabAppFn___main___closed__2 = _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_23__elabAppFn___main___closed__2);
l___private_Lean_Elab_App_23__elabAppFn___main___closed__3 = _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_23__elabAppFn___main___closed__3);
l___private_Lean_Elab_App_23__elabAppFn___main___closed__4 = _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_App_23__elabAppFn___main___closed__4);
l___private_Lean_Elab_App_23__elabAppFn___main___closed__5 = _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_App_23__elabAppFn___main___closed__5);
l___private_Lean_Elab_App_23__elabAppFn___main___closed__6 = _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_App_23__elabAppFn___main___closed__6);
l___private_Lean_Elab_App_23__elabAppFn___main___closed__7 = _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_App_23__elabAppFn___main___closed__7);
l___private_Lean_Elab_App_23__elabAppFn___main___closed__8 = _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_App_23__elabAppFn___main___closed__8);
l___private_Lean_Elab_App_23__elabAppFn___main___closed__9 = _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_App_23__elabAppFn___main___closed__9);
l___private_Lean_Elab_App_23__elabAppFn___main___closed__10 = _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_App_23__elabAppFn___main___closed__10);
l___private_Lean_Elab_App_23__elabAppFn___main___closed__11 = _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_App_23__elabAppFn___main___closed__11);
l___private_Lean_Elab_App_23__elabAppFn___main___closed__12 = _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_App_23__elabAppFn___main___closed__12);
l___private_Lean_Elab_App_23__elabAppFn___main___closed__13 = _init_l___private_Lean_Elab_App_23__elabAppFn___main___closed__13();
lean_mark_persistent(l___private_Lean_Elab_App_23__elabAppFn___main___closed__13);
l___private_Lean_Elab_App_26__toMessageData___closed__1 = _init_l___private_Lean_Elab_App_26__toMessageData___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_26__toMessageData___closed__1);
l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__1 = _init_l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__1);
l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__2 = _init_l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__2);
l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__3 = _init_l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_28__mergeFailures___rarg___closed__3);
l___private_Lean_Elab_App_29__elabAppAux___closed__1 = _init_l___private_Lean_Elab_App_29__elabAppAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_App_29__elabAppAux___closed__1);
l___private_Lean_Elab_App_29__elabAppAux___closed__2 = _init_l___private_Lean_Elab_App_29__elabAppAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_App_29__elabAppAux___closed__2);
l___private_Lean_Elab_App_29__elabAppAux___closed__3 = _init_l___private_Lean_Elab_App_29__elabAppAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_App_29__elabAppAux___closed__3);
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
res = l___private_Lean_Elab_App_31__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
